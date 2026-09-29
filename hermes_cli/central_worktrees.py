"""Central worktree lifecycle gate - V1 (SHADOW ONLY).

Central-root worktrees (the pool at :data:`CENTRAL_WORKTREE_ROOT`, by default
``/home/can/worktrees``) grew past 265 GB because missions create them with raw
``git worktree add`` commands that no lifecycle owner ever retires; the built-in
Hermes/Kanban/subagent cleanup paths only cover each repository's own
``.worktrees/`` directory, and registrations OUTSIDE it are by design treated
as external state that nothing reaps.  This module is the V1 visibility layer:

* :func:`observe_terminal_command` - shadow observer for RAW terminal
  creations.  It parses the command (top-level segments, ``env``/wrapper
  prefixes, ``cd`` tracking, ``git -C``, ``git worktree add`` options, one
  level of ``bash -c``) and records a central record + event when the
  effective destination resolves under the central root.  It NEVER blocks,
  refuses, mutates, or removes anything, and it never raises.
* :func:`observe_managed_creation` - observer for creations that went through
  a Hermes worktree API (``hermes -w`` CLI, Kanban workspaces, subagent
  isolation).  Central destinations get a record; repo-local ones are
  classified and left alone.
* :func:`scan_central_worktrees` - READ-ONLY population scanner (counts,
  bytes, registration, dirty/clean, same-HEAD duplicates, unpinned detached
  HEADs, active process references, references, lease state).  It backfills
  registry records for pre-existing worktrees as ``UNKNOWN_CREATION``.
  It performs NO retirement of any kind.
* A minimal renewable lease store (:func:`issue_lease` / :func:`renew_lease`).
  A missing or expired lease classifies a record as ``ORPHAN_REVIEW``; it
  NEVER authorizes deletion.  Dirty, referenced, active, unpinned,
  unresolvable or untracked-content trees remain protected regardless.

Explicit non-goals for V1 (do not add without a new authorization): blocking
or refusing commands, ``git worktree remove``/``prune``, ``git gc/clean``,
filesystem deletion, dirty-tree cleanup, or any enforcement of the shadow
policy codes.

Known limitations (honest by design): git invocations buried inside other
programs (``xargs``, ``find -exec``, scripts), ``$( ... )`` substitutions and
unparseable quoting are not classified; the scanner backfill covers them as
``UNKNOWN_CREATION`` records.  Destinations containing shell variables are
recorded as ``UNKNOWN_CREATION`` events instead of guesses.  Fast path: any
command without the literal substring ``worktree`` is dropped immediately.

State lives under ``<hermes home>/state/central_worktrees/`` (registry.json,
events.jsonl, leases.json, snapshots.jsonl, .lock).  Tests pass explicit
``state_dir`` / ``central_root`` to stay hermetic.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import logging
import os
import re
import shlex
import shutil
import stat
import subprocess
import sys
import time
import uuid
from concurrent.futures import ThreadPoolExecutor
from datetime import datetime, timezone
from pathlib import Path
from typing import Any, Dict, List, Optional, Sequence, Tuple

logger = logging.getLogger(__name__)

try:  # POSIX advisory locking; Windows degrades to best-effort
    import fcntl
except ImportError:  # pragma: no cover - Windows
    fcntl = None  # type: ignore[assignment]

# ---------------------------------------------------------------------------
# Constants
# ---------------------------------------------------------------------------

CENTRAL_WORKTREE_ROOT = Path("/home/can/worktrees")
"""Default central-root pool.  Host-specific by design; override per call."""

SCHEMA_VERSION = 1
_REGISTRY_NAME = "registry.json"
_EVENTS_NAME = "events.jsonl"
_LEASES_NAME = "leases.json"
_SNAPSHOTS_NAME = "snapshots.jsonl"
_LOCK_NAME = ".lock"

CLASS_MANAGED = "MANAGED_CREATION"
CLASS_RAW_CENTRAL = "RAW_CENTRAL_CREATION"
CLASS_RAW_NON_CENTRAL = "RAW_NON_CENTRAL_CREATION"
CLASS_UNKNOWN = "UNKNOWN_CREATION"

STATUS_LEASED = "LEASED"
STATUS_ORPHAN_REVIEW = "ORPHAN_REVIEW"

LEASE_ACTIVE = "ACTIVE"
LEASE_EXPIRED = "EXPIRED"
LEASE_MISSING = "MISSING"

CLEANUP_POLICY_SHADOW_ONLY = "SHADOW_ONLY_NO_RETIREMENT"

DEFAULT_LEASE_TTL_SECONDS = 24 * 3600
_MAX_COMMAND_ANALYSIS_CHARS = 200_000
_DEFAULT_SCAN_WORKERS = 8

# Shadow policy codes.  V1 evaluates and RECORDS these only; nothing is refused.
PASS_REGISTERED_OWNER = "PASS_REGISTERED_OWNER"
WARN_MISSING_OWNER = "WARN_MISSING_OWNER"
WARN_DUPLICATE_SAME_HEAD = "WARN_DUPLICATE_SAME_HEAD"
WARN_UNPINNED_DETACHED_HEAD = "WARN_UNPINNED_DETACHED_HEAD"
WARN_MISSING_LEASE = "WARN_MISSING_LEASE"
WARN_UNKNOWN_PURPOSE = "WARN_UNKNOWN_PURPOSE"
WARN_EXISTING_CENTRAL_PATH = "WARN_EXISTING_CENTRAL_PATH"
ESCALATE_DIRTY_DUPLICATE = "ESCALATE_DIRTY_DUPLICATE"
ESCALATE_UNRESOLVABLE_HEAD = "ESCALATE_UNRESOLVABLE_HEAD"

POLICY_CODE_ORDER = (
    PASS_REGISTERED_OWNER,
    WARN_MISSING_OWNER,
    WARN_MISSING_LEASE,
    WARN_UNKNOWN_PURPOSE,
    WARN_DUPLICATE_SAME_HEAD,
    WARN_UNPINNED_DETACHED_HEAD,
    WARN_EXISTING_CENTRAL_PATH,
    ESCALATE_DIRTY_DUPLICATE,
    ESCALATE_UNRESOLVABLE_HEAD,
)

_PROTECTION_FLAGS = (
    "dirty",
    "untracked_content",
    "active_process",
    "referenced",
    "unpinned_detached_head",
    "unresolvable_head",
)

_REPO_IDENTITIES = {
    "/home/can/flowbot/.git": "FlowBot",
    "/home/can/.hermes/hermes-agent/.git": "Hermes Agent",
    "/home/can/projects/FlowCoach-canonical/.git": "FlowCoach canonical",
    "/mnt/c/Users/PC/Desktop/Projects/FlowCoach/.git": "FlowCoach retired (NTFS)",
    "/mnt/c/Users/PC/Desktop/Projects/ZipZap/.git": "ZipZap",
}

_WRAPPER_SIMPLE = frozenset({"nohup", "exec", "setsid", "ionice"})
_WRAPPER_SHELLS = frozenset({"bash", "sh", "dash", "zsh", "ksh", "mksh", "ash"})
_ASSIGNMENT_RE = re.compile(r"^[A-Za-z_][A-Za-z0-9_]*=")
_ENV_VALUE_OPTS = frozenset({"-u", "--unset", "-C", "--chdir", "-S", "--split-string"})
_TIMEOUT_VALUE_OPTS = frozenset({"-k", "--kill-after", "-s", "--signal"})

_REFERENCE_EXTENSIONS = frozenset({".json", ".md", ".yaml", ".yml", ".service", ".txt", ".toml"})
_DEFAULT_MAX_REFERENCE_FILES = 400
_DEFAULT_MAX_REFERENCE_BYTES = 4_000_000


# ---------------------------------------------------------------------------
# State paths / small IO helpers
# ---------------------------------------------------------------------------


def _state_dir(state_dir: Optional[os.PathLike | str] = None) -> Path:
    if state_dir is not None:
        return Path(state_dir).expanduser()
    from hermes_constants import get_hermes_home

    return get_hermes_home() / "state" / "central_worktrees"


def _central_root(central_root: Optional[os.PathLike | str] = None) -> Path:
    return Path(central_root).expanduser() if central_root is not None else CENTRAL_WORKTREE_ROOT


def _norm_path(value: os.PathLike | str) -> str:
    return os.path.normpath(os.path.abspath(os.path.expanduser(str(value))))


def _is_under(path: os.PathLike | str, root: os.PathLike | str) -> bool:
    """True when *path* is *root* itself or below it (lexical, post-expand)."""
    try:
        p, r = _norm_path(path), _norm_path(root)
    except Exception:
        return False
    return p == r or p.startswith(r + os.sep)


def _now_iso(ts: Optional[float] = None) -> str:
    return datetime.fromtimestamp(ts if ts is not None else time.time(), tz=timezone.utc).isoformat(
        timespec="seconds"
    )


def _atomic_write_json(path: Path, data: Any) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    tmp = path.with_name(path.name + f".tmp.{os.getpid()}")
    tmp.write_text(json.dumps(data, indent=2, sort_keys=False) + "\n", encoding="utf-8")
    os.replace(tmp, path)


def _append_jsonl(path: Path, payload: Dict[str, Any]) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    line = json.dumps(payload, ensure_ascii=False, sort_keys=False) + "\n"
    with open(path, "a", encoding="utf-8") as handle:
        if fcntl is not None:
            try:
                fcntl.flock(handle.fileno(), fcntl.LOCK_EX)
            except OSError:
                pass
        handle.write(line)
        # flock is released on close


def _locked(state_dir: Path):
    """Advisory lock over one state directory; degrades to no-op without fcntl."""

    class _Lock:
        def __enter__(self):
            self._handle = None
            if fcntl is None:
                return self
            try:
                state_dir.mkdir(parents=True, exist_ok=True)
                self._handle = open(state_dir / _LOCK_NAME, "a+")
                fcntl.flock(self._handle.fileno(), fcntl.LOCK_EX)
            except OSError:
                self._handle = None
            return self

        def __exit__(self, *_exc):
            if fcntl is not None and self._handle is not None:
                try:
                    fcntl.flock(self._handle.fileno(), fcntl.LOCK_UN)
                except OSError:
                    pass
                try:
                    self._handle.close()
                except OSError:
                    pass
            return False

    return _Lock()


def _load_json(path: Path, default: Any) -> Any:
    try:
        return json.loads(path.read_text(encoding="utf-8"))
    except FileNotFoundError:
        return default
    except (OSError, ValueError):
        # Preserve unreadable state rather than clobbering it silently.
        try:
            path.replace(path.with_name(path.name + f".corrupt.{int(time.time())}"))
        except OSError:
            pass
        return default


def _load_registry(state_dir: Path) -> Dict[str, Any]:
    data = _load_json(state_dir / _REGISTRY_NAME, None)
    if not isinstance(data, dict) or not isinstance(data.get("records"), dict):
        return {"schema": "hermes.central-worktrees.registry.v1", "version": SCHEMA_VERSION, "records": {}}
    return data


def _load_leases(state_dir: Path) -> Dict[str, Any]:
    data = _load_json(state_dir / _LEASES_NAME, None)
    if not isinstance(data, dict) or not isinstance(data.get("leases"), dict):
        return {"schema": "hermes.central-worktrees.leases.v1", "version": SCHEMA_VERSION, "leases": {}}
    return data


# ---------------------------------------------------------------------------
# Command classification (structured, deterministic)
# ---------------------------------------------------------------------------


def _split_top_level(command: str) -> List[str]:
    """Split a shell command on top-level separators (``;`` ``&&`` ``||`` ``|`` ``&`` newline)."""
    parts: List[str] = []
    buf: List[str] = []
    i, n, quote = 0, len(command), None
    while i < n:
        ch = command[i]
        if quote == "'":
            if ch == "'":
                quote = None
            buf.append(ch)
            i += 1
            continue
        if quote == '"':
            if ch == "\\" and i + 1 < n:
                buf.append(ch)
                buf.append(command[i + 1])
                i += 2
                continue
            if ch == '"':
                quote = None
            buf.append(ch)
            i += 1
            continue
        if ch == "\\" and i + 1 < n:
            buf.append(ch)
            buf.append(command[i + 1])
            i += 2
            continue
        if ch in "'\"":
            quote = ch
            buf.append(ch)
            i += 1
            continue
        if ch in ";\n":
            parts.append("".join(buf))
            buf = []
            i += 1
            continue
        if ch == "&":
            if command.startswith("&&", i):
                i += 2
            else:
                i += 1
            parts.append("".join(buf))
            buf = []
            continue
        if ch == "|":
            i += 2 if command.startswith("||", i) else 1
            parts.append("".join(buf))
            buf = []
            continue
        buf.append(ch)
        i += 1
    parts.append("".join(buf))
    return [p for p in parts if p.strip()]


def _tokenize(segment: str) -> Optional[List[str]]:
    try:
        tokens = shlex.split(segment, posix=True, comments=False)
    except ValueError:
        return None
    return tokens if tokens else None


def _strip_prefixes(tokens: List[str]) -> Optional[List[str]]:
    """Strip env assignments and known non-shell wrapper commands from the front."""
    idx = 0
    depth = 0
    while idx < len(tokens) and depth < 6:
        tok = tokens[idx]
        if _ASSIGNMENT_RE.match(tok):
            idx += 1
            continue
        base = tok.rsplit("/", 1)[-1]
        if base in _WRAPPER_SIMPLE:
            idx += 1
            depth += 1
            continue
        if base == "command":
            if idx + 1 < len(tokens) and tokens[idx + 1] in ("-v", "-V", "-p"):
                return None  # a query, not a runner
            idx += 1
            depth += 1
            continue
        if base == "env":
            idx += 1
            while idx < len(tokens) and (
                _ASSIGNMENT_RE.match(tokens[idx]) or tokens[idx].startswith("-")
            ):
                if tokens[idx] in _ENV_VALUE_OPTS and idx + 1 < len(tokens):
                    idx += 2
                else:
                    idx += 1
            depth += 1
            continue
        if base == "timeout":
            idx += 1
            while idx < len(tokens) and tokens[idx].startswith("-"):
                if tokens[idx] in _TIMEOUT_VALUE_OPTS and idx + 1 < len(tokens):
                    idx += 2
                else:
                    idx += 1
            if idx < len(tokens):
                idx += 1  # the duration token
            depth += 1
            continue
        if base == "nice":
            idx += 1
            if idx < len(tokens) and tokens[idx] in ("-n", "--adjustment") and idx + 1 < len(tokens):
                idx += 2
            elif idx < len(tokens) and tokens[idx].startswith("-"):
                idx += 1
            depth += 1
            continue
        break
    return tokens[idx:] if idx < len(tokens) else None


def _shell_inner_command(tokens: List[str]) -> Optional[str]:
    """The command string of ``bash -c ...`` / ``sh -lc ...``, else None."""
    for i, tok in enumerate(tokens[1:], start=1):
        if tok == "--":
            continue
        if tok.startswith("-") and not tok.startswith("--") and "c" in tok[1:]:
            return tokens[i + 1] if i + 1 < len(tokens) else None
        if not tok.startswith("-"):
            break
    return None


def _parse_git_worktree_add(tokens: List[str], current_cwd: Optional[str], cwd_known: bool) -> Dict[str, Any]:
    """Parse ``git [global opts] worktree add ...`` tail; tokens[0] is git."""
    idx = 1
    git_dir: Optional[str] = None
    while idx < len(tokens) and tokens[idx].startswith("-"):
        tok = tokens[idx]
        if tok == "-C":
            if idx + 1 >= len(tokens):
                return {"kind": "not_worktree_add"}
            git_dir = tokens[idx + 1]
            idx += 2
            continue
        if tok.startswith("-C") and len(tok) > 2:
            git_dir = tok[2:]
            idx += 1
            continue
        if tok in ("-c", "--config", "--git-dir", "--work-tree", "--namespace", "--exec-path") and idx + 1 < len(tokens):
            idx += 2
            continue
        idx += 1
    if idx + 1 >= len(tokens) or tokens[idx] != "worktree" or tokens[idx + 1] != "add":
        return {"kind": "not_worktree_add"}
    idx += 2

    dest: Optional[str] = None
    new_branch: Optional[str] = None
    detached = False
    rest: List[str] = []
    i = idx
    while i < len(tokens):
        tok = tokens[i]
        if tok == "--":
            i += 1
            if i < len(tokens):
                if dest is None:
                    dest = tokens[i]
                else:
                    rest.append(tokens[i])
                i += 1
            continue
        if tok != "-" and tok.startswith("-"):
            if tok in ("-b", "-B"):
                if i + 1 >= len(tokens):
                    return {"kind": "worktree_add_unknown_dest", "reason": "branch_option_missing_value"}
                new_branch = tokens[i + 1]
                i += 2
                continue
            if (tok.startswith("-b") or tok.startswith("-B")) and len(tok) > 2 and not tok.startswith("--"):
                new_branch = tok[2:]
                i += 1
                continue
            if tok in ("-d", "--detach"):
                detached = True
            i += 1
            continue
        if dest is None:
            dest = tok
        else:
            rest.append(tok)
        i += 1

    eff_cwd = current_cwd
    if git_dir is not None:
        if "$" in git_dir or "`" in git_dir:
            eff_cwd, cwd_known = None, False
        else:
            expanded = os.path.expanduser(git_dir)
            if not os.path.isabs(expanded):
                if current_cwd is None or not cwd_known:
                    eff_cwd, cwd_known = None, False
                else:
                    eff_cwd = os.path.normpath(os.path.join(current_cwd, expanded))
            else:
                eff_cwd = os.path.normpath(expanded)
            cwd_known = True

    if dest is None:
        return {
            "kind": "worktree_add_unknown_dest",
            "reason": "missing_path",
            "new_branch": new_branch,
            "detached": detached,
            "repo_dir": eff_cwd,
        }
    if "$" in dest or "`" in dest:
        return {
            "kind": "worktree_add_unknown_dest",
            "reason": "dest_contains_shell_expansion",
            "new_branch": new_branch,
            "detached": detached,
            "repo_dir": eff_cwd,
        }
    expanded = os.path.expanduser(dest)
    if not os.path.isabs(expanded):
        if eff_cwd is None or not cwd_known:
            return {
                "kind": "worktree_add_unknown_dest",
                "reason": "relative_dest_cwd_unknown",
                "new_branch": new_branch,
                "detached": detached,
                "repo_dir": eff_cwd,
            }
        resolved = os.path.normpath(os.path.join(eff_cwd, expanded))
    else:
        resolved = os.path.normpath(expanded)
    return {
        "kind": "worktree_add",
        "dest": resolved,
        "new_branch": new_branch,
        "detached": detached,
        "base_revision": rest[0] if rest else None,
        "extra_args": rest[1:] if len(rest) > 1 else [],
        "repo_dir": eff_cwd,
        "dest_source": "absolute" if os.path.isabs(expanded) else "relative",
        "confidence": "high" if eff_cwd or os.path.isabs(expanded) else "medium",
    }


def _classify_segment(segment: str, current_cwd: Optional[str], cwd_known: bool, depth: int) -> Dict[str, Any]:
    tokens = _tokenize(segment)
    if tokens is None:
        return {"kind": "not_worktree_add"}
    stripped = _strip_prefixes(tokens)
    if not stripped:
        return {"kind": "not_worktree_add"}

    first_base = stripped[0].rsplit("/", 1)[-1]
    if first_base == "cd":
        target = stripped[1] if len(stripped) > 1 else None
        if target is None or target == "-" or "$" in target or "`" in target:
            return {"kind": "cd", "cwd": current_cwd, "cwd_known": False}
        expanded = os.path.expanduser(target)
        if not os.path.isabs(expanded):
            if current_cwd is None or not cwd_known:
                return {"kind": "cd", "cwd": None, "cwd_known": False}
            expanded = os.path.join(current_cwd, expanded)
        return {"kind": "cd", "cwd": os.path.normpath(expanded), "cwd_known": True}

    if first_base in _WRAPPER_SHELLS and depth < 2:
        inner = _shell_inner_command(stripped)
        if inner:
            return _classify_command(inner, current_cwd, cwd_known, depth + 1)
        return {"kind": "not_worktree_add"}

    if first_base != "git":
        return {"kind": "not_worktree_add"}
    return _parse_git_worktree_add(stripped, current_cwd, cwd_known)


def _classify_command(command: str, current_cwd: Optional[str], cwd_known: bool, depth: int = 0) -> Dict[str, Any]:
    for segment in _split_top_level(command):
        result = _classify_segment(segment, current_cwd, cwd_known, depth)
        kind = result.get("kind")
        if kind == "cd":
            current_cwd = result.get("cwd")
            cwd_known = bool(result.get("cwd_known"))
            continue
        if kind and kind != "not_worktree_add":
            return result
    return {"kind": "not_worktree_add"}


def classify_terminal_command(command: Any, cwd: Optional[str] = None) -> Dict[str, Any]:
    """Classify a terminal command string for effective ``git worktree add`` intent.

    Pure and side-effect free.  Returns one of:

    * ``{"kind": "not_worktree_add"}``
    * ``{"kind": "worktree_add", "dest": <absolute normalized path>, ...}``
    * ``{"kind": "worktree_add_unknown_dest", "reason": ...}``

    ``cwd`` is the command's effective starting directory (the terminal tool's
    resolved cwd); relative destinations resolve against ``cd`` / ``git -C``
    state tracked across top-level segments.  Never raises.
    """
    try:
        if not isinstance(command, str) or "worktree" not in command:
            return {"kind": "not_worktree_add"}
        base_cwd = _norm_path(cwd) if cwd else None
        return _classify_command(command[:_MAX_COMMAND_ANALYSIS_CHARS], base_cwd, base_cwd is not None)
    except Exception:  # defensive: classification must never break a command
        return {"kind": "not_worktree_add", "error": "classifier_exception"}


# ---------------------------------------------------------------------------
# Shadow policy + records
# ---------------------------------------------------------------------------


def _policy_codes(
    *,
    owner: Optional[str],
    purpose: Optional[str],
    lease_state: str,
    registered: bool,
    dirty: bool,
    in_duplicate_group: bool,
    unpinned_detached: bool,
    unresolvable: bool,
    existing_path_observed: bool,
) -> List[str]:
    codes = set()
    if unresolvable:
        codes.add(ESCALATE_UNRESOLVABLE_HEAD)
    if existing_path_observed:
        codes.add(WARN_EXISTING_CENTRAL_PATH)
    if lease_state != LEASE_ACTIVE:
        codes.add(WARN_MISSING_LEASE)
    elif owner and registered and not unresolvable:
        codes.add(PASS_REGISTERED_OWNER)
    if not owner:
        codes.add(WARN_MISSING_OWNER)
    if not purpose:
        codes.add(WARN_UNKNOWN_PURPOSE)
    if in_duplicate_group:
        codes.add(WARN_DUPLICATE_SAME_HEAD)
    if in_duplicate_group and dirty:
        codes.add(ESCALATE_DIRTY_DUPLICATE)
    if unpinned_detached:
        codes.add(WARN_UNPINNED_DETACHED_HEAD)
    return [code for code in POLICY_CODE_ORDER if code in codes]


def _lifecycle_status(lease_state: str) -> str:
    return STATUS_LEASED if lease_state == LEASE_ACTIVE else STATUS_ORPHAN_REVIEW


def _repo_identity(common_dir: Optional[str], path: str) -> str:
    if not common_dir:
        return "UNKNOWN"
    known = _REPO_IDENTITIES.get(common_dir)
    if known:
        return known
    repo = os.path.dirname(common_dir) if common_dir.endswith(os.sep + ".git") else common_dir
    return os.path.basename(repo) or "UNKNOWN"


def _new_record(path: str, *, mechanism: str, now_ts: float, creator: Optional[Dict[str, Any]] = None,
                session_id: Optional[str] = None, mission_id: Optional[str] = None) -> Dict[str, Any]:
    return {
        "path": path,
        "first_observed_at": _now_iso(now_ts),
        "updated_at": _now_iso(now_ts),
        "creation": {
            "mechanism": mechanism,
            "observed_at": _now_iso(now_ts),
            "command_fingerprint": None,
            "cwd": None,
            "confidence": None,
            "existing_path_observed": False,
            "session_id": session_id,
            "creator": creator,
        },
        "repo": {"common_dir": None, "identity": "UNKNOWN", "head": None, "branch": None,
                 "detached": None, "registered": None, "standalone_repo": None},
        "owner": {"owner": None, "mission_id": mission_id, "session_id": session_id, "creator": creator},
        "purpose": None,
        "lease": {"lease_id": None, "state": LEASE_MISSING, "expires_at": None},
        "cleanup_policy": {"mode": CLEANUP_POLICY_SHADOW_ONLY, "retirement_authorized": False},
        "scan": None,
        "protection": [],
        "policy_codes": [],
        "lifecycle_status": STATUS_ORPHAN_REVIEW,
    }


def _upsert_creation_record(
    registry: Dict[str, Any],
    *,
    path: str,
    mechanism: str,
    now_ts: float,
    creator: Optional[Dict[str, Any]],
    session_id: Optional[str],
    mission_id: Optional[str],
    command_fingerprint: Optional[str] = None,
    cwd: Optional[str] = None,
    confidence: Optional[str] = None,
    repo_dir: Optional[str] = None,
    branch: Optional[str] = None,
    base_revision: Optional[str] = None,
    detached: Optional[bool] = None,
    existing_path_observed: bool = False,
    subagent_id: Optional[str] = None,
) -> Dict[str, Any]:
    records = registry.setdefault("records", {})
    record = records.get(path)
    if record is None:
        record = _new_record(path, mechanism=mechanism, now_ts=now_ts, creator=creator,
                             session_id=session_id, mission_id=mission_id)
        records[path] = record
    creation = record.setdefault("creation", {})
    if mechanism != CLASS_UNKNOWN or creation.get("mechanism") in (None, CLASS_UNKNOWN):
        creation["mechanism"] = mechanism
        creation["observed_at"] = _now_iso(now_ts)
        creation["command_fingerprint"] = command_fingerprint
        creation["cwd"] = cwd
        creation["confidence"] = confidence
        creation["session_id"] = session_id
        creation["creator"] = creator
        if subagent_id:
            creation["subagent_id"] = subagent_id
        if base_revision:
            creation["base_revision"] = base_revision
        if branch:
            creation["branch"] = branch
        if detached is not None:
            creation["detached"] = detached
    if existing_path_observed:
        creation["existing_path_observed"] = True
    if repo_dir:
        creation.setdefault("repo_dir_hint", repo_dir)
    owner = record.setdefault("owner", {})
    if session_id and not owner.get("session_id"):
        owner["session_id"] = session_id
    record["updated_at"] = _now_iso(now_ts)
    return record


def _command_fingerprint(command: str) -> str:
    return "sha256:" + hashlib.sha256(command.encode("utf-8", errors="replace")).hexdigest()


# ---------------------------------------------------------------------------
# Observers (creation paths)
# ---------------------------------------------------------------------------


def observe_terminal_command(
    command: Any,
    *,
    cwd: Optional[str] = None,
    session_id: Optional[str] = None,
    session_key: Optional[str] = None,
    env_type: str = "local",
    creator: Optional[Dict[str, Any]] = None,
    central_root: Optional[os.PathLike | str] = None,
    state_dir: Optional[os.PathLike | str] = None,
) -> Optional[Dict[str, Any]]:
    """Observe one terminal command for a raw central-root worktree creation.

    Returns the event/record dict when the command is a worktree creation this
    gate cares about (central destination, or unknown destination), else None.
    NEVER raises, NEVER blocks, NEVER mutates any worktree.  Only central
    destinations (and unresolvable-destination attempts) produce state writes;
    repo-local and other outside-root creations are classified and dropped.
    """
    try:
        if not isinstance(command, str) or "worktree" not in command:
            return None
        root = _central_root(central_root)
        info = classify_terminal_command(command, cwd)
        kind = info.get("kind")
        if kind == "not_worktree_add":
            return None
        now_ts = time.time()
        if creator is None:
            creator = {"kind": "terminal", "pid": os.getpid(), "session_key": session_key}

        if kind == "worktree_add_unknown_dest":
            event = {
                "ts": _now_iso(now_ts),
                "event": "creation_observed",
                "classification": CLASS_UNKNOWN,
                "reason": info.get("reason"),
                "path": None,
                "central_record_created": False,
                "cwd": _norm_path(cwd) if cwd else None,
                "env_type": env_type,
                "session_id": session_id,
                "session_key": session_key,
                "creator": creator,
                "command_fingerprint": _command_fingerprint(command),
                "command_len": len(command),
            }
            _append_jsonl(_state_dir(state_dir) / _EVENTS_NAME, event)
            return event

        dest = info["dest"]
        in_central = _is_under(dest, root) and env_type == "local"
        if not _is_under(dest, root):
            # Outside the central root: classified, deliberately not recorded.
            info["classification"] = CLASS_RAW_NON_CENTRAL
            info["central_record_created"] = False
            return info
        if not in_central:
            # Central-looking path on a non-local backend is not this host's pool.
            info["classification"] = CLASS_RAW_NON_CENTRAL
            info["central_record_created"] = False
            info["reason"] = f"non_local_backend:{env_type}"
            return info

        existing = os.path.lexists(dest)
        fingerprint = _command_fingerprint(command)
        event = {
            "ts": _now_iso(now_ts),
            "event": "creation_observed",
            "classification": CLASS_RAW_CENTRAL,
            "path": dest,
            "central_root": str(root),
            "dest_source": info.get("dest_source"),
            "repo_dir": info.get("repo_dir"),
            "new_branch": info.get("new_branch"),
            "detached": info.get("detached"),
            "base_revision": info.get("base_revision"),
            "confidence": info.get("confidence"),
            "existing_path_observed": existing,
            "central_record_created": True,
            "cwd": _norm_path(cwd) if cwd else None,
            "env_type": env_type,
            "session_id": session_id,
            "session_key": session_key,
            "creator": creator,
            "command_fingerprint": fingerprint,
            "command_len": len(command),
        }
        state = _state_dir(state_dir)
        with _locked(state):
            registry = _load_registry(state)
            record = _upsert_creation_record(
                registry,
                path=dest,
                mechanism=CLASS_RAW_CENTRAL,
                now_ts=now_ts,
                creator=creator,
                session_id=session_id,
                mission_id=None,
                command_fingerprint=fingerprint,
                cwd=_norm_path(cwd) if cwd else None,
                confidence=info.get("confidence"),
                repo_dir=info.get("repo_dir"),
                branch=info.get("new_branch"),
                base_revision=info.get("base_revision"),
                detached=info.get("detached"),
                existing_path_observed=existing,
            )
            if existing:
                codes = set(record.get("policy_codes") or [])
                codes.add(WARN_EXISTING_CENTRAL_PATH)
                record["policy_codes"] = [c for c in POLICY_CODE_ORDER if c in codes]
            registry["updated_at"] = _now_iso(now_ts)
            _atomic_write_json(state / _REGISTRY_NAME, registry)
            _append_jsonl(state / _EVENTS_NAME, event)
        info["classification"] = CLASS_RAW_CENTRAL
        info["central_record_created"] = True
        info["existing_path_observed"] = existing
        info["record"] = record
        return info
    except Exception:
        logger.debug("central worktree observer (terminal) failed", exc_info=True)
        return None


def observe_managed_creation(
    path: os.PathLike | str,
    *,
    repo_root: Optional[os.PathLike | str] = None,
    branch: Optional[str] = None,
    base_revision: Optional[str] = None,
    detached: Optional[bool] = None,
    creator: Optional[str] = None,
    mission_id: Optional[str] = None,
    session_id: Optional[str] = None,
    subagent_id: Optional[str] = None,
    central_root: Optional[os.PathLike | str] = None,
    state_dir: Optional[os.PathLike | str] = None,
) -> Optional[Dict[str, Any]]:
    """Observe a creation routed through a Hermes worktree API (shadow, no writes
    outside the central root).  NEVER raises, NEVER blocks."""
    try:
        if path is None:
            return None
        target = _norm_path(path)
        root = _central_root(central_root)
        creator_info = {"kind": "managed", "name": creator, "pid": os.getpid()}
        if subagent_id:
            creator_info["subagent_id"] = subagent_id
        if repo_root:
            creator_info["repo_root"] = _norm_path(repo_root)
        now_ts = time.time()
        if not _is_under(target, root):
            return {
                "classification": CLASS_MANAGED,
                "central_record_created": False,
                "path": target,
                "repo_dir": _norm_path(repo_root) if repo_root else None,
                "branch": branch,
            }
        event = {
            "ts": _now_iso(now_ts),
            "event": "creation_observed",
            "classification": CLASS_MANAGED,
            "path": target,
            "central_root": str(root),
            "repo_dir": _norm_path(repo_root) if repo_root else None,
            "new_branch": branch,
            "detached": detached,
            "base_revision": base_revision,
            "central_record_created": True,
            "session_id": session_id,
            "creator": creator_info,
        }
        state = _state_dir(state_dir)
        with _locked(state):
            registry = _load_registry(state)
            record = _upsert_creation_record(
                registry,
                path=target,
                mechanism=CLASS_MANAGED,
                now_ts=now_ts,
                creator=creator_info,
                session_id=session_id,
                mission_id=mission_id,
                repo_dir=_norm_path(repo_root) if repo_root else None,
                branch=branch,
                base_revision=base_revision,
                detached=detached,
                subagent_id=subagent_id,
            )
            registry["updated_at"] = _now_iso(now_ts)
            _atomic_write_json(state / _REGISTRY_NAME, registry)
            _append_jsonl(state / _EVENTS_NAME, event)
        return {"classification": CLASS_MANAGED, "central_record_created": True, "path": target,
                "record": record}
    except Exception:
        logger.debug("central worktree observer (managed) failed", exc_info=True)
        return None


# ---------------------------------------------------------------------------
# Leases
# ---------------------------------------------------------------------------


def issue_lease(
    path: os.PathLike | str,
    *,
    owner: str,
    mission_id: Optional[str] = None,
    session_id: Optional[str] = None,
    ttl_seconds: int = DEFAULT_LEASE_TTL_SECONDS,
    now: Optional[float] = None,
    state_dir: Optional[os.PathLike | str] = None,
) -> Dict[str, Any]:
    """Issue a renewable ownership lease for one central worktree path (metadata only)."""
    now_ts = now if now is not None else time.time()
    ttl = max(60, int(ttl_seconds))
    lease_id = "lease-" + uuid.uuid4().hex[:16]
    lease = {
        "lease_id": lease_id,
        "path": _norm_path(path),
        "owner": owner,
        "mission_id": mission_id,
        "session_id": session_id,
        "created_at": _now_iso(now_ts),
        "renewed_at": _now_iso(now_ts),
        "expires_at": _now_iso(now_ts + ttl),
        "expires_at_epoch": now_ts + ttl,
        "ttl_seconds": ttl,
        "renewable": True,
        "state": LEASE_ACTIVE,
    }
    state = _state_dir(state_dir)
    with _locked(state):
        data = _load_leases(state)
        data["leases"][lease_id] = lease
        data["updated_at"] = _now_iso(now_ts)
        _atomic_write_json(state / _LEASES_NAME, data)
    return lease


def renew_lease(
    lease_id: str,
    *,
    ttl_seconds: Optional[int] = None,
    now: Optional[float] = None,
    state_dir: Optional[os.PathLike | str] = None,
) -> Optional[Dict[str, Any]]:
    """Renew a lease; returns the updated lease or None when unknown."""
    now_ts = now if now is not None else time.time()
    state = _state_dir(state_dir)
    with _locked(state):
        data = _load_leases(state)
        lease = data["leases"].get(lease_id)
        if lease is None:
            return None
        ttl = max(60, int(ttl_seconds if ttl_seconds is not None else lease.get("ttl_seconds") or DEFAULT_LEASE_TTL_SECONDS))
        lease["renewed_at"] = _now_iso(now_ts)
        lease["ttl_seconds"] = ttl
        lease["expires_at"] = _now_iso(now_ts + ttl)
        lease["expires_at_epoch"] = now_ts + ttl
        data["updated_at"] = _now_iso(now_ts)
        _atomic_write_json(state / _LEASES_NAME, data)
        return lease


def lease_status_for_path(
    path: os.PathLike | str,
    *,
    now: Optional[float] = None,
    state_dir: Optional[os.PathLike | str] = None,
) -> Dict[str, Any]:
    """Lease state for one path: ACTIVE / EXPIRED / MISSING (never deletion authority)."""
    try:
        now_ts = now if now is not None else time.time()
        target = _norm_path(path)
        data = _load_leases(_state_dir(state_dir))
        candidates = [l for l in data["leases"].values() if l.get("path") == target]
        if not candidates:
            return {"state": LEASE_MISSING, "lease_id": None, "owner": None, "expires_at": None}
        best = max(candidates, key=lambda l: float(l.get("expires_at_epoch") or 0))
        if float(best.get("expires_at_epoch") or 0) > now_ts:
            return {"state": LEASE_ACTIVE, "lease_id": best["lease_id"], "owner": best.get("owner"),
                    "expires_at": best.get("expires_at")}
        return {"state": LEASE_EXPIRED, "lease_id": best["lease_id"], "owner": best.get("owner"),
                "expires_at": best.get("expires_at")}
    except Exception:
        return {"state": LEASE_MISSING, "lease_id": None, "owner": None, "expires_at": None}


# ---------------------------------------------------------------------------
# Read-only discovery helpers (no retirement of any kind)
# ---------------------------------------------------------------------------


def _git_env() -> Dict[str, str]:
    env = os.environ.copy()
    env.update({
        "GIT_OPTIONAL_LOCKS": "0",
        "GIT_NO_LAZY_FETCH": "1",
        "GIT_TERMINAL_PROMPT": "0",
        "GIT_PAGER": "cat",
    })
    return env


def _run_git(args: List[str], cwd: str, timeout: float = 60) -> Optional[subprocess.CompletedProcess]:
    try:
        return subprocess.run(
            ["git", "-C", cwd, *args], capture_output=True, text=True,
            env=_git_env(), timeout=timeout,
        )
    except Exception:
        return None


def scan_process_references(paths: List[str], *, proc_root: str = "/proc") -> Dict[str, Any]:
    """Read-only /proc scan for process CWD/FD references into any of *paths*."""
    refs: Dict[str, Dict[str, List[str]]] = {}
    inaccessible = {"cwd": 0, "fd_dir": 0, "fd_link": 0}
    processes = 0
    try:
        for entry in os.scandir(proc_root):
            if not entry.name.isdigit():
                continue
            processes += 1
            base = os.path.join(proc_root, entry.name)
            try:
                target = os.readlink(os.path.join(base, "cwd"))
            except PermissionError:
                inaccessible["cwd"] += 1
                target = None
            except OSError:
                target = None
            if target:
                for p in paths:
                    if target == p or target.startswith(p + os.sep):
                        refs.setdefault(p, {"cwd": [], "fd": []})["cwd"].append(entry.name)
                        break
            try:
                fd_iter = os.scandir(os.path.join(base, "fd"))
            except PermissionError:
                inaccessible["fd_dir"] += 1
                continue
            except OSError:
                continue
            try:
                with fd_iter:
                    for fd in fd_iter:
                        try:
                            target = os.readlink(fd.path)
                        except PermissionError:
                            inaccessible["fd_link"] += 1
                            continue
                        except OSError:
                            continue
                        if not target.startswith("/") or target.endswith(" (deleted)"):
                            continue
                        for p in paths:
                            if target == p or target.startswith(p + os.sep):
                                refs.setdefault(p, {"cwd": [], "fd": []})["fd"].append(entry.name)
                                break
            except OSError:
                pass
    except OSError:
        pass
    return {"refs": refs, "processes": processes, "inaccessible": inaccessible}


def collect_references(
    paths: List[str],
    sources: Sequence[os.PathLike | str],
    *,
    max_files: int = _DEFAULT_MAX_REFERENCE_FILES,
    max_total_bytes: int = _DEFAULT_MAX_REFERENCE_BYTES,
    exclude_dirs: Sequence[os.PathLike | str] = (),
) -> Dict[str, List[str]]:
    """Bounded read-only substring search for exact worktree paths inside *sources*.

    ``exclude_dirs`` prunes subtrees that must not count as references — in
    particular this gate's own state directory, whose registry contains every
    path and would otherwise self-reference the whole pool.
    """
    found: Dict[str, List[str]] = {}
    excludes = [str(Path(e).expanduser()) for e in exclude_dirs]

    def _excluded(value: str) -> bool:
        return any(value == e or value.startswith(e + os.sep) for e in excludes)

    files_read = 0
    bytes_read = 0
    stack: List[Tuple[Path, int]] = [(Path(s).expanduser(), 0) for s in sources]
    while stack and files_read < max_files and bytes_read < max_total_bytes:
        current, depth = stack.pop(0)
        if _excluded(str(current)):
            continue
        try:
            if current.is_file():
                candidates = [current]
            elif current.is_dir() and depth <= 3:
                candidates = [p for p in sorted(current.iterdir()) if p.suffix.lower() in _REFERENCE_EXTENSIONS or (p.is_dir() and depth < 3)]
            else:
                candidates = []
        except OSError:
            continue
        for cand in candidates:
            if files_read >= max_files or bytes_read >= max_total_bytes:
                break
            if _excluded(str(cand)):
                continue
            try:
                if cand.is_dir():
                    stack.append((cand, depth + 1))
                    continue
                if cand.suffix.lower() not in _REFERENCE_EXTENSIONS:
                    continue
                data = cand.read_bytes()
            except OSError:
                continue
            files_read += 1
            bytes_read += len(data)
            text = data.decode("utf-8", errors="replace")
            for p in paths:
                if p in text:
                    found.setdefault(p, []).append(str(cand))
    return found


def default_reference_sources() -> List[str]:
    """Bounded authoritative-source set for live scans (read-only)."""
    sources: List[str] = []
    for candidate in (
        Path(os.environ.get("HOME", "/home/can")) / ".config" / "systemd" / "user",
        CENTRAL_WORKTREE_ROOT.parent / "flowbot" / "releases" / "ops_api" / "current",
        Path(os.environ.get("HOME", "/home/can")) / ".hermes" / "state",
    ):
        if candidate.exists():
            sources.append(str(candidate))
    return sources


# ---------------------------------------------------------------------------
# Scanner
# ---------------------------------------------------------------------------


def _python_tree_bytes(root: Path) -> int:
    total = 0
    stack = [root]
    while stack:
        current = stack.pop()
        try:
            it = os.scandir(current)
        except OSError:
            continue
        with it:
            for entry in it:
                try:
                    st = entry.stat(follow_symlinks=False)
                except OSError:
                    continue
                if stat.S_ISLNK(st.st_mode):
                    continue
                if stat.S_ISDIR(st.st_mode):
                    blocks = getattr(st, "st_blocks", 0) or 0
                    total += blocks * 512
                    stack.append(Path(entry.path))
                elif stat.S_ISREG(st.st_mode):
                    blocks = getattr(st, "st_blocks", 0) or 0
                    total += blocks * 512 if blocks else st.st_size
    return total


def _birthtimes_epoch(paths: List[str]) -> Dict[str, float]:
    """Best-effort creation-time (ext4 birth) per path; ``stat`` CLI fallback for py<3.12."""
    result: Dict[str, float] = {}
    missing: List[str] = []
    for p in paths:
        try:
            st = os.stat(p, follow_symlinks=False)
            born = getattr(st, "st_birthtime", None)
        except OSError:
            born = None
        if born:
            result[p] = float(born)
        else:
            missing.append(p)
    if not missing:
        return result
    exe = shutil.which("stat")
    if not exe:
        return result
    attempts = (
        [exe, "-c", "%W\t%n", "--", *missing],  # GNU coreutils
        [exe, "-f", "%B\t%N", *missing],  # BSD / macOS
    )
    for argv in attempts:
        try:
            proc = subprocess.run(argv, capture_output=True, text=True, timeout=120)
        except Exception:
            continue
        if proc.returncode != 0:
            continue
        for line in proc.stdout.splitlines():
            try:
                value, name = line.split("\t", 1)
                epoch = int(value)
            except (ValueError, TypeError):
                continue
            if epoch > 0:
                result[name] = float(epoch)
        break
    return result


def _du_walk(root: str, *, timeout: float = 900) -> Optional[Dict[str, int]]:
    """One ``du --max-depth=1`` walk of *root*: per-child + total allocation."""
    exe = shutil.which("du")
    if not exe:
        return None
    try:
        proc = subprocess.run([exe, "-x", "-B1", "--max-depth=1", "--", root], capture_output=True, text=True, timeout=timeout)
    except Exception:
        return None
    sizes: Dict[str, int] = {}
    for line in proc.stdout.splitlines():
        try:
            size, path = line.split("\t", 1)
            sizes[path] = int(size)
        except ValueError:
            continue
    return sizes or None


def _probe_candidate(path: str, marker_type: str) -> Dict[str, Any]:
    facts: Dict[str, Any] = {
        "path": path,
        "marker": marker_type,
        "common_dir": None,
        "head": None,
        "branch": None,
        "detached": None,
        "dirty": None,
        "untracked_count": None,
        "tracked_change_count": None,
        "unresolvable": True,
        "unborn_head": False,
    }
    if marker_type != "gitfile" and marker_type != "git-dir":
        return facts
    rev = _run_git(["rev-parse", "--path-format=absolute", "--git-common-dir"], path, timeout=90)
    if rev is None or rev.returncode != 0 or not rev.stdout.strip():
        return facts
    facts["common_dir"] = rev.stdout.strip().splitlines()[0].strip()
    facts["unresolvable"] = False
    head = _run_git(["rev-parse", "HEAD"], path, timeout=60)
    if head is not None and head.returncode == 0 and head.stdout.strip():
        facts["head"] = head.stdout.strip()
    else:
        # Repo structure resolves but HEAD has no commit (fresh `git init` tree).
        facts["unborn_head"] = True
    branch = _run_git(["symbolic-ref", "-q", "--short", "HEAD"], path, timeout=60)
    if branch is not None and branch.returncode == 0:
        facts["branch"] = branch.stdout.strip()
        facts["detached"] = False
    else:
        facts["branch"] = None
        facts["detached"] = True
    status = _run_git(["status", "--porcelain=v1", "--untracked-files=all"], path, timeout=120)
    if status is not None and status.returncode == 0:
        entries = status.stdout.splitlines()
        facts["dirty"] = bool(entries)
        facts["untracked_count"] = sum(1 for e in entries if e.startswith("??"))
        facts["tracked_change_count"] = sum(1 for e in entries if not e.startswith("??"))
    else:
        facts["unresolvable"] = True
    return facts


def scan_central_worktrees(
    central_root: Optional[os.PathLike | str] = None,
    state_dir: Optional[os.PathLike | str] = None,
    *,
    process_refs: Optional[Dict[str, Dict[str, List[str]]]] = None,
    references: Optional[Dict[str, List[str]]] = None,
    use_du: Optional[bool] = None,
    now: Optional[float] = None,
    max_workers: Optional[int] = None,
    write: bool = True,
) -> Dict[str, Any]:
    """Read-only scan of the central worktree pool.  Performs NO retirement.

    ``process_refs`` / ``references`` may be injected (tests, callers with their
    own collectors); otherwise live collectors run.  ``write=True`` updates the
    registry (backfilling ``UNKNOWN_CREATION`` records) and appends a snapshot;
    ``write=False`` is a pure read for reports.
    """
    started = time.time()
    now_ts = now if now is not None else started
    root = _central_root(central_root)
    state = _state_dir(state_dir)
    workers = max_workers or min(_DEFAULT_SCAN_WORKERS, (os.cpu_count() or 4))

    direct_children = 0
    candidates: List[str] = []
    markers: Dict[str, str] = {}
    try:
        with os.scandir(root) as it:
            for entry in it:
                direct_children += 1
                try:
                    if not entry.is_dir(follow_symlinks=False):
                        continue
                    git_marker = os.path.join(entry.path, ".git")
                    if not os.path.lexists(git_marker):
                        continue
                    st = os.lstat(git_marker)
                    markers[entry.path] = "git-dir" if stat.S_ISDIR(st.st_mode) else (
                        "gitfile" if stat.S_ISREG(st.st_mode) else "other")
                    candidates.append(entry.path)
                except OSError:
                    continue
    except OSError:
        pass
    candidates.sort()

    with ThreadPoolExecutor(max_workers=workers) as pool:
        facts_list = list(pool.map(lambda p: _probe_candidate(p, markers.get(p, "other")), candidates))

    # Sizes.
    root_total: Optional[int] = None
    size_map: Dict[str, int] = {}
    if use_du is not False:
        du_map = _du_walk(str(root))
        if du_map:
            root_total = du_map.get(str(root))
            if all(p in du_map for p in candidates):
                size_map = {p: int(du_map[p]) for p in candidates}
    size_method = "du" if size_map else "python_walk"
    if not size_map:
        size_map = {p: _python_tree_bytes(Path(p)) for p in candidates}
        if root_total is None:
            root_total = sum(size_map.values())

    facts_by_path = {f["path"]: f for f in facts_list}

    # Registration: one worktree-list per common repository.
    registered: Dict[str, bool] = {}
    standalone: Dict[str, bool] = {}
    commons = sorted({f["common_dir"] for f in facts_list if f.get("common_dir")})
    for common in commons:
        repo = os.path.dirname(common) if common.endswith(os.sep + ".git") else common
        listing = _run_git(["worktree", "list", "--porcelain"], repo, timeout=120)
        paths_in_repo: set = set()
        if listing is not None and listing.returncode == 0:
            for line in listing.stdout.splitlines():
                if line.startswith("worktree "):
                    paths_in_repo.add(os.path.normpath(line[len("worktree "):]))
        for f in facts_list:
            if f.get("common_dir") == common:
                p = f["path"]
                registered[p] = p in paths_in_repo
                standalone[p] = os.path.normpath(repo) == os.path.normpath(p)
    for f in facts_list:
        if f.get("common_dir") is None:
            registered[f["path"]] = False
            standalone[f["path"]] = False

    # Unpinned detached HEADs: one for-each-ref per (common, head).
    detached = [f for f in facts_list if f.get("detached") and f.get("head") and f.get("common_dir")]
    ref_cache: Dict[Tuple[str, str], bool] = {}

    def _has_containing_ref(common: str, head: str) -> bool:
        key = (common, head)
        if key in ref_cache:
            return ref_cache[key]
        repo = os.path.dirname(common) if common.endswith(os.sep + ".git") else common
        result = _run_git(["for-each-ref", "--contains=" + head, "--format=%(refname:short)"], repo, timeout=120)
        has = bool(result is not None and result.returncode == 0 and result.stdout.strip())
        ref_cache[key] = has
        return has

    unpinned: Dict[str, bool] = {}
    if detached:
        with ThreadPoolExecutor(max_workers=workers) as pool:
            results = list(pool.map(lambda f: _has_containing_ref(f["common_dir"], f["head"]), detached))
        for f, has_ref in zip(detached, results):
            unpinned[f["path"]] = not has_ref

    # Same-HEAD duplicate groups.
    head_groups: Dict[Tuple[str, str], List[str]] = {}
    for f in facts_list:
        if f.get("common_dir") and f.get("head"):
            head_groups.setdefault((f["common_dir"], f["head"]), []).append(f["path"])
    duplicate_members: Dict[str, bool] = {}
    duplicate_group_count = 0
    for key, members in head_groups.items():
        if len(members) > 1:
            duplicate_group_count += 1
            for m in members:
                duplicate_members[m] = True

    # Process references + references.
    if process_refs is None:
        proc_scan = scan_process_references(candidates)
        process_refs = proc_scan["refs"]
        proc_stats = {k: proc_scan[k] for k in ("processes", "inaccessible")}
    else:
        proc_stats = {"processes": None, "inaccessible": None}
    if references is None:
        references = collect_references(
            candidates, default_reference_sources(), exclude_dirs=[str(state)],
        )
    process_refs = process_refs or {}
    references = references or {}

    # Registry + leases.
    registry = _load_registry(state)
    records = registry.setdefault("records", {})
    scan_ts_iso = _now_iso(now_ts)

    counts = {
        "total_count": len(candidates),
        "registered_count": 0,
        "unregistered_count": 0,
        "dirty_count": 0,
        "clean_count": 0,
        "unresolvable_count": 0,
        "unborn_head_count": 0,
        "unowned_count": 0,
        "owned_count": 0,
        "active_lease_count": 0,
        "expired_lease_count": 0,
        "missing_lease_count": 0,
        "unpinned_detached_count": 0,
        "active_process_ref_count": 0,
        "referenced_count": 0,
        "unknown_creation_count": 0,
    }
    bytes_acc = {
        "dirty_bytes": 0,
        "clean_bytes": 0,
        "allocated_bytes": 0,
        "same_head_duplicate_bytes": 0,
        "unowned_bytes": 0,
        "expired_lease_bytes": 0,
        "unpinned_detached_bytes": 0,
    }
    policy_counts: Dict[str, int] = {code: 0 for code in POLICY_CODE_ORDER}
    duplicate_path_count = 0
    now_cutoff = now_ts - 86400

    for f in facts_list:
        p = f["path"]
        size = int(size_map.get(p, 0))
        bytes_acc["allocated_bytes"] += size
        is_registered = bool(registered.get(p))
        counts["registered_count" if is_registered else "unregistered_count"] += 1
        if f.get("unresolvable"):
            counts["unresolvable_count"] += 1
        if f.get("unborn_head"):
            counts["unborn_head_count"] += 1
        if f.get("dirty"):
            counts["dirty_count"] += 1
            bytes_acc["dirty_bytes"] += size
        elif f.get("dirty") is False:
            counts["clean_count"] += 1
            bytes_acc["clean_bytes"] += size
        in_dup = bool(duplicate_members.get(p))
        if in_dup:
            duplicate_path_count += 1
            bytes_acc["same_head_duplicate_bytes"] += size
        is_unpinned = bool(unpinned.get(p))
        if is_unpinned:
            counts["unpinned_detached_count"] += 1
            bytes_acc["unpinned_detached_bytes"] += size
        active_proc = bool(process_refs.get(p))
        if active_proc:
            counts["active_process_ref_count"] += 1
        is_referenced = bool(references.get(p))
        if is_referenced:
            counts["referenced_count"] += 1

        lease = lease_status_for_path(p, now=now_ts, state_dir=state)
        if lease["state"] == LEASE_ACTIVE:
            counts["active_lease_count"] += 1
        elif lease["state"] == LEASE_EXPIRED:
            counts["expired_lease_count"] += 1
            bytes_acc["expired_lease_bytes"] += size
        else:
            counts["missing_lease_count"] += 1

        existing_record = records.get(p)
        if existing_record is None:
            record = _new_record(p, mechanism=CLASS_UNKNOWN, now_ts=now_ts)
            creation = record["creation"]
            creation["source"] = "scanner_backfill"
            records[p] = record
        else:
            record = existing_record
        if record.get("creation", {}).get("mechanism") in (None, CLASS_UNKNOWN):
            counts["unknown_creation_count"] += 1
        owner = (record.get("owner") or {}).get("owner")
        if not owner and lease["state"] == LEASE_ACTIVE:
            # An active lease IS deterministic ownership evidence (issued via
            # issue_lease with an explicit owner); never invented otherwise.
            owner = lease.get("owner")
        if owner:
            counts["owned_count"] += 1
        else:
            counts["unowned_count"] += 1
            bytes_acc["unowned_bytes"] += size

        protection = []
        if f.get("dirty"):
            protection.append("dirty")
        if (f.get("untracked_count") or 0) > 0:
            protection.append("untracked_content")
        if active_proc:
            protection.append("active_process")
        if is_referenced:
            protection.append("referenced")
        if is_unpinned:
            protection.append("unpinned_detached_head")
        if f.get("unresolvable"):
            protection.append("unresolvable_head")
        if f.get("unborn_head"):
            protection.append("unborn_head")

        codes = _policy_codes(
            owner=owner,
            purpose=record.get("purpose"),
            lease_state=lease["state"],
            registered=is_registered,
            dirty=bool(f.get("dirty")),
            in_duplicate_group=in_dup,
            unpinned_detached=is_unpinned,
            unresolvable=bool(f.get("unresolvable")) or bool(f.get("unborn_head")),
            existing_path_observed=bool(record.get("creation", {}).get("existing_path_observed")),
        )
        for code in codes:
            policy_counts[code] += 1

        record["repo"] = {
            "common_dir": f.get("common_dir"),
            "identity": _repo_identity(f.get("common_dir"), p),
            "head": f.get("head"),
            "branch": f.get("branch"),
            "detached": f.get("detached"),
            "registered": is_registered,
            "standalone_repo": bool(standalone.get(p)),
        }
        record["lease"] = {"lease_id": lease.get("lease_id"), "state": lease["state"],
                           "expires_at": lease.get("expires_at")}
        record["scan"] = {
            "last_scan_at": scan_ts_iso,
            "present": True,
            "allocated_bytes": size,
            "dirty": f.get("dirty"),
            "untracked_count": f.get("untracked_count"),
            "tracked_change_count": f.get("tracked_change_count"),
            "active_process_refs": process_refs.get(p),
            "referenced_by": references.get(p),
            "unpinned_detached": is_unpinned,
            "unresolvable": bool(f.get("unresolvable")),
            "unborn_head": bool(f.get("unborn_head")),
            "duplicate_same_head_group": in_dup,
            "size_method": size_method,
        }
        record["protection"] = protection
        record["policy_codes"] = codes
        record["lifecycle_status"] = _lifecycle_status(lease["state"])
        record["cleanup_policy"] = {"mode": CLEANUP_POLICY_SHADOW_ONLY, "retirement_authorized": False}
        record["updated_at"] = scan_ts_iso

    stale_records = sum(1 for rp in records if rp not in set(candidates))

    # Creations in 24h: registry events when present, else ext4 birth-time proxy.
    creations_events = 0
    events_path = state / _EVENTS_NAME
    try:
        if events_path.exists():
            with open(events_path, "r", encoding="utf-8", errors="replace") as handle:
                for line in handle:
                    try:
                        event = json.loads(line)
                    except ValueError:
                        continue
                    if (
                        event.get("event") == "creation_observed"
                        and event.get("central_record_created")
                        and float(event.get("ts_epoch") or 0) > 0
                        and float(event["ts_epoch"]) >= now_cutoff
                    ):
                        creations_events += 1
    except OSError:
        pass
    birthtimes = _birthtimes_epoch(candidates)
    birthtime_proxy = sum(1 for p in candidates if birthtimes.get(p, 0) >= now_cutoff)
    creations_24h = creations_events if creations_events else birthtime_proxy
    creations_basis = "registry_events" if creations_events else "ext4_birthtime_proxy"

    # Snapshot delta (previous run), then append the new snapshot.
    previous_snapshot = None
    snapshots_path = state / _SNAPSHOTS_NAME
    try:
        if snapshots_path.exists():
            with open(snapshots_path, "r", encoding="utf-8", errors="replace") as handle:
                for line in handle:
                    try:
                        previous_snapshot = json.loads(line)
                    except ValueError:
                        continue
    except OSError:
        previous_snapshot = None
    net_count = None
    net_bytes = None
    if isinstance(previous_snapshot, dict):
        try:
            net_count = counts["total_count"] - int(previous_snapshot.get("total_count") or 0)
            net_bytes = bytes_acc["allocated_bytes"] - int(previous_snapshot.get("allocated_bytes") or 0)
        except (TypeError, ValueError):
            net_count = net_bytes = None

    report: Dict[str, Any] = {
        "schema": "hermes.central-worktrees.scan.v1",
        "scanned_at": scan_ts_iso,
        "central_root": str(root),
        "state_dir": str(state),
        "direct_children": direct_children,
        "total_count": counts["total_count"],
        "allocated_bytes": bytes_acc["allocated_bytes"],
        "allocated_gb": round(bytes_acc["allocated_bytes"] / 1e9, 3),
        "root_total_allocated_bytes": root_total,
        "root_total_allocated_gb": round(root_total / 1e9, 3) if root_total else None,
        "registered_count": counts["registered_count"],
        "unregistered_count": counts["unregistered_count"],
        "dirty_count": counts["dirty_count"],
        "dirty_gb": round(bytes_acc["dirty_bytes"] / 1e9, 3),
        "clean_count": counts["clean_count"],
        "clean_gb": round(bytes_acc["clean_bytes"] / 1e9, 3),
        "unresolvable_count": counts["unresolvable_count"],
        "unborn_head_count": counts["unborn_head_count"],
        "same_head_duplicate_group_count": duplicate_group_count,
        "same_head_duplicate_count": duplicate_path_count,
        "same_head_duplicate_gb": round(bytes_acc["same_head_duplicate_bytes"] / 1e9, 3),
        "unowned_count": counts["unowned_count"],
        "unowned_gb": round(bytes_acc["unowned_bytes"] / 1e9, 3),
        "owned_count": counts["owned_count"],
        "active_lease_count": counts["active_lease_count"],
        "expired_lease_count": counts["expired_lease_count"],
        "expired_lease_gb": round(bytes_acc["expired_lease_bytes"] / 1e9, 3),
        "missing_lease_count": counts["missing_lease_count"],
        "unpinned_detached_count": counts["unpinned_detached_count"],
        "unpinned_detached_gb": round(bytes_acc["unpinned_detached_bytes"] / 1e9, 3),
        "active_process_ref_count": counts["active_process_ref_count"],
        "active_process_refs": process_refs,
        "referenced_count": counts["referenced_count"],
        "creations_24h": creations_24h,
        "creations_24h_basis": creations_basis,
        "creations_24h_events": creations_events,
        "creations_24h_birthtime_proxy": birthtime_proxy,
        "retirements_24h": 0,
        "retirements_24h_basis": "NO_RETIREMENT_MECHANISM_ACTIVE",
        "net_count_delta_since_previous_snapshot": net_count,
        "net_bytes_delta_since_previous_snapshot": net_bytes,
        "unknown_creation_count": counts["unknown_creation_count"],
        "registry_records_total": len(records),
        "registry_paths_not_present": stale_records,
        "policy_code_counts": {k: v for k, v in policy_counts.items() if v},
        "process_scan_stats": proc_stats,
        "size_method": size_method,
        "scan_seconds": round(time.time() - started, 2),
    }

    if write:
        with _locked(state):
            registry["updated_at"] = scan_ts_iso
            _atomic_write_json(state / _REGISTRY_NAME, registry)
            _append_jsonl(snapshots_path, {
                "ts": scan_ts_iso,
                "ts_epoch": now_ts,
                "total_count": counts["total_count"],
                "allocated_bytes": bytes_acc["allocated_bytes"],
                "dirty_count": counts["dirty_count"],
                "clean_count": counts["clean_count"],
                "unowned_count": counts["unowned_count"],
                "expired_lease_count": counts["expired_lease_count"],
                "unpinned_detached_count": counts["unpinned_detached_count"],
            })
    return report


def format_report(report: Dict[str, Any]) -> str:
    """Compact human-readable scan summary (no mutation of *report*)."""
    lines = [
        f"central worktrees @ {report.get('central_root')} ({report.get('scanned_at')})",
        f"count={report.get('total_count')} allocated={report.get('allocated_gb')}GB"
        f" (root_total={report.get('root_total_allocated_gb')}GB)",
        f"registered={report.get('registered_count')} unregistered={report.get('unregistered_count')}"
        f" unresolvable={report.get('unresolvable_count')} unborn={report.get('unborn_head_count')}",
        f"dirty={report.get('dirty_count')} ({report.get('dirty_gb')}GB)"
        f" clean={report.get('clean_count')} ({report.get('clean_gb')}GB)",
        f"same_head_duplicates: groups={report.get('same_head_duplicate_group_count')}"
        f" paths={report.get('same_head_duplicate_count')} ({report.get('same_head_duplicate_gb')}GB)",
        f"unowned={report.get('unowned_count')} ({report.get('unowned_gb')}GB)"
        f" leased={report.get('active_lease_count')} expired_leases={report.get('expired_lease_count')}",
        f"unpinned_detached={report.get('unpinned_detached_count')} ({report.get('unpinned_detached_gb')}GB)",
        f"active_process_refs={report.get('active_process_ref_count')} referenced={report.get('referenced_count')}",
        f"creations_24h={report.get('creations_24h')} ({report.get('creations_24h_basis')})"
        f" retirements_24h={report.get('retirements_24h')} ({report.get('retirements_24h_basis')})",
        f"net_movement: count={report.get('net_count_delta_since_previous_snapshot')}"
        f" bytes={report.get('net_bytes_delta_since_previous_snapshot')}",
        f"policy_codes={report.get('policy_code_counts')}",
    ]
    return "\n".join(lines)


# ---------------------------------------------------------------------------
# CLI
# ---------------------------------------------------------------------------


def main(argv: Optional[List[str]] = None) -> int:
    parser = argparse.ArgumentParser(description="Central worktree lifecycle gate V1 (shadow-only)")
    sub = parser.add_subparsers(dest="cmd", required=True)

    p_scan = sub.add_parser("scan", help="read-only scan of the central worktree pool")
    p_scan.add_argument("--central-root", default=None)
    p_scan.add_argument("--state-dir", default=None)
    p_scan.add_argument("--json", action="store_true")
    p_scan.add_argument("--read-only", action="store_true", help="do not update registry/snapshot")
    p_scan.add_argument("--workers", type=int, default=None)

    p_show = sub.add_parser("show", help="print one registry record")
    p_show.add_argument("path")
    p_show.add_argument("--state-dir", default=None)

    p_issue = sub.add_parser("lease-issue", help="issue a renewable ownership lease")
    p_issue.add_argument("path")
    p_issue.add_argument("--owner", required=True)
    p_issue.add_argument("--mission", default=None)
    p_issue.add_argument("--session", default=None)
    p_issue.add_argument("--ttl", type=int, default=DEFAULT_LEASE_TTL_SECONDS)
    p_issue.add_argument("--state-dir", default=None)

    p_renew = sub.add_parser("lease-renew", help="renew a lease by id")
    p_renew.add_argument("lease_id")
    p_renew.add_argument("--ttl", type=int, default=None)
    p_renew.add_argument("--state-dir", default=None)

    args = parser.parse_args(argv)
    if args.cmd == "scan":
        report = scan_central_worktrees(
            args.central_root, args.state_dir, max_workers=args.workers, write=not args.read_only,
        )
        if args.json:
            print(json.dumps(report, indent=2))
        else:
            print(format_report(report))
        return 0
    if args.cmd == "show":
        state = _state_dir(args.state_dir)
        record = _load_registry(state)["records"].get(_norm_path(args.path))
        print(json.dumps(record, indent=2) if record else "no record")
        return 0 if record else 1
    if args.cmd == "lease-issue":
        lease = issue_lease(
            args.path, owner=args.owner, mission_id=args.mission, session_id=args.session,
            ttl_seconds=args.ttl, state_dir=args.state_dir,
        )
        print(json.dumps(lease, indent=2))
        return 0
    if args.cmd == "lease-renew":
        lease = renew_lease(args.lease_id, ttl_seconds=args.ttl, state_dir=args.state_dir)
        if lease is None:
            print("unknown lease id")
            return 1
        print(json.dumps(lease, indent=2))
        return 0
    return 2


if __name__ == "__main__":  # pragma: no cover
    sys.exit(main())
