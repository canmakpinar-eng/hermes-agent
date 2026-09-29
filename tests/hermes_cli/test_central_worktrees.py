"""Tests for the Central Worktree Lifecycle Gate V1 (SHADOW ONLY).

Covers the mission acceptance list: managed creation, raw terminal
``git worktree add`` to the central root (the key acceptance), repo-local
``.worktrees`` creation, creation outside the central root, dirty/clean trees,
same-HEAD duplicates, detached pinned vs unpinned HEADs, missing owner,
missing/expired leases, referenced trees, and active-process trees.

Every test is hermetic: ``central_root`` and ``state_dir`` always point into
``tmp_path``; nothing touches the real pool at /home/can/worktrees, no command
is ever refused, and nothing is ever removed.
"""

from __future__ import annotations

import json
import os
import subprocess
import sys
from pathlib import Path
from types import SimpleNamespace

import pytest

sys.path.insert(0, os.path.abspath(os.path.join(os.path.dirname(__file__), "..", "..")))

from hermes_cli import central_worktrees as cw  # noqa: E402


# ---------------------------------------------------------------------------
# Fixtures / helpers
# ---------------------------------------------------------------------------


def _git(args, cwd):
    return subprocess.run(["git", *args], cwd=str(cwd), capture_output=True, text=True)


def _make_repo(root: Path) -> Path:
    repo = root / "repo"
    repo.mkdir()
    _git(["init", "-q", "-b", "main"], repo)
    _git(["config", "user.email", "test@test"], repo)
    _git(["config", "user.name", "Test"], repo)
    (repo / "README.md").write_text("hello\n", encoding="utf-8")
    _git(["add", "-A"], repo)
    _git(["commit", "-q", "-m", "seed"], repo)
    return repo


def _wt(repo: Path, dest: Path, branch: str = None, detach: bool = False, commit: str = None) -> Path:
    args = ["worktree", "add"]
    if detach:
        args.append("--detach")
    args.append(str(dest))
    if branch:
        args += ["-b", branch]
    if commit:
        args.append(commit)
    result = _git(args, repo)
    assert result.returncode == 0, result.stderr
    return dest


@pytest.fixture
def sandbox(tmp_path):
    repo = _make_repo(tmp_path)
    central = tmp_path / "central"
    central.mkdir()
    state = tmp_path / "state"
    return {"repo": repo, "central": central, "state": state, "tmp": tmp_path}


def _scan(sandbox, **kwargs):
    report = cw.scan_central_worktrees(
        sandbox["central"], sandbox["state"],
        process_refs=kwargs.pop("process_refs", {}),
        references=kwargs.pop("references", {}),
        use_du=False,
        **kwargs,
    )
    return report


def _registry(sandbox):
    return json.loads((sandbox["state"] / "registry.json").read_text(encoding="utf-8"))


def _events(sandbox):
    path = sandbox["state"] / "events.jsonl"
    if not path.exists():
        return []
    return [json.loads(line) for line in path.read_text(encoding="utf-8").splitlines() if line.strip()]


def _codes(record):
    return set(record.get("policy_codes") or [])


# ---------------------------------------------------------------------------
# Classifier
# ---------------------------------------------------------------------------


def test_classifier_resolves_effective_destination(sandbox):
    repo, central = sandbox["repo"], sandbox["central"]
    cwd = str(sandbox["tmp"])

    info = cw.classify_terminal_command(f"git worktree add {central}/x -b b1 HEAD", cwd=cwd)
    assert info["kind"] == "worktree_add" and info["dest"] == str(central / "x")
    assert info["new_branch"] == "b1" and info["base_revision"] == "HEAD"

    info = cw.classify_terminal_command(f"git worktree add -b b2 {central}/y HEAD", cwd=cwd)
    assert info["kind"] == "worktree_add" and info["dest"] == str(central / "y")

    info = cw.classify_terminal_command(f"git -C {repo} worktree add ../central/z -b b3", cwd="/elsewhere")
    assert info["kind"] == "worktree_add" and info["dest"] == str(central / "z")

    info = cw.classify_terminal_command(f"cd {repo} && git worktree add ../central/w -b b4", cwd=cwd)
    assert info["kind"] == "worktree_add" and info["dest"] == str(central / "w")

    info = cw.classify_terminal_command(f"bash -c 'cd {repo} && git worktree add ../central/v -b b5'", cwd=cwd)
    assert info["kind"] == "worktree_add" and info["dest"] == str(central / "v")

    info = cw.classify_terminal_command(f"env FOO=1 nohup timeout 30 git worktree add {central}/u --detach", cwd=cwd)
    assert info["kind"] == "worktree_add" and info["dest"] == str(central / "u") and info["detached"] is True


def test_classifier_rejects_non_creations_and_unknown_dest(sandbox):
    cwd = str(sandbox["tmp"])
    assert cw.classify_terminal_command("git worktree list", cwd=cwd)["kind"] == "not_worktree_add"
    assert cw.classify_terminal_command("git worktree remove /tmp/x", cwd=cwd)["kind"] == "not_worktree_add"
    assert cw.classify_terminal_command("echo git worktree add /nope", cwd=cwd)["kind"] == "not_worktree_add"
    assert cw.classify_terminal_command("git worktree add", cwd=cwd)["kind"] == "worktree_add_unknown_dest"
    info = cw.classify_terminal_command("git worktree add $DEST -b b", cwd=cwd)
    assert info["kind"] == "worktree_add_unknown_dest"
    info = cw.classify_terminal_command("bash -c 'git worktree add rel'", cwd=None)
    assert info["kind"] == "worktree_add_unknown_dest" and info["reason"] == "relative_dest_cwd_unknown"
    assert cw.classify_terminal_command(None)["kind"] == "not_worktree_add"
    assert cw.classify_terminal_command(12345)["kind"] == "not_worktree_add"


# ---------------------------------------------------------------------------
# Raw terminal observation (the key acceptance path)
# ---------------------------------------------------------------------------


def test_raw_central_worktree_creation_observed_end_to_end(sandbox):
    """RAW_CENTRAL_WORKTREE_CREATION_OBSERVED: a raw terminal ``git worktree add``
    aimed at the central root is observed, recorded, and then really executes."""
    repo, central, state = sandbox["repo"], sandbox["central"], sandbox["state"]
    dest = central / "raw1"
    command = f"git -C {repo} worktree add {dest} -b raw1 HEAD"

    result = cw.observe_terminal_command(
        command, cwd=str(repo), session_id="sess-raw-1", state_dir=state, central_root=str(central),
    )
    assert result is not None
    assert result["classification"] == cw.CLASS_RAW_CENTRAL
    assert result["central_record_created"] is True
    assert result["dest"] == str(dest)

    # The command really executes and lands where the observer said it would.
    run = _git(["worktree", "add", str(dest), "-b", "raw1", "HEAD"], repo)
    assert run.returncode == 0, run.stderr
    assert dest.is_dir()

    record = _registry(sandbox)["records"][str(dest)]
    assert record["creation"]["mechanism"] == cw.CLASS_RAW_CENTRAL
    assert record["creation"]["command_fingerprint"].startswith("sha256:")
    assert record["creation"]["session_id"] == "sess-raw-1"
    assert record["cleanup_policy"]["mode"] == cw.CLEANUP_POLICY_SHADOW_ONLY
    assert record["cleanup_policy"]["retirement_authorized"] is False
    assert record["lifecycle_status"] == cw.STATUS_ORPHAN_REVIEW

    observed = [e for e in _events(sandbox) if e.get("classification") == cw.CLASS_RAW_CENTRAL]
    assert observed and observed[0]["path"] == str(dest)
    assert observed[0]["command_fingerprint"] == record["creation"]["command_fingerprint"]


def test_raw_central_observed_via_cd_and_relative_dest(sandbox):
    repo, central, state = sandbox["repo"], sandbox["central"], sandbox["state"]
    command = f"cd {repo} && git worktree add ../central/rel1 -b rel1"
    result = cw.observe_terminal_command(
        command, cwd=str(sandbox["tmp"]), state_dir=state, central_root=str(central),
    )
    assert result["classification"] == cw.CLASS_RAW_CENTRAL
    assert result["dest"] == str(central / "rel1")


def test_managed_central_creation_observed(sandbox):
    repo, central, state = sandbox["repo"], sandbox["central"], sandbox["state"]
    result = cw.observe_managed_creation(
        str(central / "managed1"), repo_root=str(repo), branch="mission/m1",
        creator="hermes-cli-worktree", session_id="sess-m", state_dir=state, central_root=str(central),
    )
    assert result["classification"] == cw.CLASS_MANAGED
    assert result["central_record_created"] is True
    record = _registry(sandbox)["records"][str(central / "managed1")]
    assert record["creation"]["mechanism"] == cw.CLASS_MANAGED
    assert record["creation"]["creator"]["kind"] == "managed"


def test_repo_local_and_outside_creations_are_not_recorded(sandbox):
    repo, central, state = sandbox["repo"], sandbox["central"], sandbox["state"]

    # Managed repo-local creation (the hermes -w / kanban / subagent default).
    result = cw.observe_managed_creation(
        str(repo / ".worktrees" / "hermes-abc123"), repo_root=str(repo),
        creator="hermes-cli-worktree", state_dir=state, central_root=str(central),
    )
    assert result["classification"] == cw.CLASS_MANAGED and result["central_record_created"] is False

    # Raw repo-local `.worktrees/` creation.
    info = cw.observe_terminal_command(
        f"git -C {repo} worktree add .worktrees/local1 -b local1", cwd=str(repo), state_dir=state,
        central_root=str(central),
    )
    assert info["classification"] == cw.CLASS_RAW_NON_CENTRAL and info["central_record_created"] is False

    # Raw creation outside the central root entirely.
    info = cw.observe_terminal_command(
        f"git worktree add {sandbox['tmp']}/elsewhere/z -b z1", cwd=str(repo), state_dir=state,
        central_root=str(central),
    )
    assert info["classification"] == cw.CLASS_RAW_NON_CENTRAL and info["central_record_created"] is False

    # None of the above wrote any state.
    assert not (state / "registry.json").exists()
    assert not (state / "events.jsonl").exists()


def test_unknown_destination_logs_unknown_event_only(sandbox):
    state = sandbox["state"]
    result = cw.observe_terminal_command(
        "git worktree add $DEST -b u1", cwd=str(sandbox["tmp"]), state_dir=state,
    )
    assert result["classification"] == cw.CLASS_UNKNOWN
    assert result["central_record_created"] is False
    assert _events(sandbox)[0]["classification"] == cw.CLASS_UNKNOWN
    assert not (state / "registry.json").exists()


def test_existing_central_path_warns(sandbox):
    central, state = sandbox["central"], sandbox["state"]
    (central / "already").mkdir()
    result = cw.observe_terminal_command(
        f"git worktree add {central}/already -b dup1", cwd=str(sandbox["repo"]), state_dir=state,
        central_root=str(central),
    )
    assert result["existing_path_observed"] is True
    record = _registry(sandbox)["records"][str(central / "already")]
    assert record["creation"]["existing_path_observed"] is True
    assert cw.WARN_EXISTING_CENTRAL_PATH in _codes(record)


def test_observer_never_raises_and_fast_paths_non_worktree_commands(sandbox):
    state = sandbox["state"]
    for bad in (None, 12345, b"bytes", "git worktree add 'unclosed", {"a": 1}):
        assert cw.observe_terminal_command(bad, cwd=str(sandbox["tmp"]), state_dir=state) is None
    assert cw.observe_terminal_command("echo hi", cwd=str(sandbox["tmp"]), state_dir=state) is None
    # Fast path never even creates the state directory.
    assert not state.exists()


# ---------------------------------------------------------------------------
# Scanner
# ---------------------------------------------------------------------------


def test_scanner_counts_dirty_clean_and_duplicates(sandbox):
    repo, central = sandbox["repo"], sandbox["central"]
    _wt(repo, central / "a", "wa")
    _wt(repo, central / "b", "wb")
    (central / "a" / "wip.txt").write_text("uncommitted\n", encoding="utf-8")

    report = _scan(sandbox)
    assert report["total_count"] == 2
    assert report["registered_count"] == 2 and report["unregistered_count"] == 0
    assert report["dirty_count"] == 1 and report["clean_count"] == 1
    assert report["same_head_duplicate_group_count"] == 1
    assert report["same_head_duplicate_count"] == 2
    assert report["unowned_count"] == 2 and report["owned_count"] == 0

    registry = _registry(sandbox)
    rec_a = registry["records"][str(central / "a")]
    rec_b = registry["records"][str(central / "b")]
    # Backfilled records carry the honest unknown mechanism.
    assert rec_a["creation"]["mechanism"] == cw.CLASS_UNKNOWN
    assert rec_b["creation"]["mechanism"] == cw.CLASS_UNKNOWN
    # Shadow policy: dirty duplicate escalates, the clean twin only warns.
    assert cw.ESCALATE_DIRTY_DUPLICATE in _codes(rec_a)
    assert cw.WARN_DUPLICATE_SAME_HEAD in _codes(rec_a)
    assert cw.WARN_DUPLICATE_SAME_HEAD in _codes(rec_b)
    assert cw.ESCALATE_DIRTY_DUPLICATE not in _codes(rec_b)
    assert cw.WARN_MISSING_OWNER in _codes(rec_a)
    assert cw.WARN_MISSING_LEASE in _codes(rec_a)
    # Protection flags never authorize anything.
    assert "dirty" in rec_a["protection"] and rec_a["cleanup_policy"]["retirement_authorized"] is False

    # A second scan reports net movement via snapshots.
    second = _scan(sandbox)
    assert second["net_count_delta_since_previous_snapshot"] == 0
    assert second["net_bytes_delta_since_previous_snapshot"] == 0
    assert second["retirements_24h"] == 0


def test_scanner_detached_pinned_vs_unpinned(sandbox):
    repo, central = sandbox["repo"], sandbox["central"]
    commit1 = _git(["rev-parse", "HEAD"], repo).stdout.strip()
    _wt(repo, central / "pin", detach=True, commit=commit1)

    (repo / "two.txt").write_text("two\n", encoding="utf-8")
    _git(["add", "-A"], repo)
    _git(["commit", "-q", "-m", "second"], repo)
    commit2 = _git(["rev-parse", "HEAD"], repo).stdout.strip()
    _wt(repo, central / "det", detach=True, commit=commit2)

    # Move the branch back so commit2 is reachable only through the worktree HEAD.
    moved = _git(["update-ref", "refs/heads/main", commit1], repo)
    assert moved.returncode == 0, moved.stderr

    report = _scan(sandbox)
    assert report["unpinned_detached_count"] == 1
    registry = _registry(sandbox)
    rec_det = registry["records"][str(central / "det")]
    rec_pin = registry["records"][str(central / "pin")]
    assert rec_det["scan"]["allocated_bytes"] > 0
    assert rec_det["scan"]["unpinned_detached"] is True
    assert cw.WARN_UNPINNED_DETACHED_HEAD in _codes(rec_det)
    assert rec_pin["scan"]["unpinned_detached"] is False
    assert cw.WARN_UNPINNED_DETACHED_HEAD not in _codes(rec_pin)


def test_scanner_flags_unresolvable_head(sandbox):
    central = sandbox["central"]
    broken = central / "broken"
    broken.mkdir()
    (broken / ".git").write_text("gitdir: /nonexistent/gitdir\n", encoding="utf-8")

    report = _scan(sandbox)
    assert report["unresolvable_count"] == 1
    record = _registry(sandbox)["records"][str(broken)]
    assert cw.ESCALATE_UNRESOLVABLE_HEAD in _codes(record)


def test_scanner_handles_unborn_head_standalone_repo(sandbox):
    central = sandbox["central"]
    fresh = central / "fresh"
    fresh.mkdir()
    init = subprocess.run(["git", "init", "-q", "-b", "main", str(fresh)], capture_output=True, text=True)
    assert init.returncode == 0, init.stderr

    report = _scan(sandbox)
    assert report["unborn_head_count"] == 1
    assert report["unresolvable_count"] == 0
    record = _registry(sandbox)["records"][str(fresh)]
    assert record["scan"]["unborn_head"] is True
    assert "unborn_head" in record["protection"]
    assert cw.ESCALATE_UNRESOLVABLE_HEAD in _codes(record)


def test_scanner_active_process_and_referenced_inputs(sandbox):
    repo, central = sandbox["repo"], sandbox["central"]
    _wt(repo, central / "live", "wl")

    report = cw.scan_central_worktrees(
        central, sandbox["state"],
        process_refs={str(central / "live"): {"cwd": ["4242"], "fd": []}},
        references={str(central / "live"): ["/etc/systemd/user/some.service"]},
        use_du=False,
    )
    assert report["active_process_ref_count"] == 1
    assert report["referenced_count"] == 1
    record = _registry(sandbox)["records"][str(central / "live")]
    assert "active_process" in record["protection"]
    assert "referenced" in record["protection"]
    assert record["scan"]["active_process_refs"] == {"cwd": ["4242"], "fd": []}
    assert record["scan"]["referenced_by"] == ["/etc/systemd/user/some.service"]


@pytest.mark.platforms("posix")
def test_process_scan_finds_cwd_and_fd_references(tmp_path):
    target = tmp_path / "central" / "tree"
    target.mkdir(parents=True)
    proc = tmp_path / "proc"
    pid_dir = proc / "4242"
    pid_dir.mkdir(parents=True)
    (pid_dir / "cwd").symlink_to(target)
    fd_dir = pid_dir / "fd"
    fd_dir.mkdir()
    (fd_dir / "7").symlink_to(target / "subdir")
    other = proc / "4243"
    other.mkdir()
    (other / "cwd").symlink_to(tmp_path / "elsewhere")

    result = cw.scan_process_references([str(target)], proc_root=str(proc))
    refs = result["refs"][str(target)]
    assert refs["cwd"] == ["4242"] and refs["fd"] == ["4242"]


def test_collect_references_is_bounded_substring_search(tmp_path):
    central = tmp_path / "central"
    (central / "alpha").mkdir(parents=True)
    target = str(central / "alpha")
    source = tmp_path / "receipt.md"
    source.write_text(f"TARGET = {target}\n", encoding="utf-8")
    no_hit = tmp_path / "other.md"
    no_hit.write_text("nothing here\n", encoding="utf-8")

    found = cw.collect_references([target], [str(source), str(no_hit)])
    assert found == {target: [str(source)]}


def test_collect_references_excludes_own_state(tmp_path):
    central = tmp_path / "central"
    (central / "alpha").mkdir(parents=True)
    target = str(central / "alpha")
    state = tmp_path / "state"
    state.mkdir()
    (state / "registry.json").write_text(json.dumps({"records": {target: {}}}), encoding="utf-8")

    # Without the exclusion the registry self-references the whole pool.
    assert cw.collect_references([target], [str(state)]) == {target: [str(state / "registry.json")]}
    assert cw.collect_references([target], [str(state)], exclude_dirs=[str(state)]) == {}


# ---------------------------------------------------------------------------
# Leases
# ---------------------------------------------------------------------------


def test_lease_lifecycle_and_policy_effects(sandbox):
    repo, central, state = sandbox["repo"], sandbox["central"], sandbox["state"]
    _wt(repo, central / "leased", "wlease")

    # Missing lease first: ORPHAN_REVIEW + warnings.
    report = _scan(sandbox, now=1000.0)
    record = _registry(sandbox)["records"][str(central / "leased")]
    assert record["lease"]["state"] == cw.LEASE_MISSING
    assert record["lifecycle_status"] == cw.STATUS_ORPHAN_REVIEW
    assert cw.WARN_MISSING_LEASE in _codes(record) and cw.WARN_MISSING_OWNER in _codes(record)

    # Issue a lease: ownership is established; PASS_REGISTERED_OWNER; LEASED.
    lease = cw.issue_lease(
        str(central / "leased"), owner="can", mission_id="m-1", ttl_seconds=3600,
        now=1000.0, state_dir=state,
    )
    report = _scan(sandbox, now=1500.0)
    record = _registry(sandbox)["records"][str(central / "leased")]
    assert report["active_lease_count"] == 1
    assert report["owned_count"] == 1 and report["unowned_count"] == 0
    assert record["lifecycle_status"] == cw.STATUS_LEASED
    assert cw.PASS_REGISTERED_OWNER in _codes(record)
    assert cw.WARN_MISSING_LEASE not in _codes(record)

    # Renewal keeps it alive past the original expiry...
    renewed = cw.renew_lease(lease["lease_id"], ttl_seconds=100, now=5000.0, state_dir=state)
    assert renewed["expires_at_epoch"] == 5100.0
    report = _scan(sandbox, now=5050.0)
    record = _registry(sandbox)["records"][str(central / "leased")]
    assert record["lease"]["state"] == cw.LEASE_ACTIVE

    # ...and an expired lease falls back to ORPHAN_REVIEW (never deletion).
    report = _scan(sandbox, now=5200.0)
    record = _registry(sandbox)["records"][str(central / "leased")]
    assert report["expired_lease_count"] == 1
    assert report["active_lease_count"] == 0
    assert record["lease"]["state"] == cw.LEASE_EXPIRED
    assert record["lifecycle_status"] == cw.STATUS_ORPHAN_REVIEW
    assert cw.WARN_MISSING_LEASE in _codes(record)
    assert record["cleanup_policy"]["retirement_authorized"] is False


def test_renew_unknown_lease_returns_none(sandbox):
    assert cw.renew_lease("lease-nope", now=0.0, state_dir=sandbox["state"]) is None


# ---------------------------------------------------------------------------
# Wiring: the terminal tool and the managed creation APIs call the observer
# ---------------------------------------------------------------------------


def test_wiring_terminal_pre_exec_observes_commands(monkeypatch, sandbox):
    import tools.terminal_tool as terminal_module

    calls = []
    monkeypatch.setattr(
        cw, "observe_terminal_command",
        lambda command, **kwargs: calls.append((command, kwargs)),
    )
    monkeypatch.setattr(terminal_module, "gateway_lifecycle_block", lambda **_k: None)
    monkeypatch.setattr(terminal_module, "self_repo_block", lambda **_k: None)

    terminal_module._pre_exec_block(
        "git worktree add /tmp/x -b wired", env=SimpleNamespace(), env_type="local",
        cwd=str(sandbox["tmp"]), workdir=None, session_key="wiring-1", session_id="sess-wire",
    )
    assert len(calls) == 1
    command, kwargs = calls[0]
    assert command == "git worktree add /tmp/x -b wired"
    assert kwargs["env_type"] == "local" and kwargs["session_id"] == "sess-wire"
    assert kwargs["cwd"] == str(sandbox["tmp"])

    # Garbage commands must still pass through without raising (never blocks).
    terminal_module._pre_exec_block(
        "git worktree add 'unclosed", env=SimpleNamespace(), env_type="local",
        cwd=str(sandbox["tmp"]), workdir=None, session_key="wiring-1",
    )
    assert len(calls) == 2


def test_wiring_worktree_ops_observes_managed_creation(monkeypatch, sandbox):
    from hermes_cli import worktree_ops

    calls = []
    monkeypatch.setattr(
        cw, "observe_managed_creation",
        lambda path, **kwargs: calls.append((path, kwargs)),
    )
    # ``_cprint`` lazily imports ``cli`` (which pulls the PM bootstrap at import);
    # the print path is orthogonal to the observer wiring under test.
    monkeypatch.setattr(worktree_ops, "_cprint", lambda *a, **k: None)
    info = worktree_ops._setup_worktree(repo_root=str(sandbox["repo"]), sync_base=False)
    assert info is not None and Path(info["path"]).is_dir()
    assert len(calls) == 1
    path, kwargs = calls[0]
    assert path == info["path"]
    assert kwargs["creator"] == "hermes-cli-worktree"
    assert kwargs["base_revision"] == "HEAD"


def test_wiring_subagent_observes_managed_creation(monkeypatch, sandbox):
    from tools import subagent_worktree as sw

    calls = []
    monkeypatch.setattr(
        cw, "observe_managed_creation",
        lambda path, **kwargs: calls.append((path, kwargs)),
    )
    info = sw.create_subagent_worktree(str(sandbox["repo"]), "wirecheck")
    assert info is not None
    assert len(calls) == 1
    path, kwargs = calls[0]
    assert path == info["path"]
    assert kwargs["creator"] == "subagent" and kwargs["subagent_id"] == "wirecheck"


def test_wiring_kanban_observes_managed_creation(monkeypatch, sandbox):
    from hermes_cli import kanban_db_workspace as kbw

    calls = []
    monkeypatch.setattr(
        cw, "observe_managed_creation",
        lambda path, **kwargs: calls.append((path, kwargs)),
    )
    target = sandbox["repo"] / ".worktrees" / "t_wire"
    kbw._ensure_git_worktree(sandbox["repo"], target, "wt/t_wire")
    assert target.is_dir()
    assert len(calls) == 1
    path, kwargs = calls[0]
    assert path == str(target)
    assert kwargs["creator"] == "kanban"
