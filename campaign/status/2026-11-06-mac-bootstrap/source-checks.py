"""Prepare reproducible source evidence for gates 106, 114 and 115; no Lean runs.

Run with python3 -I after sourcing TCSLIB_SCRATCH/env.sh. The worktrees must
already contain the campaign tip. Archives are fresh Git exports. Expected
policy-lint findings are retained, including the process exit status.
"""

from __future__ import annotations

import contextlib
import hashlib
import io
import json
import os
from pathlib import Path
import runpy
import subprocess
import sys
import tarfile


RECORDS = Path(__file__).resolve().parents[3]
SCRATCH = Path(os.environ["TCSLIB_SCRATCH"])
SOURCE = Path(os.environ["TCSLIB_REPO"])
EXPORTS = SCRATCH / "gate-source-exports"
GIT_PATHS = ["TCSlib", "TCSlib.lean", "scripts", "devtools", "blueprint/src",
             "dep_graph.json", "policy.md", "workflow.md"]


def git(*args: str, root: Path = RECORDS) -> str:
    return subprocess.check_output(["git", "-C", str(root), *args], text=True).strip()


def checked_commit(ref: str, root: Path = RECORDS) -> str:
    sha = git("rev-parse", ref, root=root)
    subprocess.run(["git", "-C", str(root), "cat-file", "-e", sha + "^{commit}"], check=True)
    return sha


def export(sha: str) -> Path:
    target = EXPORTS / sha
    if target.exists():
        entries = subprocess.check_output(
            ["git", "-C", str(RECORDS), "ls-tree", "-rz", sha, "--", *GIT_PATHS])
        for entry in entries.split(b"\0"):
            if not entry:
                continue
            metadata, raw_path = entry.split(b"\t", 1)
            mode, kind, blob = metadata.split()
            assert kind == b"blob", entry
            path = target / os.fsdecode(raw_path)
            data = os.fsencode(os.readlink(path)) if mode == b"120000" else path.read_bytes()
            actual = hashlib.sha1(b"blob " + str(len(data)).encode() + b"\0" + data).hexdigest()
            assert actual == blob.decode(), path
        return target
    target.mkdir(parents=True)
    proc = subprocess.Popen(
        ["git", "-C", str(RECORDS), "archive", sha, *GIT_PATHS],
        stdout=subprocess.PIPE,
    )
    assert proc.stdout is not None
    with tarfile.open(fileobj=proc.stdout, mode="r|") as archive:
        archive.extractall(target, filter="data")
    assert proc.wait() == 0
    return target


def logged(args: list[str], path: Path, cwd: Path) -> int:
    with path.open("w") as output:
        proc = subprocess.run(args, cwd=cwd, stdout=output, stderr=subprocess.STDOUT)
        output.write(f"\nexit={proc.returncode}\n")
    return proc.returncode


def main() -> None:
    base_sha = checked_commit("origin/complexity/arora-barak-ch3-4")
    base = export(base_sha)
    empty = EXPORTS / "empty.lean.txt"
    empty.write_text("")
    # Load the campaign's comment-aware declaration census without emitting a
    # throwaway comparison; no delivered Lean text is executed as Python.
    sys.argv = [str(RECORDS / "devtools/seyoon/declfreeze.py"), str(empty), str(empty)]
    with contextlib.redirect_stdout(io.StringIO()):
        census = runpy.run_path(sys.argv[0])
    chunks, statement = census["chunks"], census["stmt"]
    cases = [
        ("106-sg1-dedup", "wt-sg1", 4,
         {"CounterLoop.lean": "counterLoopTMVia_run_done,counterLoopTMVia_done_witness,"
          "counterLoopTMVia_escape_witness,RoundContract.counterLoopDone_traj,"
          "RoundContract.counterLoopEscape_traj", "Frag.lean": "halfL_run"}),
        ("114-natbits-dedup", "wt-natbits", 22,
         {"Meyer.lean": "lenAll_inst", "MeyerTableau.lean": "bits_pad",
          "SpaceAmplifyPoly.lean": "bigK_le", "UniformSample.lean": "le_two_pow_size_pred",
          "CfgRecord.lean": "record_pos_lt", "Frag.lean": "halfL_run"}),
        ("115-epad-fill", "wt-epad", 1,
         {"Padding.lean": "mem_SPACE_padLang"}),
    ]
    summary_path = EXPORTS / "summary.json"
    summary = json.loads(summary_path.read_text()) if summary_path.exists() else {}
    for gate, worktree, expected, allowed in cases:
        if os.environ.get("TCSLIB_SOURCE_GATE") not in (None, gate):
            continue
        wt = SCRATCH / worktree
        assert not git("status", "--porcelain", root=wt)
        head_sha = checked_commit("HEAD", root=wt)
        assert subprocess.run(["git", "-C", str(wt), "merge-base", "--is-ancestor",
                               base_sha, head_sha]).returncode == 0
        changed = git("diff", "--name-only", base_sha, head_sha, "--", "*.lean").splitlines()
        assert len(changed) == expected, (gate, changed)
        head = export(head_sha)
        evidence = RECORDS / "campaign/gates" / gate / "evidence/current"
        for directory in ("landing", "freeze", "lint", "screen", "search"):
            (evidence / directory).mkdir(parents=True, exist_ok=True)
        (evidence / "landing/changed-lean-files.txt").write_text("\n".join(changed) + "\n")
        (evidence / "landing/change.diff").write_text(
            git("diff", base_sha, head_sha, "--", "*.lean", "blueprint/src") + "\n")
        (evidence / "landing/diff-stat.txt").write_text(git("diff", "--stat", base_sha, head_sha) + "\n")
        base_inputs = {}
        for path in changed:
            old = base / path
            if old.exists():
                target = evidence / "base-source" / (path + ".txt")
                target.parent.mkdir(parents=True, exist_ok=True)
                target.write_bytes(old.read_bytes())
                base_inputs[path] = str(target.relative_to(evidence))
            else:
                base_inputs[path] = None
        (evidence / "landing/base-source-map.json").write_text(
            json.dumps({"base": base_sha, "head": head_sha, "changed_files": base_inputs,
                        "unchanged_population_files": "Use the bundled head source; its blob is identical at base."},
                       indent=2) + "\n")
        for path in git("diff", "--name-only", base_sha, head_sha, "--", "blueprint/src").splitlines():
            for label, tree in (("base", base), ("head", head)):
                original = tree / path
                if original.exists():
                    target = evidence / "landing" / ("blueprint-" + original.stem + "-" + label + ".tex.txt")
                    target.write_bytes(original.read_bytes())
        changes = {}
        for path in changed:
            old = base / path
            new = head / path
            result = evidence / "freeze" / (Path(path).stem + ".txt")
            logged(["python3", "-I", str(RECORDS / "devtools/seyoon/declfreeze.py"),
                    str(old if old.exists() else empty), str(new), allowed.get(Path(path).name, "")],
                   result, RECORDS)
            old_chunks = list(chunks(old.read_text() if old.exists() else ""))
            new_chunks = list(chunks(new.read_text()))
            a = {n: (private, text) for n, private, text in old_chunks}
            b = {n: (private, text) for n, private, text in new_chunks}
            changes[path] = {
                "before_public": sum(not private for private, _ in a.values()),
                "after_public": sum(not private for private, _ in b.values()),
                "before_private": sum(private for private, _ in a.values()),
                "after_private": sum(private for private, _ in b.values()),
                "public_added": sorted(n for n in b.keys() - a.keys() if not b[n][0]),
                "public_removed": sorted(n for n in a.keys() - b.keys() if not a[n][0]),
                "public_body_changed": sorted(n for n in a.keys() & b.keys()
                                              if not a[n][0] and a[n][1] != b[n][1]),
                "statement_changed": sorted(n for n in a.keys() & b.keys()
                                            if statement(a[n][1]) != statement(b[n][1])),
                "private_added": sorted(n for n in b.keys() - a.keys() if b[n][0]),
                "private_removed": sorted(n for n in a.keys() - b.keys() if a[n][0]),
                "private_body_changed": sorted(n for n in a.keys() & b.keys()
                                               if a[n][0] and a[n][1] != b[n][1]),
                "visibility_changed": sorted(n for n in a.keys() & b.keys() if a[n][0] != b[n][0]),
                "surviving_public_order_unchanged":
                    [n for n, private, _ in old_chunks if not private and n in b] ==
                    [n for n, private, _ in new_chunks if not private and n in a],
                "surviving_private_order_unchanged":
                    [n for n, private, _ in old_chunks if private and n in b] ==
                    [n for n, private, _ in new_chunks if private and n in a],
            }
            assert not changes[path]["statement_changed"], (path, changes[path])
            assert not changes[path]["visibility_changed"], (path, changes[path])
            assert "UNAUTHORIZED" not in result.read_text(), result
        (evidence / "freeze/census.json").write_text(json.dumps(changes, indent=2) + "\n")
        subtrees = sorted({"/".join(path.split("/")[:3]) for path in changed
                           if path != "TCSlib/Complexity/TuringMachine.lean"})
        policy = {}
        for label, tree in (("base", base), ("head", head)):
            for subtree in subtrees:
                output = evidence / "lint" / f"campaign-{Path(subtree).name}-{label}.txt"
                policy[str(output.name)] = logged(
                    ["python3", "-I", str(tree / "scripts/campaign_style_lint.py"), subtree], output, tree)
            # A new file has no base counterpart; existing files are compared as
            # a common population, and the new module is checked separately.
            common = [path for path in changed if (base / path).exists()]
            output = evidence / "lint" / f"policy-{label}.txt"
            policy[output.name] = logged(["python3", "-I", str(tree / "scripts/style_lint.py"),
                                          *common], output, tree)
            if label == "head":
                added = [path for path in changed if not (base / path).exists()]
                if added:
                    output = evidence / "lint/policy-new-module.txt"
                    policy[output.name] = logged(["python3", "-I", str(tree / "scripts/style_lint.py"),
                                                  *added], output, tree)
            output = evidence / "lint" / f"blueprint-{label}.txt"
            policy[output.name] = logged(
                ["python3", "-I", str(tree / "scripts/blueprint_validate.py"),
                 "--strict", "--allow-orphans"], output, tree)
        population = set(changed)
        if gate.startswith("106"):
            population.update("TCSlib/Complexity/" + path for path in (
                "TuringMachine/Build/Contract/Basic.lean", "TuringMachine/Build/Primitives.lean",
                "TuringMachine/Build/Catalog.lean", "ClassNP/SAT.lean", "CookLevin/Hardness.lean"))
        if gate.startswith("115"):
            population.update("TCSlib/Complexity/" + path + ".lean" for path in (
                "ClassNP/PolyTimePairing", "SpaceComplexity/Basic", "SpaceComplexity/Codec/Word",
                "SpaceComplexity/Codec/Engine",
                "SpaceComplexity/ConfigCount", "SpaceComplexity/Logspace/InputAccess",
                "SpaceComplexity/Logspace/PreimageHost", "SpaceComplexity/Machines/ARM",
                "SpaceComplexity/Machines/ARMKit", "SpaceComplexity/Machines/ARMProof",
                "SpaceComplexity/Machines/Bank", "SpaceComplexity/Machines/Bin",
                "SpaceComplexity/Machines/CleanSweep", "SpaceComplexity/Machines/Compile",
                "SpaceComplexity/Machines/FragDec", "SpaceComplexity/Machines/Layout",
                "SpaceComplexity/Machines/ParsePlain", "SpaceComplexity/Machines/Program",
                "TuringMachine/Build/Catalog", "TuringMachine/Deterministic",
                "TuringMachine/Encoding", "TuringMachine/Finite"))
        population = sorted(population)
        (evidence / "screen/population-head.txt").write_text("\n".join(population) + "\n")
        (evidence / "screen/population-base.txt").write_text(
            "\n".join(path for path in population if (base / path).exists()) + "\n")
        info = {"base": base_sha, "head": head_sha, "worktree": worktree,
                "base_export": str(base), "head_export": str(head),
                "changed_lean_files": len(changed), "lint_exit_statuses": policy}
        (evidence / "landing/refs.json").write_text(json.dumps(info, indent=2) + "\n")
        summary[gate] = info
        print(gate, "source checks complete", len(changed), "Lean files", flush=True)
    (EXPORTS / "summary.json").write_text(json.dumps(summary, indent=2) + "\n")


if __name__ == "__main__":
    main()
