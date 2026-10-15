"""Source precheck of the dedup payback landing (read-only; writes nothing).

Usage: python3 -I -B precheck.py <S> <base export> <olean snapshot> <packages worktree> <L>

Checks every source the pipeline reads, before any output is created:
* the base export holds every file read (the touched files, every other Lean file of
  `TCSlib/` the screens read, the gate scripts executed unchanged, the style lint, the ledger
  evidence and the scope documents), and each of the listed files is byte-identical to its
  blob at the export's commit (work/base-commit.txt: run.sh's `git rev-parse` of
  origin/complexity/arora-barak-ch3-4 when it made the export; `git cat-file blob`), and that
  commit is an ancestor of the live tip, which has changed none of the touched files since;
* the base export's `TCSlib/` has exactly the tip's Lean files (`git ls-tree`);
* the Lean tool, the olean snapshot (with sampled oleans) and the packages;
* the pipeline's own scripts.
Exit 0 if all are present and current; otherwise each problem goes to stderr and the exit
status is 2. land.py, the first step that writes, calls it first too.
"""
import os
import subprocess
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
import lib  # noqa: E402

C = lib.C
DOCS = ["lean-toolchain", "TCSlib.lean", "policy.md", "workflow.md", "backlog.md",
        "scripts/campaign_style_lint.py",
        "audits/evidence/b6hosts/gate/scripts/freeze.py",
        "audits/evidence/b6hosts/gate/scripts/names.py",
        "audits/evidence/mig1/gate/scripts/decls.py",
        "audits/evidence/arm-fill/r2/ledger-r2-tables.md",
        "audits/evidence/arm-fill/r2/classify.tsv",
        "audits/evidence/arm-fill/r2/pairs.tsv",
        "audits/evidence/arm-fill/r2/manual.tsv",
        "audits/arm-extensions-fill-r2-findings.md",
        "audits/arm-extensions-fill-r2-resolutions.md",
        "audits/arm-extensions-fill-findings.md",
        "TCSlib/Programs/Util/List.lean",
        C + "TuringMachine/Build/CfgRecord.lean",
        C + "SpaceComplexity/Logspace/Mult.lean",
        C + "CookLevin/Hardness.lean"]
SNAP = [C + "SpaceComplexity/ConfigGraph.olean", C + "SpaceComplexity/Logspace/InputAccess.olean",
        C + "SpaceComplexity/Codec/Machine.olean", C + "ClassPSPACE/TQBFHardBridge.olean",
        C + "TuringMachine/Build/CfgRecord.olean", "TCSlib/Programs/Util/List.olean",
        C + "TuringMachine/Build/StepBlockLoop.olean"]
SCRIPTS = ["lib.py", "edits.py", "precheck.py", "land.py", "cuts.py", "probes.py", "elab.sh",
           "freeze.py", "freezectl.py", "names.py", "graph.py", "hygiene.py", "lint.sh",
           "ledger.py", "verify.py", "run.sh", "sums.sh"]


def problems(S, base, oleans, wt, L):
    import edits as E
    out = []
    files = DOCS + [rel for rel, _, _ in E.FILES.values()]
    for f in files:
        if not os.path.isfile(os.path.join(base, f)):
            out.append(f"missing {os.path.join(base, f)}")
    if not os.path.isfile(os.path.join(S, "tools", "leanelab.sh")):
        out.append(f"missing {os.path.join(S, 'tools', 'leanelab.sh')}")
    if not os.path.isdir(oleans):
        out.append(f"missing {oleans}/")
    else:
        out += [f"missing {os.path.join(oleans, f)}" for f in SNAP
                if not os.path.isfile(os.path.join(oleans, f))]
    pk = os.path.join(wt, ".lake", "packages", "mathlib", ".lake", "build", "lib", "lean")
    if not os.path.isdir(pk):
        out.append(f"missing {pk}/")
    out += [f"missing {os.path.join(L, 'scripts', f)}" for f in SCRIPTS
            if not os.path.isfile(os.path.join(L, "scripts", f))]
    if out:
        return out
    try:
        live = lib.tip()
        tip = lib.base_commit()
        lib.git("rev-parse", "--verify", tip + "^{commit}")
        lib.git("merge-base", "--is-ancestor", tip, live)  # raises unless an ancestor
    except (subprocess.CalledProcessError, OSError) as e:
        return [f"git rev-parse / merge-base failed: {e}"]
    touched = {rel for rel, _, _ in E.FILES.values()}
    hit = sorted(set(lib.lean_diff(tip, live)) & touched)
    if hit:
        out.append(f"the live tip {live} changes touched files since the base {tip}: {hit}")
    for f in files:
        r = subprocess.run(["git", "-C", lib.REPO, "cat-file", "blob", f"{tip}:{f}"],
                           capture_output=True)
        if r.returncode != 0:
            out.append(f"not at the tip {tip}: {f}")
        elif r.stdout != open(os.path.join(base, f), "rb").read():
            out.append(f"differs from the tip {tip}: {f}")
    ls = subprocess.run(["git", "-C", lib.REPO, "ls-tree", "-r", "--name-only", tip, "TCSlib"],
                        capture_output=True, text=True, check=True).stdout.split()
    want = {p for p in ls if p.endswith(".lean")}
    have = set()
    for dp, _, fs in os.walk(os.path.join(base, "TCSlib")):
        for f in fs:
            if f.endswith(".lean"):
                have.add(os.path.relpath(os.path.join(dp, f), base))
    if want != have:
        out.append(f"the export's Lean files differ from the tip's: missing "
                   f"{sorted(want - have)[:5]}, extra {sorted(have - want)[:5]}")
    return out


def main():
    S, base, oleans, wt, L = sys.argv[1:6]
    import edits as E
    pr = problems(S, base, oleans, wt, L)
    if pr:
        for p in pr:
            print(f"precheck: {p}", file=sys.stderr)
        print(f"precheck: {len(pr)} problem(s); nothing written", file=sys.stderr)
        sys.exit(2)
    n = len(DOCS) + len(E.FILES)
    print(f"precheck: export {lib.base_commit()} (live tip {lib.tip()}, which changes none of the touched "
          f"files; Lean files it changes: {lib.lean_diff(lib.base_commit(), lib.tip())}); {n} source files present and byte-identical to their tip "
          f"blobs ({len(E.FILES)} touched files, {len(DOCS)} other inputs); the export holds "
          f"exactly the tip's Lean files; the tool, the snapshot ({len(SNAP)} sampled oleans), "
          f"the packages and {len(SCRIPTS)} pipeline scripts present")


if __name__ == "__main__":
    main()
