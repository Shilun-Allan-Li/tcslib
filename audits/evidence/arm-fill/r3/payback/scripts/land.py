"""Dedup payback: build the landing tree and the patches (read-only on the base export).

Usage: python3 -I -B land.py <S> <base export> <olean snapshot> <packages worktree> <L>
       [--out <subdir>]

0. Runs the source precheck (precheck.py) before writing anything: exit 2 if a source is
   missing or differs from the tip's blob.
1. Applies the asserted edits of edits.py to each touched file of the base export and writes
   <L>/tree/<path> (or <L>/<subdir>/tree with --out). A file of kind "comment" must keep its
   code: its comment-stripped, whitespace-collapsed text equals the base's (asserted). The
   whitespace-only width wraps of edits.WRAPS follow each file's edits.
2. Writes `diff -u` patches to patches/, and replays each one on a scratch copy of the base
   file (`patch -p1`), asserting byte equality with the tree.
The edit log goes to logs/land-edits.txt.
"""
import os
import shutil
import subprocess
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
import lib  # noqa: E402
import edits as E  # noqa: E402
import precheck  # noqa: E402


def main():
    args = sys.argv[1:]
    outsub = None
    if "--out" in args:
        k = args.index("--out"); outsub = args[k + 1]; args = args[:k] + args[k + 2:]
    S, base, OL, WT, L = args[:5]
    miss = precheck.problems(S, base, OL, WT, L)
    if miss:
        for m in miss:
            print(f"land.py: precheck: {m}", file=sys.stderr)
        print("land.py: nothing written", file=sys.stderr)
        sys.exit(2)
    out = os.path.join(L, outsub) if outsub else L
    tree = os.path.join(out, "tree")
    shutil.rmtree(tree, ignore_errors=True)
    lines = []

    def log(s):
        print(s)
        lines.append(s)
    for key, (rel, fn, kind) in E.FILES.items():
        bt = lib.rd(os.path.join(base, rel))
        log(f"{key} ({rel}, {bt.count(chr(10))} lines, {kind}):")
        f = getattr(E, fn)
        if key in E.EXTRA_INPUT:
            lt = f(bt, lib.rd(os.path.join(base, E.FILES[E.EXTRA_INPUT[key]][0])), log)
        else:
            lt = f(bt, log)
        for old, new in E.WRAPS.get(key, []):
            assert " ".join(old.split()) == " ".join(new.split()), key
            lt = lib.sub(lt, old, new, 1, f"{key} width wrap")
            log(f"  width wrap (whitespace only): {old.strip().split(chr(10))[0][:70]!r}")
        assert lt != bt, key
        if kind == "comment":
            assert lib.code_norm(lt) == lib.code_norm(bt), f"{key}: code changed"
            log("  code unchanged (comment-stripped identity with the base, asserted)")
        lib.wr(os.path.join(tree, rel), lt)
        log(f"  -> {lt.count(chr(10))} lines")
    pdir = os.path.join(out, "patches")
    shutil.rmtree(pdir, ignore_errors=True)
    os.makedirs(pdir)
    rep = os.path.join(L, "work", "patchreplay" + ("-" + outsub.replace("/", "_") if outsub else ""))
    shutil.rmtree(rep, ignore_errors=True)
    for key, (rel, _, _) in E.FILES.items():
        r = subprocess.run(["diff", "-u", os.path.join(base, rel), os.path.join(tree, rel)],
                           capture_output=True, text=True)
        assert r.returncode == 1, (rel, r.returncode)
        pl = r.stdout.split("\n")
        pl[0], pl[1] = f"--- a/{rel}", f"+++ b/{rel}"
        lib.wr(os.path.join(pdir, key + ".patch"), "\n".join(pl))
        lib.wr(os.path.join(rep, rel), lib.rd(os.path.join(base, rel)))
        subprocess.run(["patch", "-s", "-p1", "-i", os.path.join(pdir, key + ".patch")], cwd=rep,
                       check=True)
        same = lib.rd(os.path.join(rep, rel)) == lib.rd(os.path.join(tree, rel))
        add = sum(1 for l in pl if l.startswith("+") and not l.startswith("+++"))
        rem = sum(1 for l in pl if l.startswith("-") and not l.startswith("---"))
        log(f"patch {key}.patch: +{add} -{rem}; replay {'identical' if same else 'DIFFERENT'}")
        assert same
    lib.wr(os.path.join(out, "logs", "land-edits.txt"), "\n".join(lines) + "\n")


if __name__ == "__main__":
    main()
