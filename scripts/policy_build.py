#!/usr/bin/env python3
"""
Scratch builder for the policy cleanup (direct `lean -o`, never `lake build`).

Given a set of touched .lean files, compile them in import-topological order into
cleanup/.olean/ and prepend that directory to LEAN_PATH, so that a touched file
that imports another touched file sees the NEW olean of its dependency rather
than the stale one in .lake/build.  Untouched modules still resolve from .lake.

    python3 scripts/policy_build.py TCSlib/Cryptography/RSA.lean TCSlib/Cryptography/RSA/*.lean
    python3 scripts/policy_build.py --area Cryptography --exclude TCSlib/GraphTheory/Core

Prints one line per module; exits nonzero if any module has an error.  Once this
passes, run `POLICY_OLEAN_DIR=cleanup/.olean python3 scripts/decl_snapshot.py ...`
so the snapshot elaborates against the same fresh oleans.
"""

from __future__ import annotations

import argparse
import os
import re
import subprocess
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
from leanlock import lean_lock  # noqa: E402

ROOT = Path(__file__).resolve().parent.parent
OLEAN_DIR = ROOT / "cleanup" / ".olean"
IMPORT_RE = re.compile(r"^\s*import\s+(TCSlib(?:\.\w+)+)\s*$", re.M)


def module_name(path: Path) -> str:
    return ".".join(path.resolve().relative_to(ROOT).with_suffix("").parts)


def lean_path() -> str:
    lp = [str(OLEAN_DIR), str(ROOT / ".lake/build/lib/lean")]
    for d in sorted((ROOT / ".lake/packages").glob("*/.lake/build/lib/lean")):
        lp.append(str(d))
    return ":".join(lp)


def topo(files: list[Path]) -> list[Path]:
    by_mod = {module_name(f): f for f in files}
    deps = {m: [d for d in IMPORT_RE.findall(f.read_text()) if d in by_mod] for m, f in by_mod.items()}
    order: list[str] = []
    state: dict[str, int] = {}

    def visit(m: str) -> None:
        if state.get(m) == 2:
            return
        if state.get(m) == 1:
            sys.exit(f"import cycle through {m}")
        state[m] = 1
        for d in deps[m]:
            visit(d)
        state[m] = 2
        order.append(m)

    for m in sorted(by_mod):
        visit(m)
    return [by_mod[m] for m in order]


LAKE_LIB = ROOT / ".lake/build/lib/lean"


def seed_scratch() -> int:
    """Lean resolves a module by the first search-path entry that contains its package
    directory (`TCSlib/`), so once cleanup/.olean/TCSlib exists EVERY TCSlib.* module must
    be findable there.  Seed it with symlinks to the .lake oleans; a module that was built
    into the scratch dir is a regular file and is left alone."""
    n = 0
    src_root = LAKE_LIB / "TCSlib"
    if not src_root.is_dir():
        return 0
    for src in src_root.rglob("*"):
        if src.suffix not in (".olean", ".ilean"):
            continue
        dst = OLEAN_DIR / src.relative_to(LAKE_LIB)
        if dst.exists() or dst.is_symlink():
            if dst.is_symlink() and not dst.exists():
                dst.unlink()  # dangling
            else:
                continue
        dst.parent.mkdir(parents=True, exist_ok=True)
        dst.symlink_to(src)
        n += 1
    return n


def build(f: Path) -> tuple[bool, str]:
    mod = module_name(f)
    out = OLEAN_DIR / Path(*mod.split(".")).with_suffix(".olean")
    out.parent.mkdir(parents=True, exist_ok=True)
    # build to temp names, then atomically replace (a concurrent reader never sees a
    # missing olean, and a seed symlink into .lake is replaced, never written through)
    tmp_o = out.with_suffix(".olean.tmp")
    tmp_i = out.with_suffix(".ilean.tmp")
    env = dict(os.environ, LEAN_PATH=lean_path())
    with lean_lock():
        proc = subprocess.run(
            ["lean", "-o", str(tmp_o), "-i", str(tmp_i), str(f)],
            cwd=ROOT, env=env, capture_output=True, text=True,
        )
        if proc.returncode == 0 and tmp_o.exists():
            os.replace(tmp_o, out)
            if tmp_i.exists():
                os.replace(tmp_i, out.with_suffix(".ilean"))
        for t in (tmp_o, tmp_i):
            if t.exists():
                t.unlink()
    log = proc.stdout + proc.stderr
    errs = [l for l in log.splitlines() if "error:" in l]
    sorries = [l for l in log.splitlines() if "declaration uses 'sorry'" in l]
    ok = proc.returncode == 0 and not errs
    msg = errs[0][:200] if errs else (f"{len(sorries)} sorry warning(s)" if sorries else "")
    return ok, msg


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--area", action="append", default=[])
    ap.add_argument("--exclude", action="append", default=[])
    ap.add_argument("--changed", action="store_true",
                    help="skip a module whose scratch olean is a regular file newer than its source "
                         "and than the oleans of its TCSlib imports (restartable incremental build)")
    ap.add_argument("--clean", action="store_true",
                    help="delete cleanup/.olean (scratch oleans are large; run after the verifier)")
    ap.add_argument("files", nargs="*")
    args = ap.parse_args()
    if args.clean:
        import shutil
        shutil.rmtree(OLEAN_DIR, ignore_errors=True)
        print(f"removed {OLEAN_DIR.relative_to(ROOT)}")
        if not args.files and not args.area:
            return 0
    files = [Path(f) for f in args.files]
    for a in args.area:
        files += sorted((ROOT / "TCSlib" / a).rglob("*.lean"))
    files = [f for f in files if not any(str(f.resolve().relative_to(ROOT)).startswith(x) for x in args.exclude)]
    # TCSlib/Tactics holds metaprogram fixtures (e.g. EntropyIterTest) whose *elaboration*
    # writes generated .lean files into the source tree; never build them as a side effect
    # of an importer sweep.
    fixtures = [f for f in files if str(f.resolve().relative_to(ROOT)).startswith("TCSlib/Tactics/")]
    if fixtures:
        print("skipping metaprogram fixtures: " + ", ".join(module_name(f) for f in fixtures))
        files = [f for f in files if f not in fixtures]
    if not files:
        ap.error("no files")
    seeded = seed_scratch()
    if seeded:
        print(f"seeded {seeded} symlinks from .lake into {OLEAN_DIR.relative_to(ROOT)}")
    bad = 0
    skipped = 0
    for f in topo(files):
        if args.changed:
            mod = module_name(f)
            out = OLEAN_DIR / Path(*mod.split(".")).with_suffix(".olean")
            if out.is_file() and not out.is_symlink():
                t = out.stat().st_mtime
                deps = IMPORT_RE.findall(f.read_text())
                dep_ok = all(
                    (OLEAN_DIR / Path(*d.split(".")).with_suffix(".olean")).exists()
                    and (OLEAN_DIR / Path(*d.split(".")).with_suffix(".olean")).stat().st_mtime <= t
                    for d in deps)
                if f.stat().st_mtime <= t and dep_ok:
                    skipped += 1
                    continue
        ok, msg = build(f)
        print(f"[{'OK ' if ok else 'ERR'}] {module_name(f):70s} {msg}")
        bad += not ok
    print(f"\n{len(files) - bad - skipped}/{len(files)} modules built into {OLEAN_DIR.relative_to(ROOT)}"
          + (f" ({skipped} up to date, skipped)" if skipped else ""))
    return 1 if bad else 0


if __name__ == "__main__":
    sys.exit(main())
