#!/usr/bin/env python3
"""
Declaration-level content snapshot for the policy-cleanup invariance gate.

For each given .lean file, elaborate a scratch copy with a snapshot command
appended (direct `lean` invocation, same LEAN_PATH as scripts/lean_check.sh —
never `lake build`), and record every user-written declaration of that file:

  name        unmangled full name (private names un-mangled, so a private decl
              keeps its identity if its file moves)
  kind        thm | def | opaque | axiom | induct | ctor | rec | quot
  private     bool
  levelParams universe parameter names
  typeHash    structural (alpha-invariant) hash of the statement / type
  typePP      `pp.all` rendering of the type (for human diffs)
  valueHash   structural hash of the body — recorded for def/opaque/induct/ctor
              (theorem bodies are deliberately NOT part of the invariant)
  valuePP     `pp.all` rendering of the body, def-like kinds only
  axioms      sorted list of axioms the declaration depends on (sorryAx ∈ this
              list means the theorem is not fully proved)
  module      file the declaration currently lives in (informational; the
              diff is keyed by name, so moving a declaration is allowed)
  range       [startLine, endLine]

Usage:
    python3 scripts/decl_snapshot.py --label before TCSlib/Cryptography/*.lean
    python3 scripts/decl_snapshot.py --label after  --area LearningTheory
Output:
    cleanup/snapshots/<label>/<Module.Name>.json   (one per file)

Compare two labels with scripts/decl_snapshot_diff.py.
"""

from __future__ import annotations

import argparse
import json
import os
import shutil
import subprocess
import sys
import tempfile
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
from leanlock import lean_lock  # noqa: E402

ROOT = Path(__file__).resolve().parent.parent
SNAP_ROOT = ROOT / "cleanup" / "snapshots"
MARK = "@@SNAP@@"

SNAPSHOT_CMD = r'''

-- <<policy-snapshot: appended by scripts/decl_snapshot.py; never commit>>
set_option pp.all true in
set_option maxRecDepth 100000 in
#eval show Lean.Elab.Command.CommandElabM Unit from do
  let env ← Lean.getEnv
  let mut names : Array (Lean.Name × Lean.ConstantInfo) := #[]
  for (n, ci) in env.constants.map₂.toList do
    names := names.push (n, ci)
  for (n, ci) in names do
    let some rng ← Lean.findDeclarationRanges? n | continue
    let user := match Lean.privateToUserName? n with
      | some u => u
      | none => n
    if user.isInternal then continue
    if Lean.isAuxRecursor env n || Lean.isNoConfusion env n then continue
    if Lean.isRecCore env n || Lean.isCasesOnRecursor env n then continue
    let kind := match ci with
      | .thmInfo _ => "thm" | .defnInfo _ => "def" | .opaqueInfo _ => "opaque"
      | .axiomInfo _ => "axiom" | .inductInfo _ => "induct" | .ctorInfo _ => "ctor"
      | .recInfo _ => "rec" | .quotInfo _ => "quot"
    let typePP ← Lean.Elab.Command.liftTermElabM do
      return (← Lean.Meta.ppExpr ci.type).pretty 1000000
    -- same, with instance arguments elided (`_`): "up to instance resolution path"
    let typeNI ← Lean.Elab.Command.liftTermElabM do
      Lean.withOptions (fun o => o.setBool `pp.instances false) do
        return (← Lean.Meta.ppExpr ci.type).pretty 1000000
    let (valueHash, valuePP) ← Lean.Elab.Command.liftTermElabM do
      match kind, ci.value? with
      | "thm", _ => return (Lean.Json.null, Lean.Json.null)
      | _, some v =>
        let vpp := (← Lean.Meta.ppExpr v).pretty 1000000
        return (Lean.toJson (toString v.hash), Lean.toJson vpp)
      | _, none => return (Lean.Json.null, Lean.Json.null)
    let valueNI ← Lean.Elab.Command.liftTermElabM do
      match kind, ci.value? with
      | "thm", _ => return Lean.Json.null
      | _, some v =>
        Lean.withOptions (fun o => o.setBool `pp.instances false) do
          return Lean.toJson ((← Lean.Meta.ppExpr v).pretty 1000000)
      | _, none => return Lean.Json.null
    let axs ← Lean.collectAxioms n
    let axs := (axs.qsort (fun a b => a.toString < b.toString)).map (·.toString)
    let j := Lean.Json.mkObj [
      ("name", Lean.toJson user.toString),
      ("mangled", Lean.toJson n.toString),
      ("kind", Lean.toJson kind),
      ("private", Lean.toJson (Lean.isPrivateName n)),
      ("levelParams", Lean.toJson (ci.levelParams.map (·.toString))),
      ("typeHash", Lean.toJson (toString ci.type.hash)),
      ("typePP", Lean.toJson typePP),
      ("typeNI", Lean.toJson typeNI),
      ("valueHash", valueHash),
      ("valuePP", valuePP),
      ("valueNI", valueNI),
      ("axioms", Lean.toJson axs),
      ("range", Lean.toJson [rng.range.pos.line, rng.range.endPos.line])
    ]
    IO.println s!"@@SNAP@@ {j.compress}"
'''


def lean_path() -> str:
    lp = [str(ROOT / ".lake/build/lib/lean")]
    if os.environ.get("POLICY_OLEAN_DIR"):
        # fresh oleans from scripts/policy_build.py take precedence over .lake
        lp.insert(0, str(Path(os.environ["POLICY_OLEAN_DIR"]).resolve()))
    for d in sorted((ROOT / ".lake/packages").glob("*/.lake/build/lib/lean")):
        lp.append(str(d))
    return ":".join(lp)


def module_name(path: Path) -> str:
    rel = path.resolve().relative_to(ROOT)
    return ".".join(rel.with_suffix("").parts)


def snapshot_file(src: Path, label: str, keep_scratch: bool = False,
                  git_rev: str | None = None) -> tuple[int, str]:
    mod = module_name(src)
    out_dir = SNAP_ROOT / label
    out_dir.mkdir(parents=True, exist_ok=True)
    scratch = Path(tempfile.mkdtemp(prefix="declsnap_"))
    # keep the relative path so `_private.<module>` mangling is unchanged
    copy = scratch / src.resolve().relative_to(ROOT)
    copy.parent.mkdir(parents=True, exist_ok=True)
    if git_rev:
        rel = src.resolve().relative_to(ROOT)
        text = subprocess.run(["git", "show", f"{git_rev}:{rel}"], cwd=ROOT,
                              capture_output=True, text=True, check=True).stdout
    else:
        text = src.read_text()
    copy.write_text(text + SNAPSHOT_CMD)
    if os.environ.get("POLICY_OLEAN_DIR"):
        from policy_build import seed_scratch  # same dir on sys.path
        seed_scratch()
    env = dict(os.environ, LEAN_PATH=lean_path())
    with lean_lock():
        proc = subprocess.run(
            ["lean", "--root", str(scratch), str(copy)],
            cwd=ROOT, env=env, capture_output=True, text=True,
        )
    decls = []
    errors = []
    for line in proc.stdout.splitlines():
        if line.startswith(MARK):
            d = json.loads(line[len(MARK):].strip())
            d["module"] = mod
            decls.append(d)
        elif "error:" in line:
            errors.append(line)
    if proc.stderr.strip():
        errors.append(proc.stderr.strip())
    decls.sort(key=lambda d: (d["range"][0], d["name"]))
    (out_dir / f"{mod}.json").write_text(
        json.dumps({"module": mod, "source": str(src), "errors": errors,
                    "declarations": decls}, indent=1, ensure_ascii=False) + "\n"
    )
    if not keep_scratch:
        shutil.rmtree(scratch, ignore_errors=True)
    return len(decls), ("; ".join(errors[:3]) if errors else "")


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--label", required=True, help="snapshot label, e.g. before / after")
    ap.add_argument("--area", action="append", default=[],
                    help="snapshot every .lean under TCSlib/<Area> (repeatable)")
    ap.add_argument("--exclude", action="append", default=[],
                    help="path prefix to skip, e.g. TCSlib/GraphTheory/Core")
    ap.add_argument("--git-rev", default=None,
                    help="snapshot the file contents at this git revision instead of the working tree "
                         "(module name still from the path); for re-baselining")
    ap.add_argument("files", nargs="*")
    args = ap.parse_args()

    files = [Path(f) for f in args.files]
    for area in args.area:
        files += sorted((ROOT / "TCSlib" / area).rglob("*.lean"))
    files = [f for f in files if not any(str(f.resolve().relative_to(ROOT)).startswith(x)
                                          for x in args.exclude)]
    if not files:
        ap.error("no files given")
    bad = 0
    for f in files:
        n, err = snapshot_file(f, args.label, git_rev=args.git_rev)
        status = "OK " if not err else "ERR"
        print(f"[{status}] {module_name(f):70s} {n:4d} decls  {err}")
        bad += bool(err)
    return 1 if bad else 0


if __name__ == "__main__":
    sys.exit(main())
