"""Prepare unfiltered non-private constant censuses for every changed module."""

from pathlib import Path
import json
import os


records = Path(__file__).resolve().parents[3]
scratch = Path(os.environ["TCSLIB_SCRATCH"])
cases = json.loads((scratch / "gate-source-exports/summary.json").read_text())
for gate, data in cases.items():
    evidence = records / "campaign/gates" / gate / "evidence/current"
    changed = (evidence / "landing/changed-lean-files.txt").read_text().splitlines()
    for label in ("base", "head"):
        files = [p for p in changed if (Path(data[label + "_export"]) / p).exists()]
        modules = [p.removesuffix(".lean").replace("/", ".") for p in files]
        text = "\n".join("import " + m for m in modules) + "\n\n"
        wanted = "[" + ", ".join("`" + m for m in modules) + "]"
        text += r'''open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let wanted : List Name := WANTED
  for mod in wanted do
    unless (env.getModuleIdx? mod).isSome do throwError "missing imported module {mod}"
  let names := env.constants.toList.filterMap fun (n, ci) =>
    match env.getModuleIdxFor? n with
    | some i =>
      let mod := env.header.moduleNames[i.toNat]!
      if wanted.contains mod && !isPrivateName n then some (n, ci, mod) else none
    | none => none
  for (n, ci, mod) in names.toArray.qsort (fun a b => a.1.toString < b.1.toString) do
    let kind := match ci with
      | .thmInfo _ => "theorem" | .defnInfo _ => "definition"
      | .opaqueInfo _ => "opaque" | .axiomInfo _ => "axiom"
      | .ctorInfo _ => "constructor" | .recInfo _ => "recursor"
      | .inductInfo _ => "inductive" | .quotInfo _ => "quotient"
    logInfo m!"CONSTANT {n} module={mod} kind={kind} internal={n.isInternalDetail}"
'''.replace("WANTED", wanted)
        target = evidence / "axioms" / ("ModuleCensus-" + label + ".lean.txt")
        target.parent.mkdir(exist_ok=True)
        target.write_text(text)
print("Prepared changed-module census sources only.")
