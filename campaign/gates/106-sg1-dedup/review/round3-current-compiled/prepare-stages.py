"""Split retained metadata instrumentation into small, separately reported stages."""
from pathlib import Path

OUT = Path(__file__).resolve().parent
large = (OUT / "Metadata-v3.lean.txt").read_text()
imports = large.split("\nset_option", 1)[0]
owners = large.split("  let owners : List Name :=", 1)[1].split("  for owner in owners do", 1)[0]
enumeration = """  let owned := env.constants.toList.filterMap fun (n, ci) =>
    match env.getModuleIdxFor? n with
    | some i =>
      let owner := env.header.moduleNames[i.toNat]!
      if owners.contains owner then some (n, ci, owner) else none
    | none => none
"""
types = imports + """
set_option maxHeartbeats 0
open Lean Elab Command Meta in
run_cmd do
  let env ← getEnv
  let owners : List Name :=""" + owners + enumeration + """  for (n, ci, _) in owned.toArray.qsort (fun a b => a.1.toString < b.1.toString) do
    logInfo m!"TYPE_REPR|{n}|{reprStr ci.type}"
  logInfo m!"TYPECOMPLETE|constants={owned.length}"
"""
(OUT / "Metadata-types-v1.lean.txt").write_text(types)

extra = large.split("  let extra := fun (ci : ConstantInfo) => match ci with\n", 1)[1].split("  let inlineName :=", 1)[0]
extra = "\n".join(line[2:] if line.startswith("  ") else line for line in extra.splitlines())
extra = extra.replace("hint d.hints", "metadataHint d.hints").replace("names ", "metadataNames ")
inline = large.split("  let inlineName := fun (k : Compiler.InlineAttributeKind) => match k with\n", 1)[1].split("  liftIO", 1)[0]
inline = "\n".join(line[2:] if line.startswith("  ") else line for line in inline.splitlines())
attr_body = large.split("    let instancePrio ←", 1)[1].split('    liftIO <| IO.println s!"CONSTANT', 1)[0]
attr_body = "    let instancePrio ←" + attr_body
attr_body = attr_body.replace("inlineName", "metadataInlineName")
ci = imports + """
set_option maxHeartbeats 0
open Lean Elab Command Meta
private def metadataNames (ns : List Name) : Json := toJson (ns.map Name.toString)
private def metadataHint (h : ReducibilityHints) : String :=
  match h with
  | .opaque => "opaque" | .abbrev => "abbrev" | .regular height => s!"regular:{height.toNat}"
private def metadataSpecific (ci : ConstantInfo) : Json :=
  match ci with
""" + extra + """
private def metadataInlineName (k : Compiler.InlineAttributeKind) : String :=
  match k with
""" + inline + """
run_cmd do
  let env ← getEnv
  let simp ← liftTermElabM getSimpTheorems
  let envAfter ← getEnv
  unless env.constants.toList.length == envAfter.constants.toList.length do
    throwError "getSimpTheorems changed the environment population"
  let owners : List Name :=""" + owners + enumeration + """  for (n, ci, _) in owned.toArray.qsort (fun a b => a.1.toString < b.1.toString) do
    let info := Json.mkObj [("levelParams", metadataNames ci.levelParams), ("unsafe", toJson ci.isUnsafe),
      ("partial", toJson ci.isPartial), ("specific", metadataSpecific ci)]
""" + attr_body + """    logInfo m!"CI|{n}|{info.compress}"
    logInfo m!"ATTR|{n}|{attrs.compress}"
  logInfo m!"CICOMPLETE|constants={owned.length}|simp_environment_unchanged=true"
"""
# Simp rule inspection is a separate short command so any diagnostic has a small context.
ci += """
run_cmd do
  let env ← getEnv
  let simp ← liftTermElabM getSimpTheorems
  let owners : List Name :=""" + owners + """  let rules : Array SimpTheorem :=
    (simp.pre.foldValues (fun (a : Array SimpTheorem) s => a.push s) #[]) ++
    (simp.post.foldValues (fun (a : Array SimpTheorem) s => a.push s) #[])
  for s in rules do
    if let .decl n phase inv := s.origin then
      if let some idx := env.getModuleIdxFor? n then
        if owners.contains env.header.moduleNames[idx.toNat]! then
          let row := Json.mkObj [("phase", toJson phase), ("inverse", toJson inv), ("priority", toJson s.priority),
            ("post", toJson s.post), ("perm", toJson s.perm), ("rfl", toJson s.rfl),
            ("levelParams", metadataNames s.levelParams.toList), ("proof_repr", toJson (reprStr s.proof))]
          logInfo m!"SIMP_RULE|{n}|{row.compress}"
  logInfo "SIMPCOMPLETE"
"""
(OUT / "Metadata-ciattrs-v1.lean.txt").write_text(ci)
print("Prepared separate uncapped type and structural-CI/attribute probes; no Lean invoked.")
