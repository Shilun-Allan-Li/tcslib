"""mkprobes.py <modules-file(dotted)> <outdir>: writes StmtDump.lean and AxiomProbe.lean (the GSW
statement phase's probes, with the module list replaced) for the new and changed modules.
StmtDump: every non-internal constant of the modules, with its type printed with full names, and the
TCSlib-namespace constants (BoolCircuit, BranchingProgram, Language, TCSlib) its type mentions.
AxiomProbe: every constant (declarations and auxiliary constants) of the modules with its axioms
(`Lean.collectAxioms`), and, for every constant whose axioms include `sorryAx`, the dependency trace:
the constants of the modules, in its transitive closure, whose own value or type mentions `sorryAx`
directly (the admitted targets through which it reaches `sorryAx`)."""
import sys
mods = [l.strip() for l in open(sys.argv[1]) if l.strip()]
out = sys.argv[2]
imports = ''.join(f'import {m}\n' for m in mods)
mlist = ',\n    '.join('`' + m for m in mods)
dump = f'''{imports}open Lean Elab Command Meta

/-! Statement dump (6a statement job): every constant of the new and changed modules, with its type
printed with full names, and the library constants its type mentions. -/

set_option pp.fullNames true in
set_option pp.funBinderTypes true in
#eval show CommandElabM Unit from do
  let env ← getEnv
  let mods : List Name := [
    {mlist}]
  let idxs := mods.filterMap env.getModuleIdx?
  let names := env.header.moduleNames
  let mut out : Array (String × String) := #[]
  for (n, c) in env.constants.toList do
    let some i := env.getModuleIdxFor? n | continue
    if idxs.contains i && !n.isInternal then
      let fmt ← liftTermElabM <| ppExpr c.type
      let consts := c.type.getUsedConstants.filter fun d =>
        (`TCSlib).isPrefixOf d || (`BoolCircuit).isPrefixOf d || (`BranchingProgram).isPrefixOf d ||
          (`BranchingProgramFamily).isPrefixOf d || (`Language).isPrefixOf d
      let kind := match c with
        | .defnInfo _ => "def" | .thmInfo _ => "theorem" | .inductInfo _ => "inductive"
        | .ctorInfo _ => "constructor" | .recInfo _ => "recursor" | .opaqueInfo _ => "opaque"
        | .axiomInfo _ => "axiom" | .quotInfo _ => "quot"
      out := out.push (n.toString, s!"{{n}}\\t{{kind}}\\t{{names[i.toNat]!}}\\n  : {{fmt}}\\n  CONSTS {{consts.toList}}")
  for (_, s) in out.qsort (fun a b => a.1 < b.1) do
    IO.println s
'''
ax = f'''{imports}open Lean Elab Command

/-! Axiom census and `sorryAx` dependency trace (6a statement job) of the new and changed modules. -/

#eval show CommandElabM Unit from do
  let env ← getEnv
  let mods : List Name := [
    {mlist}]
  let names := env.header.moduleNames
  let idxs := mods.filterMap env.getModuleIdx?
  let inMods (n : Name) : Bool := match env.getModuleIdxFor? n with
    | some i => idxs.contains i | none => false
  -- constants of the modules whose own type or value mentions `sorryAx` directly
  let mut direct : Std.HashSet Name := {{}}
  for (n, c) in env.constants.toList do
    if inMods n then
      let v := (c.value? (allowOpaque := true)).getD (mkConst `True)
      if (c.type.getUsedConstants ++ v.getUsedConstants).contains ``sorryAx then
        direct := direct.insert n
  let mut out : Array String := #[]
  for (n, c) in env.constants.toList do
    let some i := env.getModuleIdxFor? n | continue
    if idxs.contains i then
      let axs ← liftCoreM (Lean.collectAxioms n)
      let tag := if n.isInternal then "AUX" else "DECL"
      let axl := axs.qsort (·.toString < ·.toString) |>.toList
      out := out.push s!"{{tag}}\\t{{names[i.toNat]!}}\\t{{n}}\\t{{axl}}"
      if axs.contains ``sorryAx then
        -- walk the closure inside the modules
        let mut seen : Std.HashSet Name := {{}}
        let mut stack : Array Name := #[n]
        let mut via : Array Name := #[]
        while !stack.isEmpty do
          let m := stack.back!
          stack := stack.pop
          if seen.contains m then continue
          seen := seen.insert m
          if direct.contains m then via := via.push m
          let some cm := env.find? m | continue
          let v := (cm.value? (allowOpaque := true)).getD (mkConst `True)
          for d in cm.type.getUsedConstants ++ v.getUsedConstants do
            if inMods d && !seen.contains d then stack := stack.push d
        let vl := via.qsort (·.toString < ·.toString) |>.toList
        out := out.push s!"TRACE\\t{{n}}\\tvia {{vl}}"
  for l in out.qsort (· < ·) do
    IO.println l
'''
open(out + '/StmtDump.lean', 'w').write(dump)
open(out + '/AxiomProbe.lean', 'w').write(ax)
