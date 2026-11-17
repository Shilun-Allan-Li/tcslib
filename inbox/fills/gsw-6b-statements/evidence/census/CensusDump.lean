import TCSlib.Cryptography.AdvancedEncryption.Homomorphic.GSW
import TCSlib.Cryptography.LWE

/-! Census dump (gsw-6b statements, sub-agent probe; check 6 reader census, G6A-F03).
For every constant declared in the new modules (and O2's in `LWE/BitEncoding`), print the
TCSlib constants **foreign to its module** that occur in its type (`T`) and, for definitions,
in its value (`V`), with the foreign constant's module, kind, reducibility and declaration line.
For every foreign TCSlib definition met, print every TCSlib theorem whose last name component
starts with the definition's last component and `_` (case-insensitive) and whose statement
mentions the definition: the candidate published readers, with module and line. -/

open Lean Meta Elab Command

def newMods : List Name :=
  [`TCSlib.Cryptography.AdvancedEncryption.Homomorphic.GSW.Branching,
   `TCSlib.Cryptography.AdvancedEncryption.Homomorphic.GSW.DecryptFormula,
   `TCSlib.Cryptography.AdvancedEncryption.Homomorphic.GSW.Bootstrap,
   `TCSlib.Cryptography.AdvancedEncryption.Homomorphic.GSW.Circular,
   `TCSlib.Cryptography.AdvancedEncryption.Homomorphic.GSW.Leveled,
   `TCSlib.Cryptography.AdvancedEncryption.Homomorphic.GSW.LeveledSecurity,
   `TCSlib.Cryptography.AdvancedEncryption.Homomorphic.GSW.PolyRatio,
   `TCSlib.Cryptography.AdvancedEncryption.Homomorphic.GSW.Asymptotic,
   `TCSlib.Cryptography.LWE.Ratio]

def o2Names : List Name :=
  [`TCSlib.Cryptography.LWE.BitEncoding.decodeLo, `TCSlib.Cryptography.LWE.BitEncoding.decodeHi,
   `TCSlib.Cryptography.LWE.BitEncoding.decodeLo_eq, `TCSlib.Cryptography.LWE.BitEncoding.decodeHi_eq,
   `TCSlib.Cryptography.LWE.BitEncoding.decode_iff_mem_Ico]

def modOf (env : Environment) (n : Name) : Name :=
  match env.getModuleIdxFor? n with
  | some i => env.header.moduleNames[i.toNat]!
  | none => `_current

def kindOf (ci : ConstantInfo) : String :=
  match ci with
  | .defnInfo _ => "def" | .thmInfo _ => "thm" | .axiomInfo _ => "axiom"
  | .opaqueInfo _ => "opaque" | .quotInfo _ => "quot" | .inductInfo _ => "inductive"
  | .ctorInfo _ => "ctor" | .recInfo _ => "rec"

def lineOf (n : Name) : CommandElabM String := do
  match ← findDeclarationRanges? n with
  | some r => return toString r.selectionRange.pos.line
  | none => return "?"

def isTCSlib (m : Name) : Bool := (`TCSlib).isPrefixOf m

#eval show CommandElabM Unit from do
  let env ← getEnv
  let mut foreignDefs : Std.HashSet Name := {}
  let mut out : Array String := #[]
  for (n, ci) in env.constants.map₁.toList do
    let m := modOf env n
    let isNew := newMods.contains m || o2Names.contains n
    if !isNew || n.isInternalDetail then continue
    let parts : List (String × Expr) :=
      [("T", ci.type)] ++ (if ci matches .defnInfo _ then [("V", ci.value!)] else [])
    for (tag, e) in parts do
      for c in e.getUsedConstants do
        let mc := modOf env c
        if !isTCSlib mc || mc == m then continue
        let some cci := env.find? c | continue
        let red := match getReducibilityStatusCore env c with
          | .reducible => "reducible" | .semireducible => "semi" | .irreducible => "irreducible"
        let proj := if (env.getProjectionFnInfo? c).isSome then "projection" else
          if isInstanceCore env c then "instance" else ""
        out := out.push s!"USE\t{n}\t{kindOf ci}\t{tag}\t{c}\t{kindOf cci}\t{red}\t{proj}\t{mc}:{← lineOf c}"
        if kindOf cci == "def" || kindOf cci == "inductive" then foreignDefs := foreignDefs.insert c
  for s in out.qsort (· < ·) do IO.println s
  -- candidate readers
  let thms := env.constants.map₁.toList.filter fun (n, ci) =>
    ci matches .thmInfo _ && isTCSlib (modOf env n) && !n.isInternalDetail
  for d in foreignDefs.toArray.qsort (·.toString < ·.toString) do
    let last := (d.componentsRev.headD .anonymous).toString.toLower
    let mut rs : Array String := #[]
    for (t, ci) in thms do
      let tl := (t.componentsRev.headD .anonymous).toString.toLower
      if tl.startsWith (last ++ "_") && ci.type.getUsedConstants.contains d then
        rs := rs.push s!"{t}@{modOf env t}:{← lineOf t}"
    IO.println s!"READERS\t{d}\t{modOf env d}:{← lineOf d}\t{if rs.isEmpty then "MISSING" else " ".intercalate rs.toList}"
