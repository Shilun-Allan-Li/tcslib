import sys
cands=[l.strip() for l in open('/workspace/dlc-work/candidates.txt') if l.strip()]
extra=sys.argv[1:]  # extra module names to import (new modules)
imports=cands+['TCSlib.Cryptography.Implications.PublicKey']+extra
mods=cands+extra
src='\n'.join('import '+m for m in imports)+'''
open Lean Elab Command Meta

/-! Declaration and axiom dump: every stored constant of the candidate modules, as
`name | module | kind | type hash | attributes | axioms`, and the axioms of the campaign endpoints. -/

def candMods : List Name := [%s]

def endpoints : List Name := [`TCSlib.Cryptography.Composability.prfFixedScheme_cpa,
  `TCSlib.Cryptography.Composability.prfFixedScheme_cca1,
  `TCSlib.Cryptography.Composability.not_prfFixedScheme_cca2,
  `TCSlib.Cryptography.Composability.FixedLengthPKScheme.INDSecure.adaptive_cpa,
  `TCSlib.Cryptography.BitPublicKeyScheme.SingleBitSecure.bitwise_padded_cpa,
  `TCSlib.Cryptography.BitPublicKeyScheme.SingleBitSecure.exists_adaptive_cpa,
  `TCSlib.Cryptography.BitPublicKeyScheme.SingleBitSecure.padded_cpa,
  `TCSlib.Cryptography.Implications.PublicKey.exists_adaptiveCPA_of_rsa,
  `TCSlib.Cryptography.Implications.PublicKey.exists_adaptiveCPA_of_factoring]

#eval show CommandElabM Unit from do
  let env ← getEnv
  let mut rows : Array String := #[]
  for (c, ci) in env.constants.map₁.toList do
    let some idx := env.getModuleIdxFor? c | continue
    let m := env.header.moduleNames[idx.toNat]!
    unless candMods.contains m do continue
    let kind := match ci with
      | .thmInfo _ => "thm" | .defnInfo _ => "def" | .axiomInfo _ => "axiom"
      | .opaqueInfo _ => "opaque" | .inductInfo _ => "induct" | .ctorInfo _ => "ctor"
      | .recInfo _ => "rec" | .quotInfo _ => "quot"
    let st := getReducibilityStatusCore env c
    let red := match st with | .reducible => "reducible" | .irreducible => "irreducible" | _ => "regular"
    let simp := (simpExtension.getState env).lemmaNames.contains (.decl c)
    let inst := isInstanceCore env c
    let prot := isProtected env c
    let attrs := s!"{red}{if simp then ",simp" else ""}{if inst then ",instance" else ""}{if prot then ",protected" else ""}"
    let axs ← liftCoreM <| Lean.collectAxioms c
    let axs := (axs.map toString).qsort (· < ·)
    rows := rows.push s!"{c} | {m} | {kind} | {ci.type.hash} | {attrs} | {axs.toList}"
  for r in rows.qsort (· < ·) do
    IO.println r
  IO.println s!"constants: {rows.size}"
  for e in endpoints do
    match env.find? e with
    | none => IO.println s!"ENDPOINT {e}: NOT FOUND"
    | some _ =>
      let axs ← liftCoreM <| Lean.collectAxioms e
      IO.println s!"ENDPOINT {e}: {((axs.map toString).qsort (· < ·)).toList}"
''' % ', '.join('`'+m for m in mods)
open('/workspace/dlc/lean_proof/dlc/DeclDump.lean','w').write(src)
