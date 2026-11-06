import TCSlib.Cryptography.Candidates.RSA


/-! Review addition: sorry sources. For each name: the TCSlib declarations that contain
`sorryAx` directly, reached through its type only (`TYPE`), or through its type and value
(`ALL`). Descends into TCSlib constants only (Mathlib has no `sorry`). -/
open Lean in
def reviewSorrySources (env : Environment) (n : Name) (withValue : Bool) : Array Name := Id.run do
  let isTCS : Name → Bool := fun c =>
    match env.getModuleIdxFor? c with
    | some i => (`TCSlib).isPrefixOf (env.header.moduleNames[i.toNat]!)
    | none => true
  let mut seen : NameSet := {}
  let mut todo : List Name := []
  let mut out : Array Name := #[]
  match env.find? n with
  | none => return #[`MISSING]
  | some d =>
    let cs := d.type.getUsedConstants ++
      (if withValue then (d.value?.map (·.getUsedConstants)).getD #[] else #[])
    if cs.contains ``sorryAx then out := out.push n
    todo := cs.toList
  while !todo.isEmpty do
    let c := todo.head!
    todo := todo.tail!
    if seen.contains c then continue
    seen := seen.insert c
    if !isTCS c then continue
    let some d := env.find? c | continue
    let cs := d.type.getUsedConstants ++ (d.value?.map (·.getUsedConstants)).getD #[]
    if cs.contains ``sorryAx then out := out.push c
    todo := cs.toList ++ todo
  return out

open Lean Elab Command in
elab "#review_sorry " t:ident* : command => do
  let env ← getEnv
  for i in t do
    let n ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo i
    let a := reviewSorrySources env n false
    let b := reviewSorrySources env n true
    logInfo m!"{n}\n  TYPE: {a.toList}\n  ALL:  {b.toList}"

open TCSlib.Cryptography.Candidates
#print axioms TCSlib.Cryptography.Candidates.statClose_sampleUnitL
#print axioms TCSlib.Cryptography.Candidates.polyTimeComputable_rsaGenRaw
#print axioms TCSlib.Cryptography.Candidates.polyTimeComputable_unitSampleStr
#print axioms TCSlib.Cryptography.Candidates.rsaSampler_spec
#print axioms TCSlib.Cryptography.Candidates.rsaCollection_sampleClose
#print axioms TCSlib.Cryptography.Candidates.rsaCollection_invProbAt_le
#print axioms TCSlib.Cryptography.Candidates.rsaCollection_oneWay
#print axioms TCSlib.Cryptography.Candidates.polyTimeComputable_rsaFromFactorRaw
#print axioms TCSlib.Cryptography.Candidates.factorProb_le_rsaProb
#print axioms TCSlib.Cryptography.Candidates.rsa_imp_factoring
#review_sorry TCSlib.Cryptography.Candidates.statClose_sampleUnitL TCSlib.Cryptography.Candidates.polyTimeComputable_rsaGenRaw TCSlib.Cryptography.Candidates.polyTimeComputable_unitSampleStr TCSlib.Cryptography.Candidates.rsaSampler_spec TCSlib.Cryptography.Candidates.rsaCollection_sampleClose TCSlib.Cryptography.Candidates.rsaCollection_invProbAt_le TCSlib.Cryptography.Candidates.rsaCollection_oneWay TCSlib.Cryptography.Candidates.polyTimeComputable_rsaFromFactorRaw TCSlib.Cryptography.Candidates.factorProb_le_rsaProb TCSlib.Cryptography.Candidates.rsa_imp_factoring 
