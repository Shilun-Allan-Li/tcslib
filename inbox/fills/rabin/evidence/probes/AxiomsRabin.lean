import TCSlib.Cryptography.Candidates.Rabin

/-! Axiom prints and sorry sources for the 19 rabin targets. For each name: the TCSlib
declarations that contain `sorryAx` directly, reached through its type only (`TYPE`), or through
its type and value (`ALL`), descending into TCSlib constants only (the method of the brief's
review probe `#review_sorry`, as used by the rsa delivery's `AxiomsRSA.lean`;
`preship/probes/SorrySources.lean` is not in the issue tree). -/
open Lean in
def rabinSorrySources (env : Environment) (n : Name) (withValue : Bool) : Array Name := Id.run do
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
elab "#rabin_sorry " t:ident* : command => do
  let env ← getEnv
  for i in t do
    let n ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo i
    let a := rabinSorrySources env n false
    let b := rabinSorrySources env n true
    logInfo m!"{n}\n  TYPE: {a.toList}\n  ALL:  {b.toList}"

#print axioms TCSlib.Cryptography.Candidates.oddFactorProb_le
#print axioms TCSlib.Cryptography.Candidates.blumFactorProb_le
#print axioms TCSlib.Cryptography.Candidates.blumFactoring_of_factoring
#print axioms TCSlib.Cryptography.Candidates.polyTimeComputable_oddGenRaw
#print axioms TCSlib.Cryptography.Candidates.polyTimeComputable_blumGenRaw
#print axioms TCSlib.Cryptography.Candidates.rabinSampler_spec
#print axioms TCSlib.Cryptography.Candidates.rabinCollection_sampleClose
#print axioms TCSlib.Cryptography.Candidates.polyTimeComputable_rabinFactorRaw
#print axioms TCSlib.Cryptography.Candidates.rabinCollection_invProbAt_le
#print axioms TCSlib.Cryptography.Candidates.rabinCollection_oneWay
#print axioms TCSlib.Cryptography.Candidates.polyTimeComputable_blumInvRaw
#print axioms TCSlib.Cryptography.Candidates.blumInv_spec
#print axioms TCSlib.Cryptography.Candidates.blumSampler_spec
#print axioms TCSlib.Cryptography.Candidates.rabinBlumTrapdoor_sampleClose
#print axioms TCSlib.Cryptography.Candidates.rabinBlumTrapdoor_invProbAt_le
#print axioms TCSlib.Cryptography.Candidates.rabinBlumTrapdoor_oneWay
#print axioms TCSlib.Cryptography.Candidates.polyTimeComputable_rabinRootRaw
#print axioms TCSlib.Cryptography.Candidates.blumFactorProb_le_invProbAt
#print axioms TCSlib.Cryptography.Candidates.blumFactoring_of_rabinBlum_oneWay
#rabin_sorry TCSlib.Cryptography.Candidates.oddFactorProb_le TCSlib.Cryptography.Candidates.blumFactorProb_le TCSlib.Cryptography.Candidates.blumFactoring_of_factoring TCSlib.Cryptography.Candidates.polyTimeComputable_oddGenRaw TCSlib.Cryptography.Candidates.polyTimeComputable_blumGenRaw TCSlib.Cryptography.Candidates.rabinSampler_spec TCSlib.Cryptography.Candidates.rabinCollection_sampleClose TCSlib.Cryptography.Candidates.polyTimeComputable_rabinFactorRaw TCSlib.Cryptography.Candidates.rabinCollection_invProbAt_le TCSlib.Cryptography.Candidates.rabinCollection_oneWay TCSlib.Cryptography.Candidates.polyTimeComputable_blumInvRaw TCSlib.Cryptography.Candidates.blumInv_spec TCSlib.Cryptography.Candidates.blumSampler_spec TCSlib.Cryptography.Candidates.rabinBlumTrapdoor_sampleClose TCSlib.Cryptography.Candidates.rabinBlumTrapdoor_invProbAt_le TCSlib.Cryptography.Candidates.rabinBlumTrapdoor_oneWay TCSlib.Cryptography.Candidates.polyTimeComputable_rabinRootRaw TCSlib.Cryptography.Candidates.blumFactorProb_le_invProbAt TCSlib.Cryptography.Candidates.blumFactoring_of_rabinBlum_oneWay
