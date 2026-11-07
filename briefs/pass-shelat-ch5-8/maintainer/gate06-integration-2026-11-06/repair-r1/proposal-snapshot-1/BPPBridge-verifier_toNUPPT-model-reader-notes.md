# BPPBridge: polynomial-time verifier-model reader

Unapplied proposal:
`BPPBridge-verifier_toNUPPT-model-reader.patch`.
Frozen Gate06 head: `e9d64158461bfe24ddc88ab885bc4017899b4c16`.
No library source edit, Lean/cache/build command, or Git mutation occurred.

## Observed root and proof scope

The valid V3 BPPBridge pilot reports probe 132:9 / source
`BPPBridge.lean:82`: the direct `obtain` cannot destruct
`hM : Randomized.polyTimeModel.Eff (Randomized.boolVerifier M)` because the
foreign model's ordinary definition is irreducible. This root is independent
of the earlier polynomial-schedule reader error.

Only the existing `verifier_toNUPPT` proof block is changed. Its public header,
all premises, the machine construction/function, probability bridge and
admissions are unchanged. The previous Classes/polyLenExpr proposal is
composed with this one only in memory; no earlier patch is reapplied to the
worktree or included in this separate patch.

Frozen fingerprints:

- `TCSlib/Complexity/Randomized/PolyTimeModel.lean`:
  `e3cffbe20e78537fdc411197241a42ff0546913b019701c6c816d51e88f35ee4`.
- `TCSlib/Cryptography/Randomness/BPPBridge.lean`:
  `476f15a4848d40d5ee8fa42b937d9566016940db5912967614e6cdbd5cf27aec`.

## Necessary owner-side reader

No `polyTimeModel_eff_iff`/`polyTimeModel_Eff_iff` reader exists in the frozen
library. Add `Randomized.polyTimeModel_eff_iff` immediately beside the owning
definition, with a formula docstring and the term proof `Iff.rfl`. Its exact
right-hand side is the existing field formula:

`polyTimeModel.Eff M` iff there are languages `V1`, `V0` in `P` such that, for
every `x`, `r`, `M x r = some true` iff `pairEncode x r` belongs to `V1`, and
`M x r = some false` iff that pair belongs to `V0`.

The reader is generic in the existing Option-Bool-valued verifier type. It does
not require total output, change the treatment of `none`, constrain languages
off the encoded pairs, or change `EffTwoWitness`. No model field or security
notion is changed. There is no new attribute, hypothesis, helper definition,
host, admission, or tactic block in the owner file.

## The one consumer proof block

Replace the direct destructuring of `hM` by destructuring
`(Randomized.polyTimeModel_eff_iff (Randomized.boolVerifier M)).mp hM`.
The existing true/false-set witnesses, Boolean-verifier equation, indicator
construction and machine run proof are retained.

One further foreign-constructor read is visible later in that same block:
the existential advice field was proved by bare `rfl` after constructing
`NUPPT.ofPolyTime hf (.const 0) p xs hxs`. Replace it with the already
published `NUPPT.advice_ofPolyTime hf (.const 0) p xs hxs`
(`Randomized/PPT.lean:366-368`). That theorem has exactly the required
function equality. No new PPT reader is necessary and the construction's
arguments remain identical.

The proof therefore reads the model through its predicate contract and the
machine through its existing advice/run contracts. It does not name either
foreign definition in an unfold, rewrite, or simplification list. All nested
proofs already present in `verifier_toNUPPT` are unchanged; no new tactic block
is added.

## Verification limit and rebuild order

All patch hunks/context/counts are statically matched to frozen sources, and
the earlier Classes/evaluation patch composes with this patch only in memory.
The original definition bodies, public headers and admission counts are
preserved; the probability theorem and later source are untouched.

No Lean elaboration was run. Root should later rebuild the owner modules
(Classes for the prior proposal, PolyTimeModel for this reader) before
BPPBridge, then check the composed consumer natively and under the valid
whole-file seal. The pilot stopped at the destructuring root, so later proof
applicability remains untested; this proposal does not claim that the whole
module passes.
