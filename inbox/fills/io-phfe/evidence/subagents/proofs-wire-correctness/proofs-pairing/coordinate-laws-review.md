# Additional coordinate-law proof candidates

No live edits, Lean/lake/build/proof-check commands or Git commands were used. These are
UNELABORATED term-proof candidates copied against the actual current Exponents headers.
All ten fragments preserve the exact existing docstring/header and replace only sorry.
There are ZERO tactic blocks, new helpers, imports, algorithms, axioms or field changes.

## Files and proof dependencies

| Candidate | Uses only published base laws/readers, except listed candidate dependencies |
|---|---|
| pow_val_add_GT.proof.lean.inc | ZMod.val_add, pow_mod_card, B.card_GT, pow_add, Core congrArg/trans. |
| pow_val_neg_GT.proof.lean.inc | Previous pow_val_add_GT candidate; neg_add_cancel, ZMod.val_zero, pow_zero, eq_inv_iff_mul_eq_one. |
| expVec_neg.proof.lean.inc | expVec_apply, published Group.pow_val_neg, funext/congrArg. Fully independent of other admissions. |
| expVec_smul.proof.lean.inc | expVec_apply, published Group.pow_val_mul, Nat.mul_comm, pow_mul. Fully independent. |
| expVecT_add.proof.lean.inc | expVecT_apply and the supplied pow_val_add_GT candidate. |
| expVecT_neg.proof.lean.inc | expVecT_apply and the supplied pow_val_neg_GT candidate. |
| expVecT_smul.proof.lean.inc | expVecT_apply, published Group.pow_val_mul_GT, Nat.mul_comm, pow_mul. Fully independent. |
| pairTensor_expVec.proof.lean.inc | pairTensor_apply, expVec_apply, expVecT_apply, published Group.bilinear_pow and Group.pow_val_mul_GT. Fully independent. |
| expVec_tensor_left.proof.lean.inc | expVec_apply, published Group.pow_val_mul and Mathlib pow_mul. Fully independent. |
| expVec_tensor_right.proof.lean.inc | Same plus scalar mul_comm. Fully independent. |

The earlier expVec_add fragment remains unchanged. Integrate target-group scalar add before
neg, then the target vector wrappers if avoiding dependencies on admitted constants.
Largest fragment14 lines/max92 columns; largest proof body7 lines. Existing proof sketches
remain verbatim. Actual parent elaboration, Rule10 seals and axioms are still required.

## Exact header availability

The actual names are expVecT_add/expVecT_neg, NOT expVecGT_add/expVecGT_neg. No existing
expMat_add/neg or expMatT_add/neg header exists in the live M0 module. None was invented.
The expMat/expMatT ENTRY readers are already rfl. The remaining matrix-action/pairing
statements depend on finite groupDot/pairVec transport, so treating them as independent
coordinate add/neg wrappers would hide a missing prerequisite. No new helper is necessary
for the proofs supplied here; matrix action proofs are a later stage after groupDot.

## Rule10 and overlap

- TCSlib operations appear only through expVec/expVecT/pairTensor application readers and
  published Pairing.Group scalar/pairing theorems. No algorithm definition is unfolded.
- Mathlib/Core pointwise vector operations are notation; scalar-action multiplication is
  normalized only inside an explicit `show` in each smul proof. No foreign definition is
  passed to simp/rw/unfold. All bodies are funext/congruence/transitivity terms.
- Source-group pow_val_add/neg/mul and GT pow_val_mul are reused; not reproved.
- GT add/neg are the already declared/disclosed missing GT analogues. Their proof route is
  a disclosed near-copy of the SOURCE Group laws specialized to GT, reusing Mathlib's
  finite-group pow_mod_card and B.card_GT. No new generic finite-group theorem is proved.
- No proof uses exponent extraction, arbitrary scalar representatives, Classical choice,
  existing local sorry beyond the explicitly supplied two GT candidate dependencies, or
  the constant it is proving.

No mathematical obstruction was found: all identities are coordinate specializations of
the published modular power/pairing laws. Index types may be empty, and bases may be1.
Static risk for parent checking is ordinary implicit-instance normalization in the two
smul `show` terms; their statements and algebra are unchanged. Parent can simply choose
the independent source negation/tensor terms first if sequential proof checking is desired.

Searches and missing-name evidence are in coordinate-laws-searches.txt. exact?/apply?
probes are explicitly deferred to parent; no candidate is labeled Lean-passing here.
