# Quadratic.quadratic_dec_eq candidate

Status: full scratch candidate checked by inspection only. Root must native-check; no Lean,
lake, build, Git, live edit or extra agent was used. Frozen docstring/header byte-preserved;
one tactic block, no remaining holes/sorry, ≤100 columns. No new helper or statement change.
Dependencies Linear.pi_dec_eq and cross_value_identity are still pending native integration;
therefore no complete/standard-only quadratic-correctness chain is claimed. The latter also
depends on the pending cross_tensor_identity. mixGroup_exp/signalGroup_exp and the Pairing
transport APIs used here are already proved according to the current parent status.

## Normalized intermediate obligations

All scalar values below come from the sampled honest setup/encryption draws:
A1=a.1, A2=a.2.1, s1=s.1, s2=s.2.1. Set y1=s1*A1+z1, y2=s2*A2+z2,
signal=signalScalar s1 z2 y1 s2, F=mixScalar A1 A2, fx=PG.eval f x, egg=e(g,g).

1. hTensor identifies the flattened pairTensor(expVec g y1)(expVec g y2) with
   expVecT egg (privateTensor y1 y2). It is discharged by pairTensor_expVec, the public
   expVecT entry reader, privateTensor_eq and kroneckerMap_apply.
2. hLeak identifies e(g,Linear.leak (expMat g F) x signal) with
   egg^(signal dot (F*fx)). It is discharged through Linear.leak_eq, expMat_mulVec,
   groupDot_expVec, dotProduct_comm and pair_pow_right. This only uses the KNOWN sampled
   scalar F. The arbitrary-group version of Linear.pi_dec_eq is consumed as supplied;
   no arbitrary matrix element is assigned a scalar witness.
3. hValue is exactly cross_value_identity with the honest scalar draws and fx. Its native
   status is pending, not silently assumed proved in the dependency ledger.
4. The main normalization reads all four outer algorithm equations. expVec_vecMul and
   reverse expVec_add identify both masked inputs in every occurrence, mixGroup_exp
   identifies the public matrix, and signalGroup_exp identifies the linear group input.
   The exact honest Linear.pi_dec_eq now applies with setup draw a.2.2, encryption draw
   s.2.2, key draw t, matrix expMat g F, and private scalar signal.
5. hTensor/groupDot_expVecT and hLeak reduce the actual decryption to
   egg^maskedValue * (egg^crossValue)^(-1). Read value_eq; hValue says desiredValue is
   maskedValue-crossValue. sub_eq_add_neg and the target-group add/neg exponent readers
   close the equality.

No sampler, algorithm, inverse encoding, group logarithm, or scalar-existence argument is
constructed. All definitions are consumed via public readers; only local aliases and allowed
Mathlib/core projection/let reduction enter definitional matching. No generated-equation
reader or foreign explicit unfold is used.

## Actual source searches / reads

All reads/searches used current live files, without Git:

* Read QuadraticCorrect.lean:120-173 for exact frozen theorem and surrounding assembly;
  Quadratic.lean:165-346 for SetupDraw/EncDraw and all core/value/dec readers.
* `rg -n 'theorem (pi_dec_eq|leak_eq|pair_expVec|pair_expMat|pow_val_add_GT|pow_val_neg_GT)|bilinear_pow|pair_pow_(left|right)'`
  over LinearCorrect, Linear, Pairing/Exponents and Pairing/Group located exact transport.
* `rg -n 'pairTensor_exp|expVecT.*reindex|groupDot.*comp|groupMulVec.*exp|pow_val_sub|sub.*val'`
  over Pairing and QuadraticCorrect found the complete existing pairTensor_expVec reader,
  so no tensor-pairing helper is needed.
* `rg -n 'pow_val_add_GT|pow_val_neg_GT|sub_eq_add_neg'` over Wee20 files and
  `rg -n 'groupDot_expVecT|expMat_mulVec|groupMulVec_apply'` over QuadraticCorrect/Exponents
  located the existing target-group laws and scalar matrix action.
* Narrow reads inspected Exponents.lean:105-141, :342-355, :399-425, :460-507 and
  LinearCorrect.lean:207-226 for their exact argument/order shapes.
* An initial read tried nonexistent Wee20/Quadratic/Data.lean; structure definitions are
  actually in Wee20/Quadratic.lean and were read there. No inference uses the missing path.

## Exact dependencies / approximate live lines

* Quadratic.lean: setupCore_eq (251), encCore_eq (271), keyCore_eq (291), value_eq (308),
  dec_eq (328); signalScalar_eq (135), mixScalar_eq (87) are not unfolded here.
* QuadraticCorrect.lean: mixGroup_exp (52), signalGroup_exp (75),
  cross_value_identity (111, pending).
* LinearCorrect.lean: pi_dec_eq (212, pending); Linear.lean: leak_eq (315).
* Pairing/Exponents.lean: expVec_add (204), expVec_vecMul (358), expMat_mulVec (342),
  groupDot_expVec (near 280), groupDot_expVecT (311), expVecT_apply (137),
  pairTensor_expVec (467), pow_val_add_GT (182), pow_val_neg_GT (192).
* Pairing/Group.lean: pair_pow_right (187); Classes.lean: privateTensor_eq (294).
* Mathlib: dotProduct_comm, Matrix.kroneckerMap_apply, sub_eq_add_neg.

## Native integration focus

The key unverified elaboration points are dependent record projections after the public core
readers, matching piDim/n1.mul n2 dimensions through the existing notation APIs, repeated
normalization of y1 in both its own ciphertext field and the linear signal, and let-alias
matching when applying hTensor/hLeak. The simp list deliberately uses the complete published
algorithm and transport equations and does not expand Linear's cores before pi_dec_eq.
If a failure occurs, retain the frozen target and isolate that exact normalization subgoal;
no new generic helper is currently mathematically required.
