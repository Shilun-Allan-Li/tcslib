# MatrixDH M0 scratch draft review

Files:
- Defs.lean: 195 lines, maximum width 97; 5 definitions with 5 term-rfl readers;
  5 substantive statement admissions.
- SelfReduction.lean: 323 lines, maximum width 96; 9 definitions/abbreviations with
  9 term equation/iff readers, plus proved term-only finite/nonempty facts;
  6 substantive statement admissions.

No Lean/lake/build/proof-check command, git mutation, or additional agent was used.
There are zero tactic blocks. All exact?/apply? probes and elaboration are pending lead checks.
No invFun, Classical.choose, exists_pow_eq, or pow_val_bijective token occurs in either file.
No custom Fintype instance, Sigma sampling instance, sampler bridge or machine is constructed.

## Construction checked by hand

The canonical JLS challenge supplies group representations of
A0=((a,0),(0,b),(1,1)) and c=(ar,bs,r+s) in the real branch or c=(ar,bs,t) in the random branch.
Advice supplies L of dimension l-by-3, known masks S for other real columns, known U for
other random columns, and one index j in Fin(d+1). The preprocessor computes:

- [M_i0]=[a]^(L_i0) * g^(L_i2), [M_i1]=[b]^(L_i1) * g^(L_i2);
- [v_i]=[ar]^(L_i0) * [bs]^(L_i1) * [last]^(L_i2);
- columns k<j are [M*S_k], column k=j is [v], and columns k>j are [U_k].

The sentinel j=d never uses the embedded challenge column and makes the advice type
inhabited even when d=0. The proof chooses a genuine j<d when a nontrivial hop is needed.
All scalars are advice; no exponent is recovered from a group element.

Real A0 fails to have rank two exactly when a=b=0: probability p^-2. Conditional on rank
two, uniform L maps to uniform M=LA0 and real response M(r,s).

For random c, det(A0|c)=ab(t-r-s). Therefore its good probability is (1-1/p)^3. Conditional
on invertibility, L(A0|c) is uniform in l-by-3 matrices, supplying uniform M and independent
uniform challenge response. Its bad probability is 3/p-3/p^2+1/p^3. The total two-branch
comparison error is 3/p-2/p^2+1/p^3, bounded safely by 4/p for p prime.

One hybrid index and all other masks/randomizers are selected by averaging, separately
at each kappa but as one advice family. Thus one realiser B suffices, and the core bound is

  mddhAdv D(kappa) <= d(kappa)*dlinAdv B(kappa) + 4*d(kappa)/p(kappa).

It is NOT a sum over a parameter-dependent family of NUPPTs. This matters for asymptotic
negligibility: no unjustified summation of an unbounded set of negligible functions occurs.

This directly consumes canonical JLS DLIN; the zero-diagonal event is already included.
Do not add Linear.dlinMatrixSlack again on this direct route.

## Public parameter and advice APIs

MDDHChallenge shares PublicParams from MatrixDH/Parameters. It stores no generator coins.
Its encoding pairs pp.encode with row-major group matrix words. Encoding is injective on
all reachable public objects; exact length is

  4*descLen + (2+4*l+l*d)*wG + 8.

MddhAdvice p d l kappa is a product of:

- Fin(d(kappa)+1),
- l(kappa)-by-3 residues,
- 2-by-d(kappa) residues,
- l(kappa)-by-d(kappa) residues.

The default is (0,0,0,0), independently of any nonzero assumption. Its finite proof installs
only a LOCAL NeZero(p(kappa)) obtained from the lead's shared orderSchedule_neZero lemma.
No extra hypothesis on the prime schedule is introduced.

Advice encoding pairs unary kappa with shortest binary d(kappa), l(kappa) headers (using
Candidates.natToList at Nat.size), followed by a one-hot index and Modular.encodeMatrix
blocks at G.wG(kappa). It includes numeric dimensions so one uniform preprocessing target
can work across polynomial dimension choices without hardwiring/evaluating their syntax.
The polynomial bound includes 2*kappa+2*d+2*l+10 for paired headers, d+1 for one-hot index,
and (3*l+2*d+l*d)*wG for scalar blocks. The public theorem is
length_mddhAdviceEnc_le (a bound, not equality).

Only Mathlib ZMod.ringEquivCongr transports advice into the drawn field. Its equality comes
from the shared order_eq_of_publicParams; no new cast predicate or primitive is defined.
Use ringEquivCongr_val to compare advice encodings after the transport.

## Realisation and core quantifiers

`G.dlinToMddh p hp d l D omega kappa c r` is EXACTLY

  D.runAtL kappa (G.mddhPre p hp d l kappa (omega kappa) c)
    (r.take (D.coinLen kappa)).

`mddhAdv_le` quantifies D, then EXISTS one advice family, then EVERY B satisfying shared
RealizesOn G.dlinEnc D.coins, then every kappa. Its docstring records encoded-challenge and
layout-length-only scope of the shared predicate. MDDHRealizable quantifies only over
machine distinguishers D:NUPPT, not arbitrary typed functions, and has a proved iff reader.
The later target-to-realiser link can use exists_realizesOn_of_preTarget_id with:

- enc := G.dlinEnc;
- encOmega := G.mddhAdviceEnc p hp d l;
- pre := G.mddhPre p hp d l;
- bound := G.mddhAdviceLen d l;
- length bound := length_mddhAdviceEnc_le.

The bodies of algorithms use only proved common order-transport lemmas, not admitted
statistical lemmas. No efficiency target is a hypothesis of the raw quantitative theorem.

## Nearest relatives and disclosed overlap

- groupMatrixEnc and its length/injectivity facts parallel
  Encoding/Modular.lean:65,89,126. Those encode ZMod through natToList and cannot encode
  arbitrary unknown group elements without recovering exponents. The new encoder uses
  the existing injective encG and otherwise the same row-major block organization.
  This is disclosed representation-specific near-copy glue; no scalar encoder is copied.
- Matrix sampling/game/advantage follow Pairing/Assumptions.dbdhGame's published pattern
  and the new Linear module. Shared PublicParams and Probability/Advantage APIs are reused.
- MddhAdvice finiteness is existing finite-product/function inference under the proved
  local schedule NeZero. The cast is Mathlib ZMod.ringEquivCongr (Basic.lean:419), with
  ringEquivCongr_val:459. No local variant is introduced.
- Advice scalar blocks reuse Modular.encodeMatrix, encodeMatrix_eq, encodeMatrix_length,
  encodeMatrix_injective. Binary headers reuse Candidates.natToList/length_natToList.
- Width injectivity MUST-REUSES
  AdvancedEncryption.IdentityBased.BB1Machine.order_le_two_pow,
  BonehBoyenMachine/Draws.lean:156. The lead authorized importing that file solely for this
  public lemma. This undesirable Pairing-to-IBE dependency is disclosed; requested future
  promotion: move the EXISTING width lemma into common Pairing once scope opens, rather
  than reprove it here. No draw/decoder/Words declaration is used.
- Hybrid selection reuses Games.exists_advantage_hybrid_gap (Advantage.lean:122).
  Advice averaging must reuse LamportReduction.exists_expect_sample_le
  (Authentication/Signatures/Lamport/Averaging.lean:114), now explicitly imported, and
  ProbComp.abs_expect_sub_le_expect (Games/Probability.lean:409).
- Probability couplings reuse expect_sample_equiv:304, expect_sample_comm:313,
  expect_const:174, prob_split (Games/Hopping.lean:77), and existing event bounds.
- Negligibility uses EnsembleLemmas.negligible_polyExpr_mul
  (Asymptotic/EnsemblesLemmas.lean:377), plus shared Negligible and Subexponential APIs.
  SubexpSmall.mul_pow:204, const_mul:190, add:176, mono:152, negligible:218 are reused;
  no analytic closure theorem is re-proved.
- Scalar rank/algebra normalization should use Matrix.det_fin_three (Determinant/Basic:811)
  and the published matrix equivalence/surjectivity API, not a copied determinant theorem.

## Searches performed

Read at the active lead worktree, base plus the lead's new Parameters/Exponents/Linear:

1. All introduced names:
   rg -n 'mddhAdvice|mddhPre|dlinToMddh|mddhSlack|MDDHRealizable|groupMatrixEnc|MDDHChallenge|mddhEnc|mddhGame|mddhAdv' \
     TCSlib .lake/packages/mathlib/Mathlib
   No matches before writing the scratch modules.
2. Group encoding by name/shape:
   rg -n 'encode.*[Gg]roup|[Gg]roup.*[Ee]ncod|encode.*[Mm]atrix|[Mm]atrix.*Str|groupMatrix' \
     TCSlib/Cryptography/Encoding TCSlib/Cryptography/Pairing
   Found only existing modular-matrix encoding and public-parameter encoding.
   Also searched encodeMatrix/matrixEncode/encode.*Matrix and List.ofFn.*List.ofFn/
   flatten-flatten shapes in Encoding, Pairing and encoding support folders. Existing
   generic modular encoders and DyadicUniform proofs were the nearest relatives.
3. Cast and order width:
   rg -n 'order_le_two_pow|card_G.*2|encG_injective|ringEquivCongr|cast.*ZMod|castHom' \
     TCSlib/Cryptography/Pairing \
     TCSlib/Cryptography/AdvancedEncryption/IdentityBased/BonehBoyenMachine/Draws.lean \
     .lake/packages/mathlib/Mathlib/Data/ZMod
   Confirmed existing width helper and Mathlib cast equivalence/readers.
4. Coin activation:
   rg -n 'coinLen_eq|coinLen.*eval|def coinLen' TCSlib/Complexity/Randomized/PPT.lean
   coinLen:168 and coinLen_eq:171; exact dlinToMddh layout follows the shared realisation API.
5. Read shared Asymptotic/Realization.lean:96-145 and :239 target-to-realiser lemma.
   No predicate variant or local copy was written.
6. Rank and matrix determinant shapes:
   rg -n 'rank.*uniform|full.*rank|card_GL_field|det_fin_three' \
     .lake/packages/mathlib/Mathlib/LinearAlgebra/Matrix/GeneralLinearGroup/Card.lean \
     .lake/packages/mathlib/Mathlib/LinearAlgebra/Matrix/Determinant/Basic.lean \
     TCSlib/Cryptography/Pairing
   Existing card_GL_field:82 and det_fin_three:811; no assumption-specific rank result.
7. One-hot encodings:
   rg -n 'oneHot|one_hot|onehot|decide.*Injective|Injective.*decide' \
     TCSlib/Cryptography/Encoding TCSlib/Cryptography/Pairing \
     .lake/packages/mathlib/Mathlib/Data/Fintype .lake/packages/mathlib/Mathlib/Logic
   No matches.
8. Exact source/read checks:
   ZMod.Basic:419,459; Candidates.Arithmetic:97-109; Nat.Size:81,92,123;
   NumberTheory.Primality:655; Lamport/Averaging:114; Games.Advantage:122;
   Games.Probability:409; EnsemblesLemmas:377. No helper proof has been copied.

Pending every exact?/apply? helper probe, actual declaration elaboration and axiom/style/
Rule-10 checking. The scratch draft is not a claimed passing checkpoint.

## Imports and cache roots

Defs imports the new Pairing.Linear only. SelfReduction imports Defs, shared Realization,
EnsemblesLemmas, Lamport.Averaging, Modular, and BB1 Draws for the published width lemma.
No new direct Mathlib root is needed merely to elaborate these statements. Later proof
files may need precise Matrix.ToLinearEquiv/NonsingularInverse and determinant/card roots;
add those only when the actual proof uses them and follow the narrowed-cache rule.
