# Partial garbling sources and the layered specialization

Verified sources: AGW20 pp11–12,37–39 and IW14 pp6–11 were read/rendered in place. This audit
also re-inspected complete IW14 pp6,8,11 PNGs and the previously reviewed AGW37–38 formulas.
Printed=PDF page for these papers. The five hash lines are recorded by the parent before
source access. No PDF, extracted paper text or page image is copied into proposed delivery.

Paths are relative to FunctionalEncryption/. Raw definitions carry laws; efficient interfaces
carry uniform algorithm efficiency. M0 admitted proof obligations remain explicit.

## Source obligations and concrete syntax

| Source location | Actual claim / formula | Lean counterpart and fidelity |
|---|---|---|
| Wee Lemma1 pp8–9 = AGW Lemma2 p12 | Four efficient lgen,pgb,rec,pgb*; matrices depend only on f. | PartialGarbling.Raw has explicit L1/L0/eval/recVec and law fields; PartialGarbling adds lgen_eff/rec_eff uniform witnesses. Matrix arithmetic defines pgb/pgb*. No bare interface omits required efficiency. |
| AGW Lemma2 p12; (32) p38 | Correct dimensions L1:(m+n'−1)×(ℓm), L0:(m+n'−1)×m. | Raw L1 rows=TIdx⊕Fin n', cols=Finℓ×MIdx; L0 same rows, cols=MIdx. W1 corrected explicitly. |
| AGW Lemma2 p12 | Randomness length t_rng=m+n'−1, final n' entries are tbar. | auxCount+1=mCount; draw=(TIdx⊕Fin n')→ZMod p. mCoord/tCoord canonical explicit equivalences. No opaque Fintype.equivFin. |
| AGW(28) p37 | p=L_(x,z)(t;1). | Layered incidence matrices and pgbCore give this specialized last-column randomization, reordered as in(31). A general L/determinant/ABP datatype is not introduced. |
| AGW(29) p37 | Reconstruction det(L_x|p)=f(x)^T z; linear in p. | Layered.forward/rec, reconstruct_spec: dotProduct p recVec=dotProduct z eval, for EVERY draw. Proof route uses telescoping path values. |
| AGW(30) p37 | Simulated column is (L_x|e1*µ)(t;1). | pgbStarCore puts µ at m0=root. groupPGStar multiplies supplied g^µ at that coordinate after zero-leak PG*. |
| AGW(31) p38 | Output rows first: (z−tbar, t^T Lbar_x^T). | Raw output type Fin n'⊕MIdx; exact pgbCore branch readers. |
| AGW(32) p38 | Lbar_x^T=L1(x⊗I_m)+L0. | publicTensor plus L1/L0; Layered.matrix and action laws. One variable-labelled incidence matrix per public coordinate, constant labels in L0. |
| AGW Algorithm rec p38 | Distinguished non-output reconstruction coordinate equals1. | root forward value=empty product1, m0=root, m0_coord=0. This is used by Pi's simulated leak placement and group lift. |
| AGW AppendixB p38 | KeyGen states corrected L1/L0 dimensions. | Corroborates W1 only. Extended/unbounded-slot AppendixB scheme is not implemented or claimed. |
| AGW Remark1 p11; AppendixB final Dec p39 | Scalar extraction by bounded brute-force discrete log. | Excluded. This unit outputs the value in GT and never implements the paper's bounded scalar decoder. |
| IW Def1 p6 | Rec correct with probability1; simulated and real garbling identically distributed. | Raw rec_spec for every t; Raw.privacy/exactPrivacy equality of expectations for every test, not negligible/statistical-distance approximation. |
| IW Def1 continuation p7 | Families require an efficient description-generation algorithm. | PartialGarbling efficiency fields and PGTargets, quantified before κ and arbitrary positive p. No per-modulus nonuniform machine witness. |
| IW Def1 “affine” p6; variants p7 | Strong local syntax uses a single input coordinate per output. | NOT claimed for the general matrix expression. Here fixed-coin garbling is general degree-one in x,z. Cite Theorem3's syntax, not Corollary1's locality transformation. |
| IW Thm3 p8 | Private inputs only on edges into last t_tail vertices; output length t_tail(|V|−1), input degree1, reconstruction degree t_tail. | The chosen layered ABP interpretation has private variables only on edges into ONE sink (t_tail=1). Output n'+m=|V|−1, reconstruction linear. t_tail is not t_rng. |
| IW §4.2 pp9–11 | Last t_tail columns of R1 L R2; correctness by det; privacy by identical group-translation laws. | At t_tail=1 the AGW last-column specialization. Path-sum translation supplies the same law; full matrix group/canonical-form proof is not formalized. |
| IW p11 privacy | R1LR2 and randomized canonical form have identical distributions. | Layered.exact_privacy uses Equiv.addRight(−shift) and shared expect_sample_equiv. No additional privacy loss term. |

## Exact layered specialization

| Ingredient | Formula / code family | Source reading / derived choice |
|---|---|---|
| Coefficients | PolyTensor p ℓ n' d; f_C(x)_j=Σ_tau C_j,tau Π_i xhat(x)_(tau_i). | Bounded-degree polynomial-vector restriction of the source ABP class; sufficient for GJLS§9. |
| Nodes | MIdx=Σ_(k:Fin(d+1)) (Fin k→Fin(ℓ+1)); root empty tuple. | Prefix-node representation of layered ABP; no new generic ABP model. |
| Auxiliary coins | TIdx=Σ_(k:Fin d) (Fin(k+1)→Fin(ℓ+1)); final output block Fin n'. | Node coins exclude root, with output coins last. |
| Counts | m=Σ_(k=0)^d(ℓ+1)^k; aux=m−1; t_rng=m+n'−1. | Source-required sizes, independent of coefficient values. mBound=nodeBound polynomial; all layered keys have the same actual m,t. Generic Raw permits smaller function-dependent m under this bound. |
| Coordinates | tupleCoord=finFunctionFinEquiv, then sigmaCongrRight and finSigmaFinEquiv. | Arithmetic base-(ℓ+1) tuple rank and depth order, reused Mathlib APIs. No cardinality-choice ranking or custom Sigma instance. |
| L1 | Variable parent→child incidences. | Coefficient of each x_i in the source incidence matrix. |
| L0 | Padded constant-one incidences, −1 at non-root diagonals, terminal C entries. | Constant part of the same matrix. Output/sink edges give the output-minus-last-coin block. |
| Rec | Output coordinates f_C(x), node coordinates forward prefix products. | Each non-root forward value is parent-forward times edge label; root1. Dot product telescopes. |
| Backward | Explicit suffix sums to the sink, private z at output nodes. | No recursive witness choice or scalar extraction. Fin.append/standard casts concatenate prefix/suffix. |
| Shift | Output coin shift=z; auxiliary coin shift=backward value of its node. | Pointwise real(t)=ideal(µ,t−shift), µ=z·f_C(x). |
| Exact privacy | Translation t↦t−shift is a finite additive equivalence. | Existing Equiv.addRight and ProbComp.expect_sample_equiv, not a new measure/reindexing lemma. |
| Zero extensions | d=0, n'=0, ℓ=0 supported. | Derived totality extension beyond explicitly discussed source examples. If d=n'=0, draw type is singleton, garbling has one zero node coordinate and rec there is1. Not attributed as a separately numbered paper theorem. |

## Disclosed proof-route deviation

The algorithmic syntax is AGW(28)–(32), specialized to the layered polynomial-vector DAG.
Reconstruction uses FORWARD path products and cancellation, replacing determinant/cofactor
expansion. Privacy uses BACKWARD path values and a translation, replacing the source matrix
canonical-form argument. These prove the same specialized rec/privacy statements. They do
not claim the full general-ABP theorem or an affine-locality compiler.

IK02 is mentioned only as cited in AGW/IW. Its determinant lemma is NOT imported/reproved.
Wee17 and EHKRV13 are likewise cited only through the supplied papers. No unread primary
paper is claimed as a proof source. Matrix.card_GL_field is used for the independent Pi rank
counting problem, not as a substitute for partial-garbling privacy.
