# io-phfe: duplication sweep, r2

Static sweep, refreshed 2026-11-18 for pack r2. **Line numbers re-checked:** the `TCSlib/` tree is
identical (`849ee9454cff17b1fb15a22183526d7e071a9669`) at r1's records tip `0fec2589` and at the r2
records tip `1a9a32959cc58d7a882d0f6a7e2b0003b52f82ae`, so r1's lines stand; 27 rows across §§ 1–4
were re-read at their stated lines (all matched), and every new row was read directly. At
`foundations/subexp` head
`cbce64d1c135c710b7c036968ed9d4f21414aa72` (the expected `<BASE>` or its ancestor) the tree differs
only by `Foundations/Subexponential.lean` (new) and three lines of `Foundations.lean`, so every row
below holds there too. Mathlib is the pinned `029db123ddaa7f8fd0d18cea3b1b33bf84dacd1e`. The worker
re-checks every row at `<BASE>`, because Stage 2 or a stacked in-house PR may move some.

**What changed from r1:**
- § 0 (new): the `Foundations/Subexponential` API (must-reuse).
- § 2: the machine-building rows are kept for reference, but **Phase A builds no machines**. Their
  status is "Phase B" except the exponent decoder (`BB1Machine.draw` and its bounds), which reduction
  functions use now.
- § 4a (new): the NUPPT activation, uniformity and time-bound items that Phase A's realiser predicate
  and written efficiency `Prop`s are stated with.
- § 5a (new): Mathlib items for the MDDH self-reduction and partial garbling.
- § 7 (new): false friends for partial garbling and branching programs.
- The rule against touching `Pairing/Assumptions.lean` stands (cleanup S2-A step A05 edits it): its
  rows are **pattern only**, and the job's new files need not import it.

## 0. Subexponential security (`Foundations/Subexponential.lean`, draft PR #374, branch `foundations/subexp`, head `cbce64d1`)

Read with `git show origin/foundations/subexp:TCSlib/Cryptography/Foundations/Subexponential.lean`.
Namespace `TCSlib.Cryptography`. All rows are **must**: no local re-proof of any of them, and no
second "subexponentially small" predicate.

| Name | Line | Reuse | Note |
|---|---|---|---|
| `SubexpSmall c μ` (eventually `\|μ n\| ≤ 2^{-n^c}`), `subexpSmall_iff`, `subexpSmall_iff_eventually` | :71, :76, :81 | must | the slack and advantage bounds |
| `eventually_const_mul_rpow_mul_two_rpow_neg_le` | :132 | must (if needed) | the analytic core behind `.mul_pow` |
| `SubexpSmall.mono`, `.mono_exponent` | :152, :163 | must | domination; lowering the exponent to `min(c, 1)` |
| `SubexpSmall.add`, `.const_mul`, `.mul_pow` | :176, :190, :204 | must | sums of hops; polynomial factors (q keys, draws), to any `c' < c` |
| `SubexpSmall.negligible` | :218 | must | subexponential ⇒ negligible |
| `SubexpSmall.comp_of_rpow_le` | :238 | must | re-indexing by a polynomial parameter ([JLS26, Remark 2.1]) |
| `subexpSmall_zero`, `subexpSmall_two_pow_neg` | :253, :258 | must | perfect hops; `2^{-κ}` slack (1/p under `2^κ ≤ p κ`) |
| `SubexpHard adv` (`∃ c > 0, ∀ D, SubexpSmall c (adv D)`), `subexpHard_iff` | :274, :279 | must | `SubexpDLIN := SubexpHard G.dlinAdv`; `SubexpSimSecure` over `NUPPT × PolyExpr` |
| `SubexpHard.negligible`, `SubexpHard.comp_of_rpow_le` | :286, :293 | must | |
| `tendsto_rpow_mul_two_rpow_sub` | :95 | no (private) | do not copy |

**Rule (binding, in the dispatch).**
- An undisclosed re-proof of a public TCSlib or Mathlib lemma is a **major**. This includes an
  inline re-derivation inside a proof, and a private copy with renamed binders.
- Search before every helper: by name, by statement shape (grep), and by `exact?`/`apply?` in a
  scratch probe.
- Disclose every helper with its nearest relatives and the searches run (`REPORT.md` § *Overlap
  and reuse*).

Column **Reuse:**
- **must**: use it, never restate it;
- **must (pattern)**: follow its form, copy no proof;
- **if needed**: use it rather than re-prove it, should the route need the fact;
- **no**: listed to prevent a false match.

## 1. Pairing substrate (`TCSlib/Cryptography/Pairing/`)

| Name | Where | Reuse | Note |
|---|---|---|---|
| `BilinearGroup` (fields `pair`, `gen`, `encG`, `encT`, `card_G`, `card_GT`, `order_prime`, …) | `Pairing/Group.lean:96` | must | the symmetric bundle; G₁ = G₂ = G for Wee20 |
| `pow_val_bijective_of_prime_card` | `Group.lean:154` | must | `a ↦ g^a` bijective ℤ_p → M (any prime-order group); for "g^u uniform" and target-group uniformity |
| `BilinearGroup.factPrime`, `neZeroOrder`, `nonempty_ne_one` (instances) | `Group.lean:167`, `:170`, `:173` | must | `ZMod B.order` is a field; G* is nonempty for `sample` |
| `bilinear_pow`, `pair_pow_left`, `pair_pow_right` | `Group.lean:178`, `:183`, `:187` | must | bilinearity; the vector pairing lemma is built on these |
| `natCard_G`, `exists_pow_eq`, `pair_comm`, `pow_order`, `pow_order_GT` | `Group.lean:191`–`:212` | must | |
| `pow_val_mul`, `pow_val_mul_GT` | `Group.lean:218`, `:222` | must | exponents act through ℤ_p (G and G_T) |
| `pair_ne_one`, `pow_val_bijective` | `Group.lean:232`, `:248` | must | e(x, x) ≠ 1; `a ↦ e(x,x)^a` bijective |
| `pow_val_add`, `pow_val_neg` | `Group.lean:254`, `:260` | must | G only. A G_T analogue is **absent**: derive it from `pow_mod_card` (Mathlib) and disclose it as a near-copy of `pow_val_add` |
| `pow_val_bijective_of_ne_one` | `Group.lean:266` | must | |
| `BilinearGen`, `desc`/`desc_eq`, `length_desc`, `inst`/`inst_eq` | `Group.lean:283`–`:318` | must | |
| `BilinearGen.OrderAtLeastExcept`, `orderAtLeastExcept_iff` | `Group.lean:328`, `:333` | must | the headline's `hN` |
| `tupleStr`/`tupleStr_eq`, `bdhStr` | `Pairing/Assumptions.lean:79`, `:95` | must (pattern) | the form of `dlinStr` |
| `dbdhGame`/`_eq`, `dbdhAdv`/`_eq`, `DBDHAssumption`/`_iff` | `Assumptions.lean:225`–`:270` | must (pattern) | the form of `dlinGame`, `dlinAdv`, `DLINAssumption` (sequential draws) |
| `prob_eq_encT_le`, `exists_bdhDistinguisher`, `distinguisherL_tupleStr`, `tupleBdh` (private) | `Assumptions.lean:203`, `:166`, `:189`, `:113` | no (private) | private: no import is possible, and a copy needs disclosure |
| `BilinearGen.Ops` (`orderStr`, `mulG`, `powG`, `pairStr`, `mulT`, `memT` and their `_poly`/`_spec`) | `Pairing/Operations.lean:68` | must | the only group operations a machine may use |

**Not in TCSlib** (new work, no duplication risk):
- DLIN, k-Lin, MDDH (no hit for `dlin`, `k-Lin`, `MDDH`, "decision linear" under `TCSlib/`);
- vectors and matrices of group elements;
- any functional encryption (no hit for "functional encryption", `PHFE`, "partially hiding");
- arithmetic branching programs (`Complexity/BranchingPrograms/` is Boolean, Barrington-style).

## 2. Machines and reductions (IBE / BB1 precedent)

**Phase A status.** The reduction functions use only the decoder rows (`blockLen`, `draw`,
`order_le_two_pow`, `statClose_draw`, `abs_expect_draws_sub_le`): **must**. The machine-assembly
rows (`exists_bb1_distinguisher`, the `Words` rows, and the `PolyHandler` rows in § 3) are
**Phase B**: listed so that Phase A neither re-creates them nor builds a machine. The IBE interface
rows remain **must (pattern)** for the FE syntax and the oracle game.

| Name | Where | Reuse | Note |
|---|---|---|---|
| `BB1Machine.blockLen`/`blockLen_eval` | `IdentityBased/BonehBoyenMachine/Draws.lean:131`, `:134` | must | n = κ + wG + 1 |
| `BB1Machine.draw`/`draw_eq` | `Draws.lean:142`, `:148` | must | the ℤ_p exponent from n·n coins: **the** machine sampler (settled convention) |
| `BB1Machine.order_le_two_pow` | `Draws.lean:156` | must | p ≤ 2^{wG}: residue width `wG` is lossless |
| `BB1Machine.statClose_draw` | `Draws.lean:168` | must | (1/2)^n-close to uniform |
| `BB1Machine.abs_expect_draws_sub_le` | `Draws.lean:448` | must | `cap` drawn vs ideal exponents on a {0,1} test |
| `BB1Machine.exists_simulate_tape_eq_pure` | `Draws.lean:408` | must (pattern) | BB1-specific (`drawStep`); its proof pattern (determinism from a tape) is the model |
| `BB1Machine.pS`, `modS`, `negS`, `addS`, `mulS`, `invS`, `mulGS`, `powGS`, `listToNat_modS`, `listToNat_invS`, `mulGS_ofFn`, `powGS_ofFn`, `poly_mulGS`, `poly_powGS` | `BonehBoyenMachine/Words.lean:147`–`:162`, `:357`–`:361`, `:489`–`:543` | no (pattern only) | tied to BB1's input layout (`zD`). A layout-generic twin is a **near-copy**: disclose it and request a promotion |
| `BB1Machine.rU` … `rX` | `Words.lean:97`–`:107` | no | duplicates of `Games.PolyHandler` readers (S2-A Q-A5). Use the `Games` readers |
| `exists_bb1_distinguisher` | `IdentityBased/BonehBoyenMachine.lean` (step 3) | must (pattern) | the reduction's assembly: T1 + `exists_toCompOn_of_toComp` + averaging + draws |
| `IBEScheme` and its fields `encPP_inj`, `encSK_inj`, `encCT_inj` | `IdentityBased/Defs.lean:106` | must (pattern) | interface style; **do not refactor** (§ 9 of the design) |
| `IBEScheme.sidImpl` and case lemmas, `oracleImpl`, the `_onSpec` readers, `sidGame`/`_eq`, `SIDSecure`/`_iff` | `Defs.lean:258`, `:352`, `:529`, `:550` | must (pattern) | the oracle-game form of the selective game |
| `FixedLengthScheme.decAnswer`, `splitHalf` | `Encryption/PrivateKey/OracleSecurity.lean:161`, `:173` | must | `⟨1, answer⟩` / `⊥` answers; two-message splits |

## 3. Games framework (`TCSlib/Cryptography/Games/`)

| Name | Where | Reuse |
|---|---|---|
| `ProbComp`, `sample`/`sample_eq`, `expect`, `prob`, `expect_bind`, `expect_map`, `expect_sample`, `expect_add`, `expect_const_mul`, `expect_const`, `expect_sum`, `expect_mono`, `prob_eq_expect`, `prob_bind`, `prob_pure` | `Games/Probability.lean:78`–`:230` | must |
| `expect_sample_equiv` (reindex a sample by an `Equiv`: one-time pads, invertible maps) | `Probability.lean:304` | must |
| `expect_sample_comm`, `expect_expect_sample`, `expect_sample_unique`, `expect_sub`, `expect_sample_update`, `expect_sample_coord` | `Probability.lean:313`–`:383` | must |
| `abs_expect_sub_le`, `abs_expect_sub_le_expect` | `Probability.lean:393`, `:409` | must |
| `accept`, `advantage` (+`_eq`), `advantage_triangle`, `advantage_comm`, `advantage_hybrid`, `exists_advantage_hybrid_gap`, `guessAdv_eq_half_advantage` | `Games/Advantage.lean:63`–`:178` | must |
| `prob_split`, `abs_prob_sub_le_of_agree`, `identical_until_bad`, `expect_simulate_congr`, `prob_bad_le`, `expect_simulate_eager` | `Games/Hopping.lean:77`–`:494` | if needed |
| `expect_simulate_rel`, `prob_simulate_rel`, `expect_sample_rel` (couplings of oracle runs) | `Games/Relational.lean:85`, `:111`, `:130` | must (for real/ideal oracle couplings) |
| `Games.freshImpl`, `tapeImpl`, `expect_simulate_tapeImpl`, `extTape*`, `ovr*`, `expect_simulate_abs` | `Games/Tapes.lean:125`, `:167`, `:209`, `:72` | must (fresh vs. tape exponents) |
| `simulate`, `simulate_bind`, `simulate_call`, `QueryImpl.comp`, `simulate_comp` | `Games/Simulate.lean:83`–`:199` | must |
| `bitSpec`, `bitSpec_dom`, `bitSpec_rng`, `zeroBits`, `bitCodec` | `Games/BitCodec.lean:73`, `:77`, `:82`, `:126`, `:220` | must |
| `MachineCodec`, `NUPPT.toComp`, `toCompOn` (+ `_eq`, `_costBoundedBy`) | `Games/Machines.lean:79`, `:233`, `:257` | must |
| `PolyHandler` (+ `input`, `advInput`, `result`, `impl`, `impl_apply`), `exists_handlerMachine` (T1) | `Games/Efficiency.lean:163`, `:332` | must |
| `InteractiveHandler`, `exists_interactiveHandlerMachine`, `exists_toCompOn_of_toComp`, `exists_toOracleAdversary_of_bitCodec`; readers `rU` … `rAns`, `finA` | `Efficiency.lean:411`, `:844`, `:905`, `:960`, `:465`–`:764` | must |
| `prob_sample_eq_uprob`, `expect_sample_pair`, `prob_sample_pair`, `acceptGame`, `distAdv_eq` | `Games/Bridges/Experiments.lean:66`–`:139` | must |

## 4. Probability, closeness, negligibility, machines

| Name | Where | Reuse |
|---|---|---|
| `StatClose` and `.abs_uprob_sub_le`, `.uprob_le_add`, `.refl`, `.symm`, `.mono`, `.trans`, `.map`, `.comp_equiv_left`, `.comp_equiv_right`, `.comp_pushesUniform`, `.abs_uprob_sub_le_prod`, `.prod` | `Asymptotic/Sampling.lean:126`–`:291` | must |
| `OneWay.statClose_pi` (product of closeness; the `cap` draws) | `Asymptotic/OneWayLemmas.lean:276` | must. Two same-named lemmas elsewhere (`ZeroKnowledge/GraphIsomorphismZK/Closeness.lean:165`, `ZeroKnowledge/GraphIsomorphism/SoundnessRep.lean:279`) are ZK-local: do not use them, do not add a fourth |
| `HardcoreBit.PushesUniform`, `pushesUniform_equiv`, `pushesUniform_add_right` | `HardcoreBit/Basic.lean:196`, `:202` | if needed (uniform translation) |
| `uprob`, `uprob_comp_equiv` | `Foundations/Probability.lean:59`, `:165` | must |
| `OneWay.uprob_congr`, `OneWay.uprob_eq_one_div_card` | `OneWayFunctions/Basic.lean:50`, `:144` | must (another `uprob_congr` in `Pseudorandom/Functions/LazySampling.lean:60` is local; prefer `OneWay`'s) |
| `Negligible`, `.mono`, `.add`, `.const_mul`, `negligible_two_pow_neg` | `Foundations/Negligible.lean:57`, `:74`, `:86`, `:143`, `:153` | must |
| `EnsembleLemmas.negligible_polyExpr_mul` | `Asymptotic/EnsemblesLemmas.lean:377` | must (S2-A A07 adds readers in this file; the name is stable) |
| `NUPPT`, `runAt`, `runAtL`, `coinsCongr`, `Uniform`, `ofPolyTime`, `ofPolyTimeUniform` | `Complexity/Randomized/PPT.lean:137`, `:235`, `:240`, `:256`, `:301`, `:345`, `:406` | must |
| `NUPPT.exists_split` | `Complexity/Randomized/Closure.lean:390` | must |
| `NUPPT.distinguisherL` | `Asymptotic/Adversary.lean:381` | must |
| `Candidates.sampleBelowL`, `statClose_sampleBelowL` | `Candidates/DiscreteLog.lean:578`, `:618` | must (through `BB1Machine.draw`) |
| `Candidates.ArithmeticFP`, `natToBits`, `natToList` | `Candidates/Arithmetic.lean:314`, `:97`, `:100` | must (exponent arithmetic in machines) |
| `NumberTheory.listToNat` | `NumberTheory/Primality.lean:655` | must |
| `Encoding.Modular.encodeVector`, `encodeMatrix` (+ `_eq`, `_length`, `_injective`); `decodeVector`, `decodeMatrix` (+ round-trip lemmas) | `Encoding/Modular.lean:51`–`:126`; `Encoding/ModularDecode.lean:47`–`:235` | must (residue vectors and coefficient tensors as strings) |
| `LWE.Family` (exact laws, samplers as separate contracts), `encodeChallenge` | `LWE/Assumption.lean:65`; `LWE/Encoding.lean:42` | must (pattern) |
| `InformationTheory.statDist`, `FinDist.uniform`, `FinDist.map_uniform_equiv` | `InformationTheory/StatisticalDistance.lean:46`; `InformationTheory/FinDist.lean:92`; `Randomness/Extraction/Rejection.lean:45` | if needed. The crypto layer measures closeness by `StatClose`, so prefer that |

## 4a. Activations, uniformity, time bounds (realisers and written efficiency `Prop`s)

| Name | Where | Reuse | For |
|---|---|---|---|
| `NUPPT.output`, `advInput` | `Complexity/Randomized/PPT.lean:179`, `:210` | must | running an adversary's machine with a given advice inside a reduction function |
| `NUPPT.runAt`, `runAtL`, `runAt_eq`, `coinsCongr`, `coinsCongr_ofFn` | `PPT.lean:235`, `:240`, `:249`, `:256`, `:260` | must | `NUPPT.Realizes` (coins and activation) |
| `NUPPT.Uniform`, `NUPPT.Computes` (+ `_iff`) | `PPT.lean:301`, `:328` | must | written efficiency `Prop`s in the `∃ A, A.Uniform ∧ A.Computes f` form; **never a bare `∃ A : NUPPT, A.Computes f`** (see that docstring) |
| `NUPPT.ofPolyTimeUniform`, `runAtL_ofPolyTimeUniform`, `exists_uniform_computes` | `PPT.lean:406`, `:437`, `:448` | must (Phase B) | the bridge from `PolyTimeComputable` to a uniform machine |
| `NUPPT.Computes.polyTimeComputable` | `Complexity/Randomized/Closure.lean:458` | must (Phase B) | the converse, for uniform machines |
| `PolyTimeComputable` (+ `_iff`), `.comp`, `.pairEncode`, `.append` | `Complexity/ClassNP/PolyTime.lean:73`, `:161`; `ClassNP/PolyTimePairing.lean:129`, `:186` | must | written efficiency `Prop`s |
| `FinTM.ComputesInTime`, `FinTM.ComputesFunInTime` | `Complexity/TuringMachine/Finite.lean:276`, `:281` | must | `Wee20.LinearEfficient` ([GJLS21, Def 4.6]) as one uniform machine with a per-input time bound |
| `OracleComp.AllOutputs` | `Games/OracleComp.lean:292` | must | perfect correctness (as `IBEScheme`) |
| `BilinearGen.Ops` (`orderStr` …) | `Pairing/Operations.lean:68` | must | string forms in the efficiency `Prop`s read p with `orderStr` ("p as an input") |

## 5. Mathlib (pinned `029db123`)

| Name | Where | Reuse | For |
|---|---|---|---|
| `dotProduct` (`⬝ᵥ`), `dotProduct_comm`, `add_dotProduct`, `dotProduct_add`, `dotProduct_smul` | `Mathlib/Data/Matrix/Mul.lean:67`, `:79`, `:115`, `:119`, `:241` | must | inner products |
| `Matrix.mulVec_add`, `mulVec_smul`, `mulVec_mulVec`, `vecMul_vecMul`, `dotProduct_mulVec`, `mulVec_transpose`, `vecMul_transpose` | `Data/Matrix/Mul.lean:735`, `:755`, `:824`, `:818`, `:710`, `:1032`, `:1036` | must | `[A s]`, `sᵀ A` |
| `Matrix.vecMulVec`, `vecMulVec_mulVec` | `Data/Matrix/Mul.lean:575`, `:840` | must | z ⊗ z as an outer product |
| `Matrix.kroneckerMap`, `kroneckerMap_apply`, `kronecker_apply`, `mul_kronecker_mul`, `kronecker_assoc`, `one_kronecker_one` | `LinearAlgebra/Matrix/Kronecker.lean:55`, `:60`, `:267`, `:369`, `:375`, `:355` | must | (A ⊗ A)(s ⊗ s), mixed products |
| `Matrix.vec`, `kronecker_mulVec_vec`, `vec_mul_eq_mulVec` | `LinearAlgebra/Matrix/Vec.lean:37`, `:132`, `:145` | must | flattening tensors |
| `Matrix.isUnit_iff_isUnit_det`, `mulVec_injective_iff_isUnit`, `mulVec_surjective_iff_isUnit`, `vecMul_injective_iff_isUnit`, `vecMul_surjective_iff_isUnit` | `LinearAlgebra/Matrix/NonsingularInverse.lean:118`, `:355`, `:340`, `:344`, `:336` | must | uniformity of `A s` / `[A | z]·u` |
| `Matrix.toLinearEquiv'`, `exists_mulVec_eq_zero_iff`, `exists_vecMul_eq_zero_iff` | `LinearAlgebra/Matrix/ToLinearEquiv.lean:53`, `:161`, `:165` | must | invertible maps as `Equiv`s; the kernel vector a⊥ |
| `Matrix.det_fin_two`, `det_fin_three` | `LinearAlgebra/Matrix/Determinant/Basic.lean:800`, `:811` | if needed | det of `[A | z]` for the 2-Lin matrix |
| `Matrix.rank`, `rank_mul_le`, `rank_of_isUnit`, `rank_le_card_width` | `LinearAlgebra/Matrix/Rank.lean:117`, `:178`, `:194`, `:155` | if needed | |
| `Matrix.card_GL_field` | `LinearAlgebra/Matrix/GeneralLinearGroup/Card.lean:82` | if needed | probability that a uniform matrix is invertible |
| `ZMod.card`, `ZMod.val_lt`, `ZMod.natCast_zmod_val` | `Data/ZMod/Defs.lean:164`; `Data/ZMod/Basic.lean:57`, `:197` | must | |
| `Fintype.card_fun`, `Fintype.card_pi` | `Data/Fintype/BigOperators.lean:195`, `:128` | must | |
| `Equiv.mulRight` / `Equiv.addRight` (to_additive) | `Algebra/Group/Units/Equiv.lean:116` | must | one-time pads (`u ↦ u + z`) |
| `pow_mod_card`, `pow_card_eq_one`, `orderOf_eq_prime`, `pow_injOn_Iio_orderOf` | `GroupTheory/OrderOfElement.lean:1012`, `:1003`, `:490`, `:268` | must | a G_T exponent law, if one is needed |
| `MvPolynomial.totalDegree`, `totalDegree_mul`, `MvPolynomial.eval_eq` | `Algebra/MvPolynomial/Degrees.lean:332`, `:403`; `Algebra/MvPolynomial/Eval.lean:237` | if needed | an optional reader from the coefficient-tensor class to `MvPolynomial` (and the later sPRG bridge) |

## 5a. Mathlib additions for MDDH and partial garbling (pinned `029db123`)

| Name | Where | Reuse | For |
|---|---|---|---|
| `Matrix.mul_kronecker_mul` (mixed product) | `LinearAlgebra/Matrix/Kronecker.lean:369` | must | Wee20 (4), (10); `(I_n ⊗ R)(x^⊤ ⊗ I_m) = (x^⊤ ⊗ I_k)R` |
| `Matrix.kronecker_mulVec_vec`, `kronecker_mulVec_vec_of_commute` | `LinearAlgebra/Matrix/Vec.lean:132`, `:112` | must | flattening `(A ⊗ B)` actions |
| `Matrix.det_of_upperTriangular`, `det_of_lowerTriangular` | `LinearAlgebra/Matrix/Block.lean:282`, `:287` | if needed | partial-garbling privacy (the triangular ABP matrix has determinant ±1) |
| `Matrix.rank_le_width` | `LinearAlgebra/Matrix/Rank.lean:161` | if needed | rank events in the self-reduction (ℓ ≤ k case) |
| `Matrix.card_GL_field` | `LinearAlgebra/Matrix/GeneralLinearGroup/Card.lean:82` | if needed | the probability that a uniform matrix is invertible (re-randomisation slack) |

## 6. Parallel and recent work

- **sPRG job (parallel).** It may define bidegree-(d, 2) polynomial maps over ℤ_p and uniform ℤ_p
  laws. Neither job can import the other. Each discloses its representation, and the overlap is
  recorded as a known bridge, not as debt (design-r1 Q10; settled (A) in design-r2 § 7).
- **Cleanup Stage 2 (S2-A, in house now).**
  - A04 adds `ProbComp.mul_prob_le_expect` to `Games/Probability.lean`.
  - A06 moves DL-57's `zeroBits_eq_cast` to `Games/BitCodec.lean` as `Games.zeroBits_eq_cast`.
  - A05 re-points a proof in `Pairing/Assumptions.lean`.
  - A38 edits `Games/Relational.lean` docstrings.

  Use the post-merge names if S2-A lands during the job.
- **Duplication ledger** (`briefs/pass-shelat-ch5-8/duplication-ledger.md`): DL-55 to DL-58 touch
  pairing and IBE helpers. Read it before writing any group or oracle helper.

## 7. False friends (do not use as partial garbling or ABPs)

| Name | Where | Why not |
|---|---|---|
| Yao garbling (`SecureComputation/Garbling*.lean`) | `TCSlib/Cryptography/SecureComputation/` | Boolean-circuit garbling for secure computation; [Wee20, Lemma 1] is an *arithmetic partial* garbling, affine in x and linear in z. No overlap; name new declarations so as not to clash (`PartialGarbling`, not `Garbling`) |
| `BranchingProgram`, `BranchingProgramFamily` | `TCSlib/ComputationalModels.lean:59` (Barrington, Boolean) | Boolean width-w programs; Wee20's ABPs are arithmetic over ℤ_p. The job uses polynomial vectors, with no ABP model |
| `Candidates.ArithmeticFP` | `Candidates/Arithmetic.lean:314` | an assumed string-arithmetic bundle for machines: Phase B only (efficiency); Phase A's typed algorithms compute in `ZMod` |

## 8. In-house items expected at `<BASE>` (check, then reuse)

- `ReductionFn` / `NUPPT.Realizes` (design-r2 Q5(A)): if `<BASE>` has them, they are **must** and
  the job defines no variant; if not, follow the Q5 ruling recorded in `rulings.md`.
- `TCSlib/Cryptography/CoinSampling/` (sampler bridge, in house): if present at `<BASE>`, its ℤ_p
  sampler may replace `BB1Machine.draw` in reduction functions, with disclosure. The job **builds no
  sampler**.
