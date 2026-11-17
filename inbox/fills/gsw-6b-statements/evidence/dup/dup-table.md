# Duplication searches (check 12), gsw-6b statements at 8f92fe7d53967bc488a4075fb38210e7d40b9031 (same as 2c974b5f except G16's sketch)

Searches (all recorded in `searches.txt`, `../clash/short-external.txt`, `../clash/clash-scan.txt`):
1. **By name**: every new full name against TCSlib/ and audits/ at the base and #355's head (`clash6b.py`, 0 clashes);
   every new short name against TCSlib (3 shared: `Coins`, `select`, `PublicKey`, all in unrelated namespaces) and
   against Mathlib, Batteries and core sources (`short_ext.py`: only `select`, 4 unrelated hits: Witt vectors,
   two private tactic helpers, premise selection).
2. **By shape**: `dup_search.py`, 46 hand-chosen line patterns per declaration family (bodies' key sub-terms,
   conclusions' heads, `def` name stems), in TCSlib at the statement head (new files excluded) and in Mathlib,
   Batteries and core.
3. **By reading** the nearest relatives named in the brief (*Duplication*) and r3 §H2 at the statement head.
`exact?`/`apply?` were not run on the targets: every target's statement mentions a new definition, so no library
lemma can close it without that definition's reader (the shape searches above are the substitute); the one
statement with no new definition in its conclusion's head, G5, is checked by name and shape (no
`secretVector P s ⬝ᵥ` / `dotProduct (secretVector …)` statement outside the private `decrypt_eq_decode_errorSum`).

**Result: no exact restatement** of a public lemma or definition (nothing to report to the lead under G45-01);
the specializations are the two proved citations (G11, L1) and the proved `_length` readers.

## Table (relation: restates / specializes / re-proves / near / none)

| new declaration (file) | nearest relative (`path:line` at 8f92fe7d) | relation | why not reused / note |
|---|---|---|---|
| `select` (Branching) | `GSW.nand` Noise.lean:73 (`G − C₁ ⊡ C₂`); `homGate` Eval.lean:96 | near | different combinator (`(G−C)⊡U + C⊡V`); no selector/cmux in TCSlib, Mathlib or core (`def select` hits are unrelated) |
| `homEvalPBP` (Branching) | `BranchingProgram.evalWith` Complexity/BranchingPrograms/Eval.lean:83 (H18) | specializes (definitionally, by design) | the registered host instantiated with `select P`; `homEvalPBP_eq` is its reader; no second fold |
| `homEvalFormula` (Branching) | `barrington` Barrington.lean:259 | none (composition) | composes `barrington` and `homEvalPBP`; no other consumer of `barrington` reads coordinate `σ 0` |
| `Encrypts.select` G1 (Branching) | `Encrypts.mul`/`add`/`sub`, `encrypts_gadget` Noise.lean:216/149/177/118 | near | new combination; its sketch composes exactly those lemmas; no selector noise lemma exists |
| `encrypts_homEvalPBP` G2 | `evalWith_rel` Eval.lean:143; `evalWith_single` | specializes (uses) | application of the host lemma with G1 as the step; not a restatement (different conclusion) |
| `encrypts_homEvalFormula` G3 | `barrington_yield_zero` Barrington.lean:463, `barrington_length_le` :430 | none | consequence; no GSW formula-evaluation lemma exists |
| `Parameters.neZero_columns` (DecryptFormula) | `instance : NeZero P.modulus` LWE/Basic.lean:54 | none | no `NeZero` for `columns`/`width` in TCSlib (`NeZero .*columns`: 0 hits); inline `omega` on two field reads |
| `keyBits` (DecryptFormula) | `decomposeVec` Gadget.lean:112, `secretVector` Scheme.lean:66 | none (wrapper) | names the bits the evaluation key encrypts (P6-Q8); body is the composition |
| `decConstants` (DecryptFormula) | `decryptColumn` Scheme.lean:129 | none (wrapper) | `Gᵀc`; no `vecMul (decryptColumn …)` anywhere |
| `decryptFormula`, `nandFormula`, `decDepth` (DecryptFormula) | `modSumInterval` ModSum.lean:82, `TreeCircuit.and2`/`neg` Combinators.lean:452/272, `modSumDepth` ModSum.lean:142 | none (instantiations) | the formula layer's combinators instantiated at GSW's constants; 6a provides no decryption formula |
| `vecMul_secretVector_eq_sum` G5 | `gadget_mulVec_decomposeVec` Gadget.lean:164; `vecMul_secretVector_augmented` Scheme.lean:82; Mathlib `Matrix.dotProduct_mulVec` | near | G5 is `⟨t, c⟩ = ∑ xᵢ (Gᵀc)ᵢ`, a two-step consequence (sketch); `vecMul_secretVector_augmented` is `tᵀĀ = e` (another statement) |
| `decryptFormula_eval` G6 | private `decrypt_eq_decode_errorSum` Scheme.lean:213; `modSumInterval_eval` ModSum.lean:131; O2 `decode_iff_mem_Ico` | near | needs the owner-side `decrypt_eq_decode_dotProduct` (MISSING, census); not a restatement |
| `nandFormula_eval` G7 | `TreeCircuit.neg_eval`, `and2_eval`; `Encrypts.nand` Noise.lean:274 | near | `Encrypts.nand` is phase-5 leveled homomorphic NAND (`G − C₁⊡C₂`, noise), not a formula evaluation (r3 §H2) |
| `depth_nandFormula_le`, `maxFanin_nandFormula_le` G8 | `depth_modSumInterval_le` ModSum.lean:165, `maxFanin_modSumInterval_le` :190 | near | add the `and2`/`neg` layer; not restatements |
| `decDepth_le` G8 | `modSumDepth_le` ModSum.lean:179 (F10, admitted) | specializes (weaker) | `modSumDepth_le` at `M = N` with `⌈log₂ q⌉ ≤ ℓ` substituted (weaker in the inner term), behind the wrapper `decDepth`; not the same statement (ℓ in place of `⌈log₂ q⌉`); disclose as a specialization (r3 G8 asks for the ℓ-form) |
| `PublicKey`, `Secret`, `Coins`, `KeySeed` (Bootstrap) | inline types of `Regev.keygen` Regev/Basic.lean:45 and `encrypt` Scheme.lean:102 | none | no abbreviation exists (`abbrev (PublicKey…)` 0 hits outside new files); short-name overlaps only with `RSA.PublicKey`, `NUPPT.Coins`, `LWE.Noise.Coins` etc. in other namespaces |
| `bootNoise` | `eval_encrypts`'s bound `(N+1)^d·β` Eval.lean:250 | none | different (bootstrapped) noise |
| `bootNAND`, `bootGate` | `homGate` Eval.lean:96 (H19 gate function of phase 5) | near | `homGate` evaluates a gate homomorphically (`homAnd`/`homNot`); `bootGate` bootstraps a NAND gate with padding; no reuse possible |
| `fheEval`, `fheEvalCircuit` | `GSW.eval` Eval.lean:122 (runWith with `homGate`) | near | same host `runWith` (H19), different gate function (r3 §H2: different scheme) |
| `evalKey` | `encrypt` Scheme.lean:102 | none (wrapper) | P6-Q8's key; body is `encrypt` |
| `encrypts_bootNAND` G9, `decrypt_fheEval` G10, `decrypt_fheEvalCircuit` G18 | `eval_encrypts` Eval.lean:250, `decrypt_of_encrypts` Scheme.lean:272 | near | phase 5 is leveled multiplicative evaluation (noise grows with depth); G9–G10 are bootstrapping (noise independent of depth) |
| `encrypts_evalKey` G11 | `encrypts_encrypt` Scheme.lean:161 | specializes (proved citation) | proved in one step after `evalKey_eq` (LE-g45 precedent); disclosed |
| `decrypt_keygen_fheEvalCircuit` G12 | `decrypt_keygen_eval` Eval.lean:300 | near | phase-5 statement is for `GSW.eval` with depth-dependent `(N+1)^L`; G12 is for `fheEvalCircuit`, any depth |
| `bootNoise_le` G13 | Mathlib `Nat.pow_pred_clog_lt_self` (cited in sketch) | none | closed form; the Mathlib lemma is used, not re-derived |
| `FheView`, `Seeds`, `fheView` (Circular) | `realView` Security.lean:77, `view` :59 | near | adds the evaluation key and its coins; reuses `Regev.keygen`, `evalKey`, `encrypt` as terms |
| `WeakCircularSecure` (+ `_iff`) | none (`(?i)def .*circular`: 0 hits) | none | new hypothesis (A1); its reader is r3's G14 (Q-6B-1 A, no theorem) |
| `distAdv_fheView_noEvk_le` G15 | `distAdv_encrypt_le` Security.lean:248 | near (transport) | stated over `fheView`'s evk-dropped projection with the extra coins, not `realView` (else a restatement, G45-01); sketch cites `uprob_fst` (Foundations/Probability.lean:175, confirmed present and cited at 8f92fe7d, Circular.lean:134) and `acceptProb_comp_equiv` |
| `LevelCoins`, `levelKey` (Leveled) | `evalKey` (Bootstrap) | none (wrapper) | `levelKey` is `evalKey` at chain indices |
| `literalCts` (+ `_castAdd`, `_natAdd`) | `litInput` NANDLayering.lean:124 (`Fin.append x fun i => !x i`) | near (ciphertext analogue) | reuses `homNot` (Eval.lean:78) for the negations, as the brief requires; readers use Mathlib `Fin.append_left/right` |
| `levelGate`, `leveledEval`, `leveledEvalCircuit` | `fheEval`, `GSW.eval` (runWith) | near | same host H19, level-indexed gate function |
| `encrypts_levelKey` L1 | `encrypts_keygen_encrypt` Scheme.lean:186 | specializes (proved citation) | one step after `levelKey_eq`, `evalKey_eq`; disclosed |
| `encrypts_leveledEval` L2, `decrypt_keygen_leveledEvalCircuit` L3 | `eval_encrypts`, `decrypt_keygen_eval` | near | different scheme (key chain, bootstrapped gates) |
| `LeveledSeeds`, `LeveledView`, `leveledView`, `levelHybrid` (LeveledSecurity) | `realView` Security.lean:77; hybrids `prgHybrid`, `multicopyHybrid`, `columnHybrid` etc. (6 `def …Hybrid`) | near | specific to the key chain; no generic hybrid fits the level structure |
| `levelMsgs`, `levelAssemble`, `levelReduction` | `hybridPlant` EnsembleSecurity.lean:110, phase-5 `reduction` Security.lean:113 | none (composition) | `levelReduction` composes `hybridPlant` and `reduction` as terms (no copy); `hybridPlant` has no reader (census MISSING) |
| `levelTerm`, `challengeDist`, `challengeTerm` | RHS of `distAdv_encrypt_le` Security.lean:248 | none (names for a term shape) | glue |
| `distAdv_levelHybrid_le` L4 | `distAdv_multi_le_sum` EnsembleSecurity.lean:134, `abs_sub_le_sum_hybrids` Foundations/Probability.lean:218 | near | sketch reuses both; no local hybrid lemma |
| `distAdv_leveledView_le` L5 | `distAdv_encrypt_le` | near | chain of L4 plus phase 5's bound |
| `LWE.Family.RatioBounded` (+ `_iff`) (LWE/Ratio) | `LWE.Noise.Bounded` LWE/Noise.lean:57 | none | no ratio predicate exists (`RatioBounded`: 0 hits; `Bounded (B κ)`: 0 hits) |
| `Parameters.ofFamily` (+ simps `_lwe`, `_width`), `pBoot` (PolyRatio) | uses of `F.residueBits.eval κ` (12 TCSlib hits, e.g. `pseudorandom_under_DLWE`) | none | no GSW-family parameter map exists; `def …ofFamily` only in Lake (unrelated) |
| `bootRatio_le_poly` G16, `decrypt_fheEval_of_ratio`/`decrypt_leveledEval_of_ratio` G17 | G13, G12, L3 | near (consequences) | |
| `encodeCiphertext` (+ `_eq`, `_length`) (Asymptotic) | `Encoding.Modular.encodeMatrix` Encoding/Modular.lean:65, `encodeMatrix_length` :89 | specializes (wrapper; `_length` proved from `encodeMatrix_length`) | wrapper with a GSW-typed length; proved, not admitted |
| `encodeView`, `encodeFheView`, `encodeLeveledView` (+ readers) | `LWE.encodeChallenge` LWE/Encoding.lean:42 | none (compositions) | `_length` readers proved from the public `_length` lemmas |
| `WeakCircularSecureFamily`, `ReductionEfficient`, `LeveledReductionEfficient` (+ `_iff`) | `LWE.DLWEAssumption` LWE/Assumption.lean:136; `∃ D' : NUPPT` once in ZeroKnowledge/NPLemmas.lean:389 (unrelated) | none | new hypotheses |
| `indCPA_of_dlweAssumption` A1, `leveledINDCPA_of_dlweAssumption` A3 | `pseudorandom_under_DLWE` Pseudorandom/Generators/LWE/Basic.lean:85 (model); no asymptotic Regev/GSW IND-CPA in TCSlib (`Negligible` in Regev/GSW Security: 0 hits) | none | sketches cite `negligible_polyExpr_mul` of `Asymptotic/EnsemblesLemmas.lean:377` (one of the three copies; no fourth added: no new name contains `polyExpr_mul`) |
| `decodeLo`, `decodeHi`, `decode_iff_mem_Ico` (O2, LWE/BitEncoding) | `decode_codepoint_add` BitEncoding.lean:181; Mathlib `ZMod.valMinAbs_natAbs_eq_min` Mathlib/Data/ZMod/ValMinAbs.lean:160 | none / uses | see *O2* below |

## O2 (`decode_iff_mem_Ico`) at 8f92fe7d: Mathlib use and the remaining inline step

* The maintainer's fix is confirmed: the proof now rewrites with Mathlib's
  `ZMod.valMinAbs_natAbs_eq_min : a.valMinAbs.natAbs = min a.val (n - a.val)` (Mathlib/Data/ZMod/ValMinAbs.lean:160;
  `git diff a855e111 2c974b5f`: the local `habs` re-derivation via `ZMod.valMinAbs_def_pos` is gone). It does not
  re-prove `decode_codepoint_add` (different statement: interval characterization vs bounded-error decoding).
* The remaining inline step is `hsub : (v − ⌊q/2⌋).val = if ⌊q/2⌋ ≤ v.val then v.val − ⌊q/2⌋ else v.val + q − ⌊q/2⌋`.
  Own search (Mathlib `Mathlib/Data/ZMod/`, `Mathlib/Data/Fin/`, core `Init/Data/Fin/`, Batteries): for `ZMod n`
  the only subtraction-value lemma is `ZMod.val_sub (h : b.val ≤ a.val) : (a − b).val = a.val − b.val`
  (Mathlib/Data/ZMod/Basic.lean:1024), used for the first case. There is **no two-case lemma for `ZMod n`**. The
  two-case and second-case facts exist **only for `Fin n`**: core `Fin.coe_sub_iff_lt : ↑(a − b) = n + a − b ↔ a < b`
  (Init/Data/Fin/Lemmas.lean:1089), `Fin.coe_sub_iff_le` (:1076), `Fin.coe_sub` (:1050), and Mathlib
  `Fin.intCast_val_sub_eq_sub_add_ite` (Mathlib/Data/Fin/Basic.lean:305); they apply to `ZMod q` only after
  `cases` on `q = k + 1` (where `ZMod (k+1)` is `Fin (k+1)` by definition), i.e. by unfolding `ZMod`, which the
  file's style avoids. A two-lemma ZMod route also exists (`sub_eq_add_neg`, `ZMod.val_add_of_lt` Basic.lean:635,
  `ZMod.val_neg_of_ne_zero` :1021). The delivered second case (`Nat.cast_sub`, `ZMod.natCast_self`,
  `ZMod.natCast_zmod_val`, `ZMod.val_natCast_of_lt`) is a 3-line case of a fact Mathlib does not state for
  `ZMod`: **not a re-derivation** (GF-F01 concerns re-proving an existing lemma). Optional tightening for the
  lead: none needed.

## Inline general facts in the proofs the statement job wrote (GF-F01 check)

Scanned every proof body of the 9 new files and O2 at 8f92fe7d (`have`, `obtain`, arithmetic tactics):
* `decode_iff_mem_Ico` (O2): `hq`, `hv` (reads of `modulus_ge_two`, `ZMod.val_lt`), `hh : q/2 < q` (`omega`),
  `hsub` (above), `hcast` (inside `hsub`). No other general fact.
* `Parameters.neZero_columns` (DecryptFormula.lean:64–70): `hle`, `hq` (field reads) and `omega` for
  `ℓ ≠ 0`; no Mathlib lemma states "`2 ≤ q ≤ 2^ℓ → ℓ ≠ 0`" (it is linear arithmetic after `pow_zero`).
* Readers: `rfl`/`Iff.rfl`; the case readers of `bootGate`/`levelGate` (`unfold`, `rw [h]`, `dif_pos`/`dif_neg`
  with `Nat.not_lt.mpr`); `literalCts_castAdd`/`_natAdd` (Mathlib `Fin.append_left`/`Fin.append_right`).
* `encodeCiphertext_length`, `encodeView_length`, `encodeFheView_length`, `encodeLeveledView_length`: rewrites
  with the public `encodeMatrix_length`, `encodeChallenge_length`, `List.length_append`, `List.length_flatten`,
  `List.ofFn_comp'`, `List.ofFn_const`, `List.sum_replicate_nat`; no `have`.
* G11 (`encrypts_evalKey`), L1 (`encrypts_levelKey`): `rw [..._eq]` and `exact` of the public phase-5 lemma.
* `levelMsgs`/`levelAssemble`/`levelReduction` use Mathlib's `Nat.sub_one_add_one` with `NeZero.ne` for the
  index cast (no local copy).
No inline re-derivation of a Mathlib/TCSlib fact was found.
