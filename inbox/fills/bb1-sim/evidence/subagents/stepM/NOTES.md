# Sub-agent A (stepM): notes

File owned: `TCSlib/Cryptography/AdvancedEncryption/IdentityBased/BonehBoyenSecurity/Coupling.lean`
(worktree `/home/user/fill/wt-subA`, olean tree `/home/user/fill/treeA`). No commits, no ref
changes, no other tracked file edited. Scratch files: `SubAScratch/` (the original file
`Coupling.orig.lean.txt`, draft fragments `rows.lean.txt` and `call.lean.txt`, diagnostic module
`T1.lean`); `Bb1sSeal/` is the devseal output directory.

## Status: DONE

- Final SHA-256 of Coupling.lean:
  `0707678461f3c2a0170c21e25d298e0e5329c8ab793af057c0ccdb29c16c7ae7`
- 552 lines, longest line 100 characters. No `sorry`, `admit`, `native_decide`, `axiom`,
  `@[simp]`, or micro sign. No new imports, `open`s or attributes.
- Original SHA-256 (as seeded): `046b46d41d7a288c06ba83360dd1fe1dcfe050bec7b793d8a77361ed4bce22ef`.
- Existing declaration headers unchanged. The only removed lines are the 7 `sorry`s, plus
  `natCast_bitsToNat_injective`'s last header line, where only the trailing `:= by` became
  `:= fun u v huv =>`.

## Log (UTC, 2026-11-17)

- 04:40 Read Coupling.lean, Lazy.lean, Real.lean, Relational.lean (`expect_simulate_rel`,
  `expect_sample_rel`), Defs.lean readers, BonehBoyen.lean simulator readers, Pairing/Group.lean,
  the probe `BB1SimStepM.lean.txt` and devseal.py. Backed up the original file.
- Filled the Algebra section (5 lemmas). Native check: rc=0, 0 errors, only the `sorry` warning
  from `stepM_call`.
- Added the 9 step-M rows (ported from the probe's P-2, with `bb1RealLazy`/`bb1SimLazy` readers
  in place of `realAt`/`bb1SimImpl`) and the proof of `stepM_call`. Native check: rc=0, 0 errors,
  no warnings.
- devseal A: rc=1, 1 error; devseal B: rc=1, 1 error. Both at `stepM_init_none`: the term
  `.some ⟨rfl, he _ h⟩` (RelM of the new states) did not elaborate under the seal. The expected
  type holds a beta-redex, and its cast proof is the reader's `show … from rfl`.
- Gave the bijection argument explicitly (`hz := he (idToZ (cast x)) h`). devseal A: still rc=1,
  1 error (same spot).
- Diagnostic: scratch module `SubAScratch/T1` (that row alone, with `trace_state`) under devseal
  A: rc=0. Fix confirmed: `refine ⟨…, .some ⟨rfl, ?_⟩⟩` then `dsimp only; exact hz`.
- Applied the fix. devseal A: rc=0, errors=0 (sealed 873); devseal B: rc=0, errors=0
  (sealed 874).
- Added `**Proof sketch.**` paragraphs to `stepM_init_none` (19-line proof) and
  `stepM_challenge_invalid` (16-line proof).
- 04:49 Final checks on the final file (SHA above):
  - native: rc=0, 0 errors, 0 warnings (`native.log`);
  - devseal A: rc=0, errors=0, DEVSEAL A sealed 873, 0 warnings (`devseal-A.log`);
  - devseal B: rc=0, errors=0, DEVSEAL B sealed 874, 0 warnings (`devseal-B.log`).
- Lead note received (`bb1SimImpl_two_of_not` statement changed): Coupling.lean does not use
  `bb1SimImpl_two_of_not` (grep: no match). The non-fresh Challenge rows use
  `bb1SimLazy_two_of_not`, then `bb1SimImpl_eq`, `IBEScheme.oracleImpl_two_onSpec` and
  `bb1SimChal_none` / `_repeat` / `_invalid`, as the probe does.

## Proofs of the existing declarations

- `exists_equiv_mul_pow`: `e z := (Equiv.mulLeft (X^{(−z).val})⁻¹).trans E.symm`, where
  `E := Equiv.ofBijective _ (pow_val_bijective_of_ne_one hg)`. Then `apply_symm_apply` and
  `mul_inv_cancel_left`.
- `natCast_bitsToNat_injective`: `bitsToNat_injective` ∘ `CharP.natCast_injOn_Iio (ZMod p) p`
  (instance `ZMod.charP`), with `bitsToNat_lt` and `hp` (ruling BS-F01).
- `key_eq`: local `hpow` (from `pow_val_mul`, `pow_mul`) and `hmul` (`pow_val_add`), then
  `simp only [hpow, hmul]`, `congr 2`, `field_simp`, `ring` (uses `z − z' ≠ 0`).
- `F_target_eq`: `pow_val_neg`, `mul_inv_cancel_left`.
- `pair_pow_val_eq`: `pow_val_mul_GT`, `pow_mul`, `pow_val_mul_GT`, `bilinear_pow`.
- `stepM_call`: generalize the coin map `zt`, take `e` from `exists_equiv_mul_pow`, split the
  states and `RelM`, then `match i, x, g₀, g₁, hg₀₁` with cases `0`, `1`, `2`, and dispatch to
  the rows. Deterministic rows close with `expect_pure` and `hg₀₁ … huv`. Sampling rows close
  with `ProbComp.expect_sample_rel` along `e ID` (Init), `Equiv.addRight (b'/(ID − ID*))`
  (KeyGen) and `Equiv.refl` (first valid Challenge, after `subst` of the coin map).
- `expect_simulate_bb1RealLazy`: unchanged (already proved from `stepM_call`).

## Declarations added (all public, in `section StepM`, with docstrings)

The section-level variable `{U} [Fintype U] [Nonempty U] (zt : U → G × G_T)` was added for the
rows that do not read the challenge coins.

| Name | Kind | One line |
|---|---|---|
| `stepM_init_none` | sampling | Init before a commitment: `sample G` vs `sample Z_p`, along `e ID`; [*Setup*]; has a sketch |
| `stepM_init_some` | deterministic | Init after a commitment: same parameters, states kept; [*Setup*] |
| `stepM_keyGen_none` | deterministic | KeyGen before Init: both `⊥`; Glue |
| `stepM_keyGen_target` | deterministic | KeyGen for `ID*`: both `⊥`; Glue |
| `stepM_keyGen_ne` | sampling | KeyGen for `ID ≠ ID*` along `r ↦ r + b'/(ID − ID*)`; [*Phase 1*, quote]; has a sketch |
| `stepM_challenge_none` | deterministic | Challenge before Init: both `⊥`; Glue |
| `stepM_challenge_repeat` | deterministic | Challenge after a recorded one: both repeat it; Glue |
| `stepM_challenge_invalid` | deterministic | First invalid Challenge: both `⊥`; Glue; has a sketch |
| `stepM_challenge_fresh` | sampling | First valid Challenge, `s = c` along `Equiv.refl`; [*Challenge*, quote]; has a sketch |

Row form, as in the probe: a deterministic row gives `∃ a, real = pure (a, u) ∧ sim = pure (a, v)`;
a sampling row gives `∃ f₀ f₁, real = sample.bind (pure ∘ f₀) ∧ sim = sample.bind (pure ∘ f₁) ∧
∀ u, (f₀ u).1 = (f₁ (e u)).1 ∧ RelM (f₀ u).2 (f₁ (e u)).2` (the premise of `expect_sample_rel`).

## Duplication searches and reuse

- Searched TCSlib (`grep`) for `bitsToNat_lt`, `bitsToNat_injective` (Asymptotic/Sampling.lean:412,
  :417), the BilinearGroup pow lemmas (Pairing/Group.lean), `expect_pure`, `expect_sample_equiv`,
  `expect_sample_rel`, `expect_simulate_rel`, and `match i, x` patterns on `Fin 3`
  (BonehBoyenMachine/Oracles.lean, Draws.lean). Searched Mathlib for `natCast_injOn_Iio`
  (Algebra/CharP/Basic.lean:55).
- Reused from Mathlib: `CharP.natCast_injOn_Iio`, `Equiv.ofBijective`, `Equiv.apply_symm_apply`,
  `Equiv.mulLeft`, `Equiv.coe_mulLeft`, `Equiv.addRight`, `Equiv.coe_addRight`, `Equiv.refl`,
  `Equiv.refl_apply`, `mul_inv_cancel_left`, `pow_mul`, `pow_right_comm`, `mul_comm`,
  `sub_ne_zero`, `List.ofFn_injective`, `Option.map_some`, `Option.some_ne_none`,
  `Bool.false_ne_true`, `field_simp`, `ring`.
- Reused from TCSlib: `bitsToNat_lt`, `bitsToNat_injective`,
  `BilinearGroup.pow_val_bijective_of_ne_one`, `pow_val_add`, `pow_val_neg`, `pow_val_mul`,
  `pow_val_mul_GT`, `bilinear_pow`, `ProbComp.expect_pure`, `ProbComp.expect_sample_rel`.
- Reused readers (Rule 10):
  - Real.lean: `bb1RealLazy_zero_none`, `bb1RealLazy_none_of_ne`, `bb1RealLazy_some`, and the
    `RealReads` fields `.encPP`, `.msgSpace`, `.keyGen`, `.enc`.
  - Lazy.lean: `bb1SimLazy_zero`, `_one`, `_two_fresh`, `_two_of_not`; `sidSpec_dom_zero`,
    `_one`, `_two`; `sidSpec_rng_one`, `_two`; `zeroBits_eq_cast`.
  - Defs.lean: `IBEScheme.sidImpl_zero_onSpec`, `sidImpl_two_onSpec`, `sidImpl_one_onQuery`,
    `sidImpl_two_onQuery`, `sidImpl_init_none` / `_some`, `sidImpl_keyGen_none` / `_target`,
    `sidImpl_keyGen_ne_onSpec`, `sidImpl_challenge_none` / `_repeat` / `_invalid`,
    `sidImpl_challenge_fresh_onSpec`, `oracleImpl_zero` / `_one` / `_two_onSpec`, `outLens_one`,
    `outLens_two`.
  - BonehBoyen.lean: `bb1SimImpl_eq`, `bb1SimInit_none` / `_some`, `bb1SimKeyQ_none` /
    `_target` / `_ne`, `bb1SimChal_none` / `_repeat` / `_fresh` / `_invalid`, `bb1SimParams_eq`,
    `bb1SimKey_eq`, `ofFn_bb1SimCt`, `ofFn_bb1Scheme_encPP`, `ofFn_bb1Scheme_encSK`,
    `bb1Scheme_msgSpace_iff`, `BB1.F_eq`, `BB1.idToZ_eq`.
- No foreign definition is unfolded. There is no anonymous constructor of `PP κ`.
  `bb1SimImpl_two_of_not` is not used.

## For the lead

- No statement looked false. Every existing header is kept.
- Seal gotcha (dev seals A and B): an anonymous-constructor proof of `RelM` whose expected type
  holds a beta-redex over a reader's `cast (show … from rfl) x` failed to elaborate under the
  seal, though it was fine natively. Using `?_` with `dsimp only; exact …` fixes it
  (`stepM_init_none`).
- The checks ran against tree A, which still has the old Lazy.lean. Coupling does not depend on
  the changed `bb1SimImpl_two_of_not`, so it should be unaffected, but it has not been checked
  against the lead's tree.
