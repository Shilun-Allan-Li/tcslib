# Claude fill · `gsw-6b-u18-u19`: GSW 6b units U18 and U19, the polynomial ratio and the asymptotic forms (G16, G17, A1, A3)

**Unit** `gsw-6b-u18-u19` · **Route** Claude fill, a lead with up to 1 sub-agent · **Base** B6
`bff0567b6c4b6b724c8fd20ff3ef92258eb3fc9d` (tree `845bdc982fd8f79aba755796bb13188922c4655d`) · **Size** 290–500 fill
lines (r3 §H7: U18 140–220, U19 150–280) plus the public helper · **Delivery** `inbox/fills/gsw-6b-u18-u19/` on
`exchange/pass-shelat-ch5-8` · **Local inputs (rule 16)** none.

Read `../COMMON.md` first; it is part of this brief. Then `../dup-sweep.md` §0 and §U18-U19 (binding must-reuse list).

**Why one unit** (README Q-6BF-2 A). G16 and both A1 and A3 need the same family-level fact,
`N = (n + 1)·ℓ ≤ (d(κ) + 1)·ℓ(κ)` at `P = ofFamily F κ`, read through `ofFamily`'s two readers only (type-level Rule
10). One owner states it once, public, in `PolyRatio.lean` (upstream of `Asymptotic.lean`), and EF-R1 reuses it.

**EF-R1 is not in this unit** (README Q-6BF-1 A): A1 and A3 are proved here **from the frozen `heff` hypotheses**
(ruling Q2 A keeps their statements); EF-R1, a separate unit, proves `ReductionEfficient`/`LeveledReductionEfficient`
and adds the unconditional wrappers in a new file.

## Targets (frozen statements; prove all five)

| Row | Declaration (`TCSlib.Cryptography.AdvancedEncryption.Homomorphic.GSW.`) | Line at B6 |
|---|---|---|
| G16 | `bootRatio_le_poly`: `8·(ℓ·bootNoise P (m·B κ)) ≤ pBoot(κ)·B(κ)` at `P = ofFamily F κ` | `GSW/PolyRatio.lean:113` |
| G17 | `decrypt_fheEval_of_ratio`: pure scheme correct when `χ` is `B κ`-bounded and `pBoot(κ)·B(κ) < q(κ)` | `:133` |
| G17 | `decrypt_leveledEval_of_ratio`: leveled scheme, same regime | `:161` |
| A1 | `indCPA_of_dlweAssumption`: from `DLWEAssumption F`, `heff : ReductionEfficient F` and the width condition | `GSW/Asymptotic.lean:297` |
| A3 | `leveledINDCPA_of_dlweAssumption`: from `DLWEAssumption F`, `heff : LeveledReductionEfficient F L`, width | `:328` |

## Owned files and scope

| File | Lines at B6 | Permitted (COMMON §4) |
|---|---|---|
| `TCSlib/Cryptography/AdvancedEncryption/Homomorphic/GSW/PolyRatio.lean` | 179 | the three proofs, private helpers, sketches, the admitted-sentence, **and the one public helper `Parameters.ofFamily_columns_le`**, inserted after `pBoot_eq` and before G16, with a `## Main results` (or definitions) entry |
| `TCSlib/Cryptography/AdvancedEncryption/Homomorphic/GSW/Asymptotic.lean` | 340 | the two proofs, private helpers, sketches, the admitted-sentence |

**The public helper** (README Q-6BF-3 A; the only new public declaration):

```lean
theorem Parameters.ofFamily_columns_le (F : LWE.Family) (κ : ℕ) :
    (Parameters.ofFamily F κ).columns ≤ (F.dimensionBound.eval κ + 1) * F.residueBits.eval κ
```

Docstring: words and formula, "Glue.", proof through `Parameters.columns_eq`, `Parameters.ofFamily_lwe`,
`Parameters.ofFamily_width`, `F.dimension_le`, `Nat.mul_le_mul_right`. If a `PolyExpr` form serves A1/A3 better
(e.g. `≤ ((F.dimensionBound.add (.const 1)).mul F.residueBits).eval κ`), state that one instead, disclosed; one helper
only. Seal it with its own liveness pair (COMMON C6).

Frozen: every definition and reader in the two files (`Parameters.ofFamily` and its `simps` readers, `pBoot`,
the encodings, `WeakCircularSecureFamily`, **`ReductionEfficient`, `LeveledReductionEfficient`** and their `_iff`
readers), `LWE/Ratio.lean` and `LWE/Assumption.lean`, phase 5, and every other unit's file.

## Known context

- **Type-level Rule 10** (Gate 46): `ofFamily`'s body is never read; only `Parameters.ofFamily_lwe`
  (`(ofFamily F κ).lwe = F.parameters κ`) and `Parameters.ofFamily_width`. `q` is `(ofFamily F κ).lwe.modulus`
  rewritten by `ofFamily_lwe` where a hypothesis states it on `F.parameters κ`.
- **G16.** G13 (`bootNoise_le`, U14-U16) at `β = m·B`; `pBoot_eq` and the `PolyExpr.eval_*` equations; `n ≤ d(κ)`,
  `m ≤ s(κ)` (`dimension_le`, `samples_le`), so `N ≤ N̂` (the helper); `⌈log₂ N⌉ ≤ N` (`Nat.clog_le_iff_le_pow`,
  `Nat.lt_two_pow_self`); monotonicity; `8·4^33·2 = 2^70` (`norm_num`). Ruling Q-6B-W1 A: the factor is `8`, the
  constant exactly `2^70` (LE-6b2).
- **G17.** G12 (`decrypt_keygen_fheEvalCircuit`) and L3 (`decrypt_keygen_leveledEvalCircuit`), both U14-U16, at `P`;
  their conditions from G16 and `hq`: `8y ≤ pBoot·B < q` gives `2y < ⌊q/2⌋` (`omega`; `y = 0` trivially as `q ≥ 2`);
  the leveled input condition from `m·B ≤ bootNoise P (m·B)` (`bootNoise_eq`, `N ≥ 1`).
- **A1.** At each `κ`, `distAdv_encrypt_le_of_width` with `w = ℓ` (`q ≤ 2^ℓ` from `modulus_le_pow`; `hm` read through
  the two readers) bounds the advantage by the two DLWE advantages of `reduction` plus `N·2^{−κ}`;
  `reductionEfficient_iff` on `heff` gives `D'₀`, `D'₁` dominating them by `F.advantageAt D'ᵢ κ`, negligible by
  `dlweAssumption_iff`; `N ≤ (d(κ)+1)·ℓ(κ)` (the helper) and `negligible_polyExpr_mul` (`EnsemblesLemmas.lean:377`)
  with `negligible_two_pow_neg`; `Negligible.add`, `Negligible.mono` (`distAdv` is nonnegative by `distAdv_def` and
  `abs_nonneg`).
- **A3.** L5 (`distAdv_leveledView_le`, U15-U17) bounds the advantage by `∑_e ∑_j (levelTerm₀ + levelTerm₁) +
  challengeTerm`; `leveledReductionEfficient_iff` on `heff` for `μ = false`, `true` gives `D'₀`, `D'₁` dominating every
  DLWE term of `levelTerm_eq` and `challengeTerm_eq`; `Regev.two_extractionError_le` with `hm` bounds `2·ε_LHL ≤
  2^{−κ}`; the total is at most `(2·L(κ)·N + 1)·(2·(adv D'₀ + adv D'₁) + N·2^{−κ})`, a polynomial times negligible
  functions (`negligible_polyExpr_mul` with an explicit `PolyExpr` built from `L`, `F.dimensionBound`,
  `F.residueBits`; `Finset.sum_le_sum`, `Finset.sum_const`).
- **Sizes** (G6B-F07): `Asymptotic.lean` was projected at ≤ 604 lines filled.

## Axioms (C5)

Allowed `sorryAx` traces, through these frozen targets of other units only:
- U14-U16: `bootNoise_le` (G16), `decrypt_keygen_fheEvalCircuit` (G17 pure), `decrypt_keygen_leveledEvalCircuit`
  (G17 leveled), and through them the U14-U16, U13 and U12 targets their own briefs allow;
- U15-U17: `distAdv_leveledView_le` (A3), and through it `distAdv_levelHybrid_le`.

**A1 and `Parameters.ofFamily_columns_le` must be standard only** (A1 uses phase 5's proved bound). No trace may name
a declaration of `PolyRatio.lean` or `Asymptotic.lean`.

## Unit checks (in addition to COMMON C1–C13)

- **C2 count.** `base-sorries.txt` minus the 5 targets: **37 declarations in 14 modules**.
- **C3.** decls2: `PolyRatio.lean` ADDED exactly `Parameters.ofFamily_columns_le`, 0 CHANGED, 0 REMOVED;
  `Asymptotic.lean` 0/0/0.
- **C12 probe U18-P1** (optional): `norm_num`/`decide` check of `8 * 4 ^ 33 * 2 = 2 ^ 70` and of G16 at three small
  families' parameter values by `#eval`, evidence only.
- **Split.** Lead: `Asymptotic.lean` (A1 first: it is sorry-free), the integration, final checks, delivery.
  Sub-agent `ratio`: `PolyRatio.lean` (the helper first, so A1/A3 can use it at once).

## Size

290–500 fill lines plus the helper (about 10–20). Checkpoint 1: the helper, G16 and A1 proved and checked.

**Ready to dispatch once the records pin is filled and Q-6BF-2/Q-6BF-3 are ruled** (README).
