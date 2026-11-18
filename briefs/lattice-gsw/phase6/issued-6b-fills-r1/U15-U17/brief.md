# Claude fill · `gsw-6b-u15-u17`: GSW 6b units U15 and U17, the evk-free view and the leveled key hybrid (G15, L4, L5)

**Unit** `gsw-6b-u15-u17` · **Route** Claude fill, a lead with up to 1 sub-agent · **Base** B6
`bff0567b6c4b6b724c8fd20ff3ef92258eb3fc9d` (tree `845bdc982fd8f79aba755796bb13188922c4655d`) · **Size** 290–490 fill
lines (r3 §H7: U15 60–120, U17 230–370) · **Delivery** `inbox/fills/gsw-6b-u15-u17/` on `exchange/pass-shelat-ch5-8` ·
**Local inputs (rule 16)** none.

Read `../COMMON.md` first; it is part of this brief. Then `../dup-sweep.md` §0 and §U15-U17 (binding must-reuse list).

**Why one unit** (README Q-6BF-2 A). Both files transport phase 5's `distAdv_encrypt_le` along seed regroupings of
views built from `Regev.keygen` seeds (G15 drops the evaluation-key coins; L5's middle step identifies `H_0(μ)` with
`challengeDist` run on `realView`). One owner keeps the regrouping technique consistent and reuses the same public
marginalization lemmas; U15 alone is too small (60–120 lines) to justify its own bootstrap. No public helper is needed:
the seed types differ, so the private glue of the two files is not a copy.

## Targets (frozen statements; prove all three)

| Row | Declaration (`TCSlib.Cryptography.AdvancedEncryption.Homomorphic.GSW.`) | Line at B6 |
|---|---|---|
| G15 | `distAdv_fheView_noEvk_le`: the projection `(pk, ct)` of `fheView` (evk dropped) obeys phase 5's bound | `GSW/Circular.lean:140` |
| L4 | `distAdv_levelHybrid_le`: `distAdv (H_{e+1}) (H_e) D ≤ ∑ j, levelTerm P χ L μ e j D` | `GSW/LeveledSecurity.lean:329` |
| L5 | `distAdv_leveledView_le`: IND-CPA of leveled GSW-FHE, the two chains plus `challengeTerm` | `:354` |

G14 and A2 are reader-only (ruling Q-6B-1 A): `weakCircularSecure_iff` is G14; nothing to prove.

## Owned files and scope

| File | Lines at B6 |
|---|---|
| `TCSlib/Cryptography/AdvancedEncryption/Homomorphic/GSW/Circular.lean` | 149 |
| `TCSlib/Cryptography/AdvancedEncryption/Homomorphic/GSW/LeveledSecurity.lean` | 362 |

Under COMMON §4, **no public helper**. Frozen: everything else, including phase 5's `Security.lean`, the hybrid layer
(`Encryption/PublicKey/{EnsembleSecurity,Hybrid}.lean`), every definition and reader in the two files (`fheView`,
`WeakCircularSecure`, `leveledView`, `levelHybrid`, `levelMsgs`, `levelAssemble`, `levelReduction`, `levelTerm`,
`challengeDist`, `challengeTerm`).

## Known context

- **G15.** Through `fheView_fst`/`fheView_snd` (or `fheView_eq`), `Regev.keygen_fst`, `realView_eq`, `view_eq`, the
  projected view at `(rg, R, R₀)` is `realView P χ μ (rg, R₀)`: it never reads `R`. Regroup the seed-and-coin space
  so that `R` is a separate factor (`acceptProb_comp_equiv` with `Equiv.prodComm`/`prodAssoc`) and drop it with
  **`acceptProb_fst`/`acceptProb_snd`** (`Pseudorandom/Indistinguishability.lean:73`, `:83`), which are exactly the
  marginalization the frozen sketch derives from `uprob_fst`; then `distAdv_def` and `distAdv_encrypt_le`. The target
  is deliberately over the projection of `fheView`, not `realView` (G45-01): do not add a restatement over `realView`.
- **L4.** Position hybrids `G_i` (`i ≤ N`) between `H_{e+1}` and `H_e`; `abs_sub_le_sum_hybrids` reduces to the gaps,
  as in `distAdv_multi_le_sum` (whose `hybridPlant` the reduction uses). The messages (the bits of `s_e`) are drawn
  inside the reduction's coins (r3 §H8 item 12), so either apply `distAdv_multi_le_sum` per value of the other seeds
  (fixing a seed factor: `exists_fixSeed`, `ColZKLemmas.lean:157`, or an averaging over the seed with
  `acceptProb_bind`), or follow its proof with those seeds in the coins. The gap at `i = j` is `levelReduction`'s
  real-vs-uniform gap plus the uniform-key gap: `levelReduction_eq`, `reduction_eq`, `hybridPlant_eq`,
  `levelAssemble_eq`, `levelHybrid_eq`, `Regev.keygen_fst` (the planted key is distributed as `pk_{e+1}`, whose secret
  is unused in `H_{e+1}`: top-down order), `real_uniformKey_advantage`, `LWE.decisionAdvantage_eq`, and
  `uniformKey_uniform_advantage_le` twice for `2·(N·ε_LHL)`; sum over `j` with `levelTerm_eq`.
- **L5.** `leveledView = levelHybrid … L` (`leveledView_eq`, `levelHybrid_eq`: no `e : Fin L` has `L ≤ e`); the chain
  `H_L(μ₀) … H_0(μ₀), H_0(μ₁) … H_L(μ₁)` with L4 for `e = L − 1, …, 0` (`Fin.sum_univ_eq_sum_range`,
  `abs_sub_le_sum_hybrids` or `abs_sub_le`); the middle step: `H_0(μ)` is `challengeDist P χ L D` run on
  `realView P χ μ` after the seed regrouping (`challengeDist_eq`, `realView_eq`, `view_eq`, `Regev.keygen_fst`,
  `acceptProb_comp_equiv`, the unused coordinates dropped by `acceptProb_fst`/`_snd`), bounded by
  `distAdv_encrypt_le` as `challengeTerm` (`challengeTerm_eq`); `linarith`.
- **Rulings in force.** Q-6B-W3 A: the μ-dependent `levelTerm` and the two-chain L5 bound are accepted as stated.
  P6-Q19 B: the reconstruction disclosure of the module docstring stays. Sizes (G6B-F07): `LeveledSecurity.lean` was
  projected at ≤ 721 lines filled.

## Axioms (C5)

All three targets and every helper: standard axioms only. **No `sorryAx`**: U15-U17 depends on no other 6b target
(phase 5 and the hybrid layer are proved). The trace must be empty.

## Unit checks (in addition to COMMON C1–C13)

- **C2 count.** `base-sorries.txt` minus the 3 targets: **39 declarations in 14 modules**.
- **C3.** decls2 on the two files: 0 ADDED, 0 CHANGED, 0 REMOVED.
- **C12 probe U17-P1** (optional): an `#eval` comparing `levelHybrid P χ L μ L r` with `leveledView P χ L μ r` on a
  few seeds of a toy instance (`n = 1`, `q = 4`, `ℓ = 2`, `L = 1`), evidence only.
- **Split.** Lead: `LeveledSecurity.lean`, the integration, the final checks and delivery. Sub-agent `circ`:
  `Circular.lean` (G15), then the seals and controls of both owners.

## Size

290–490 fill lines. Checkpoint 1: G15 and L4 proved and checked; L5 outlined.

**Ready to dispatch once the records pin is filled and Q-6BF-2 is ruled** (README).
