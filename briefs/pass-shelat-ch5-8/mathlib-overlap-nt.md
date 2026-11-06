# Mathlib overlap audit: TCSlib elementary number theory (Pass–Shelat ch. 2 base, ch. 5–8 fills)

**Scope.** All declarations of `TCSlib/Cryptography/NumberTheory/*.lean`, the number-theoretic
declarations (sorried targets included) of `TCSlib/Cryptography/Candidates/{Arithmetic, Concrete,
Factoring, RSA, Rabin, DiscreteLog, DiscreteLogHardcore, ElGamal}.lean`, and the number-theory
ingredients named in `fills/{dl-candidates, factoring-candidates, 3col}/brief.md`. Tree: branch
`cryptography/pass-shelat-ch2-4` at `e0f4d19e`. The `TCSlib/` sources are identical to the probe
worktree `wt-fillfac` at `5f277163` (`git diff --stat` is empty). Mathlib is the pinned copy
`.lake/packages/mathlib` at `029db123` (2025-11-14), Lean 4.25.0. The audit read the sources and
wrote only this report and its probe logs.

**Excluded, as briefed:** machines, coin-string samplers, polynomial time, `uprob`/`StatClose` and
encodings. That covers `Primality.lean` from `samplePrime` on, the `uprob_*` and
`pushesUniform_*` lemmas, `rabin_symmetry`, `statClose_sq_generator`, the encoders and decoders
and every `polyTimeComputable_*`. Where one of them has a separate number-theoretic core, the
core gets its own row. `Concrete.one_sub_one_div_pow_le_exp_neg` and `exp_neg_le_half_pow` are
real analysis, not number theory. They are already thin wrappers of `Real.one_sub_div_pow_le_exp_neg`
and `Real.add_one_le_exp`.

**Method.** I grepped the pinned Mathlib by name and by docstring for each concept. Wherever a
candidate existed, I restated the TCSlib statement as an `example` and closed it from Mathlib.
Then I ran an `exact?` sample (maxHeartbeats 400000) **in a file that imports Mathlib only**. A
first run with the TCSlib files imported found only TCSlib's own lemmas, so it was discarded.
There are five probe files, each logged with its source and the Lean output, in
`mathlib-overlap-nt-probes/`:

| Log | Content | Result |
|---|---|---|
| `NTOverlap1.log` | P1.1–P1.23: NumberTheory statements closed from Mathlib, plus `#check`s | EXIT=0 (all close) |
| `NTOverlap3.log` | E1–E23: `exact?`, Mathlib-only imports | 1 hit (E13, an ingredient). Every other `exact?` reports "could not close". E12′ (a 3-line derivation) closes |
| `NTOverlap4.log` | C1–C12: candidate-level and fill-route cores closed from Mathlib | EXIT=0 |
| `NTOverlap5.log` | Which recommended names the candidate files already reach without a new import | all reachable except the 7 listed under "Import caveat" |
| `NTOverlap6.log` | `#check` of every further Mathlib name cited here | EXIT=0 (all resolve; three names in modules with no cached olean were checked by grep: `Nat.roughNumbersUpTo_card_le'`, `not_summable_one_div_on_primes`, `lucas_primality`) |

`exact?` searches only the imported modules, so the greps (quoted below) are the evidence for
modules that were not imported.

*Probe environment:* I ran `scripts/lean_check_tree.sh` with `TCSLIB_OLEANS=fillfac-oleans`, plus
one addition. Four Mathlib modules have no olean in the local cache: `NumberTheory/PowModTotient`,
`NumberTheory/FermatPsp`, `RingTheory/ZMod/UnitsCyclic` and `Algebra/Group/Subgroup/Even`. I
compiled them from the pinned sources with a direct `lean -o` into a scratch overlay
(`scratchpad/ntoverlap-mlib-oleans`, wrapper `scratchpad/ntoverlap-tools/run.sh`). There was no
`lake build` and no `cache get`, and I ran one Lean process at a time.

## Summary

All 90 table rows below are classified. Each row is one declaration or a tight group (for
example a definition with its unfolding lemmas).

| Class | Rows | Meaning here |
|---|---|---|
| **DUP** | 6 | Mathlib already has the same object or statement (four definitions, one hypothesis form, one lemma). Four are already one-line aliases (keep or inline). `powOneSubgroup` and `rsaPerm` can become the Mathlib object (`(powMonoidHom m).ker`, `powCoprime`) |
| **WRAP** | 9 | A derivation from a Mathlib lemma is markedly shorter than TCSlib's proof, or removes a hypothesis. **Replacing the proof is recommended** |
| **WRAP✓** | 26 | Already implemented as a ≤3-line composition of Mathlib lemmas. No action |
| **PARTIAL** | 14 | Mathlib has a key ingredient, but the TCSlib proof is already about as short, or the statement is about TCSlib's own algorithm |
| **NONE** | 35 | Nothing at this pin (what was searched is given in the row or in (a)–(e)) |

**Headline.** The base already piggybacks on Mathlib heavily, with 26 WRAP✓ rows and 6 DUP
aliases. No proved TCSlib number-theory *theorem* is a verbatim Mathlib duplicate. Eight proved
proofs can be shortened (the ninth WRAP row is the core of the sorried `elGamal_correct`). The substantive TCSlib content is new relative to this pin:
- Chebyshev's lower bound and the prime density `|Π_n| ≥ 2^n/2n`;
- the totient density `m ≤ φ(m)(log₂ m + 1)`;
- Miller–Rabin (liar set and the `≤ (N−1)/2` bound);
- the four-root and CRT residue theory mod `pq`;
- the Blum square root;
- the gcd-factoring lemma;
- extended Euclid and repeated squaring with operation counts;
- discrete logs and the safe-prime group facts.

## Table

`NT/` is `TCSlib/Cryptography/NumberTheory/` and `C/` is `TCSlib/Cryptography/Candidates/`.
Mathlib files are given relative to `Mathlib/`.

| TCSlib declaration (file:line) | class | Mathlib name (file) | evidence | recommended action |
|---|---|---|---|---|
| **Chebyshev.lean** | | | | |
| `Primes` (NT/Chebyshev:78) | NONE | analogue `Nat.primesBelow` (NumberTheory/SmoothNumbers) is a `Finset`, not a `Fin`-subtype | grep | keep (`uprob` needs the type) |
| `card_primes` (:81) | WRAP✓ | `Nat.primesBelow_card_eq_primeCounting'` (NumberTheory/PrimeCounting) | proof is that lemma plus a `Fintype.card_congr` | none |
| `two_mul_le_two_pow` (:92, private) | NONE | — | E1: `exact?` could not close | keep |
| `two_pow_le_centralBinom` (:102, private) | PARTIAL | `Nat.four_pow_le_two_mul_self_mul_centralBinom` (Data/Nat/Choose/Central), already used | E2: none | keep |
| `two_pow_le_pow_primeCounting` (:120) | PARTIAL | `Nat.prod_pow_factorization_centralBinom`, `Nat.pow_factorization_choose_le` (Data/Nat/Choose/Factorization), already used | E3: none | keep |
| `chebyshev_two_mul`, `chebyshev` (:143, :171) | NONE | no π(x) lower bound at the pin; see (a) | E18: none; grep "chebyshev" in NumberTheory: no hit | keep |
| `primeCounting_two_pow` (:240, private) | NONE | `Nat.count_succ` (used) | — | keep |
| `two_pow_le_two_mul_card_primes` (:252) | NONE | — | E19: none | keep |
| **Euclid.lean** (no user outside the file) | | | | |
| `extEuclid`, `extEuclidCalls` and 6 unfolding lemmas (NT/Euclid:70–116) | NONE | Mathlib's `Nat.xgcd`/`Nat.gcdA`/`Nat.gcdB` (Data/Int/GCD) is a different recursion with no call counter; I did not check equality with it | grep | keep (the formalized object is Algorithm 43.2) |
| `extEuclid_spec` (:130) | PARTIAL | `Nat.gcd_eq_gcd_ab` (Data/Int/GCD) is Bézout for `gcdA`/`gcdB` | P1.16 | keep; cite it as the Mathlib analogue |
| `extEuclid_inv` (:153) | PARTIAL | `ZMod.coe_mul_inv_eq_one` (Data/ZMod/Basic) | P1.17 | keep (its subject is the algorithm's output) |
| `extEuclidCalls_le` (:175) | NONE | no Lamé-type bound | grep `Lame`, `xgcd`: no hit | keep |
| **ModExp.lean** (no user outside the file) | | | | |
| `modExpLoop`, `modExp`, `modExpMults` and all 9 lemmas (NT/ModExp:59–178) | NONE | no repeated-squaring algorithm or count (grep `powMod`, `modPow`: no hit); `modExp_cast` is thin over `ZMod.natCast_mod` | grep | keep |
| **Units.lean** | | | | |
| `units_val_mem` (NT/Units:72) | WRAP | `ZMod.val_pos`, `ZMod.val_lt` (Data/ZMod/Basic) | P1.1: one term | replace the 5-line proof by `⟨ZMod.val_pos.2 u.ne_zero, Nat.le_sub_one_of_lt (ZMod.val_lt _)⟩` |
| `totient_prime_mul_prime` (:83) | WRAP✓ | `Nat.totient_mul`, `Nat.totient_prime`, `Nat.coprime_primes` | E4: no single lemma; P1.2 | none |
| `card_units_zmod_prime_mul_prime` (:90) | WRAP✓ | `ZMod.card_units_eq_totient` (Data/Nat/Totient) | — | none |
| `units_pow_mod_totient` (:102) | WRAP✓ | `ZMod.pow_totient` (FieldTheory/Finite/Basic); `pow_mod_natCard` (GroupTheory/OrderOfElement) under `NeZero` | E5: none; P1.3 | none (the TCSlib form needs no `NeZero`) |
| `pow_mod_totient_modEq` (:108) | WRAP | `Nat.pow_totient_mod` (NumberTheory/PowModTotient; needs `1 < n`) | E12′: 3-line derivation for every `N` | optional; it needs a new import whose olean is not in the local cache (see caveat) |
| `rsa_pow_pow` (:123) | WRAP✓ | `ZMod.pow_totient`; equivalently `pow_mod_natCard` | E6: none; P1.4 | none |
| `rsa_pow_bijective` (:134) | WRAP✓ | `powCoprime` (GroupTheory/OrderOfElement) | P1.5 | none |
| `exists_rsa_inverse` (:143) | WRAP✓ | `Nat.exists_mul_emod_eq_one_of_coprime`, `Nat.totient_even` | — | none |
| `prod_le_prod_pred_mul_card` (:164, private) | NONE | — | — | keep |
| `le_totient_mul_log_succ` (:198) | NONE | no totient lower bound; see (b). Ingredient `Nat.totient_mul_prod_primeFactors` already used | E7: none | keep |
| **Primality.lean** (number theory only) | | | | |
| `mrExp`, `mrOdd`, `two_pow_mrExp_mul_mrOdd`, `mrOdd_odd`, `mrOdd_mul_two_pow` (NT/Primality:99–114) | WRAP✓ | `Nat.ordProj_mul_ordCompl_eq_self`, `Nat.not_dvd_ordCompl`; existential form `Nat.exists_eq_two_pow_mul_odd` | P1.10 | none |
| `MRLiar`, `mrLiars`, `mem_mrLiars`, `MRLiar.ne_zero` (:124–140) | NONE | Mathlib has only Fermat probable primes (`Nat.ProbablePrime`, NumberTheory/FermatPsp) | grep `miller`, `rabin`, `strong`: no hit | keep |
| `mrLiar_iff_of_prime`, `card_mrLiars_of_prime` (:154, :165) | PARTIAL | `ZMod.pow_card_sub_one_eq_one`, `mul_self_eq_one_iff` (used) | E13: `exact?` finds `ZMod.pow_card_sub_one_eq_one` for the ingredient | keep |
| `mrLiar_isUnit` (:172, private) | WRAP✓ | `IsUnit.of_pow_eq_one` | — | none |
| `units_pow_eq_one_iff`, `units_pow_eq_neg_one_iff` (:176, :181, private) | WRAP | `Units.val_eq_one`, `Units.val_pow_eq_pow_val` | P1.9: `rw [← Units.val_pow_eq_pow_val, Units.val_eq_one]` | optional: inline at use sites |
| `two_mul_card_le_of_ne_top` (:187, private) | WRAP | `Subgroup.card_mul_index`, `Subgroup.index_eq_one`, `Subgroup.index_ne_zero_of_finite` (GroupTheory/Index) | P1.7: 5 lines instead of 10 (E23: no single lemma) | replace the proof |
| `card_mrLiars_le_card` (:201, private) | NONE | — | — | keep |
| `powOneSubgroup`, `mem_powOneSubgroup` (:215, :228, private) | DUP | `(powMonoidHom m).ker`, `MonoidHom.mem_ker` | P1.8 | replace the 12-line structure by the kernel |
| `powPmOneSubgroup`, `mem_powPmOneSubgroup` (:232, :249, private) | PARTIAL | could be `Subgroup.comap (powMonoidHom m) {±1}`; Mathlib has no named `{±1}` subgroup | not probed | keep |
| `neg_one_ne_one_of_dvd_odd` (:253, private) | WRAP✓ | `ZMod.neg_one_ne_one` (Data/ZMod/Basic) | — | none |
| `not_prime_pow_of_forall_pow` (:265, private) | NONE | no Carmichael or Korselt theory (grep `armichael`: only FermatPsp prose). Ingredients `exists_prime_orderOf_dvd_card`, `Nat.totient_prime_pow` already used | grep | keep |
| `exists_coprime_factorization` (:290, private) | NONE | ingredients `Nat.ordProj_mul_ordCompl_eq_self`, `Nat.coprime_ordCompl` (used) | — | keep |
| `exists_unit_pow_ne` (:315, private) | PARTIAL | `Nat.chineseRemainder`, `ZMod.unitOfCoprime` (used); could use `crtUnits.symm (v mod n₁, 1)` | not probed | keep |
| `liar_pow_mem`, `two_mul_card_mrLiars_le` (:358, :410) | NONE | no Miller–Rabin liar bound | grep | keep |
| `millerRabin`, `base_ne_zero`, `millerRabin_of_prime` (:461–480) | NONE | — | — | keep |
| **QuadraticResidues.lean** | | | | |
| `QR` (NT/QuadraticResidues:90) | DUP | already `(powMonoidHom 2).range`; equals `Subgroup.square (ZMod N)ˣ` (Algebra/Group/Subgroup/Even) | P1.12: `ext`, 4 lines | keep the range form: `IsCyclic.card_powMonoidHom_range` consumes it directly. Optionally add `QR_eq_square` |
| `mem_QR_iff`, `DecidablePred` instance, `sq_mem_QR`, `sqTo`, `coe_sqTo` (:93–108) | WRAP✓ | `MonoidHom.mem_range`, `MonoidHom.decidableMemRange` | — | none |
| `card_units_eq_mul_card_QR` (:115) | WRAP | `Subgroup.index_ker`, `Subgroup.card_mul_index`, giving `\|Z_N^*\| = \|ker(x↦x²)\| · \|QR_N\|` | C2: `rw [QR, ← Subgroup.index_ker, Subgroup.card_mul_index]` | optional: replace the per-fibre hypothesis by the kernel count (the fibre over `1`) |
| `ne_neg_self` (:136, private) | NONE | (thin; `ZMod.natCast_eq_zero_iff`) | — | keep |
| `card_sqrt_eq_two` (:154) | PARTIAL | `legendreSym.card_sqrts`, `quadraticChar_card_sqrts` (NumberTheory/LegendreSymbol/{Basic, QuadraticChar/Basic}). These count field elements with an `ℤ` argument; the transfer to units is no shorter | E8: none | keep |
| `card_QR_prime` (:167) | WRAP | `IsCyclic.card_powMonoidHom_range` (GroupTheory/SpecificGroups/Cyclic), `ZMod.card_units`, `Nat.gcd_eq_right` | P1.11: 4 lines, independent of the fibre count | replace the proof |
| `div_four_succ_eq` (:173) | NONE | arithmetic (`omega`) | — | keep |
| `sq_pow_div_four_succ` (:183) | WRAP | `ZMod.euler_criterion_units` (NumberTheory/LegendreSymbol/Basic) | P1.14: 2 lines; E9: none | replace the proof |
| `pow_div_four_succ_mem_QR` (:195) | NONE | trivial | — | keep |
| `sqrtMod3`, `sqrtMod3_sq` (:201, :208) | PARTIAL | `ZMod.euler_criterion` (`a ≠ 0` case); `ZMod.pow_card_sub_one_eq_one` already used | E10: none | keep; optionally mirror P1.14 |
| `crtUnits` (:232) | DUP | no named definition in Mathlib; this is exactly the inline construction of `Data/Nat/Totient:133` and `RingTheory/ZMod/UnitsCyclic:267` | C1: `rfl` | keep (the named alias is useful) |
| `crtUnits_fst`, `crtUnits_snd` (:236, :242) | WRAP✓ | `Prod.fst_zmod_cast`, `Prod.snd_zmod_cast` | — | none |
| `mem_QR_mul_iff`, `sq_crtUnits_symm`, `card_sqrt_mul` (:255, :268, :278) | NONE | no residue theory modulo composites | grep | keep |
| `coprime_of_ne` (:300) | DUP | `(Nat.coprime_primes hp hq).2` (Data/Nat/Prime/Basic) | P1.13: literally the body | keep as a convenience, or inline |
| `card_sqrt_mul_eq_four`, `card_QR_mul` (:309, :320) | NONE | — | grep | keep |
| `gcd_sub_eq_prime_of_sq_eq_sq` (:352) | NONE | — | E11: none (ℕ core) | keep |
| `blumSqrt`, `blumSqrt_sq`, `blumSqrt_mem_QR`, `eq_blumSqrt_of_sq_eq`, `sqTo_bijective_of_blum` (:410–484) | NONE | ingredient `ZMod.exists_sq_eq_neg_one_iff` already used | grep `Blum`: no hit | keep |
| **Candidates** | | | | |
| `val_units_pow` (C/Arithmetic:352) | WRAP✓ | `Units.val_pow_eq_pow_val`, `ZMod.val_natCast`, `ZMod.natCast_zmod_val` | E17: none | none |
| `one_div_card_primes_le` (C/Concrete:341) | NONE | corollary of `two_pow_le_two_mul_card_primes` | — | keep |
| `DistinctPrimes.neZero_totient`, `totient_mul` (C/Concrete:398, :408) | WRAP✓ | `Nat.totient_pos`; alias of `totient_prime_mul_prime` | — | none |
| `DistinctPrimes.one_lt_totient` (:412) | PARTIAL | `Nat.totient_eq_one_iff`, `Nat.totient_pos` (Data/Nat/Totient) | P1.6; E21: none | keep (no shorter) |
| `fmultNat_eq_mul_prime` (C/Factoring:110) | WRAP | `Nat.dvd_mul`, `Nat.dvd_prime` (Data/Nat/Prime/Basic) | P1.23: the core in 8 lines instead of about 30; E22: none | replace the `key` argument |
| `rsaPerm` (C/RSA:143) | DUP | `powCoprime h : G ≃ G` with `toFun g := g ^ n` (GroupTheory/OrderOfElement:1031) | source read | optional: define as `powCoprime` (needs `Nat.card` coprimality, as in `rsa_pow_bijective`) |
| `rsaPerm_symm_apply` (:153) | WRAP✓ | via `rsa_pow_pow` | — | none |
| `mul_inv_val_modEq` (:169) | WRAP✓ | `ZMod.coe_mul_inv_eq_one`, `ZMod.val_mul` | E16: none | none |
| `BlumDistinctPrimes.ne_two` (C/Rabin:92) | NONE | arithmetic | — | keep |
| `BlumDensity` (:117, hypothesis) | NONE | only Dirichlet *infinitude*: `Nat.infinite_setOf_prime_and_eq_mod`, `Nat.forall_exists_prime_gt_and_modEq` (NumberTheory/LSeries/PrimesInAP), no counting form | grep | keep the hypothesis; its docstring is accurate |
| `crtNegOne`, `crtNegOne_sq`, `crtNegOne_ne_one`, `crtNegOne_ne_neg_one` (:155–176) | NONE | ingredient `ZMod.neg_one_ne_one` (used) | — | keep |
| `BlumValid.exists_mul`, `sqTo_bijective_of_exists` (:668, :676) | NONE | thin wrappers | — | keep |
| `blumInvNat`, `blumInv_spec` (:789, :823, sorried) | PARTIAL | `ZMod.coe_mul_inv_eq_one`; Mathlib's `Nat.chineseRemainder` is a different formula | C6: the mod-`p` reduction of the formula in 3 lines | fill route (see Advice) |
| `coprime_dlG_dlP`, `orderOf_expUnit` (C/DiscreteLog:189, :201) | WRAP✓ | `Nat.Prime.coprime_iff_not_dvd`, `orderOf_units` | — | none |
| `expF_injective` (:263) | PARTIAL | `pow_injOn_Iio_orderOf` (GroupTheory/OrderOfElement); `pow_eq_pow_iff_modEq` already used | P1.20 | keep |
| `expValid_dlDefaultIndex` (:401) | WRAP✓ | `orderOf_eq_prime` | — | none |
| `IsGenerator` (C/DiscreteLogHardcore:116) | DUP | Mathlib's hypothesis form `∀ x, x ∈ Subgroup.zpowers g`, as in `IsCyclic.exists_generator` | C4 | keep (an abbreviation of Mathlib's form) |
| `IsGenerator.orderOf_eq` (:120) | WRAP✓ | `orderOf_eq_card_of_forall_mem_zpowers` | — | none |
| `expo_injective`, `expo_bijective` (:124, :134) | PARTIAL | `pow_injOn_Iio_orderOf`; `IsCyclic.unique_zpow_zmod` (`∃! n : ZMod (card), x = a ^ n.val`) | P1.20 | keep |
| `dlog`, `expo_dlog`, `dlog_expo` (:138–145) | NONE | no discrete-log function (existence only via `IsCyclic.unique_zpow_zmod`) | grep `dlog`, `discreteLog`: no hit | keep |
| `two_mul_half` (:152) | NONE | arithmetic | — | keep |
| `neg_one_ne_one_units` (:160) | WRAP✓ | `ZMod.neg_one_ne_one` | — | none |
| `pow_half_eq_neg_one` (:171) | PARTIAL | `ZMod.pow_div_two_eq_neg_one_or_one` | C3 (same length); E14: none | keep |
| `pow_mem_QR_iff` (:190) | WRAP✓ | `ZMod.euler_criterion_units`, `neg_one_pow_eq_one_iff_even` | — | none |
| `sq_eq_pow_two_mul_iff` (:203) | WRAP✓ | `Units.sq_eq_sq_iff_eq_or_eq_neg` | — | none |
| `neg_pow_eq` (:210) | NONE | trivial | — | keep |
| `dlBits_pow` (:319, sorried) | NONE | algorithm-specific; ingredients in C8 | — | fill (see Advice) |
| `safe_ne_two`, `five_le_safe`, `safe_half` (C/ElGamal:115–125) | NONE | arithmetic | — | keep |
| `card_QR_safe`, `card_sqrt_safe` (:129, :164) | WRAP✓ | thin over `card_QR_prime` and `card_sqrt_eq_two` | — | none |
| `mem_QR_iff_pow_eq_one` (:134) | WRAP✓ | `ZMod.euler_criterion_units` | C10 | none |
| `orderOf_eq_of_mem_QR` (:139) | WRAP✓ | `orderOf_eq_prime` | — | none |
| `zpowers_eq_QR` (:144) | WRAP✓ | `Subgroup.eq_of_le_of_card_ge`, `Nat.card_zpowers` | — | none |
| `eq_QR_of_card` (:151) | NONE | no "a subgroup of a cyclic group is determined by its order" lemma | E15: none | keep |
| `egSquareGen_valid` (:688) | NONE | thin over `orderOf_eq_of_mem_QR` | — | keep |
| `elGamal_correct` (:663, sorried), number-theory core | WRAP | the group identity `(h^a)^b·m·((h^b)^a)⁻¹ = m` from `pow_mul`, `mul_comm`, `mul_inv_cancel_comm` | C7: one `rw` | fill (see Advice) |

## Answers

**(a) Chebyshev's lower bound on π(x), or primes in dyadic intervals.** There is nothing at this pin
beyond Bertrand and the upper-type bounds. These are all the prime-counting and
central-binomial facts at the pin:
- `Nat.exists_prime_lt_and_le_two_mul` (Bertrand, `NumberTheory/Bertrand`), with
  `Nat.exists_prime_lt_and_le_two_mul_eventually` and `Bertrand.real_main_inequality`;
- `Nat.primeCounting'_add_le` (an *upper* bound), `Nat.tendsto_primeCounting` (`π → ∞`, no
  rate), `Nat.primesBelow_card_eq_primeCounting'` (`NumberTheory/PrimeCounting`);
- `primorial_le_4_pow` (`NumberTheory/Primorial`, root namespace: the upper-bound ingredient);
- `Nat.four_pow_le_two_mul_self_mul_centralBinom` (`Data/Nat/Choose/Central`),
  `Nat.prod_pow_factorization_centralBinom` and `Nat.pow_factorization_choose_le`
  (`Data/Nat/Choose/Factorization`);
- `Nat.roughNumbersUpTo_card_le'` and `not_summable_one_div_on_primes` (`NumberTheory/SumPrimeReciprocals`).

The pin has no Chebyshev `θ`/`ψ` function, no `π(x) ≥ c·x/log x`, and no count of primes in
`[2^{n−1}, 2^n)`: grep "chebyshev" in `NumberTheory/` gives no hit, and `exact?` E3, E18 and E19
report "could not close". Bertrand only gives `π(2^n) ≥ n − 1`. TCSlib's `chebyshev`,
`two_pow_le_pow_primeCounting` and `two_pow_le_two_mul_card_primes` are therefore new. Dirichlet
gives only infinitude (`Nat.infinite_setOf_prime_and_eq_mod`), so `Rabin.BlumDensity` correctly
stays a hypothesis.

**(b) A lower bound on Euler's totient.** None. `Data/Nat/Totient` has `totient_le`, `totient_lt`,
`totient_pos`, `totient_eq_one_iff`, `totient_even`, `totient_super_multiplicative`, and the product
formulas `totient_mul_prod_primeFactors` and `totient_eq_div_primeFactors_mul`. It has no
`φ(N) ≳ N/log N` and no `N/log log N` (grep `≤ φ`, `≤ totient`: no hit; `exact?` E7: none).
`le_totient_mul_log_succ` is new, and it already rests on `Nat.totient_mul_prod_primeFactors`.

**(c) Quadratic residues.**
- **Euler's criterion: yes.** `ZMod.euler_criterion_units` (units, `∃ y, y^2 = x ↔ x^(p/2) = 1`),
  `ZMod.euler_criterion` (`a ≠ 0`, `IsSquare`), `ZMod.pow_div_two_eq_neg_one_or_one` and
  `legendreSym.eq_pow` (`NumberTheory/LegendreSymbol/Basic`). Over a general finite field the forms
  are `FiniteField.unit_isSquare_iff` and `FiniteField.isSquare_iff` (`FieldTheory/Finite/Basic`).
  TCSlib already uses the units form in four places.
- **Quadratic reciprocity: yes.** `legendreSym.quadratic_reciprocity` (and `'`, `_one_mod_four`,
  `_three_mod_four`) and `ZMod.exists_sq_eq_prime_iff_of_mod_four_eq_three`
  (`LegendreSymbol/QuadraticReciprocity`).
- **Jacobi symbol: yes.** `jacobiSym`, `jacobiSym.quadratic_reciprocity` and
  `ZMod.nonsquare_of_jacobiSym_eq_neg_one` (`LegendreSymbol/JacobiSymbol`). TCSlib uses none
  of these, and none of the in-scope statements needs them.
- **Square roots mod `p ≡ 3 (mod 4)`.** Mathlib has no explicit `y^{(p+1)/4}` formula, but the
  proof is 2 lines from `ZMod.euler_criterion_units` (P1.14). `ZMod.exists_sq_eq_neg_one_iff` and
  `ZMod.mod_four_ne_three_of_sq_eq_neg_one` cover `−1` as a nonresidue.
- **Root counts.** `legendreSym.card_sqrts` and `quadraticChar_card_sqrts` count `χ(a) + 1`.
- **`|QR_p| = (p−1)/2`.** Use `IsCyclic.card_powMonoidHom_range` (P1.11).
- **CRT for units.** Mathlib has no named equivalence. The inline construction
  `(Units.mapEquiv (ZMod.chineseRemainder h).toMulEquiv).trans MulEquiv.prodUnits` is `rfl` to
  `crtUnits` (C1).
- **The four square roots of a QR mod `pq`: none.**

**(d) Miller–Rabin and Fermat witnesses.** There is no Miller–Rabin, no strong pseudoprime, no
liar or witness density and no Carmichael/Korselt theory at the pin. Fermat appears only as
definitions and infinitude results:
- `Nat.ProbablePrime`, `Nat.FermatPsp`, `Nat.probablePrime_iff_modEq`, `Nat.coprime_of_probablePrime`,
  `Nat.exists_infinite_pseudoprimes` (`NumberTheory/FermatPsp`);
- `lucas_primality` (`NumberTheory/LucasPrimality`).

TCSlib's liar bound already uses the Mathlib ingredients: `ZMod.pow_card_sub_one_eq_one`
(Fermat), `Subgroup.card_subgroup_dvd_card` (Lagrange) and `exists_prime_orderOf_dvd_card`
(Cauchy). Only `two_mul_card_le_of_ne_top` (WRAP) and `powOneSubgroup` (DUP) can shrink.

**(e) Cyclic units, generators, orders: yes, extensively.**
- **Cyclicity.** `IsCyclic (ZMod p)ˣ` is inferred from the existing imports (P1.21, through the
  finite-field units). `ZMod.isCyclic_units_prime` and the full classification
  `ZMod.isCyclic_units_iff` are in `RingTheory/ZMod/UnitsCyclic`, which is not in the closure.
- **Generators.** `IsCyclic.exists_generator`, `IsCyclic.exists_ofOrder_eq_natCard`,
  `IsCyclic.card_orderOf_eq_totient` (`#{a | orderOf a = d} = φ d`) and
  `orderOf_eq_card_of_forall_mem_zpowers`.
- **Exponents.** `IsCyclic.unique_zpow_zmod` (the unique exponent in `ZMod (card)`, i.e. the
  existence of discrete logs), `pow_injOn_Iio_orderOf`, `pow_eq_pow_iff_modEq`, `orderOf_eq_prime`
  and `Nat.card_zpowers`.
- **Power maps.** `IsCyclic.card_powMonoidHom_range`/`_ker`/`index_*` and `powCoprime`.

What is missing: a discrete-log *function*, safe-prime facts, and uniqueness of the order-`q`
subgroup (E15: none). `ElGamal.eq_QR_of_card` stays.

## Advice for the fill briefs

The fills should cite these instead of proving them. Every name below is reachable from the
candidate files' **existing** imports (`NTOverlap5.log`) unless it is marked otherwise.

- **rsa, S3 `statClose_sampleUnitL`** (transport `{v < 2^k | v < N ∧ gcd = 1} ≃ (ZMod N)ˣ`). Use
  `ZMod.unitsEquivCoprime : (ZMod n)ˣ ≃ {x : ZMod n // x.val.Coprime n}`, `ZMod.finEquiv n : Fin n ≃+* ZMod n`,
  `ZMod.val_coe_unit_coprime`, `ZMod.coe_unitOfCoprime`, `ZMod.isUnit_iff_coprime` and `ZMod.val_lt`.
  The acceptance rate uses TCSlib's `le_totient_mul_log_succ`, which Mathlib does not have.
- **rsa, `rsaCollection_invProbAt_le`** (`Φ ≥ 2`). `DistinctPrimes.one_lt_totient` exists. The
  Mathlib route is `Nat.totient_eq_one_iff` with `Nat.totient_pos`, so there is nothing new to prove.
- **rsa, `factorProb_le_rsaProb` / `rsaFromFactorStep_correct`.** These are already proved on
  `rsa_pow_pow`, `mul_inv_val_modEq` and `ZMod.natCast_mod`. If an exponent identity is needed, use
  `pow_mod_natCard` (with `Nat.card_eq_fintype_card` and `ZMod.card_units_eq_totient`) or
  `ZMod.pow_totient`. Do not use `Nat.pow_totient_mod`: its module is not imported (caveat below).
- **rabin, `blumInv_spec`** (P13 route). The mod-`p` component of `blumInvNat` is
  `push_cast; rw [ZMod.natCast_self, ZMod.natCast_zmod_val, ZMod.coe_mul_inv_eq_one q h]; ring`
  (C6, with `[NeZero p]` and `h : q.Coprime p`), and symmetrically mod `q`. Then use
  `ZMod.chineseRemainder` / `crtUnits_fst`/`_snd`, `ZMod.unitOfCoprime` and the TCSlib lemmas
  the brief names (`sq_pow_div_four_succ`, `pow_div_four_succ_mem_QR`, `mem_QR_mul_iff`,
  `sq_crtUnits_symm`, `eq_blumSqrt_of_sq_eq`).
- **rabin, the odd and Blum generators.** Test parity and residues with `Nat.odd_iff` and
  `Nat.Prime.eq_two_or_odd'`. Blum density has no Mathlib source, so keep `hD`. Odd-prime density
  is `two_pow_le_two_mul_card_primes` (TCSlib) minus the single prime `2`. Mathlib's Bertrand
  (`Nat.exists_prime_lt_and_le_two_mul`) is too weak, and its module is not imported.
- **rabin, the reductions.** These use `Units.sq_eq_sq_iff_eq_or_eq_neg`, `ZMod.neg_one_ne_one`
  (`Fact (2 < n)`), `Nat.Coprime.gcd_mul`, `Nat.Coprime.mul_dvd_of_dvd_of_dvd`, `Nat.Prime.dvd_mul`
  and `Nat.dvd_prime`. The factoring step itself is TCSlib's `gcd_sub_eq_prime_of_sq_eq_sq`, which
  Mathlib does not have.
- **fac, `factoringCollection_invProbAt_le`.** This uses `fmultNat_eq_mul_prime` as is. If its
  proof is touched, the Mathlib core is `Nat.dvd_mul` with `Nat.dvd_prime` (P1.23).
- **dl-b, `dlBits_pow`.**
  - Squares and roots: `ZMod.euler_criterion_units` (behind `pow_mem_QR_iff`),
    `Units.sq_eq_sq_iff_eq_or_eq_neg` (behind `sq_eq_pow_two_mul_iff`) and
    `ZMod.units_pow_card_sub_one_eq_one`.
  - Exponents: `pow_eq_pow_iff_modEq` and `pow_injOn_Iio_orderOf` to compare them, and
    `IsGenerator.orderOf_eq` for the order.
  - Parity: `Nat.even_or_odd`, `Nat.two_mul_div_two_of_even`, `Nat.two_mul_div_two_add_one_of_odd`.
  - There is no Mathlib discrete log. Use `dlog_expo`.
- **dl-c, `elGamal_correct`.** The group core is
  `rw [← pow_mul, ← pow_mul, mul_comm a b, mul_inv_cancel_comm]` (C7). Read residues with
  `ZMod.natCast_mod`, `ZMod.val_natCast_of_lt`, `ZMod.natCast_zmod_val` and
  `Units.val_pow_eq_pow_val`.
- **dl-c, `statClose_sq_generator`.** The number theory is `card_QR_safe` (TCSlib, on
  `card_QR_prime`) and `Fintype.card_subtype_compl`. If `|G_q| = q` is needed afresh, the Mathlib
  route is `IsCyclic.card_powMonoidHom_range` (P1.11).
- **dl-a.** The sampler and polynomial-time targets need no number theory. `expF_injective` is done.
- **3col.** The only number theory is `Nat.sqrt`/`Nat.sqrt_eq`, which is core Mathlib and already
  cited. There is nothing to add.

**Import caveat.** Seven names in this report are outside the candidate files' import closure:
- `Nat.pow_totient_mod` (`NumberTheory/PowModTotient`);
- `Subgroup.square` (`Algebra/Group/Subgroup/Even`);
- `ZMod.isCyclic_units_prime` (`RingTheory/ZMod/UnitsCyclic`);
- `Nat.ProbablePrime` (`NumberTheory/FermatPsp`);
- `legendreSym.quadratic_reciprocity` and `jacobiSym.quadratic_reciprocity`;
- `Nat.exists_prime_lt_and_le_two_mul` (`NumberTheory/Bertrand`).

The first four modules also have **no olean in the local Mathlib cache**, so a worker would need a
cache fetch for them. The fill briefs authorize no such import, and none is needed: every route
above uses names already in scope.

## Not checked

- Whether `extEuclid a b` agrees with Mathlib's `(Nat.gcdA a b, Nat.gcdB a b)`. The recursions
  differ, and it does not matter while `Euclid.lean` formalizes Algorithm 43.2 and its call count.
  Neither `Euclid.lean` nor `ModExp.lean` has a user outside its own file.
- A probe of `powPmOneSubgroup` as a `comap`, and of `exists_unit_pow_ne` through `crtUnits`
  (both PARTIAL, not probed).
- `exact?` cannot see modules outside its imports. Coverage there rests on the greps quoted in
  the rows. `NumberTheory/LSeries/PrimesInAP` was read but not compiled.
