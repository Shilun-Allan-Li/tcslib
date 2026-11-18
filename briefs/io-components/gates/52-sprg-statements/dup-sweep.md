# Gate 52 · duplication sweep (maintainer, static)

Static sweep of the io-sprg checkpoint-0 statements (`inbox/fills/io-sprg/src/` at exchange
`15946b52d0615fda8afad9ed3c57cfaf5beaaa8d`, source HEAD `d10a560b34d58919bc1a5206ce66a444613f94c7`)
against TCSlib at the base `5ed465f62e4ae0f93ded1a1ba49e807591b589eb` and Mathlib `029db123`.
No Lean was run: the sweep is by name, by `git grep` of the base and of the pinned Mathlib checkout,
and by reading. The gate confirms it with `exact?`/`apply?` probes where it doubts a row. `SS/` is
`TCSlib/Cryptography/Obfuscation/StructuredSeed/`.

The rule (prompt §8; `briefs/pass-shelat-ch5-8/duplication-ledger.md`): an undisclosed re-proof or
restatement of a public TCSlib or Mathlib lemma, including an inline re-derivation, is a **major**.
A disclosed near-copy with a promotion request is a minor at most.

## 0. Searches

- Declarations: the 670 written declarations of `evidence/checks/m0-sp-w3/decls2.log` (611 short
  names) against the 29,724 short names declared under `TCSlib/` at the base (the Gate 51 index;
  same base). 16 short names coincide (`Data`, `Params`, `Secure`, `W`, `adv`, `bucket`,
  `draw_eq`, `enc`, `encSample`, `noise`, `nonempty`, `rc`, `sample_eq`, `secure_iff`, `seed_eq`,
  `w`); all are in the job's own namespace, and the delivery's clash scan
  (`evidence/checks/m0-sp-w3/clash.log`: "670 new names, 0 clashes") finds no full-name clash. The
  new files `open` only `Complexity`, `Turing`, `Games`, `CoinSampling` and their own namespace.
- Concepts, by `git grep` at the base: `LPN` (none); `PrimeParam|PrimeSchedule` (none);
  `sparse` factorisation (none; only Fourier-sparsity results); `weightedTotalDegree_add|_mul`
  (none in TCSlib; Mathlib at the pin has only `_zero`, `_coe`, `_one`, `_rename_of_injective`,
  `_eq_zero_iff`, `le_weightedTotalDegree`); `findGreatest` (one hit: `PadQuad.nu`, S1);
  `uprob_pi_forall` (`OneWayFunctions/Basic.lean:118`, S2; `uprob_pi_forall_dep` in
  `Asymptotic/Permutations.lean:287`); `Real.exp 1 *` binomial bounds (only inline copies inside private
  proofs, S5); `foldr pairEncode` (none in the delivery).

## 1. Must-reuse items (`duplication-sweep-r2.md` as amended by `-r3.md`)

| Item | Used | Remark |
|---|---|---|
| `LWE.Noise`, `LWE.Parameters`, `LWE.Family`, `advantageAt`, `DLWEAssumption`, `dlweAssumption_iff` | yes | `lpnNoise` is an `LWE.Noise`; `LPNFamily.Raw.toLWE`, `.adv`, `.Assumption`, `assumption_iff` (`SS/LPN.lean:136–184`) |
| `LWE.encodeChallenge` (+ `_injective`) | yes | `lpnEnc` is exactly it (`SS/Reductions/LPN.lean:68`); injectivity planned from the base lemma |
| `Complexity.NUPPT.RealizesOn` and readers; `exists_realizesOn_of_preTarget` | yes | every realiser hypothesis; `realizable_of_targets` sketch; no local variant |
| `CoinSampling.SamplesEfficiently`, `DrawSamplable`, `CoreComputable`, `.intro`, `.congr` | yes | the five sampler fields and T3, T5, T6; no `SamplerEfficiency.lean`; no product sampler |
| `Foundations/Subexponential` (`SubexpSmall`, `SubexpHard`, closure, `comp_of_rpow_le`, `subexpSmall_two_pow_neg`) | yes | only one-line wrappers `SPRG.Raw.SubexpSecure`, `BoolPRG.SubexpSecure` with `_iff` |
| `Negligible` closure, `Negligible.polyExpr_mul` | planned | `jls_secure` sketch |
| `Encoding.Modular.encodeVector`/`encodeMatrix` | yes | seeds, matrices, advice residues |
| `BoolCircuit.encodeList`, `pairEncode`, `Candidates.natToList` | yes | buckets, noise lists, term lists, `PrimeParam.enc` |
| `finSumFinEquiv`, `finProdFinEquiv`, `finFunctionFinEquiv`, `finCongr`, `ZMod.finEquiv` | yes | every explicit coordinate equivalence; no `Fintype.equivFin` |
| `exists_expect_sample_le`, `abs_expect_sub_le_expect`, `advantage_hybrid`, `abs_prob_sub_le_of_agree` | planned | hop and hybrid sketches; `Lamport/Averaging` imported in `SS/Claim42/Load.lean:8`, `Games.Hopping` in `SS/Hybrids.lean:7` |
| `uprob_exists_le`, `Nat.choose_le_pow_div`, `Real.pow_div_factorial_le_exp` | planned | `Claim42/Load` sketches |
| `MvPolynomial` (`restrictDegree`, `vars`, `eval₂Hom_congr'`, `rename`, `weightedTotalDegree_rename_of_injective`, `Finset.prod_univ_sum`) | yes / planned | |
| `Nat.exists_prime_lt_and_le_two_mul` | yes | `PrimeSchedule.nonempty` only |
| Not to use: `PrimeFind`, `rejectionSample`, `StatClose`, `sampleFromBits`, `uniformFromBits`, `DyadicUniform`, `Games.Closeness`, other `CoinSampling` modules, `Programs/*`, `RAMSimulation/*`, the Phase B appendix | not used | `Complexity.BinArith.pairEncode_nil_append` was considered and not used (`evidence/route-requests/raw-selector-encoding-exploration.txt`) |

## 2. Items

| # | Where (delivery) | Nearest existing | Disclosed? | Grade |
|---|---|---|---|---|
| **S1** | `SS/Params.lean:155` `kappaOf`, `:164` `kappaOfN` (`Nat.findGreatest (· ^ e ≤ L) L`), readers `kappaOf_le`, `kappaOfN_le`, `kappaOf_pow`, `kappaOfN_n` | `PadQuad.nu` (`Asymptotic/UniversalPadding/Parameter.lean:36`, same body) with `nu_le`, `nu_pow_le`, `lt_succ_nu_pow`, `le_nu` (`:43–61`); the module is imported (`SS/Params.lean:7`) but unused at M0 | partly (the import and "reuse existing bounded power inverse API"; not that the definition duplicates `nu`) | minor (intake F03): define `kappaOf P L := PadQuad.nu P.E L` |
| **S2** | `SS/Claim42/Load.lean:9` imports `OneWayFunctions.Basic` for `uprob_pi_forall` | the lemma itself (reused, not copied) | partly (REPORT: "existing coordinate-independence API") | minor (layering, intake F04); promote to `Foundations/Probability` |
| **S3** | `LPNFamily.Raw.{residueEquiv, vectorEquiv, matrixEquiv, noiseSeedEquiv, noiseVectorEquiv}` (`SS/LPN.lean:214–267`) and `ConstructionEncoding.{…}` (`SS/Encoding.lean:50–107`) | each other | no | minor (intake F05): one set for an arbitrary modulus |
| **S4** | `SS/Degree.lean:70–110` `Internal.weightedTotalDegree_add_le`, `_mul_le`, `_finset_sum_le`, `_finset_prod_le`, `_C`, `_X_le` | none in Mathlib at the pin (`totalDegree_*` analogues, `AddMonoidAlgebra.sup_support_add_le`/`sup_support_mul_le`, `supDegree_sum_le`/`_prod_le` exist and are planned for the proofs) | yes (design-r1 §4.4; REPORT.md:333) | note: Mathlib-shaped, upstream candidates; the gate checks the sketches reuse the `AddMonoidAlgebra` lemmas |
| **S5** | `SS/Claim42/Load.lean:54` `Internal.binomial_bound` (C(n,k) ≤ (e n/k)^k) | private/inline copies only (`KikuchiLDC/LDC/BackgroundFacts.lean:252` `h_binom`; `DeterministicCC/FuncIndexing/LowerBound.lean:544`, inside the private `choose_quarter_le_eleven_pow`) | yes (sweep-r2 §G foresaw "one disclosed public helper") | note |
| **S6** | `SS/Defs.lean:48`, `:72` `PrimeParam`, `PrimeSchedule` | none at the base; io-phfe's `p : ℕ → ℕ` with `hp` (not landed) | n/a | note (intake F12): two schedule notions for one Theorem 5.1 |
| **S7** | `SS/Buckets.lean` (`bucket`, `load`, `overfull`, `rank`, `indexMap`, `bucketMatrix`), `SS/SparseFactor.lean` | none | yes | none: new |
| **S8** | `SS/PolyTerms.lean` (`PolyTerms`, `denote`, `encInt`, `encFin`, `encTerms`) | none (no string encoding of `MvPolynomial` at the base) | yes | none: new; reuses `encodeList`, `pairEncode` |
| **S9** | `SS/Samplers.lean:186` `firstGood := (List.finRange κ).find? flags` | `List.find?` API | yes | none |
| **S10** | `SS/BoolPRG.lean:50` `BoolPRG` and its game | `Pseudorandom/Generators/Asymptotic/Defs` `PRG` (X: Stage 2 owns it) | yes | none: the link "a PRG is an sPRG" is out of scope |
| **S11** | `SS/LPN.lean:341` `encDraw` (variable-width `Nat.bits` selectors) vs `SS/Encoding.lean:288` `encOneDraw` (fixed `natToList (ℓ+1)`) | each other (different codes for the same seed type) | yes (`raw-selector-encoding-exploration.txt`) | note: consistent enough; both injective |

## 3. For the gate

- Run `exact?`/`apply?` (one slot) on `Params.kappaOf_le`, `kappaOfN_le`, `kappaOf_pow`
  (after unfolding through `kappaOf_eq`/`nu_eq`), `Internal.weightedTotalDegree_add_le`,
  `_mul_le`, `_C`, `_X_le`, `Internal.binomial_bound`, `Internal.bucket_tail`,
  `LPNFamily.Raw.encSample_injective`, `Params.encSeed'_injective`, `firstGood_none_iff`,
  `SparseFactor.sparseFactor_mul_of_card_le`. A hit that closes a statement outright is a
  restatement: grade it (major if undisclosed).
- Check that no sketch plans to re-prove a public lemma inline (prompt §8): e.g. `lpnNoise_law`
  should go through the finite-product `uprob` readers, `lemma42`/`prop41` through
  `advantage_hybrid`/`exists_advantage_hybrid_gap` and `exists_expect_sample_le`, Claim 4.2's
  Markov step through `LamportReduction.expect_favourable_of_success` (or Stage 2's
  `ProbComp.mul_prob_le_expect` if at the base).
- Grade S1–S3, and say whether S6 needs a coordination ruling (intake Q-G52-5).
- Cross-job: the io-phfe delivery (`1e77173a…`, not landed) also defines explicit `ZMod`
  coordinate encodings and a prime schedule; no landed overlap, but note any shape both jobs should
  share.
