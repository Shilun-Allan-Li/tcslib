# Chapter 7 completeness grade, round 2 (printed AB09, pp. 123–143)

Independent grader pass, 2026-10-14, worktree `tcstcslib-ch7`, branch
`complexity/arora-barak-ch7`. For each round-1 problem (P1–P10) I read the new declarations
and checked them against the printed text (`ch7_book_pp123-143.txt`). I then re-read the whole
printed chapter: body, footnotes, "What have we learned", chapter notes and all exercises.
Paths below are relative to `TCSlib/Complexity/`.

**Sorry check.** No `sorry`, `admit`, `native_decide`, `axiom` or `implemented_by` in
`Randomized/*.lean`, which includes the new files `BPPAmplify`, `RPExpected`,
`AlgCircuitExample`, `BPOperator`, `QuasiPolyHierarchy` and `BPPEqP`. The only grep hit is the
English word "admits" in a docstring at `PTM.lean:45`.

**Name check.** Every one of the 260 backticked names in `SURVEY.md` and `NOT_FORMALIZED.md`
resolves to a declaration under `TCSlib/`, with one exception: SURVEY row G2 cites
`Complexity.P_ssubset_DTIME_pow_log`. The declaration is `Randomized.P_ssubset_DTIME_pow_log`
(`QuasiPolyHierarchy.lean` is entirely `namespace Randomized`). See R2. Spot-checked SURVEY line
numbers (10 of them) are now within 0–2 lines.

## 1. Round-1 problems: status

| # | Round-1 problem | Fix found | Faithfulness check | Status |
|---|---|---|---|---|
| P1 | Lemma 7.9 and Thm 7.10 abstract only | `FinNDTM.BPDecidesInTimeWith`, `BPP_PTMWith`, `InBPPWith`, `mem_BPP_PTMWith_iff` (PTMEquiv.lean:180–355); `bpp_error_reduction_polyTime`, `inBPPWeak_polyTimeModel_iff_inBPP`, `BPP_PTMWith_error_reduction`, `BPP_PTMWith_weakAdv_eq_BPP_PTM`, `BPP_PTMWith_const_eq_BPP_PTM` (BPPAmplify.lean:78–122) | These are genuine PTM-class statements. `BPP_PTMWith p` is polynomial-time PTMs with success `≥ p(|x|)` on every branch-halting machine. Lemma 7.9 is an equality of classes. In Thm 7.10, the hypothesis `1/2 + min(1/6, (n+1)^{-c})` is weaker than the book's `1/2 + n^{-c}` wherever the book's is defined, and the conclusion `1 − 2^{-((n+1)^d+1)}` is stronger than `1 − 2^{-n^d}`. Real `c` versus `ℕ` and the `n = 0` patch are recorded (BPPAmplify.lean:35–45). The "any constant > 1/2" statement of p.132 is also done. `mem_BPP_PTM_iff` is now the `2/3` instance | RESOLVED |
| P2 | Ex 7.11(d) weakened | `hitTime_le_length_mul` (`≤ k·D·(n−1)`), `hitTime_le_hundred_mul` (`≤ 100kn²`), `missProb_thousand_mul_pow_three_le` (`1000n³` walk misses w.p. `≤ 1/10`) (RandomWalkHitting.lean:503–538) | Both conclusions of the exercise are proved, uniformly in the truncation `N`, so they bound `E_{u,v}`. The extra hypothesis `D ≤ 100n` is recorded and justified (lines 47–55): for multigraphs with self-loops the printed bound is false, e.g. `E_{a,c} ≥ D` on the 3-vertex path. Simple regular graphs (`D ≤ n`) and the UPATH padded graphs (`D ≤ 2n`) satisfy it | RESOLVED |
| P3 | §7.4.2 for RTIME missing | `FinNDTM.RDecidesInExpTime`, `RP_ExpPTM`, `coRP_ExpPTM`, `RP_ExpPTM_eq_RP_PTM`, `coRP_ExpPTM_eq_coRP_PTM` (RPExpected.lean:55–215) | The truncation is one-sided: on timeout it answers 0, so non-members keep acceptance 0. Members get `≥ 5/8`, and two OR votes restore `2/3`. The non-member condition "every halted branch outputs 0" matches `RDecidesInTime` | RESOLVED |
| P4 | p.129 `∏(1+xᵢ)` example | `prodOnePlus`, `wellFormed_prodOnePlus`, `countP_isOp_prodOnePlus` (= 2n), `size_prodOnePlus` (= 3n+1), `toMvPolynomial_prodOnePlus`, `card_support_toMvPolynomial_prodOnePlus` (= 2ⁿ) (AlgCircuitExample.lean) | Exactly the book's claim. The size convention (`2n` operator gates against `3n+1` total nodes) is recorded | RESOLVED |
| P5a | BP·P = BPP (notes p.141) | `BPdot`, `BPdot_P_eq_BPP`, `BPdot_P_eq_BPP_PTM`, `BPdot_NP_eq_BPNP` (consistency with Def 7.17), `BPdot_BPP_eq_BPP` (BPOperator.lean) | Both inclusions are genuine. The generalization follows Def 7.16 rather than [Koz06]; this is recorded, and both give BPP for P | RESOLVED |
| P5b | BPP = P ⇒ BPP ⊊ DTIME(n^{log n}) | `P_ssubset_DTIME_pow_log` (QuasiPolyHierarchy.lean:308), proved by the time hierarchy (`diagLang`) with a time-constructible quasi-polynomial budget; `BPP_PTM_ssubset_DTIME_pow_log_of_eq_P` (BPPEqP.lean:91) | Genuine strict inclusion `P ⊂ DTIME(n^{log₂ n})`, sorry-free | RESOLVED |
| P5c | BPP = P ⇒ BPP has a complete problem | `exists_BPPHard_mem_BPP_PTM_of_eq_P` (BPPEqP.lean:85), with `BPPHard L := ∀ L' ∈ BPP_PTM, L' ≤ₚ L` | The witness `{ε}` is in BPP, and every BPP = P language Karp-reduces to it. This is the book's "since P does" | RESOLVED |
| P6 | (no problem) | | | — |
| P7 | NOT_FORMALIZED not exhaustive | New section "Results the chapter mentions but attributes to other chapters or the literature" with 8 rows: NC matching, #P-completeness, Valiant–Vazirani, deterministic-logspace UPATH, AKS, quantum factoring, derandomization (Ch. 19–20), and [Can96, RS95] / BPP/1 / promise problems / PP | All round-1 items are listed | RESOLVED (but see R1) |
| P8 | Draft numbering and false "Erratum" | Retagged in Classes, Adleman, SipserGacs, PolyTimeModel and ErrorReduction. The "Erratum" is replaced by an accurate Hoeffding-vs-Chernoff deviation note (ErrorReduction.lean:55–68). The Classes.lean:66–69 future-work note is fixed | See §3. No draft numbering remains | RESOLVED |
| P9 | Ex 7.11(b)(a) ℚ-only | `isStationary_real_iff_eq_uniform` (RandomWalkMixing.lean:441), for `p : V → ℝ` with `∑ p = 1` and no nonnegativity needed (so stronger); documented at :38–40 and :55 | | RESOLVED |
| P10 | Stale SURVEY rows, missing U11/U17 | SURVEY row 15 now cites `PITLang_le_ZEROP`. Row 50 now cites `BPL_error_reduction` / `RL_error_reduction`. Row 30's line numbers are correct (`Classes.lean:1180`). CRITIQUE_LOG has `## U11` (:238) and `## U17` (:241) | | RESOLVED (but see R2) |

## 2. Independent re-walk of the printed chapter

The rows below give the verdict for every chapter item. They are unchanged from round 1 except
where marked. Round-1 notes still apply where they are not repeated here.

| Item | Lean name(s) | Verdict |
|---|---|---|
| Intro (pp.123–124): forward references to Ch. 9, 20, 21, 8, 11 | — | EXCLUSION-OK (no claims; derandomization row in NOT_FORMALIZED) |
| Footnote 1 (name "BPP") | — | EXCLUSION-OK (terminology) |
| Def 7.1 PTM, runs in T(n); Pr = fraction of branches | `FinNDTM.RunsInTime`, `outputProb` | OK |
| Def 7.2 BPTIME, BPP | `BPDecidesInTime`, `BPTIME`, `BPP_PTM` | OK |
| **p.125: "2/3 … can be replaced with any other constant greater than half without changing the classes BPTIME(T(n)) and BPP"** | BPP only: `BPP_PTMWith_const_eq_BPP_PTM` | **EXCLUSION-NOT-OK (new, R1).** The BPTIME(T(n)) half is neither formalized nor listed (see §4) |
| p.125: unfair coins / expected polynomial time allowed | §7.4.2 and §7.4.3 rows below | OK |
| p.126 P ⊆ BPP; Def 7.3; Def 7.2 ≡ Def 7.3; BPP ⊆ EXP | `P_subset_BPP_PTM`, `InBPP`, `mem_BPP_PTM_iff`, `BPP_PTM_subset_EXP` | OK |
| p.126 BPP vs NEXP open; belief that BPP = P | — | EXCLUSION-OK (open problem / Ch. 19–20 row) |
| §7.2.1 median, FindKthElement, Claim 7.4; footnote 2 | `findKthElement_correct`, `maxExpectedComparisons_le` | OK / EXCLUSION-OK |
| §7.2.2 PRIMES, QR_N, three facts, Solovay–Strassen PRIMES ∈ coRP ⊆ BPP; constant-repetition amplification | `PrimalityMath`, `Primality`, `Jacobi` declarations as in round 1; amplification via Ex 7.4 | OK |
| Footnotes 3, 4; AKS; factoring (Ch. 10) | — | EXCLUSION-OK (listed now) |
| §7.2.3 algebraic circuits, ZEROP, PIT ≤ ZEROP | `AlgCircuit`, `ZEROP`, `PITLang_le_ZEROP` | OK |
| p.129 ∏(1+xᵢ) example | `card_support_toMvPolynomial_prodOnePlus` etc. | **OK (was MISSING)** |
| Lemma 7.5; degree ≤ 2^m; naive test; fingerprinting; ZEROP ∈ coRP | `schwartz_zippel`, `totalDegree_toMvPolynomial_le`, `abs_eval_le_pow`, `prob_eval_ne_zero`, `fingerprint`, `ZEROP_mem_coRP_PTM` | OK |
| §7.2.4 det(X) ≢ 0 ⇔ PM; Lovász's test | `det_edmondsMatrix_ne_zero_iff`, `lovasz_test`, `BipartitePerfectMatching_mem_RP_PTM` | OK |
| p.131 NC implementation (Ex 6.16) | — | **EXCLUSION-OK (now listed)** |
| Def 7.6 RTIME/RP; RP ⊆ NP; coRP | `RTIME`, `RP_PTM`, `RP_PTM_subset_NP`, `coRP_PTM` | OK |
| T_{M,x}, expected time; Def 7.7 ZTIME/ZPP; Thm 7.8 | `ExpTimeLe`, `ZTIME`, `ZPP_PTM`, `ZPP_PTM_eq_RP_PTM_inter_coRP_PTM` | OK |
| RP, coRP ⊆ BPP | `RP_PTM_subset_BPP_PTM`, `coRP_PTM_subset_BPP_PTM` | OK |
| §7.4.1 "any constant larger than 1/2" | `BPP_PTMWith_const_eq_BPP_PTM` | **OK (new)** |
| Lemma 7.9 | `BPP_PTMWith_weakAdv_eq_BPP_PTM`, `inBPPWeak_polyTimeModel_iff_inBPP` | **OK (was UNFAITHFUL)** |
| Thm 7.10 | `BPP_PTMWith_error_reduction`, `bpp_error_reduction_polyTime`, `majority_error_le` | **OK (was UNFAITHFUL)** |
| p.133 RP/coRP error reduction, constants < 1/2 (Ex 7.4) | `RP_PTMWith_error_reduction`, `inRPWeak_iff_inRP` | OK |
| p.133 O(m+k)-coin repetition (Ch. 21) | — | EXCLUSION-OK (listed) |
| §7.4.2 expected ≡ worst-case for BPTIME and RTIME | `haltProb_le_truncate`, `BPP_ExpPTM_eq_BPP_PTM`, `RP_ExpPTM_eq_RP_PTM`, `coRP_ExpPTM_eq_coRP_PTM` | **OK (RTIME was MISSING)**. Proved at the level of the polynomial classes, which is recorded in ZPPEquiv.lean:17 and RPExpected.lean:18 |
| §7.4.3 ρ-coin setting; Note 7.11; Lemma 7.12; Lemma 7.13 | `biasedBPP`, `exists_sample_count`, `rhoCoinRun` family, `vonNeumann_*` | OK (coin-level Lemma 7.12, recorded divergence; unchanged from round 1) |
| p.135 weak random sources (Ch. 21) | — | EXCLUSION-OK |
| p.135 P ⊆ BPP ⊆ P/poly; NP = P ⇒ BPP = P | `BPP_PTM_subset_PPoly`, `BPP_PTM_eq_P_of_P_eq_NP` | OK |
| p.135 BPP = P ⇒ BPP ⊊ DTIME(n^{log n}) | `BPP_PTM_ssubset_DTIME_pow_log_of_eq_P` | **OK (was EXCLUSION-NOT-OK)** |
| §7.5.1 3SAT ∈ BPP ⇒ PH collapses; Thm 7.14 | `PH_eq_SigmaP_two_of_SAT3_mem_BPP_PTM`, `adleman_polyTime` | OK |
| BPP = coBPP; Thm 7.15; Claims 1–2 | `compl_mem_BPP_PTM`, `BPP_PTM_subset_SigmaP_two_inter_PiP_two`, `sipser_gacs` | OK |
| §7.5.3 BPTIME property undecidable | — | EXCLUSION-OK (listed) |
| §7.5.3 ⟨M,x,1ᵗ⟩ language BPP-hard / #P-complete | `probAccept_bppHard` / — | OK / EXCLUSION-OK (now listed) |
| §7.5.3 BPP = P ⇒ complete problem | `exists_BPPHard_mem_BPP_PTM_of_eq_P` | **OK (was EXCLUSION-NOT-OK)** |
| §7.5.3 BPTIME hierarchy open | — | EXCLUSION-OK (open) |
| Def 7.16; "not transitive"; C ∈ BPP, B ≤ᵣ C ⇒ B ∈ BPP; Def 7.17 | `RandReducible`, `InBPP.of_randReducible`, `BPNP` | OK |
| Valiant–Vazirani (Ch. 17) | — | EXCLUSION-OK (listed) |
| §7.7 space; Def 7.18; log-space error reduction; RL ⊆ NL ⊆ P | `UsesSpace`, `BPL`, `RL`, `BPL_error_reduction`, `RL_subset_P` | OK |
| UPATH; Thm 7.19; 10n⁴ / 3/4 | `UPATH_mem_RL`, `hitTime_le_ten_mul_pow_four`, `three_quarters_le_hitProb` | OK |
| Deterministic logspace UPATH (§21.4); BPL ⊆ SPACE(log^{3/2}); footnote 7 | — | EXCLUSION-OK (all listed) |
| "What have we learned" | as above | OK |
| Notes: BP·P = BPP | `BPdot_P_eq_BPP_PTM` | **OK (was EXCLUSION-NOT-OK)** |
| Notes: Can96/RS95, BPP/1, promise problems, PP, historical remarks | — | EXCLUSION-OK (now listed / historical) |
| Ex 7.1–7.10, 7.11(a), (b), (c), (e) | as in round 1 | OK |
| Ex 7.11(b)(a) | `isStationary_iff_eq_uniform`, `isStationary_real_iff_eq_uniform` | **OK (was minor)** |
| Ex 7.11(d) | `hitTime_le_hundred_mul`, `missProb_thousand_mul_pow_three_le` | **OK (was UNFAITHFUL)** |

Not counted as gaps: the class-level consequence of §7.4.3 ("a ρ-coin gives no new power if ρ is
efficiently computable", that is `biasedBPP ρ ⊆ BPP`) is the book's informal reading of
Lemma 7.12. Round 1 accepted Lemma 7.12 at the coin level with the divergence recorded, and I
keep that verdict.

## 3. Citation-tag spot check (`[AB09, …]` in `Randomized/*.lean`)

I extracted every numbered tag. Chapter-7 tags in use: Def 7.1, 7.2, 7.3, 7.6, 7.7, 7.16,
7.17, 7.18; Claim 7.4; Lemma 7.5, 7.9, 7.12, 7.13; Thm 7.8, 7.10, 7.14, 7.15, 7.19; Note 7.11;
Exercises 7.1–7.11. Each matches the printed numbering, and the objects tagged are the right
ones: Def 7.3 for the certificate BPP, 7.14 for Adleman, 7.15 for Sipser–Gács, Thm 7.10 with
Cor A.15 in ErrorReduction. None of `Def 7.4`, `Thm 7.17`, `Thm 7.18` or `Cor 7.11` remains
anywhere in `Randomized/`, `SpaceComplexity/Machines/` or `ClassP/BinaryArith/`. Tags to other
chapters (Def 2.7, Thm 3.1, Def 5.3, Thm 5.4, Def 6.5, Thm 6.6, Thm 6.19, Lemma A.7, Cor A.15)
are consistent with the printed edition.

## 4. Problems found (round 2)

- **R1 — p.125: constant-robustness of BPTIME(T(n)) is neither formalized nor listed.** The
  book says (p.125) that "the constant 2/3 is arbitrary in the sense that it can be replaced
  with any other constant greater than half without changing the classes BPTIME(T(n)) and
  BPP". The repo proves this only for BPP (`BPP_PTMWith_const_eq_BPP_PTM`). No
  `BPTIME`-with-threshold class or statement exists, and NOT_FORMALIZED.md has no row for it.
  The exclusion would be legitimate: it is a preview of §7.4, which proves only the BPP form,
  and nothing depends on it. By the round-1 standard (P7), however, an unlisted exclusion is not
  acceptable. **Needed:** either prove it, e.g. `BPTIME`-with-threshold `ρ` equals
  `BPTIME T` for constant `ρ ∈ (1/2, 1)` (with `O(T)` overhead, and `T(n) ≥ n` if the
  repetition machine needs it), or add a NOT_FORMALIZED row. The row should say that
  constant-threshold independence is formalized at the BPP level only, and that §7.4.2 is
  likewise formalized at the level of the polynomial classes.
- **R2 — SURVEY row G2 wrong namespace (documentation).** It cites
  `Complexity.P_ssubset_DTIME_pow_log`; the declaration is `Randomized.P_ssubset_DTIME_pow_log`.
- Lint noise, not a grading issue: the build log shows unused-simp-argument warnings in
  pre-existing files, e.g. `TuringMachine/Build/Loop.lean:2904`.

## 5. Axiom probe

Probe `TCSlib/Complexity/Randomized/Scratch_Grader2.lean`, built only through `lb.sh`
(log `scratchpad/ch7/logs/build-172956-37070.log`, BUILD EXIT 0). I have since deleted the
probe. Results of `#print axioms`:
`Randomized.BPP_PTMWith_error_reduction`, `Randomized.BPP_PTMWith_weakAdv_eq_BPP_PTM`,
`Randomized.BPP_PTMWith_const_eq_BPP_PTM`, `Randomized.mem_BPP_PTMWith_iff`,
`Randomized.mem_BPP_PTM_iff`, `Randomized.bpp_error_reduction_polyTime`,
`Randomized.RP_ExpPTM_eq_RP_PTM`, `Randomized.coRP_ExpPTM_eq_coRP_PTM`,
`Randomized.BPdot_P_eq_BPP_PTM`, `Randomized.BPdot_NP_eq_BPNP`,
`Randomized.RegularMultigraph.hitTime_le_hundred_mul`,
`Randomized.RegularMultigraph.missProb_thousand_mul_pow_three_le`,
`Randomized.RegularMultigraph.isStationary_real_iff_eq_uniform`,
`Randomized.AlgCircuit.card_support_toMvPolynomial_prodOnePlus`,
`Randomized.P_ssubset_DTIME_pow_log`, `Randomized.exists_BPPHard_mem_BPP_PTM_of_eq_P` and
`Randomized.BPP_PTM_ssubset_DTIME_pow_log_of_eq_P` all depend only on
`[propext, Classical.choice, Quot.sound]`. `Randomized.AlgCircuit.countP_isOp_prodOnePlus`
depends on `[propext]` only. No `sorryAx` and no custom axioms.

GRADE: INCOMPLETE
1. R1 — p.125: prove that BPTIME(T(n)) does not depend on the constant threshold in (1/2, 1), or add a NOT_FORMALIZED.md row saying that constant-threshold independence (p.125) is formalized at the BPP level only. That row should also note that §7.4.2 is formalized at the level of the polynomial classes.
2. R2 — SURVEY row G2: `Complexity.P_ssubset_DTIME_pow_log` → `Randomized.P_ssubset_DTIME_pow_log`.
