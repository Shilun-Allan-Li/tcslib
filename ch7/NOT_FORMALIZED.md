# Chapter 7 — items deliberately not formalized

Final list after Phase 2 (U12–U16). Every exercise and every proved claim of the printed chapter is formalized; the rows below are results the book cites from the literature without proof, an informal aside, or material outside the printed chapter.

| Item | Reason |
|---|---|
| p.139 "BPL ⊆ SPACE(log^{3/2} n)" [SZ99] | Cited research result (Saks–Zhou), deferred by the book to §21.6; nothing in ch. 7 depends on it. |
| Footnote 7 (p.139): cover time `(4/27)n³ + o(n³)`, lollipop tightness [Fei95] | Cited research result; the UPATH ∈ RL argument needs only the hitting-time bound of Ex 7.11(d), which is proved. |
| §7.5.3 (p.137) "testing the BPTIME property is undecidable" | Informal aside (motivation for the absence of BPP-complete problems); nothing depends on it. Not provable for the repo's lawful-but-non-effective machine codes (a lawful scheme can make the property decidable); a faithful version needs an effective PTM code scheme, a code-level s-m-n/hardwiring map, and a clocked universal PTM — none exist in the repo (critic estimate 1300+ lines). |
| Remark p.133: error reduction with O(m+k) coins via expander walks | The book defers the proof to Ch. 21 (§21.2.5); ch. 7's own error reduction (Thm 7.10, majority of independent runs) is proved and is what every later result uses. |
| Web-draft expander appendix (`Expanders/`, incl. the intentional `walk_visits_concentration` sorry) | Not part of printed ch. 7 (printed ch. 21, §21.2.5). |

## Results the chapter mentions but attributes to other chapters or the literature (no proof in ch. 7, nothing in ch. 7 depends on them)

| Item | Where the book places it |
|---|---|
| §7.2.4 and chapter notes: Lovász's matching test can be done in NC [Lov79] | Exercise 6.16 |
| p.138: the ⟨M, x, 1ᵗ⟩ language is #P-complete | Ch. 17 (its BPP-hardness, the ch. 7 claim, is proved: `Randomized.probAccept_bppHard`) |
| §7.6: reducing SAT to instances with a unique satisfying assignment (Valiant–Vazirani) | Ch. 17 |
| §7.7: deterministic logspace algorithm for UPATH | §21.4 |
| §7.2.1 and chapter notes: PRIMES ∈ P [AKS04] | cited; ch. 7 proves PRIMES ∈ coRP (`Randomized.PRIMESBin_mem_coRP_PTM`) |
| §7.2.1: factoring is efficient on quantum computers | Ch. 10 |
| Introduction and §7.5: evidence that BPP = P (derandomization) | Ch. 19–20 |
| Chapter notes: BPP in classes weaker than Σ₂ ∩ Π₂ [Can96, RS95]; hierarchy theorems for BPP/1; promise-BPP; the class PP [Gil74] (Ch. 17) | cited research results |

