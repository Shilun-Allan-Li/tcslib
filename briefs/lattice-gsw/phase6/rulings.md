# GSW phase 6 · rulings P6-Q1 to P6-Q13 and the location ruling (Seyoon, 2026-11-16)

Seyoon answered the thirteen questions in [questions.md](questions.md): eight as recommended and five changed (Q3, Q4,
Q9, Q10, Q11). He then added a location ruling. `plan-section.md` is revised to match before the statement phase.

| # | Ruling | |
|---|---|---|
| P6-Q1 | **One phase 6** on the BV14 route to pure FHE at a polynomial ratio; it merges the roadmap's phases 6 and 7. **Two statement gates:** **Gate 45** covers the complexity layer (6a: branching programs, Barrington, formula arithmetic, NAND conversion), and **Gate 46** covers the cryptography (6b). The quasi-polynomial instantiation is dropped. Gates 42–44 are taken, so 45 and 46 replace the plan's provisional 42 and 43. | as recommended |
| P6-Q2 | Barrington's input model is **`BoolCircuit.TreeCircuit n`**, AND/OR formulas over literals with polarity, which is Bar89's model. `DAGCircuit` is reached through the depth-preserving `DAGCircuit.toTree`. | as recommended |
| P6-Q3 | **Both directions now: BWBP = NC¹.** This covers Bar89 Thm 1 with Lemmas 1–3, the `DAGCircuit` corollary (length ≤ `4^depth`), NC¹ ⊆ polynomial-length width-5 PBPs, **and** Thm 2 (BWBP ⊆ NC¹) with its composition-tree circuit. The plan's estimate is about +300–500 lines; FHE does not use Thm 2. | **changed** (was: Thm 1 and NC¹ ⊆ PBP only) |
| P6-Q4 | **The general branching-program model of Bar89 §1**, with instructions mapping `[w] → [w]`, plus an **`IsPermutation`** predicate. It is otherwise as proposed: instructions `⟨var, f0, f1⟩` in BV14's order (`f0` when the bit is `0`), with Bar89's order disclosed; `yield` in program order; and the public host `evalWith`, generic in the selector and value type, with the step-indexed relational lemma `evalWith_rel`. It is registered in `ComputationalModels.lean` and `machine-library-design.md` §14. Boolean semantics and GSW are its consumers. | **changed** (was: permutation programs only) |
| P6-Q5 | The decryption formula is built in a **new shared formula-arithmetic layer** over `TreeCircuit`: De Morgan negation, substitution, `xor3`/`maj3`, the carry-save (3:2) reduction, carry-out comparison with constants, and the modular interval sum. | as recommended |
| P6-Q6 | The layer goes in **`Complexity/CircuitComplexity/FormulaArith/{Combinators,CarrySave,Compare,ModSum}.lean`**, as the first rows of a circuit/formula gadget registry. A small owner-side PR promotes the private `TreeNCAC.combine` to public. `Parity.lean`'s private dual-rail XOR is re-pointed later, on the dedup queue. At statement prep, check `Complexity/FormulaKit/Gate.lean` (CNF truth-table gates) for reuse; it is a different formula model. | as recommended |
| P6-Q7 | **`decode_iff_mem_Ico`**, with explicit `lo` and `hi`, is a published reader in the owner file `LWE/BitEncoding.lean`, added by a small owner-side PR. | as recommended |
| P6-Q8 | The evaluation key is **public-key GSW encryptions, under the user's own `pk`, of the `N` bits of `G⁻¹(t)` with `t = (−s, 1)`**. This is BV11 Def 3.8. There is one `GSW.Parameters` record, the evaluation-key noise is `m·B`, and decryption becomes a binary subset sum with public constants `Gᵀc`. | as recommended |
| P6-Q9 | **Bootstrapping is NAND only**, literally BV14 Def 2.13. Circuits are first converted to NAND form by a **new conversion with its own lemmas** (semantics, size and depth). | **changed** (was: every `DAGCircuit` gate) |
| P6-Q10 | **The concrete statements, and now also the asymptotic forms:** an asymptotic `WeakCircularSecure` family predicate and an asymptotic IND-CPA theorem, conditional on an explicit reduction-efficiency hypothesis. Concrete as in phase 5: `WeakCircularSecure P χ ε` bounds every distinguisher's advantage on `(pk, evk, Enc(μ))`, and the `evk`-free view inherits phase 5's DLWE bound. Compactness holds by typing and is stated in the docstring. | **changed** (was: concrete only, asymptotic later) |
| P6-Q11 | **The full leveled scheme now:** `L+1` keys, correctness, and IND-CPA by a hybrid over the keys from DLWE (BV14 Thm 2.14 first part; BV11 Thm 3.1). The plan's estimate is about +400–700 lines. It is the FHE statement that needs no circular-security assumption. The key-switching form of the bootstrapping lemma remains its basis. | **changed** (was: key-switching lemma only) |
| P6-Q12 | **Explicit `decDepth P` and `bootNoise P β`** in the correctness theorems, with closed-form bounds proved separately. The ruled `RatioBounded F B p` goes in a new `LWE/Ratio.lean`, with a family theorem carrying an explicit `PolyExpr` `pBoot`. | as recommended |
| P6-Q13 | **`barrington` is computable**: Lemma 1's conjugator is explicit (`θ(σᵏ 0) = τᵏ 0` for five-cycles), so `fheEval` is computable. | as recommended |

## Location ruling (Seyoon, 2026-11-16, after Q1–Q13)

**Branching programs, Barrington and the NAND conversion go in `Complexity/`.** In Seyoon's words, these are general
facts about models of computation and will be usable elsewhere. The 6b (GSW) modules only consume them.

The maintainer proposes these homes; the revised plan section confirms them:
- **Branching programs.** The facade is `Complexity/BranchingPrograms.lean`, with:
  - `Complexity/BranchingPrograms/Defs.lean`: the general model, `IsPermutation` and `yield`;
  - `Complexity/BranchingPrograms/Eval.lean`: the host `evalWith` and `evalWith_rel`;
  - `Complexity/BranchingPrograms/Barrington.lean`: Thm 1, Lemmas 1–3 and the NC¹ corollary;
  - `Complexity/BranchingPrograms/BarringtonConverse.lean`: Thm 2.

  The model is registered in `ComputationalModels.lean`.
- **NAND conversion:** `Complexity/CircuitComplexity/NANDForm.lean`, beside `DAGTransform.lean`.
- **Formula arithmetic:** `Complexity/CircuitComplexity/FormulaArith/`, per P6-Q6.

## Effect on scope
The changed rulings enlarge the phase:
- Thm 2 adds about 300–500 lines (P6-Q3), and the leveled scheme about 400–700 (P6-Q11), per the plan's estimates.
- The general BP model (P6-Q4), the NAND conversion (P6-Q9) and the asymptotic forms (P6-Q10) are new items. The revised
  plan section estimates them.
- Gate 45 (6a) now covers the BP model, Barrington in both directions, formula arithmetic and the NAND conversion.

## Rulings P6-Q14 to P6-Q19 (Seyoon, 2026-11-16, on plan section r2)

| # | Ruling | |
|---|---|---|
| P6-Q14 | **Consecutive keys plus a layering conversion.** Each `evk_d` encrypts the bits of `s_{d−1}`, giving `N·L` ciphertexts (the textbook chain). Circuits are made **layered** by a new generic conversion under `Complexity/`, which pads uneven paths with double-NAND identity chains, with care for odd gaps. It is part of 6a and Gate 45; estimated +150–250 lines. | **changed** (was: keys by depth, evk to every lower key) |
| P6-Q15 | **Per-distinguisher concrete form:** `WeakCircularSecure P χ D ε := distAdv (fheView … false) (fheView … true) D ≤ ε`. The asymptotic `WeakCircularSecureFamily` (NUPPT, negligible) is the headline hypothesis, faithful to BV11 Def 3.8. This corrects P6-Q10's concrete form, which, quantified over every function, holds only for `ε` near 1. | as recommended |
| P6-Q16 | **NAND form is a predicate on `DAGCircuit`:** every gate is a `¬` gate (negated conjunction) of fan-in ≤ 2. The conversion is an instance of `DAGCircuit.rewrite`, within its budget, with depth factor 2. Bootstrapping pads fan-in 1 to `(a, a)` and fan-in 0 to `(G, G)`. Disclosed: NAND-form circuits are not `IsWellFormed`. | as recommended |
| P6-Q17 | **Registry rows:** `BranchingProgram.evalWith` as H18; `runWith`/`runWith_rel` recorded as H19 and `DAGCircuit.rewrite` as H20. Gate 45 audits their contracts. Records only. | as recommended |
| P6-Q18 | **Thm 2's circuit is a `TreeCircuit` formula** with fan-in 2, mirroring Bar89's three sections. It reaches `DAGCircuit` and `Language.InNC 1` through `Language.InTreeNC.inNC`; its size `l^{O(log w)}` is polynomial for fixed `w`. | as recommended |
| P6-Q19 | **Ingest Gen09:** the leveled-bootstrapping passage of Gentry's thesis or his STOC 2009 paper (the key chain and its security hybrid), which is cited for the leveled scheme. **Needs the PDF from Seyoon.** Until then the 6b leveled-scheme statements wait; 6a is unaffected. | **changed** (was: no new ingest) |

Effect: 6a gains the layering conversion (P6-Q14). 6b's leveled scheme uses the consecutive chain over layered circuits and cites
Gen09 once ingested. The plan section is updated to r3 accordingly.
