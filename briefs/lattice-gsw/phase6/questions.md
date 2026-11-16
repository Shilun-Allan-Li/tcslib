# GSW phase 6 (bootstrapping, BV14 route): design questions for Seyoon

Each question is multiple choice, with the recommended option first and marked **(rec.)**. Section
numbers refer to `plan-section.md` in this folder. The questions are numbered P6-Q1 to P6-Q13 so
that they do not collide with the ruled phase-5 questions Q1–Q16 (`../rulings.md`), several of
which they build on: Q12 (BV14 route), Q13 (Barrington as its own complexity unit), Q15 (weak
circular security as an explicit hypothesis), Q16 (the ratio predicate) and the addendum (small-
secret LWE assumed only where used; it is not used here).

## Shape of the phase

**P6-Q1. Phase numbering and gates** (§H0, §H7)
- **A (rec.)** One phase 6 that merges the roadmap's phases 6 and 7: the BV14 route to pure FHE at
  a polynomial ratio. Two statement gates: Gate 42 for the complexity layer (6a: branching
  programs, Barrington, formula arithmetic), Gate 43 for the cryptography (6b). The quasi-polynomial
  instantiation of the old phase 6 is dropped, since the BV14 route subsumes it.
- **B** Keep the roadmap's split: phase 6 = generic bootstrapping instantiated at a quasi-polynomial
  ratio with the phase-5 depth-bounded evaluator; phase 7 = BV14. This needs the same decryption
  circuit twice in different forms.
- **C** One phase with a single gate over 6a and 6b (about 55 targets in one audit).

## Complexity layer (6a)

**P6-Q2. Barrington's input model** (§H2, §H5.2)
- **A (rec.)** `BoolCircuit.TreeCircuit n` (AND/OR formulas over polarity-carrying literals),
  which is exactly Bar89's model ("AND and OR gates with a bottom level of inputs and negated
  inputs"). `DAGCircuit` is reached through the existing `DAGCircuit.toTree` (depth-preserving).
- **B** `DAGCircuit` directly, by recursion on `depthAt`, with `¬` gates handled by complement
  (Lemma 2). Duplicates the unfolding that `toTree` already proves.
- **C** A new NAND-only formula type, matching BV14 Thm 3.5's "NAND circuit". A second circuit
  model outside the registry.

**P6-Q3. Barrington scope** (§H5.2–§H5.3)
- **A (rec.)** Bar89 Thm 1 with Lemmas 1–3, the `DAGCircuit` corollary (length `≤ 4^depth`), and
  the one-directional Corollary `NC¹ ⊆` polynomial-length 5-PBPs (ruling Q13's theorem). The
  converse (Thm 2, `BWBP ⊆ NC¹`) is recorded for later.
- **B** Both directions now (`BWBP = NC¹`): adds a composition-tree circuit for Thm 2, about
  +300–500 lines, unused by FHE.
- **C** Thm 1 for formulas only; no `DAGCircuit`/`NC¹` corollary.

**P6-Q4. The branching-program model and its host** (§H3.5, §H4)
- **A (rec.)** A root-level model type `PermBranchingProgram w n` registered in
  `ComputationalModels.lean`; instructions `⟨var, perm0, perm1⟩` in BV14's order (`perm0` when the
  bit is `0`), with the Bar89 order disclosed; `yield` in program order
  (`yield (B₁ ++ B₂) = yield B₂ * yield B₁`); and the public **host** `evalWith` (fold over
  instructions, generic in the selector and value type) with a step-indexed relational lemma
  `evalWith_rel`, registered in `machine-library-design.md` §14. Boolean semantics and GSW are its
  two consumers.
- **B** As A, but the general (non-permutation) branching-program model of Bar89 §1 (maps
  `[w] → [w]`) with an `IsPermutation` predicate. More general; the selector analysis needs
  permutations anyway.
- **C** Namespaced types under `BoolCircuit` without registration, and the fold written inside the
  GSW file. Not recommended: a private host.

**P6-Q5. How the decryption circuit is built** (§H3.2–§H3.4, §H5.4)
- **A (rec.)** A new shared **formula-arithmetic layer** over `TreeCircuit`: De Morgan negation,
  substitution, `xor3`/`maj3`, a carry-save (3:2) reduction, a carry-out comparison with constants,
  and a modular interval-sum formula. Barrington consumes the formula directly. Estimated
  730–1,110 fill lines (U4–U6).
- **B** Gate lists in `DAGCircuit` (as `Adder.lean`), then `toTree`. Reuses the DAG plumbing style
  but needs relocation/sharing ledgers that the formula route avoids; ripple-carry addition is too
  deep and cannot be reused.
- **C** No construction: state BV14 Prop 3.4 (a decryption circuit of depth `c_dec·log N` exists)
  as an explicit hypothesis of the bootstrapping theorems. Fast, but leaves the main theorem
  conditional on an unproved complexity claim.

**P6-Q6. Home of the formula layer, and the two private helpers** (§H2, §H8 item 5)
- **A (rec.)** `Complexity/CircuitComplexity/FormulaArith/{Combinators,CarrySave,Compare,ModSum}.lean`,
  as the first rows of a circuit/formula gadget registry (policy §1). Promote the private
  `TreeNCAC.combine` (balanced fan-in-2 node, depth `+⌈log₂ k⌉ + 1`) to a public declaration in
  `Combinators.lean` by a small owner-side PR (as #332 did for `DAGCircuit.lean`); re-point
  `Parity.lean`'s private dual-rail XOR to the public `neg`/`xor2` later, on the dedup queue.
- **B** Same home, but a disclosed local copy of `combine` (duplication, needs your approval and a
  payback entry).
- **C** Inside the GSW folder. Not recommended: the layer is generic complexity material.

## Cryptography layer (6b)

**P6-Q7. Where the `decode` interval lemma lives** (§H3.3, §H5.6 G4)
- **A (rec.)** A published reader in the owner file `LWE/BitEncoding.lean`:
  `decode_iff_mem_Ico` with explicit `lo`, `hi` (small owner-side PR). `decode` is that file's
  definition, so its characterization belongs beside it.
- **B** A GSW-local theorem in `DecryptFormula.lean`, reading `decode` only through `decode_eq`.
  No shared-file change; one more reader of another file's definition outside that file.
- **C** Replace the decryptor by an explicit interval test. Not recommended: it changes the audited
  phase-5 decryption.

**P6-Q8. The evaluation key** (§H3.8, §H5.7 G11)
- **A (rec.)** Public-key GSW encryptions, under the user's own `pk`, of the `N` bits of
  `G⁻¹(t)`, `t = (−s, 1)`: exactly BV11 Def 3.8's `{Enc_pk(sk[i])}_i`; one `GSW.Parameters` record;
  evaluation-key noise `m·B`. Decryption becomes a binary subset sum with public constants `Gᵀc`
  (§H3.2).
- **B** BV14's choice: batched secret-key encryptions (phase-5 unit F7, noise `B`), which saves a
  factor `m` in the ratio but needs a second parameter record (`LWE.Parameters.withSamples`) and
  the type-level Rule-10 transport that phase 5 avoided.
- **C** As A, but encrypting the `n·ℓ` bits of `s` instead of `G⁻¹(t)`; the decryption constants
  become `−2^k·c_j`, with the last coordinate as a separate constant.

**P6-Q9. Which gates are bootstrapped** (§H3.1, §H5.6 G7)
- **A (rec.)** Every gate of a fan-in-2 `DAGCircuit` (`∧`, `∨`, `¬`, constants) through its own
  augmented formula `g(Dec(C_a))`, evaluated by `runWith`. Every wire then has the same noise bound
  and the circuit model is the library's. A disclosed generalization of BV14 Def 2.13 (NAND) and
  BV11 Def 3.7 (XOR/AND).
- **B** NAND only, literally BV14 Def 2.13; circuits are first converted to NAND form (a new
  conversion with its own lemmas).
- **C** Mixed: evaluate with the phase-5 gates and bootstrap only when the noise passes a threshold.
  More efficient, much harder to state.

**P6-Q10. Security and compactness statements** (§H5.8)
- **A (rec.)** Concrete only, as in phase 5 (Q8): `WeakCircularSecure P χ ε` bounds every
  distinguisher's advantage on the FHE view `(pk, evk, Enc(μ))`; the FHE security theorem reads
  it (G14), and the `evk`-free view inherits phase 5's DLWE bound (G15). The asymptotic
  predicate comes with the `NUPPT` bridge. Compactness is by typing and stated in the docstring.
- **B** Also an asymptotic `WeakCircularSecure` family predicate and an asymptotic IND-CPA theorem
  now, conditional on an explicit reduction-efficiency hypothesis.
- **C** As A, plus an explicit compactness theorem on the encoded length of `fheEval`'s output
  (BV11 Def 3.4).

**P6-Q11. Leveled FHE without circular security** (§H9)
- **A (rec.)** Only the key-switching form of the bootstrapping lemma (G9: `evk` under `t'`
  bootstraps ciphertexts under `t`), from which leveled correctness over a key chain is a short
  later corollary; the key-chain security hybrid is deferred.
- **B** The full leveled scheme now: `L+1` keys, correctness, and IND-CPA by a hybrid over the keys
  from DLWE (BV14 Thm 2.14 first part, BV11 Thm 3.1), about +400–700 lines. The only
  assumption-free FHE statement.
- **C** Omit leveled FHE.

**P6-Q12. Form of the ratio statement** (§H5.9, §H6)
- **A (rec.)** Explicit definitions `decDepth P` and `bootNoise P β` used by the correctness
  theorems, closed-form bounds proved separately (G8, G13), the ruled `RatioBounded F B p` in a new
  `LWE/Ratio.lean`, and a family theorem with an explicit `PolyExpr` `pBoot` (G16–G17).
- **B** Only the concrete separation inequality per parameter set; no family statement.
- **C** Asymptotic `O(·)` statements. Not recommended: the library's statements are explicit.

**P6-Q13. Computability of `barrington`** (§H5.2, §H8 item 9)
- **A (rec.)** Computable: the Lemma-1 conjugator is explicit (`θ(σᵏ 0) = τᵏ 0` for five-cycles
  `σ, τ`), so `fheEval` is a computable function.
- **B** `noncomputable`, choosing `θ` from Mathlib's conjugacy of equal cycle types. Shorter; the
  FHE evaluator becomes noncomputable (harmless for correctness and security, which are the
  phase's claims).
