<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/PolyHierarchy/Collapse.lean :: Complexity.mem_PiP_two_iff_forall_exists -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Universal-Existential Characterization of $\Pi_2^P$

**Claim.** A language belongs to $\Pi_2^P$ exactly when there are polynomial bounds and a polynomial-time language such that membership is equivalent to a universal first witness followed by an existential second witness of the same prescribed length.

**Proof.** Apply the general $\Pi_i^P$ characterization (`Complexity.mem_PiP_iff`) at level $2$. Its alternating condition begins universally. Unfolding the next level of that condition gives an existential witness of the same bound, and the terminal condition is membership in the polynomial-time language. The two successive pair encodings record the input and the two witnesses, giving the displayed characterization.

**Key facts.** `Complexity.mem_PiP_iff`.
