<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/BLR/LowDegree.lean :: LowDegreeTest.one_mem_ReedMuller -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Constant function is low degree

**Claim.** For every degree bound $d$, the constant-true function belongs to the Reed–Muller code $\mathrm{RM}(d,n)$.

**Proof.** It suffices to show that every $(d+1)$-fold Gowers product of the constant-true function's sign lift is $1$. Induct on $d$, allowing the base point to vary. At degree bound zero, the sign lift is constantly $1$, so the claim follows immediately. At the successor step, the recursive Gowers product is the product of two lower-order products: one based at $x$, and the other based at $x$ XORed with the last direction. Both equal $1$ by the induction hypothesis, so their product is $1$. This proves the defining degree condition, which is membership in the Reed–Muller code.
