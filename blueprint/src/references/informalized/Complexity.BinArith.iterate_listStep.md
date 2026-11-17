<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassP/BinaryArith/Words.lean :: Complexity.BinArith.iterate_listStep -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Iteration of the list step

**Claim.** Applying the list step $i$ times to the pair encoding $\langle q,w\rangle$ gives $\langle q,\pi_2^{[i]}(w)\rangle$, where $\pi_2$ is the total second projection.

**Proof.** Induct on $i$. At zero, both sides are the original encoding. For the successor step, first use the induction hypothesis, then apply the list step once more. By its definition, this step keeps the first component and applies the total second projection to the second component. Consequently the first component remains $q$, while the second becomes one further iterate of $\pi_2$, as claimed.
