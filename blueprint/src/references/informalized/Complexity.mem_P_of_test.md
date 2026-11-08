<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassNP/PClosure.lean :: Complexity.mem_P_of_test -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Polynomial-Time Tests Define Languages in P

**Claim.** If the Boolean-valued test can be computed in polynomial time as a one-bit output, then the language on which it returns true belongs to $\mathsf{P}$.

**Proof.** By the characterization of $\mathsf{P}$ by polynomial-time indicator functions (`Complexity.mem_P_iff_polyTimeComputable`), it suffices to show that the test's one-bit output agrees with the indicator of the language $\{z:b(z)=\mathrm{true}\}$. For each input $z$, if $b(z)$ is true, that indicator is true and its one-bit output is $[\mathrm{true}]$; if $b(z)$ is false, the indicator is false and its one-bit output is $[\mathrm{false}]$. Thus the given polynomial-time computation is exactly the required indicator computation.

**Key facts.** `Complexity.mem_P_iff_polyTimeComputable`.
