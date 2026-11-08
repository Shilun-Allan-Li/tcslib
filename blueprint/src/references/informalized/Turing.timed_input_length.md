<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Universal.lean :: Turing.timed_input_length -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Nested Encoding Length

**Claim.** For finite Boolean words $b$, $\alpha$, and $x$, the nested pair encoding has length $4|b|+2|\alpha|+6+|x|$.

**Proof.** Apply the pair-encoding length formula twice: first, $|\langle b,\alpha\rangle|=2|b|+2+|\alpha|$; then the outer encoding has length $2|\langle b,\alpha\rangle|+2+|x|$. Substituting the first expression into the second and collecting terms gives $4|b|+2|\alpha|+6+|x|$.

**Key facts.** `Turing.universal_pair_length`.
