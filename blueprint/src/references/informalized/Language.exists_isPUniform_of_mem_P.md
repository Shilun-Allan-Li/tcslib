<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/UniformTableau.lean :: Language.exists_isPUniform_of_mem_P -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Polynomial-Time-Uniform Circuits for Polynomial Time

**Claim.** Every Boolean-string language decidable in polynomial time has a family of fan-in-two Boolean circuits whose descriptions are computable in polynomial time from the unary input length and whose accepted language is exactly the given language.

**Proof.** The polynomial-time characterization supplies natural numbers $C,d$ and a machine $M$ deciding the language within time $C(n+1)^d$ ( `Complexity.mem_P_iff`). Tabulate this machine to obtain a circuit family. The tabulation theorem makes its circuit descriptions polynomial-time computable from unary input lengths ( `Complexity.tabFamily_isPUniform`) and gives fan-in at most two ( `Complexity.tabFamily_hasFaninTwo`). The family-language correctness theorem shows that the resulting circuits recognize precisely the language decided by $M$ ( `Complexity.tabFamily_language`).

**Key facts.** `Complexity.mem_P_iff`, `Complexity.tabFamily_isPUniform`, `Complexity.tabFamily_hasFaninTwo`, `Complexity.tabFamily_language`.
