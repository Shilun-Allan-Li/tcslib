<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/MeyerVerifier.lean :: Complexity.Meyer.badLang_mem_P -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Polynomial Time for the Bad Language

**Claim.** For any natural numbers $C_w,c_w$ and finite-state Turing machine $M$ with Boolean alphabet, the language defined by the bad-valuation predicate belongs to polynomial time.

**Proof.** Each atom of a valuation has a polynomial-time language of inputs on which it evaluates to true, by the polynomial-time decidability of each atom ($\texttt{evalAtom\_mem\_P}$). The bad-valuation predicate is a Boolean function of the finitely many atom values. The closure theorem for polynomial time under Boolean combinations of finitely many polynomial-time predicates therefore gives polynomial-time decidability of the language defined by that predicate ($\texttt{mem\_P\_of\_atoms}$).

**Key facts.** `Complexity.Meyer.evalAtom_mem_P`, `Complexity.mem_P_of_atoms`.
