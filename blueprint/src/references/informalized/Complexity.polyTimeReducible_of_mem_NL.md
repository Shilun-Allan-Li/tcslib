<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/ExpTime.lean :: Complexity.polyTimeReducible_of_mem_NL -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Reduction to a Nontrivial Language

**Claim.** Let $L$ and $L'$ be languages of binary strings. If $L$ contains at least one string and omits at least one string, and $L'$ belongs to $\textsf{NL}$, then $L'$ is polynomial-time many-one reducible to $L$.

**Proof.** Because $L'$ belongs to $\textsf{NL}$ and nondeterministic log-space languages are contained in polynomial time (`NL_subset_P`), $L'$ has a polynomial-time decider (`mem_P_iff`). Thus its membership indicator is polynomial-time computable. Choose $y\in L$ and $z\notin L$, as the hypotheses permit, and define the reduction to output $y$ when the indicator accepts and $z$ otherwise. This function is polynomial-time computable by the conditional closure theorem and the polynomial-time computability of constant functions (`polyTimeComputable_ite`, `polyTimeComputable_const`). If $x\in L'$, the output is $y\in L$; if $x\notin L'$, the output is $z\notin L$. Hence $x\in L'$ exactly when its image lies in $L$, so this is a polynomial-time many-one reduction.

**Key facts.** `Complexity.NL_subset_P`, `Complexity.mem_P_iff`, `Complexity.polyTimeComputable_ite`, `Complexity.polyTimeComputable_const`.
