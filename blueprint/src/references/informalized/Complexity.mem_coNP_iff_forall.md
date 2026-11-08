<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassNP/CoNP.lean :: Complexity.mem_coNP_iff_forall -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Universal-certificate characterization of coNP

**Claim.** A language lies in coNP exactly when membership can be characterized by every string of a specified polynomial length producing, by concatenation with the input, a member of a polynomial-time language.

**Proof.** If $L$ is in coNP, its complement has an NP characterization: for each $x$, nonmembership in $L$ is equivalent to the existence of a witness $u$ of the specified length for which $xu$ lies in a polynomial-time language $V$. Replace $V$ by its complement, which is still in polynomial time (compl_mem_P). Negating the existential condition says that every witness of that length has $xu$ outside the original $V$, equivalently inside the complemented language. This is the claimed universal characterization.

Conversely, suppose membership in $L$ is equivalent to every prescribed-length $u$ giving $xu\in V$, where $V$ is polynomial-time decidable. The negation says that nonmembership is equivalent to the existence of a prescribed-length $u$ with $xu\notin V$. Since the complement of $V$ is also in polynomial time (compl_mem_P), this is an NP witness characterization for $L^c$, hence $L$ is in coNP.

**Key facts.** `Complexity.compl_mem_P`.
