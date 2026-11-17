<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassOracle/Classes.lean :: Complexity.compl_mem_POracle -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Complement Closure of Polynomial Oracle Time

**Claim.** If a binary language is decidable in polynomial time by a finite oracle Turing machine with oracle $O$, then its complement is also decidable in polynomial time with the same oracle.

**Proof.** Choose an exponent and oracle machine witnessing that $L$ belongs to $\mathrm{POracle}(O)$. Replace the machine by the machine `negOut M`, which has the same running time and oracle behavior and complements its Boolean output. The run correspondence ( `Complexity.negOut_runFrom`) identifies its run from the negated initial configuration with the negation of the original run. Thus it halts whenever the original machine does. For each input $x$, the original output is the indicator of membership in $L$; negating that bit gives the indicator of membership in $L^c$, whether $x$ lies in $L$ or not. The same exponent and time bound therefore witness $L^c\in\mathrm{POracle}(O)$.

**Key facts.** `Complexity.negOut_runFrom`.
