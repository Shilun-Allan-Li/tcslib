<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/UHaltMachine.lean :: Complexity.HALT_computable_of_decidesInTime_UHALT -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Computability of the Halting Function

**Claim.** If a finite-state Boolean machine decides the unary language associated with the halting function within time bound $T$, then some finite-state Boolean machine computes the one-bit output $[\mathrm{HALT}_c(s)]$ on each input $s$.

**Proof.** First construct a machine that, on input $s$, produces the all-true word of length $\operatorname{numOfString}(s)$, with a time bound (Turing.codePrim_machine, using Complexity.primrec_replicate_numOfString). Compose this machine with the given decider $M$ using the partial-composition construction (Turing.FinTM.exists_comp_partial), obtaining a machine $D$ that runs $M$ on that all-true word and returns its output. By the definition of deciding, $M$ outputs the indicator of membership in $\mathrm{UHALT}_c$ on the generated word. The characterization of that word's membership (Complexity.replicate_numOfString_mem_UHALT_iff) says precisely that this indicator is $\mathrm{HALT}_c(s)$. Thus the composed machine outputs the required one-bit list for every $s$, proving computability.

**Key facts.** `Turing.codePrim_machine`, `Complexity.primrec_replicate_numOfString`, `Turing.FinTM.exists_comp_partial`, `Complexity.replicate_numOfString_mem_UHALT_iff`.
