<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassPSPACE/TQBF.lean :: Complexity.codecGate_cnf -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Existence of a gate CNF

**Claim.** There exists a CNF formula of cost at most $2^{3k+7}(3k+8)$ whose evaluation under every assignment equals the gate value on the prescribed wired assignment.

**Proof.** Apply the general local Boolean-function CNF construction (`Complexity.codecLocalCheck`) to the finite set of gate ports. The wiring sends each enumerated port to its corresponding encoded variable, and the Boolean function on port assignments is the gate value. The construction gives a CNF whose cost is at most $2^m(m+1)$, where $m$ is the number of ports, and whose evaluation agrees with that Boolean function after wiring. The port-count identity (`Complexity.codecPort_card`) gives $m=3k+7$, yielding the asserted bound. Reindexing the enumerated ports through the finite equivalence preserves the wiring and evaluation identity; the resulting expression is exactly the assignment obtained by composing with the prescribed port wiring.

**Key facts.** `Complexity.codecLocalCheck`, `Complexity.codecPort_card`.
