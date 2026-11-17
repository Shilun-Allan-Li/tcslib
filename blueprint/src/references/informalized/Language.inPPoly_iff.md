<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/PPoly.lean :: Language.inPPoly_iff -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Polynomial-Size Circuit Characterization

**Claim.** A Boolean language is recognized by a family of fan-in-two Boolean circuits of polynomial size exactly when there is such a family whose recognized language is precisely that language.

**Proof.** Unpack membership in the polynomial-size circuit class: there are natural numbers $a,k$ and a circuit family $C$ such that every circuit has size at most $a(n+1)^k$, the family has fan-in at most two, and its language equals $L$. The same family, bounds, and gate property give the stated existential characterization. Conversely, the data in that characterization satisfy the definition of membership in the polynomial-size class, so they establish it directly.
