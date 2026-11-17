<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter06/Constructions/ExecutableFiniteFields.lean :: FABL.binaryHasProperFactor_eq_true_iff -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Characterization of proper polynomial factors

**Claim.** For positive $\ell$ and a coefficient vector $m$, the finite search for a proper factor returns true exactly when there are coefficient vectors $a,b$ whose low-degree polynomials are each different from $1$ and whose product is the monic polynomial specified by $m$.

**Proof.** The search ranges over all binary coefficient vectors $a$ and, for each one, all binary coefficient vectors $b$. Every such vector occurs in the enumerated list. For a given pair, the witness test returns true exactly when both associated low-degree polynomials differ from $1$ and their product equals the specified monic polynomial. Thus a successful pair in the finite search is precisely an existential pair satisfying those conditions, in either direction.

**Key facts.** `FABL.mem_allBinaryVectors`, `FABL.binaryProperFactorWitness_eq_true_iff`.
