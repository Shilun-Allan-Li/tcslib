<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter09/KKLBribery.lean :: FABL.exercise9_25_singleton_equalities -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Singleton influence identities

**Claim.** For a Boolean function and coordinate $i$, the pivotal probability equals the coalitional influence of $\{i\}$, and that influence is twice the coalitional influence toward either output.

**Proof.** The singleton coalitional influence equals the coordinate's pivotal probability, by the singleton identity `coalitionalInfluence_singleton`. For either output $b\in\{1,-1\}$, the singleton influence toward $b$ equals half the pivotal probability, by `coalitionalInfluenceToward_singleton`. Substituting these identities gives both asserted equalities; the remaining step is the elementary rearrangement of the factor of two.

**Key facts.** `FABL.coalitionalInfluence_singleton`, `FABL.coalitionalInfluenceToward_singleton`.
