<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter07/UniqueGamesReduction.lean :: FABL.RawCSPInstance.value_le_optimum -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Every Assignment Is Bounded by the Optimum

**Claim.** For a raw instance with finite variable set and finite nonempty domain, every assignment’s value is at most the optimum value.

**Proof.** The optimum is attained by a maximizing assignment among the finitely many assignments. By the defining maximality of that choice (`Finite.exists_max`), the value of any assignment is no greater than the value of the maximizing assignment, which is the optimum.
