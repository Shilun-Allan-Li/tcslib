<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/SavitchARM/Run.lean :: Complexity.LogProg.SavitchARM.cp_run -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Register Copy Loop

**Claim.** Under the stated bounds, zero scratch register, and bound on the sum of the source and destination values, the copy loop reaches its exit with the destination increased by the source value, all other registers unchanged, and the answer unset; every earlier configuration satisfies the guard.

**Proof.** Apply the general copy-loop result (`copy_run`) to the seven instruction phases defining the routine at site $k$. The register-disjointness fact (`cp_ne`) supplies that source, destination, and scratch registers are pairwise distinct. Unfolding the machine's instruction definition at those phases identifies the loop's zero test, source decrement, destination increment, scratch increment, cleanup test and decrement, and source restoration with exactly the instruction pattern required by `copy_run`. The register bounds follow from `st.Bd` via `Bd.toV`, and the sum bound is the stated hypothesis. Thus `copy_run` gives the guarded finite execution and its asserted final register vector.

**Key facts.** `Complexity.LogProg.SavitchARM.cp_ne`, `Complexity.LogProg.SavitchARM.St.Bd.toV`, `Complexity.LogProg.copy_run`.
