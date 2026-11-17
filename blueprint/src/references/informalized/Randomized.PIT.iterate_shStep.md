<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Randomized/ZeroPReduce.lean :: Randomized.PIT.iterate_shStep -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Iteration of gate shifting

**Claim.** If the gate list has length at most $T$, then after $T$ shifts the encoded state contains the unchanged unary counter, the terminal marker, and the output followed by the encodings of the gates with their arithmetic references shifted by $m$.

**Proof.** Use induction on the gate list, with the number of steps allowed to exceed its length. If the list is empty, the state is fixed by the shifting step (`shStep_nil`), so any number of iterations leaves the counter, terminal marker, and output in place. For a nonempty list, the length bound ensures at least one step; write the step count as $T'+1$. The first step removes the leading gate from the work list and appends its shifted encoding to the output (`shStep_cons`). The remaining list has length at most $T'$, so the induction hypothesis shifts its gates in the remaining steps. Combining the two output extensions gives the original output followed by the shifted encodings of all gates in order.

**Key facts.** `Randomized.PIT.shStep_nil`, `Randomized.PIT.shStep_cons`.
