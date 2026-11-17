<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Codec/Run.lean :: Complexity.Codec.Reach.trans -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Transitivity of Bounded Reachability

**Claim.** If the codec program has a guarded run from $(l_1,v_1)$ to $(l_2,v_2)$ and another from $(l_2,v_2)$ to $(l_3,v_3)$, then it has a guarded run from $(l_1,v_1)$ to $(l_3,v_3)$.

**Proof.** Let the first run have length $T_1$ and the second length $T_2$. Concatenate them to obtain a run of length $T_1+T_2$: iteration of the same one-step transition for the combined number of steps first follows the initial run and then continues from its endpoint along the second. The endpoint is therefore $(l_3,v_3)$. For any time strictly before the combined endpoint, either it is before $T_1$, where the first run supplies the guard, or it is at least $T_1$ and still before $T_1+T_2$, where subtracting $T_1$ gives a time before $T_2$ and the second run supplies the guard. This is precisely transitivity of guarded reachability (`AReach.trans`), applied to the two witnesses in the definition of `Reach`.

**Key facts.** `Complexity.LogProg.AReach.trans`.
