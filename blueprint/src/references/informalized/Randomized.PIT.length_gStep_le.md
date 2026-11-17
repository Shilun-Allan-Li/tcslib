<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Randomized/ZeroPRun.lean :: Randomized.PIT.length_gStep_le -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Length bound for one update

**Claim.** For every state $D$, one update has length at most $|D|+10(|\pi_1(D)|+1)$, where $\pi_1(D)$ is the first projection of the pair encoding.

**Proof.** First bound the lengths of the nested components of $D$ using the fact that the two projections together, counted with the first projection twice, fit within the encoding length (`length_pair_components_le`). The projections individually cannot exceed the length of their input (`length_pairFstD_le`, `length_pairSndD_le`). The updated word is no longer than the current word (`length_restW_le`), and the appended computed value is no longer than the raw part of the state (`length_valW_le`). Now split according to the update rule. If the state is already done, it is unchanged. If it is not done but the current word is valid, expand the lengths of the pair encodings and the appended counter and value; the component bounds above give the claimed increase. If it is invalid, the update clears the work word and retains the other stored components, and the same encoding-length bounds give the stated estimate.

**Key facts.** `Complexity.length_pair_components_le`, `Complexity.length_pairFstD_le`, `Complexity.length_pairSndD_le`, `Randomized.PIT.length_restW_le`, `Randomized.PIT.length_valW_le`, `Turing.length_pairEncode`.
