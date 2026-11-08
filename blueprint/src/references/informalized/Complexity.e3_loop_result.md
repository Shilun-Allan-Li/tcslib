<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassNP/Nondeterminism.lean :: Complexity.e3_loop_result -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Loop Output and Split Emitter

**Claim.** The loop’s output, formed from the first state passing the round test or the empty word if none passes, equals the word produced by the exponential split emitter on $w$.

**Proof.** By the orbit-search equality, the loop’s search result is the split search result. If that result is none, both constructions return the empty word. If it is some $i$, the split-search specification gives $i\le |w|$ (`Complexity.e3_split_spec`). The orbit lemma then says the loop state at index $i$ is the word of $i$ true bits (`Complexity.e3_step_orbit`), whose length is $i$. Consequently the loop encodes the prefix and suffix of $w$ cut at $i$, exactly as the split emitter does.

**Key facts.** `Complexity.e3_find_eq`, `Complexity.e3_split_spec`, `Complexity.e3_step_orbit`.
