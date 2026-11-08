<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassOracle/Classes.lean :: Complexity.queryTM_init -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Initial Configuration of the Constructed Oracle Machine

**Claim.** The constructed oracle machine's initial configuration on $x$ is the capture image of the original machine's initial configuration, with the query state as return state and empty prefix and output words.

**Proof.** Both configurations have the same state, input-head position, and output word by their definitions: the initial state is the embedded original initial state, the input position is its initial value, and the output is empty. It remains to compare tape contents and head positions. For each of the original $k$ tapes, the capture configuration uses the corresponding original tape and head position, so these coordinates agree. On the additional tape, the empty prefix concatenated with the empty output is empty; its buffer tape is blank everywhere, and its head position is the length of that empty word, namely zero. These are exactly the additional tape's contents and head position in the constructed machine's initial configuration. Hence all configuration fields agree.
