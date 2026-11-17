<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/Primitives.lean :: Turing.FinTM.computesFunInTime_incFixed -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Fixed-Width Binary Increment

**Claim.** A finite Turing machine computes the fixed-width binary increment, with overflow represented by the empty word, in time at most a constant multiple of the input length plus one.

**Proof.** Take the machine `incFixedTM` and the constant $c=3$. For each input word, the established computation theorem `incFixedTM_computes` gives exactly the specified output, halting within $3(|x|+1)$ steps. Since this holds for every input, it is the required function computation.

**Key facts.** `Turing.FinTM.incFixedTM_computes`.
