<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/CounterLoop.lean :: Turing.lastEmb_apply -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Last-Position Embedding

**Claim.** The embedding from the singleton index set into the set of $k+1$ indices sends every element to the final index $k$.

**Proof.** By definition, the embedding sends its argument to `Fin.last k`. Thus for every element of the singleton index set its value is the final index, which is the claimed identity.
