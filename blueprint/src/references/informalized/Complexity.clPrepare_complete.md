<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CookLevin/Hardness.lean :: Complexity.clPrepare_complete -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Completion of Field Preparation

**Claim.** Given bounded-length Boolean fields and any trailer, the preparation machine reaches the specified loading configuration within the stated time bound.

**Proof.** Let $x$ be the packed fields followed by the trailer. The preparation-start result (`Complexity.clPrepare_start`) gives a time $a\le 2|x|+3$ at which the machine has entered the loader with empty field tapes, the stream tape holding $x$ at position zero, and counter zero. Independently, apply the loader completion result (`Complexity.clLoad_complete`) to load the fields from the packed stream, taking the old fields to be empty, the prefix to be empty, and the trailer to be the given tail. The empty prefix reduces the stream and head-position expressions to those for $x$, and gives a duration $b\le l(3W+7)$. The loader and preparation machines agree on the loader-state component, so the guarded run-mapping theorem (`Turing.MultiTapeTM.runFrom_mapState_of_agreeOn`) transports this $b$-step loader run into the preparation machine. Concatenate the initial $a$ steps with these $b$ steps using the run-addition law (`Turing.MultiTapeTM.runFrom_add`). The resulting configuration is the required one, and $a+b\le 2|x|+3+l(3W+7)$.

**Key facts.** `Complexity.clPrepare_start`, `Complexity.clLoad_complete`, `Turing.MultiTapeTM.runFrom_mapState_of_agreeOn`, `Turing.MultiTapeTM.runFrom_add`.
