<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Robustness/ObliviousCandidate.lean :: Complexity.clockStageCfg_init -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Initialization of the Clock Stage

**Claim.** One step of the schedule machine from its initial configuration on the embedded input equals the clock-stage configuration of the masked machine's initial configuration on $x$.

**Proof.** From the schedule machine's initial phase, its first transition enters the clock phase with $W$'s initial state. It writes the origin marker on both the budget and unary tapes, leaves the guide tape blank, and leaves the input-head position and original work tapes at their initial values. These are exactly the fields of the clock-stage configuration of the masked machine's initial configuration: the captured tape of the empty output is the origin marker, and the captured empty tape used for the unary tape is also the origin marker (`clockTape_nil`). To check the added tapes, split their three possible indices (`finThree_cases`); the resulting tape contents and head positions agree, while the input position agrees because embedding the input preserves its length. The output is empty on both sides. Thus all configuration fields coincide.

**Key facts.** `Complexity.clockTape_nil`, `Complexity.finThree_cases`.
