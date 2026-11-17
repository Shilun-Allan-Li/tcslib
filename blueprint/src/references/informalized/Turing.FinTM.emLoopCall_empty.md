<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/Loop.lean :: Turing.FinTM.emLoopCall_empty -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Empty-Prefix Call Identity

**Claim.** When the body configuration has empty output, the forwarding call with empty prefix equals the corresponding capturing call.

**Proof.** The forwarding-call decomposition (`emLoopCall_frame`) identifies the forwarding call with the capturing call formed from the same configuration after replacing its output by the empty word, with the physical output set to the prefix followed by the original output. Set the prefix to empty and use the hypothesis that the original output is empty. The physical output is therefore empty as well, and replacing the configuration's output by empty leaves the configuration unchanged. The two calls are equal.

**Key facts.** `Turing.FinTM.emLoopCall_frame`.
