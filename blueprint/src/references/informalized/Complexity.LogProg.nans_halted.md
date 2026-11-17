<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Machines/NARM.lean :: Complexity.LogProg.nans_halted -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Answer from a Halted Configuration

**Claim.** From a halted configuration, a length-$N$ choice sequence leaves recorded answer $b$ exactly when the recorded answer is already `some b`.

**Proof.** A halted configuration remains unchanged under every step, so running any choice sequence from it preserves its recorded answer. Thus, if a sequence witnesses an answer of `some b`, the recorded answer in the starting configuration was already `some b`. Conversely, if the recorded answer is `some b`, choose any length-$N$ sequence, such as $N$ false bits. Since the machine is halted throughout, this sequence witnesses the same answer.
