<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Machines/NARMKit.lean :: Complexity.LogProg.nacc_live -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Acceptance from a Live Configuration

**Claim.** A live configuration with state $l$, register valuation $v$, and no recorded answer has an accepting run exactly when some choice bit leads in one step to a configuration with an accepting run.

**Proof.** An accepting witness is a finite sequence of choice bits. It cannot be empty, because the starting configuration is live rather than halted. Write the sequence as its first bit $b$ followed by a remaining sequence. The defining recursion for runs on choice sequences (narun_cons) says that executing this sequence is the same as taking the first step using $b$ and then executing the remainder. Thus the remainder witnesses acceptance from the resulting configuration. Conversely, given a bit $b$ and a sequence witnessing acceptance after that step, prepend $b$; the same recursion shows the concatenated sequence witnesses acceptance from the original live configuration.
