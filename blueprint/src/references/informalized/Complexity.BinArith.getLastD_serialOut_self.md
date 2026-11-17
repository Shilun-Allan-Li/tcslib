<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassP/BinaryArith/Basic.lean :: Complexity.BinArith.getLastD_serialOut_self -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Final Output Equals Final State

**Claim.** For a nonempty finite sequence of input pairs, the last output bit produced by repeatedly applying $\delta$ as both transition and output function equals the state obtained after processing the entire sequence.

**Proof.** Induct on the input sequence, allowing the initial state to vary. The empty sequence is impossible under the nonemptiness hypothesis. For a one-pair sequence, the sole output is $\delta$ applied to the initial state and that pair, which is also the final state. For a sequence with at least two pairs, the last output and final state are obtained by processing the tail from the updated state $\delta(s,p)$, where $p$ is the first pair. The induction hypothesis applies to this nonempty tail and gives their equality.
