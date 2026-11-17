<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Randomized/ZeroPRun.lean :: Randomized.PIT.sI_scanRun -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Scan Run Gate Count

**Claim.** If decoding $x$ yields $(n,C)$ and $C$ is well formed, then the scan-run index component is the all-ones string of length equal to the number of gates of $C$.

**Proof.** The decoding hypothesis implies that $x$ is the encoding of $(n,C)$. Expanding that encoding, the unary head and remainder procedures recover the unary encoding of $n$ and the remaining gate encoding. Thus the scan run starts with the context for $n$ and empty auxiliary lists. The gate-run simulation theorem says that, when every gate reference points to an earlier gate as required by well-formedness, this run encodes the completed evaluation state. Its index component is the all-ones string whose length is the number of evaluated values. The evaluation-length identity says that this number is the initial value-list length plus the number of gates; since the initial list is empty, it equals $C$’s gate count.

**Key facts.** `Randomized.AlgCircuit.encode_of_decode`, `Complexity.BinArith.uHead_encodeNat`, `Complexity.BinArith.uRest_encodeNat`, `Randomized.PIT.gateRun_encodeGates`, `Randomized.PIT.length_evalVals`.
