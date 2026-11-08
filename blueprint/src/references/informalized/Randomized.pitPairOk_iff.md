<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Randomized/ZeroPReduce.lean :: Randomized.pitPairOk_iff -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Valid circuit-pair characterization

**Claim.** The pair test accepts exactly when its two total projections decode to well-formed arithmetic circuits with the same number of input variables.

**Proof.** Assume the pair test is true. Its two validity tests are true, so the validity characterization (`Randomized.PIT.validW_iff`) decodes each projection to a circuit and shows each is well formed. The decoded circuits initially come with possibly different input counts. The encoding recovery fact (`Randomized.AlgCircuit.encode_of_decode`) identifies each circuit's encoding with its projection. Applying the leading-run identity (`Complexity.BinArith.uHead_encodeNat`) to these encodings shows that the lengths compared by the pair test are the respective input counts. Since that comparison is true, the counts agree, giving the required pair. Conversely, suppose both projections decode to well-formed circuits with a common input count. Encoding recovery and the same leading-run identity show that their tested lengths agree. The validity characterization makes each validity test true, and hence the pair test is true.

**Key facts.** `Randomized.PIT.validW_iff`, `Randomized.AlgCircuit.encode_of_decode`, `Complexity.BinArith.uHead_encodeNat`.
