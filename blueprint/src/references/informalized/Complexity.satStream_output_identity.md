<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassNP/SAT.lean :: Complexity.satStream_output_identity -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Streaming Emitter Output

**Claim.** For every bit string $x$, concatenating the emitted chunks for rounds $0$ through $|x|$—using the encoded state after each number of steps from the encoded startup state—produces the serialization of the clause-splitting transform of the decoded formula.

**Proof.** First, the iterate of the encoded-state step is the encoding of the corresponding iterate of the state round (satStreamStep_iterate). Reading an encoded state recovers that state (satStreamRead_word), so each emitted chunk in the stated concatenation is precisely the output of the corresponding state round. The round-run output identity (satStreamRun_output), applied for $|x|+1$ rounds from the startup state, identifies the concatenation of those chunks with the output of the complete run. The run computes the desired serialization (satStreamRun_correct), giving the result.

**Key facts.** `Complexity.satStreamStep_iterate`, `Complexity.satStreamRead_word`, `Complexity.satStreamRun_output`, `Complexity.satStreamRun_correct`.
