<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Robustness/ObliviousSchedule.lean :: Complexity.parallelDecode_code -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Decoding the Transverse Encoding

**Claim.** For any type $A$ with decidable equality and any possibly blank symbol $a$, decoding the transverse encoding of $a$ returns $a$, including when $a$ is blank.

**Proof.** The transverse encoding is an embedding of the type of possibly blank symbols into families of bits. The decoder is defined as a choice of preimage under this embedding; the left-inverse property of that choice on values in the embedding's image guarantees that decoding the encoding of $a$ returns $a$.
