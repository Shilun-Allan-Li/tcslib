<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter07/CSPDerandomization.lean :: FABL.ConditionalExpectationPolytimeAdapter.decode_algorithm -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Decoding the algorithm output

**Claim.** For every input, decoding the algorithm’s output yields exactly the packed assignment specified by its conditional-expectation plan.

**Proof.** The algorithm’s behavior on a canonical input encoding is specified to be the canonical output encoding of that plan’s packed assignment. Apply this identity to the given input, then use the output encoding’s decode-after-encode law. The decoded output is therefore exactly the stated packed assignment.
