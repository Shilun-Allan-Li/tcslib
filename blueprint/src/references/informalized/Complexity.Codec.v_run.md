<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Codec/Run.lean :: Complexity.Codec.v_run -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Bounded Verifier Run

**Claim.** Under the stated length, register-bound, offset, and input-bit hypotheses, the codec program has a finite run from the verifier-test label to the verifier-done label. Before the endpoint, every configuration satisfies the precondition and register bound $B$; the final verifier accumulator is the fold of the verifier update over the zipped words, and the two input registers have advanced by twice their common length.

**Proof.** This is an instance of the general scan-loop theorem (`scan_loop`). Its hypotheses are met because the two input registers are distinct from each other and from the endpoint register, the scan stride is $2>0$, and the specified labels implement the scan pattern: test whether the first pointer has reached its limit; read its bit; read the second pointer's bit; update the accumulator with that pair; and advance each pointer by two positions before returning to the test. The program's oracle for bit queries returns the bit at the requested position (`orc_bit`), so the assumptions about the bits of $y$ supply exactly the two word entries at each iteration. The common-length assumption ensures the scan reads paired entries throughout and terminates after the required number of iterations. Applying `scan_loop` gives a finite run with the stated endpoint accumulator and updated pointers, while maintaining the guard, which is precisely the precondition and register bound required in the claim.

**Key facts.** `Complexity.Codec.scan_loop`, `Complexity.Codec.orc_bit`.
