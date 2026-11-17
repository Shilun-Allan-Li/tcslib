<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Codec/Run.lean :: Complexity.Codec.ct_run -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Execution of the Capacity-Check Routine

**Claim.** Under the register-bound, length, and bit hypotheses, the capacity-check routine has a guarded execution with the stated bounded final assignment and control state, depending on the length of the word, the binary length of the initial capacity, and the last bit of the word.

**Proof.** Apply the canonical-tail loop theorem (`canonicalTail_loop`) to the routine that scans the word from the position register up to the length register. Its hypotheses are met by the distinctness of the position, length, and capacity registers, the displayed program equations for the test, capacity check, bit read, halving, and pointer advance, and the assumed relation between the length and position registers. Each oracle read at the encoded position returns the corresponding input bit: `orc_bit` identifies this answer with the input's bit at that position, and the hypothesis `ho` makes it equal to the corresponding bit of $w$. The loop theorem supplies a final register assignment with all values bounded, the position not increased, and all registers other than position and capacity unchanged; it also gives the guarded execution. Its terminal condition selects the continuation precisely when the word length is at most the binary length of the original capacity and the last bit (defaulting to true for the empty word) is true, and selects rejection otherwise. These are exactly the control states in the theorem statement.

**Key facts.** `Complexity.Codec.orc_bit`, `Complexity.LogProg.canonicalTail_loop`.
