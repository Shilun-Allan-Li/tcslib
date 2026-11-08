<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/RecordTable.lean :: Turing.rt_initRecord_fields -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Initial Configuration Record

**Claim.** The initial configuration record has the stated state, binary position, centered blank work-tape fields, and final tag.

**Proof.** First express the record of the initial configuration using `Turing.cfgRecord_init`: its state cell is `some q₀`, its position field is the binary-digit encoding of $1$ at width `posWidth x.length`, and its work-tape cells are blank with a mark precisely at the central index. The width is positive because it is the bit width of the positive number $|x|+1$. The theorem for the digits of $1$ at positive width (`Turing.rt_binDigits_one`) turns that position field into one true digit followed by width minus one false digits. The centered-word identity (`Turing.rt_centeredWord`) rewrites the indexed cells, whose mark is true exactly at the center, as $s$ false cells, one true cell, and then $s$ false cells. Finally, unfold the width notation and simplify the list maps to obtain the stated record.

**Key facts.** `Turing.cfgRecord_init`, `Turing.rt_binDigits_one`, `Turing.rt_centeredWord`.
