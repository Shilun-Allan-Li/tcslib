<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/CodeSimulator.lean :: Turing.MachineFormat.canonGuard_run -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Bounded Run of the Canonicality Guard

**Claim.** The binary guard machine reaches done when the required block fits in the parsed remainder and escape otherwise, with the stated time, output, input-position, and earlier-avoidance bounds.

**Proof.** Let $B$ be the guard-block bound and $j=2|bits|+2$. Positivity of $B$ (`Turing.MachineFormat.canonGuardBlock_pos`) gives $B-1+1=B$. Since paired decoding succeeds, the input is the corresponding paired encoding (`Turing.eq_pairEncode_of_pairDecode`), whose length is $2|bits|+2+|rest|$ (`Turing.length_pairEncode`); hence $j\le|\alpha|$. The fixed-width increment of $bits$ has length $|bits|+1$ and represents $\operatorname{value}(bits)+1$, by the increment specification (`Turing.MachineFormat.canonCount_spec`) and the identity between the fold defining the bit value and base-two digit evaluation (`Turing.foldr_bit_eq_ofDigits`). If the required block fits in $rest$, the binary guard's successful-run theorem (`Turing.MachineFormat.binaryGuard_done`) supplies a time at which the machine reaches done, with the required position, unchanged output, and no earlier terminal state. Its time bound is at most the claimed one after using the width bound and elementary inequalities. If the block does not fit, the input is too short for the required scan from $j$, so the escape theorem (`Turing.MachineFormat.binaryGuard_escape`) supplies the corresponding escape run, position, output, earlier-avoidance, and time bound. The same width bound and elementary arithmetic give the claimed time estimate in this case as well.

**Key facts.** `Turing.MachineFormat.canonGuardBlock_pos`, `Turing.eq_pairEncode_of_pairDecode`, `Turing.length_pairEncode`, `Turing.MachineFormat.canonCount_spec`, `Turing.foldr_bit_eq_ofDigits`, `Turing.MachineFormat.binaryGuard_done`, `Turing.MachineFormat.binaryGuard_escape`.
