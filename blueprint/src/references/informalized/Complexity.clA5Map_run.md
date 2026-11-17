<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CookLevin/Hardness.lean :: Complexity.clA5Map_run -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Transducer Run on a Suffix

**Claim.** Starting from the configuration whose head is just after a prefix of the input, the machine halts after the suffix length plus one steps and appends exactly the transduction of that suffix to the existing output.

**Proof.** We argue by induction on the suffix. If it is empty, the input head is at the end marker. The machine therefore takes its final transition, emits the prescribed final output, and enters the halting state. This gives the claimed output because the transduction of the empty word is precisely that final output. For a nonempty suffix $b::r$, the head reads $b$, so the transition emits $(\mathrm{emit}\ q\ b)$, moves the head one position to the right, and changes the state to $\mathrm{next}\ q\ b$. The head-position fact for a positive move (`moveInputPos_pos_of_ne_right`) ensures the new configuration is the one just after the enlarged prefix. The input-symbol fact (`FinTM.inputSymbol_at`) identifies the symbol read as $b$. Equality of configurations follows from matching state, input position, and output; with zero work tapes there are no further components to check (`Cfg.ext_zero_tapes`). By the run recursion (`MultiTapeTM.runFrom_succ_eq_step`), this first transition is followed by the run on the remaining suffix. Apply the induction hypothesis to that run, starting in state $\mathrm{next}\ q\ b$ with output already extended by $(\mathrm{emit}\ q\ b).toList$. It halts and appends the transduction of $r$. The recursive definition of the transduction and associativity of list concatenation identify the resulting output with the transduction of $b::r$, as required.

**Key facts.** `Turing.FinTM.inputSymbol_at`, `Turing.moveInputPos_pos_of_ne_right`, `Turing.Cfg.ext_zero_tapes`, `Turing.MultiTapeTM.runFrom_succ_eq_step`.
