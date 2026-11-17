<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Universal.lean :: Turing.timed_apply_record -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Applying a Decoded Transition Record

**Claim.** For a coded machine $M$, Boolean words $\alpha,x$, a configuration $\mathrm{src}$ of $M$ on input $x$, table positions $p_0,p$, and an action $a$, one step of the universal interpreter from the specified record-application configuration equals the simulation configuration of $a$ applied to $\mathrm{src}$, with table position $p$.

**Proof.** Let the simulated configuration be the base configuration and let the interpreter configuration carry the record-application control, the table at cursor $p$, and the unary tape for the successor state of $a$. The decoded action bits recover exactly the input-head movement, work-tape write, work-head movement, and output symbol of $a$ (`Turing.timedCut_ActionBits_decode`). The interpreter's input convention also preserves the simulated input symbol despite its shifted encoding (`Turing.universalInput_read`). It therefore chooses the virtual input movement that represents $a$'s movement in the simulated machine. The encoded input head then agrees with the encoding of the simulated head after the move, and the corresponding displacement agrees as an integer (`Turing.universalInput_move`). Applying the interpreter transition updates the four lanes: the table and state lanes are left as required, the simulated work lane receives $a$'s write and head movement, and the input-position lane records the virtual movement. Its output and successor state likewise match the applied action, including the case in which that successor state is halting. Thus all components agree with the simulation configuration of $a$ applied to $\mathrm{src}$ at table position $p$.

**Key facts.** `Turing.timedCut_ActionBits_decode`, `Turing.universalInput_read`, `Turing.universalInput_move`.
