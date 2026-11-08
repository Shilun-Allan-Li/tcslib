<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/MeyerSound.lean :: Complexity.Meyer.work_edge -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# One-Step Work-Tape Update

**Claim.** At an encoded time and offset within the stated bounds, the symbol encoding at the next time satisfies the machine’s work-tape update rule: it is unchanged in a halting configuration, and otherwise reflects the prescribed write and head movement.

**Proof.** Fix the simulated configuration $c$ at time $t$. Apply the all-checks hypothesis to the work-tape step check at address $a_E(e)$, with sign flag $s_E(e)$. Correctness at time $t$ supplies the check’s claims about the state and the symbols read by the heads (`claims_of_correct`). The bounds on $t$ and $e$ ensure that the check applies and that its encoded time and address coordinates are valid.

The sign-and-address encoding translates the two neighboring address slots used by the check into the integer offsets $e$ and $e+1$: these are the identities `edge_c1` and `edge_c2`. The zero-address tests in the check translate to $e=0$ and $e+1=0$ (`edge_E0`, `edge_E1`). By the sign-decoding property `sv_sgn`, each encoded symbol in the check is the corresponding value of $cX$; `symvA_NumVal` and `avOf_ite` identify which address slot is selected by the sign flag. Thus the check’s work-tape condition becomes exactly the desired equation for the appropriate head movement.

Finally split on whether $c$ is halting and, if not, on the transition’s movement on tape $h$. For a halting configuration, the check equates the time-$t+1$ and time-$t$ values at the same offset. For positive movement it gives the updated value at $e$ from the write at the scanned cell when $e+1=0$, and otherwise the old value at $e+1$. For negative movement the corresponding equation is at $e+1$, using the write when $e=0$ and otherwise the old value at $e$. For zero movement it gives the value at $e$, using the write when $e=0$ and otherwise retaining the old value there. These are precisely the three clauses of the statement.

**Key facts.** `Complexity.Meyer.claims_of_correct`, `Complexity.Meyer.sv_sgn`, `Complexity.Meyer.edge_c1`, `Complexity.Meyer.edge_c2`, `Complexity.Meyer.edge_E0`, `Complexity.Meyer.edge_E1`, `Complexity.Meyer.symvA_NumVal`, `Complexity.Meyer.avOf_ite`.
