<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/Loop.lean :: Turing.FinTM.exists_emitLoopTM -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Emitting Loop Machine

**Claim.** If a body machine repeatedly updates a state word and emits an output chunk, while a counter machine computes the number of rounds, then a finite machine computes the concatenation of the chunks from rounds $0$ through $R(|x|)$ within $c(T(|x|)+1)(R(|x|)+2)$ steps.

**Proof.** Use the loop host configured to emit the fixed output $[\mathrm{true}]$ on each successful round. First, the preparation lemma runs the counter machine to obtain the bits of $R(|x|)$ and places the host in a ready configuration. The start lemma then uses the assumed clean-seam startup run to reach a call configuration for the initial word $s_0(x)$. For each index $i\le R(|x|)$, the orbit-invariant lemma gives the round invariant for the state $(\mathrm{stepF}\ x)^i(s_0(x))$. The binary debit lemmas show that the host’s fuel word retains its length and that its success flag is true exactly when fewer than $R(|x|)$ rounds have already been completed. The round simulation combines this counter behavior with the assumed body round: it emits the chunk for the current state and either sets up the next candidate configuration or halts after the last one. Its time is bounded by $10(T(|x|)+1)$, using the fuel-width estimate and the assumed round bound. The loop-summing lemma concatenates these $R(|x|)+1$ chunks, starting with empty output, and halts within $(R(|x|)+1)10(T(|x|)+1)$ additional steps. Including preparation and startup gives a total no greater than $10(T(|x|)+1)(R(|x|)+2)$. The resulting run computes the required concatenation; monotonicity of timed computation allows the bound to be stated in the theorem’s exact form.

**Key facts.** `Turing.FinTM.loopHost_prepare`, `Turing.FinTM.loopHost_start`, `Turing.FinTM.loop_fuel_width`, `Turing.FinTM.loopDebit_iterate_length`, `Turing.FinTM.loopDebit_success`, `Turing.FinTM.loopDebit_iterate_value`, `Turing.FinTM.loop_orbit_inv`, `Turing.emLoopHost_round`, `Turing.FinTM.emLoop_sum`, `Turing.MultiTapeTM.runFrom_add`, `Turing.FinTM.ComputesInTime.mono`.
