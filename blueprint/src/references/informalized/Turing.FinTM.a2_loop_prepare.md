<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/Catalog.lean :: Turing.FinTM.a2_loop_prepare -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: low -->

# Preparation for bounded loop simulation

**Claim.** Under the stated time and space bounds for $F$, there is a halted configuration $c$ with the required binary output and a time $t\le 5T(|x|)+7$ at which the loop host is ready for $c$; the heads of $c$ and the host's heads throughout the run satisfy the stated bounds.

**Proof.** Fix the input $x$. The computation hypothesis for $F$ gives a time at which its run halts with output $\operatorname{bits}(R(|x|))$. Choose the first halting time $u$; the first-halt principle ensures that the run stays live before $u$ and that its configuration at $u$ equals the one at the supplied halting time. Let $c$ be that configuration. The output-prefix property ensures that every earlier output is a prefix of $c$'s output. The space bound, together with the fact that the initial work heads are at zero, bounds every head of $F$'s run through time $u$ by $S(|x|)$ (`a2_source_radius`). Thus $c$ has the desired output and head bound.

Up to time $u$, the host simulates the fuel machine while capturing its output on an added tape. The simulation correspondence identifies each host configuration in this phase with the captured fuel configuration (`f2_loopHost_fuel_capture`, using the fuel initialization and run correspondences). The captured heads remain bounded by the fuel heads and the length of the output written so far (`a2_fuel_heads`); output-prefix monotonicity bounds that length by $|c.\mathrm{output}|$. The head bounds are enlarged as needed by monotonicity (`a2_heads_mono`).

After time $u$, the host performs its setup: it transfers the captured output to the payload tape and positions its control heads. This takes $3|c.\mathrm{output}|+4$ steps (`f2_loopHost_fuel_setup`). A rewind then returns the input head to its prescribed position without changing any work-tape head (`rewind_heads`). Its duration is at most the current input-head position plus two, which is at most $u+3`f2_loop_input_run_le`). Since the output word has length at most $T(|x|)$, the total time is at most $u+3|c.\mathrm{output}|+4+u+3$ as represented in the proof; the established first-halt and input-position bounds yield the claimed $5T(|x|)+7$ bound.

For the head estimate during setup, the host starts with radius at most $S(|x|)+|c.\mathrm{output}|$. The setup lasts at most $3|c.\mathrm{output}|+4$ steps, so the per-step displacement bound (`a2_heads_steps`) gives radius at most $S(|x|)+4|c.\mathrm{output}|+4$. The rewind preserves heads, and the head-bound concatenation principle (`a2_heads_join`) combines the simulation, setup, and rewind intervals. Substituting $c.\mathrm{output}=\operatorname{bits}(R(|x|))$ gives the stated uniform bound.

**Key facts.** `Turing.FinTM.f2_loop_first_halt`, `Turing.FinTM.a2_source_radius`, `Turing.FinTM.f2_loopHost_fuel_capture`, `Turing.MultiTapeTM.output_prefix`, `Turing.FinTM.a2_fuel_heads`, `Turing.FinTM.a2_heads_mono`, `Turing.FinTM.f2_loopHost_fuel_setup`, `Turing.FinTM.rewind_heads`, `Turing.FinTM.f2_loop_input_run_le`, `Turing.FinTM.a2_heads_steps`, `Turing.FinTM.a2_heads_join`.

**Caveat.** The supplied proof derives the time bound through several arithmetic bounds, but the displayed source does not make the intermediate simplification to $5T(|x|)+7$ transparent; the account summarizes that estimate.
