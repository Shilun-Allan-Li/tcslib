<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Composition.lean :: Turing.FinTM.condTM_start -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Conditional machine reaches the selected branch

**Claim.** If the controller $D$ halts on input $x$ with singleton output $[b]$, then the conditional machine reaches a configuration consisting of the selected branch machine's initial configuration on $x$, embedded in its branch tape block, together with suitable controller-tape contents and head positions.

**Proof.** Choose a time at which $D$ computes $[b]$. The timed-computation characterization (`computesInTime_iff`) shows that $D$ is halted then. Let $t$ be its first halting time and let $c_f$ be its configuration at that time. The computation of $D$ at time $t$ has output $c_f$'s output; uniqueness of a machine's output across halting computations (`ComputesInTime.output_unique`) therefore gives $c_f$'s output as $[b]$. Up to time $t$, the conditional machine follows the controller: its run from the embedded initial configuration agrees with the embedded run of $D$ (`controlCfg_run`), since $D$ has not halted at any earlier time. At that point the controller is halted and has recorded $b$. The conditional machine now scans back to the designated boundary and moves into the initial state of the branch selected by $b$. The rewind lemma (`rewind_from_any`) supplies a finite number $r$ of steps for this transition, leaving the input head at its initial position. Applying the run-composition law (`runFrom_add`) to the first $t$ steps and these additional $r$ steps gives the desired configuration at time $t+r$. The controller tapes and head positions in that configuration are those of $c_f$; the branch block contains the selected branch machine's initial configuration.

**Key facts.** `Turing.FinTM.computesInTime_iff`, `Turing.FinTM.ComputesInTime.output_unique`, `Turing.FinTM.controlCfg_run`, `Turing.FinTM.rewind_from_any`, `Turing.MultiTapeTM.runFrom_add`.
