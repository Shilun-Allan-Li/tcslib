<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/MeyerMachineWalk.lean :: Complexity.Meyer.walk_run -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Bounded Simulation of a Walk

**Claim.** Under the stated counter and boundary-tag hypotheses, the constructed machine halts within $(v+1)(2|w|+3)$ steps and outputs the selector answer determined by the configuration after $v$ simulated walk steps.

**Proof.** Proceed by strong induction on the counter value $v$. The induction step uses the representation of a positive counter as a string of initial zeros followed by a one and a remaining suffix; decrementing the counter replaces that one by zero after borrowing across the initial zeros. The zero-counter case and the positive-counter case follow different machine paths.

1. If $v=0$, the zero-counter characterization says that $w$ consists entirely of zeros. The waiting-decision sweep theorem (`wdec_sweep`) carries the constructed machine across this blank counter tape to the position where it can decide. The blank-tape emission theorem (`wdec_emit`) then shows that one further step halts and outputs the selector answer for the current configuration. The resulting time is $|w|+1$, within the claimed bound.

2. If $v>0$, write $w$ as $j$ zeros, then a one, then a suffix. The sweep theorem advances across the initial zeros to the one. At that position the buffer tape reads true, by the indexed-read fact (`bufferTape_at`), so the firing theorem (`wdec_fire`) executes one simulated selector step and changes the counter bit from one to zero. The update agrees with the buffer representation of the decremented word by the tape-update identity (`bufferTape_update_mid`); the counter-borrow identity (`ctrVal_borrow`) confirms that this new word has value $v-1$. The tag supplied by the firing theorem is valid for the updated configuration, so strong induction applies to that configuration and the decremented word.

   The machine returns from the firing point to the start of the counter using `wret_sweep`, then runs the inductive simulation. The iterate identity for one additional walk step identifies the resulting simulated configuration with the one after $v$ steps. The prefix length $j$ is at most $|w|$, so the initial sweep and return cost at most $2|w|+2$; adding the induction bound gives at most $(v+1)(2|w|+3)$. The run-composition laws (`runFrom_add` and `runFrom_succ_eq_step'`) assemble these segments into a run, preserving the inductive halt and output conclusion.

**Key facts.** `Complexity.TimeHierarchy.ctrVal_zero_eq`, `Complexity.TimeHierarchy.ctrVal_pos_decomp`, `Complexity.Meyer.wdec_sweep`, `Complexity.Meyer.bufferTape_at`, `Complexity.Meyer.wdec_fire`, `Complexity.TimeHierarchy.bufferTape_update_mid`, `Complexity.TimeHierarchy.ctrVal_borrow`, `Complexity.Meyer.wret_sweep`, `Turing.MultiTapeTM.runFrom_add`, `Turing.MultiTapeTM.runFrom_succ_eq_step'`.
