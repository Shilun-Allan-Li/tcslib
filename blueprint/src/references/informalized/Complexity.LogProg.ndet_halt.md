<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Machines/NARMCompile.lean :: Complexity.LogProg.ndet_halt -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Halting of the Compiled Program

**Claim.** Under the stated hypotheses, there is a time bound and a final configuration such that all choice words up to that bound keep the register and decider head positions within the prescribed limits, while every choice word of exactly that length reaches the same halted configuration with output extended by $b_0$.

**Proof.** First replace the nondeterministic program by the deterministic part that sends every choice instruction to the answer opposite $b_0$. Since the current instruction is deterministic, the deterministic step lemma (`nastep_det`) shows that this replacement has the same halting computation as the given deterministic interpretation. The precondition transfers to this deterministic part (`pre_detPart`).

Apply the simulation theorem for register programs (`arm_run`) to obtain a compiled deterministic run of some length $T$ ending halted with output $\mathrm{out} ++ [b_0]$, with register heads bounded below by $-1$ and above by $W$, and decider heads bounded by $B$ throughout. Its invariant supplies those bounds at every time before $T`; the terminal configuration supplies them at time $T$ as well. The initial register bounds follow from the assumed bit-length bounds.

Now regard this compiled deterministic machine as $M$. At any state where the nondeterministic machine offers a genuine choice, the deterministic replacement immediately halts and emits the opposite bit to $b_0$ (`detPart_step_choose`). Since the run of $M$ instead ends with output extended by $b_0$, such a choice state cannot occur before time $T$: otherwise the output would already have been extended by the opposite bit (`avoid_of_halt`). Thus throughout the first $T$ steps the nondeterministic machine and $M$ use the same transitions (`ncompileTM_tr`). The run-agreement theorem (`ndtm_runWith_eq_runFrom`) therefore identifies every nondeterministic run on a word of length at most $T$ with the corresponding prefix of the deterministic run. Taking $S=T$ and the deterministic run's terminal configuration, the head bounds hold for every such word, and every word of length exactly $S$ reaches that terminal configuration. The seam preserves the halted state, and the output is $\mathrm{out} ++ [b_0]$ (`seam_state_none`).

**Key facts.** `Complexity.LogProg.nastep_det`, `Complexity.LogProg.pre_detPart`, `Complexity.LogProg.arm_run`, `Complexity.LogProg.detPart_step_choose`, `Complexity.LogProg.avoid_of_halt`, `Complexity.LogProg.ncompileTM_tr`, `Complexity.LogProg.ndtm_runWith_eq_runFrom`, `Complexity.LogProg.seam_state_none`.
