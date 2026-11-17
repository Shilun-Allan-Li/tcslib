<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/Primitives.lean :: Turing.FinTM.emitterToken_separator -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Separator Emission

**Claim.** Starting from the scan configuration on input $x$ in state $3$ at position $i$ with output $o$, two steps of the unary token machine reach state $5$ at the same position, with output $o$ followed by $0,1$.

**Proof.** Express two steps as successive one-step transitions. From state $3$, the machine emits the first separator bit, $0$, and keeps the input head fixed. Its next transition emits $1$, again without moving the head, and enters state $5$. Thus the output is extended by $[0,1]$ and the position remains $i$. Since there are no work tapes, these equalities of state, position, and output establish equality of configurations (`Turing.Cfg.ext_zero_tapes`). The iteration identities used to pass from the two-step run to these transitions are `Turing.MultiTapeTM.runFrom_succ_eq_step'` and `Turing.MultiTapeTM.runFrom_zero`.

**Key facts.** `Turing.MultiTapeTM.runFrom_succ_eq_step'`, `Turing.MultiTapeTM.runFrom_zero`, `Turing.Cfg.ext_zero_tapes`.
