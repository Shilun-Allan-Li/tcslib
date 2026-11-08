<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/Primitives.lean :: Turing.FinTM.catalogRewind -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Bounded Input Rewind

**Claim.** Under the stated transition rules, from any configuration $c$ in state $\mathrm{start}$ there is a number of steps at most the input-head position plus $2$ after which the machine is in the destination state and its input head is at position $1$.

**Proof.** The first transition from $c$ is fixed by the start-state rule: it moves left and enters $\mathrm{scan}$, without changing the other components. The resulting input-head position is the old position minus one (`moveInputPos_neg_val`), and it is at most the input length, so the scan-state rewind lemma applies (`rewind_scan`). That lemma says that from this scan configuration, after its current head position plus one steps, the machine reaches the destination state with head at position $1$. Combining the initial step with this scan gives $1+((\text{old position}-1)+1)$ steps, which is bounded by the old position plus $2$. The run-addition law justifies composing the initial step and the subsequent scan (`MultiTapeTM.runFrom_add`). The first transition’s configuration update is the direct effect of applying the prescribed control action (`controlAction_apply`).

**Key facts.** `Turing.FinTM.moveInputPos_neg_val`, `Turing.FinTM.rewind_scan`, `Turing.MultiTapeTM.runFrom_add`, `Turing.FinTM.controlAction_apply`.
