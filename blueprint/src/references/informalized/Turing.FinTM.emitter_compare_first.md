<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/Primitives.lean :: Turing.FinTM.emitter_compare_first -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# First Comparator Return

**Claim.** For Boolean words $w,u,v$ and a valid input-head position, the comparator reaches its return phase within $2(\max(|u|,|v|)+1)$ steps, with register equal to the truth value of $u=v$ and both work-tape heads at zero; before that first return time it is in neither return state.

**Proof.** The comparator run theorem gives the configuration after the full bound $T=2(\max(|u|,|v|)+1)$: it is in state $2$ with register $\operatorname{decide}(u=v)$ and both work heads at zero (`Turing.FinTM.emitter_compare_run`). Once a configuration is in a return state, the transition fixes it: the transition is a control action with zero movement, and a zero input move preserves the input position (`Turing.FinTM.controlAction_apply`, `Turing.moveInputPos_zero`). Apply the first-entry principle to this fixed return set and the run ending in the specified configuration (`Turing.FinTM.emitter_first_entry`). It yields a time no greater than $T$ at which the target configuration is reached, with no earlier run state in the return set. This time is positive: at time zero the starting state has first component $0$, whereas the target return state has first component $2$. The first-entry property says precisely that every earlier configuration is in neither return state, and the target equality supplies the register and head positions claimed.

**Key facts.** `Turing.FinTM.emitter_compare_run`, `Turing.FinTM.emitter_first_entry`, `Turing.FinTM.controlAction_apply`, `Turing.moveInputPos_zero`.
