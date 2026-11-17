<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/Catalog.lean :: Turing.FinTM.f2_splitPrepare_first -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# First Preparation Phase

**Claim.** For every natural number $k$ and Boolean words $w,s$, there is a time $t\le 2(|s|+1)$ such that, from the specified initial configuration, the preparation machine is never in state $(2,[|w|<|s|])$ at any time $j<t$, and at time $t$ it is in the specified ready configuration with that state and all work-tape heads at zero.

**Proof.** The run lemma (`f2_splitPrepare_run`) gives the specified ready configuration in state $(2,[|w|<|s|])$ at time $T=2(|s|+1)$. This state is fixed by the machine: its transition is a control action with zero input movement, no tape writes or head movements, and no output. The control-action identity (`controlAction_apply`) and the fact that zero movement fixes the input head (`moveInputPos_zero`) show that every configuration in this state remains unchanged after one step. Apply the first-entry principle for a fixed target state (`f2_catalogFirstEntry`) to the run up to time $T$. It supplies a first time $t\le T$ at which the target configuration occurs, with no earlier run configuration in that state. This is the required time and avoidance property.

**Key facts.** `Turing.FinTM.f2_splitPrepare_run`, `Turing.FinTM.controlAction_apply`, `Turing.moveInputPos_zero`, `Turing.FinTM.f2_catalogFirstEntry`.
