<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/Catalog.lean :: Turing.FinTM.f2_splitEmit_separator -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Separator emitted in two steps

**Claim.** Starting in state $0$ with both heads at position $|s|$ and output $out$, two steps of the specified machine lead to state $3$, with the heads unchanged and output $out$ followed by $01$.

**Proof.** At position $|s|$, the auxiliary tape is blank, so the machine in state $0$ takes its blank-cell branch: it emits $0$, enters state $2$, and leaves the heads in place. The first-step configuration is therefore state $2$ with output $out$ followed by $0$. In state $2$, the machine emits $1$, enters state $3$, and again leaves both heads in place. Combining the two steps gives output $out$ followed by $01$. The run equations for a successor step (`runFrom_succ_eq_step`, `runFrom_zero`) identify this pair of transitions with the two-step run, and the zero-movement identity (`moveInputPos_zero`) preserves the input-head position; the auxiliary head also remains fixed by the transition definition.

**Key facts.** `Turing.MultiTapeTM.runFrom_succ_eq_step`, `Turing.MultiTapeTM.runFrom_zero`, `Turing.moveInputPos_zero`.
