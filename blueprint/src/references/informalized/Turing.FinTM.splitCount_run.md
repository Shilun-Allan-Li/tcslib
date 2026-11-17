<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/Primitives.lean :: Turing.FinTM.splitCount_run -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Counted simulation of a source run

**Claim.** If the source run from $c$ is live at every time before $t$, then the host run from the encoded configuration agrees at time $t$ with the encoded source run at time $t$.

**Proof.** Proceed by induction on $t$. At time $0$, the encoded host configuration is exactly the encoding of the source configuration. For the induction step, let $d$ be the source configuration at time $t$. It is live by hypothesis, so its state is present. Because the source machine has empty input, its input symbol is blank; the host simulation supplies this blank symbol and its successor-indexed work-tape symbols to the source transition. The one-step correspondence (`splitCount_apply`) then identifies the host's next configuration with the encoding of the source's next configuration. Applying this at each live time and using the run successor identity (`runFrom_succ_eq_step'`) completes the induction.

**Key facts.** `Turing.FinTM.splitCount_apply`, `Turing.MultiTapeTM.runFrom_succ_eq_step'`.
