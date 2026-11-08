<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CookLevin/Hardness.lean :: Complexity.clPrepare_start -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Preparation from the Initial Configuration

**Claim.** For each input word, the preparation machine reaches the loader entry configuration within $2|x|+3$ steps.

**Proof.** The input-reading machine reaches its terminal state after some positive time $t\le 2|x|+2$, with its work tape holding a copy of $x$ (`Complexity.clInput_first`). The preparation machine simulates this reader on its stream tape, using the placement that reserves the loader’s tapes; the placed-run theorem transports the reader’s run to the preparation machine (`Complexity.clPlaced_run`). The guard needed for this simulation holds because the reader’s terminal state is avoided at all earlier times, and the two machines’ transitions agree in every nonterminal reader state. The placed initial configuration is exactly the preparation machine’s initial configuration. At time $t$, the preparation machine is consequently in the reader’s terminal control state with the stream tape holding $x$. One more step switches to the loader entry state without moving any tape head or changing tape contents: the control-action effect is given by `Turing.FinTM.controlAction_apply`, and zero input movement fixes the input position (`Turing.moveInputPos_zero`). The run successor law (`Turing.MultiTapeTM.runFrom_succ_eq_step'`) identifies this with time $t+1$, whose bound is $2|x|+3$.

**Key facts.** `Complexity.clInput_first`, `Complexity.clPlaced_run`, `Turing.FinTM.controlAction_apply`, `Turing.moveInputPos_zero`, `Turing.MultiTapeTM.runFrom_succ_eq_step'`.
