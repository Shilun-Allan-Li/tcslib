<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Robustness/ObliviousSetup.lean :: Complexity.setupCfg_copy_return -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Return to the Budget Start

**Claim.** Starting in copy-return phase with the guide head at cell $j$ and the partial guide for $n+1$ copied cells, after $j+1$ steps the machine is in budget-start phase with the guide head at $0$. The base data, input-head position, budget and unary tapes and heads, and guide tape are unchanged.

**Proof.** Use induction on $j$. When $j=0$, the guide at coordinate $0$ contains the origin mark, so the copy-return transition enters budget-start immediately without moving any head or changing any tape. For the successor case, the guide head is at $j+1>0$, where the partial guide has no origin mark. Thus the first transition remains in copy-return and moves the guide head one cell left, leaving all tapes unchanged. The induction hypothesis then applies from head position $j$ and gives the claimed result after the remaining $j+1$ steps. The fact that the partial guide has its origin mark exactly at coordinate zero is `copyGuide_origin`; the configuration update under the controller action is `setupCfg_apply`. The run-length decomposition follows from `runFrom_succ_eq_step` and `runFrom_zero`.

**Key facts.** `Complexity.copyGuide_origin`, `Complexity.setupCfg_apply`.
