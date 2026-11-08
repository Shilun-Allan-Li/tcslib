<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/Catalog.lean :: Turing.FinTM.a2_heads_steps -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Head bounds over bounded time

**Claim.** If the initial work-tape heads lie in $[-A,A]$ and $t\le B$, then after $t$ steps every work-tape head lies in $[-(A+B),A+B]$.

**Proof.** Fix a work tape. The head-displacement bound for a run of $t$ steps says that its final position is at least its initial position minus $t$, and at most its initial position plus $t$ (`f2_head_steps`). The initial bounds therefore give a lower bound of $-A-t$ and an upper bound of $A+t$. Since $t\le B$, these imply the desired bounds $-(A+B)$ and $A+B$.

**Key facts.** `Turing.FinTM.f2_head_steps`.
