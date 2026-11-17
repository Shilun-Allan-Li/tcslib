<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/LogspaceUniformWalk.lean :: BoolCircuit.AdjWalk.inLoop -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Bounded Input Scan Loop

**Claim.** If $n+1\le B$, the input scan processes the word of $d$ ones followed by zero from position $k$, returning the stated bit when the target position lies in the word and otherwise reaching the specified postcondition. All registers stay bounded by $B$ before the walk reaches its endpoint.

**Proof.** Use induction on the number $d$ of leading ones, with the current input position $V$ and output position $k$ carried along. The register-tuple bound (`gd_rg`) supplies the bound needed to account for each machine transition, and `Em.step` transfers the behavior across that transition.

When $d=0$, $V=n$. The oracle's type test says that this input vertex is not a gate vertex (`orc_type`, together with `vtype_none`), so the walk emits the final zero bit and then reaches the stated postcondition (`Em.emit`).

For the successor case, split off the first one from the word. Since $V+d=n$, we have $V<n$, so the type test identifies $V$ as an input vertex. The walk emits the one bit and increments both the input position and the output position. The induction hypothesis then processes the remaining $d$ ones and the final zero, starting from $V+1$ and $k+1$. Concatenating the emitted bit with that inductive behavior gives the result for the full word (`Em.append`); the endpoint registers agree by the relation $V+d=n$.

**Key facts.** `BoolCircuit.AdjWalk.gd_rg`, `BoolCircuit.AdjWalk.Em.step`, `BoolCircuit.AdjWalk.astep_call₁`, `BoolCircuit.AdjWalk.orc_type`, `BoolCircuit.AdjWalk.vtype_none`, `BoolCircuit.AdjWalk.rg_1`, `BoolCircuit.AdjWalk.Em.emit`, `BoolCircuit.AdjWalk.Em.append`, `BoolCircuit.AdjWalk.upd_1`, `BoolCircuit.AdjWalk.Em.mono`.
