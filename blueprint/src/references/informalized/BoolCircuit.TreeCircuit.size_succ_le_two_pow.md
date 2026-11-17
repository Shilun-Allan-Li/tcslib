<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/Basic.lean :: BoolCircuit.TreeCircuit.size_succ_le_two_pow -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Size Bound for Bounded-Fanin Circuits

**Claim.** If a Boolean circuit has maximum fanin at most $2$, then its size plus $1$ is at most $2$ raised to its depth plus $1$.

**Proof.** Use structural induction on the circuit. A literal has size $1$ and depth $0$, so the claimed bound holds directly. Now let the circuit be a gate with children $cs$, and assume the bound for every child. The fanin hypothesis implies both that the list has length at most $2$ and that each child's maximum fanin is at most $2$ (`maxFanin_node` and `maxFanin_le_maxFaninL`). Write $D$ for the maximum depth among the children. Each child depth is at most $D$ (`depth_le_maxDepth`), so the induction hypothesis and monotonicity of powers give $\mathrm{size}(c)+1\le 2^{D+1}$ for every child. The list-sum estimate `sumSize_add_length_le` now yields $\mathrm{sumSize}(cs)+|cs|\le |cs|\,2^{D+1}$. The gate has depth $D+1$ (`depth_node`) and size $1+\mathrm{sumSize}(cs)` (`size_node`). If the list is empty, its sum is zero and the result follows directly. If it has one child, the list-sum estimate bounds its size, giving the desired result. If it has two children, the estimate bounds the sum by $2\cdot 2^{D+1}=2^{D+2}$; substituting the gate size and depth gives the claim. These are all possible list lengths under the fanin bound.

**Key facts.** `BoolCircuit.TreeCircuit.ind`, `BoolCircuit.TreeCircuit.maxFanin_node`, `BoolCircuit.TreeCircuit.maxFanin_le_maxFaninL`, `BoolCircuit.TreeCircuit.depth_le_maxDepth`, `BoolCircuit.TreeCircuit.sumSize_add_length_le`, `BoolCircuit.TreeCircuit.depth_node`, `BoolCircuit.TreeCircuit.size_node`, `BoolCircuit.TreeCircuit.sumSize_nil`.
