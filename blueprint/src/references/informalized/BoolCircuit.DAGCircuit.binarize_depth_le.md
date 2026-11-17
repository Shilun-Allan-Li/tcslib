<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/DAGFanin.lean :: BoolCircuit.DAGCircuit.binarize_depth_le -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Depth of the binarized circuit

**Claim.** If each gate has distinct arguments and every negation gate has exactly one argument, then binarizing $C$ gives a circuit whose output depth is at most $(\lceil\log_2(\mathrm{size}(C))\rceil+1)$ times the depth of $C$.

**Proof.** The general depth bound for rewriting a circuit says that if every original gate is replaced by a correct gadget of depth overhead at most $c$, then the rewritten circuit's output depth is at most $c$ times the original output depth (`DAGCircuit.rewrite_depth_le`). Here binarization uses a balanced tree gadget: for a gate with $k$ arguments, its added depth is at most $\lceil\log_2 K\rceil+1$, where $K$ is the bound on the gate's argument count. The argument-count bound gives $k\le \mathrm{size}(C)$ for every gate, so take $K=\mathrm{size}(C)$. Substituting this value of $c$ into the rewrite depth bound yields the stated estimate.

**Key facts.** `BoolCircuit.DAGCircuit.rewrite_depth_le`.
