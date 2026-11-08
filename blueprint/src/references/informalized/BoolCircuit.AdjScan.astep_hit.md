<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/LogspaceUniformScan.lean :: BoolCircuit.AdjScan.astep_hit -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# One-step gate-hit transition

**Claim.** If the scan instruction at label $l$ is the task’s hit instruction with successors $l_1,l_0$, then one step from registers $(p,c,a)$ preserves the registers and chooses $l_1$ exactly when $c=tv$.

**Proof.** Split on the task. For an edge task, the hit instruction compares the second component of the decoded pair of input words with the bits of register $c$. The target hypothesis identifies that second component with the binary representation of $tv$, so this comparison succeeds exactly when $c=tv$: injectivity of the natural-number bit representation (`Complexity.LogProg.bits_injective`) gives the equivalence. For a size or type task, the hit instruction instead compares the plain input word with the bits of $c$; the target hypothesis identifies that word with the bits of $tv$, and the same injectivity gives the same branch condition. In each case, the comparison instruction leaves all registers and the result unchanged, so the resulting configuration has the asserted form.

**Key facts.** `Complexity.LogProg.bits_injective`.
