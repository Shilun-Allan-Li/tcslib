<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/UniformTableauEmitterInstr.lean :: Complexity.UTab.baseE_val -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Value of the Base Expression

**Claim.** When the input-length register is $n$ and the fixed-string-length register is $|z|$, the base expression evaluates to $n+2+|z|+W(i+1)$, where $i$ is the instruction register and $W$ is the table width.

**Proof.** The base expression has register list consisting of the input-length register, the fixed-string-length register, and $W$ copies of the instruction register, with constant term $2+W$. Evaluating its register list therefore gives $e.nc+e.z+W e.i$. The register lookup facts identify the three register values with $e.nc,e.z,e.i$ respectively (`ER.f_nc`, `ER.f_z`, and `ER.f_i`). Substituting the hypotheses $e.nc=n$ and $e.z=|z|$, the total is $n+|z|+Wi+2+W$. Rearranging yields $n+2+|z|+W(i+1)$, the defining value of the table base.

**Key facts.** `Complexity.UTab.ER.f_nc`, `Complexity.UTab.ER.f_z`, `Complexity.UTab.ER.f_i`.
