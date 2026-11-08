<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter07/QuadraticCircuitReduction.lean :: FABL.BooleanCircuit.circuitQuadraticSystemDenseSize_le_cube -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Dense Size of the Quadratic System

**Claim.** The dense size of the circuit’s homogeneous quadratic system is at most $(n+g+2)^3$, where $g$ is the number of gates.

**Proof.** The system has $g+2$ equations, and each equation is represented densely using an $m\times m$ coefficient matrix, where the variable count is $m=n+g+1$. Hence its dense size is $(g+2)m^2$. Both factors satisfy $g+2\le n+g+2$ and $m\le n+g+2$. Multiplying these nonnegative bounds gives $(g+2)m^2\le(n+g+2)^3$. The equation count and variable count are supplied by `circuitQuadraticSystem_length` and `circuitQuadraticVariableCount_eq`.

**Key facts.** `FABL.BooleanCircuit.circuitQuadraticSystem_length`, `FABL.BooleanCircuit.circuitQuadraticVariableCount_eq`.
