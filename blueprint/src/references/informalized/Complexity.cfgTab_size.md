<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/UniformTableauSpec.lean :: Complexity.cfgTab_size -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Configuration Tableau Circuit Size

**Claim.** The size of the configuration tableau circuit is $n+2+|z|+W\bigl((T+1)(k(2T+1)+(|z|+n)+3)+1\bigr)$, with $W$ the fixed instruction-block width.

**Proof.** Use the general tableau-circuit size formula (`BoolCircuit.tabCircuit_size`) for the program used to define the configuration tableau. Its number of instructions is $(T+1)$ times the configuration stride, by `Complexity.length_cfgProg`; the stride is $k(2T+1)+|z|+n+3$. The input layout has length $|z|+n$ (`Complexity.length_tabLayout`). Substituting these lengths into the general formula gives the stated size.

**Key facts.** `BoolCircuit.tabCircuit_size`, `Complexity.length_cfgProg`, `Complexity.length_tabLayout`.
