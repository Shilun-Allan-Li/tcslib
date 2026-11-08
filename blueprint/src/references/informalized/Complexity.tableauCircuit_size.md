<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/PSubsetPPolyTableau.lean :: Complexity.tableauCircuit_size -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Size of the Tableau Circuit

**Claim.** For every finite-state Turing machine $M$ with Boolean input and output and all natural numbers $n,T$, the tableau circuit has size $n+2+(T+1)W$, where $W$ is the tableau width determined by $M$.

**Proof.** The circuit size is its input width plus its number of gates. The tableau circuit uses the gate list through time $T+1$, whose length is $2+(T+1)W$ by the gate-count formula (Complexity.length_tableauGates). Therefore its size is $n+2+(T+1)W$, as claimed.

**Key facts.** `Complexity.length_tableauGates`.
