<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/CircuitSatReductionValid.lean :: BoolCircuit.CktSatReduction.T_ones -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Preservation of Leading Ones

**Claim.** If reading a $1$ from state $q$ leaves the state unchanged and outputs $1$, then for every natural number $k$ and finite bit string $r$, processing $k$ consecutive $1$s followed by $r$ from $q$ preserves those $k$ leading $1$s and then processes $r$ from $q$.

**Proof.** Induct on $k$. When $k=0$, the input is just $r$, so the identity is immediate. For the successor case, separate the first $1$ from the remaining $k$ ones and suffix. The hypotheses say that this bit is output unchanged and the state remains $q$. The induction hypothesis applied to the remaining input gives the stated output (`T_cons`).

**Key facts.** `BoolCircuit.CktSatReduction.T_cons`.
