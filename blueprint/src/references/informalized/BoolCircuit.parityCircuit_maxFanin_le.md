<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/Parity.lean :: BoolCircuit.parityCircuit_maxFanin_le -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Parity circuit fanin bound

**Claim.** For every natural number $n$, the maximum fanin of the parity circuit on $n$ Boolean variables is at most $2$.

**Proof.** Apply the fanin bound for the XOR construction (`xorFuel_fanin`) to the list of literal pairs for the $n$ variables, taking the fuel to be the list's length. Its length therefore satisfies the required hypothesis. The pair fanin of this list is zero (`pairFanin_parityPairs`), since each pair consists only of literals. Thus both output circuits have maximum fanin at most $\max(2,0)=2$. The parity circuit is the first component of this output pair, so its maximum fanin is at most $2$ as well.

**Key facts.** `BoolCircuit.xorFuel_fanin`, `BoolCircuit.pairFanin_parityPairs`.
