<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/Adder.lean :: BoolCircuit.prefixVal_lt -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Binary Prefix Bound

**Claim.** For every Boolean sequence $f$ and every natural number $i$, its weighted prefix value below $i$ is strictly less than $2^i$.

**Proof.** Proceed by induction on $i$. At $i=0$, the prefix value is $0$, which is less than $1=2^0$. For the successor step, the successor formula (BoolCircuit.prefixVal_succ) writes the next prefix value as the old one plus $(f(i)).toNat\,2^i$. By the induction hypothesis the old value is less than $2^i$, and the Boolean value $(f(i)).toNat$ is at most $1$. Thus the new value is strictly less than $2^i+2^i=2^{i+1}$.

**Key facts.** `BoolCircuit.prefixVal_succ`.
