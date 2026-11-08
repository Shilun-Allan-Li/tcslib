<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/Adder.lean :: BoolCircuit.prefixVal_succ' -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Shifted Successor Formula

**Claim.** For every Boolean sequence $f$ and natural number $i$, its weighted prefix value below $i+1$ equals $(f(0)).toNat$ plus twice the weighted prefix value below $i$ of the shifted sequence $j\mapsto f(j+1)$.

**Proof.** Use induction on $i$. For $i=0$, the prefix value at $1$ consists only of the contribution from position $0$, giving $(f(0)).toNat$. For the successor step, first express the prefix value at $i+2$ by the successor formula (BoolCircuit.prefixVal_succ), then apply the induction hypothesis to the prefix below $i+1$. The shifted sequence contributes its next term $(f(i+1)).toNat\,2^i$; after multiplying by $2$, this is $(f(i+1)).toNat\,2^{i+1}$. The resulting terms are precisely the initial bit and the shifted prefix expansion, and rearranging them gives the claimed formula.

**Key facts.** `BoolCircuit.prefixVal_succ`.
