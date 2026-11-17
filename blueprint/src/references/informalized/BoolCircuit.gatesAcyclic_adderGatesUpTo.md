<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/Adder.lean :: BoolCircuit.gatesAcyclic_adderGatesUpTo -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Acyclicity of Partial Adder Lists

**Claim.** If $3k\le n$, then for every $i$, the partial ripple-carry adder list formed from two constant gates and $i$ successive bit blocks is acyclic.

**Proof.** Induct on the number $i$ of appended blocks. With zero blocks, the list consists of two constant gates, which have no inputs, so it is acyclic. For the induction step, split the list into the preceding partial list and the next bit block. The previous list is acyclic by induction. Its length is $2+15i$, so the next block is checked with starting bound $n+2+15i$ (length_adderGatesUpTo and gatesAcyclic_append). The input indices for the block’s two carry-related wires are below this bound by accIdx_lt and cinIdx_lt; the other required input bounds follow from $3k\le n$ and the block’s index formulas. Thus the block is acyclic at the shifted bound (gatesAcyclic_bitBlock), completing the induction.

**Key facts.** `BoolCircuit.RippleCarry.length_adderGatesUpTo`, `BoolCircuit.gatesAcyclic_append`, `BoolCircuit.accIdx_lt`, `BoolCircuit.cinIdx_lt`, `BoolCircuit.gatesAcyclic_bitBlock`.
