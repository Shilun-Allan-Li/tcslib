<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/TreeNCAC.lean :: BoolCircuit.maxFaninL_pairUp -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Fan-In of Paired Circuits

**Claim.** Pairing consecutive circuits into gates produces a list whose maximum fan-in is at most the larger of two and the original list’s maximum fan-in.

**Proof.** Proceed by induction, with separate empty-list, singleton, and two-head cases. The empty list has maximum fan-in zero, while a singleton is unchanged and therefore satisfies the bound. For a list beginning with $c_1,c_2$, the new leading node has two children, so its fan-in is the maximum of $2$ and the maximum fan-in of its children. The node fan-in formula (`BoolCircuit.TreeCircuit.maxFanin_node`), together with the list maximum formulas (`BoolCircuit.TreeCircuit.maxFaninL_cons`, `BoolCircuit.TreeCircuit.maxFaninL_nil`), gives its fan-in as $\max(2,\max(c_1.\mathrm{maxFanin},\max(c_2.\mathrm{maxFanin},0)))$. The induction hypothesis bounds the paired remainder by the larger of two and the original remainder’s maximum. Taking the maximum with the leading node’s fan-in yields the claimed bound for the full list.

**Key facts.** `BoolCircuit.TreeCircuit.maxFanin_node`, `BoolCircuit.TreeCircuit.maxFaninL_cons`, `BoolCircuit.TreeCircuit.maxFaninL_nil`.
