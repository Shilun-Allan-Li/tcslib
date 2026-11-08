<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/FormulaFanOut.lean :: BoolCircuit.compileTree_fanout -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Fanout of a Compiled Circuit

**Claim.** Compiling a circuit tree after an acyclic gate list appends gates with the stated fanout properties: old gate vertices are not read, each vertex of index at least the input count is read at most once, the root is unread when its index is not an input, and every new vertex other than the root is read exactly once.

**Proof.** Proceed by structural induction on the circuit tree. For a negative literal, compilation appends one NOT gate and takes its new vertex as root. Its sole input is an input vertex, so it reads no vertex of index at least $n$; the root is therefore unread, and there are no other new vertices to check. For a positive literal, compilation appends nothing and returns the input vertex. All fanout counts in the appended list are zero, and the root is an input vertex.

Now let the circuit be a node with children $cs$. Compile the children first. By the list fanout result (`BoolCircuit.compileTrees_fanout`), this yields an extension $e$ and child-root list $r.2$ with the required list-level fanout properties. The specification of compiling a list (`BoolCircuit.compileTrees_spec`) supplies acyclicity of the intermediate gate list and ensures that the new node gate's inputs, obtained by deduplicating the child roots, are valid earlier vertices. Append this node gate $g$. Its fanout contribution is exactly one for each child root and zero otherwise (`BoolCircuit.fanoutIn_singleton`), and counts add across concatenated gate lists (`BoolCircuit.fanoutIn_append`).

For an old gate vertex, the child extension and the new gate both contribute zero: the former by the induction properties, and the latter because such a vertex cannot be a newly produced child root. For any vertex of index at least $n$, the child extension contributes at most one; the added gate contributes one only if that vertex is a child root. In that case the child-root unread property makes its contribution from the extension zero, so the total remains at most one. The final root is the index of the appended node gate. Acyclicity of the intermediate list implies this index is not among the child roots, hence it is unread. It is a new vertex, and is therefore at least $n+|gs|$. Finally, consider a vertex in the new range beyond the old gates and below the end of the extended list, other than the final root. If it lies in the child extension's range, the child result makes it occur exactly once as an input; the added gate cannot read it because it is not a child root. If it is the new node's vertex, it is excluded as the final root. This proves the required exact-once property.

**Key facts.** `BoolCircuit.TreeCircuit.ind`, `BoolCircuit.compileTrees_fanout`, `BoolCircuit.compileTrees_spec`, `BoolCircuit.fanoutIn_singleton`, `BoolCircuit.fanoutIn_append`, `BoolCircuit.fanoutIn_ext_eq_zero`.
