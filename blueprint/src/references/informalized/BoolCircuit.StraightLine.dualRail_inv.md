<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/StraightLineDualRail.lean :: BoolCircuit.StraightLine.dualRail_inv -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Correctness of the Dual-Rail Construction

**Claim.** For an acyclic list of gates with at most two arguments per gate, the dual-rail construction produces one rail pair for each input or gate vertex. The statements and rails satisfy the validity and evaluation conditions of the dual-rail invariant, and the number of statements is at most twice the number of gates.

**Proof.** Proceed by induction on the gate list, building it from the end by appending one gate. For the empty list, the initial rail pair for each input consists of the input and its negation, and there are no statements; these directly satisfy the invariant (`dualInv_nil`).

For the induction step, write the list as an earlier acyclic list followed by a gate $g$. The earlier list is acyclic because its gate positions and arguments are unchanged. The induction hypothesis therefore gives the invariant for its constructed statements and rails. Acyclicity of the full list, applied at the final position, says that every argument of $g$ has index less than $n$ plus the length of the earlier list. Together with the bound of two arguments for $g$, these are precisely the hypotheses needed for the one-gate extension result (`dualInv_step`). Applying that result establishes all invariant clauses for the extended list: it adds the new rail pair, preserves valid references and correct evaluations, and increases the statement count by at most two. Since the fold defining the construction over the appended list is exactly this one-step extension of the earlier fold, the resulting invariant is the desired one.

**Key facts.** `BoolCircuit.StraightLine.dualInv_nil`, `BoolCircuit.StraightLine.dualInv_step`.
