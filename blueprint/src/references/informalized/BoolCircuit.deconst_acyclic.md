<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/StrictCircuit.lean :: BoolCircuit.deconst_acyclic -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Acyclicity After Removing Constants

**Claim.** If $n>0$ and $G$ is acyclic relative to $n$ inputs, then prefixing the three constant-construction gates and replacing each gate of $G$ by its strict version yields an acyclic list relative to the same inputs.

**Proof.** Use the append characterization of acyclicity (BoolCircuit.gatesAcyclic_append): it suffices to verify the three-gate prefix relative to $n$ inputs and the transformed list relative to $n+3$ inputs. For the prefix, the three gates read respectively $0$, then $0,n$, then $0,n$. These indices are within the available earlier vertices at their respective positions; the required inequalities follow from $n>0$. The empty-tail and one-gate decomposition rules for acyclicity (BoolCircuit.gatesAcyclic_cons and BoolCircuit.gatesAcyclic_nil) reduce this check to those inequalities. For a gate at position $i$ in $G$, its position after the prefix is $i+3$. The strict-gate argument characterization (BoolCircuit.strictGate_args) says each of its inputs is either a shifted original argument, $n+1$, or $n+2$. An original argument is less than $n+i$ by the assumed acyclicity of $G$; the shift bound (BoolCircuit.shiftPrefix_lt) places its shifted index below $n+3+i$. The two added constant indices also lie below $n+3+i$. Hence every transformed gate reads only an earlier vertex.

**Key facts.** `BoolCircuit.gatesAcyclic_append`, `BoolCircuit.gatesAcyclic_cons`, `BoolCircuit.gatesAcyclic_nil`, `BoolCircuit.strictGate_args`, `BoolCircuit.shiftPrefix_lt`.
