<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/TreeDAG.lean :: BoolCircuit.TreeCircuit.toDAG_isFaninTwo -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Fanin of Compiled Circuits

**Claim.** If a Boolean circuit tree has maximum fanin at most $2$, then every gate in its compiled directed acyclic circuit has at most two inputs, has no repeated input vertices, and any NOT gate has exactly one input.

**Proof.** By the well-formedness theorem for compiled trees (`BoolCircuit.TreeCircuit.toDAG_isWellFormed`), every compiled gate has no repeated inputs, and a NOT gate has exactly one input. It remains to bound the number of inputs. Start the compilation with no previously constructed gates; the empty gate list is acyclic (`BoolCircuit.GatesAcyclic.nil`), so the compilation specification applies (`BoolCircuit.compileTree_spec`). Its new-gate property says that each gate produced by compiling the tree has fanin bounded by the tree's maximum fanin. Since that maximum is at most $2$, every compiled gate has at most two inputs. Together these properties give the claimed fanin condition.

**Key facts.** `BoolCircuit.GatesAcyclic.nil`, `BoolCircuit.compileTree_spec`, `BoolCircuit.TreeCircuit.toDAG_isWellFormed`.
