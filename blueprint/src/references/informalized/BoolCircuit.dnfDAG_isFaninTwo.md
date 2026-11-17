<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/BookModelBasics.lean :: BoolCircuit.dnfDAG_isFaninTwo -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Fan-In of the DNF Circuit

**Claim.** For every natural number $n$ and Boolean function $f$, the constructed DNF circuit is well formed: each gate has distinct arguments, every negation gate has exactly one input, and every gate has at most two inputs.

**Proof.** The minterm-tree specification (BoolCircuit.minterms_spec) and the final DNF-tree specification (BoolCircuit.dnf_spec) each state that their output gate lists extend their respective initial lists, and that every newly added gate has distinct arguments and at most two inputs. The initial list for the minterm construction consists of negation gates, each with its single input, so these gates have distinct arguments and fan-in one. Every later gate belongs to one of the two added portions: a gate added during minterm construction is an AND gate, while a gate added during the final construction is an OR gate. The specifications give both types distinct arguments and fan-in at most two. Since neither type is a negation gate, the condition that every negation gate has exactly one input holds for all gates in the final circuit. The same bounds establish the asserted fan-in property.

**Key facts.** `BoolCircuit.minterms_spec`, `BoolCircuit.dnf_spec`.
