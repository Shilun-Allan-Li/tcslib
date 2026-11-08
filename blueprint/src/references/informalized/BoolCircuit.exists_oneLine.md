<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/StraightLineSmall.lean :: BoolCircuit.exists_oneLine -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# One-line representation of a Boolean function

**Claim.** Every Boolean function of one input bit is computed by a valid straight-line program of length exactly one.

**Proof.** Let $a$ and $b$ be the function's values on the constant-false and constant-true inputs. Choose the one-line program furnished by the truth-table construction `oneLine` for the pair $(a,b)$. Its line evaluates the two selected input literals and combines them with the selected conjunction or disjunction. The evaluation formula for this program (`oneLine_eval`) says its output is exactly that operation on those literals. Since there is only one input bit, both selected input positions are index $0$. The construction's truth table therefore gives output $a$ when the input is false and $b$ when it is true. Every one-bit input is one of these two cases, so the program computes the given function; its length is one by construction.

**Key facts.** `BoolCircuit.oneLine_eval`.
