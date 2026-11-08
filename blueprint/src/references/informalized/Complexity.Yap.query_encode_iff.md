<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Randomized/Yap.lean :: Complexity.Yap.query_encode_iff -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Circuit Queries and Accepting Assignments

**Claim.** A query asking whether a fan-in-two circuit $C$ accepts the bit string $q$ holds exactly when there is an assignment $x$ to its inputs whose ordered bit string is $q$ and on which $C$ evaluates to true.

**Proof.** Suppose first that the query holds. By the definition of the yes-language, its encoded pair has a circuit witness $C'$ and an input string $q'$ on which $C'$ accepts. Injectivity of pair encoding (`Turing.pairEncode_injective`) identifies the query with the pair $(C.encode,q)$, so $q'=q$ and $C'.encode=C.encode$. Equality of circuit encodings forces the input counts to agree and the gate lists and outputs to agree (`BoolCircuit.DAGCircuit.eq_of_encode_eq`). Use the witness assignment on the coordinates indexed by $q'$ to define an assignment to $C$'s inputs. Its ordered bit string is $q$, and equality of evaluations for circuits with equal encodings and matching input lists (`Complexity.Yap.eval_eq_of_encode_eq`) transfers acceptance to $C$.

Conversely, suppose an assignment $x$ has ordered bit string $q$ and makes $C$ accept. Then the encoded pair of $C$ and that input string satisfies the defining conditions of the circuit value language, using the assumed fan-in-two property. This is exactly the query.

**Key facts.** `Turing.pairEncode_injective`, `BoolCircuit.DAGCircuit.eq_of_encode_eq`, `Complexity.Yap.eval_eq_of_encode_eq`.
