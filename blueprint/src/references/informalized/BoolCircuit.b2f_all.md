<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/LayeredDAG.lean :: BoolCircuit.b2f_all -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Boolean conjunction as a product

**Claim.** Encoding the conjunction of Boolean values over a list in $\mathrm{Fin}(2)$ gives the product of their individual encodings.

**Proof.** Induct on the list. For the empty list, the conjunction is true and the empty product is $1$, so the encodings agree. For a head $a$ and tail $l$, the list conjunction is the conjunction of $f(a)$ with the tail conjunction, while the mapped list's product is the encoding of $f(a)$ times the product for the tail. The identity that encoding Boolean conjunction as multiplication (`BoolCircuit.b2f_and`), together with the induction hypothesis, identifies these expressions.

**Key facts.** `BoolCircuit.b2f_and`.
