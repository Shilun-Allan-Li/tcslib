<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/LayeredDAG.lean :: BoolCircuit.prod_b2f_getElem -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Conjunction as a Product of Bits

**Claim.** Encoding false by $0$ and true by $1$ in $\mathrm{Fin}(2)$, the product over the positions of a finite list $l$ of the encodings of $f(l_j)$ equals the encoding of the conjunction of the values of $f$ on the entries of $l$.

**Proof.** Induct on the list. For the empty list, the product is the multiplicative identity $1$, which is also the encoding of the empty conjunction, true. For a list with head $a$ and tail $l$, split off the factor at the head; the remaining product is the encoding of the conjunction over $l$ by induction. The head factor times this tail factor is the encoding of $f(a)\mathbin{\mathrm{and}}(l.\mathrm{all}\ f)$, because Boolean conjunction is multiplication of the corresponding bits (`BoolCircuit.b2f_and`). This is the conjunction over the whole list.

**Key facts.** `BoolCircuit.b2f_and`.
