<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/Parity.lean :: BoolCircuit.xorFuel_eval -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Evaluation of XOR reduction

**Claim.** Given a list of pairs whose second circuits evaluate to the complements of their first circuits, the first circuit returned by the fuel-bounded XOR reduction evaluates to the iterated exclusive OR of the original first circuits, and the returned circuits evaluate to complementary values.

**Proof.** Induct on the fuel, splitting into the empty list, a singleton, and a list with at least two pairs. For the empty list, the reduction returns a false-valued first circuit and a true-valued second circuit, matching the empty exclusive-OR fold and giving complementary values. A singleton is returned unchanged: its first evaluation is the one-term exclusive-OR fold, and the assumed complementarity gives the second conclusion.

For a list with at least two pairs, one round replaces each consecutive pair by the pair constructed by one XOR step. The length formula for this round shows that the new list has length at most the reduced fuel. Each new pair is dual, by the preservation-of-duality fact for the pairing round (`isDual_xorPairUp`), so the induction hypothesis applies. It identifies the returned first circuit's evaluation with the exclusive-OR fold over the paired list and says the returned pair is dual. The fold is unchanged by pairing under the duality hypothesis (`xorAll_xorPairUp`); hence the first evaluation is the fold over the original list, while the duality conclusion supplies the required complementarity.

**Key facts.** `BoolCircuit.length_xorPairUp`, `BoolCircuit.isDual_xorPairUp`, `BoolCircuit.xorAll_xorPairUp`.
