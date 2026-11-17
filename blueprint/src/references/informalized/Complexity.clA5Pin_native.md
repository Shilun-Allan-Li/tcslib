<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CookLevin/Hardness.lean :: Complexity.clA5Pin_native -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Polynomial-Time Variable-Pinning Clause

**Claim.** The serialized clause group pinning the variable indexed by a polynomial-time computable index to the corresponding bit of a polynomial-time computable word is polynomial-time computable, using false when that index is out of range.

**Proof.** First compute the selected bit, defaulting to false when the index lies outside the word. The bit-extraction result (`clA5GetBit_native`) shows that this one-bit output is polynomial-time computable. Independently, the index can be encoded as a unary wire in polynomial time by hypothesis. The template result (`clA5Template_native`) then gives polynomial-time serialized clause groups for the unit clause asserting that this wire is true, and for the unit clause asserting that it is false. Choose between these two groups according to the extracted bit; polynomial-time conditional composition (`clA5_pt_cond`) preserves polynomial-time computability. In the true and false cases these groups are exactly the clauses pinning the indexed variable to the selected bit, respectively.

**Key facts.** `Complexity.clA5GetBit_native`, `Complexity.clA5Template_native`, `Complexity.clA5_pt_cond`.
