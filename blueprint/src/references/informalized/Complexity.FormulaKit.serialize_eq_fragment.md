<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/FormulaKit/Emit.lean :: Complexity.FormulaKit.serialize_eq_fragment -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Formula Encoding and Clause Fragment

**Claim.** The encoding of a CNF formula is its clause-fragment encoding followed by one false bit.

**Proof.** By definition, serialization forms the concatenation of each clause marker and its clause encoding, then appends one false bit. The fragment is precisely that concatenation before the final bit, so the stated identity follows directly from the definitions.
