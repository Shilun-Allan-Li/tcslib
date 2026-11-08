<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassPSPACE/TQBFARM/Semantics.lean :: Complexity.LogProg.TQBFARM.val_root -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Root Valuation Encoding

**Claim.** The valuation at depth zero with number $1$ holds exactly when the quantified Boolean formula decoded from the paired encoding of the prefix and serialized matrix is true.

**Proof.** The decoding theorem for a paired encoding (`Complexity.LogProg.TQBFARM.decode_pairEncode`) identifies the decoded formula with the prefix mapped to its corresponding quantifiers and the original matrix. At depth zero, the encoded assignment is the constantly false assignment, by `Complexity.LogProg.TQBFARM.asg_zero`. Unfolding the definitions of valuation and quantified truth then gives the same quantified-truth expression on both sides, proving the equivalence.

**Key facts.** `Complexity.LogProg.TQBFARM.decode_pairEncode`, `Complexity.LogProg.TQBFARM.asg_zero`.
