<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassP/BinaryArith/Loops.lean :: Complexity.BinArith.hasFalse_cons -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# False Bits After Prepending

**Claim.** For a Boolean $b$ and a Boolean list $w$, the list $b::w$ contains a false entry exactly when $b$ is false or $w$ contains a false entry.

**Proof.** The false-bit test scans the list for an entry whose negation is true. On the list with head $b$, such an entry occurs either at the head, precisely when $b$ is false, or in the tail, precisely when the tail's false-bit test is true. Thus the result is the disjunction of those two conditions.
