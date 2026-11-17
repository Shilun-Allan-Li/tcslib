<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Machines/Parse.lean :: Complexity.LogProg.canon_eq_bits -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Canonical Words Encode Their Values

**Claim.** Every canonical Boolean word $w$ is exactly the binary bit word for its value, where the first bit is least significant.

**Proof.** Induct on $w$. For the empty word, both its value and its binary expansion are zero, so the claim holds. For a nonempty word $b::w$, the tail $w$ is canonical by the tail property (`canon_tail`), and induction identifies it with the binary expansion of its value. The value of $b::w$ is $b.toNat+2\,\mathrm{bitsVal}(w)$, which can be rewritten as $2\,\mathrm{bitsVal}(w)+b.toNat$. The binary-expansion rule for doubling and adding a bit (`bits_two_mul_add`) then gives the word $b$ followed by the expansion of the tail's value. Its side condition says that if the tail's value is zero, then $b$ must be true. In that case, the induction equality makes the tail the binary expansion of zero, hence empty; canonicality of the original word then forces its final bit $b$ to be true, establishing the side condition. Thus the expansion is exactly $b::w$.

**Key facts.** `Complexity.LogProg.canon_tail`, `Complexity.LogProg.bits_two_mul_add`.
