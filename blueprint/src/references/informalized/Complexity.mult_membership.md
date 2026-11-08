<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Logspace/Mult.lean :: Complexity.mult_membership -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Multiplication encoding characterization

**Claim.** The nested pair encoding $\langle a,\langle b,c\rangle\rangle$ belongs to the multiplication language exactly when all three words are canonical and their little-endian binary values satisfy $\operatorname{val}(c)=\operatorname{val}(a)\operatorname{val}(b)$.

**Proof.** Suppose the nested encoding belongs to the language. It is therefore equal to the encoding built from the canonical binary words for some natural numbers $u$ and $v$, with product word representing $uv$. Injectivity of pair encoding, applied first to the outer pair and then to the inner pair, identifies $a,b,c$ with those three binary words. The canonicality lemma for natural-number bit words supplies canonicality of each, and the value-of-bits lemma gives the stated multiplication equation.

Conversely, suppose the three words are canonical and their values satisfy the equation. A canonical word is exactly the little-endian bit representation of its value, by `Complexity.LogProg.canon_eq_bits`. Replace each of $a,b,c$ by that representation. The assumed equation then identifies the third representation with the representation of the product of the first two values, so the nested encoding witnesses membership in the multiplication language.

**Key facts.** `Turing.pairEncode_injective`, `Complexity.LogProg.canon_bits`, `Complexity.LogProg.bitsVal_bits`, `Complexity.LogProg.canon_eq_bits`.
