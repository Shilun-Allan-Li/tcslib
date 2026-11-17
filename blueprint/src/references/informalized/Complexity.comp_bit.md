<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Logspace/QueryReshape.lean :: Complexity.comp_bit -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Input-Bit Oracle Answer

**Claim.** The first oracle in the four-language bank, queried on the encoding of $(h,\operatorname{bin}(i))$, returns the bit of $h$ at position $i$, with false returned beyond the end of $h$.

**Proof.** The first oracle is the input-bit oracle. Its value on a paired query is exactly the input-bit answer, as given by the input-bit oracle lemma (`Complexity.drop_bit`): it returns $h.getD(i,\mathrm{false})$.

**Key facts.** `Complexity.drop_bit`.
