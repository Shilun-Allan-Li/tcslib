<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Logspace/QueryReshape.lean :: Complexity.comp_suffix_run -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Suffix Search Run

**Claim.** Under the stated register bounds and initial values, the suffix-search machine halts with the specified answer: in mode, it tests whether the position lies before the end of the suffix; otherwise, it returns the corresponding bit of $b$, defaulting to false beyond the end. The step-validity condition and register bound hold throughout.

**Proof.** Write $n=2|f(x)|+2$ for the position immediately after the encoded output, and let $h$ be the full encoded input. The encoding-length formula (Turing.length_pairEncode) and the given initial-register equations yield $v_3=v_0+2|b|$. The bound on the full output and suffix gives $v_{13}+|b|\le B$, while the hypotheses also give $v_{13}\le v_5$. These are precisely the conditions for the suffix-search run lemma (comp_seek_run). It advances the search to the suffix hit when $v_5<v_{13}+|b|$, and otherwise reaches the negative answer state; both runs preserve the register bound and step-validity.

If $p<n+|b|$, the hit case applies. The search lemma places the input head at address $4|x|+4+2(p-n)$ and register $13$ at $p$. The register updates preserve the bound (register_update_le), using the derived address bound and $p\le B$. The address identity (comp_suffix_address) says that the bit of $h$ at this address is exactly the bit of $b$ at position $p-n$. The suffix-hit routine (comp_suffix_hit) therefore halts with true in mode and with that bit otherwise. Since the position is in range, the mode answer is exactly the stated comparison.

If $p\ge n+|b|$, the search lemma reaches the negative answer state. The bit of $b$ at position $p-n$ is false by the out-of-range convention, and the comparison is false as well. The false-answer routine (comp_ret) halts with that answer while respecting the register bound. Together, the two cases establish the claimed halt and answer.

**Key facts.** `Turing.length_pairEncode`, `Complexity.comp_seek_run`, `Complexity.LogProg.register_update_le`, `Complexity.comp_suffix_address`, `Complexity.comp_suffix_hit`, `Complexity.comp_ret`.
