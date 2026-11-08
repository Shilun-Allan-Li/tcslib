<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Logspace/QueryReshape.lean :: Complexity.comp_rejected_tail -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Rejection of an Invalid Tail

**Claim.** If the tail is not both canonical and short enough to fit within the binary representation of the stated bound, then the specified language indicator is false on the encoded pair $\langle z,\mathrm{tail}\rangle$.

**Proof.** Split according to whether the tail is canonical. If it is canonical, the canonical-word representation theorem (\texttt{canon\_eq\_bits}) writes it as $\mathrm{bits}(p)$ for some $p$. Since the pair of canonicality and the stated width bound fails, the width bound must fail: the binary representation of $(2C+3)(|\langle z,\mathrm{bits}(p)\rangle|+1)^{e+1}$ is strictly shorter than $\mathrm{bits}(p)$. The query-overflow lemma (\texttt{compQ\_query\_overflow}) then says that the queried bit is false and the purported output length does not reach index $p$. Unfolding the language on a properly encoded pair via \texttt{comp\_lang\_pair} gives a false answer in either mode: the bit answer is false, and the length-mode comparison fails.

If the tail is not canonical, suppose for contradiction that the encoded input belonged to the language. The bad-query exclusion lemma (\texttt{comp\_bad\_query}) would then provide a representation of the input as a pair whose second component is a binary word. Injectivity of pair encoding (\texttt{pairEncode\_injective}) forces that component to equal the original tail. But every binary word is canonical (\texttt{canon\_bits}), contradicting the assumption. Thus the indicator is false in this case as well.

**Key facts.** `Complexity.LogProg.canon_eq_bits`, `Complexity.compQ_query_overflow`, `Complexity.comp_lang_pair`, `Complexity.comp_bad_query`, `Turing.pairEncode_injective`, `Complexity.LogProg.canon_bits`.
