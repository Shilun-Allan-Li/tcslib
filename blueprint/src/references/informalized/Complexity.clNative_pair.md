<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CookLevin/Hardness.lean :: Complexity.clNative_pair -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: low -->

# Polynomial-Time Pairing of Outputs

**Claim.** If $f$ and $g$ are polynomial-time computable, then the function sending $x$ to the encoded pair of $f(x)$ and $g(x)$ is polynomial-time computable.

**Proof.** First use the linear-time constructions for duplicating an encoded pair, extracting either component, concatenating encoded components, and producing the empty string; by the linear-time-to-polynomial-time result, each is polynomial-time computable. Also, polynomial-time computability is preserved by composition. The proof now builds the desired output through encoded-pair maps: it extracts $f(x)$, arranges it as the first component with an empty second component, and then applies the map that computes $g$ on a second component. The resulting nested encoding has the form of an encoded pair whose payload is itself a pair. A final pair extraction and concatenation rearranges that encoding into the encoding of $(f(x),g(x))$. The identities $\operatorname{decode}(\operatorname{encode}(u,v))=(u,v)$ and $\operatorname{encode}(a,b)\mathbin{++}c=\operatorname{encode}(a,b\mathbin{++}c)$ verify that these intermediate encodings simplify to the required output for every $x$. Since each operation is polynomial-time computable and composition preserves that property, the full function is polynomial-time computable.

**Key facts.** `Complexity.clNative_linear`, `Turing.FinTM.computesFunInTime_pairDup`, `Turing.FinTM.computesFunInTime_pairFst`, `Turing.FinTM.computesFunInTime_pairSnd`, `Turing.FinTM.computesFunInTime_pairConcat`, `Turing.FinTM.computesFunInTime_const`, `Complexity.clNative_map`, `Complexity.PolyTimeComputable.comp`, `Turing.pairDecode_pairEncode`.

**Caveat.** The proof’s intermediate composition terms are not fully expanded in the supplied source, so the exact sequence of encoded-pair rearrangements is difficult to recover; the account describes their stated extraction, mapping, and concatenation roles.
