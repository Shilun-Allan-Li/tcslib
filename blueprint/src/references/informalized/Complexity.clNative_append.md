<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CookLevin/Hardness.lean :: Complexity.clNative_append -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Closure Under Concatenation

**Claim.** If $f$ and $g$ are polynomial-time computable functions from binary words to binary words, then the function $x\mapsto f(x)g(x)$ is polynomial-time computable.

**Proof.** First compute the paired encoding of the two values, $\operatorname{pairEncode}(f(x),g(x))$, using polynomial-time computability of pairing (`Complexity.clNative_pair`). A machine that decodes such a pair and concatenates its two components runs in linear time (`Turing.FinTM.computesFunInTime_pairConcat`), so its function is polynomial-time computable (`Complexity.clNative_linear`). Compose this linear-time concatenation procedure with the pairing computation; polynomial-time computable functions are closed under composition (`Complexity.PolyTimeComputable.comp`). Finally, decoding the encoding of $f(x),g(x)$ returns exactly that pair (`Turing.pairDecode_pairEncode`), so the composite outputs $f(x)g(x)$.

**Key facts.** `Complexity.clNative_pair`, `Turing.FinTM.computesFunInTime_pairConcat`, `Complexity.clNative_linear`, `Complexity.PolyTimeComputable.comp`, `Turing.pairDecode_pairEncode`.
