<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/UnaryLogspace.lean :: Complexity.indexLang_unaryExt -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Unary Extension of an Indexed Language

**Claim.** Under the stated hypotheses on $p$ and $q$, the indexed language for $p$ consists exactly of encodings whose first component is a unary string $1^n$ and for which $q(n,i)$ holds.

**Proof.** To prove the forward inclusion, take an encoding witnessing membership in the indexed language, so it has the form $\operatorname{pairEncode}(x,\operatorname{bits}(i))$ with $p(x,i)$. The first hypothesis forces $x$ to be the all-ones string of its own length and preserves $p(x,i)$. Set $n=|x|$; then $x=1^n$, and the second hypothesis gives $q(n,i)$. Thus the same word witnesses membership in the claimed unary description. Conversely, a word witnessed there has the form $\operatorname{pairEncode}(1^n,\operatorname{bits}(i))$ with $q(n,i)$. The second hypothesis yields $p(1^n,i)$, which directly witnesses membership in the indexed language.
