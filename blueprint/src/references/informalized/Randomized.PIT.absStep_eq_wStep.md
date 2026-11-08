<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Randomized/ZeroPEval.lean :: Randomized.PIT.absStep_eq_wStep -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Agreement of the Two Parsing Steps

**Claim.** For natural numbers $n,k$, a function $a\colon\mathbb{N}\to\mathbb{N}$, a bit string $w$, and a list $v$ of natural numbers, the algebraic-gate parsing transition and the validity-checking transition produce the same residual word and value list.

**Proof.** Split according to the initial bits of $w$. The empty word and the one-bit terminator $[0]$ are fixed by both transitions. A word beginning with $0$ and having at least two bits is rejected by the parsing transition; the validity test also fails, so both return the empty residual word and leave $v$ unchanged. For the remaining short words beginning with $1$, inspect their possible tag bits: these prefixes are too short to encode a complete gate, and both transitions reject them.

For a longer word, write it as a leading $1$, three tag bits, and a body. The identity for binary parsing ($\mathrm{decodeNat\_eq}$) identifies the two unary-decoded components of the body with $uHead$ and $uRest$, provided each contains a zero delimiter; without such a delimiter, parsing fails. Now split on the tag bits, on whether the body and its second component contain delimiters, and on the relevant index bound. These cases distinguish variable and constant gates from binary gates and reject malformed or out-of-range references. When a gate is valid, the decoded indices are exactly the lengths used by the validity test, and the gate’s computed value is exactly the value selected by $valN$: the variable, constant, sum, difference, and product cases agree respectively. Both transitions therefore remove the same encoded gate and append the same value. In every invalid case, both return the empty residual word and keep the value list unchanged. This exhausts the possible words and proves equality of the transitions.

**Key facts.** `Complexity.BinArith.decodeNat_eq`.
