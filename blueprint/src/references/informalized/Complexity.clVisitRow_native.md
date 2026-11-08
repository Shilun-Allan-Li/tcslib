<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CookLevin/Hardness.lean :: Complexity.clVisitRow_native -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Polynomial-time computability of visit rows

**Claim.** For every finite Turing machine $M$ over Booleans and natural numbers $C,e$, the function sending a Boolean request to its visit row is polynomial-time computable.

**Proof.** Let $m(z)$ be the input length prescribed by the decoded first header field, and let $t(z)$ be the length of the decoded unary time field. First construct the all-false input of length $m(z)$: its length component comes from the decoded header, and its polynomial-size padding is supplied by the unary constructor for $C(|x|+1)^e$. The polynomial-time closure under composition and the polynomial-time append operation justify assembling this length; filling a word of a given length with a fixed bit is polynomial-time. Similarly, construct the all-true word of length $t(z)$ from the decoded tail. For each work tape, the previous-visit computation applied to these two constructed words is polynomial-time, by the visit-code computation result. There are finitely many tapes, so the list of their functions is finite; the result that packing a finite list of polynomial-time functions is polynomial-time now yields the visit row.

**Key facts.** `Complexity.clHeaderField_native`, `Complexity.PolyTimeComputable.comp`, `Complexity.clNative_unary`, `Complexity.clNative_append`, `Complexity.clNative_fill`, `Complexity.clHeaderTail_native`, `Complexity.clPrev_native`, `Complexity.clNative_fields`.
