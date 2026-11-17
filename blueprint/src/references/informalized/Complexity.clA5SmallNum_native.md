<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CookLevin/Hardness.lean :: Complexity.clA5SmallNum_native -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Polynomial-Time Bounded Interpretation

**Claim.** If $f$ and the unary encoding of $N$ are polynomial-time computable, then the unary encoding of $f(x)$ when $f(x)\le N(x)$, and of zero otherwise, is polynomial-time computable.

**Proof.** Use the polynomial-time construction that outputs the unary word of length $\operatorname{clNum}(f(x))$ when this value is at most $N(x)$, and the empty word otherwise (\texttt{clA5Decode\_native}). For each input $x$, split into the cases $\operatorname{clNum}(f(x))\le N(x)$ and $\operatorname{clNum}(f(x))>N(x)$. In the first case, the constructed output is already the desired unary word. In the second, it is empty, which is the unary word of length zero. Thus the constructed function agrees pointwise with the claimed function, so it has the same polynomial-time computability.

**Key facts.** `Complexity.clA5Decode_native`.
