<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CookLevin/Hardness.lean :: Complexity.clA5Iter_native -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Polynomial-Time Bounded Iteration

**Claim.** If $f$ and $s$ are polynomial-time computable, the unary encoding of $N$ is polynomial-time computable, and all iterates up to $N(x)$ have the stated quadratic length bound, then $x\mapsto f^{N(x)}(s(x))$ is polynomial-time computable.

**Proof.** Choose a machine $W$ computing $f$ together with entry and exit states and a polynomial time bound for each call (`clNative_cleanCall`). A polynomial-time construction packages the initial word $s(x)$ and a unary counter for $N(x)$ into a repeated-call argument (`clRepeatArgument_native`). The lengths of both $s(x)$ and the unary counter are bounded by the length of this package (`clFields_width`). Thus the assumed orbit bound implies that every intermediate iterate has length at most $4K(L+1)^2$, where $L$ is the package length; this follows by bounding $|s(x)|+N(x)+1$ by $2(L+1)$.

The repeated-call simulation runs $W$ successively, using the counter to make exactly $N(x)$ calls. The call bound and the orbit-length bound give a polynomial runtime for this simulation (`clRepeatOutput_compute`). The polynomial budget inequality `clRepeat_budget`, using $N(x)\le L$, places that runtime under a polynomial in $L$. Since the packaged argument itself is polynomial-time computable, the polynomial-time image principle (`clNative_image`) yields the desired iterated function.

**Key facts.** `Complexity.clNative_cleanCall`, `Complexity.clRepeatArgument_native`, `Complexity.clFields_width`, `Complexity.clRepeatOutput_compute`, `Complexity.clRepeat_budget`, `Complexity.clNative_image`.
