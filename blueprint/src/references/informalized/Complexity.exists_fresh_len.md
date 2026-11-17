<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Diagonalization/Relativization.lean :: Complexity.exists_fresh_len -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: low -->

# A Length Exceeding Exponential and Polynomial Bounds

**Claim.** For any natural numbers $i,b$, some $n$ exceeds $b$, satisfies $i+2\le n$, and has $n^i+i<2^n$.

**Proof.** Set $m=i+b+1$ and choose $n=2^{2^m}$. First, $2m\le2^m$ and $m<2^m$ by the elementary inequality $r<2^r$ (with the first estimate obtained by applying it to $m-1$). These imply $n>b$ and $i+2\le n$. To prove the final inequality, it is enough to compare exponents after writing $n^i=2^{2^m i}$. The inequality $i+1\le2^i$ gives $2^m i+1\le2^m2^i\le2^{2^m}$; the second inequality follows from $m+i\le2^m$. Hence $n^i\le2^{2^{2^m}-1}$. If $i>0$, then $i<2^{2^m i}$, so adding $i$ still leaves $n^i+i<2^{2^{2^m}}=2^n$. If $i=0$, the desired inequality reduces to $1<2^n$, which holds since $n>0$.

**Caveat.** The proof source's exponent comparison steps are not fully transparent from the supplied text, and the displayed derivation above does not establish the key bound $m+i\le 2^m$ for every $i,b$ (nor does that bound follow from the preceding estimates as stated).
