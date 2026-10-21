<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/ErrorCorrectingCodes/QuantumSingleton.lean :: orth_inter_eq_orth_map -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: claude-opus-4-8; confidence: high -->

# Restriction to a Support and the Symplectic Complement

**Claim.** Fix a prime $p$ and work in the symplectic space $V = \mathbb{F}_p^{\,n} \times \mathbb{F}_p^{\,n}$ with the form $\omega\big((x,z),(x',z')\big) = \sum_{i=0}^{n-1}(x_i z'_i - z_i x'_i)$. For a subset $M \subseteq \{0,\dots,n-1\}$ write $V_M$ for the subspace of vectors whose support lies in $M$, and $r_M\colon V \to V$ for the linear map that zeroes every coordinate outside $M$ and leaves those in $M$ untouched. The claim is that for every $\mathbb{F}_p$-subspace $S \le V$, the parts of $S^{\perp_\omega}$ and of $(r_M(S))^{\perp_\omega}$ that live inside $V_M$ coincide:
\[
S^{\perp_\omega} \cap V_M \;=\; \big(r_M(S)\big)^{\perp_\omega} \cap V_M .
\]
In words: once we test orthogonality only against vectors already supported on $M$, it makes no difference whether we take the complement of $S$ or of its restriction $r_M(S)$.

**Proof.** The whole argument rests on a single symmetry of the form, after which the equality of the two sides is a matter of unwinding what membership in an orthogonal complement means.

**The restriction identity.** The decisive fact is that for any $s \in V$ and any $v \in V_M$,
\[
\omega\big(r_M(s),\,v\big) \;=\; \omega(s,\,v)
\]
(this is `sym_form_left_restrict`). It is worth seeing why: expanding the form,
\[
\omega(r_M(s), v) = \sum_{i=0}^{n-1}\Big( (r_M s)_{x,i}\, v_{z,i} - (r_M s)_{z,i}\, v_{x,i}\Big).
\]
For an index $i \in M$ the map $r_M$ changes nothing, so $(r_M s)_{\bullet,i} = s_{\bullet,i}$ and the $i$-th term already agrees with the $i$-th term of $\omega(s,v)$. For an index $i \notin M$ two things happen at once: $r_M$ kills the entry, so $(r_M s)_{\bullet,i} = 0$, and — because $v$ is supported on $M$ — the entries $v_{x,i}$ and $v_{z,i}$ also vanish. Hence the $i$-th term is $0$ on the left, and on the right it is $s_{x,i}\cdot 0 - s_{z,i}\cdot 0 = 0$ as well. Summing, the two forms are equal. The hypothesis $v \in V_M$ is exactly what is needed to make the outside-$M$ terms disappear on both sides simultaneously; this is why the identity holds only after intersecting with $V_M$.

Recall also that membership $v \in S^{\perp_\omega}$ unwinds to the condition $\omega(s, v) = 0$ for every $s \in S$, with the vector ranging over the subspace sitting in the left slot of the form. (That the abstract bilinear form agrees with the explicit sum $\omega$ is the definitional identity `symB_apply`, which we use silently throughout.)

Now fix $v \in V_M$; we show $v \in S^{\perp_\omega}$ if and only if $v \in (r_M(S))^{\perp_\omega}$. Since both sides of the asserted equality carry the same intersection with $V_M$, this is all that is at issue.

1. **$S^{\perp_\omega} \cap V_M \subseteq (r_M(S))^{\perp_\omega} \cap V_M$.** Suppose $v \in S^{\perp_\omega}$ and $v \in V_M$. A general element of $r_M(S)$ has the form $r_M(s)$ with $s \in S$. By the restriction identity, $\omega(r_M(s), v) = \omega(s, v)$, and the right-hand side is $0$ because $v$ is orthogonal to all of $S$. Thus $v$ is orthogonal to every element of $r_M(S)$, i.e. $v \in (r_M(S))^{\perp_\omega}$.

2. **$(r_M(S))^{\perp_\omega} \cap V_M \subseteq S^{\perp_\omega} \cap V_M$.** Suppose $v \in (r_M(S))^{\perp_\omega}$ and $v \in V_M$. Let $s \in S$ be arbitrary. Then $r_M(s)$ lies in $r_M(S)$, so by hypothesis $\omega(r_M(s), v) = 0$. Applying the restriction identity once more gives $\omega(s, v) = \omega(r_M(s), v) = 0$. As $s$ was an arbitrary element of $S$, we conclude $v \in S^{\perp_\omega}$.

The two inclusions give the claimed equality. Note that the argument is genuinely symmetric in the two directions: each uses the same identity $\omega(r_M(s), v) = \omega(s, v)$, read once from left to right and once from right to left, and in both cases the restriction to $V_M$ is what licenses it.

**Key facts.** `sym_form_left_restrict`.
