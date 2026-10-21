<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/ErrorCorrectingCodes/QuantumSingleton.lean :: sym_form_sub_nondegenerate -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: claude-opus-4-8; confidence: high -->

# Nondegeneracy of the restricted symplectic form

**Claim.** Fix a prime $p$ and equip $V = \mathbb{F}_p^n \times \mathbb{F}_p^n$ with the symplectic form $\omega\big((x,z),(x',z')\big) = \sum_{i=0}^{n-1}(x_i z'_i - z_i x'_i)$. For a subset $M \subseteq \{0,\dots,n-1\}$ let $V_M$ be the support submodule of those $(x,z)$ with $x_i = z_i = 0$ for all $i \notin M$. Then the restriction of $\omega$ to $V_M$ is nondegenerate: any $u \in V_M$ with $\omega(u,v) = 0$ for every $v \in V_M$ is zero.

**Proof.** The claim is phrased as nondegeneracy of the bilinear form obtained by restricting $\omega$ to the submodule $V_M$. By construction this restricted form is $\omega$ composed with the inclusion $V_M \hookrightarrow V$ in both arguments, so evaluating it on two members $v,w$ of $V_M$ returns nothing other than $\omega$ of their underlying ambient vectors. The entire argument then transports a nondegeneracy fact already proved on the ambient space — if $u \in V_M$ is $\omega$-orthogonal to all of $V_M$ then $u = 0$ (`sym_form_nondegenerate_on_V_sub`) — across this repackaging.

1. **Unfold nondegeneracy.** Let $v \in V_M$ and suppose the restricted form vanishes against every $w \in V_M$. Because the restricted form is $\omega$ precomposed with the inclusion on both slots, this hypothesis says precisely that $\omega(v, w) = 0$ for every $w \in V_M$ (reading $v,w$ as their ambient vectors in $V$). The goal is $v = 0$.

2. **Pass to the contrapositive.** Argue by contradiction and assume $v \neq 0$. It suffices to exhibit some $w \in V_M$ with $\omega(v, w) \neq 0$, for that single $w$ already contradicts the orthogonality hypothesis of step 1.

3. **Produce the witness from the ambient lemma.** The existence of such a $w$ is exactly the contrapositive of the ambient nondegeneracy fact (`sym_form_nondegenerate_on_V_sub`): that lemma states that any ambient vector lying in $V_M$ and $\omega$-orthogonal to every member of $V_M$ must be zero. Were there no $w \in V_M$ with $\omega(v,w) \neq 0$, then $v$ would be orthogonal to all of $V_M$; as $v$ itself lies in $V_M$, the lemma would force $v = 0$, against the assumption $v \neq 0$. Hence some $w \in V_M$ with $\omega(v, w) \neq 0$ does exist. (Matching the existential goal to this contrapositive is routine bookkeeping.)

4. **Close the contradiction.** For that $w$, step 1 gives $\omega(v, w) = 0$, directly contradicting $\omega(v, w) \neq 0$. The assumption $v \neq 0$ is therefore untenable, so $v = 0$, which is what nondegeneracy demands.

**Key facts.** `sym_form_nondegenerate_on_V_sub`.
