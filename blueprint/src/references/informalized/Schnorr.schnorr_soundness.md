<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Cryptography/SchnorrProtocol.lean :: Schnorr.schnorr_soundness -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Special soundness of Schnorr

**Claim.** If two accepted Schnorr transcripts use the same commitment and distinct challenges, then the extracted quotient of response difference by challenge difference equals the witness in $\mathbb{Z}_q$.

**Proof.** Acceptance gives $g^{s_1}=a(g^w)^{c_1}$ and $g^{s_2}=a(g^w)^{c_2}$. Multiply the first equality by $(g^w)^{c_2}$ and the second by $(g^w)^{c_1}$. Commutativity makes the right sides equal, so the left sides are equal as well. The laws of exponents rewrite this as $g^{s_1+w c_2}=g^{s_2+w c_1}$. Since $g$ has order $q$, two powers of $g$ are equal exactly when their exponents are congruent modulo $q$; hence $s_1+w c_2=s_2+w c_1$ in $\mathbb{Z}_q$. Rearranging yields $s_1-s_2=w(c_1-c_2)$. Distinctness of the challenges implies $c_1-c_2\ne0$, so it is invertible in the field $\mathbb{Z}_q$. Dividing the displayed identity by this difference gives the claimed extraction formula.
