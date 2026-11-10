<!-- generated-by: Codex source review of scoped excerpts -->
<!-- source-pdf-sha256: c0f87bf2e871180d62b2b27d38b916bce1a7b2228dbb68de72341597341d6d87 -->
<!-- validation-status: scoped excerpts for PR #237 -->

# CS 395T Topics in Cryptography

David Wu, Spring 2024 lecture notes. Compilation last updated 30 April 2024.

This excerpt covers Definition 20.5 and its correctness discussion, followed
by the security argument in Lecture 21. The anchors refer to pages 83 and 85
of the original PDF. The accompanying source review records the adaptations
in the formal statements.

<a id="pdf-c0f87bf2e871-p083-b001"></a>
<!-- pdf-source: page=83; block=1; confidence=0.95 -->

**Definition 20.5 (Regev Symmetric Encryption Scheme).** The definition of the scheme follows below:

* $\mathrm{Setup}(1^\lambda)$: Output $s\stackrel R\leftarrow\mathbb Z_q^n$.
* $\mathrm{Encrypt}(s,\mu\in\{0,1\})$: Sample $a\stackrel R\leftarrow\mathbb Z_q^n$ and $e\stackrel R\leftarrow\chi$. Output $\mathrm{ct}=(a,s^Ta+e+\mu\lfloor q/2\rfloor)$
* $\mathrm{Decrypt}(s,\mathrm{ct}=(c_1,c_2))$: Output $\lfloor c_2-s^Tc_1\pmod q\rceil_{q,2}$, where $\lfloor\cdot\rceil$ is the rounding operation and
  $\lfloor x\rceil_{q,2}:=\left\lfloor\frac2q\cdot x\right\rceil$.

**Correctness** Let $\mathrm{ct}=(c_1,c_2)\leftarrow\mathrm{Encrypt}(s,\mu)$. It follows that

$$
\begin{aligned}
\lfloor c_2-s^Tc_1\pmod q\rceil_{q,2}
&=\left\lfloor s^Ta+e+\mu\left\lfloor\frac q2\right\rfloor-s^Ta\pmod q\right\rceil_{q,2}\\
&=\left\lfloor e+\mu\left\lfloor\frac q2\right\rfloor\pmod q\right\rceil_{q,2}\\
&\approx\left\lfloor\frac2q e+\mu\pmod q\right\rceil.
\end{aligned}
$$

Note that if $|e|<q/4$, then we can see that the result of the rounding operation is unchanged by $e$, and thus
rounds to the value $\mu$.

<a id="pdf-c0f87bf2e871-p085-b001"></a>
<!-- pdf-source: page=85; block=1; confidence=0.95 -->

**Security.** The scheme is CPA-secure assuming the hardness of the LWE problem, which we recall here.

**Definition 21.2 (LWE Problem).** Given $a\stackrel R\leftarrow\mathbb Z_q^n$, $e\leftarrow\chi$, $s\stackrel R\leftarrow\mathbb Z_q^n$, $u\stackrel R\leftarrow\mathbb Z_q$, distinguish $(a,s^Ta+e)$ and
$(a,u)$.

By this assumption, in the security argument, we can replace the ciphertexts with $(a,u+\mu\lfloor q/2\rfloor)$. Then,
the encryption scheme becomes a one-time pad.

<a id="pdf-c0f87bf2e871-p086-b001"></a>
<!-- pdf-source: page=86; block=1; confidence=1.00 -->

**Lecture 21, Regev public-key encryption and Definition 21.3.** The
public key contains zero encryptions under one secret. To encrypt, take a
random binary subset and shift its second component by the message
codepoint. Decryption subtracts the secret product. The bounded error law
gives an absolute subset-error bound of $mB$. The formalization uses strict
separation for its chosen decoder.

<a id="pdf-c0f87bf2e871-p086-b002"></a>
<!-- pdf-source: page=86; block=2; confidence=1.00 -->

**Lecture 21, Regev public-key security.** The first comparison replaces
the LWE public key by a uniform matrix and vector. The second uses the
leftover hash lemma for the uniform augmented matrix and binary subset to
hide the fixed message shift statistically.
