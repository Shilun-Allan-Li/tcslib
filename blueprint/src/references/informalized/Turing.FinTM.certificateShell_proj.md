<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/CertShell.lean :: Turing.FinTM.certificateShell_proj -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Certificate-Shell Projection

**Claim.** The set of words $x$ admitting a certificate $u$ of length $C(|x|+1)^c$ for which $xu$ has a decomposition $x'u'$ with the prescribed certificate length and output $[1]$ is exactly the set of words $x$ admitting a certificate of that length with output $[1]$ directly on $x$.

**Proof.** For one inclusion, suppose $u$ has the prescribed length for $x$, and $x++u=x'++u'$ where $u'$ has the prescribed length for $x'$ and the output on $(x',u')$ is $[1]$. The function sending an input length $n$ to $n+C(n+1)^c$ is strictly increasing (`certificateLength_strictMono`). Therefore an appended word of the prescribed length determines its split uniquely: the two decompositions force $x=x'$ and $u=u'$ (`append_split_unique`). The given output condition then supplies the required certificate directly for $x$. Conversely, any such certificate $u$ for $x$ gives the required decomposition by choosing $x'=x$ and $u'=u$.

**Key facts.** `Turing.certificateLength_strictMono`, `Turing.append_split_unique`.
