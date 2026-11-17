<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/CertShell.lean :: Turing.cert_tail_test -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Characterisation of a One-Symbol Buffer

**Claim.** The buffer has value true at position $|w|-1$ and is blank at position $|w|-2$ exactly when $w=[\mathrm{true}]$.

**Proof.** Suppose first that the two buffer conditions hold. If $|w|>1$, then $|w|-2$ is a nonnegative position strictly less than $|w|$. The buffer at that position must therefore return the list entry there, contradicting the asserted blank value. Hence $|w|\leq 1$. The empty word cannot satisfy the first condition, since its buffer at position $-1$ is blank. Thus $w$ has one element, say $b$. At position $|w|-1=0$ its buffer is $b$, so the first condition forces $b$ to be true. Conversely, for the one-element word $[\mathrm{true}]$, position zero contains true and position $-1$ is negative, hence blank by the definition of the buffer.
