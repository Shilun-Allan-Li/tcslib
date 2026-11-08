<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CookLevin/Hardness.lean :: Complexity.clA5DecodeStep_state -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Decoding State Advances by One

**Claim.** For every binary word $w$ and natural number $j$, one decoding step applied to the state for $w$ at count $j$ gives the state for $w$ at count $j+1$.

**Proof.** Unpack the paired encoding in the state: the first header field is $w$, the second is the unary list of $j$ true bits, and the remaining field is the bounded unary value determined by whether $\mathrm{clNum}(w)\le j$. The fact that decoding a pair encoding recovers both fields (`pairDecode_pairEncode`) justifies these identifications. The step appends one true bit to the unary counter, giving the unary list for $j+1$. If $\mathrm{clNum}(w)=j+1$, the new counter itself is the required bounded value. Otherwise, if $\mathrm{clNum}(w)\le j$, the previously stored unary value remains the correct one; if not, the value remains empty. These cases agree with the definition of the state at count $j+1$, using the elementary comparisons between $\mathrm{clNum}(w)$, $j$, and $j+1$.

**Key facts.** `Turing.pairDecode_pairEncode`.
