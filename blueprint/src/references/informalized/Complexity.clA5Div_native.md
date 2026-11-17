<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CookLevin/Hardness.lean :: Complexity.clA5Div_native -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Polynomial-Time Unary Division

**Claim.** If the unary representation of $f(x)$ is polynomial-time computable, then for every natural number $k$, the unary representation of $f(x)/k$ is polynomial-time computable, with natural-number division and $f(x)/0=0$.

**Proof.** If $k=0$, the quotient is zero for every input, so the output is the constant empty list (`clA5_pt_const`). Otherwise write the divisor as $k+1$. Use a finite-state word map with states $0,1,\ldots,k$: each input bit advances the state cyclically, and a true bit is emitted exactly when the current state is $k$. Starting in state zero, after reading a word of length $n$ the number of emitted bits is $\lfloor n/(k+1)\rfloor$. This follows by induction on the input word: each complete block of $k+1$ symbols produces one emission, and an incomplete block produces none. The map is polynomial-time computable (`clA5Map_poly`); composing it with the function producing the unary representation of $f(x)$ gives a polynomial-time computable function (`PolyTimeComputable.comp`). The induction identifies its output as the unary representation of $f(x)/(k+1)$, proving the positive-divisor case.

**Key facts.** `Complexity.clA5_pt_const`, `Complexity.clA5Map_poly`, `Complexity.PolyTimeComputable.comp`.
