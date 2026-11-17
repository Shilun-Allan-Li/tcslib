<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/CounterProg.lean :: Complexity.CounterProg.enc_inputSymbol -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Input Symbol in an Encoded State

**Claim.** If the abstract read position $p$ satisfies $p\le |x|$, then the symbol under the input head in the encoded configuration is $x[p]?$.

**Proof.** The encoded input-head position is $p+1$ by the encoded-position result (`enc_inputPos`). A configuration whose input-head position is $i+1$ reads the possibly absent input symbol $x[i]?$, provided $i\le |x|$ (`Turing.FinTM.inputSymbol_at`). Apply this fact with $i=p$ and the stated bound to obtain the claim.

**Key facts.** `Complexity.CounterProg.enc_inputPos`, `Turing.FinTM.inputSymbol_at`.
