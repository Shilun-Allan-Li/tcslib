<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Robustness/ObliviousCandidate.lean :: Complexity.payloadForward_row -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# One forward row

**Claim.** Applying the forward row transducer with left register $f(z-1)$ to the uncached row at $z$ gives register $f(z)$ and the cached row at $z$.

**Proof.** At each index $i$, the uncached row stores $f(z,i)$ in its first component and the blank payload in its second. The forward transducer sets the new register to the first component and forms the output row from that component and the supplied left register. Since the supplied register is $f(z-1)$, the output row is precisely the cached row at $z$.
