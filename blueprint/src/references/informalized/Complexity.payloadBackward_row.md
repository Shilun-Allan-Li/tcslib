<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Robustness/ObliviousCandidate.lean :: Complexity.payloadBackward_row -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Backward payload row update

**Claim.** Applying the backward row transducer to the cached row at $z$, with right register $f(z+1)$, produces the register $f(z)$ and the uncached row whose payload at index $i$ is $f(z+d(i),i)$.

**Proof.** The first component of the transducer output is the first component of the input row, which is $f(z)$. For each index $i$, the input row’s current payload is $f(z,i)$ and its cached payload is $f(z-1,i)$. If $d(i)=-1$, the transducer selects the cached payload, giving $f(z-1,i)$; if $d(i)=0$, it selects the current payload, giving $f(z,i)$; and if $d(i)=1$, it selects the supplied right register, giving $f(z+1,i)$. In each case the selected value is $f(z+d(i),i)$. The output row is uncached, so its second component is the blank payload, as required.
