<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Robustness/ObliviousCandidate.lean :: Complexity.payloadBackward_zone -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Backward sweep over a zone

**Claim.** Folding the backward row transducer over the reversed cached zone of length $n$ starting at $z$, from register $f(z+n)$, produces register $f(z)$ and the reversed uncached zone whose payload at coordinate $t$ and index $i$ is $f(t+d(i),i)$.

**Proof.** Proceed by induction on $n$, allowing the starting coordinate $z$ to vary. For $n=0$, the zone is empty, so the fold leaves its register unchanged; the result follows directly. For the induction step, the zone consists of its first row at $z$ followed by the zone of length $n$ starting at $z+1$. Reversing this list puts the reversed tail first and the row at $z$ last. The identity $z+(n+1)=(z+1)+n$ makes the initial register the one required by the induction hypothesis. Folding the reversed tail therefore changes the register from $f(z+n+1)$ to $f(z+1)$ and produces the reversed uncached tail. The remaining row is transformed by the one-row backward identity (payloadBackward_row), which takes register $f(z+1)$ to $f(z)$ and converts that row to the corresponding uncached row with shifted payloads. Appending this row at the end gives exactly the claimed reversed zone.

**Key facts.** `Turing.FinTM.sweepFold_append`, `Complexity.payloadBackward_row`.
