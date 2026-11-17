<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Robustness/ObliviousCandidate.lean :: Complexity.payload_sweeps_source -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Backward sweep for a source action

**Claim.** For a configuration $c$, action $a$, coordinate $z$, and length $n$, folding the backward row transducer with directions prescribed by $a$ over the reversed cached zone of written payloads, from the written payloads at $z+n$, yields the written payloads at $z$ and the reversed uncached zone of source payloads for the configuration obtained by applying $a$ to $c$.

**Proof.** Apply the general backward-zone result (payloadBackward_zone) to the family of written payloads of $c$ under $a$, with direction function given by the source shift. It gives the desired register and a reversed uncached zone whose payload at coordinate $t$ and index $i$ is the written payload at $t+	ext{shift}(i)$. The source-payload transition identity (sourcePayload_apply) says exactly that this shifted written payload equals the source payload of the configuration after applying $a$. Replacing the shifted family by that source-payload family proves the claim.

**Key facts.** `Complexity.payloadBackward_zone`, `Complexity.sourcePayload_apply`.
