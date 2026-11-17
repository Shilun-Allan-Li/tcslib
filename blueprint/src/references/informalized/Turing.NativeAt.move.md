<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/InputDevice.lean :: Turing.NativeAt.move -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Head Position After Movement

**Claim.** If a configuration’s input head is at position $i$, then after movement by any sign $m$, its position is the correspondingly moved position of $i$.

**Proof.** The NativeAt hypothesis says the configuration’s input position equals $i$. After replacing that position by its move under $m$, the resulting position is therefore the move of $i$ under the same $m$, which is precisely the asserted NativeAt relation.
