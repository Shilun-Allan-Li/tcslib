<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/Primitives.lean :: Turing.FinTM.mapPrefix_replay -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Replay of the Encoded Prefix

**Claim.** If $x=\mathrm{pre}\,\langle a,b\rangle$, then for any prior output $\mathrm{out}$ there is a valid input-head position such that after $2|a|+2$ steps from the emitting pair-reading state, the controller is in the payload-replay state with capture displacement $0$ and output $\mathrm{out}$ followed by the encoding of $a$ paired with the empty word.

**Proof.** Use induction on $a$. If $a$ is empty, the encoded input begins with the delimiter $[\mathrm{false},\mathrm{true}]$. The two-step parse-block behavior (`mapParse_block`) reads this delimiter in emitting mode, emits its two bits, and places the controller in the payload-replay phase at the position immediately after the delimiter, as required; the step count is $2$. For the inductive case, write $a=\text{bit}::a'$. The encoding begins with the doubled bit $[\text{bit},\text{bit}]$, followed by the encoding of $a'$ paired with $b$. First apply `mapParse_block` to read that doubled bit. Since its two bits agree, the parser returns to the pair-reading state, and emitting mode appends the doubled bit to the output. Now apply the induction hypothesis to the remaining encoded suffix, taking the new prefix to include those two bits and the new prior output to include the same two bits. The runs concatenate by `runFrom_add`; their lengths combine as $2+(2|a'|+2)=2|a|+2$. The resulting output is the original output followed by the encoding of $a$ paired with the empty word, by the definition of the encoding and associativity of list concatenation.

**Key facts.** `Turing.FinTM.mapParse_block`, `Turing.MultiTapeTM.runFrom_add`.
