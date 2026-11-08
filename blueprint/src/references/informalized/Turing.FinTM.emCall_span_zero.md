<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/Loop.lean :: Turing.FinTM.emCall_span_zero -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# The Origin Marker

**Claim.** The closed-span marker for $[0,0]$ is the buffer tape containing the one-symbol word $[\mathrm{true}]$.

**Proof.** Evaluate both functions at an integer $z$. At $z=0$, both return $\mathrm{true}$. If $z\ne0$ and $z<0$, neither marker returns a symbol. If $z>0$, the closed-span marker is blank, and the one-symbol buffer has no entry at index $z$, so it too is blank. Hence the functions agree everywhere.
