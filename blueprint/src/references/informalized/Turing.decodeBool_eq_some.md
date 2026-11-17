<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/SymbolLift.lean :: Turing.decodeBool_eq_some -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Characterization of successful decoding

**Claim.** If decoding an element $\gamma$ returns a Boolean $b$, then $\gamma=e(b)$.

**Proof.** The decoder tests first whether $\gamma=e(true)$, and otherwise whether $\gamma=e(false)$. If the first test succeeds, its output is true, so the assumed output forces $b=true$ and gives $\gamma=e(b)$. If it fails, a successful output can only come from the second test; that test gives $\gamma=e(false)$ and output false, hence $b=false$ and again $\gamma=e(b)$.
