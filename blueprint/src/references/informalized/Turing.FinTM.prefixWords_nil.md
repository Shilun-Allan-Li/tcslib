<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/OracleSim.lean :: Turing.FinTM.prefixWords_nil -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Empty Words Under Prefix Extension

**Claim.** Extending the family that assigns the empty word at every index below $k$ by empty words at any additional indices yields the everywhere-empty family on indices below $k'$.

**Proof.** Evaluate the two families at an arbitrary index $j<k'$. If $j<k$, the extension returns the original family’s value, which is empty. If $j\not<k$, the extension assigns the empty word by definition. Thus both cases give the empty word at $j$, so the functions agree everywhere.
