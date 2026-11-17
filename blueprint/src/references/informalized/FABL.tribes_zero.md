<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter04/Tribes.lean :: FABL.tribes_zero -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Tribes with zero blocks

**Claim.** For every $w$, tribes with zero blocks is the constant function with value $+1$.

**Proof.** Fix an input in the zero-dimensional cube. By definition, tribes applies OR over the empty collection of block outputs. The defining condition for OR to return $+1$—that every entry equal $+1$—holds vacuously for an empty collection. Hence tribes returns $+1$ on every input, as claimed.
