<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Machines/ParsePlain.lean :: Complexity.LogProg.getElem?_lt_tRun -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Bits in the Initial Run of Ones

**Claim.** Every index $j$ strictly less than the length $t$ of the initial run of ones in $x$ has entry $x_j=\mathrm{true}$.

**Proof.** By the defining property of the initial run of ones, each entry at an index strictly before its endpoint is true. The stated fact is precisely this property (`takeWhile_true_getElem?`).

**Key facts.** `Complexity.LogProg.takeWhile_true_getElem?`.
