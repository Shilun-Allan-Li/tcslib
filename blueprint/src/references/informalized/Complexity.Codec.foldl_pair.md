<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Codec/Step.lean :: Complexity.Codec.foldl_pair -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Folding paired updates componentwise

**Claim.** Folding the paired update over a list gives the pair of the separate folds of its two component updates.

**Proof.** Induct on the list. For the empty list, both folds return their initial values, so the equality holds. For a head $c$ followed by a tail $L$, the paired fold first updates $(a,b)$ to $(f(a,c),g(b,c))$ and then folds over $L$. Apply the induction hypothesis to that tail with these updated initial values. The two resulting components are exactly the separate folds of $f$ from $a$ and $g$ from $b$ over the whole list.
