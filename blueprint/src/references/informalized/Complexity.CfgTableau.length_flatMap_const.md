<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/PSubsetPPolyTableau.lean :: Complexity.CfgTableau.length_flatMap_const -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Uniform Flat-Map Length

**Claim.** If every list $f(a)$ has length $c$, then flattening the lists obtained from a finite list $l$ produces a list of length $|l|c$.

**Proof.** Induct on $l$. For the empty list, the flat map is empty, so both sides are zero. For a list with head $a$ and tail $l'$, its flat map is $f(a)$ followed by the flat map of $l'$. Its length is therefore $c+|l'|c$, by the uniform-length hypothesis and the induction hypothesis. The distributive identity $(|l'|+1)c=c+|l'|c$ gives the required formula.
