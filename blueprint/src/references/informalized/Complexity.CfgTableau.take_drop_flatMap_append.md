<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/PSubsetPPolyTableauCorrect.lean :: Complexity.CfgTableau.take_drop_flatMap_append -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Fixed-Length Block Extraction

**Claim.** If each list $g(a)$ has length $c$, then the length-$c$ block starting at position $ic$ in the flattened lists, followed by any remainder, is exactly $g(l_i)$ whenever $i<|l|$.

**Proof.** Induct on the list $l$, keeping the index $i$ arbitrary. If $l$ is empty, the hypothesis $i<|l|$ is impossible. Otherwise write $l=a::l'$. When $i=0$, the flattened list begins with $g(a)$, whose length is $c$, so taking its first $c$ entries gives exactly $g(a)$. When $i=i'+1$, the desired starting position is $(i'+1)c=c+i'c$. The initial block $g(a)$ has length $c$, so dropping this many entries first removes that block and then drops $i'c$ entries from the flattened tail followed by the remainder. The induction hypothesis, applied to $l'$ and $i'$, identifies the next length-$c$ block with $g(l'_{i'})$, which is the required element of the original list.
