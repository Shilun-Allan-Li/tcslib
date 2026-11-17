<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassNP/TMSAT.lean :: Complexity.tmsat_flatMap_length -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Length under list flattening

**Claim.** If every list $f(a)$ has length at least $1$, then for any finite list $l$, the length of $l$ is at most the length of the concatenation of the lists $f(a)$ for its entries.

**Proof.** Induct on $l$. For the empty list, both lengths are zero. For a list with first entry $a$ and tail $l'$, flattening produces $f(a)$ followed by the flattening of $l'$. Its length is therefore $|f(a)|$ plus the length of the flattened tail. By the hypothesis, $|f(a)|\geq1$, and by induction the flattened tail has length at least $|l'|$. Adding these inequalities shows the flattened list has length at least $1+|l'|$, which is the length of the original list.
