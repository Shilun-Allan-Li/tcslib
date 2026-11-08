<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassP/BinaryArith/DetMod.lean :: Complexity.BinArith.lt_of_mem_zipWith -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Range of Zipped List Entries

**Claim.** If every value of $f$ is less than $p$, then every entry in the list obtained by applying $f$ pairwise to two lists is less than $p$.

**Proof.** Induct on the first list. If it is empty, the zipped list has no entries. If it has head $a$ and tail $l_1$, split on the second list. When that list is empty, the zip is again empty. When it has head $b$ and tail $l_2$, the zipped list consists of $f(a,b)$ followed by the zip of the tails. An entry is therefore either the head, which is less than $p$ by hypothesis, or belongs to the tail zip, where the induction hypothesis applies.
