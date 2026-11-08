<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/CodeParser.lean :: Turing.codeFlatMap_length -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Length Bound for Concatenated Words

**Claim.** If every element occurring in a finite list maps to a bit string of length at least $c$, then the concatenation of those images has length at least $c$ times the length of the list.

**Proof.** Induct on the list. For the empty list, both the concatenation length and the product are zero. For a list with head $a$ and tail $xs$, the hypothesis gives $c\leq |f(a)|$, and it applies to every element of the tail as well. By induction, the concatenation of the tail images has length at least $c|xs|$. The length of the full concatenation is $|f(a)|$ plus that tail length, so it is at least $c+c|xs|=c(1+|xs|)$, as required.
