<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Randomized/NPPoly.lean :: Randomized.length_flatMap_dup -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Length After Duplicating Entries

**Claim.** Replacing each entry of a finite list by two consecutive copies produces a list of length twice the original length.

**Proof.** Proceed by induction on the list. The empty list produces an empty list, so the claim holds. For a list with first entry $a$ and tail $l$, the transformed list consists of the two copies of $a$ followed by the transformed tail. Its length is therefore $2$ plus the tail's transformed length. By induction that tail length is $2|l|$, giving $2+2|l|=2(|l|+1)$, as required.
