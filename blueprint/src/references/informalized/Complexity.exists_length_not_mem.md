<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Diagonalization/Relativization.lean :: Complexity.exists_length_not_mem -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# A Missing Bit String of Prescribed Length

**Claim.** If a finite list $Q$ of binary strings has fewer than $2^n$ entries, some binary string of length $n$ is absent from $Q$.

**Proof.** Assume, toward contradiction, that every binary string of length $n$ occurs in $Q$. There are exactly $2^n$ such strings, since each of the $n$ positions has two choices. More explicitly, represent each integer $j<2^n$ by the length-$n$ list of its binary digits, with leading zeroes. Under the assumption, every such list lies in $Q$, so the map from these integers to their digit lists, viewed as members of the finite set of entries of $Q$, is injective: equality of the lists forces equality of the integers, because their first $n$ binary digits determine them. Thus $2^n\le |Q|$, contradicting the hypothesis $|Q|<2^n$.
