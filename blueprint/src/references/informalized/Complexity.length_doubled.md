<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/Advice.lean :: Complexity.length_doubled -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Length of a Doubled Bit List

**Claim.** For every finite bit string $x$, replacing each bit by two consecutive copies gives a list of length $2|x|$.

**Proof.** Induct on $x$. The empty list and its doubled list both have length zero. For a list with head $b$ and tail $x$, doubling produces the two copies of $b$ followed by the doubled tail. Its length is therefore $2$ plus the tail’s doubled length. By the induction hypothesis this is $2+2|x|=2(1+|x|)$, as required.
