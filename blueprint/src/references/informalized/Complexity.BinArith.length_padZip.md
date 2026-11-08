<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassP/BinaryArith/Basic.lean :: Complexity.BinArith.length_padZip -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Length of a padded zip

**Claim.** For any bit strings $a,b$ and natural number $N$, the padded list of $N$ aligned bit pairs has length $N$.

**Proof.** Induct on $N$, allowing $a$ and $b$ to vary. At $N=0$ the list is empty. At a successor, the construction puts exactly one pair of head bits, using $0$ if a string has no head, before the padded zip with parameter $N$. Its length is therefore one plus the induction-hypothesis length $N$, giving $N+1$.
