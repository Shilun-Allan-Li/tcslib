<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassP/BinaryArith/Basic.lean :: Complexity.BinArith.flatMap_zipChunk -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Flattening a Padded Zip

**Claim.** For bit strings $a,b$ and a natural number $N$, flattening the list of paired padded entries at positions $0$ through $N-1$ gives the same string as concatenating the padded entries of each pair in order.

**Proof.** Induct on $N$, generalizing over $a$ and $b$. At $N=0$, both lists are empty. For the successor case, the first pair contributes the head of each string, using false for a missing head. The remaining pairs are formed from $a$ and $b$ with their first entries removed. Apply the induction hypothesis to those tails; adjoining the initial pair's two entries yields exactly the flattened padded zip.
