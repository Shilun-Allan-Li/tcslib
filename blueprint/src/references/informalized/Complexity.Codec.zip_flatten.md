<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Codec/Scan.lean :: Complexity.Codec.zip_flatten -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Flattening and aligned zipping

**Claim.** If two lists of lists have the same number of entries and corresponding entries have the same lengths, then zipping their flattened lists equals flattening the list of pairwise inner zips.

**Proof.** Induct on the first outer list, generalizing the second. When the first list is empty, the equal-length hypothesis makes the second empty as well, and both sides are empty. In the nonempty case, write the lists as $a::L_1$ and $b::L_2$; the outer lengths force this matching decomposition. The length hypothesis at index $0$ says that $a$ and $b$ have equal lengths. Thus zipping their concatenation with the flattened tails splits into the zip of $a$ with $b$, followed by the zip of the two flattened tails. The induction hypotheses apply to those tails: their outer lengths still agree, and their corresponding inner lengths agree by applying the original pointwise condition at index $i+1$. This identifies the tail zip with the flattening of the tailwise inner zips, giving the claimed equality after adjoining the first inner zip.
