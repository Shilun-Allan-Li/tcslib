<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassNP/TMSAT.lean :: Complexity.tmsat_good_spec -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Structure of valid verifier inputs

**Claim.** A bit string satisfying the validity guard splits into its instance part $Y$ and certificate part $W$, with $|W|=|Y|+1$, and $Y$ is the nested encoding of its code, input, unary width, and unary clock fields.

**Proof.** Unpack the validity guard into the successful-decode conditions for the outer split and each nested pair, together with the two unary-field checks. The outer split-components fact (Complexity.tmsat_split_components) identifies $z$ as the concatenation of its extracted parts $Y$ and $W$, and gives $|W|=|Y|+1$. For the nested structure, successful decoding implies that each encoded pair is exactly the pair encoding of its extracted components (Complexity.tmsat_pair_valid). Apply this first to $Y$, then to its second component, and then to the second component of that pair. These identities give the nested encoding of the code, input, width, and clock fields. The unary checks identify the width and clock fields with all-ones words of their respective lengths, yielding the claimed expression for $Y$.

**Key facts.** `Complexity.tmsat_split_components`, `Complexity.tmsat_pair_valid`.
