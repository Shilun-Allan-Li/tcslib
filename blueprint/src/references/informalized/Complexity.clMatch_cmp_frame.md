<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CookLevin/Hardness.lean :: Complexity.clMatch_cmp_frame -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Comparator tape placement

**Claim.** Placing the comparator configuration into the matcher’s comparison slots gives exactly the matcher configuration in the comparison phase, with the surrounding tapes and heads unchanged.

**Proof.** Compare the configurations field by field. Their control states agree by the specified embedding of the comparator state, and their input-head positions and output lists are identical. For the work tapes and head positions, split the matcher’s slots into the row slots and the five auxiliary slots. In the row part, the placement selects the positive coordinate for comparator tape 0 and the negative coordinate for tape 3; distinctness of `pos` and `neg` ensures these assignments do not conflict. At every other row coordinate the placement leaves the original tape and head unchanged. In the auxiliary part, the placement sends comparator tapes 1 and 2 to the target slots in the prescribed order, while the remaining slots retain their original data. The comparator tapes contain the four words specified by `clMatchWords`, so these cases give precisely the matcher’s row and target tapes. Thus all fields agree.
