<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter07/CNFReductions.lean :: FABL.length_flatten_le_mul -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Flattened List Length Bound

**Claim.** If each list in a finite list of lists has length at most $b$, then flattening it gives a list of length at most $b$ times the number of lists.

**Proof.** Proceed by induction on the outer list. For the empty list, the flattening has length zero, so the bound holds. For a list beginning with a list $S$, followed by a tail $T$, the flattened length is $|S|$ plus the flattened length of $T$. The hypothesis bounds $|S|$ by $b$, and it also restricts every list in $T$ to length at most $b$. By induction, the flattened tail has length at most $b|T|$. Adding these bounds gives at most $b+b|T|=b(|T|+1)$, which is the required bound for the original outer list.
