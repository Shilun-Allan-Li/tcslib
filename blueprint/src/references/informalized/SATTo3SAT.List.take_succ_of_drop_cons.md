<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/NPReductions/SATTo3SAT.lean :: SATTo3SAT.List.take_succ_of_drop_cons -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Prefix extension after dropping entries

**Claim.** If dropping the first $n$ entries of a list leaves a list headed by $a$, then taking the first $n+1$ entries is the same as taking the first $n$ entries and appending $a$.

**Proof.** Proceed by induction on $n$, splitting according to whether the list is empty. At $n=0$, the hypothesis says the original list is headed by $a$, and the claimed equality follows directly. An empty list cannot satisfy the hypothesis. For the successor case, write the original list as a head followed by a tail. The drop hypothesis then says that dropping $n$ entries from the tail yields a list headed by $a$. Apply the induction hypothesis to the tail; adding back the original head gives the desired equality of prefixes.
