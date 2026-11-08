<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter05/PrescribedFourierSupport.lean :: FABL.card_lowDegreeFourierFamily_add_ncard_high -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Partition of Subsets at the Cutoff

**Claim.** The number of subsets with size at most the cutoff, plus the number with size greater than the cutoff, is $2^n$.

**Proof.** Every subset of the $n$-element coordinate set either has cardinality at most the cutoff or has cardinality greater than it, and these two cases are disjoint. Thus the two classes partition the full powerset. The low-degree Fourier family is exactly the first class: by its construction it collects the subsets of each size from $0$ through the cutoff. The second class is finite, and its set cardinality agrees with its finite cardinality. Consequently the two counts sum to the cardinality of the full powerset, which is $2^n$.
