<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter06/Constructions/RandomSmallBias.lean :: FABL.randomSmallBiasMultiset_card -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Cardinality of the sample multiset

**Claim.** For any list of $m$ vectors in $(\mathbb F_2)^n$, the multiset of those samples, counting repetitions, has cardinality $m$.

**Proof.** The sample multiset is obtained by mapping the $m$-element set of indices $\{0,\ldots,m-1\}$ through the sample function and retaining repetitions. Mapping a finite set to a multiset preserves the number of entries, including when distinct indices have the same image. Thus its cardinality is the cardinality of the index set, namely $m$.
