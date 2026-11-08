<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Diagonalization/EXPCOM.lean :: Complexity.expcom_all_true -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Overflow forces an all-ones word

**Claim.** If the fixed-width binary increment of a finite Boolean word, with overflow interpreted as the empty word, is empty, then every entry of the word is true.

**Proof.** The characterization of increment overflow says that `incFixed w = none` exactly when $w$ is the all-true word of its length (`Turing.incFixed_eq_none_iff_replicate`). It remains to obtain this overflow condition from the hypothesis that `(incFixed w).getD [] = []`. If $w$ is empty, the characterization applies directly. If its first entry is false, increment produces a nonempty word beginning with true, contradicting the hypothesis. If its first entry is true, the increment is the recursive increment of the tail with false prefixed whenever that recursive result exists. The hypothesis forces the recursive result to be absent; applying the characterization to the tail shows that the tail is all true, and hence so is $w$.

**Key facts.** `Turing.incFixed_eq_none_iff_replicate`.
