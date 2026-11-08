<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter09/MatchingMomentCombinatorics.lean :: FABL.natCard_perfectMatchingCode -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Perfect matching code count

**Claim.** For every natural number $m$, the number of perfect matching codes with parameter $m$ is $(2m-1)!!$.

**Proof.** Induct on $m$. At $m=0$, the code type is a singleton, and the double factorial at the corresponding index is $1$. For the successor step, a code consists of a choice from a set of size $2m+1$ together with a code of parameter $m$. Thus its cardinality is $(2m+1)$ times the previous code count. When $m=0$, this agrees directly with the initial double-factorial value. For $m>0$, the double-factorial recurrence $(2m+1)!!=(2m+1)(2m-1)!!$ gives exactly the same count, completing the induction.
