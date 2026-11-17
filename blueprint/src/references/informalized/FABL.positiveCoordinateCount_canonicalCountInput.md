<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter02/SocialChoiceFunctions/Definitions.lean :: FABL.positiveCoordinateCount_canonicalCountInput -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Canonical Sign Vector Count

**Claim.** For the canonical sign vector that equals $1$ at coordinate $i$ exactly when $i<k$, the number of coordinates equal to $1$ is $\min(n,k)$.

**Proof.** The positive coordinates are precisely those elements of $\mathrm{Fin}(n)$ whose values are less than $k$. The number of such coordinates is $\min(n,k)$: if $k\le n$, there are $k$ of them, and if $n\le k$, all $n$ coordinates qualify.
