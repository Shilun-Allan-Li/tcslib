<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter05/ThresholdCircuits.lean :: FABL.profileGate_pair_value -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Value of a Profile Gate Pair

**Claim.** For each coordinate $i$ and sign vector $x$, the sum of the real-valued outputs of the main and correction gates is $a(i+1)-a(i)$ when $i$ is less than the number of coordinates in $S$ where $x$ equals $1$, and is zero otherwise.

**Proof.** First consider the case $a(i+1)=a(i)$. The main gate is constantly $1$ and the correction gate is constantly $-1$, so their real-valued outputs sum to zero, as required. Now suppose the two signs differ. If $a(i+1)=1$, then $a(i)=-1$; the main gate outputs $1$ exactly when the positive-coordinate count is at least $i+1$, and otherwise outputs $-1$. The correction gate is constantly $1$. Thus the sum is $2=a(i+1)-a(i)$ when the count is greater than $i$, and zero when it is at most $i$. If instead $a(i+1)=-1$, then $a(i)=1$. The main gate reverses those outputs, while the correction gate is constantly $-1$. The sum is $-2=a(i+1)-a(i)$ when the count is greater than $i$, and zero otherwise. These cases establish the stated formula.
