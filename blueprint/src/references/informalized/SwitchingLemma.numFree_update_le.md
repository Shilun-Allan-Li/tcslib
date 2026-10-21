<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/Switching/CanonicalDTree.lean :: SwitchingLemma.numFree_update_le -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: claude-opus-4-8; confidence: high -->

# Fixing a Variable Does Not Increase the Free Count

**Claim.** Let $\rho$ be a restriction on $n$ variables, i.e. a function assigning to each $i \in \mathrm{Fin}\,n$ either a fixed Boolean value or the symbol $\ast$ marking $i$ as free, and write $\mathrm{numFree}(\rho)$ for the number of free variables of $\rho$. Given a variable $v \in \mathrm{Fin}\,n$ and a Boolean value $b$, let $\rho[v \mapsto b]$ be the restriction agreeing with $\rho$ everywhere except at $v$, where it takes the fixed value $b$. Then $\mathrm{numFree}(\rho[v \mapsto b]) \le \mathrm{numFree}(\rho)$.

**Proof.** Recall that the free variables of a restriction $\rho$ form the set
\[
\mathrm{freeVars}(\rho) = \{\, i \in \mathrm{Fin}\,n : \rho(i) = \ast \,\},
\]
and $\mathrm{numFree}(\rho)$ is the cardinality of this set. Since cardinality is monotone under set inclusion (`Finset.card_le_card`), it suffices to prove the set inclusion
\[
\mathrm{freeVars}(\rho[v \mapsto b]) \subseteq \mathrm{freeVars}(\rho);
\]
the desired inequality of cardinalities follows at once.

So fix an index $i$ that is free in the updated restriction, meaning $\rho[v \mapsto b](i) = \ast$. We must show that $i$ is free in $\rho$, i.e. $\rho(i) = \ast$. By the definition of the pointwise update, $\rho[v \mapsto b](i)$ equals $b$ when $i = v$ and equals $\rho(i)$ otherwise. Split on whether $i = v$:

- If $i = v$, then $\rho[v \mapsto b](i) = b$ is a fixed Boolean value, which cannot equal $\ast$. This contradicts the hypothesis that $i$ is free in the updated restriction, so this case does not occur.
- If $i \neq v$, then $\rho[v \mapsto b](i) = \rho(i)$, so the hypothesis $\rho[v \mapsto b](i) = \ast$ reads $\rho(i) = \ast$, which is exactly what we wanted.

In either case $i \in \mathrm{freeVars}(\rho)$, establishing the inclusion and hence the inequality. Intuitively: updating $v$ to a fixed value can only remove $v$ from the free set (if it was free there) and changes nothing at any other coordinate, so the free set can only shrink.
