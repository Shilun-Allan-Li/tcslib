<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/Switching/EncodingProperties.lean :: SwitchingLemma.processClauseLits_aux_entries_from_lits -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: claude-opus-4-8; confidence: high -->

# Auxiliary Indices Trace Back to Input Literals

**Claim.** Fix $n$ and run the free-literal processing of a clause: feed a list $\mathrm{lits}$ of literal–index pairs, a decision-tree path, and two restrictions $\rho_0$ and $\sigma$ on $n$ variables into $\mathrm{processClauseLits}$, and let $A$ be the fourth component of its output — the accumulated list of index–direction pairs. Then every pair $(i, b)$ occurring in $A$ has its first component $i$ equal to the index component $j$ of some literal–index pair $(\ell, j)$ in $\mathrm{lits}$. In short, no index appears in the auxiliary output unless it was supplied by one of the input literals.

**Proof.** Recall how $\mathrm{processClauseLits}$ builds its auxiliary list $A$. It recurses on $\mathrm{lits}$ and the path in lockstep. If either list is empty it returns $A = [\,]$. Otherwise, writing the first literal–index pair as $(\ell, \mathrm{idx})$ and the first path entry as $(\_, \mathrm{dir})$, it processes the tails (with the restrictions updated at $\ell$'s variable) to obtain a recursive auxiliary list $A'$, and returns
\[
A = (\mathrm{idx}, \mathrm{dir}) :: A'.
\]
So each step prepends one pair whose index is exactly the index drawn from the literal it just consumed. The claim is that this index always comes from $\mathrm{lits}$; we prove it by induction on $\mathrm{lits}$, letting the path and both restrictions vary freely so that the inductive hypothesis applies to whatever tails the recursion produces.

1. **Empty literal list.** If $\mathrm{lits} = [\,]$, then $A = [\,]$ by definition, so there is no pair $(i,b) \in A$ and the statement holds vacuously.

2. **Nonempty literals, empty path.** Suppose $\mathrm{lits} = (\ell,\mathrm{idx}) :: \mathrm{rest}$ but the path is empty. The second defining clause applies and again returns $A = [\,]$, so the statement is once more vacuous.

3. **Both lists nonempty.** Write $\mathrm{lits} = \mathrm{hd} :: \mathrm{tl}$ with $\mathrm{hd} = (\ell, \mathrm{idx})$, and let the path be $p :: ps$ with $p = (\_, \mathrm{dir})$. Then $A = (\mathrm{idx}, \mathrm{dir}) :: A'$, where $A'$ is the auxiliary list returned by the recursive call on $\mathrm{tl}$, $ps$, and the two updated restrictions. Take any $(i,b) \in A$. Membership in a cons-list gives two cases:
   - **The pair is the head.** If $(i,b) = (\mathrm{idx}, \mathrm{dir})$, then $i = \mathrm{idx} = \mathrm{hd}.2$, and $\mathrm{hd}$ is the first element of $\mathrm{lits}$. So $\mathrm{hd}$ itself is the witnessing literal–index pair, and $i$ equals its index.
   - **The pair lies in the recursive tail.** If instead $(i,b) \in A'$, the inductive hypothesis — applied to the tail $\mathrm{tl}$, the tail path $ps$, and the updated restrictions — furnishes a pair $\mathrm{li} \in \mathrm{tl}$ with $i = \mathrm{li}.2$. Since $\mathrm{tl}$ is a sublist of $\mathrm{lits} = \mathrm{hd} :: \mathrm{tl}$, this same $\mathrm{li}$ also lies in $\mathrm{lits}$, and it witnesses the claim.

In either case we have produced a literal–index pair in $\mathrm{lits}$ whose index equals $i$, completing the induction.
