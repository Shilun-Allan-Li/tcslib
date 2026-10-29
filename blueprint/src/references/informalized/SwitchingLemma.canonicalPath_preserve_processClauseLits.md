<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/Switching.lean :: SwitchingLemma.canonicalPath_preserve_processClauseLits -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: claude-opus-4-8; confidence: high -->

# Processing a clause's literals preserves canonical paths

**Claim.** Fix a DNF formula $f$ on $n$ variables, restrictions $\rho_0,\sigma$, and let $t$ be the first term of $f$ not killed by $\rho_0$, with no repeated literal and no two distinct literals sharing a variable. Write $\mathrm{lits}$ for the position-tagged list of literals of $t$ whose variable is free under $\rho_0$, and let $\mathrm{path}$ be a canonical path for $f|_{\rho_0}$ — an initial segment of the deepest root-to-leaf path of the canonical decision tree of $f|_{\rho_0}$ — of length at most the depth of that tree, with the variable of each $\mathrm{lits}$ entry matching the variable queried at the aligned path step. Process $\mathrm{lits}$ against $\mathrm{path}$ in lockstep, one path step per literal: each literal with variable $v$, flag $b$, aligned with a step of direction $d$, sends $v\mapsto d$ into $\rho_0'$ and $v\mapsto\lnot b$ into $\sigma$, and its path step is consumed; $\rho_0'$ agrees with $\rho_0$ elsewhere and $\mathrm{path}'$ is the unconsumed tail. Then $\mathrm{path}'$ is a canonical path for $f|_{\rho_0'}$, and $|\mathrm{path}'|$ is at most the depth of the canonical decision tree of $f|_{\rho_0'}$.

**Proof.** Throughout write $T_\rho$ for the canonical decision tree of $f|_\rho$, write $\operatorname{depth}(T_\rho)$ for its depth, and write $D_\rho$ for its *deepest path* (`deepPath`), the greedy root-to-leaf path that at each branch descends into the taller subtree. Recall the length of the deepest path equals the depth of the tree (`DecisionTree.length_deepPath`), and that being a *canonical path* means $\mathrm{path}=D_{\rho_0}.\mathrm{take}(|\mathrm{path}|)$: the path is literally the initial segment of $D_{\rho_0}$ of its own length.

The whole argument rests on one structural fact about the lockstep processing (`processClauseLits_fst_eq_drop`): if we set
\[
m=\min(|\mathrm{lits}|,|\mathrm{path}|),
\]
then the returned path $\mathrm{path}'$ is exactly $\mathrm{path}.\mathrm{drop}(m)$ — processing consumes the first $m$ steps of $\mathrm{path}$ and keeps the rest — while $\rho_0'$ is $\rho_0$ updated on the variables of those first $m$ literals. The proof splits on which list runs out first.

1. **The path is shorter than (or as short as) the literal list.** Suppose $|\mathrm{lits}|\ge|\mathrm{path}|$, so $m=|\mathrm{path}|$ and $\mathrm{path}'=\mathrm{path}.\mathrm{drop}(|\mathrm{path}|)=[]$. The empty path is canonical for any restriction (it is the length-$0$ take of any deepest path), and its length $0$ is trivially below any depth. Both conclusions hold at once; nothing about $t$ or the canonical tree is needed.

2. **The literal list is shorter than the path.** Now $|\mathrm{lits}|<|\mathrm{path}|$, so $m=|\mathrm{lits}|$, the surviving path is $\mathrm{path}'=\mathrm{path}.\mathrm{drop}(|\mathrm{lits}|)$, and $\rho_0'$ updates $\rho_0$ on the variables of *all* of $\mathrm{lits}$. In particular $|\mathrm{path}|\ge 1$, so by the depth hypothesis $\operatorname{depth}(T_{\rho_0})\ge|\mathrm{path}|>0$: the canonical tree of $f|_{\rho_0}$ is not a leaf.

3. **The tree is "alive", so its root branches on $t$.** A canonical tree of positive depth cannot have all terms killed (that forces depth $0$, `canonicalDTree_depth_zero_of_killed`) nor any term fixed/satisfied (that also forces depth $0$, `canonicalDTree_depth_zero_of_fixed`). Hence neither degenerate case applies, and since $t$ is the first non-killed term, the canonical tree unfolds as a *term subtree* on $t$ (`canonicalDTree_alive_eq_termSubTree'`):
\[
T_{\rho_0}=\operatorname{termSubTree}\!\big(t,\rho_0,\ \mathrm{cont}\big),
\qquad
\mathrm{cont}(\rho')=\begin{cases}\text{leaf }\mathsf{true}&\text{if }t\text{ is fixed by }\rho',\\[2pt] \operatorname{go}(f,\ \rho_0.\mathrm{numFree},\ \rho')&\text{otherwise.}\end{cases}
\]
The term subtree queries, in order, the free-under-$\rho_0$ literals of $t$, and at the leaf of that spine it hands control to $\mathrm{cont}$ applied to the updated restriction. Because no two literals of $t$ share a variable (immediate from the two hypotheses on $t$: distinct literals have distinct variables, and the list has no repeats), this spine queries each variable at most once.

4. **The literal list is exactly the free spine of $t$.** By definition $\mathrm{lits}$ is the position-indexed list $t.\mathrm{zipIdx}$ filtered to the free-under-$\rho_0$ variables. Stripping the indices, its length equals that of the plain filtered list $t.\mathrm{filter}(\text{free})$ (`zipIdx_filter_length`), and entrywise the $k$-th literal of $\mathrm{lits}$ is the $k$-th free literal of $t$ (`zipIdx_filter_getElem_fst`). So $\mathrm{lits}$ names precisely the variables queried along the spine of the term subtree, in order — which is why consuming the first $|\mathrm{lits}|$ path steps corresponds exactly to descending past that spine.

5. **Dropping the spine from the deepest path leaves the deepest path of the continuation.** Using the canonical-path hypothesis rewritten through step 3, $\mathrm{path}=D_{\rho_0}.\mathrm{take}(|\mathrm{path}|)$ with $D_{\rho_0}$ the deepest path of the term subtree, and $|\mathrm{path}|\le\operatorname{depth}(T_{\rho_0})=|D_{\rho_0}|$. The core combinatorial lemma (`processClauseLits_termSubTree_drop`) says that, with the entrywise match of step 4 and the distinctness of the spine, dropping the first $|\mathrm{lits}|$ edges of the deepest path walks exactly down the term's spine into the continuation, so
\[
D_{\rho_0}.\mathrm{drop}(|\mathrm{lits}|)=\mathrm{deepPath}\big(\mathrm{cont}(\rho_0')\big).
\]

6. **The continuation at $\rho_0'$ is the canonical tree of $f|_{\rho_0'}$.** For this we need a strict drop in the number of free variables. Every variable named in $\mathrm{lits}$ is free under $\rho_0$ (that is the filter condition) and these variables are pairwise distinct (step 3), so each is genuinely fixed by the processing; the free-variable count satisfies $\rho_0'.\mathrm{numFree}+|\mathrm{lits}|=\rho_0.\mathrm{numFree}$ (`processClauseLits_numFree_ρ_eq`, with $m=|\mathrm{lits}|$). It remains to see $|\mathrm{lits}|\ge 1$. If instead $\mathrm{lits}$ were empty, then no literal of $t$ would have a free variable; since $t$ is not killed by $\rho_0$, every literal would then be assigned its *satisfying* value, making $t$ fixed by $\rho_0$ — contradicting step 3. Hence $|\mathrm{lits}|\ge 1$ and
\[
\rho_0.\mathrm{numFree}\ \ge\ \rho_0'.\mathrm{numFree}+1 .
\]
This strict decrease is the fuel bound under which $\mathrm{cont}(\rho_0')=T_{\rho_0'}$ (`cont_eq_canonicalDTree`): the "term fixed" branch collapses to the canonical leaf, and the recursive branch has enough fuel to coincide with the canonical tree of $f|_{\rho_0'}$. Taking deepest paths, $\mathrm{deepPath}(\mathrm{cont}(\rho_0'))=D_{\rho_0'}$.

7. **Assembling the two conclusions.** From the canonical-path hypothesis, dropping commutes with taking on the deepest path:
\[
\mathrm{path}'=\mathrm{path}.\mathrm{drop}(|\mathrm{lits}|)
=\big(D_{\rho_0}.\mathrm{drop}(|\mathrm{lits}|)\big).\mathrm{take}\big(|\mathrm{path}|-|\mathrm{lits}|\big).
\]
Substituting step 5 and then step 6,
\[
\mathrm{path}'=D_{\rho_0'}.\mathrm{take}\big(|\mathrm{path}|-|\mathrm{lits}|\big).
\]
Thus $\mathrm{path}'$ is an initial segment of the deepest path of $T_{\rho_0'}$, i.e. a canonical path for $f|_{\rho_0'}$; and its length is $\min(|\mathrm{path}|-|\mathrm{lits}|,\ |D_{\rho_0'}|)\le|D_{\rho_0'}|=\operatorname{depth}(T_{\rho_0'})$. Both claimed statements follow. $\qquad\blacksquare$

**Key facts.** `SwitchingLemma.processClauseLits_fst_eq_drop`, `SwitchingLemma.canonicalDTree_depth_zero_of_killed`, `SwitchingLemma.canonicalDTree_depth_zero_of_fixed`, `SwitchingLemma.canonicalDTree_alive_eq_termSubTree'`, `SwitchingLemma.zipIdx_filter_length`, `SwitchingLemma.zipIdx_filter_getElem_fst`, `SwitchingLemma.processClauseLits_termSubTree_drop`, `SwitchingLemma.processClauseLits_numFree_ρ_eq`, `SwitchingLemma.cont_eq_canonicalDTree`, `DecisionTree.length_deepPath`.
