<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/DecisionTree.lean :: DecisionTree.buildFull_depth -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: claude-opus-4-8; confidence: high -->

# Depth bound for the full decision tree

**Claim.** Let $f\colon\{0,1\}^n \to \{0,1\}$ be a Boolean function on $n$ variables, let $k \le n$, and let $acc$ be a partial assignment of the variables. The full decision tree $\mathrm{buildFull}(f,k,acc)$, which queries the variables $k, k+1, \dots, n-1$ in order (starting from the stored assignment $acc$) and places the value of $f$ at each leaf, has depth at most $n - k$.

**Proof.** The tree $\mathrm{buildFull}(f,k,acc)$ is defined by recursion on the quantity $n-k$: if $k < n$ it is a branch on variable $k$ whose two children are $\mathrm{buildFull}(f,k+1,acc')$ for the two ways $acc'$ of extending $acc$ at position $k$ (to $\mathrm{false}$ and to $\mathrm{true}$); if $k \ge n$ it is a leaf carrying the value $f(acc)$. The depth is $0$ at a leaf and $1 + \max(\text{left depth},\ \text{right depth})$ at a branch. The proof is the well-founded induction that mirrors this recursion exactly, so it splits on the same test $k < n$.

1. **Leaf case ($k \ge n$).** Here the tree is a single leaf, which has depth $0$. Since $0 \le n - k$ trivially (and indeed $k \le n$ together with $k \ge n$ forces $k = n$, so $n - k = 0$), the bound holds.

2. **Branch case ($k < n$).** The tree is a branch on variable $k$ with children $L = \mathrm{buildFull}(f,k+1,\ \mathrm{update}(acc,k,\mathrm{false}))$ and $R = \mathrm{buildFull}(f,k+1,\ \mathrm{update}(acc,k,\mathrm{true}))$, so its depth equals $1 + \max(\mathrm{depth}(L), \mathrm{depth}(R))$. Because $k < n$ we have $k+1 \le n$, so the inductive hypothesis applies to both children at the parameter $k+1$ (the recursive argument $n-(k+1)$ is strictly smaller, which is what justifies the recursion). It gives
\[
\mathrm{depth}(L) \le n - (k+1), \qquad \mathrm{depth}(R) \le n - (k+1).
\]
Taking the maximum of the two bounds, $\max(\mathrm{depth}(L),\mathrm{depth}(R)) \le n - (k+1)$. Therefore
\[
\mathrm{depth} \;=\; 1 + \max(\mathrm{depth}(L),\mathrm{depth}(R)) \;\le\; 1 + \big(n-(k+1)\big) \;=\; n - k,
\]
where the final equality is valid because $k < n$ makes the truncated subtraction behave like ordinary subtraction. This is the claimed bound, completing the induction.
