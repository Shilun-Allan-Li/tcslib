<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Logspace/PathWalk.lean :: Complexity.walkLe_short -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Shortening the Walk Bound

**Claim.** If $c,t<n$ and there is a walk from $c$ to $t$ with bound $j$, then there is one with bound $n$.

**Proof.** For each bound $r$, let $S_r$ be the set of vertices below $n$ from which $t$ can be reached by a walk of bound $r$. These sets lie in the finite set of vertices below $n$, and they increase with $r$: increasing the allowed bound preserves a walk (the monotonicity of bounded walks, `Complexity.walkLe_mono`). Also, $t\in S_0$, since $t<n$ and the zero-bound walk from $t$ to itself is equality.

The recursive definition gives a useful stabilization property. If $S_r=S_{r+1}$, then $S_{r+1}=S_{r+2}$: membership at the next bound is either the equality case, or comes from a first step to some $v<n$ followed by a walk from $v$ to $t$. The equality of the two earlier sets says that for every such $v$, the latter walk condition is equivalent at bounds $r$ and $r+1$. Thus the same membership alternatives hold at the next pair of bounds.

There must be some $r_0\le n$ with $S_{r_0}=S_{r_0+1}$. Otherwise, since the sets increase, each inclusion from $S_r$ to $S_{r+1}$ for $r<n$ would be strict. Starting with the nonempty set $S_0$, this would force $S_n$ to have at least $n+1$ elements, though it is contained in a set of exactly $n$ vertices. By the stabilization property, all subsequent sets equal $S_{r_0}$. Finally, $S_j\subseteq S_n$ for every $j$: if $j\le n$, this follows from monotonicity; if $j>n$, stabilization makes $S_j=S_{r_0}$, and $r_0\le n$ gives $S_{r_0}\subseteq S_n$. Since $c<n$ and the assumed walk puts $c$ in $S_j$, it follows that $c\in S_n$, proving the claim.

**Key facts.** `Complexity.walkLe_mono`.
