<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Expanders/Walks.lean :: Expander.walk_filter_sum -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Endpoint Distribution for Restricted Walks

**Claim.** For every $k$ and state $j$, the probability sum over walks whose states all lie in $B$ and whose final state is $j$ equals the $j$th coordinate of the vector obtained by starting with mass $1/n$ on states in $B$ and applying the matrix that retains only rows indexed by $B$ at each step.

**Proof.** Proceed by induction on the walk length, with a separate check of whether the specified endpoint belongs to $B$.

At length zero, a walk has just one state. If $j\in B$, the only qualifying walk is the constant walk at $j$; its probability is $1/n$ by the uniform initial distribution, matching the initial restricted vector’s $j$th coordinate. If $j\notin B$, there are no qualifying walks and that coordinate is zero. These are precisely the two cases of the initial vector’s definition.

For the successor step, first suppose $j\in B$. Write each extended walk uniquely as a prefix $g$ followed by a final state $x$. The condition that all its states lie in $B$ is equivalent to all states of $g$ lying in $B$ and $x\in B$. Its final-state condition forces $x=j$, so summing over extensions reduces to summing over eligible prefixes. By the extension-probability formula (`Expander.walkPMF_succ_apply`), each prefix contributes its probability multiplied by $\operatorname{ENNReal.ofReal}(A_{g_kj})$.

Group those prefixes by their own final state $l$. Within a group, the transition factor is constant, so it factors out of the sum. The induction hypothesis (`Expander.walk_filter_sum`) identifies the group’s probability sum with $\operatorname{ENNReal.ofReal}(\mathrm{resVec}(A,B,k)_l)$. Thus the total is the sum over $l$ of the products of this coordinate and the transition weight from $l$ to $j$. Nonnegativity of the restricted-vector coordinates (`Expander.resVec_nonneg`) and of the matrix entries ensures these products and sums correspond under conversion from real to extended-real values. Finally, symmetry gives $A_{lj}=A_{jl}$, so this sum is exactly the $j$th coordinate of the next restricted vector, whose $j$th row is retained because $j\in B$.

If instead $j\notin B$, no walk with every state in $B$ can end at $j$, so the probability sum is zero. The next restricted vector’s $j$th coordinate is also zero because its row is discarded. This completes the induction.

**Key facts.** `Expander.walkPMF_zero_apply`, `Expander.walkPMF_succ_apply`, `Expander.resVec_nonneg`.
