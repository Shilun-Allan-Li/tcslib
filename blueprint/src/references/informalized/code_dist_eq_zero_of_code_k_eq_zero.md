<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/ErrorCorrectingCodes/QuantumSingleton.lean :: code_dist_eq_zero_of_code_k_eq_zero -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: claude-opus-4-8; confidence: high -->

# Zero Logical Dimension Forces Zero Code Distance

**Claim.** Let $p$ be a prime and let $S$ be a subspace of the symplectic space $V = \mathbb{F}_p^n \times \mathbb{F}_p^n$, equipped with the symplectic form $\langle u,v\rangle = \sum_{i} \big(u_1(i)\,v_2(i) - u_2(i)\,v_1(i)\big)$. Suppose $S$ is isotropic, meaning $S \subseteq S^{\perp}$, where $S^{\perp}$ is the orthogonal complement with respect to this form. If the logical dimension vanishes, $k(S) = n - \dim S = 0$, then the code distance vanishes as well, $d(S) = 0$. Here $d(S)$ is the least weight of a vector lying in $S^{\perp}$ but not in $S$, with the convention that an infimum over the empty set is $0$.

**Proof.** The argument is a dimension count that collapses the set defining the distance to the empty set.

1. **The hypothesis pins $\dim S$ to $n$.** An isotropic subspace of a $2n$-dimensional symplectic space can have dimension at most half the ambient dimension, so $\dim S \le n$ (`finrank_le_n_of_isotropic`). On the other hand, unwinding the definition $k(S) = n - \dim S$, the hypothesis $k(S) = 0$ says $n - \dim S = 0$ in the natural numbers, which is exactly $n \le \dim S$. Together these two inequalities force
\[
\dim S = n.
\]

2. **The orthogonal complement has the same dimension.** The symplectic form is nondegenerate, so the orthogonal complement of any subspace satisfies $\dim S^{\perp} = 2n - \dim S$ (`finrank_sym_orth`). Substituting $\dim S = n$ gives
\[
\dim S^{\perp} = 2n - n = n = \dim S.
\]

3. **$S$ is its own orthogonal complement.** Isotropy gives the inclusion $S \subseteq S^{\perp}$, and by step 2 both spaces have the same (finite) dimension $n$. A subspace contained in another of equal finite dimension must equal it (`Submodule.eq_of_le_of_finrank_eq`), so
\[
S = S^{\perp}.
\]
In other words, the maximal isotropic condition $k(S)=0$ makes $S$ self-dual.

4. **The distance is an infimum over an empty set.** By definition $d(S)$ is the infimum of the weights $\mathrm{wt}(v)$ over all vectors $v$ with $v \in S^{\perp}$ and $v \notin S$. Since $S = S^{\perp}$, no vector can lie in $S^{\perp}$ while failing to lie in $S$; the indexing set is empty. With the standard convention that the infimum of the empty set of natural numbers is $0$, we conclude $d(S) = 0$.

**Key facts.** `finrank_le_n_of_isotropic`, `finrank_sym_orth`.
