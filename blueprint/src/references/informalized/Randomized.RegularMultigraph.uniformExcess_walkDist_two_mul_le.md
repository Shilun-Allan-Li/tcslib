<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Randomized/RandomWalkMixing.lean :: Randomized.RegularMultigraph.uniformExcess_walkDist_two_mul_le -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Nonbipartite Walk Contraction

**Claim.** Under the stated connectivity, nonbipartiteness, and degree bound, the uniform excess after $2|V|$ steps is at most $\left(1-1/|V|^{10|V|}\right)$ times the initial uniform excess.

**Proof.** The auxiliary contraction estimate gives the factor $1-|V|/D^{2|V|}$ (`uniformExcess_walkDist_two_mul_le_aux`). Put $n=|V|$. Since $D\le n^5$, raising both sides to the positive power $2n$ gives $D^{2n}\le n^{10n}$, and hence $1/n^{10n}\le 1/D^{2n}$. Also $n\ge1$, so $1/D^{2n}\le n/D^{2n}$. Thus $1/n^{10n}\le n/D^{2n}$, making the auxiliary contraction factor no larger than the claimed factor. The initial uniform excess is nonnegative (`uniformExcess_nonneg`), so multiplying the factor inequality by it preserves the order and yields the result.

**Key facts.** `Randomized.RegularMultigraph.uniformExcess_walkDist_two_mul_le_aux`, `Randomized.uniformExcess_nonneg`.
