<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/Hypercontractivity/Randomization/Basic.lean :: BooleanAnalysis.Hypercontractivity.RandomizationAux.component_tail_le_totalInfluence -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Component tail and total influence

**Claim.** For each $k$, $(k+1)$ times the sum of the squared component expectations over sets of size greater than $k$ is at most the total influence of $f$.

**Proof.** Express total influence as the sum over all coordinate sets $S$ of $|S|$ times the expectation of the squared $S$-component (\texttt{totalInfluence\_eq\_sum\_card\_components}); distribute the factor $k+1$ over the tail sum. For a set with $k<|S|$, the integer inequality gives $k+1\le |S|$. The squared-component expectation is nonnegative because it is a finite sum of nonnegative product masses times squares. Multiplying the cardinality inequality by this nonnegative quantity bounds that tail term by its total-influence term. For $|S|\le k$, the tail summand is zero and the corresponding total-influence term is nonnegative. Summing these termwise bounds proves the claim.

**Key facts.** `BooleanAnalysis.Hypercontractivity.RandomizationAux.totalInfluence_eq_sum_card_components`.
