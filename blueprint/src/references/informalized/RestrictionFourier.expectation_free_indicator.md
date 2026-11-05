<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/LMN/RestrictionCardTail.lean :: RestrictionFourier.expectation_free_indicator -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: claude-opus-4-8; confidence: high -->

# Total Bernoulli weight of restrictions leaving a coordinate free

**Claim.** Fix a real parameter $p$, a number of variables $n$, and a coordinate $i$. Each restriction $\rho$ on the $n$ variables fixes some coordinates and leaves others free, with free set $F(\rho)$ and Bernoulli weight $p^{|F(\rho)|}\bigl(\tfrac{1-p}{2}\bigr)^{\,n-|F(\rho)|}$. Summing this weight over exactly those restrictions that leave $i$ free yields $p$: the total Bernoulli weight assigned to the event "$i$ is a free variable" is $p$.

**Proof.** The claim is a single instance of a general formula for the Bernoulli weight of a "keep-this-set-free" event, read off at a one-point set.

For a set $T$ of coordinates, let
\[
W(T) \;=\; \sum_{\rho \,:\, T \subseteq F(\rho)} p^{|F(\rho)|}\Bigl(\tfrac{1-p}{2}\Bigr)^{\,n-|F(\rho)|}
\]
be the total Bernoulli weight of the restrictions whose free set contains all of $T$ — i.e. the restrictions that leave every coordinate in $T$ free. The engine behind the proof is the formula
\[
W(T) \;=\; p^{|T|},
\]
which says that leaving a prescribed set of coordinates free costs exactly one factor of $p$ per coordinate (`bernoulliRestrProb_subset_freeVars`). Intuitively, this is the independence of the coordinates under the Bernoulli-restriction distribution: each of the $|T|$ named coordinates is free with weight $p$, and the remaining coordinates are summed out to total weight $1$.

The proof applies this with the singleton $T = \{i\}$. Two observations finish it:

1. **The event matches the indicator.** A restriction $\rho$ satisfies $\{i\} \subseteq F(\rho)$ precisely when $i \in F(\rho)$, and by the definition of the free set this holds precisely when $\rho(i) = \mathrm{none}$, i.e. when $i$ is left free (`mem_freeVars`). Hence the indicator $\mathbf{1}[\rho(i) = \mathrm{none}]$ appearing in the stated sum is the same, restriction by restriction, as the indicator $\mathbf{1}[\{i\} \subseteq F(\rho)]$ defining $W(\{i\})$. The two weighted sums are therefore equal term by term, so the left-hand side of the claim equals $W(\{i\})$.

2. **Evaluate the formula.** Since $|\{i\}| = 1$, the general formula gives $W(\{i\}) = p^{1} = p$.

Chaining the two, the sum in the statement equals $W(\{i\}) = p$, as claimed.

**Key facts.** `RestrictionFourier.bernoulliRestrProb_subset_freeVars`, `RestrictionFourier.mem_freeVars`.
