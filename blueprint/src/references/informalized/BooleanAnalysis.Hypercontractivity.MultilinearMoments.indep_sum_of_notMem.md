<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/Hypercontractivity/RandomVariables/Polynomial.lean :: BooleanAnalysis.Hypercontractivity.MultilinearMoments.indep_sum_of_notMem -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Independence from Sums Omitting a Coordinate

**Claim.** If the coordinates are mutually independent and almost everywhere measurable, and $i\notin s$, then $X_i$ is independent of the pair of multilinear sums indexed by subsets of $s$.

**Proof.** Regard the coordinates indexed by $s$ as a tuple valued in $\mathbb R^s$. Extend each polynomial evaluation to all of $\mathbb R^s$ by using the coordinate values for indices in $s$ (and zero for indices outside $s$). These evaluations are measurable: they are finite sums and products of measurable coordinate projections. Independence of the coordinate subfamilies on the disjoint sets $\{i\}$ and $s$ implies independence of the $i$-coordinate from the tuple indexed by $s$. Applying measurable functions to the respective members preserves independence. The first function selects $X_i$, and the second maps the tuple to the pair of polynomial evaluations. Evaluating that map on the random tuple gives exactly the two stated sums, proving the result.
