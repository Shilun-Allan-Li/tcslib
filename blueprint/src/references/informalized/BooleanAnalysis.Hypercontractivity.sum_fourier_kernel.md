<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/Hypercontractivity/Cube/General/Kernel.lean :: BooleanAnalysis.Hypercontractivity.sum_fourier_kernel -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: claude-opus-4-8; confidence: high -->

# The Fourier form of the noise kernel as a product over coordinates

**Claim.** Fix a natural number $n$ and a real number $\rho$, and let $x, y$ be points of the Boolean cube $\{0,1\}^n$. Writing $\sigma$ for the sign encoding ($0 \mapsto 1$, $1 \mapsto -1$) and $\chi_S(x) = \prod_{i \in S} \sigma(x_i)$ for the Walsh–Fourier character indexed by a subset $S \subseteq [n]$, the sum of $\rho^{|S|}\chi_S(x)\chi_S(y)$ over all subsets $S$ equals the coordinatewise product $\prod_{i=1}^n \bigl(1 + \rho\,\sigma(x_i)\,\sigma(y_i)\bigr)$. In other words, the degree-weighted correlation kernel factorises as an independent product over the $n$ coordinates.

**Proof.** The two sides are matched by expanding the product over coordinates into a sum over subsets, and then checking that the two sums agree term by term. It is cleaner to start from the right.

1. **Expand the product into a sum over subsets.** Each factor of the right-hand side is a binomial $1 + t_i$, with $t_i := \rho\,\sigma(x_i)\,\sigma(y_i)$. Multiplying out $\prod_{i=1}^n (1 + t_i)$, each term of the expansion is obtained by choosing, for every coordinate $i$, either the summand $t_i$ or the summand $1$; recording the set $S$ of coordinates where $t_i$ was chosen turns the expansion into a sum indexed by subsets $S \subseteq [n]$, with the term for $S$ equal to $\prod_{i \in S} t_i$ (the omitted coordinates contribute a factor of $1$). This is the distributive expansion of a product of sums (`Finset.prod_add`), and it gives
\[
   \prod_{i=1}^n \bigl(1 + \rho\,\sigma(x_i)\,\sigma(y_i)\bigr)
   \;=\; \sum_{S \subseteq [n]} \ \prod_{i \in S} \rho\,\sigma(x_i)\,\sigma(y_i).
\]

2. **Match the two sums term by term.** It now suffices to show, for each fixed subset $S$, that the summand just produced equals the corresponding summand $\rho^{|S|}\chi_S(x)\chi_S(y)$ on the left. Inside a single term the factors commute, so the product over $i \in S$ splits into three separate products (`Finset.prod_mul_distrib`):
\[
   \prod_{i \in S} \rho\,\sigma(x_i)\,\sigma(y_i)
   \;=\; \Bigl(\prod_{i \in S} \rho\Bigr)\cdot\Bigl(\prod_{i \in S} \sigma(x_i)\Bigr)\cdot\Bigl(\prod_{i \in S} \sigma(y_i)\Bigr).
\]
The first factor is a constant $\rho$ multiplied over the $|S|$ elements of $S$, hence $\rho^{|S|}$. The remaining two factors are, by the very definition of the character $\chi_S(z) = \prod_{i \in S}\sigma(z_i)$, exactly $\chi_S(x)$ and $\chi_S(y)$. Therefore the term for $S$ equals $\rho^{|S|}\chi_S(x)\chi_S(y)$.

Since the two sums agree summand by summand over all $S \subseteq [n]$, they are equal, which is the claimed identity.
