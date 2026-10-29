<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/Basic.lean :: BooleanAnalysis.influence_chi -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: claude-opus-4-8; confidence: high -->

# Influence of a Walsh Character Equals Its Indicator

**Claim.** Fix a dimension $n$, a coordinate $i \in [n]$, and a set $S \subseteq [n]$. Then the influence of coordinate $i$ on the Walsh–Fourier character $\chi_S$ is $1$ when $i \in S$ and $0$ when $i \notin S$. Here $\chi_S(x) = \prod_{j \in S} (-1)^{x_j}$ on the Boolean cube $\{0,1\}^n$, and the influence is $\mathrm{Inf}_i[f] = \mathbb{E}_x\!\left[\tfrac{1}{4}\bigl(f(x) - f(x^{\oplus i})\bigr)^2\right]$, where $x^{\oplus i}$ denotes $x$ with its $i$-th bit flipped and $\mathbb{E}$ is the average over the uniform measure on the cube.

**Proof.** The proof unfolds the definition of influence and splits on whether the coordinate $i$ belongs to $S$. In both cases the quantity being averaged turns out to be *constant* in $x$, so the expectation is that constant, and the two constants are exactly $1$ and $0$.

Throughout, write $x^{\oplus i}$ for the point obtained from $x$ by flipping its $i$-th coordinate, and recall the influence is the uniform average
\[
  \mathrm{Inf}_i[\chi_S] \;=\; \frac{1}{2^n}\sum_{x \in \{0,1\}^n} \frac{\bigl(\chi_S(x) - \chi_S(x^{\oplus i})\bigr)^2}{4}.
\]
The whole argument rests on two elementary facts about characters:

- **Flipping a bit in the support negates the character** (`chiS_flipBit`): $\chi_S(x^{\oplus i}) = -\chi_S(x)$ if $i \in S$, and $\chi_S(x^{\oplus i}) = \chi_S(x)$ if $i \notin S$. This is immediate from the product definition: flipping coordinate $i$ changes the factor $(-1)^{x_i}$ to its negative when that factor is present (i.e. $i \in S$), and leaves the product untouched otherwise.
- **Characters are $\pm 1$-valued** (`chiS_sq_eq_one`): $\chi_S(x)^2 = 1$ for every $x$, since each factor $\mathrm{boolToSign}(x_j) \in \{-1, +1\}$ and squares to $1$.

1. **Case $i \in S$.** Fix any point $x$. By the negation fact, $\chi_S(x^{\oplus i}) = -\chi_S(x)$, so the difference inside the average is
\[
  \chi_S(x) - \chi_S(x^{\oplus i}) \;=\; \chi_S(x) - \bigl(-\chi_S(x)\bigr) \;=\; 2\,\chi_S(x).
\]
Squaring and dividing by $4$ gives $\tfrac{1}{4}(2\chi_S(x))^2 = \chi_S(x)^2$, which equals $1$ by the $\pm 1$-valued fact. (The Lean proof records this last step as a small algebraic identity: from $c^2 = 1$ one gets $(2c)^2/4 = 1$.) Thus the summand is identically $1$, so the sum over the cube is just its number of points. The Boolean cube $\{0,1\}^n$ has $2^n$ elements, and the uniform weight is $2^{-n}$, so
\[
  \mathrm{Inf}_i[\chi_S] \;=\; \frac{1}{2^n}\sum_{x} 1 \;=\; \frac{1}{2^n}\cdot 2^n \;=\; 1.
\]

2. **Case $i \notin S$.** Fix any $x$. Now the negation fact degenerates: flipping a bit outside the support leaves the character unchanged, $\chi_S(x^{\oplus i}) = \chi_S(x)$. Hence the difference $\chi_S(x) - \chi_S(x^{\oplus i})$ is $0$, its square divided by $4$ is $0$, and the summand vanishes for every $x$. The average of the zero function is $0$, so $\mathrm{Inf}_i[\chi_S] = 0$.

Combining the two cases yields the claimed indicator value, $\mathrm{Inf}_i[\chi_S] = \mathbf{1}[\,i \in S\,]$.

**Key facts.** `BooleanAnalysis.chiS_flipBit`, `BooleanAnalysis.chiS_sq_eq_one`.
