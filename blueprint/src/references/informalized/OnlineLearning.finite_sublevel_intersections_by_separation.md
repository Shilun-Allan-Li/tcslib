<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/LearningTheory/Minimax/ConvexMinimaxSeparation.lean :: OnlineLearning.finite_sublevel_intersections_by_separation -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Finite Sublevel Intersection

**Claim.** For every positive $\varepsilon$ and finite sample of columns, there is a row in $X$ whose payoff on each sampled column is at most the lower value plus $\varepsilon$.

**Proof.** 1. Write $v=\sup_{y\in Y}\inf_{x\in X}f(x,y)$, $c=v+\varepsilon$, and let $cvec$ be the constant vector with value $c$ on the finite sample $u$. If $cvec$ belongs to the finite upper image, some $x\in X$ has $f(x,y)<c$ for every sampled column. This immediately gives the required weak inequalities.

2. Otherwise, separate the point $cvec$ from the open convex finite upper image by a continuous linear functional, using geometric Hahn–Banach separation. Convexity of the upper image follows from convexity of $X$ and convexity of the payoff in the row variable (OnlineLearning.finiteUpperImage_convex); its openness is supplied by OnlineLearning.finiteUpperImage_isOpen. The separating functional has nonpositive value on each coordinate vector (OnlineLearning.separating_coordinate_nonpos), and the sum $W$ of the negatives of those coordinate values is strictly positive (OnlineLearning.separating_weight_sum_pos).

3. Normalize those negatives by $W$ to obtain weights $q_y$. They are nonnegative and sum to one. Expanding the separating inequality in coordinates and dividing by $W$ shows that, for every $x\in X$, $c\le\sum_{y\in u}q_y f(x,y)$ (OnlineLearning.separating_functional_normalized_le).

4. Let $\bar y=\sum_{y\in u}q_y y$. Since the weights form a probability distribution and $Y$ is convex, $\bar y\in Y$. Concavity in the column variable gives $\sum_y q_y f(x,y)\le f(x,\bar y)$ for each $x\in X$, by Jensen's inequality. Hence $c\le f(x,\bar y)$ for every row point. Taking the infimum over $x$, then comparing with the supremum over columns, gives $c\le v$. This contradicts $c=v+\varepsilon$ with $\varepsilon>0$. Therefore the separated case is impossible, and the finite sublevel intersection is nonempty.

**Key facts.** `OnlineLearning.finiteUpperImage_convex`, `OnlineLearning.finiteUpperImage_isOpen`, `OnlineLearning.separating_coordinate_nonpos`, `OnlineLearning.separating_weight_sum_pos`, `OnlineLearning.separating_functional_normalized_le`.
