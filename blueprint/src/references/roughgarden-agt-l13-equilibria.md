<!-- generated-by: proofmatch Claude repair -->
<!-- source-pdf-sha256: 33b1d82024214fb478a0c294e0a7543740c733e85052a5b670e91ab047f021ba -->

<a id="pdf-33b1d8202421-p001-b001"></a>
<!-- pdf-source: page=1; block=1; confidence=0.95 -->
CS364A: Algorithmic Game Theory — Lecture #13 (Tim Roughgarden, Nov 4, 2013). Topics: potential games and a hierarchy of equilibrium concepts.

<a id="pdf-33b1d8202421-p001-b002"></a>
<!-- pdf-source: page=1; block=2; confidence=0.90 -->
Recap: pure Nash equilibria (PNE) of atomic selfish routing with affine costs $c_e(x)=a_e x+b_e$ ($a_e,b_e\ge 0$) have cost at most $\tfrac52$ times optimal, and this tight bound applies to all such equilibria. Open question motivating the lecture: does a PNE always exist (unlike Rock-Paper-Scissors)? The lecture introduces several equilibrium concepts and asks about their existence, computational tractability, and desirability.

<a id="pdf-33b1d8202421-p001-b003"></a>
<!-- pdf-source: page=1; block=3; confidence=0.95 -->
**Section 1. Potential Games and the Existence of Pure Nash Equilibria.**

<a id="pdf-33b1d8202421-p001-b004"></a>
<!-- pdf-source: page=1; block=4; confidence=0.97 -->
**Theorem 1.1 (Rosenthal's Theorem [4]).** Every atomic selfish routing game, with arbitrary real-valued cost functions, has at least one equilibrium flow (a PNE).

<a id="pdf-33b1d8202421-p001-b005"></a>
<!-- pdf-source: page=1; block=5; confidence=0.90 -->
**Proof (idea).** Show every atomic selfish routing game is a potential game: players collectively behave as if optimizing a single potential function. This is one of the few general tools guaranteeing PNE existence in a class of games. (Construction and details continue on the next page.)

<a id="pdf-33b1d8202421-p002-b001"></a>
<!-- pdf-source: page=2; block=1; confidence=0.98 -->
Figure 1: The function $c_e$ and its corresponding (underestimating) potential function.

<a id="pdf-33b1d8202421-p002-b002"></a>
<!-- pdf-source: page=2; block=2; confidence=0.93 -->
**Definition (potential function, Eq. (1)).** On flows of an atomic selfish routing game, define
$$\Phi(f)=\sum_{e\in E}\sum_{i=1}^{f_e} c_e(i),$$
where $f_e$ is the number of players whose chosen path in $f$ includes edge $e$. The inner sum is the discrete "area under the curve" of $c_e$, contrasted with the cost-objective term $f_e\cdot c_e(f_e)$ (bounding box).

<a id="pdf-33b1d8202421-p002-b003"></a>
<!-- pdf-source: page=2; block=3; confidence=0.93 -->
**Defining property (Eq. (2)).** For a flow $f$, player $i$ using $s_i$-$t_i$ path $P_i$, and a deviation to another $s_i$-$t_i$ path $\hat P_i$ yielding flow $\hat f$:
$$\Phi(\hat f)-\Phi(f)=\sum_{e\in\hat P_i} c_e(\hat f_e)-\sum_{e\in P_i} c_e(f_e).$$
The change in $\Phi$ under a unilateral deviation equals exactly the change in the deviator's individual cost, so $\Phi$ simultaneously tracks the effect of each player's deviations.

<a id="pdf-33b1d8202421-p002-b004"></a>
<!-- pdf-source: page=2; block=4; confidence=0.92 -->
**Verification of (2).** The inner sum for edge $e$ gains the extra term $c_e(f_e+1)$ when $e$ becomes newly used (in $\hat P_i\setminus P_i$) and loses its final term $c_e(f_e)$ when $e$ becomes newly unused (in $P_i\setminus\hat P_i$). Hence the left side of (2) equals
$$\sum_{e\in\hat P_i\setminus P_i} c_e(f_e+1)-\sum_{e\in P_i\setminus\hat P_i} c_e(f_e),$$
which matches the right side of (2).

<a id="pdf-33b1d8202421-p002-b005"></a>
<!-- pdf-source: page=2; block=5; confidence=0.90 -->
**Proof (conclusion, part).** Let $f$ minimize $\Phi$; such a minimizer exists since there are finitely many flows. No unilateral deviation decreases $\Phi$, so by (2) no player can decrease its cost by deviating. (Continues on next page.)

<a id="pdf-33b1d8202421-p003-b001"></a>
<!-- pdf-source: page=3; block=1; confidence=0.92 -->
**Proof (conclusion).** Therefore the $\Phi$-minimizing flow $f$ is an equilibrium flow. $\blacksquare$

<a id="pdf-33b1d8202421-p003-b002"></a>
<!-- pdf-source: page=3; block=2; confidence=0.93 -->
**Section 2. Extensions.** The proof technique of Theorem 1.1 extends to further settings.

<a id="pdf-33b1d8202421-p003-b003"></a>
<!-- pdf-source: page=3; block=3; confidence=0.90 -->
**Extension 1.** The proof holds for arbitrary cost functions, nondecreasing or not (used in Lecture 15 for games with positive externalities). **Extension 2.** The proof never uses network structure, so it applies to congestion games: an abstract resource set $E$ (each with a cost function), where each player $i$ has an arbitrary strategy collection $S_i\subseteq 2^E$ of resource subsets (Lecture 19).

<a id="pdf-33b1d8202421-p003-b004"></a>
<!-- pdf-source: page=3; block=4; confidence=0.90 -->
**Extension 3 (nonatomic selfish routing).** Replace the inner sum by an integral (Eq. (3)):
$$\Phi(f)=\sum_{e\in E}\int_0^{f_e} c_e(x)\,dx,$$
with $f_e$ the traffic on edge $e$. Costs continuous and nondecreasing make $\Phi$ continuously differentiable and convex. The first-order optimality conditions of $\Phi$ are exactly the equilibrium conditions, so local minima of $\Phi$ are equilibrium flows. By continuity and compactness of the flow space, $\Phi$ attains a global minimum, proving existence of an equilibrium flow. Convexity gives uniqueness (all local minima are global); multiple global minima share the same potential value and correspond to multiple equilibrium flows of equal total cost. Details in [5].

<a id="pdf-33b1d8202421-p003-b005"></a>
<!-- pdf-source: page=3; block=5; confidence=0.90 -->
**Section 3. A Hierarchy of Equilibrium Concepts.** Motivation: analyzing POA when no PNE exists — e.g. Rock-Paper-Scissors, and atomic selfish routing with varying player sizes (no PNE even with two players and quadratic costs [5, Example 18.4]). To recover guaranteed existence, enlarge the equilibrium set. The lecture introduces three relaxations of PNE, each more permissive and more computationally tractable than the last (Figure 2); all three are guaranteed to exist in every finite game.

<a id="pdf-33b1d8202421-p004-b001"></a>
<!-- pdf-source: page=4; block=1; confidence=0.95 -->
**Figure 2:** The Venn-diagram of the hierarchy of equilibrium concepts: PNE ⊆ MNE ⊆ CE ⊆ CCE. Noted properties: PNE need not exist; MNE are guaranteed to exist but hard to compute; CE are easy to compute; CCE are even easier to compute.

<a id="pdf-33b1d8202421-p004-b002"></a>
<!-- pdf-source: page=4; block=2; confidence=0.95 -->
**Section 3.1 (Cost-Minimization Games).** A cost-minimization game consists of: a finite number k of players; a finite strategy set $S_i$ for each player i; and a cost function $C_i(s)$ for each player i, where $s \in S_1 \times \cdots \times S_k$ is a strategy profile (outcome). Example: atomic routing games, where $C_i(s)$ is player i's travel time on its chosen path given the others' paths $s_{-i}$. Equilibrium concepts here are the cost-minimization analogues of the standard payoff-maximization definitions, with all inequalities reversed; the two formulations are equivalent.

<a id="pdf-33b1d8202421-p004-b003"></a>
<!-- pdf-source: page=4; block=3; confidence=0.96 -->
**Definition 3.1 (PNE).** A strategy profile s of a cost-minimization game is a pure Nash equilibrium if for every player $i \in \{1,\dots,k\}$ and every unilateral deviation $s_i' \in S_i$,
$$C_i(s) \le C_i(s_i', s_{-i}). \quad (4)$$
Unilateral deviations can only increase a player's cost. PNE need not exist; the price of anarchy (POA) of PNE is left undefined in games with no PNE.

<a id="pdf-33b1d8202421-p005-b001"></a>
<!-- pdf-source: page=5; block=1; confidence=0.94 -->
**Definition 3.2 (MNE).** Distributions $\sigma_1,\dots,\sigma_k$ over strategy sets $S_1,\dots,S_k$ of a cost-minimization game form a mixed Nash equilibrium if for every player $i \in \{1,\dots,k\}$ and every unilateral deviation $s_i' \in S_i$,
$$E_{s\sim\sigma}[C_i(s)] \le E_{s\sim\sigma}[C_i(s_i', s_{-i})], \quad (5)$$
where $\sigma = \sigma_1 \times \cdots \times \sigma_k$ is the product distribution. Allowing mixed-strategy deviations does not change the definition (exercise). Every PNE is an MNE with deterministic play; some games have MNE that are not PNE (Rock-Paper-Scissors). Key facts (Lecture 20): every cost-minimization game has at least one MNE (Nash's theorem [3]); computing an MNE appears computationally intractable (roughly NP-complete), even for two players. Guaranteed MNE existence makes the POA of MNE well defined in every finite game.

<a id="pdf-33b1d8202421-p005-b002"></a>
<!-- pdf-source: page=5; block=2; confidence=0.95 -->
**Definition 3.3 (CE).** A distribution $\sigma$ on the set of outcomes $S_1 \times \cdots \times S_k$ of a cost-minimization game is a correlated equilibrium if for every player $i \in \{1,\dots,k\}$, every strategy $s_i \in S_i$, and every deviation $s_i' \in S_i$,
$$E_{s\sim\sigma}[C_i(s) \mid s_i] \le E_{s\sim\sigma}[C_i(s_i', s_{-i}) \mid s_i]. \quad (6)$$

<a id="pdf-33b1d8202421-p006-b001"></a>
<!-- pdf-source: page=6; block=1; confidence=0.92 -->
The CE distribution $\sigma$ (Definition 3.3) need not be a product distribution, so players' strategies may be correlated. The MNE of a game are exactly the CE that are product distributions (exercise); since MNE exist, so do CE. CE have an equivalent characterization via "switching functions" (exercise). Standard interpretation [1]: a trusted third party knows public $\sigma$, samples outcome $s \sim \sigma$, and privately recommends $s_i$ to each player i. Each player, knowing $\sigma$ and its own $s_i$ (hence a posterior on $s_{-i}$), can obey or deviate; condition (6) states that obeying the recommendation minimizes expected cost, assuming others obey. CE are computationally tractable (Lecture 18), e.g. via linear programming, and distributed learning algorithms drive the history of joint play toward the set of CE.

<a id="pdf-33b1d8202421-p006-b002"></a>
<!-- pdf-source: page=6; block=2; confidence=0.90 -->
Example of a CE that is not an MNE: a two-player 2×2 game with strategies {stop, go}. Payoff bimatrix (row, column): (stop,stop)=(0,0), (stop,go)=(0,1), (go,stop)=(1,0), (go,go)=(−5,−5). The two PNE are (stop,go) and (go,stop). Let $\sigma$ randomize 50/50 between these two PNE. This $\sigma$ is not a product distribution, so it is not an MNE, but it is a CE: e.g. when the trusted third party recommends "go" to the row player, the row player infers the column player was told "stop," and given that, "go" is a best response; symmetrically for "stop."

<a id="pdf-33b1d8202421-p006-b003"></a>
<!-- pdf-source: page=6; block=3; confidence=0.85 -->
**Section 3.5 (Coarse Correlated Equilibria).** Motivates enlarging the set of equilibria beyond CE to an even more computationally tractable concept while retaining good POA bounds. (Definition follows on subsequent pages, not included here.)

<a id="pdf-33b1d8202421-p007-b001"></a>
<!-- pdf-source: page=7; block=1; confidence=0.98 -->
**Definition 3.4 ([2]).** A distribution $\sigma$ over outcomes $S_1 \times \cdots \times S_k$ of a cost-minimization game is a *coarse correlated equilibrium (CCE)* if for every player $i \in \{1,\dots,k\}$ and every unilateral deviation $s_i' \in S_i$,
$$\mathbb{E}_{s\sim\sigma}[C_i(s)] \le \mathbb{E}_{s\sim\sigma}[C_i(s_i', s_{-i})]. \quad (7)$$

<a id="pdf-33b1d8202421-p007-b002"></a>
<!-- pdf-source: page=7; block=2; confidence=0.95 -->
In (7) the deviating player knows only $\sigma$, not the realized component $s_i$; thus a CCE protects only against *unconditional* unilateral deviations, unlike the conditional deviations of Definition 3.3. Every CE is a CCE, so CCE exist in every finite game and are computationally tractable; distributed learning algorithms converging to CCE are simpler than those for CE.

<a id="pdf-33b1d8202421-p007-b003"></a>
<!-- pdf-source: page=7; block=3; confidence=0.97 -->
## 3.6 An Example

Concrete example illustrating the four equilibrium concepts and showing all inclusions can be strict.

<a id="pdf-33b1d8202421-p007-b004"></a>
<!-- pdf-source: page=7; block=4; confidence=0.97 -->
**Example.** Atomic selfish routing game (Lecture 12) with 4 players; network is a common source $s$, common sink $t$, and 6 parallel $s$-$t$ edges $E=\{0,1,2,3,4,5\}$, each with cost $c(x)=x$.

- **Pure Nash equilibria:** the $\binom{6}{4}$ outcomes where players occupy distinct edges; each player incurs unit cost.
- **Mixed (non-pure) NE:** each player independently picks an edge uniformly at random; each has expected cost $3/2$.
- **Correlated equilibrium (non-product):** uniform distribution over outcomes with one edge holding two players and two edges holding one player each; both sides of (6) equal $3/2$ for every $i, s_i, s_i'$.
- **Coarse correlated equilibrium:** uniform distribution over the subset of those outcomes whose chosen-edge set is $\{0,2,4\}$ or $\{1,3,5\}$; both sides of (7) equal $3/2$ for every $i, s_i'$. It is *not* a CE, since a player recommended edge $s_i$ can cut its conditional expected cost to $1$ by deviating to the successive edge (mod 6).

<a id="pdf-33b1d8202421-p007-b005"></a>
<!-- pdf-source: page=7; block=5; confidence=0.97 -->
## 3.7 Looking Ahead: POA Bounds for Tractable Equilibrium Concepts

<a id="pdf-33b1d8202421-p007-b006"></a>
<!-- pdf-source: page=7; block=6; confidence=0.93 -->
Enlarging the equilibrium set increases tractability and plausibility but generally forfeits desirable properties. POA bounds compare the worst-equilibrium objective value to the optimal; a larger equilibrium set worsens (moves away from 1) the POA. The open question — whether a "sweet spot" concept is simultaneously tractable and admits strong worst-case guarantees — is answered affirmatively for many game classes in the next lecture.

<a id="pdf-33b1d8202421-p008-b001"></a>
<!-- pdf-source: page=8; block=1; confidence=0.97 -->
**References.** [1] Aumann, *Subjectivity and correlation in randomized strategies*, J. Math. Econ. 1(1):67–96, 1974. [2] Moulin & Vial, *Strategically zero-sum games*, Int. J. Game Theory 7(3/4):201–221, 1978. [3] Nash, *Equilibrium points in N-person games*, PNAS 36(1):48–49, 1950. [4] Rosenthal, *A class of games possessing pure-strategy Nash equilibria*, Int. J. Game Theory 2(1):65–67, 1973. [5] Roughgarden, *Routing games*, in Nisan, Roughgarden, Tardos & Vazirani (eds.), *Algorithmic Game Theory*, ch. 18, pp. 461–486, Cambridge Univ. Press, 2007.
