<!-- generated-by: proofmatch Claude repair -->
<!-- source-pdf-sha256: 9c61a2f1ecc11f96a5403f7423ad07671dc78eb0fde46b49551c8717c18639cc -->

<a id="pdf-9c61a2f1ecc1-p001-b001"></a>
<!-- pdf-source: page=1; block=1; confidence=0.97 -->
# Adaptive game playing using multiplicative weights

Yoav Freund and Robert E. Schapire (AT&T Labs, Shannon Laboratory). Published in *Games and Economic Behavior*, 29:79–103, 1999.

<a id="pdf-9c61a2f1ecc1-p001-b002"></a>
<!-- pdf-source: page=1; block=2; confidence=0.95 -->
Presents a simple algorithm for repeated-game play whose average loss provably approaches the minimum achievable by any fixed strategy. Bounds are non-asymptotic and hold against any opponent. Uses the multiplicative-weights method of Littlestone and Warmuth; analyzed via Kullback–Leibler divergence. Yields a new simple proof of the minmax theorem, a provable method for approximately solving a game, and a variant proved optimal in a strong sense.

<a id="pdf-9c61a2f1ecc1-p001-b003"></a>
<!-- pdf-source: page=1; block=3; confidence=0.97 -->
## 1 Introduction

<a id="pdf-9c61a2f1ecc1-p001-b004"></a>
<!-- pdf-source: page=1; block=4; confidence=0.92 -->
Studies learning to play a repeated game defined by a matrix M. Each round the row player picks row i, the column player picks column j; entry M(i,j) is the row player's loss. Analysis is from the row player's perspective; the column player's utility is unspecified. A basic goal is to suffer loss no worse than the game value (viewing M as zero-sum), achievable via a minmax mixed strategy computed by linear programming — but only if M is known, small enough, and the opponent is truly adversarial. In repeated play one can instead learn to play well against the actual opponent. Prior algorithms with this guarantee: Hannan [20], Blackwell [3], and Foster–Vohra [14,15,13].

<a id="pdf-9c61a2f1ecc1-p002-b001"></a>
<!-- pdf-source: page=2; block=1; confidence=0.93 -->
The proposed algorithm has non-asymptotic bounds valid for any finite number of rounds, based on the on-line prediction methods of Littlestone and Warmuth [25]. Organization: §2 setup and notation; §3 the basic multiplicative-weights algorithm (average performance nearly as good as the best fixed mixed strategy); §4 relation to prior multiplicative-weights on-line prediction work; §5 a simple proof of von Neumann's minmax theorem; §6 a variant whose distributions converge to an optimal mixed strategy, with application to linear programming; §7 asymptotic optimality of the convergence rate of that second variant.

<a id="pdf-9c61a2f1ecc1-p002-b002"></a>
<!-- pdf-source: page=2; block=2; confidence=0.97 -->
## 2 Playing repeated games

<a id="pdf-9c61a2f1ecc1-p002-b003"></a>
<!-- pdf-source: page=2; block=3; confidence=0.95 -->
**Definition (setup).** A non-collaborative two-person normal-form game given by a matrix M with n rows and m columns. Row player picks row i, column player picks column j simultaneously; M(i,j) is the row player's loss. All entries are assumed in [0,1] (general bounded ranges follow by scaling); the number of choices per player is finite. A *pure strategy* is a specific row/column; a *mixed strategy* is a distribution over rows/columns. Notation: P denotes a row-player mixed strategy, Q a column-player mixed strategy; M(P,Q) = P^T M Q is the expected loss; M(i,Q) and M(P,j) denote expected loss when one side plays pure and the other mixed. P* and Q* denote optimal mixed strategies for M, and the value of the game is v = M(P*, Q*).

<a id="pdf-9c61a2f1ecc1-p002-b004"></a>
<!-- pdf-source: page=2; block=4; confidence=0.88 -->
The main object is an algorithm that adaptively selects mixed strategies for one player (the row player) over repeated play. Row and column players are also called the *learner* and the *environment*. Repeated play is a sequence of rounds; the game matrix M is fixed but unknown to the learner, who knows only its number of rows. Rounds are indexed t = 1, …, T.

<a id="pdf-9c61a2f1ecc1-p003-b001"></a>
<!-- pdf-source: page=3; block=1; confidence=0.85 -->
**Definition (round t protocol).**
1. Learner chooses mixed strategy P_t.
2. Environment chooses mixed strategy Q_t (possibly knowing P_t).
3. Learner observes the loss M(i,Q_t) for each row i (the loss it would have incurred playing pure strategy i).
4. Learner suffers loss M(P_t,Q_t).

Basic goal: minimize total loss ∑_{t=1}^{T} M(P_t,Q_t). Against a maximally adversarial environment a related goal is to approximate the optimal row strategy P*; in benign environments the goal is minimum possible loss, potentially far below the game value.

<a id="pdf-9c61a2f1ecc1-p003-b002"></a>
<!-- pdf-source: page=3; block=2; confidence=0.90 -->
**Definition (relative entropy).** For distributions P1, P2, RE(P1 ‖ P2) = ∑_i P1(i) · ln(P1(i)/P2(i)). It is nonnegative and equals zero iff P1 = P2. For real numbers p1, p2 ∈ [0,1], RE(p1 ‖ p2) denotes the relative entropy between Bernoulli distributions with those parameters: RE(p1 ‖ p2) = p1 ln(p1/p2) + (1−p1) ln((1−p1)/(1−p2)).

<a id="pdf-9c61a2f1ecc1-p003-b003"></a>
<!-- pdf-source: page=3; block=3; confidence=0.97 -->
## 3 The basic algorithm

<a id="pdf-9c61a2f1ecc1-p003-b004"></a>
<!-- pdf-source: page=3; block=4; confidence=0.96 -->
**Definition (Algorithm MW).** A direct generalization of Littlestone–Warmuth's weighted majority algorithm [25] (also discovered independently by Fudenberg and Levine [17]). MW starts from an initial mixed strategy P_1, used on round 1. After round t it forms P_{t+1} by the multiplicative update

P_{t+1}(i) = P_t(i) · β^{M(i,Q_t)} / Z_t,

where Z_t = ∑_i P_t(i) · β^{M(i,Q_t)} is a normalization factor and β ∈ [0,1) is a parameter of the algorithm.

<a id="pdf-9c61a2f1ecc1-p003-b005"></a>
<!-- pdf-source: page=3; block=5; confidence=0.96 -->
**Theorem 1.** For any matrix M with n rows and entries in [0,1], and any sequence of column-player mixed strategies Q_1, …, Q_T played by the environment, the sequence of row-player mixed strategies P_1, …, P_T produced by MW satisfies

∑_{t=1}^{T} M(P_t, Q_t) ≤ min_P [ a_β · ∑_{t=1}^{T} M(P, Q_t) + c_β · RE(P ‖ P_1) ],

where a_β = ln(1/β)/(1−β) and c_β = 1/(1−β).

<a id="pdf-9c61a2f1ecc1-p004-b001"></a>
<!-- pdf-source: page=4; block=1; confidence=0.82 -->
The analysis is amortized, using relative entropy RE as a potential function (method of Kivinen–Warmuth [23]). Lemma 2 bounds the change in this potential over a single round of MW.

<a id="pdf-9c61a2f1ecc1-p004-b002"></a>
<!-- pdf-source: page=4; block=2; confidence=0.96 -->
**Lemma 2.** For any round $t$ where MW is run with parameter $\beta$ and any mixed row strategy $\tilde P$, the one-round change in potential satisfies
$$RE(\tilde P\,\|\,P_{t+1}) - RE(\tilde P\,\|\,P_t) \;\le\; \left(\ln\tfrac{1}{\beta}\right)M(\tilde P, Q_t) \;+\; \ln\!\big(1-(1-\beta)\,M(P_t,Q_t)\big).$$

<a id="pdf-9c61a2f1ecc1-p004-b003"></a>
<!-- pdf-source: page=4; block=3; confidence=0.60 -->
**Proof.** Via a chain of (in)equalities (1)–(5): (1) expand using the definition of relative entropy, giving the difference $=\ln\big(\sum_i P_t(i)\,\beta^{M(i,Q_t)}\big) - M(\tilde P,Q_t)\ln\beta$; (3) substitute the MW update rule $P_{t+1}(i)\propto P_t(i)\,\beta^{M(i,Q_t)}$; (4) simple algebra; (5) apply the definition of $\beta$ with the convexity bound $\beta^x \le 1-(1-\beta)x$ for $x\in[0,1]$, so $\sum_i P_t(i)\beta^{M(i,Q_t)} \le 1-(1-\beta)M(P_t,Q_t)$.

<a id="pdf-9c61a2f1ecc1-p004-b004"></a>
<!-- pdf-source: page=4; block=4; confidence=0.95 -->
**Proof of Theorem 1.** Fix any mixed row strategy $\tilde P$. Simplify the last term of Lemma 2 using $\ln(1-x)\le -x$ for any $x<1$, yielding $RE(\tilde P\|P_{t+1}) - RE(\tilde P\|P_t) \le \left(\ln\tfrac{1}{\beta}\right)M(\tilde P,Q_t) - (1-\beta)M(P_t,Q_t)$. Sum over $t=1,\dots,T$ so the RE terms telescope: $RE(\tilde P\|P_{T+1}) - RE(\tilde P\|P_1) \le \ln(1/\beta)\sum_t M(\tilde P,Q_t) - (1-\beta)\sum_t M(P_t,Q_t)$. Since $RE(\tilde P\|P_{T+1})\ge 0$, rearrange and use that $\tilde P$ was chosen arbitrarily to obtain Theorem 1.

<a id="pdf-9c61a2f1ecc1-p004-b005"></a>
<!-- pdf-source: page=4; block=5; confidence=0.70 -->
On choosing the initial distribution $P_1$: the closer $P_1$ is to a good mixed strategy, the tighter the loss bound; with no prior knowledge, the uniform distribution over rows still yields a bound that holds uniformly for all games with $N$ rows.

<a id="pdf-9c61a2f1ecc1-p005-b001"></a>
<!-- pdf-source: page=5; block=1; confidence=0.95 -->
**Corollary 3.** If MW is run with $P_1$ set to the uniform distribution, its total loss is bounded by
$$\sum_{t=1}^{T} M(P_t,Q_t) \;\le\; a_\beta \min_{P} \sum_{t=1}^{T} M(P,Q_t) + c_\beta \ln n,$$
where $a_\beta$ and $c_\beta$ are as defined in Theorem 1 and $n$ is the number of rows.

<a id="pdf-9c61a2f1ecc1-p005-b002"></a>
<!-- pdf-source: page=5; block=2; confidence=0.72 -->
**Proof.** For uniform $P_1(i)=1/N$, $RE(P\|P_1)=\sum_i P(i)\ln(P(i)\,N)\le \ln N$ for every $P$; substitute this into Theorem 1.

<a id="pdf-9c61a2f1ecc1-p005-b003"></a>
<!-- pdf-source: page=5; block=3; confidence=0.68 -->
As $\beta\to 1$, $a_\beta\to 1$ while $c_\beta\to\infty$; for fixed $\beta$ the term $c_\beta\ln N$ is constant and becomes negligible relative to $T$. Choosing $\beta$ as a function of the number of rounds $T$ lets the average per-trial loss approach that of the best strategy, formalized next.

<a id="pdf-9c61a2f1ecc1-p005-b004"></a>
<!-- pdf-source: page=5; block=4; confidence=0.95 -->
**Corollary 4.** Under the conditions of Theorem 1 with $\beta = \dfrac{1}{1+\sqrt{2\ln n / T}}$, the average per-trial loss satisfies
$$\frac1T\sum_{t} M(P_t,Q_t) \;\le\; \min_P \frac1T\sum_{t} M(P,Q_t) + \Delta_{T,n},\qquad \Delta_{T,n} = \sqrt{\tfrac{2\ln n}{T}} + \tfrac{\ln n}{T} = O\!\left(\sqrt{\tfrac{\ln n}{T}}\right).$$

<a id="pdf-9c61a2f1ecc1-p005-b005"></a>
<!-- pdf-source: page=5; block=5; confidence=0.60 -->
**Proof.** Uses an approximation of the coefficients $a_\beta,c_\beta$ valid for $\beta\in(0,1]$ together with the stated choice of $\beta$; since $\Delta_T\to 0$ as $T\to\infty$, the excess of the learner's average loss over the best fixed mixed strategy can be made arbitrarily small for large $T$.

<a id="pdf-9c61a2f1ecc1-p005-b006"></a>
<!-- pdf-source: page=5; block=6; confidence=0.70 -->
No assumption is made about the environment's strategy: Theorem 1 bounds cumulative loss relative to any fixed mixed strategy, which (next corollary) implies loss is not much larger than the game value; against a non-adversarial environment the algorithm is nearly as good as the best available row strategy.

<a id="pdf-9c61a2f1ecc1-p005-b007"></a>
<!-- pdf-source: page=5; block=7; confidence=0.65 -->
**Corollary 5.** Under the conditions of Corollary 4, $\dfrac1T\sum_{t} M(P_t,Q_t) \le v + \Delta_T$, where $v$ is the value of the game $M$.

<a id="pdf-9c61a2f1ecc1-p005-b008"></a>
<!-- pdf-source: page=5; block=8; confidence=0.68 -->
**Proof.** Let $P^\*$ be a minmax strategy, so $M(P^\*,Q)\le v$ for every column strategy $Q$. By Corollary 4, $\frac1T\sum_t M(P_t,Q_t) \le \frac1T\sum_t M(P^\*,Q_t) + \Delta_T \le v + \Delta_T$.

<a id="pdf-9c61a2f1ecc1-p006-b001"></a>
<!-- pdf-source: page=6; block=1; confidence=0.72 -->
**3.1 Convergence with probability one.** When MW's mixed strategies are used to sample a row each round, the expected per-iteration loss approaches the optimal fixed-strategy value as $T\to\infty$. This section strengthens that to a high-probability statement: the actual per-iteration loss of any repeated-game algorithm is with high probability at most $O(\cdot)$ away from its expected value, requiring only that all matrix entries lie in $[0,1]$.

<a id="pdf-9c61a2f1ecc1-p006-b002"></a>
<!-- pdf-source: page=6; block=2; confidence=0.58 -->
**Lemma 6.** Let both players choose mixed strategies $P_t,Q_t$ on round $t$ as functions of past events, and let $M(i_t,j_t)$ be the realized outcome with row $i_t\sim P_t$ and column $j_t\sim Q_t$. Then for every $\varepsilon>0$,
$$\Pr\!\Big[\tfrac1T\sum_t M(i_t,j_t) - \tfrac1T\sum_t M(P_t,Q_t) \ge \varepsilon\Big] \;\le\; 2\exp\!\big(-\tfrac12 T\varepsilon^2\big),$$
with probability over the random rows $i_1,\dots,i_T$ and columns $j_1,\dots,j_T$.

<a id="pdf-9c61a2f1ecc1-p006-b003"></a>
<!-- pdf-source: page=6; block=3; confidence=0.60 -->
**Proof.** The sequence $X_t = M(i_t,j_t) - M(P_t,Q_t)$ is a martingale difference sequence with $|X_t|\le 1$ (entries in $[0,1]$). Apply Hoeffding's [22] bounded-step martingale inequality ("Azuma's lemma") to the sum: $\Pr[\sum_t X_t \ge a] \le 2\exp(-a^2/(2T))$, then substitute $a=\varepsilon T$.

<a id="pdf-9c61a2f1ecc1-p006-b004"></a>
<!-- pdf-source: page=6; block=4; confidence=0.93 -->
For convergence the parameter must satisfy $\beta\to 1$ as the sequence lengthens. In the method of epochs the row player partitions time into epochs, restarting MW each epoch (resetting all the row distribution to uniform) with a $\beta$ tuned to that epoch's length. Writing $T_k$ for the length and $\beta_k$ for the parameter of epoch $k$, Equation (6) gives one choice that yields convergence with probability one: $T_k = k^2$ and $\beta_k = \dfrac{1}{1+\sqrt{2\ln n / k^2}}$.

<a id="pdf-9c61a2f1ecc1-p006-b005"></a>
<!-- pdf-source: page=6; block=5; confidence=0.62 -->
**Theorem 7.** For an unboundedly repeated game with $P_t$ chosen by the method of epochs (parameters of Eq. (6)) and rows $i_t\sim P_t$, and the environment choosing columns $j_t$ as an arbitrary stochastic function of past plays: for every $\varepsilon>0$, with probability one (over both players' randomization), for all but finitely many $T$,
$$\frac1T\sum_{t=1}^{T} M(i_t,j_t) \;\le\; \min_P \frac1T\sum_{t=1}^{T} M(P,j_t) + \varepsilon.$$

<a id="pdf-9c61a2f1ecc1-p007-b001"></a>
<!-- pdf-source: page=7; block=1; confidence=0.90 -->
**Proof (continued).** For each epoch $k$ the accuracy parameter is set to $\epsilon_k = 2\sqrt{\ln k}/k$, and the iterations composing epoch $k$ are grouped as $S_k$. Epoch $k$ is *good* if its average per-trial loss is within $\epsilon_k$ of its expected value, i.e. $\sum_{t\in S_k} M(i_t,j_t) \le \sum_{t\in S_k} M(P_t,j_t) + T_k\epsilon_k$ **(7)**. From Lemma 6 (defining $Q_t$ to give probability one to $j_t$) the probability that epoch $k$ is *bad* is bounded by $2\exp(-\tfrac12 T_k\epsilon_k^2) = 2/k^2$. Summed over all $k$ this bound is finite, so by the Borel–Cantelli lemma, with probability one all but finitely many epochs are good, and the bad epochs' influence on the average loss can be ignored. Applying Corollary 4 (again with $Q_t$ the point mass on $j_t$) gives $\sum_{t\in S_k} M(P_t,j_t) \le \min_P \sum_{t\in S_k} M(P,j_t) + \sqrt{2T_k\ln n} + \ln n$ **(8)**. Combining (7) and (8): if epoch $k$ is good then for any distribution $\tilde P$, $\sum_{t\in S_k} M(i_t,j_t) \le \sum_{t\in S_k} M(\tilde P,j_t) + k\sqrt{2\ln n} + \ln n + 2k\sqrt{\ln k}$. Summing over the first $m$ epochs (ignoring the negligible bad iterations), the total loss is bounded by $\sum M(\tilde P,j_t) + m^2\sqrt{\ln m}\,[\sqrt{2\ln n}+\ln n+2]$. Since the number of rounds in the first $m$ epochs is $\sum_{k=1}^m k^2 = O(m^3)$, dividing both sides by the round count drives the error term to zero.

<a id="pdf-9c61a2f1ecc1-p007-b002"></a>
<!-- pdf-source: page=7; block=2; confidence=0.97 -->
# 4. Relation to on-line learning

<a id="pdf-9c61a2f1ecc1-p007-b003"></a>
<!-- pdf-source: page=7; block=3; confidence=0.85 -->
On-line decision making is cast as a repeated game between a decision maker and nature: entry M(i,j) is the loss of the prediction algorithm when it plays action i at time j. The algorithm adaptively produces distributions over actions with the goal that its expected cumulative loss not much exceed the loss of the single best fixed distribution chosen with full prior knowledge of the column sequence.

<a id="pdf-9c61a2f1ecc1-p008-b001"></a>
<!-- pdf-source: page=8; block=1; confidence=0.94 -->
The framework is non-statistical: no assumptions relate actions to losses beyond the existence of one fixed mixed strategy with nontrivial expected performance (previously described in the authors' earlier paper [16]). The MW algorithm originates with Littlestone–Warmuth [25] and (in a more sophisticated form) Vovk [30], and was discovered independently by Fudenberg–Levine [17]. In the on-line *prediction* refinement, the algorithm outputs distributions over predictions, nature picks an outcome, and loss is a known loss function on action/outcome pairs; restricting nature to outcome-induced loss columns yields sharper bounds (cf. Dawid [9], Foster [12], Vovk [30]). For the **log-loss** — prediction is a distribution P over a domain X and loss is −log P(x) of the realized element x ∈ X (unbounded as probabilities → 0) — MW with β set to 1/e is a near-optimal universal-compression algorithm for individual sequences [32, 28], and (only in this case) is equivalent to Bayes prediction with the generated row distributions equal to Bayesian posteriors.

<a id="pdf-9c61a2f1ecc1-p008-b002"></a>
<!-- pdf-source: page=8; block=2; confidence=0.82 -->
Cover–Ordentlich [7,6] and Helmbold et al. [21] extended log-loss analysis to universal portfolios; other loss families are treated by Feder–Merhav–Gutman [10], Cesa-Bianchi et al. [5], Vovk [29], Kivinen–Warmuth [23]. A further extension is *bandit* feedback: after the row player picks a row distribution, one row is drawn from it and only that single matrix entry (against the opponent's column) is revealed. Minimizing expected average loss is harder here; Auer et al. [2] show a variant of MW still converges to the best fixed row distribution.

<a id="pdf-9c61a2f1ecc1-p009-b001"></a>
<!-- pdf-source: page=9; block=1; confidence=0.97 -->
# 5. Proof of the minmax theorem

<a id="pdf-9c61a2f1ecc1-p009-b002"></a>
<!-- pdf-source: page=9; block=2; confidence=0.93 -->
**Theorem (von Neumann minmax).** min_P max_Q M(P,Q) = max_Q min_P M(P,Q). (Corollary 5: MW's loss never exceeds the game value by more than Δ_{T,n}.)

**Proof.** It suffices to prove min_P max_Q M(P,Q) ≤ max_Q min_P M(P,Q) **(9)**; the reverse inequality is straightforward and omitted. Run MW against a maximally adversarial environment that on each round t plays Q_t = arg max_Q M(P_t, Q) **(10)**. Let P̄ = (1/T)Σ_t P_t and Q̄ = (1/T)Σ_t Q_t, both probability distributions. Then:

min_P max_Q Pᵀ M Q ≤ max_Q P̄ᵀ M Q = max_Q (1/T)Σ_t P_tᵀ M Q ≤ (1/T)Σ_t max_Q P_tᵀ M Q = (1/T)Σ_t P_tᵀ M Q_t (def. of Q_t) ≤ min_P (1/T)Σ_t Pᵀ M Q_t + Δ_{T,n} (Corollary 4) = min_P Pᵀ M Q̄ + Δ_{T,n} (def. of Q̄) ≤ max_Q min_P Pᵀ M Q + Δ_{T,n}.

Since Δ_{T,n} can be made arbitrarily close to zero, Eq. (9) and hence the minmax theorem follow.

<a id="pdf-9c61a2f1ecc1-p009-b003"></a>
<!-- pdf-source: page=9; block=3; confidence=0.97 -->
# 6. Approximately solving a game

<a id="pdf-9c61a2f1ecc1-p009-b004"></a>
<!-- pdf-source: page=9; block=4; confidence=0.85 -->
Beyond proving the theorem, the derivation shows MW yields an approximate minmax/maxmin strategy ("solving" the game). Three exponential-weights methods are given: (6.1) use the average of the generated row distributions over T iterations, with T set from the target accuracy in advance; (6.2) when an upper bound v on the game value is known ahead of time, a variant of MW generates row distributions whose t-th expected loss approaches v; (6.3) a related adaptive method yields a *sparse* approximate column distribution. Section 7 shows the convergence rate of the latter two methods is asymptotically optimal.

<a id="pdf-9c61a2f1ecc1-p010-b001"></a>
<!-- pdf-source: page=10; block=1; confidence=0.95 -->
## 6.1 Using the average of the row distributions

<a id="pdf-9c61a2f1ecc1-p010-b002"></a>
<!-- pdf-source: page=10; block=2; confidence=0.94 -->
Dropping the first inequality of the chain from the end of Section 5 gives max_Q M(P̄, Q) ≤ v + Δ_{T,n}, so the average row distribution P̄ is an **approximate minmax strategy**: for every column strategy Q, M(P̄, Q) exceeds the game value v by at most Δ_{T,n}, which can be made arbitrarily small, so the approximation is arbitrarily tight. Dropping the last inequality instead gives min_P M(P, Q̄) ≥ v − Δ_{T,n}, so the averaged play Q̄ is an **approximate maxmin strategy**. Moreover a column strategy Q_t satisfying Eq. (10) can always be chosen to be a pure strategy (concentrated on one column), so the approximate maxmin strategy Q̄ is sparse — at most T of its entries are nonzero.

<a id="pdf-9c61a2f1ecc1-p010-b003"></a>
<!-- pdf-source: page=10; block=3; confidence=0.95 -->
## 6.2 Using the final row distribution

<a id="pdf-9c61a2f1ecc1-p010-b004"></a>
<!-- pdf-source: page=10; block=4; confidence=0.94 -->
**Algorithm vMW.** Whereas the *average* of MW's strategies converges to optimal, here the row player — knowing an upper bound u on the value of the game v — uses a variant that generates a sequence of mixed strategies approaching one that achieves loss u each round. On iteration t: if the expected loss M(P_t, Q_t) < u the strategy is left unchanged (it is 'good enough'); if M(P_t, Q_t) ≥ u the algorithm applies MW with the round-dependent parameter β_t = u(1 − M(P_t,Q_t)) / ((1 − u) M(P_t,Q_t)). This is called vMW, 'v' for 'variable'. The following theorem shows the distance between a comparison strategy P̃ (which achieves u) and P_t decreases by an amount depending on the divergence between M(P_t, Q_t) and u.

<a id="pdf-9c61a2f1ecc1-p010-b005"></a>
<!-- pdf-source: page=10; block=5; confidence=0.60 -->
**Theorem 8.** Let P̃ be any row mixed strategy with max_Q M(P̃, Q) ≤ ℓ. Then on any iteration of vMW in which M(P_t, Q_t) ≥ ℓ, the relative entropy between P̃ and P_{t+1} satisfies

RE(P̃ ‖ P_{t+1}) ≤ RE(P̃ ‖ P_t) − RE(ℓ ‖ M(P_t, Q_t)),

where the right-hand RE(ℓ ‖ ·) is the binary relative entropy.

<a id="pdf-9c61a2f1ecc1-p010-b006"></a>
<!-- pdf-source: page=10; block=6; confidence=0.94 -->
**Proof.** When u ≤ M(P_t, Q_t) one has β_t ≤ 1. Combining this with the definition of P̃ and with Lemma 2 gives Eq. (11):

RE(P̃ ‖ P_{t+1}) − RE(P̃ ‖ P_t) ≤ M(P̃, Q_t) ln(1/β_t) + ln(1 − (1 − β_t) M(P_t, Q_t)) ≤ u · ln(1/β_t) + ln(1 − (1 − β_t) M(P_t, Q_t))   (11)

[continued on the next page]

<a id="pdf-9c61a2f1ecc1-p011-b001"></a>
<!-- pdf-source: page=11; block=1; confidence=0.50 -->
**Proof (continued).** β_t is chosen to minimize the right-hand side of (11); substituting the chosen value yields the theorem's bound. Applying the main inequality repeatedly over rounds t = 1..T gives Eq. (12):

RE(P̃ ‖ P_{T+1}) ≤ RE(P̃ ‖ P_1) − Σ_{t=1}^{T} RE(ℓ ‖ M(P_t, Q_t))   (12)

Since relative entropy is nonnegative and this holds for all T, Σ_t RE(ℓ ‖ M(P_t, Q_t)) ≤ RE(P̃ ‖ P_1). Assuming RE(P̃ ‖ P_1) is finite (e.g. P_1 uniform), this implies M(P_t, Q_t) can exceed ℓ + γ at most finitely often for any γ > 0.

<a id="pdf-9c61a2f1ecc1-p011-b002"></a>
<!-- pdf-source: page=11; block=2; confidence=0.95 -->
**Corollary 9.** Suppose vMW is used to play a game M whose value is known to be at most u, with P_1 the uniform distribution. Then for any sequence of column strategies Q_1, Q_2, …, the number of rounds on which the loss M(P_t, Q_t) ≥ u + ε is at most

ln n / RE(u ‖ u + ε),

where n is the number of rows.

<a id="pdf-9c61a2f1ecc1-p011-b003"></a>
<!-- pdf-source: page=11; block=3; confidence=0.45 -->
**Proof.** Rounds with M(P_t, Q_t) < ℓ are effectively ignored by vMW, so assume without loss of generality M(P_t, Q_t) ≥ ℓ on every round. Let S be the set of rounds with M(P_t, Q_t) ≥ ℓ + γ, and let P̃ be a minmax strategy. By Eq. (12), Σ_t RE(ℓ ‖ M(P_t, Q_t)) ≤ RE(P̃ ‖ P_1) ≤ ln N. Each round in S contributes at least RE(ℓ ‖ ℓ + γ), so |S| ≤ ln(N) / RE(ℓ ‖ ℓ + γ). A remark states that Section 7 shows this dependence on ℓ, N, and γ cannot be improved by any constant factor.

<a id="pdf-9c61a2f1ecc1-p011-b004"></a>
<!-- pdf-source: page=11; block=4; confidence=0.95 -->
## 6.3 Convergence of a column distribution

<a id="pdf-9c61a2f1ecc1-p011-b005"></a>
<!-- pdf-source: page=11; block=5; confidence=0.50 -->
When β is fixed (Section 6.1), the average Q̄ of the Q_t's is an approximate solution of the game — there are no rows i for which M(e_i, Q̄) < v. For the vMW algorithm, in which β varies, a more refined bound of this kind can be derived for a *weighted* mixture of the Q_t's.

<a id="pdf-9c61a2f1ecc1-p012-b001"></a>
<!-- pdf-source: page=12; block=1; confidence=0.95 -->
**Theorem 10.** Assume that on every iteration of vMW, M(P_t, Q_t) ≥ u. Let

Q̂ = ( Σ_{t=1}^{T} Q_t · ln(1/β_t) ) / ( Σ_{t=1}^{T} ln(1/β_t) ).

Then

Σ_{ i : M(i, Q̂) ≤ u } P_1(i) ≤ exp( − Σ_{t=1}^{T} RE(u ‖ M(P_t, Q_t)) ).

<a id="pdf-9c61a2f1ecc1-p012-b002"></a>
<!-- pdf-source: page=12; block=2; confidence=0.40 -->
**Proof.** For any comparison strategy P̃, summing Eq. (11) over t = 1..T gives an upper bound on RE(P̃ ‖ P_{T+1}) of the form RE(P̃ ‖ P_1) − Σ_t RE(ℓ ‖ M(P_t, Q_t)) minus a term involving the weighted average M(P̃, Q̂). In particular, for a row i with M(e_i, Q̂) ≤ ℓ, setting P̃ to the associated pure strategy e_i and using nonnegativity of RE gives P_1(i) ≤ exp( − Σ_t RE(ℓ ‖ M(P_t, Q_t)) ). Summing over all such rows i and using that P_1 is a distribution yields the stated bound.

<a id="pdf-9c61a2f1ecc1-p012-b003"></a>
<!-- pdf-source: page=12; block=3; confidence=0.60 -->
Consequently, if M(P_t, Q_t) stays bounded away from ℓ, the fraction of rows i (measured by P_1) for which M(e_i, Q̂) ≤ ℓ drops to zero exponentially fast — e.g. when Eq. (10) holds and M(e_i, Q̂) ≥ v + γ for some γ > 0, where v is the value of M. Thus a single run of the exponential-weights algorithm yields approximate solutions for both players: the row-player solution is the multiplicative weights, and the column-player solution is the distribution over the observed columns (Theorem 10). Given a game matrix M one may solve M or M^T, naturally choosing the orientation with fewer rows; a related paper [16] connects solving M (the on-line prediction problem of Section 4) and M^T (a method of learning called 'boosting') via multiplicative weights.

<a id="pdf-9c61a2f1ecc1-p013-b001"></a>
<!-- pdf-source: page=13; block=1; confidence=0.95 -->
## 6.4 Application to linear programming

<a id="pdf-9c61a2f1ecc1-p013-b002"></a>
<!-- pdf-source: page=13; block=2; confidence=0.72 -->
Any linear program reduces to solving a game (Owen [26, Thm. III.2.6]), so the approximate game-solving algorithms apply to approximate LP. Related approaches: Young [31], Grigoriadis–Khachiyan [18, 19], Plotkin–Shmoys–Tardos [27]. The method is best suited to the oracle setting, where an oracle selects a column each round; it then applies even when the number of columns is very large or infinite (infeasible for traditional LP methods). Cf. [16] for machine-learning examples.

<a id="pdf-9c61a2f1ecc1-p013-b003"></a>
<!-- pdf-source: page=13; block=3; confidence=0.95 -->
## 7 Optimality of the convergence rate

<a id="pdf-9c61a2f1ecc1-p013-b004"></a>
<!-- pdf-source: page=13; block=4; confidence=0.93 -->
Corollary 9 showed that algorithm vMW started from the uniform distribution over rows bounds the number of rounds on which the loss $M(P_t,Q_t)$ exceeds $u+\epsilon$ by $\dfrac{\ln n}{\mathrm{RE}(u\,\|\,u+\epsilon)}$, where $u$ is a known upper bound on the value of the game $M$. This section shows the dependence of the rate of convergence on $n$, $u$ and $\epsilon$ is optimal: no adaptive game-playing algorithm can beat this bound even by a constant factor. This is formalized as Theorem 11. A related lower bound for approximately solving linear programs is due to Klein and Young [24].

<a id="pdf-9c61a2f1ecc1-p013-b005"></a>
<!-- pdf-source: page=13; block=5; confidence=0.94 -->
**Theorem 11.** Let $0 < u < u+\epsilon < 1$ and let $n$ be a sufficiently large integer. Then for any adaptive game-playing algorithm $A$ there exist a game matrix $M$ with $n$ rows and a sequence of column strategies $Q_1,\dots,Q_T$ such that:

1. the value of game $M$ is at most $u$; and
2. the loss $M(P_t, Q_t)$ suffered by $A$ on each round $t = 1,\dots,T$ is at least $u + \epsilon$,

where $T = \left\lfloor \dfrac{\ln n - 5\ln\ln n}{\mathrm{RE}(u \,\|\, u+\epsilon)} \right\rfloor \ge \dfrac{(1-o(1))\ln n}{\mathrm{RE}(u \,\|\, u+\epsilon)}.$

<a id="pdf-9c61a2f1ecc1-p013-b006"></a>
<!-- pdf-source: page=13; block=6; confidence=0.68 -->
**Proof.** Probabilistic method: choose $M$ at random from a suitable distribution and show properties 1 and 2 hold simultaneously with strictly positive probability, so at least one qualifying $M$ exists.

Set $p$ to the target parameter. The random matrix $M$ has $N$ rows and $K$ columns; each entry $M(i,j)$ is chosen independently to be $1$ with probability $p$ and $0$ with probability $1-p$. On round $t$ the row player (algorithm $A$) chooses a row distribution $P_t$; for the construction the column player responds with column $t$, i.e. the strategy $Q_t$ is concentrated on column $t$.

<a id="pdf-9c61a2f1ecc1-p014-b001"></a>
<!-- pdf-source: page=14; block=1; confidence=0.62 -->
**Proof (cont.).** Need properties 1 and 2 to hold with positive probability for large $N$. For property 2: on round $t$, given $P_t$ and column $t$, require the loss $M(P_t,t) \ge p$. Since $M$ is random and the row player controls $P_t$, a lower bound on $\Pr[M(P_t,t)\ge p]$ is needed that is independent of $P_t$. This is supplied by Lemma 12.

<a id="pdf-9c61a2f1ecc1-p014-b002"></a>
<!-- pdf-source: page=14; block=2; confidence=0.60 -->
**Lemma 12.** For every $p \in (0,1)$ there exists $\alpha > 0$ with the following property. Let $N$ be any positive integer and let $a_1,\dots,a_N \ge 0$ satisfy $\sum_i a_i = 1$. Let $X_1,\dots,X_N$ be independent Bernoulli variables with $\Pr[X_i=1]=p$ and $\Pr[X_i=0]=1-p$, and set $X=\sum_i a_i X_i$. Then $\Pr[X \ge p] \ge \alpha$.

<a id="pdf-9c61a2f1ecc1-p014-b003"></a>
<!-- pdf-source: page=14; block=3; confidence=0.90 -->
**Proof.** Deferred to the appendix.

<a id="pdf-9c61a2f1ecc1-p014-b004"></a>
<!-- pdf-source: page=14; block=4; confidence=0.60 -->
**Proof (cont.).** Take $a_i = P_t(i)$ and $X_i = M(i,t)$. Lemma 12 gives $\Pr[M(P_t,t) \ge p] \ge \alpha$, where $\alpha>0$ depends on $p$ but not on $N$ or $P_t$. Hence $\Pr[\forall t:\; M(P_t,t)\ge p] \ge \alpha^{T}$; i.e. property 2 holds with probability at least $\alpha^{T}$.

<a id="pdf-9c61a2f1ecc1-p014-b005"></a>
<!-- pdf-source: page=14; block=5; confidence=0.93 -->
**Proof (cont.).** Goal: property 1 fails with probability strictly smaller than $B_r^{T}$, so both properties hold together with positive probability. Define the weight of row $i$ as the fraction of 1's, $W(i) = \tfrac{1}{T}\sum_{j=1}^{T} M(i,j)$. A row is *light* if $W(i) \le u - 1/T$. Let $P'$ be the row distribution uniform over the light rows and zero on the heavy rows. It suffices to show that, with high probability, $\max_j M(P', j)$ is at most $u$, giving an upper bound $u$ on the value of $M$.

<a id="pdf-9c61a2f1ecc1-p014-b006"></a>
<!-- pdf-source: page=14; block=6; confidence=0.93 -->
**Proof (cont.).** Let $\lambda$ be the probability that a given row is light (the same for all rows) and $n'$ the number of light rows, so $\mathbb{E}[n']=\lambda n$. By the Angluin–Valiant [1] form of the Chernoff bound,
$$\Pr[n' < \lambda n/2] \le \exp(-\lambda n/8). \tag{13}$$
Conditional on row $i$ being light, $\Pr[M(i,j)=1] \le u - 1/T$; for distinct light rows $i_1,i_2$ the entries $M(i_1,j)$ and $M(i_2,j)$ remain independent. Applying Hoeffding's inequality [22] to column $j$ over the $n'$ light rows gives, for all $j$, $\Pr[M(P',j) > u \mid n'] \le e^{-2n'/T^2}$, and hence, by a union bound, $\Pr[\max_j M(P',j) > u \mid n'] \le T\,e^{-2n'/T^2}$.

<a id="pdf-9c61a2f1ecc1-p015-b001"></a>
<!-- pdf-source: page=15; block=1; confidence=0.93 -->
**Proof (cont.).** Combining the per-column bound with Eq. (13) gives $\Pr[\max_j M(P',j) > u] \le e^{-\lambda n/2} + T e^{-\lambda n/T^2} \le (T+1)e^{-\lambda n/T^2}$ for $T \ge 3$. Therefore the probability that either property 1 or property 2 fails to hold is at most $(T+1)e^{-\lambda n/T^2} + 1 - B_r^{T}$. If this quantity is strictly less than $1$, some matrix $M$ satisfies both properties; this holds if and only if
$$\lambda > \frac{T^2}{n}\big(T\ln(1/B_r) + \ln(T+1)\big). \tag{14}$$
It remains to prove Eq. (14) by lower bounding $\lambda$.

<a id="pdf-9c61a2f1ecc1-p015-b002"></a>
<!-- pdf-source: page=15; block=2; confidence=0.90 -->
**Proof (cont.).** We have $\lambda = \Pr[W(i)\cdot T \le Tu-1] \ge \Pr[W(i)\cdot T = \lfloor Tu-1\rfloor] \ge \tfrac{1}{T+1}\exp\!\big(-T\cdot\mathrm{RE}(\lfloor Tu-1\rfloor/T \,\|\, u+\epsilon)\big) \ge \tfrac{1}{T+1}\exp\!\big(-T\cdot\mathrm{RE}(u-2/T \,\|\, u+\epsilon)\big)$, the last inequality via Cover–Thomas [8, Thm. 12.1.4]. By straightforward algebra $T\cdot\mathrm{RE}(u-2/T \,\|\, u+\epsilon) \le T\cdot\mathrm{RE}(u \,\|\, u+\epsilon) + C'$ for $T$ sufficiently large, with $C' = 2\ln\!\big(\tfrac{1-u/2}{1-u-\epsilon}\cdot\tfrac{u+\epsilon}{u/2}\big)$. Hence $\lambda \ge \tfrac{e^{-C'}}{T+1}\exp(-T\cdot\mathrm{RE}(u\,\|\,u+\epsilon))$, so Eq. (14) holds if $T\cdot\mathrm{RE}(u\,\|\,u+\epsilon) < \ln n - C' - \ln\!\big(T^2(T+1)(T\ln(1/B_r)+\ln(T+1))\big)$. By the chosen $T$, the left-hand side is at most $\ln n - 5\ln\ln n$ and the right-hand side is $\ln n - (4+o(1))\ln\ln n$; hence the inequality, and therefore the theorem, holds for $n$ sufficiently large. $\qquad\blacksquare$

<a id="pdf-9c61a2f1ecc1-p016-b001"></a>
<!-- pdf-source: page=16; block=1; confidence=0.92 -->
**Acknowledgments.** Thanks to N. Young, D. Foster, and R. Vohra for discussions and literature pointers, and to C. Mallows and J. Spencer for help proving Lemma 12.

<a id="pdf-9c61a2f1ecc1-p016-b002"></a>
<!-- pdf-source: page=16; block=2; confidence=0.90 -->
**References (bibliography, entries [1]–[16]).** [1] Angluin & Valiant, *Fast probabilistic algorithms for Hamiltonian circuits and matchings*, JCSS 18(2), 1979. [2] Auer, Cesa-Bianchi, Freund, Schapire, *Gambling in a rigged casino: the adversarial multi-armed bandit problem*, FOCS 1995. [3] Blackwell, *An analog of the minimax theorem for vector payoffs*, Pacific J. Math. 6(1), 1956. [4] Blackwell & Girshick, *Theory of games and statistical decisions*, Dover 1954. [5] Cesa-Bianchi, Freund, Haussler, Helmbold, Schapire, Warmuth, *How to use expert advice*, JACM 44(3), 1997. [6] Cover & Ordentlich, *Universal portfolios with side information*, IEEE Trans. IT, 1996. [7] Cover, *Universal portfolios*, Math. Finance 1(1), 1991. [8] Cover & Thomas, *Elements of Information Theory*, Wiley 1991. [9] Dawid, *Statistical theory: the prequential approach*, JRSS A 147, 1984. [10] Feder, Merhav, Gutman, *Universal prediction of individual sequences*, IEEE Trans. IT 38, 1992. [11] Ferguson, *Mathematical Statistics: A Decision Theoretic Approach*, Academic Press 1967. [12] Foster, *Prediction in the worst case*, Ann. Statist. 19(2), 1991. [13] Foster & Vohra, *Regret in the on-line decision problem*, unpublished 1997. [14] Foster & Vohra, *A randomization rule for selecting forecasts*, Oper. Res. 41(4), 1993. [15] Foster & Vohra, *Asymptotic calibration*, Biometrika 85(2), 1998. [16] Freund & Schapire, *Game theory, on-line prediction and boosting*, COLT 1996.

<a id="pdf-9c61a2f1ecc1-p017-b001"></a>
<!-- pdf-source: page=17; block=1; confidence=0.90 -->
**References (bibliography, entries [17]–[32]).** [17] Fudenberg & Levine, *Consistency and cautious fictitious play*, J. Econ. Dyn. Control 19, 1995. [18] Grigoriadis & Khachiyan, *Approximate solution of matrix games in parallel*, DIMACS TR 91-73, 1991. [19] Grigoriadis & Khachiyan, *A sublinear-time randomized approximation algorithm for matrix games*, Oper. Res. Lett. 18(2), 1995. [20] Hannan, *Approximation to Bayes risk in repeated play*, in Contributions to the Theory of Games III, 1957. [21] Helmbold, Schapire, Singer, Warmuth, *On-line portfolio selection using multiplicative updates*, Math. Finance 8(4), 1998. [22] Hoeffding, *Probability inequalities for sums of bounded random variables*, JASA 58(301), 1963. [23] Kivinen & Warmuth, *Additive versus exponentiated gradient updates for linear prediction*, Inform. & Comput. 132(1), 1997. [24] Klein & Young, *On the number of iterations for Dantzig-Wolfe optimization and packing-covering approximation algorithms*, IPCO 1999. [25] Littlestone & Warmuth, *The weighted majority algorithm*, Inform. & Comput. 108, 1994. [26] Owen, *Game Theory*, Academic Press, 2nd ed., 1982. [27] Plotkin, Shmoys, Tardos, *Fast approximation algorithms for fractional packing and covering problems*, Math. Oper. Res. 20(2), 1995. [28] Shtar'kov, *Universal sequential coding of single messages*, Probl. Inf. Transm. 23, 1987. [29] Vovk, *A game of prediction with expert advice*, JCSS 56(2), 1998. [30] Vovk, *Aggregating strategies*, COLT 1990. [31] Young, *Randomized rounding without solving the linear program*, SODA 1995. [32] Ziv, *Coding theorems for individual sequences*, IEEE Trans. IT 24(4), 1978.

<a id="pdf-9c61a2f1ecc1-p018-b001"></a>
<!-- pdf-source: page=18; block=1; confidence=0.95 -->
**Appendix A. Proof of Lemma 12.**

<a id="pdf-9c61a2f1ecc1-p018-b002"></a>
<!-- pdf-source: page=18; block=2; confidence=0.90 -->
**Proof (setup).** Define $Y = \dfrac{\sum_i \alpha_i X_i - r}{\sqrt{\sum_i \alpha_i^2}}$ and set $s = r(1-r)$; then $\mathbb{E}Y = 0$ and $\mathrm{Var}\,Y = s$. The goal is a lower bound on $\Pr[Y \ge 0]$. By Hoeffding's inequality [22], for all $\epsilon > 0$, $\Pr[Y \ge \epsilon] \le e^{-2\epsilon^2}$ **(15)** and $\Pr[Y \le -\epsilon] \le e^{-2\epsilon^2}$. For $x\in\mathbb{R}$ let $D(x) = \Pr[Y = x]$; $\sum_x$ denotes summation over the finite set of $x$ with $D(x)>0$, and restricted sums (e.g. $\sum_{x>0}$) analogously. Fix any $d > 0$ and define $G = \sum_{0<x<d} D(x)$, $R = -\sum_{-d<x<0} x D(x)$, $F_1 = \sum_{x\ge d} x D(x)$, $F_2 = \sum_{x\le -d} x^2 D(x)$, and $F_3 = \sum_{x\ge d} x^2 D(x)$. The lemma is proved by lower-bounding $G \le \Pr[Y \ge 0]$. Expanding $0 = \mathbb{E}Y = \sum_x x D(x)$ over these ranges gives $0 \le -R + dG + F_1$, i.e. $R \le dG + F_1$ **(16)**. Likewise $s = \mathrm{Var}\,Y = \sum_x x^2 D(x) \le F_2 + dR + d^2 G + F_3$.

<a id="pdf-9c61a2f1ecc1-p019-b001"></a>
<!-- pdf-source: page=19; block=1; confidence=0.93 -->
**Proof (continued).** Combining the current bound with Eq. (16) yields **Eq. (17)**: $s \le 2d^2 G + d F_1 + F_2 + F_3$.

<a id="pdf-9c61a2f1ecc1-p019-b002"></a>
<!-- pdf-source: page=19; block=2; confidence=0.55 -->
**Proof step.** States the plan: upper-bound the three quantities Λ₁, Λ₂, Λ₃; these bounds then immediately give a lower bound on γ via **Eq. (17)**.

<a id="pdf-9c61a2f1ecc1-p019-b003"></a>
<!-- pdf-source: page=19; block=3; confidence=0.93 -->
**Proof step.** Bounds $F_1$, producing **Eq. (18)**: $d F_1 = d\sum_{x\ge d} x D(x) \le \sum_{x\ge d} x^2 D(x) = F_3$.

<a id="pdf-9c61a2f1ecc1-p019-b004"></a>
<!-- pdf-source: page=19; block=4; confidence=0.90 -->
**Proof step.** To bound $F_3$, introduce a sequence $d = y_0 < y_1 < \cdots < y_m$ such that every $x \ge d$ with $D(x) > 0$ equals some $y_i$. With $S(y) = \sum_{x\ge y} D(x) \le e^{-2y^2}$ for $y>0$ (from **Eq. (15)**), computing $F_3 = \sum_{x\ge d} x^2 D(x)$ through a chain of equalities/inequalities and bounding the resulting summation by $\tfrac12 e^{-2d^2}$ yields $F_3 \le (d^2 + \tfrac12) e^{-2d^2}$. A bound on $F_2$ follows by symmetry.

<a id="pdf-9c61a2f1ecc1-p019-b005"></a>
<!-- pdf-source: page=19; block=5; confidence=0.90 -->
**Proof step.** Combining with **Eqs. (17) and (18)** gives $s \le 2d^2 G + 3(d^2+\tfrac12)e^{-2d^2}$, hence $\Pr[Y \ge 0] \ge G \ge \dfrac{s - 3(d^2+\tfrac12)e^{-2d^2}}{2d^2}$. Since this holds for all $d$, $\Pr[Y \ge 0] \ge B_r$ where $B_r = \sup_{d>0} \dfrac{s - 3(d^2+\tfrac12)e^{-2d^2}}{2d^2}$ and $s = r(1-r)$. This is strictly positive because the numerator can be made positive by choosing $d$ sufficiently large — for instance, it is positive when $d = \sqrt{1/s}$.
