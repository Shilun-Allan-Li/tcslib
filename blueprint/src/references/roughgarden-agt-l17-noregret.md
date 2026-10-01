<!-- generated-by: proofmatch Claude repair -->
<!-- source-pdf-sha256: eda737ce3103cdfc7845f80b3d2b80c68ff0241728cebdf1f85f663516194d1d -->

<a id="pdf-eda737ce3103-p001-b001"></a>
<!-- pdf-source: page=1; block=1; confidence=0.98 -->
# Lecture #17: No-Regret Dynamics (CS364A: Algorithmic Game Theory, Tim Roughgarden)

<a id="pdf-eda737ce3103-p001-b002"></a>
<!-- pdf-source: page=1; block=2; confidence=0.95 -->
Continues the study of whether/how fast strategic players reach equilibrium via learning processes. Unlike best-response dynamics (suited to potential games), no-regret dynamics converge rapidly in arbitrary games to an approximate equilibrium — specifically a coarse correlated equilibrium, not generally a Nash equilibrium.

<a id="pdf-eda737ce3103-p001-b003"></a>
<!-- pdf-source: page=1; block=3; confidence=0.97 -->
# 1 External Regret
## 1.1 The Model

<a id="pdf-eda737ce3103-p001-b004"></a>
<!-- pdf-source: page=1; block=4; confidence=0.90 -->
**Model (regret minimization, single decision-maker vs. adversary).** Fix a set $A$ of $n \ge 2$ actions. For each time $t = 1,2,\dots,T$:
- The decision-maker picks a mixed strategy $p^t$ (a probability distribution over $A$).
- An adversary picks a cost vector $c^t : A \to [0,1]$. (Key assumption: costs are bounded; extensions to negative costs/payoffs and to $[0,c_{\max}]$ are in the exercises.)

<a id="pdf-eda737ce3103-p002-b001"></a>
<!-- pdf-source: page=2; block=1; confidence=0.90 -->
**Model (continued).** An action $a^t$ is drawn from $p^t$; the decision-maker incurs cost $c^t(a^t)$ but learns the entire cost vector $c^t$ (full-information feedback), not just the realized cost. (The bandit variant, where only the realized cost is observed, gives the same guarantees with worse bounds.) Interpretation: $A$ = investment strategies or driving routes; in multi-player games (Section 3), $A$ is one player's strategy set and $c^t$ is induced by the other players' strategies.

<a id="pdf-eda737ce3103-p002-b002"></a>
<!-- pdf-source: page=2; block=2; confidence=0.97 -->
## 1.2 Lower Bounds

<a id="pdf-eda737ce3103-p002-b003"></a>
<!-- pdf-source: page=2; block=3; confidence=0.90 -->
The adversary chooses $c^t$ after the decision-maker commits to $p^t$; three examples delimit what guarantees are achievable under this asymmetry.

<a id="pdf-eda737ce3103-p002-b004"></a>
<!-- pdf-source: page=2; block=4; confidence=0.90 -->
**Example 1.1 (Impossibility w.r.t. the best action sequence).** No algorithm can compete with the best action sequence in hindsight $\sum_{t=1}^T \min_{a\in A} c^t(a)$. With $|A|=2$, for any online algorithm the adversary sets $c^t=(1,0)$ if the algorithm plays the first action with probability $\ge \tfrac12$, else $c^t=(0,1)$; this forces expected algorithm cost $\ge T/2$ while the best action sequence in hindsight has cost $0$. This motivates using the best *fixed* action $\min_{a\in A}\sum_{t=1}^T c^t(a)$ as benchmark instead.

<a id="pdf-eda737ce3103-p002-b005"></a>
<!-- pdf-source: page=2; block=5; confidence=0.90 -->
**Definition 1.2** The *(time-averaged) regret* of the action sequence $a^1,\dots,a^T$ with respect to the action $a$ is
$$\frac{1}{T}\left[\sum_{t=1}^{T} c^t(a^t) \;-\; \sum_{i=1}^{T} c^t(a)\right]. \tag{1}$$
In this lecture, "regret" will always refer to Definition 1.2. Next lecture we discuss another notion of regret.

<a id="pdf-eda737ce3103-p002-b006"></a>
<!-- pdf-source: page=2; block=6; confidence=0.85 -->
**Definition 1.3 (No-Regret Algorithm).** Let $\mathcal{A}$ be an online decision-making algorithm. [Definition continues on page 3.]

<a id="pdf-eda737ce3103-p003-b001"></a>
<!-- pdf-source: page=3; block=1; confidence=0.95 -->
**Definition 1.3 (continued).** (a) An *adversary for* $\mathcal{A}$ is a function that takes as input the day $t$, the mixed strategies $p^1,\dots,p^t$ produced by $\mathcal{A}$ on the first $t$ days, and the realized actions $a^1,\dots,a^{t-1}$ of the first $t-1$ days, and produces as output a cost vector $c^t : [0,1] \to A$. (b) An online decision-making algorithm has *no (external) regret* if for every adversary for it, the expected regret (1) with respect to every action $a\in A$ is $o(1)$ as $T\to\infty$.

<a id="pdf-eda737ce3103-p003-b002"></a>
<!-- pdf-source: page=3; block=2; confidence=0.93 -->
**Remark 1.4 (Combining Expert Advice).** Designing a no-regret algorithm is also called "combining expert advice": treating each action as an expert, a no-regret algorithm performs asymptotically as well as the best expert.

<a id="pdf-eda737ce3103-p003-b003"></a>
<!-- pdf-source: page=3; block=3; confidence=0.94 -->
**Remark 1.5 (Adaptive vs. Oblivious Adversaries).** The adversary of Definition 1.3 is *adaptive*. An *oblivious* adversary is the special case where $c^t$ depends only on $t$ (and on $\mathcal{A}$).

<a id="pdf-eda737ce3103-p003-b004"></a>
<!-- pdf-source: page=3; block=4; confidence=0.92 -->
The no-regret guarantee is adopted as the design goal because it is achievable by simple learning algorithms (Section 2), non-trivial to attain, and translates directly into coarse correlated equilibrium conditions for multi-player games (Section 3).

<a id="pdf-eda737ce3103-p003-b005"></a>
<!-- pdf-source: page=3; block=5; confidence=0.93 -->
**Remark 1.6.** The number of actions $n$ is held fixed as $T\to\infty$; time-averaged regret may depend on $n$ but tends to $0$ as $T$ grows.

<a id="pdf-eda737ce3103-p003-b006"></a>
<!-- pdf-source: page=3; block=6; confidence=0.90 -->
**Example 1.7 (Randomization Is Necessary).** No deterministic no-regret algorithm exists. For $n\ge 2$ actions and any deterministic algorithm committing to a single action $a^t$ each step, the adversary sets $c^t(a^t)=1$ and cost $0$ for all other actions. Then the algorithm's cost is $T$ while the best action in hindsight costs at most $T/n$, giving constant regret as $T\to\infty$ with respect to some action.

<a id="pdf-eda737ce3103-p003-b007"></a>
<!-- pdf-source: page=3; block=7; confidence=0.90 -->
**Example 1.8 ($\Omega(\sqrt{(\ln n)/T})$ regret lower bound).** Even with $n=2$ actions, no randomized algorithm has expected regret vanishing faster than $\Theta(1/\sqrt{T})$; with $n$ actions, expected regret cannot vanish faster than $\Theta(\sqrt{(\ln n)/T})$.

<a id="pdf-eda737ce3103-p004-b001"></a>
<!-- pdf-source: page=4; block=1; confidence=0.95 -->
An adversary picking each day uniformly between cost vectors $(1,0)$ and $(0,1)$ forces cumulative expected cost exactly $T/2$ for any algorithm, yet with constant probability one fixed action has cumulative cost $T/2-\Theta(\sqrt{T})$ (the std. deviation of $T$ fair coin flips is $\Theta(\sqrt{T})$). Hence there is a distribution over $2^T$ oblivious adversaries under which every algorithm has expected regret $\Omega(1/\sqrt{T})$, and therefore for every algorithm some oblivious adversary yields expected regret $\Omega(1/\sqrt{T})$.

<a id="pdf-eda737ce3103-p004-b002"></a>
<!-- pdf-source: page=4; block=2; confidence=1.00 -->
## 2 The Multiplicative Weights Algorithm

<a id="pdf-eda737ce3103-p004-b003"></a>
<!-- pdf-source: page=4; block=3; confidence=1.00 -->
### 2.1 No-Regret Algorithms Exist

<a id="pdf-eda737ce3103-p004-b004"></a>
<!-- pdf-source: page=4; block=4; confidence=0.90 -->
No-regret algorithms exist; simple, natural ones achieve optimal regret matching the lower bound of Example 1.8.

<a id="pdf-eda737ce3103-p004-b005"></a>
<!-- pdf-source: page=4; block=5; confidence=0.97 -->
**Theorem 2.1.** There exist simple no-regret algorithms with expected regret $O(\sqrt{(\ln n)/T})$ with respect to every fixed action.

<a id="pdf-eda737ce3103-p004-b006"></a>
<!-- pdf-source: page=4; block=6; confidence=0.97 -->
**Corollary 2.2.** There exists an online decision-making algorithm that, for every $\epsilon>0$, has expected regret at most $\epsilon$ with respect to every fixed action after $O((\ln n)/\epsilon^2)$ iterations.

<a id="pdf-eda737ce3103-p004-b007"></a>
<!-- pdf-source: page=4; block=7; confidence=1.00 -->
### 2.2 The Algorithm

<a id="pdf-eda737ce3103-p004-b008"></a>
<!-- pdf-source: page=4; block=8; confidence=0.93 -->
The multiplicative weights (MW) algorithm — also called Randomized Weighted Majority or Hedge — follows two principles: (1) the probability of choosing an action increases with its past performance (decreases with its cumulative cost); (2) for optimal regret, bad actions must be punished aggressively, decreasing their play probability at an exponential rate.

<a id="pdf-eda737ce3103-p005-b001"></a>
<!-- pdf-source: page=5; block=1; confidence=0.96 -->
**MW Algorithm.** Maintain a weight $w_t(a)$ ("credibility") per action.
1. Initialize $w_1(a)=1$ for every $a\in A$.
2. For $t=1,2,\dots,T$:
   - (a) Play an action according to $p_t := w_t/\Gamma_t$, where $\Gamma_t=\sum_{a\in A} w_t(a)$.
   - (b) Given cost vector $c_t$, update $w_{t+1}(a)=w_t(a)\cdot(1-\epsilon)^{c_t(a)}$ for every $a\in A$.

Weights only decrease. (Alternative update $w_{t+1}(a)=w_t(a)(1-\epsilon c_t(a))$ also works.)

<a id="pdf-eda737ce3103-p005-b002"></a>
<!-- pdf-source: page=5; block=2; confidence=0.92 -->
With 0/1 costs each weight stays fixed (cost 0) or is multiplied by $(1-\epsilon)$ (cost 1). Here $\epsilon\in(0,\tfrac12)$: small $\epsilon$ makes $p_t$ near uniform (exploration); as $\epsilon\to1$, $p_t$ concentrates on the lowest-cumulative-cost action (exploitation).

<a id="pdf-eda737ce3103-p005-b003"></a>
<!-- pdf-source: page=5; block=3; confidence=1.00 -->
### 2.3 The Analysis

<a id="pdf-eda737ce3103-p005-b004"></a>
<!-- pdf-source: page=5; block=4; confidence=0.90 -->
It suffices to consider oblivious adversaries fixing $c_1,\dots,c_T$ in advance, since MW's distribution $p_t$ is a deterministic function of $c_1,\dots,c_{t-1}$ and independent of realized actions; the worst adaptive adversary reduces to an oblivious one by backward induction. Fix any sequence $c_1,\dots,c_T$; $\Gamma_t=\sum_{a} w_t(a)$ is nonincreasing. The proof relates MW's expected cost and the best fixed action's cost to $\Gamma_T$.

<a id="pdf-eda737ce3103-p006-b001"></a>
<!-- pdf-source: page=6; block=1; confidence=0.96 -->
**Proof (step 1).** Let $OPT:=\sum_{t=1}^T c_t(a^*)$ be the best fixed action $a^*$'s cumulative cost. Then
$$\Gamma_T \ge w_T(a^*) = w_1(a^*)\prod_{t=1}^T (1-\epsilon)^{c_t(a^*)} = (1-\epsilon)^{OPT},$$
using $w_1(a^*)=1$. This links $\Gamma_T$ to $OPT$.

<a id="pdf-eda737ce3103-p006-b002"></a>
<!-- pdf-source: page=6; block=2; confidence=0.95 -->
**Proof (step 2).** MW's expected cost at time $t$ is
$$\nu_t=\sum_{a\in A} p_t(a)c_t(a)=\sum_{a\in A}\frac{w_t(a)}{\Gamma_t}c_t(a). \quad(2)$$
Then
$$\Gamma_{t+1}=\sum_{a} w_{t+1}(a)=\sum_{a} w_t(a)(1-\epsilon)^{c_t(a)} \le \sum_{a} w_t(a)(1-\epsilon c_t(a)) = \Gamma_t(1-\epsilon\nu_t), \quad(3)$$
where (3) uses $(1-\epsilon)^x\le 1-\epsilon x$ for $\epsilon\in[0,\tfrac12]$, $x\in[0,1]$.

<a id="pdf-eda737ce3103-p006-b003"></a>
<!-- pdf-source: page=6; block=3; confidence=0.95 -->
**Proof (step 3).** Combining with $\Gamma_1=n$:
$$(1-\epsilon)^{OPT}\le \Gamma_T \le \Gamma_1\prod_{t=1}^T (1-\epsilon\nu_t)=n\prod_{t=1}^T(1-\epsilon\nu_t),$$
and taking logarithms,
$$OPT\cdot\ln(1-\epsilon)\le \ln n+\sum_{t=1}^T \ln(1-\epsilon\nu_t).$$

<a id="pdf-eda737ce3103-p007-b001"></a>
<!-- pdf-source: page=7; block=1; confidence=0.95 -->
**Proof (continued).** Using the Taylor expansion $\ln(1-x) = -x - \tfrac{x^2}{2} - \tfrac{x^3}{3} - \cdots$: keep only the first term to get the upper bound $\ln(1-\epsilon\nu_t) \le -\epsilon\nu_t$, and keep the first two terms (doubling the second) to get, for $\epsilon \le \tfrac12$, the lower bound $\ln(1-\epsilon) \ge -\epsilon-\epsilon^2$. Hence for $\epsilon\in(0,\tfrac12]$,
$$OPT\cdot[-\epsilon-\epsilon^2] \le \ln n + \sum_{t=1}^{T}(-\epsilon\nu_t),$$
which rearranges to equation (4):
$$\sum_{t=1}^{T}\nu_t \le OPT\cdot(1+\epsilon) + \frac{\ln n}{\epsilon} \le OPT + \epsilon T + \frac{\ln n}{\epsilon},$$
using $OPT \le T$ (costs at most 1). Setting $\epsilon = \sqrt{\ln n / T}$ equalizes the two error terms, so the MW algorithm's cumulative expected cost exceeds the best fixed action by at most $2\sqrt{T\ln n}$; dividing by $T$ gives per-time-step regret at most $2\sqrt{\ln n / T}$. $\blacksquare$

<a id="pdf-eda737ce3103-p007-b002"></a>
<!-- pdf-source: page=7; block=2; confidence=0.94 -->
**Remark 2.3 (When T Is Unknown).** If the horizon $T$ is unknown, at day $t$ use $\epsilon = \sqrt{\ln n / \hat T}$, where $\hat T$ is the smallest power of 2 larger than $t$; the regret guarantee of Theorem 2.1 still holds (left to the Exercises).

<a id="pdf-eda737ce3103-p007-b003"></a>
<!-- pdf-source: page=7; block=3; confidence=0.90 -->
Example 1.8 shows Theorem 2.1 is optimal up to the constant in the additive term. Corollary 2.2: only $\tfrac{4\ln n}{\epsilon^2}$ iterations of MW suffice to achieve expected regret at most $\epsilon$.

<a id="pdf-eda737ce3103-p007-b004"></a>
<!-- pdf-source: page=7; block=4; confidence=0.95 -->
**3 No-Regret Dynamics.** Passing from single-player to multi-player cost-minimization games (analog exists for payoff-maximization).

<a id="pdf-eda737ce3103-p007-b005"></a>
<!-- pdf-source: page=7; block=5; confidence=0.93 -->
**Definition (No-regret dynamics).** In each time step $t=1,\dots,T$: (1) each player $i$ simultaneously and independently chooses a mixed strategy $p_i^t$ using a no-regret algorithm; (2) each player $i$ receives a cost vector $c_i^t$, where $c_i^t(s_i) = \mathbb{E}_{s_{-i}\sim\sigma_{-i}}[C_i(s_i,s_{-i})]$ is the expected cost of strategy $s_i$ when others play their chosen mixed strategies, with $\sigma_{-i} = \prod_{j\neq i}\sigma_j$.

<a id="pdf-eda737ce3103-p008-b001"></a>
<!-- pdf-source: page=8; block=1; confidence=0.90 -->
No-regret dynamics are well defined (no-regret algorithms exist, Theorem 2.1); each player may use any such algorithm and results extend to sequential moves. With MW, each iteration is a per-strategy weight update and only $O(\tfrac{\ln n}{\epsilon^2})$ iterations are needed for every player to have expected regret at most $\epsilon$ ($n$ = max strategy-set size). Key point: the time-averaged joint play converges to the set of coarse correlated equilibria (CCE).

<a id="pdf-eda737ce3103-p008-b002"></a>
<!-- pdf-source: page=8; block=2; confidence=0.95 -->
**Proposition 3.1.** Suppose after $T$ iterations of no-regret dynamics every player of a cost-minimization game has regret at most $\epsilon$ for each strategy. Let $\sigma^t = \prod_{i=1}^{k} p_i^t$ be the outcome distribution at time $t$ and $\sigma = \tfrac{1}{T}\sum_{t=1}^{T}\sigma^t$ the time-averaged history. Then $\sigma$ is an $\epsilon$-approximate coarse correlated equilibrium:
$$\mathbb{E}_{s\sim\sigma}[C_i(s)] \le \mathbb{E}_{s\sim\sigma}[C_i(s_i',s_{-i})] + \epsilon$$
for every player $i$ and unilateral deviation $s_i'$.

<a id="pdf-eda737ce3103-p008-b003"></a>
<!-- pdf-source: page=8; block=3; confidence=0.95 -->
**Proof.** For every player $i$,
$$\mathbb{E}_{s\sim\sigma}[C_i(s)] = \tfrac{1}{T}\sum_{t=1}^{T}\mathbb{E}_{s\sim\sigma^t}[C_i(s)] \quad(5)$$
$$\mathbb{E}_{s\sim\sigma}[C_i(s_i',s_{-i})] = \tfrac{1}{T}\sum_{t=1}^{T}\mathbb{E}_{s\sim\sigma^t}[C_i(s_i',s_{-i})] \quad(6)$$
The right-hand sides are player $i$'s time-averaged expected costs under its no-regret algorithm and under the fixed action $s_i'$, respectively. Since regret is at most $\epsilon$, the former exceeds the latter by at most $\epsilon$, verifying the approximate CCE condition. $\blacksquare$

<a id="pdf-eda737ce3103-p008-b004"></a>
<!-- pdf-source: page=8; block=4; confidence=0.92 -->
**Remark 3.2.** Proposition 3.1 requires the players' algorithms to have no regret against adaptive adversaries: player $i$'s mixed strategy at time $t$ affects other players' cost vectors $c_j^t$, hence their future strategies, hence player $i$'s future cost vectors. Other players using adaptive learning thus constitute an adaptive adversary.

<a id="pdf-eda737ce3103-p009-b001"></a>
<!-- pdf-source: page=9; block=1; confidence=0.92 -->
POA bounds for smooth games (Lecture 14) automatically extend to coarse correlated equilibria, and remain approximately correct for approximate equilibria.

<a id="pdf-eda737ce3103-p009-b002"></a>
<!-- pdf-source: page=9; block=2; confidence=0.90 -->
**Corollary 3.3** *Suppose after $T$ iterations of no-regret dynamics, player $i$ has expected regret at most $R_i$ for each of its actions. Then the time-averaged expected objective function value $\tfrac{1}{T}\mathbb{E}_{s\sim\sigma^i}[\mathrm{cost}(s)]$ is at most*
$$\frac{\lambda}{1-\mu}\,\mathrm{cost}(s^*) + \frac{\sum_{i=1}^{k}R_i}{1-\mu}.$$
In particular, as $T\to\infty$, $\sum_{i=1}^{k}R_i \to 0$ and the guarantee converges to the standard POA bound $\tfrac{\lambda}{1-\mu}$. We leave the proof of Corollary 3.3 as an exercise.

<a id="pdf-eda737ce3103-p009-b003"></a>
<!-- pdf-source: page=9; block=3; confidence=0.93 -->
**4 Epilogue.** Take-home points: (1) simple learning algorithms reach approximate CCE remarkably quickly; (2) CCE are correspondingly tractable and plausible as a behavioral prediction; (3) since POA bounds for smooth games apply to no-regret dynamics, they are robust to the behavioral model.

<a id="pdf-eda737ce3103-p009-b004"></a>
<!-- pdf-source: page=9; block=4; confidence=0.95 -->
References: [1] Arora, Hazan, Kale, *The multiplicative weights update method*, Theory of Computing 8(1):121–164, 2012; [2] Cesa-Bianchi & Lugosi, *Prediction, Learning, and Games*, Cambridge Univ. Press, 2006; [3] Hannan, *Approximation to Bayes risk in repeated play*, Contributions to the Theory of Games 3:97–139, 1957; [4] Littlestone & Warmuth, *The weighted majority algorithm*, Information and Computation 108(2):212–261, 1994.
