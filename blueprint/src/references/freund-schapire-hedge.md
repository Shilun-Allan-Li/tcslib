<!-- generated-by: proofmatch Claude repair -->
<!-- source-pdf-sha256: 01f49de027c4c2c146869da85f8e8482d6b723344cb80ce957d11e93c615e7cc -->

<a id="pdf-01f49de027c4-p001-b001"></a>
<!-- pdf-source: page=1; block=1; confidence=0.97 -->
**A Decision-Theoretic Generalization of On-Line Learning and an Application to Boosting.** Yoav Freund and Robert E. Schapire, AT&T Labs, Florham Park, NJ. *Journal of Computer and System Sciences* **55**, 119–139 (1997), article SS971504. Received December 19, 1996.

<a id="pdf-01f49de027c4-p001-b002"></a>
<!-- pdf-source: page=1; block=2; confidence=0.95 -->
**Abstract.** Part I studies worst-case on-line dynamic apportioning of resources among $N$ options, an abstract decision-theoretic extension of on-line prediction. The multiplicative weight-update Littlestone–Warmuth rule is adapted to this model, yielding slightly weaker but far more general bounds; applications include gambling, multiple-outcome prediction, repeated games, and prediction of points in $\mathbb{R}^n$. Part II derives a new boosting algorithm requiring no prior knowledge of the weak learner's performance, plus generalizations to non-binary finite ranges and to bounded real-valued ranges.

<a id="pdf-01f49de027c4-p001-b003"></a>
<!-- pdf-source: page=1; block=3; confidence=0.93 -->
**1. Introduction.** Motivating horse-racing story: a gambler apportions a fixed wager among friends by how well they perform, aiming to nearly match betting entirely with the best friend. The paper gives an algorithm for such dynamic allocation and applies it broadly, including a new boosting algorithm that converts a weak PAC learner (slightly better than random) into an arbitrarily accurate one.

<a id="pdf-01f49de027c4-p001-b004"></a>
<!-- pdf-source: page=1; block=4; confidence=0.95 -->
**On-line allocation model.** Allocation agent $A$ has $N$ strategies $1,\dots,N$. At each step $t=1,\dots,T$, $A$ picks a distribution $p^t$ over strategies with $p_i^t \ge 0$ and $\sum_{i=1}^N p_i^t = 1$. Each strategy $i$ suffers loss $l_i^t$; $A$'s loss is the **mixture loss** $p^t\cdot l^t = \sum_{i=1}^N p_i^t l_i^t$. Assume w.l.o.g. $l_i^t \in [0,1]$, with no other restriction on $l^t$; the adversary may choose $l^t$ depending on $p^t$. Goal: minimize the net loss $L_A - \min_i L_i$, where $L_A = \sum_{t=1}^T p^t\cdot l^t$ is $A$'s cumulative loss and $L_i = \sum_{t=1}^T l_i^t$ is strategy $i$'s cumulative loss. Section 2 generalizes the Littlestone–Warmuth weighted-majority algorithm to this setting.

<a id="pdf-01f49de027c4-p002-b001"></a>
<!-- pdf-source: page=2; block=1; confidence=0.90 -->
The net loss is bounded by $O(\sqrt{T\ln N})$; equivalently the average per-trial net loss decreases at rate $O(\sqrt{(\ln N)/T}) \to 0$. Section 3 generalizes Littlestone–Warmuth [20] and Cesa-Bianchi et al. [4] expert-prediction results from binary decision/outcome spaces with $[0,1]$-valued loss to any bounded loss over arbitrary decision and outcome spaces, giving explicit rates approaching the best expert. Related multiplicative-weight generalizations: Vovk [25], Kivinen–Warmuth [19], Haussler et al. [15]; Chung [5] gave a game-theoretic treatment.

<a id="pdf-01f49de027c4-p002-b002"></a>
<!-- pdf-source: page=2; block=2; confidence=0.95 -->
**Boosting.** The booster receives labelled examples $(x_1,y_1),\dots,(x_N,y_N)$. On each round $t=1,\dots,T$ it forms a distribution $D_t$ over examples and requests a weak hypothesis $h_t$ with error $\varepsilon_t = \Pr_{i\sim D_t}[h_t(x_i)\ne y_i]$. After $T$ rounds the weak hypotheses are combined into a weighted-majority hypothesis whose weights depend on each hypothesis's accuracy; unlike Freund [10,11] and Schapire [22], no prior knowledge of the accuracies is needed. For binary prediction (Section 4) the final hypothesis error is bounded by $\exp\!\big(-2\sum_{t=1}^T \gamma_t^2\big)$ where $\varepsilon_t = \tfrac12 - \gamma_t$, so $\gamma_t$ is accuracy relative to random guessing; error drops exponentially if weak hypotheses beat random. The bound improves when any single weak hypothesis improves (prior bounds depended only on the least accurate). Section 5 extends to multi-class and to real-valued regression.

<a id="pdf-01f49de027c4-p002-b003"></a>
<!-- pdf-source: page=2; block=3; confidence=0.95 -->
**2. The On-Line Allocation Algorithm and Its Analysis.** Introduces the algorithm $\mathrm{Hedge}(\beta)$ for on-line allocation.

<a id="pdf-01f49de027c4-p003-b001"></a>
<!-- pdf-source: page=3; block=1; confidence=0.92 -->
$\mathrm{Hedge}(\beta)$ directly generalizes the Littlestone–Warmuth weighted-majority algorithm [20]. It maintains a nonnegative weight vector $w^t = (w_1^t,\dots,w_N^t)$. The initial $w^1$ is nonnegative with $\sum_{i=1}^N w_i^1 = 1$ (a "prior"); bounds are strongest for strategies with greatest initial weight. With no preference one sets $w_i^1 = 1/N$. Weights on later trials need not sum to one.

<a id="pdf-01f49de027c4-p003-b002"></a>
<!-- pdf-source: page=3; block=2; confidence=0.90 -->
**Algorithm $\mathrm{Hedge}(\beta)$ (Fig. 1).** Parameters: $\beta\in[0,1]$; initial $w^1\in[0,1]^N$ with $\sum_{i=1}^N w_i^1 = 1$; number of trials $T$. For $t=1,\dots,T$:
1. Choose allocation $p^t = w^t / \sum_{i=1}^N w_i^t$  (Eq. 1).
2. Receive loss vector $l^t\in[0,1]^N$.
3. Suffer loss $p^t\cdot l^t$.
4. Update $w_i^{t+1} = w_i^t\,\beta^{l_i^t}$  (Eq. 2).

The analysis applies with minor modification to any update $w_i^{t+1} = w_i^t\,U_\beta(l_i^t)$ where $U_\beta:[0,1]\to[0,1]$ satisfies $\beta^r \le U_\beta(r) \le 1-(1-\beta)r$ for all $r\in[0,1]$.

<a id="pdf-01f49de027c4-p003-b003"></a>
<!-- pdf-source: page=3; block=3; confidence=0.93 -->
**Lemma 1.** For any sequence of loss vectors $l^1,\dots,l^T$,
$$\ln\!\Big(\sum_{i=1}^N w_i^{T+1}\Big) \le -(1-\beta)\,L_{\mathrm{Hedge}(\beta)}.$$
(Section 2.1 Analysis: bound $\sum_{i=1}^N w_i^{T+1}$ above and below to bound the algorithm's loss; this is the upper bound.)

<a id="pdf-01f49de027c4-p003-b004"></a>
<!-- pdf-source: page=3; block=4; confidence=0.88 -->
**Proof.** By convexity, $\alpha^r \le 1-(1-\alpha)r$ for $\alpha\ge 0$, $r\in[0,1]$ (Eq. 3). With Eqs. (1),(2),
$$\sum_{i=1}^N w_i^{t+1} = \sum_{i=1}^N w_i^t\beta^{l_i^t} \le \sum_{i=1}^N w_i^t\big(1-(1-\beta)l_i^t\big) = \Big(\sum_{i=1}^N w_i^t\Big)\big(1-(1-\beta)\,p^t\cdot l^t\big) \quad(\text{Eq. 4}).$$
Applying repeatedly for $t=1,\dots,T$,
$$\sum_{i=1}^N w_i^{T+1} \le \prod_{t=1}^T\big(1-(1-\beta)\,p^t\cdot l^t\big) \le \exp\!\Big(-(1-\beta)\sum_{t=1}^T p^t\cdot l^t\Big),$$
since $1+x\le e^x$. The lemma follows. $\;\blacksquare$ Consequently $L_{\mathrm{Hedge}(\beta)} \le -\ln\!\big(\sum_{i=1}^N w_i^{T+1}\big)/(1-\beta)$ (Eq. 5). Also, from Eq. (2), $w_i^{T+1} = w_i^1\prod_{t=1}^T \beta^{l_i^t} = w_i^1\,\beta^{L_i}$ (Eq. 6).

<a id="pdf-01f49de027c4-p004-b001"></a>
<!-- pdf-source: page=4; block=1; confidence=0.90 -->
**Theorem 2.** For any sequence of loss vectors l¹,…,lᵀ and any i∈{1,…,N},

$$L_{\mathrm{Hedge}(\beta)} \le \frac{-\ln(w^1_i) - L_i\ln\beta}{1-\beta}. \tag{7}$$

More generally, for any nonempty S⊆{1,…,N},

$$L_{\mathrm{Hedge}(\beta)} \le \frac{-\ln\!\big(\sum_{i\in S} w^1_i\big) - (\ln\beta)\,\max_{i\in S} L_i}{1-\beta}. \tag{8}$$

<a id="pdf-01f49de027c4-p004-b002"></a>
<!-- pdf-source: page=4; block=2; confidence=0.90 -->
**Proof.** Prove the general statement (8); (7) is the special case S={i}. From Eq. (6),

$$\sum_{i=1}^N w^{T+1}_i \ge \sum_{i\in S} w^{T+1}_i = \sum_{i\in S} w^1_i\,\beta^{L_i} \ge \beta^{\max_{i\in S} L_i}\sum_{i\in S} w^1_i.$$

The theorem then follows from Eq. (5). ∎

<a id="pdf-01f49de027c4-p004-b003"></a>
<!-- pdf-source: page=4; block=3; confidence=0.88 -->
Bound (7) shows Hedge(β) loss exceeds that of the best strategy i by an amount depending on β and w¹ᵢ. With equal initial weights w¹ᵢ=1/N,

$$L_{\mathrm{Hedge}(\beta)} \le \frac{\min_i L_i\,\ln(1/\beta) + \ln N}{1-\beta}. \tag{9}$$

The dependence on N is only logarithmic, so the bound is reasonable for very large N. Bound (8) generalizes (7) to infinite strategy sets, where the sum may be replaced by an integral and the max by a supremum.

<a id="pdf-01f49de027c4-p004-b004"></a>
<!-- pdf-source: page=4; block=4; confidence=0.90 -->
Bound (9) can be written

$$L_{\mathrm{Hedge}(\beta)} \le c\,\min_i L_i + a\,\ln N, \tag{10}$$

with $c=\ln(1/\beta)/(1-\beta)$ and $a=1/(1-\beta)$. Vovk [24] proves tight upper/lower bounds on achievable c and a; by his results the constants c and a of Hedge(β) are optimal.

<a id="pdf-01f49de027c4-p004-b005"></a>
<!-- pdf-source: page=4; block=5; confidence=0.90 -->
**Theorem 3.** Let B be an on-line allocation algorithm (arbitrary number of strategies). Suppose positive reals a, c exist such that for any number of strategies N and any loss sequence l¹,…,lᵀ,

$$L_B \le c\,\min_i L_i + a\,\ln N.$$

Then for all β∈(0,1), either

$$c \ge \frac{\ln(1/\beta)}{1-\beta} \quad\text{or}\quad a \ge \frac{1}{1-\beta}.$$

Proof given in the appendix.

<a id="pdf-01f49de027c4-p004-b006"></a>
<!-- pdf-source: page=4; block=6; confidence=0.85 -->
**2.2. How to Choose β.** Choose β to exploit prior knowledge about the specific problem; the following lemma aids this using the derived bounds.

<a id="pdf-01f49de027c4-p004-b007"></a>
<!-- pdf-source: page=4; block=7; confidence=0.90 -->
**Lemma 4.** Suppose 0≤L≤L̃ and 0<R≤R̃. Let β=g(L̃/R̃) where g(z)=1/(1+√(2/z)). Then

$$\frac{-L\ln\beta + R}{1-\beta} \le L + \sqrt{2\tilde L\tilde R} + R.$$

**Proof (sketch).** Using $-\ln\beta \le (1-\beta^2)/(2\beta)$ for β∈(0,1] together with the given β yields the result. ∎

<a id="pdf-01f49de027c4-p004-b008"></a>
<!-- pdf-source: page=4; block=8; confidence=0.90 -->
Lemma 4 applies to all the above bounds. With N strategies and a prior bound L̃ on the best strategy's loss, combining (9) and Lemma 4 gives

$$L_{\mathrm{Hedge}(\beta)} \le \min_i L_i + \sqrt{2\tilde L\,\ln N} + \ln N \tag{11}$$

for β=g(L̃/ln N). If T is known ahead of time, take L̃=T. Dividing (11) by T bounds the average per-trial loss:

$$\frac{L_{\mathrm{Hedge}(\beta)}}{T} \le \min_i \frac{L_i}{T} + \frac{\sqrt{2\tilde L\,\ln N}}{T} + \frac{\ln N}{T}. \tag{12}$$

<a id="pdf-01f49de027c4-p005-b001"></a>
<!-- pdf-source: page=5; block=1; confidence=0.85 -->
Since L̂≤T, (12) gives worst-case rate O(√((ln N)/T)); if L̂≈0 the rate is roughly O((ln N)/T). Lemma 4 applies to the other bounds of Theorem 2 too. Bound (11) can improve in special loss forms (Example 4), but in general the term √(2L̂ ln N) cannot be improved by more than a constant factor — a corollary of the lower bound of Cesa-Bianchi et al. ([4], Theorem 7).

<a id="pdf-01f49de027c4-p005-b002"></a>
<!-- pdf-source: page=5; block=2; confidence=0.90 -->
**3. Applications.** Setup (Chung [5]): decision space Δ, outcome space Ω, bounded loss λ:Δ×Ω→[0,1] (any bounded λ rescales to [0,1]). At each step t the learner picks decision δₜ∈Δ, receives outcome ωₜ∈Ω, suffers λ(δₜ,ωₜ). Allowing a distribution Dₜ over decisions, its expected loss is

$$\Lambda(D,\omega) = \mathbb{E}_{\delta\sim D}[\lambda(\delta,\omega)].$$

The learner has N experts; expert i produces distribution E^t_i on Δ and suffers Λ(E^t_i,ωₜ). Goal: combine experts to suffer expected loss not much worse than the best expert.

<a id="pdf-01f49de027c4-p005-b003"></a>
<!-- pdf-source: page=5; block=3; confidence=0.90 -->
Run Hedge(β) treating each expert as a strategy. It produces distribution pₜ over experts, giving the mixture $D_t=\sum_{i=1}^N p^t_i E^t_i$. The loss suffered is $\Lambda(D_t,\omega_t)=\sum_{i=1}^N p^t_i\,\Lambda(E^t_i,\omega_t)$. Setting $l^t_i=\Lambda(E^t_i,\omega_t)$, the learner's loss is $p_t\cdot l_t$, exactly the mixture loss analyzed in Section 2, so all Section 2 bounds apply.

<a id="pdf-01f49de027c4-p005-b004"></a>
<!-- pdf-source: page=5; block=4; confidence=0.90 -->
**Theorem 5.** For any loss function λ, any set of experts, and any outcome sequence, the expected loss of Hedge(β) used as above satisfies

$$\sum_{t=1}^T \Lambda(D_t,\omega_t) \le \min_i \sum_{t=1}^T \Lambda(E^t_i,\omega_t) + \sqrt{2\hat L\,\ln N} + \ln N,$$

where L̂≤T bounds the expected loss of the best expert and β=g(L̂/ln N).

<a id="pdf-01f49de027c4-p005-b005"></a>
<!-- pdf-source: page=5; block=5; confidence=0.88 -->
**Example 1 (k-ary prediction).** Δ=Ω={1,…,k}; λ(δ,ω)=1 if δ≠ω, else 0 (predict a sequence of letters over a size-k alphabet). Then Λ(D,ω) is the probability of a disagreeing prediction, and cumulative loss = expected number of mistakes. By Theorem 2 the learner's expected mistakes exceed the best expert's by at most O(√(T ln N)), or much less if the best expert's loss is bounded a priori. Binary case (k=2) previously by Littlestone–Warmuth [20], improved by Vovk [25] and Cesa-Bianchi et al. [4]; the new result holds for any bounded loss.

<a id="pdf-01f49de027c4-p005-b006"></a>
<!-- pdf-source: page=5; block=6; confidence=0.82 -->
**Example 2 (matrix game).** λ represents a game matrix, e.g. rock/paper/scissors with Δ=Ω={R,P,S} and loss matrix (rows = learner's play δ, columns = adversary's outcome ω):

|   | R | P | S |
|---|---|---|---|
| R | ½ | 1 | 0 |
| P | 0 | ½ | 1 |
| S | 1 | 0 | ½ |

λ(δ,ω)=1 if the learner loses the round, 0 if it wins, ½ if tied (e.g. λ(S,P)=0, scissors cut paper). For outcome ωₜ the loss is $\Lambda(D_t,\omega_t)=\sum_{i=1}^N p^t_i\,\Lambda(E^t_i,\omega_t)$.

<a id="pdf-01f49de027c4-p006-b001"></a>
<!-- pdf-source: page=6; block=1; confidence=0.85 -->
Cumulative loss of the learner (or an expert) is the expected number of rounds lost, counting ties as half a loss. In repeated play the learner's expected rounds lost converges quickly to that of the best expert for the actual adversary move sequence.

<a id="pdf-01f49de027c4-p006-b002"></a>
<!-- pdf-source: page=6; block=2; confidence=0.82 -->
**Example 3.** Δ, Ω finite, λ a game matrix; create one expert per decision δ∈Δ that always plays δ (pure strategies). Von Neumann's min-max theorem: for any fixed matrix a mixed strategy achieves the min-max optimal expected loss (the value of the game). Using Hedge(β) to pick action distributions in repeated play, Theorem 2 implies the learner's average per-round loss exceeds the best pure strategy's by a maximal gap decreasing at O(1/√T · log|Δ|). The optimal mixed strategy's loss is a convex combination of pure-strategy losses, hence never below the best pure strategy for a given sequence; so Hedge(β)'s expected per-trial loss is bounded by the value of the game plus O(1/√T · log|Δ|), even if λ is unknown to the learner and the adversary knows both the game and the algorithm. Similar (weaker-bound) algorithms: Blackwell [2], Hannan [14]; see [13].

<a id="pdf-01f49de027c4-p006-b003"></a>
<!-- pdf-source: page=6; block=3; confidence=0.85 -->
**Example 4.** Δ=Ω = unit ball in Rⁿ and λ(δ,ω)=‖δ−ω‖: predict a point ω, suffering the Euclidean distance to the prediction δ. Theorem 2 applies with probabilistic predictions, but here it is natural to require the learner and each expert to predict a single point — the problem of tracking a sequence of points ω¹,…,ωᵀ.

<a id="pdf-01f49de027c4-p006-b004"></a>
<!-- pdf-source: page=6; block=4; confidence=0.88 -->
The loss λ(δ,ω)=‖δ−ω‖ is convex in δ:

$$\|a\delta_1+(1-a)\delta_2 - \omega\| \le a\|\delta_1-\omega\| + (1-a)\|\delta_2-\omega\| \tag{13}$$

for a∈[0,1], ω∈Ω. So the learner predicts the weighted average $\delta_t=\sum_{i=1}^N p^t_i\,\varepsilon^t_i$ (ε^t_i∈Rⁿ the i-th expert's prediction), and (13) gives

$$\|\delta_t-\omega_t\| \le \sum_{i=1}^N p^t_i\,\|\varepsilon^t_i-\omega_t\|.$$

Theorem 2 bounds the right side, hence the total prediction error relative to the best expert. One-dimensional case (n=1): Littlestone–Warmuth [20], improved by Kivinen–Warmuth [19].

<a id="pdf-01f49de027c4-p006-b005"></a>
<!-- pdf-source: page=6; block=5; confidence=0.85 -->
The result needs only convexity and bounded range of λ(δ,ω) in δ. It also applies to the squared-distance loss λ(δ,ω)=‖δ−ω‖² and the log loss λ(δ,ω)=−ln(δ·ω) used by Cover [6] for universal investment portfolios (there Δ is the set of probability vectors on n points and Ω=[1/B,B]ⁿ for B>1). Though superior specialized algorithms exist, these results are far more general (e.g. the horse-racing example).

<a id="pdf-01f49de027c4-p006-b006"></a>
<!-- pdf-source: page=6; block=6; confidence=0.85 -->
**4. Boosting.** The Section 2 on-line allocation algorithm is modified to boost weak learning algorithms. PAC model review (Kearns–Vazirani [18]): X is the domain; a concept is a Boolean function c:X→{0,1}; a concept class C is a collection of concepts. The learner accesses an oracle giving labelled examples (x,c(x)) with x drawn from a fixed but unknown distribution.

<a id="pdf-01f49de027c4-p007-b001"></a>
<!-- pdf-source: page=7; block=1; confidence=0.95 -->
**Definition (learning model).** A learner faces an unknown, arbitrary distribution D on a domain X with target concept c ∈ C, and outputs a hypothesis h: X → [0,1]; h(x) is interpreted as a randomized prediction equal to 1 with probability h(x) and 0 with probability 1 − h(x). The error of h is E_{x~D}[ |h(x) − c(x)| ], which for a stochastic prediction equals the probability of an incorrect prediction.

<a id="pdf-01f49de027c4-p007-b002"></a>
<!-- pdf-source: page=7; block=2; confidence=0.95 -->
**Definition (PAC learning).** A strong PAC-learning algorithm, given ε, δ > 0 and access to random examples, outputs with probability ≥ 1 − δ a hypothesis of error ≤ ε, in time polynomial in 1/ε, 1/δ and the example/concept size (or complexity). A weak PAC-learning algorithm satisfies the same conditions only for ε ≥ 1/2 − γ, where γ > 0 is either constant or decreases as 1/p for a polynomial p in the relevant parameters. WeakLearn denotes a generic weak learning algorithm.

<a id="pdf-01f49de027c4-p007-b003"></a>
<!-- pdf-source: page=7; block=3; confidence=0.90 -->
Schapire showed any weak learner can be boosted into a strong learner; Freund's more efficient 'boost-by-majority' repeatedly calls WeakLearn on different reweighted distributions over X (emphasizing harder regions) and combines the hypotheses. Key deficiency: boost-by-majority requires the worst-case bias γ known in advance and cannot exploit hypotheses whose error is significantly below 1/2 − γ.

<a id="pdf-01f49de027c4-p007-b004"></a>
<!-- pdf-source: page=7; block=4; confidence=0.90 -->
This section presents a new boosting algorithm derived from the Section 2 on-line allocation algorithm: nearly as efficient as boost-by-majority, but its final-hypothesis accuracy depends on the accuracy of all WeakLearn hypotheses (fully exploiting the weak learner), and it cleanly handles real-valued hypotheses.

<a id="pdf-01f49de027c4-p007-b005"></a>
<!-- pdf-source: page=7; block=5; confidence=0.98 -->
**4.1. The New Boosting Algorithm**

<a id="pdf-01f49de027c4-p007-b006"></a>
<!-- pdf-source: page=7; block=6; confidence=0.90 -->
General framework: examples (x_i, y_i) are drawn from a fixed unknown distribution P on X × Y, and the goal is to predict y from x. The algorithm is first given for two labels, Y = {0,1}. It uses the boosting-by-sampling framework (batch learning on a stored training set) rather than boosting by filtering. Given N examples (x_1,y_1),…,(x_N,y_N) drawn from P, boosting seeks a hypothesis h_f consistent with most of the sample (h_f(x_i) = y_i for most i); overfitting is mitigated by keeping h_f simple (Section 4.3).

<a id="pdf-01f49de027c4-p007-b007"></a>
<!-- pdf-source: page=7; block=7; confidence=0.90 -->
The algorithm (Fig. 2) targets low error under a distribution D over the training examples, which the learner controls (unlike P, set by nature) and is typically uniform, D(i) = 1/N. It maintains a weight vector w_t; on iteration t the weights are normalized into a distribution p_t, which is fed to WeakLearn to obtain a hypothesis h_t of hopefully small error, and the weights are then updated. Footnote: algorithms that cannot use p_t directly can resample the training set (O(log N) time per resampled example).

<a id="pdf-01f49de027c4-p008-b001"></a>
<!-- pdf-source: page=8; block=1; confidence=0.90 -->
Drucker–Schapire–Simard observed that summing real-valued network outputs before selecting the best prediction outperforms selecting each network's best prediction and then majority-combining; AdaBoost's final hypothesis uses this same combination rule, which previously lacked theoretical justification. Several successful AdaBoost experiments are cited (the authors; Drucker–Cortes; Jackson–Craven; Quinlan; Breiman).

<a id="pdf-01f49de027c4-p008-b002"></a>
<!-- pdf-source: page=8; block=2; confidence=0.98 -->
**4.2. Analysis**

<a id="pdf-01f49de027c4-p008-b003"></a>
<!-- pdf-source: page=8; block=3; confidence=0.90 -->
Hedge(β) and AdaBoost are structurally similar via a dual reduction of boosting to on-line allocation, but reversed: 'strategies' correspond to examples and trials to weak hypotheses. The loss is also reversed — in AdaBoost l_i^t = 1 − |h_t(x_i) − y_i| is small when the t-th hypothesis predicts the i-th example badly — and a weight is increased for a 'hard' example rather than for a successful strategy.

<a id="pdf-01f49de027c4-p008-b004"></a>
<!-- pdf-source: page=8; block=4; confidence=0.85 -->
**Reduction to Hedge(β).** The main technical difference is that β is no longer fixed but varies with ε_t. If ε_t ≤ 1/2 − γ is known in advance for all t = 1,…,T, one may instead run Hedge(β) with fixed β = 1 − γ, loss l_i^t = 1 − |h_t(x_i) − y_i|, and h_f as in AdaBoost but with equal weight on all T hypotheses. Then p_t · l_t equals h_t's accuracy on p_t, which is ≥ 1/2 + γ. Letting S = {i : h_f(x_i) ≠ y_i}, for i ∈ S: L_i^T/T = (1/T) Σ_{t=1}^T l_i^t = 1 − (1/T) Σ_{t=1}^T |y_i − h_t(x_i)| = 1 − |y_i − (1/T) Σ_{t=1}^T h_t(x_i)| ≤ 1/2.

<a id="pdf-01f49de027c4-p008-b005"></a>
<!-- pdf-source: page=8; block=5; confidence=0.92 -->
**Algorithm AdaBoost (Fig. 2).** Input: N labeled examples ((x_1,y_1),…,(x_N,y_N)); a distribution D over them; WeakLearn; iteration count T. Initialize w_1^i = D(i) for i = 1,…,N. For t = 1,…,T: (1) p_t = w_t / Σ_{i=1}^N w_t^i; (2) call WeakLearn on p_t to get a hypothesis h_t: X → [0,1]; (3) compute error ε_t = Σ_{i=1}^N p_t^i |h_t(x_i) − y_i|; (4) set β_t = ε_t/(1 − ε_t); (5) update w_{t+1}^i = w_t^i · β_t^{1 − |h_t(x_i) − y_i|}. Output h_f(x) = 1 if Σ_{t=1}^T (log 1/β_t) h_t(x) ≥ (1/2) Σ_{t=1}^T log 1/β_t, and 0 otherwise.

<a id="pdf-01f49de027c4-p008-b006"></a>
<!-- pdf-source: page=8; block=6; confidence=0.90 -->
After T iterations h_f is output as a weighted majority vote of the h_t. It is named AdaBoost because it adapts to WeakLearn's errors: if WeakLearn is a PAC weak learner then ε_t ≤ 1/2 − γ, but no such bound need be known in advance — the results hold for any ε_t ∈ [0,1] and depend only on the distributions actually generated. β_t (a function of ε_t) drives the update, lowering the probability of well-predicted examples and raising that of poorly-predicted ones. AdaBoost combines hypotheses by summing probabilistic predictions. Footnote: for Boolean h_t the update makes h_t's error on p_{t+1} exactly 1/2.

<a id="pdf-01f49de027c4-p009-b001"></a>
<!-- pdf-source: page=9; block=1; confidence=0.90 -->
**(Hedge bound, concluded.)** Using y_i ∈ {0,1} and h_f's definition, the previous inequality gives L_i^T/T ≤ 1/2 for i ∈ S. Then by Theorem 2, T(1/2 + γ) ≤ Σ_{t=1}^T p^t · l^t ≤ [ −ln(Σ_{i∈S} D(i)) + (γ + γ²)(T/2) ] / γ, which implies that the error ε = Σ_{i∈S} D(i) of h_f is at most e^{−Tγ²/2}.

<a id="pdf-01f49de027c4-p009-b002"></a>
<!-- pdf-source: page=9; block=2; confidence=0.90 -->
AdaBoost improves on this direct Hedge(β) application in two ways: (1) a more refined analysis and choice of β gives a significantly better error bound; (2) it needs no prior knowledge of WeakLearn's accuracy, instead measuring ε_t each round and setting β_t accordingly. Smaller ε_t yields smaller β_t, which widens the gap between p_t and p_{t+1} and increases the vote weight ln(1/β_t) of h_t — so more accurate hypotheses shift the distributions more and influence h_f more.

<a id="pdf-01f49de027c4-p009-b003"></a>
<!-- pdf-source: page=9; block=3; confidence=0.92 -->
**Theorem 6.** If WeakLearn, when called by AdaBoost, generates hypotheses with errors ε_1,…,ε_T (as in Step 3 of Fig. 2), then the final hypothesis's error ε = Pr_{i~D}[ h_f(x_i) ≠ y_i ] is bounded by

ε ≤ 2^T ∏_{t=1}^T √( ε_t (1 − ε_t) ).  (14)

The bound also applies when ε_t ≥ 1/2 for some hypotheses.

<a id="pdf-01f49de027c4-p009-b004"></a>
<!-- pdf-source: page=9; block=4; confidence=0.90 -->
**Proof.** Adapting Lemma 1 and Theorem 2 with p_t, w_t from Fig. 2. The Step-5 update gives Σ_{i=1}^N w_{t+1}^i = Σ_i w_t^i β_t^{1 − |h_t(x_i) − y_i|} ≤ Σ_i w_t^i (1 − (1 − β_t)(1 − |h_t(x_i) − y_i|)) = (Σ_i w_t^i)(1 − (1 − ε_t)(1 − β_t)) (15). Iterating over t: Σ_i w_{T+1}^i ≤ ∏_{t=1}^T (1 − (1 − ε_t)(1 − β_t)) (16). h_f errs on i only if ∏_{t=1}^T β_t^{−|h_t(x_i) − y_i|} ≥ (∏_{t=1}^T β_t)^{−1/2} (17), and w_{T+1}^i = D(i) ∏_{t=1}^T β_t^{1 − |h_t(x_i) − y_i|} (18). Combining (17) and (18): Σ_i w_{T+1}^i ≥ Σ_{i: h_f(x_i) ≠ y_i} w_{T+1}^i ≥ ( Σ_{i: h_f(x_i) ≠ y_i} D(i) ) (∏_{t=1}^T β_t)^{1/2} = ε (∏_{t=1}^T β_t)^{1/2} (19). Combining (16) and (19): ε ≤ ∏_{t=1}^T (1 − (1 − ε_t)(1 − β_t)) / √β_t (20). Each positive factor is minimized separately; setting the derivative of the t-th factor to zero gives β_t = ε_t/(1 − ε_t), and substituting into (20) yields (14). □

<a id="pdf-01f49de027c4-p009-b005"></a>
<!-- pdf-source: page=9; block=5; confidence=0.82 -->
**Remark (Eq. 21).** Writing ε_t = 1/2 − γ_t, the Theorem 6 bound can be rewritten as

ε ≤ ∏_{t=1}^T √(1 − 4γ_t²) = exp( −Σ_{t=1}^T KL(1/2 ‖ 1/2 − γ_t) ) ≤ exp( −2 Σ_{t=1}^T γ_t² ),  (21)

using −ln(1 − γ) ≤ γ + γ² for γ ∈ [0, 1/2], where KL denotes relative entropy.

<a id="pdf-01f49de027c4-p010-b001"></a>
<!-- pdf-source: page=10; block=1; confidence=0.85 -->
Continuation of the boosting error analysis. Here `KL(a‖b) = a ln(a/b) + (1−a) ln((1−a)/(1−b))` is the Kullback–Leibler divergence, and in Eq. (21) each error ε_t is replaced by `1/2 − γ_t`. When all weak-hypothesis errors equal `1/2 − γ`, Eq. (21) simplifies to

**Eq. (22):** `ε ≤ (1 − 4γ²)^{T/2} = exp(−T·KL(1/2 ‖ 1/2 − γ)) ≤ exp(−2Tγ²)`.

This is a Chernoff bound on the probability of fewer than T/2 heads in T tosses of a coin with head-probability `1/2 − γ`; same asymptotics as boost-by-majority [11]. The number of iterations sufficient to reach error ε of h_f is

**Eq. (23):** `T = ⌈(1/KL(1/2 ‖ 1/2 − γ)) · ln(1/ε)⌉ ≤ ⌈(1/(2γ²)) · ln(1/ε)⌉`.

<a id="pdf-01f49de027c4-p010-b002"></a>
<!-- pdf-source: page=10; block=2; confidence=0.85 -->
Remark: when WeakLearn's hypotheses have non-uniform errors, Theorem 6 makes the final error depend on the errors of all weak hypotheses, whereas earlier boosting bounds depended only on the maximal (weakest) error; exploiting the more accurate hypotheses is practically relevant.

<a id="pdf-01f49de027c4-p010-b003"></a>
<!-- pdf-source: page=10; block=3; confidence=0.85 -->
**Section 4.3 (Generalization Error).** Theorem 6 bounds the training-set error, but the quantity of interest is the generalization error `ε_g = Pr_{(x,y)~P}[h_f(x) ≠ y]`. To make ε_g close to the empirical error ε̂, restrict h_f by (i) drawing weak hypotheses from a simple function class and (ii) limiting T; T is chosen via a VC-dimension bound (structural risk minimization) or cross-validation.

<a id="pdf-01f49de027c4-p010-b004"></a>
<!-- pdf-source: page=10; block=4; confidence=0.85 -->
Structural risk minimization bounds ε_g using the VC-dimension of the concept class; see Vapnik [23]. The paper quotes Vapnik's Theorem 6.7 (given next as Theorem 7).

<a id="pdf-01f49de027c4-p010-b005"></a>
<!-- pdf-source: page=10; block=5; confidence=0.85 -->
**Theorem 7 (Vapnik).** Let H be a class of binary functions on domain X with VC-dimension d, and P a distribution over X×{0,1}. For h∈H define the generalization error `ε_g(h) = Pr_{(x,y)~P}[h(x) ≠ y]`. For a sample `S = {(x₁,y₁),…,(x_N,y_N)}` of N i.i.d. draws from P, define the empirical error

`ε̂(h) = |{i : h(x_i) ≠ y_i}| / N`.

Then for any δ > 0,

`Pr[ ∃ h∈H : |ε̂(h) − ε_g(h)| > 2·√( (d(ln(2N/d) + 1) + ln(9/δ)) / N ) ] ≤ δ`,

where the probability is over the random choice of S.

<a id="pdf-01f49de027c4-p010-b006"></a>
<!-- pdf-source: page=10; block=6; confidence=0.90 -->
**Definition.** Let `θ: ℝ → {0,1}` be `θ(x) = 1` if `x ≥ 0`, else `0`. For a function class H, let 𝒯_T(H) be all linear-threshold combinations of T functions in H:

`𝒯_T(H) = { θ( Σ_{t=1}^{T} a_t h_t − b ) : b, a₁,…,a_T ∈ ℝ ; h₁,…,h_T ∈ H }`.

If all WeakLearn hypotheses lie in H, then AdaBoost's final hypothesis after T rounds lies in 𝒯_T(H).

<a id="pdf-01f49de027c4-p011-b001"></a>
<!-- pdf-source: page=11; block=1; confidence=0.92 -->
**Theorem 8.** If H is a class of binary functions with VC-dimension `d ≥ 2`, then the VC-dimension of `𝒯_T(H)` is at most `2(d+1)(T+1)·log₂(e(T+1))` (e = base of natural log). Hence AdaBoost's final hypotheses after T iterations lie in a class of VC-dimension at most this bound.

<a id="pdf-01f49de027c4-p011-b002"></a>
<!-- pdf-source: page=11; block=2; confidence=0.88 -->
**Proof.** View the final hypothesis as a two-layer feed-forward network (Baum & Haussler [1]): first-layer units are the weak hypotheses, the second-layer unit is a linear threshold combining them. Linear threshold functions over ℝ^T have VC-dimension `T+1` [26], so the total over all units is `Td + (T+1) < (T+1)(d+1)`. By Baum–Haussler's Theorem 1, the number of functions realizable by h∈𝒯_T(H) on a set of size m is at most `((T+1)·e·m / ((T+1)(d+1)))^{(T+1)(d+1)}`. For `d ≥ 2`, `T ≥ 1`, setting `m = ⌈2(T+1)(d+1)·log₂(e(T+1))⌉` makes this number less than `2^m`, so the VC-dimension of 𝒯_T(H) is smaller than m. ∎

<a id="pdf-01f49de027c4-p011-b003"></a>
<!-- pdf-source: page=11; block=3; confidence=0.85 -->
Using SRM: combine the observed empirical error of h_f^T with Theorems 7 and 8 to bound ε_g for each T, then pick the T minimizing the guaranteed bound. Since the bound may be loose (yielding too-small T), a simple alternative is cross-validation (choose T minimizing error on a held-out validation set; cf. Kearns et al. [17]). Experiments (authors; Drucker & Cortes [8]) indicate AdaBoost tends not to overfit—generalization error often keeps dropping after hundreds of rounds.

<a id="pdf-01f49de027c4-p011-b004"></a>
<!-- pdf-source: page=11; block=4; confidence=0.85 -->
**Section 4.4 (A Bayesian Interpretation).** AdaBoost's final hypothesis is closely related to a Bayes-optimal combination of the hypotheses h₁,…,h_T.

<a id="pdf-01f49de027c4-p011-b005"></a>
<!-- pdf-source: page=11; block=5; confidence=0.87 -->
Given predictions h_t(x), the Bayes-optimal rule predicts 1 iff `Pr[y=1 | h₁(x),…,h_T(x)] > Pr[y=0 | h₁(x),…,h_T(x)]`. Assuming the events `h_t(x) ≠ y` are conditionally independent (of the label and other predictions), Bayes' rule gives: predict 1 iff

`Pr[y=1] · ∏_{t: h_t(x)=0} ε_t · ∏_{t: h_t(x)=1} (1−ε_t) > Pr[y=0] · ∏_{t: h_t(x)=0} (1−ε_t) · ∏_{t: h_t(x)=1} ε_t`,

with `ε_t = Pr[h_t(x) ≠ y]`. Adding a trivial hypothesis h₀ ≡ 1 lets `Pr[y=0]` be replaced by ε₀; taking logarithms and rearranging shows this rule is identical to AdaBoost's combination rule. For dependent errors the exact Bayes rule is complex, but the simple ('naive Bayes') rule is common; AdaBoost is a more principled alternative with guaranteed accuracy (Theorem 6).

<a id="pdf-01f49de027c4-p012-b001"></a>
<!-- pdf-source: page=12; block=1; confidence=0.88 -->
**Section 4.5 (Improving the Error Bound).** The bound of Theorem 6 can be improved by a factor of two by replacing the hard {0,1} decision of h_f with a soft threshold.

<a id="pdf-01f49de027c4-p012-b002"></a>
<!-- pdf-source: page=12; block=2; confidence=0.88 -->
**Definition.** Let

`r(x) = ( Σ_{t=1}^{T} (log 1/β_t) h_t(x) ) / ( Σ_{t=1}^{T} log 1/β_t )`

be a weighted average of the weak hypotheses. Consider final hypotheses `h_f(x) = F(r(x))` with `F: [0,1] → [0,1]`. The Fig. 2 version uses the hard threshold `F(r) = 1` if `r ≥ 1/2`, else 0; here soft thresholds valued in [0,1] are used, so h_f is a randomized hypothesis and `E_{i~D}[|h_f(x_i) − y_i|]` is the error probability.

<a id="pdf-01f49de027c4-p012-b003"></a>
<!-- pdf-source: page=12; block=3; confidence=0.88 -->
**Theorem 9.** Let ε₁,…,ε_T be as in Theorem 6 and r(x_i) as above. Let `h_f(x) = F(r(x))` where F satisfies, for r∈[0,1],

`F(1−r) = 1 − F(r)` and `F(r) ≤ (1/2)·( ∏_{t=1}^{T} β_t )^{1/2 − r}`.

Then the error ε of h_f satisfies

`ε ≤ 2^{T−1} · ∏_{t=1}^{T} √( ε_t (1 − ε_t) )`.

Example: the sigmoid `F(r) = (1 + ∏_{t=1}^{T} β_t^{2r−1})^{−1}` satisfies the conditions.

<a id="pdf-01f49de027c4-p012-b004"></a>
<!-- pdf-source: page=12; block=4; confidence=0.93 -->
**Proof.** By the assumptions on F,

`ε = Σ_i D(i)·|F(r(x_i)) − y_i| = Σ_i D(i)·F(|r(x_i) − y_i|) ≤ (1/2) Σ_i D(i) ∏_{t=1}^{T} β_t^{1/2 − |r(x_i) − y_i|}`.

Since `y_i ∈ {0,1}` and by the definition of r(x_i), this is `≤ (1/2) Σ_i ( D(i) ∏_{t=1}^{T} β_t^{1/2 − |h_t(x_i) − y_i|} ) = (1/2)( Σ_i w_i^{T+1} ) ∏_{t=1}^{T} β_t^{−1/2} ≤ (1/2) ∏_{t=1}^{T} ( (1 − (1−ε_t)(1−β_t)) · β_t^{−1/2} )`, using Eqs. (18) and (16). The result follows from the choice of β_t. ∎

<a id="pdf-01f49de027c4-p012-b005"></a>
<!-- pdf-source: page=12; block=5; confidence=0.82 -->
**Section 5.** Extends AdaBoost beyond binary classification: two multi-class extensions (label set Y = {1,…,k}, final hypothesis h_f: X → Y, error = probability of misprediction) and one regression extension (Y a bounded real interval). The first extension, **AdaBoost.M1**, is the most direct: WeakLearn outputs one of the k labels per instance, and each weak hypothesis must have prediction error < 1/2 on its training distribution; then the combined error decreases exponentially as in the binary case. This 1/2 requirement is strong for k > 2, since random guessing is correct only with probability 1/k < 1/2. An informal example (Y = {0,1,2}, label 2 easy but 0-vs-1 hard) shows this difficulty is unavoidable when only error rate is measured (cf. Schapire [22]).

<a id="pdf-01f49de027c4-p013-b001"></a>
<!-- pdf-source: page=13; block=1; confidence=0.88 -->
Section 5.3 will extend AdaBoost to regression with $Y=[0,1]$, where a hypothesis's error is the expected squared error $E_{(x,y)\sim\mathcal{P}}[(h(x)-y)^2]$. The algorithm AdaBoost.R boosts a weak regression learner using methods like those in AdaBoost.M2.

<a id="pdf-01f49de027c4-p013-b002"></a>
<!-- pdf-source: page=13; block=2; confidence=0.98 -->
## 5.1. First Multi-class Extension

<a id="pdf-01f49de027c4-p013-b003"></a>
<!-- pdf-source: page=13; block=3; confidence=0.90 -->
In the direct multi-class extension AdaBoost.M1 (Fig. 3), on round $t$ the weak learner produces $h_t:X\to Y$ with low classification error $\varepsilon_t=\Pr_{i\sim p_t}[h_t(x_i)\neq y_i]$. It differs from AdaBoost by replacing the binary error $|h_t(x_i)-y_i|$ with the indicator $[\![h_t(x_i)\neq y_i]\!]$ (where $[\![\phi]\!]=1$ if predicate $\phi$ holds, else $0$). The final hypothesis $h_f(x)$ outputs the label $y$ maximizing the summed weights of weak hypotheses predicting $y$.

<a id="pdf-01f49de027c4-p013-b004"></a>
<!-- pdf-source: page=13; block=4; confidence=0.90 -->
For binary classification ($k=2$), a hypothesis $h$ with error much larger than $1/2$ is as useful as one with error much less than $1/2$, since $h$ can be replaced by $1-h$. For $k>2$, however, a hypothesis $h_t$ with error $\varepsilon_t\ge 1/2$ is useless to the boosting algorithm.

<a id="pdf-01f49de027c4-p013-b005"></a>
<!-- pdf-source: page=13; block=5; confidence=0.88 -->
**Algorithm AdaBoost.M1.** Input: $N$ examples $((x_1,y_1),\dots,(x_N,y_N))$ with labels $y_i\in Y=\{1,\dots,k\}$; distribution $D$ over examples; weak learner WeakLearn; iteration count $T$.

Initialize $w^1_i=D(i)$ for $i=1,\dots,N$. For $t=1,\dots,T$:
1. Set $p^t = w^t/\sum_{i=1}^N w^t_i$.
2. Call WeakLearn with $p^t$ to get $h_t:X\to Y$.
3. Compute error $\varepsilon_t=\sum_{i=1}^N p^t_i\,[\![h_t(x_i)\neq y_i]\!]$. If $\varepsilon_t>1/2$, set $T=t-1$ and abort.
4. Set $\beta_t=\varepsilon_t/(1-\varepsilon_t)$.
5. Update weights $w^{t+1}_i = w^t_i\,\beta_t^{\,1-[\![h_t(x_i)\neq y_i]\!]}$.

Output $h_f(x)=\arg\max_{y\in Y}\sum_{t=1}^T (\log\tfrac{1}{\beta_t})\,[\![h_t(x)=y]\!]$.

<a id="pdf-01f49de027c4-p013-b006"></a>
<!-- pdf-source: page=13; block=6; confidence=0.80 -->
A learner guessing may beat pure random guessing yet be infeasible to boost to arbitrary accuracy if 0/1 labels are hard to distinguish (e.g. OCR: telling a '7' from a '9'); AdaBoost.M1 cannot force the weak learner to discriminate particular hard label pairs. The second extension lets the weak learner output a vector in $[0,1]^k$ whose $y$-th component is a "degree of belief" that $y$ is correct, and evaluates it by a pseudo-loss (varying per example and per round, supplied by the boosting algorithm) so the algorithm can focus the learner on the hardest-to-discriminate labels; AdaBoost.M2 (Section 5.2) boosts whenever each weak hypothesis beats random guessing under the supplied pseudo-loss. An alternative standard approach converts the multi-class problem into binary problems, e.g. error-correcting output coding (Dietterich and Bakiri [7]).

<a id="pdf-01f49de027c4-p014-b001"></a>
<!-- pdf-source: page=14; block=1; confidence=0.92 -->
If the weak learner returns such a hypothesis (error $\ge 1/2$), AdaBoost.M1 halts and uses only the weak hypotheses already computed.

<a id="pdf-01f49de027c4-p014-b002"></a>
<!-- pdf-source: page=14; block=2; confidence=0.90 -->
**Theorem 10.** Suppose WeakLearn, called by AdaBoost.M1, generates hypotheses with errors $\varepsilon_1,\dots,\varepsilon_T$ (as defined in Fig. 3), with each $\varepsilon_t\le 1/2$. Then the error $\varepsilon=\Pr_{i\sim D}[h_f(x_i)\neq y_i]$ of the final hypothesis $h_f$ is bounded by
$$\varepsilon \le 2^T\prod_{t=1}^T \sqrt{\varepsilon_t(1-\varepsilon_t)}.$$

<a id="pdf-01f49de027c4-p014-b003"></a>
<!-- pdf-source: page=14; block=3; confidence=0.87 -->
**Proof.** Reduce AdaBoost.M1 to an instance of AdaBoost and apply Theorem 6; reduced-space variables are marked with tildes. For each example $(x_i,y_i)$ define an AdaBoost example $(\tilde x_i,\tilde y_i)$ with $\tilde x_i=i$ and $\tilde y_i=0$, and take $\tilde D=D$. On round $t$, supply AdaBoost with $\tilde h_t(i)=[\![h_t(x_i)\neq y_i]\!]$. By induction on rounds, the weight vectors, distributions, and errors coincide: $\tilde w^t=w^t$, $\tilde p^t=p^t$, $\tilde\varepsilon_t=\varepsilon_t$, $\tilde\beta_t=\beta_t$.

If $h_f(x_i)\neq y_i$, then by definition of $h_f$, $\sum_{t=1}^T \alpha_t[\![h_t(x_i)=y_i]\!] \le \sum_{t=1}^T \alpha_t[\![h_t(x_i)=h_f(x_i)]\!]$ where $\alpha_t=\ln(1/\beta_t)$. Since each $\alpha_t\ge 0$ (because $\varepsilon_t\le 1/2$), this gives $\sum_t \alpha_t[\![h_t(x_i)=y_i]\!]\le \tfrac12\sum_t\alpha_t$, hence by definition of $\tilde h_t$, $\sum_t\alpha_t\tilde h_t(i)\ge \tfrac12\sum_t\alpha_t$, so $\tilde h_f(i)=1$. Therefore $\Pr_{i\sim D}[h_f(x_i)\neq y_i]\le \Pr_{i\sim D}[\tilde h_f(i)=1]$. Since each AdaBoost instance carries a $0$-label, $\Pr_{i\sim D}[\tilde h_f(i)=1]$ is exactly the error of $\tilde h_f$; applying Theorem 6 bounds it, completing the proof. $\square$

<a id="pdf-01f49de027c4-p014-b004"></a>
<!-- pdf-source: page=14; block=4; confidence=0.85 -->
This version can also allow hypotheses that output, for each $x$, a predicted label $h(x)\in Y$ plus a confidence $\kappa(x)\in[0,1]$; the learner then suffers loss $\tfrac12-\tfrac{\kappa(x)}{2}$ when correct and $\tfrac12+\tfrac{\kappa(x)}{2}$ otherwise (details omitted).

<a id="pdf-01f49de027c4-p014-b005"></a>
<!-- pdf-source: page=14; block=5; confidence=0.98 -->
## 5.2. Second Multi-class Extension

<a id="pdf-01f49de027c4-p014-b006"></a>
<!-- pdf-source: page=14; block=6; confidence=0.86 -->
For finite label space $Y$, the weak learner generates hypotheses $h:X\times Y\to[0,1]$, where $h(x,y)$ measures the believed degree that $y$ is the correct label of $x$. If $h(x,y)$ is constant over $y$ for a given $x$, the hypothesis is *uninformative* on $x$; any deviation is potentially informative and useful for boosting. This gives the weak learner flexibility to contribute even when it does not predict the correct label with probability $>1/2$.

<a id="pdf-01f49de027c4-p014-b007"></a>
<!-- pdf-source: page=14; block=7; confidence=0.88 -->
To motivate the pseudo-loss, fix example $(x_i,y_i)$ and use $h$ to answer $k-1$ binary questions, one per incorrect label $y\neq y_i$: "Is the label of $x_i$ equal to $y_i$ or $y$?" Assuming momentarily $h\in\{0,1\}$: if $h(x_i,y)=0$ and $h(x_i,y_i)=1$ the answer is $y_i$; if $h(x_i,y)=1$ and $h(x_i,y_i)=0$ the answer is $y$; if $h(x_i,y)=h(x_i,y_i)$ one of the two answers is chosen uniformly at random.

<a id="pdf-01f49de027c4-p015-b001"></a>
<!-- pdf-source: page=15; block=1; confidence=0.88 -->
For general $h\in[0,1]$, interpret $h(x,y)$ as a randomized decision: draw a bit $b(x,y)$ equal to $1$ with probability $h(x,y)$, then apply the previous procedure to $b$. The probability of the incorrect answer $y$ is
$$\Pr[b(x_i,y_i)=0\wedge b(x_i,y)=1]+\tfrac12\Pr[b(x_i,y_i)=b(x_i,y)]=\tfrac12\big(1-h(x_i,y_i)+h(x_i,y)\big).$$

<a id="pdf-01f49de027c4-p015-b002"></a>
<!-- pdf-source: page=15; block=2; confidence=0.90 -->
**Definition (Eq. 24).** Treating all $k-1$ questions as equally important, define the loss as the average over questions of the incorrect-answer probability:
$$\frac{1}{k-1}\sum_{y\neq y_i}\tfrac12\big(1-h(x_i,y_i)+h(x_i,y)\big)=\tfrac12\Big(1-h(x_i,y_i)+\frac{1}{k-1}\sum_{y\neq y_i}h(x_i,y)\Big).\qquad(24)$$

<a id="pdf-01f49de027c4-p015-b003"></a>
<!-- pdf-source: page=15; block=3; confidence=0.85 -->
Different discrimination questions matter differently by situation (e.g. in OCR, distinguishing a '7' from a '9' can be far more important than the eight other digit questions), motivating per-question weights.

<a id="pdf-01f49de027c4-p015-b004"></a>
<!-- pdf-source: page=15; block=4; confidence=0.93 -->
**Definition (pseudo-loss).** Assign each instance $x_i$ and incorrect label $y\neq y_i$ a weight $q(i,y)$ for the question discriminating $y$ from $y_i$, and replace the average in (24) by the corresponding $q$-weighted average, giving the pseudo-loss of $h$ on instance $i$:
$$\mathrm{ploss}_q(h,i)=\tfrac12\Big(1-h(x_i,y_i)+\sum_{y\neq y_i} q(i,y)\,h(x_i,y)\Big).$$
The label weighting function $q:\{1,\dots,N\}\times Y\to[0,1]$ assigns each example $i$ a probability distribution over the $k-1$ discrimination problems, so that for all $i$, $\sum_{y\neq y_i} q(i,y)=1$.

<a id="pdf-01f49de027c4-p015-b005"></a>
<!-- pdf-source: page=15; block=5; confidence=0.92 -->
**Definition (expected pseudo-loss).** The weak learner's goal is to minimize, for a given distribution $D$ and weighting $q$,
$$\mathrm{ploss}_{D,q}(h):=E_{i\sim D}[\mathrm{ploss}_q(h,i)].$$

<a id="pdf-01f49de027c4-p015-b006"></a>
<!-- pdf-source: page=15; block=6; confidence=0.85 -->
Varying both the instance distribution $D$ and the label weighting $q$ forces the weak learner to focus on hard instances and on the incorrect labels hardest to eliminate; conversely this measure can make it easier to gain a weak advantage (e.g. merely ruling out one class for an instance may suffice depending on $q$).

<a id="pdf-01f49de027c4-p015-b007"></a>
<!-- pdf-source: page=15; block=7; confidence=0.86 -->
**Theorem 11.** A weak learner can be boosted if it consistently produces weak hypotheses with pseudo-loss smaller than $1/2$. Remarks: pseudo-loss $1/2$ is achieved trivially by any uninformative hypothesis; a weak hypothesis $h$ with pseudo-loss $\varepsilon>1/2$ is also beneficial, since it can be replaced by $1-h$, whose pseudo-loss is $1-\varepsilon<1/2$.

<a id="pdf-01f49de027c4-p015-b008"></a>
<!-- pdf-source: page=15; block=8; confidence=0.90 -->
**Example 5.** Seek an *oblivious* weak hypothesis, whose value depends only on the label: $h(x,y)=h(y)$. For convenience set $q(i,y_i)=-1$ for all $i$, so
$$\mathrm{ploss}_q(h,i)=\tfrac12\Big(1+\sum_{y\in Y} q(i,y)\,h(x_i,y)\Big).$$
Setting $\delta(y)=\sum_i D(i)\,q(i,y)$, for an oblivious $h$,
$$\mathrm{ploss}_{D,q}(h)=\tfrac12\Big(1+\sum_{y\in Y} h(y)\,\delta(y)\Big),$$
which is minimized by $h(y)=1$ if $\delta(y)<0$ and $h(y)=0$ otherwise. The example then specializes to $q(i,y)=1/(k-1)$ for $y\neq y_i$, with $d(y)=\Pr_{i\sim D}[y_i=y]$ the proportion of examples with label $y$ (continues beyond page 15).

<a id="pdf-01f49de027c4-p016-b001"></a>
<!-- pdf-source: page=16; block=1; confidence=0.92 -->
**Algorithm AdaBoost.M2.** Input: $N$ examples $(x_i,y_i)$ with labels $y_i\in Y=\{1,\dots,k\}$, distribution $D$, weak learner WeakLearn, iteration count $T$. Initialize $w^1_{i,y}=D(i)/(k-1)$ for $i=1,\dots,N$, $y\in Y-\{y_i\}$. For $t=1,\dots,T$:
1. $W^t_i=\sum_{y\ne y_i} w^t_{i,y}$; $q_t(i,y)=w^t_{i,y}/W^t_i$ for $y\ne y_i$; $D_t(i)=W^t_i/\sum_{i=1}^N W^t_i$.
2. Call WeakLearn with distribution $D_t$ and label-weight function $q_t$; obtain $h_t:X\times Y\to[0,1]$.
3. Pseudo-loss $\varepsilon_t=\tfrac12\sum_{i=1}^N D_t(i)\big(1-h_t(x_i,y_i)+\sum_{y\ne y_i} q_t(i,y)\,h_t(x_i,y)\big)$.
4. $\beta_t=\varepsilon_t/(1-\varepsilon_t)$.
5. $w^{t+1}_{i,y}=w^t_{i,y}\,\beta_t^{\,\frac12(1+h_t(x_i,y_i)-h_t(x_i,y))}$ for $i=1,\dots,N$, $y\in Y-\{y_i\}$.
Output $h_f(x)=\arg\max_{y\in Y}\sum_{t=1}^T \big(\log\tfrac1{\beta_t}\big)h_t(x,y)$.

<a id="pdf-01f49de027c4-p016-b002"></a>
<!-- pdf-source: page=16; block=2; confidence=0.95 -->
**Reduction.** For each instance $(x_i,y_i)$ and incorrect label $y\in Y-\{y_i\}$, define an AdaBoost instance $\tilde x_{i,y}=(i,y)$ with label $\tilde y_{i,y}=0$; there are $\tilde N=N(k-1)$ instances indexed by $(i,y)$, with distribution $\tilde D(i,y)=D(i)/(k-1)$. The $t$-th reduced hypothesis is $\tilde h_t(i,y)=\tfrac12(1-h_t(x_i,y_i)+h_t(x_i,y))$. With this setup the distributions and errors coincide: $\tilde w^t_{i,y}=w^t_{i,y}$, $\tilde p^t_{i,y}=p^t_{i,y}$, $\tilde\varepsilon_t=\varepsilon_t$, $\tilde\beta_t=\beta_t$.

<a id="pdf-01f49de027c4-p016-b003"></a>
<!-- pdf-source: page=16; block=3; confidence=0.90 -->
Pseudo-loss can be made $<1/2$ except under a uniform label distribution ($d(y)=1/k$ for all $y$), whereas an oblivious hypothesis attains prediction error $<1/2$ only when some label covers more than half the distribution ($d(y)>1/2$); hence small pseudo-loss is much easier to achieve than small prediction error.

<a id="pdf-01f49de027c4-p016-b004"></a>
<!-- pdf-source: page=16; block=4; confidence=0.85 -->
If $q(i,y)=0$ for all but one incorrect label per instance, pseudo-loss $<1/2$ requires predicting the correct label with probability $>1/2$, making pseudo-loss as stringent as prediction error; this case is unavoidable since a hard binary problem embeds in a multi-class one. The prediction-error bound (Theorem 10) is stronger than the pseudo-loss bound (Theorem 11); empirically pseudo-loss helps most with restricted weak learners and little for powerful ones such as decision trees.

<a id="pdf-01f49de027c4-p016-b005"></a>
<!-- pdf-source: page=16; block=5; confidence=0.90 -->
AdaBoost.M2 maintains weights $w^t_{i,y}$ per instance $i$ and label $y\ne y_i$; from $w^t$ it computes distribution $D_t$ and label-weight function $q_t$ (Step 1) given to the weak learner, whose goal is to minimize pseudo-loss $\varepsilon_t$ (Step 3); weights update at Step 5, and $h_f$ outputs the label maximizing a weighted average of the $h_t(x,y)$.

<a id="pdf-01f49de027c4-p016-b006"></a>
<!-- pdf-source: page=16; block=6; confidence=0.90 -->
**Theorem 11.** If WeakLearn, called by AdaBoost.M2, produces hypotheses with pseudo-losses $\varepsilon_1,\dots,\varepsilon_T$ (as in Fig. 4), then the error $\varepsilon=\Pr_{i\sim D}[h_f(x_i)\ne y_i]$ of the final hypothesis $h_f$ satisfies $\varepsilon\le (k-1)\,2^T\prod_{t=1}^T\sqrt{\varepsilon_t(1-\varepsilon_t)}$.

<a id="pdf-01f49de027c4-p016-b007"></a>
<!-- pdf-source: page=16; block=7; confidence=0.85 -->
**Proof.** As in the proof of Theorem 10, reduce to an instance of AdaBoost and apply Theorem 6, marking AdaBoost variables with a tilde. (Continues on next page.)

<a id="pdf-01f49de027c4-p017-b001"></a>
<!-- pdf-source: page=17; block=1; confidence=0.95 -->
**Proof (cont.).** If $h_f(x_i)\ne y_i$ then by definition of $h_f$, $\sum_{t=1}^T\alpha_t h_t(x_i,y_i)\le\sum_{t=1}^T\alpha_t h_t(x_i,h_f(x_i))$ with $\alpha_t=\ln(1/\beta_t)$. Hence $\sum_t\alpha_t\tilde h_t(i,h_f(x_i))=\tfrac12\sum_t\alpha_t(1-h_t(x_i,y_i)+h_t(x_i,h_f(x_i)))\ge\tfrac12\sum_t\alpha_t$, so $\tilde h_f(i,h_f(x_i))=1$. Therefore $\Pr_{i\sim D}[h_f(x_i)\ne y_i]\le\Pr_{i\sim D}[\exists y\ne y_i:\tilde h_f(i,y)=1]$. Since all AdaBoost instances have label $0$, $\Pr_{(i,y)\sim\tilde D}[\tilde h_f(i,y)=1]\ge\tfrac1{k-1}\Pr_{i\sim D}[\exists y\ne y_i:\tilde h_f(i,y)=1]$. Bounding the error of $\tilde h_f$ via Theorem 6 completes the proof. $\square$

<a id="pdf-01f49de027c4-p017-b002"></a>
<!-- pdf-source: page=17; block=2; confidence=0.88 -->
The AdaBoost.M2 bound can be improved by a factor of two, analogously to Section 4.5 (details omitted).

<a id="pdf-01f49de027c4-p017-b003"></a>
<!-- pdf-source: page=17; block=3; confidence=0.85 -->
**Section 5.3 — Boosting Regression Algorithms.** For regression the label space is $Y=[0,1]$; examples $(x,y)\sim P$ and the learner seeks $h:X\to Y$ minimizing mean squared error $E_{(x,y)\sim P}[(h(x)-y)^2]$ (25). The approach applies to any bounded error measure but focuses on squared error. Given a training set $(x_1,y_1),\dots,(x_N,y_N)\sim P$, minimize the empirical MSE $\tfrac1N\sum_{i=1}^N(h(x_i)-y_i)^2$; by techniques as in Section 4.3 the true MSE (25) is related to the empirical MSE.

<a id="pdf-01f49de027c4-p017-b004"></a>
<!-- pdf-source: page=17; block=4; confidence=0.83 -->
**Reduction.** Reduce regression to binary classification, then apply AdaBoost (reduced-space variables marked with tildes). For each $(x_i,y_i)$ define a continuum of examples indexed by $(i,y)$, $y\in[0,1]$: instance $\tilde x_{i,y}=(x_i,y)$, label $\tilde y_{i,y}=[\![\,y\ge y_i\,]\!]$ (with $[\![\pi]\!]=1$ if $\pi$ holds, else $0$). Each hypothesis $h:X\to Y$ reduces to $\tilde h:X\times Y\to\{0,1\}$, $\tilde h(x,y)=[\![\,y\ge h(x)\,]\!]$, answering “is $y_i$ larger or smaller than $y$?” Extension to infinite training sets is straightforward.

<a id="pdf-01f49de027c4-p017-b005"></a>
<!-- pdf-source: page=17; block=5; confidence=0.88 -->
**Definition.** Given distribution $D$ (usually uniform, $D(i)=1/N$), define the reduced density $\tilde D(i,y)=D(i)\,|y-y_i|/Z$ with $Z=\sum_{i=1}^N D(i)\int_0^1|y-y_i|\,dy$, so that minimizing classification error in the reduced space minimizes MSE. One shows $1/4\le Z\le 1/2$.

<a id="pdf-01f49de027c4-p018-b001"></a>
<!-- pdf-source: page=18; block=1; confidence=0.90 -->
**Algorithm AdaBoost.R.** Input: $N$ examples $(x_i,y_i)$ with $y_i\in Y=[0,1]$, distribution $D$, WeakLearn, iterations $T$. Initialize $w^1_{i,y}=D(i)\,|y-y_i|/Z$ for $i=1,\dots,N$, $y\in Y$, where $Z=\sum_{i=1}^N D(i)\int_0^1|y-y_i|\,dy$. For $t=1,\dots,T$:
1. $p_t=w^t\big/\big(\sum_{i=1}^N\int_0^1 w^t_{i,y}\,dy\big)$.
2. Call WeakLearn with density $p_t$; obtain $h_t:X\to Y$.
3. Loss $\varepsilon_t=\sum_{i=1}^N\big|\int_{y_i}^{h_t(x_i)} p^t_{i,y}\,dy\big|$. If $\varepsilon_t>1/2$, set $T=t-1$ and abort the loop.
4. $\beta_t=\varepsilon_t/(1-\varepsilon_t)$.
5. $w^{t+1}_{i,y}=w^t_{i,y}$ if $y_i\le y\le h_t(x_i)$ or $h_t(x_i)\le y\le y_i$, else $w^{t+1}_{i,y}=w^t_{i,y}\,\beta_t$, for $i=1,\dots,N$, $y\in Y$.
Output $h_f(x)=\inf\{\,y\in Y:\sum_{t:\,h_t(x)\le y}\log(1/\beta_t)\ge\tfrac12\sum_t\log(1/\beta_t)\,\}$.

<a id="pdf-01f49de027c4-p018-b002"></a>
<!-- pdf-source: page=18; block=2; confidence=0.87 -->
**Derivation.** The binary error of $\tilde h$ under density $\tilde D$ is proportional to MSE: $\sum_{i=1}^N\int_0^1|\tilde y_{i,y}-\tilde h(\tilde x_{i,y})|\,\tilde D(i,y)\,dy=\tfrac1Z\sum_{i=1}^N D(i)\big|\int_{y_i}^{h(x_i)}|y-y_i|\,dy\big|=\tfrac1{2Z}\sum_{i=1}^N D(i)(h(x_i)-y_i)^2$, with proportionality constant $1/(2Z)\in[1,2]$.

<a id="pdf-01f49de027c4-p018-b003"></a>
<!-- pdf-source: page=18; block=3; confidence=0.90 -->
Unravelling the reduction gives AdaBoost.R (Fig. 5): it keeps weight $w^t_{i,y}$ per instance $i$ and label $y\in Y$; $w^1$ equals the density $\tilde D$; normalizing the weights gives density $p_t$ (Step 1) passed to the weak learner (Step 2), whose goal is a hypothesis $h_t:X\to Y$ minimizing the loss $\varepsilon_t$ (Step 3); weights update at Step 5.

<a id="pdf-01f49de027c4-p018-b004"></a>
<!-- pdf-source: page=18; block=4; confidence=0.88 -->
The Step-3 loss $\varepsilon_t$ follows from the reduction and equals the classification error of $\tilde h_f$ in the reduced space. Like AdaBoost.M2, AdaBoost.R varies both the example distribution and the per-round loss definition, so the weak learner must handle losses more complicated than MSE.

<a id="pdf-01f49de027c4-p018-b005"></a>
<!-- pdf-source: page=18; block=5; confidence=0.88 -->
Each reduced weak hypothesis $\tilde h_f(x,y)$ is non-decreasing in $y$, so the threshold of their weighted sum $\tilde h_f$ is also non-decreasing in $y$: for each $x$ there is a single $y$ with $\tilde h_f(x,y')=0$ for $y'<y$ and $=1$ for $y'>y$, which is exactly $h_f(x)$. Thus $h_f$ computes a weighted median of the weak hypotheses.

<a id="pdf-01f49de027c4-p018-b006"></a>
<!-- pdf-source: page=18; block=6; confidence=0.88 -->
Although $w^t_{i,y}$ is defined over an uncountable set, as a function of $y$ it is piecewise linear: $w^1_{i,y}$ has two linear pieces, and each Step-5 update may split one piece in two at $h_t(x_i)$. Initializing, storing, and updating these piecewise-linear functions, and evaluating the integrals, are all straightforward.

<a id="pdf-01f49de027c4-p018-b007"></a>
<!-- pdf-source: page=18; block=7; confidence=0.90 -->
**Theorem 12.** If WeakLearn, called by AdaBoost.R, generates hypotheses with errors $\varepsilon_1,\dots,\varepsilon_T$ (as in Fig. 5), then the mean squared error $\varepsilon=E_{i\sim D}[(h_f(x_i)-y_i)^2]$ of the final hypothesis is bounded above by … [statement continues beyond the supplied page]. The performance guarantee follows from the reduction above coupled with a direct application of Theorem 6.

<a id="pdf-01f49de027c4-p019-b001"></a>
<!-- pdf-source: page=19; block=1; confidence=0.93 -->
**Bound (eq. 26).** The loss of the final hypothesis $h_f$ produced by AdaBoost.R satisfies $\varepsilon \le 2^T \prod_{t=1}^{T} \sqrt{\varepsilon_t(1-\varepsilon_t)}$. Noted drawback: no trivial hypothesis achieves loss $1/2$ (as with AdaBoost.M1).

<a id="pdf-01f49de027c4-p019-b002"></a>
<!-- pdf-source: page=19; block=2; confidence=0.82 -->
**Definition (reduced hypothesis).** Allow weak hypotheses given by $h:X\to[0,1]$ plus a confidence function $\kappa:X\to[0,1]$. The associated reduced hypothesis is $\tilde h(x,y)=(1+\kappa(x))/2$ if $h(x)=y$, and $(1-\kappa(x))/2$ otherwise. A variant of AdaBoost.R boosts such learners (details omitted); when $\kappa(x)\equiv 0$ the pseudo-loss is exactly $1/2$.

<a id="pdf-01f49de027c4-p019-b003"></a>
<!-- pdf-source: page=19; block=3; confidence=0.82 -->
The square-loss boosting method extends to any bounded loss $L:Y\times Y\to[0,1]$ with $L(y,y)=0$, $L$ differentiable in its first argument, non-increasing for $y'\le y$ and non-decreasing for $y'\ge y$. To adapt AdaBoost.R, replace $|y-y_i|$ in initialization with $|\partial L(y,y_i)/\partial y|$; the rest is unchanged.

<a id="pdf-01f49de027c4-p019-b004"></a>
<!-- pdf-source: page=19; block=4; confidence=0.90 -->
**Appendix: Proof of Theorem 3.** Reviews Vovk's on-line decision framework [24], similar to the Section 3 framework.

<a id="pdf-01f49de027c4-p019-b005"></a>
<!-- pdf-source: page=19; block=5; confidence=0.85 -->
**Definition (decision problem).** A decision space $\Theta$, outcome space $\Omega$, and loss $\lambda:\Theta\times\Omega\to[0,\infty]$. At trial $t$ the algorithm receives the $N$ experts' decisions $\xi^t_1,\dots,\xi^t_N\in\Theta$, then outputs its own decision $\gamma_t\in\Theta$; on outcome $\omega_t\in\Omega$ the learner incurs $\lambda(\gamma_t,\omega_t)$ and each expert $i$ incurs $\lambda(\xi^t_i,\omega_t)$. Goal: keep cumulative loss close to that of the best expert.

<a id="pdf-01f49de027c4-p019-b006"></a>
<!-- pdf-source: page=19; block=6; confidence=0.88 -->
**Assumptions.** (1) $\Theta$ is a compact topological space. (2) For each $\omega$, $\gamma\mapsto\lambda(\gamma,\omega)$ is continuous. (3) There exists $\gamma$ with $\lambda(\gamma,\omega)<\infty$ for all $\omega$. (4) There exists no $\gamma$ with $\lambda(\gamma,\omega)=0$ for all $\omega$.

<a id="pdf-01f49de027c4-p019-b007"></a>
<!-- pdf-source: page=19; block=7; confidence=0.83 -->
**Definition ((c,a)-bounded).** For positive reals $c,a$, a decision problem (obeying Assumptions 1–4) is $(c,a)$-bounded if some algorithm $A$ achieves, for any finite expert set and trial sequence, $\sum_{t=1}^T \lambda(\gamma_t,\omega_t)\le c\,\min_i \sum_{t=1}^T \lambda(\xi^t_i,\omega_t)+a\ln N$, with $N$ the number of experts. A distribution $D$ is *simple* if nonzero on a finite set $\mathrm{dom}(D)$; $S$ is the set of simple distributions over $\Theta$. Vovk's hardness function $c:(0,1)\to[0,\infty]$ is $c(\beta)=\sup_{D\in S}\ \inf_{\gamma\in\Theta}\ \sup_{\omega\in\Omega} \dfrac{\lambda(\gamma,\omega)}{\log_\beta \sum_{\xi\in\mathrm{dom}(D)}\beta^{\lambda(\xi,\omega)}D(\xi)}$. (27)

<a id="pdf-01f49de027c4-p019-b008"></a>
<!-- pdf-source: page=19; block=8; confidence=0.86 -->
**Theorem 13 (Vovk).** A decision problem is $(c,a)$-bounded if and only if for all $\beta\in(0,1)$, $c\ge c(\beta)$ or $a\ge c(\beta)/\ln(1/\beta)$.

<a id="pdf-01f49de027c4-p019-b009"></a>
<!-- pdf-source: page=19; block=9; confidence=0.85 -->
**Proof of Theorem 3.** Three steps: (i) define a decision problem in Vovk's framework; (ii) lower-bound $c(\beta)$ for it; (iii) reduce the on-line allocation problem to it, deriving via Theorem 13 a lower bound on the worst-case cumulative loss of any allocation algorithm $A$. Construction: fix integer $K>1$; set $\Theta=S_K$, the $K$-dimensional simplex $S_K=\{x\in[0,1]^K:\sum_{i=1}^K x_i=1\}$; set $\Omega=\{e_1,\dots,e_K\}$, the unit vectors in $\mathbb{R}^K$; define loss $\lambda(\gamma,e_i)=\gamma\cdot e_i=\gamma_i$. These satisfy Assumptions 1–4.

<a id="pdf-01f49de027c4-p020-b001"></a>
<!-- pdf-source: page=20; block=1; confidence=0.84 -->
**Proof (cont.).** Choose $D$ uniform over $\mathrm{dom}(D)=\{e_1,\dots,e_K\}$, giving $c(\beta)\ge \inf_{\gamma\in\Theta}\sup_{\omega\in\Omega}\dfrac{\lambda(\gamma,\omega)}{\log_\beta \sum_{\xi\in\mathrm{dom}(D)}\beta^{\lambda(\xi,\omega)}D(\xi)}$ (28). The denominator's inner sum is constant: $\sum_{\xi\in\mathrm{dom}(D)}\beta^{\lambda(\xi,\omega)}D(\xi)=\dfrac{\beta}{K}+\dfrac{K-1}{K}$ (29).

<a id="pdf-01f49de027c4-p020-b002"></a>
<!-- pdf-source: page=20; block=2; confidence=0.83 -->
**Proof (cont.).** Every probability vector $\gamma\in\Theta$ has some component $\gamma_i\le 1/K$, so $\inf_{\gamma\in\Theta}\sup_{\omega\in\Omega}\lambda(\gamma,\omega)=1/K$ (30). Combining (28), (29), (30): $c(\beta)\ge \dfrac{\ln(1/\beta)}{K\,\ln\!\big(1-(1-\beta)/K\big)}$ (31).

<a id="pdf-01f49de027c4-p020-b003"></a>
<!-- pdf-source: page=20; block=3; confidence=0.85 -->
**Proof (cont.).** Match each of the $N$ experts to an allocation strategy. Each iteration $t$: (1) each expert generates $\xi^t_i\in S_K$; (2) algorithm $A$ generates distribution $p_t\in S_N$; (3) learner chooses $\gamma_t=\sum_{i=1}^N p^t_i\,\xi^t_i$; (4) outcome $\omega_t\in\Omega$ is generated; (5) learner incurs $\gamma_t\cdot\omega_t$, expert $i$ incurs $\xi^t_i\cdot\omega_t$; (6) $A$ receives loss vector $l_t$ with $l^t_i=\xi^t_i\cdot\omega_t$ and incurs $p_t\cdot l_t=\sum_{i=1}^N p^t_i(\xi^t_i\cdot\omega_t)=\big(\sum_{i=1}^N p^t_i\xi^t_i\big)\cdot\omega_t=\gamma_t\cdot\omega_t$. Thus the learner's loss equals $A$'s loss.

<a id="pdf-01f49de027c4-p020-b004"></a>
<!-- pdf-source: page=20; block=4; confidence=0.82 -->
**Proof (concl.).** If $A$ satisfies $L_A\le c\,\min_i L_i+a\ln N$, the decision problem is $(c,a)$-bounded. Conversely, Theorem 13 with the bound (31) gives, for every $K$ and $\beta$: $c\ge \dfrac{\ln(1/\beta)}{K\,\ln(1-(1-\beta)/K)}$ or $a\ge \dfrac{1}{K\,\ln(1-(1-\beta)/K)}$ (32). Letting $K\to\infty$ (free parameter), the denominators in Eq. (22) tend to $1-\beta$, yielding the statement of the theorem. $\blacksquare$

<a id="pdf-01f49de027c4-p020-b005"></a>
<!-- pdf-source: page=20; block=5; confidence=0.90 -->
Acknowledgments thanking C. Cortes, H. Drucker, D. Helmbold, K. Messer, V. Vovk, and M. Warmuth. (No mathematical content.)

<a id="pdf-01f49de027c4-p020-b006"></a>
<!-- pdf-source: page=20; block=6; confidence=0.85 -->
Bibliography entries 1–13 (Baum–Haussler; Blackwell; Breiman; Cesa-Bianchi et al.; Chung; Cover; Dietterich–Bakiri; Drucker–Cortes; Drucker–Schapire–Simard; Freund; Freund–Schapire). No mathematical content.

<a id="pdf-01f49de027c4-p021-b001"></a>
<!-- pdf-source: page=21; block=1; confidence=0.85 -->
Bibliography entries 14–26 (Hannan; Haussler–Kivinen–Warmuth; Jackson–Craven; Kearns et al.; Kearns–Vazirani; Kivinen–Warmuth; Littlestone–Warmuth; Quinlan; Schapire; Vapnik; Vovk [24], [25]; Wenocur–Dudley). No mathematical content.
