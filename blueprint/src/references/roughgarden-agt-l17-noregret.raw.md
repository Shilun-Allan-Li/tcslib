<!-- generated-by: proofmatch local extraction -->
<!-- source-pdf-sha256: eda737ce3103cdfc7845f80b3d2b80c68ff0241728cebdf1f85f663516194d1d -->
<!-- extractor: pdfminer.six v20260107 -->

<!-- pdf-page: 1 -->
CS364A: Algorithmic Game Theory
Lecture #17: No-Regret Dynamics∗

Tim Roughgarden†

November 18, 2013

This lecture continues to study the questions introduced last time. Do strategic players
reach an equilibrium of a game? How quickly? By what learning processes? Positive results
on these questions justify equilibrium analysis, including bounds on the price of anarchy.

Last lecture focused on best-response dynamics. These dynamics are most relevant for
potential games, which cover many but not all interesting applications. This lecture, we
study a second fundamental class of learning dynamics — no-regret dynamics. An attractive
feature of these dynamics is their rapid convergence to an approximate equilibrium — a
coarse correlated equilibrium (Lecture 13), not generally a Nash equilibrium — in arbitrary
games.

1 External Regret

1.1 The Model

Most of the this lecture studies the regret-minimization problem, which concerns a single
decision-maker playing a game against an adversary. Section 3 connects this single-player
theory to multi-player games and their coarse correlated equilibria.
Consider a set A of n ≥ 2 actions. The setup is as follows.

• At time t = 1, 2, . . . , T :

– A decision-maker picks a mixed strategy pt — that is, a probability distribution

— over its actions A.

– An adversary picks a cost vector ct : A → [0, 1].1

∗ c(cid:13)2013, Tim Roughgarden. These lecture notes are provided for personal use only. See my book Twenty

Lectures on Algorithmic Game Theory, published by Cambridge University Press, for the latest version.

†Department of Computer Science, Stanford University, 462 Gates Building, 353 Serra Mall, Stanford,

CA 94305. Email: tim@cs.stanford.edu.

1The important assumption is that costs are bounded. See the Exercises for extensions of today’s results

to negative costs (i.e., payoﬀs) and to costs in [0, cmax] instead of in [0, 1].

1



<!-- pdf-page: 2 -->
– An action at is chosen according to the distribution pt, and the decision-maker
incurs cost ct(at). The decision-maker learns the entire cost vector ct, not just the
realized cost ct(at).2

For example, A could represent diﬀerent investment strategies, or diﬀerent driving routes
between home and work. When we return to multi-player games (Section 3), the action
set will be the strategy set of a single player, and the cost vector will be induced by the
strategies chosen by all of the other players.

1.2 Lower Bounds

We seek a “good” algorithm for online decision-making problems of the above type. But the
setup above seems a bit unfair, no? The adversary is allowed to choose a cost function after
the decision-maker has committed to a mixed strategy. This asymmetry motivates asking
what kind of guarantee we could possibly hope for in such a model. We next consider three
examples that show limitations on what is possible.

Example 1.1 (Impossibility w.r.t. the Best Action Sequence) There is no hope of
comparing the cost of an online decision-making algorithm to the cost of the best action
sequence in hindsight — the latter quantity (cid:80)T
t=1 mina∈A ct(a) is simply too strong a bench-
mark.

For instance, suppose A = 2 and ﬁx an arbitrary online decision-making algorithm. Each
if the algorithm plays the ﬁrst
2 then ct is (1 0); otherwise the cost vector is (0 1). The
2 while ensuring that

day t, the adversary chooses the cost vector ct as follows:
strategy with probability at least 1
adversary has forced the expected cost of the algorithm to be at least T
the cost of the best action sequence in hindsight is 0.

Example 1.1 motivates the following important deﬁnitions. Rather than comparing the
expected cost of an algorithm to that of the best action sequence in hindsight, we compare
it to the cost incurred by the best ﬁxed action in hindsight. That is, our benchmark will be
mina∈A

t=1 ct(a) rather than (cid:80)T

t=1 mina∈A ct(a).

(cid:80)T

Deﬁnition 1.2 The (time-averaged) regret of the action sequence a1, . . . .aT with respect to
the action a is

(cid:34) T

(cid:88)

1
T

t=1

i=1

T
(cid:88)

(cid:35)

ct(at) −

ct(a)

.

(1)

In this lecture, “regret” will always refer to Deﬁnition 1.2. Next lecture we discuss another
notion of regret.

Deﬁnition 1.3 (No-Regret Algorithm) Let A be an online decision-making algorithm.

2The bandit model, where the decision-maker only learns the realized cost, has also been studied exten-
sively (e.g. [2]). The guarantees presented in this lecture carry over, with somewhat worse bounds and more
complex algorithms, to the bandit model as well.

2



<!-- pdf-page: 3 -->
(a) An adversary for A is a function that takes as input the day t, the mixed strategies
p1, . . . , pt produced by A on the ﬁrst t days, and the realized actions a1, . . . , at−1 of the
ﬁrst t − 1 days, and produces as output a cost vector ct : [0, 1] → A.

(b) An online decision-making algorithm has no (external) regret if for every adversary for
it, the expected regret (1) with respect to every action a ∈ A is o(1) as T → ∞.

Remark 1.4 (Combining Expert Advice) The problem of designing a no-regret algo-
rithm is sometimes called “combining expert advice” — if we think of each action an “ex-
pert” that makes recommendations, then a no-regret algorithms performs asymptotically as
well as the best expert.

Remark 1.5 (Adaptive vs. Oblivious Adversaries) The adversary in Deﬁnition 1.3 is
sometimes called an adaptive adversary. An oblivious adversary is the special case in which
the cost vector ct depends only on t (and on the algorithm A).

For this lecture, we’ll adopt the no-regret guarantee of Deﬁnition 1.3 as the “holy grail”
in the design of online decision-making algorithms. The ﬁrst reason is that, as we’ll see in
Section 2, this goal can be achieved by simple and natural learning algorithms. The second
reason is that the goal is non-trivial: as the examples below make clear, some ingenuity
is required to achieve it. The third reason is that, when we pass to multi-player games
in Section 3, no-regret guarantees will translate directly to coarse correlated equilibrium
conditions.

Remark 1.6 In regret-minimization, one usually thinks of the number n of actions as ﬁxed
as the time horizon T tends to inﬁnity. In a no-regret algorithm, the (time-averaged) regret
can be a function of n but tends to 0 as the time horizon grows.

The next example rules out deterministic no-regret algorithms.

Example 1.7 (Randomization Is Necessary for No Regret) A simple consequence of
the asymmetry between the decision-maker and the adversary is that there does not exist
a no-regret deterministic algorithm. To see this, suppose there are n ≥ 2 actions and ﬁx a
deterministic algorithm. At each time step t, the algorithm commits to a single action at.
The obvious strategy for the adversary is to set the cost of action at to be 1, and the cost of
every other action to be 0. Then, the cost of the algorithm is T while the cost of the best
action in hindsight is at most T
n . Thus, even when there are only 2 actions, the algorithm
has constant regret (as T → ∞) with respect to some action a.

The next example does not rule out (randomized) no-regret algorithms, though it does

limit the rate at which regret can vanish as the time horizon T grows.
Example 1.8 (Ω((cid:112)(ln n)/T ) Regret Lower Bound) The next example shows that, even
with only n = 2 actions, no (randomized) algorithm has expected regret vanishing faster than
T ). A similar argument shows that, with n actions, expected regret cannot
the rate Θ(1/
vanish faster than Θ((cid:112)(ln n)/T ).

√

3



<!-- pdf-page: 4 -->
Consider an adversary that, independently on each day T , chooses uniformly at random
between the cost vectors (1 0) and (0 1). No matter how smart or dumb an online decision-
making algorithm is, its cumulative expected cost is exactly T
2 . In hindsight, however, with
constant probability one of the two ﬁxed actions has cumulative cost only T
T ). The
2 − Θ(
reason is that if you ﬂip T fair coins, while the expected number of heads is T
2 , the standard
T ). This implies that there is a distribution over 2T (oblivious) adversaries
deviation is Θ(
√
such that every algorithm has expected regret Ω(1/
T ), where the expectation is over the
algorithm’s coin ﬂips and the choice of the adversary. It follows that for every algorithm,
T ).
there exists an (oblivious) adversary for which the algorithm has expected regret Ω(1/

√

√

√

2 The Multiplicative Weights Algorithm

2.1 No-Regret Algorithms Exist

The most important result in this lecture is that no-regret algorithms exist. Next lecture
we’ll see that this fact alone has some amazing consequences. Even better, there are simple
and natural such algorithms — while not a literal description of human player behavior, the
guiding principles of the following algorithm are recognizable from the way many people learn
and make decisions. Finally, the algorithm we discuss next has optimal regret, matching the
lower bound provided by Example 1.8.

Theorem 2.1 ([3, 4], etc.) There exist simple no-regret algorithms with expected regret
O((cid:112)(ln n)/T ) with respect to every ﬁxed action.

An immediately corollary is that a logarithmic (in n) number of iterations suﬃce to drive

the expected regret down to a small constant.

Corollary 2.2 There exists an online decision-making algorithm that, for every (cid:15) > 0, has
expected regret at most (cid:15) with respect to every ﬁxed action after O((ln n)/(cid:15)2) iterations.

2.2 The Algorithm

We next discuss the multiplicative weights (MW) algorithm, which is also sometimes called
Randomized Weighted Majority or Hedge. This algorithm has numerous applications beyond
online decision-making [1]. Its design follows two guiding principles.

1. Past performance of actions should guide which action is chosen now. Since the action
choice must be randomized (Example 1.7), the probability of choosing an action should
be increasing in its past performance (i.e., decreasing in its cumulative cost).

2. Many instantiations of the above idea yield no-regret algorithms. For optimal regret
bounds, however, it is important to aggressively punish bad actions — when a previ-
ously good action turns sour, the probability with which it is played should decrease
at an exponential rate.

4



<!-- pdf-page: 5 -->
Here is a formal description of the MW algorithm.

It maintains a weight, intuitively
a “credibility,” for each action. At each time step the algorithm chooses an action with
probability proportional to its current weight. The weight of each action can only decrease,
and the rate of decrease depends on the cost of the action.

1. Initialize w1(a) = 1 for every a ∈ A.

2. For t = 1, 2, . . . , T :

(a) Play an action according to the distribution pt := wt/Γt, where Γt = (cid:80)

is the sum of the weights.

a∈A wt(a)

(b) Given the cost vector ct, decrease weights using the formula wt+1(a) = wt(a) · (1 −

(cid:15))ct(a) for every action a ∈ A.3

For example, if all costs are either 0 or 1, then the weight of each action either stays the
same (if ct(a) = 0) or gets multiplied by (1 − (cid:15)) (if ct(a) = 1). We’ll choose an exact value for
(cid:15) later; it will be between 0 and 1
2. For intuition, note that as (cid:15) grows small, the distribution
pt tends to the uniform distribution. Thus small values of (cid:15) encourage exploration. As (cid:15)
tends to 1, the distribution pt tends to the distribution that places all its mass on the action
that has incurred the smallest cumulative cost so far. Thus large values of (cid:15) encourage
“exploitation,” and (cid:15) is a knob for interpolating between these two extremes. The MW
algorithm is obviously simple to implement — the only requirement is to maintain a weight
for each action.

2.3 The Analysis

This section proves the bound in Theorem 2.1 for the MW algorithm. We can restrict
attention to oblivious adversaries (as deﬁned in Remark 1.5) that ﬁx a sequence of cost
vectors c1, . . . , cT up front. The intuitive reason is that the behavior of the MW algorithm is
independent of the realized actions a1, . . . , at: the distribution pt chosen by the algorithm is
a deterministic function of c1, . . . , ct−1. Thus, there is no reason for a worst-case adversary
for the MW algorithm to condition its cost vectors on previous realized actions. Similarly,
a worst-case adversary does not need to explicitly condition on the distributions p1, . . . , pt,
since these are uniquely determined by the adversary’s previous cost vectors c1, . . . , ct−1.4

Fix an arbitrary sequence c1, . . . , cT of cost vectors. Recall Γt = (cid:80)

a∈A wt(a) denotes the
sum of the actions’ weights at time t. The weight of every action (and hence Γt) can only
decrease with t. The plan for the proof is to relate the two quantities we care about, the
expected cost of the MW algorithm and the cost of the best ﬁxed action, to ΓT . The bound
will then follow from some simple algebra and approximations.

3Other update steps, like wt+1(a) = wt(a) · (1 − (cid:15)ct(a)), also work; see the Exercises.
4A bit more formally, one can solve for the worst adaptive adversary for the MW algorithm using backward

induction, and the result is an oblivious adversary.

5



<!-- pdf-page: 6 -->
The ﬁrst step is to show that if there is a good ﬁxed action, then the weight of this
action single-handedly shows that the ﬁnal value ΓT is pretty big. Formally, deﬁne OP T :=
(cid:80)T

t=1 ct(a∗) as the cumulative cost for the best ﬁxed action a∗. Then,

ΓT ≥ wT (a∗)

(1 − (cid:15))ct(a∗)

T
(cid:89)

= w1(a∗)
(cid:124) (cid:123)(cid:122) (cid:125)
=1
= (1 − (cid:15))OP T .

t=1

This connects our intermediate quantity ΓT with one of the two quantities that we care
about, namely OP T .

The second step, and the step which is special to the MW algorithm and its close cousins,
is that the sum of weights Γt decreases exponentially fast with the expected cost of the MW
algorithm. This implies that the algorithm can only incur large cost if all ﬁxed actions are
bad.

Precisely, the expected cost of the MW algorithm at time t is

pt(a) · ct(a) =

(cid:88)

a∈A

wt(a)
Γt

(cid:88)

a∈A

· ct(a).

Next, to understand Γt+1 as a function of Γt and the expected cost (2), we write

Γt+1 =

=

≤

(cid:88)

a∈A
(cid:88)

a∈A
(cid:88)

a∈A

wt+1(a)

wt(a) · (1 − (cid:15))ct(a)

wt(a) · (1 − (cid:15)ct(a))

= Γt(1 − (cid:15)νt),

(2)

(3)

where (3) follows from the fact that (1 − (cid:15))x ≤ 1 − (cid:15)x for (cid:15) ∈ [0, 1
2] and x ∈ [0, 1] (see
the Exercises), and νt denotes the expected cost (2) of the MW algorithm at time t. As
promised, the expected algorithm cost (and (cid:15)) govern the rate at which the total weight Γt
decreases.

Our goal is to upper bound the cumulative expected cost (cid:80)t

in terms of OP T . We’ve related these quantities through ΓT :

i=1 νt of the MW algorithm

and hence

(1 − (cid:15))OP T ≤ ΓT ≤ Γ1
(cid:124)(cid:123)(cid:122)(cid:125)
=n

T
(cid:89)

t=1

(1 − (cid:15)νt)

OP T · ln(1 − (cid:15)) ≤ ln n +

T
(cid:88)

t=1

ln(1 − (cid:15)νt).

6



<!-- pdf-page: 7 -->
We want to extract the νt’s from the clutches of the logarithm, so it makes sense to recall
the Taylor expansion

ln(1 − x) = −x − x2

2 − x3

3 − · · · .

By throwing away all (negative) terms but the ﬁrst, we can use this expansion to upper bound
ln(1 − (cid:15)νt) by −(cid:15)νt. While we’re at it, we may as well lower bound ln(1 − (cid:15)) by throwing
out all terms but the ﬁrst two, and doubling the second term to compensate (assuming here
that (cid:15) ≤ 1

2), yielding −(cid:15) − (cid:15)2. Summarizing, for (cid:15) ∈ (0, 1

2] we have

OP T · (cid:2)−(cid:15) − (cid:15)2(cid:3) ≤ ln n +

T
(cid:88)

t=1

(−(cid:15)νt)

and hence

T
(cid:88)

t=1

νt ≤ OP T · (1 + (cid:15)) +

ln n
(cid:15)

≤ OP T + (cid:15)T +

ln n
(cid:15)

,

(4)

where in the second inequality we use the very weak upper bound that, since costs are at
most 1, OP T is at most T .

√

We now set the free parameter (cid:15) in the MW algorithm to equalize the two error terms
in (4) — that is, to (cid:112)ln n/T . Then, the cumulative expected cost of the MW algorithm is
at most 2
T ln n more than the cumulative cost of the best ﬁxed action; dividing both sides
by T shows that (per-time-step) regret is at most 2(cid:112)ln n/T . This completes the proof of
Theorem 2.1.

Remark 2.3 (When T Is Unknown) In setting the parameter (cid:15), we assumed that the
time horizon T is known a priori. When this is not the case, the algorithm can be modiﬁed
ln n/ ˆT , where ˆT is the smallest power of 2 larger than

as follows: at day t, use the value (cid:15) =
t. The regret guarantee of Theorem 2.1 carries over to this algorithm (see the Exercises).

(cid:113)

Recall that Example 1.8 shows that Theorem 2.1 is optimal up the constant in the additive
iterations of the MW algorithm

term. Corollary 2.2 is also worth remembering — only 4 ln n
(cid:15)2
are necessary to achieve expected regret at most (cid:15).

3 No-Regret Dynamics

We now pass from single-player to multi-player settings. We use the language of cost-
minimization games (Lecture 13); there is an obvious analog for payoﬀ-maximization games.
In each time step t = 1, 2, . . . , T of no-regret dynamics:

1. Each player i simultaneously and independently chooses a mixed strategy pt

i using a

no-regret algorithm.

2. Each player i receives a cost vector ct

i, where ct

egy si when the other players play their chosen mixed strategies. That is, ct
Es−i∼σ−i[Ci(si, s−i)], where σ−i = (cid:81)
j(cid:54)=i σj.

i(si) is the expected cost of strat-
i(si) =

7



<!-- pdf-page: 8 -->
No-regret dynamics are well deﬁned because no-regret algorithms exist (Theorem 2.1). Each
player can use whatever no-regret algorithm it wants. Players move simultaneously, un-
like in best-response dynamics, but the following results also extend to players that move
sequentially (see the Exercises).

No-regret dynamics can be implemented very eﬃciently.

If each player uses the MW
algorithm, for example, then in each iteration each player does a simple update of one
weight per strategy, and only O( ln n
(cid:15)2 ) iterations of this are required before every player has
expected regret at most (cid:15) for every strategy. (Here n is the maximum size of a player’s
strategy set.) The next result is simple but important: the time-averaged history of joint
play under no-regret dynamics converges to the set of coarse correlated equilibrium — the
biggest set in our hierarchy of equilibria (Lecture 13). This forges a fundamental connection
between a static equilibrium concept and outcomes generated by natural learning dynamics.

Proposition 3.1 Suppose after T iterations of no-regret dynamics, every player of a cost-
minimization game has regret at most (cid:15) for each of its strategies. Let σt = (cid:81)k
i denote
the outcome distribution at time t and σ = 1
t=1 σt the time-averaged history of these
T
distributions. Then σ is an (cid:15)-approximate coarse correlated equilibrium, in the sense that

i=1 pt

(cid:80)T

Es∼σ[Ci(s)] ≤ Es∼σ[Ci(s(cid:48)

i, s−i)] + (cid:15)

for every player i and unilateral deviation s(cid:48)
i.

Proof: By deﬁnition, for every player i,

and

Es∼σ[Ci(s)] =

1
T

T
(cid:88)

t=1

Es∼σt[Ci(s)]

Es∼σ[Ci(s(cid:48)

i, s−i)] =

1
T

T
(cid:88)

t=1

Es∼σt[Ci(s(cid:48)

i, s−i)] .

(5)

(6)

The right-hand sides of (5) and (6) are the time-averaged expected costs of player i when
playing according to its no-regret algorithm and when playing the ﬁxed action s(cid:48)
i every day,
respectively. Since every player has regret at most (cid:15), the former is at most (cid:15) more than the
latter. This veriﬁes the approximate coarse correlated equilibrium condition. (cid:4)

Remark 3.2 For Proposition 3.1, it is important that the decision-making algorithms used
by the players have no regret with respect to adaptive adversaries (Remark 1.5). The mixed
strategy chosen by player i at time t aﬀects the cost vectors ct
j received by the other players
j (cid:54)= i at time t, hence it aﬀects their chosen strategies at future time steps, and hence it
aﬀects the cost vectors received by player i at future time steps. That is, when other players
are themselves using adaptive learning algorithms to choose strategies, they correspond to
an adaptive adversary.

8



<!-- pdf-page: 9 -->
In Lecture 14 we proved that POA bounds for smooth games — including all of the
examples we’ve studied in this course — automatically extend to coarse correlated equilibria.
With an approximate equilibrium, the POA bounds remain approximately correct.

Corollary 3.3 Suppose after T iterations of no-regret dynamics, player i has expected regret
at most Ri for each of its actions. Then the time-averaged expected objective function value
1
T Es∼σi[cost(s)] is at most

λ
1 − µ

cost(s∗) +

(cid:80)k

i=1 Ri
1 − µ

.

In particular, as T → ∞, (cid:80)k
bound λ

1−µ. We leave the proof of Corollary 3.3 as an exercise.

i=1 Ri → 0 and the guarantee converges to the standard POA

4 Epilogue

The key take-home points of this lecture are:

1. Very simple learning algorithms lead remarkably quickly to (approximate) coarse cor-

related equilibria (CCE).

2. In this sense, CCE are unusually tractable, and hence unusually plausible as a predic-

tion for player behavior.

3. Since POA bounds in smooth games apply to no-regret dynamics, they are particularly

robust to the behavioral model.

References

[1] S. Arora, E. Hazan, and S. Kale. The multiplicative weights update method: a meta-

algorithm and applications. Theory of Computing, 8(1):121–164, 2012.

[2] N. Cesa-Bianchi and G. Lugosi. Prediction, Learning, and Games. Cambridge University

Press, 2006.

[3] J. Hannan. Approximation to Bayes risk in repeated play. Ccontributions to the Theory

of Games, 3:97–139, 1957.

[4] N. Littlestone and M. K. Warmuth. The weighted majority algorithm. Information and

Computation, 108(2):212–261, 1994.

9


