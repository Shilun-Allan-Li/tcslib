<!-- generated-by: scoped Poppler extraction of the passages used (DW-8) -->
<!-- source-pdf-sha256: 216f8cd86ce5e077730bcf9d5ed1a90131f0107d23e64f249c7df02690b4678a -->
<!-- extractor: pdftotext version 24.02.0; no -layout, one page at a time (pdftotext -f N -l N); scoped to the line ranges listed below -->
<!-- scope (physical page: lines of that page's own extraction): p6: 82-118; p7: 1-137; p8: 1-150; p9: 39-123; p9: 128-147; p10: 1-7 -->
<!-- note: physical page = printed page. The paper is set in two columns; Poppler's reading order interleaves the columns around figures, so headings can appear after the text they head. The transcription (.md) restores the reading order. -->

<!-- pdf-page: 6 -->
that can be read and written by the adversary) and Gro (those that
the adversary can only read), we say that an adversary A is wellformed in an environment E if the judgment ⊢wf A can be derived
using the rules in Fig. 4. These rules guarantee that each time a
variable is written by the adversary, the adversary has the right to
do so; and that each time a variable is read by the adversary, it is
either a global variable in GA ∪ Gro or a local variable previously
initialized. A well-formed adversary is free to call oracles, but any
other procedure it calls must be a well-formed adversary itself.
Additional constraints may be imposed on adversaries. For example, exact security proofs usually impose an upper bound to the
number of calls adversaries can make to a given oracle, whereas
for some properties such as IND-CCA2 there are some restrictions
on the parameters with which the oracles may be called. Likewise,
some proofs impose extra conditions such as forbidding repeated or
malformed queries. These kinds of properties can be formalized using lists that record the oracle calls, and verifying as postcondition
that the calls were legitimate.

3.4 Adversaries

4. Relational Hoare Logic

In order to reason formally about security, we make explicit which
variables and procedures are accessible to adversaries, and provide
a simple analysis to check whether an adversary respects its policy.
Given a set of procedure identifiers O (the procedures that may
be called by the adversary), and sets of global variables GA (those

Shoup [31] classifies proof steps into three categories: transitions
based on indistinguishability—which typically involve applying a
security hypothesis, e.g. the DDH assumption—; transitions based
on failure events—which typically amount to bound the probability
of bad, as in the Switching Lemma—; and bridging steps—which
correspond to replacing or reorganizing code in a way that is not
observable by adversaries. In some circumstances, a bridging transition from G1 to G2 may replace a program fragment P by another
fragment P ′ observationally equivalent to P . In general, however,

2 It is of course a weak result in terms of termination of probabilistic
programs, but nevertheless sufficient as regards cryptographic applications.

<!-- pdf-page: 7 -->
P and P ′ are only observationally equivalent in the context where
the replacement is done. Such transitions are supported through a
relational Hoare logic, that generalizes observational equivalence
through preconditions and postconditions which we use to characterize the context where the replacement is valid. Besides, we use
relational Hoare logic to establish (in)equalities between probabilities of two events, as shown by the lemmas (=JK ) and (≤JK ) below,
and to establish program invariants, e.g. in the proof of the Switching Lemma in Sec. 2.2.

Second, some rules of pRHL do not appear in RHL, or generalize
existing rules. The rule [R-Case] allows to do a case analysis on the
evaluation of an arbitrary relation in the initial memories. Together
with simple rules in the spirit of
 E1 , c1 ∼ E2 , c : Ψ ∧ eh1i ⇒ Φ
 E1 , if e then c1 else c2 ∼ E2 , c : Ψ ∧ eh1i ⇒ Φ
it subsumes [R-Cond] and allows to prove judgments that would
otherwise not be derivable, such as the equivalence between
(if e then c1 else c2 ) and (if ¬e then c2 else c1 ). We also use
[R-Case] to prove the correctness of dataflow analyses that exploit
the information provided by entering branches.
In addition, we often use the rule [R-Inv] that generalizes the
rule [R-Sym] to inverse of relations

4.1 Probabilistic Relational Hoare Logic (pRHL)
Our logic pRHL elaborates on and extends to probabilistic programs Benton’s Relational Hoare Logic [9]. Benton’s logic uses
judgments of the form ⊢ G1 ∼ G2 : Ψ ⇒ Φ, and relates the evaluation of a program G1 to the evaluation of a program G2 w.r.t.
a precondition Ψ and a postcondition Φ, both defined as relations
on deterministic states. Such a judgment states that for any initial
memories m1 and m2 satisfying the precondition m1 Ψ m2 , if the
evaluations of G1 in m1 and G2 in m2 terminate with final memories m′1 and m′2 respectively, then m′1 Φ m′2 holds. In a probabilistic setting, the evaluation of a program w.r.t. an initial memory
yields a (sub-)distribution. In order to give a meaning to the above
judgment, one therefore needs to lift relations over memories into
relations over distributions.3 We follow early work on probabilistic
bisimulations [21]. The lifting to distributions of a unary predicate
P and of a binary relation Φ are respectively defined as

 G1 ∼ G2 : Ψ ⇒ Φ
[R-Inv]
 G2 ∼ G1 : Ψ−1 ⇒ Φ−1
and we make an extensive use of the rule [R-Comp] that generalizes
the rule [R-Tr] to composition of relations4
 G1 ∼ G : Ψ′ ⇒ Φ′  G ∼ G2 : Ψ′′ ⇒ Φ′′
[R-Comp]
 G1 ∼ G2 : Ψ′ ◦ Ψ′′ ⇒ Φ′ ◦ Φ′′
The benefits of the rule [R-Comp], as opposed to [R-Tr], are illustrated by considering “independent” preconditions and postconditions of the form
Ψ def
= λx y .Ψ1 x ∧ Ψ2 y

range P µ def
= ∀f. (∀a. P a ⇒ f a = 0) ⇒ µ f = 0
µ1 ∼Φ µ2 def
= ∃µ. π1 (µ) = µ1 ∧ π2 (µ) = µ2 ∧ range Φ µ

Φ def
= λx y .Φ1 x ∧ Φ2 y

In order to apply the rule [R-Tr] to G1 and G2 , we are essentially
forced to have Ψ1 = Ψ2 and Φ1 = Φ2 , and furthermore we must
also choose the same pre and postcondition for the intermediate
game G. This constraint makes the rule [R-Tr] impractical, we use
instead the rule [R-Comp] to introduce intermediate games that do
not satisfy the same specification as G1 or G2 .
The rule [R-Rand] is also (obviously) not present in RHL. Let
Ix def
= (λv.if x = v then 1 else 0), and define the support of a
distribution, supp(JdK m), by the clause

where the projections of µ are defined as
def
π1 (µ) def
= bind µ (λ(x, y).unit x) π2 (µ) = bind µ (λ(x, y).unit y)

This way of lifting relations over memories to relations over distributions is a generalization to arbitrary relations of the definition of Sabelfeld and Sands [29]. Their definition applies only to
PERs, whereas our definition applies to arbitrary relations. Nevertheless, both definitions coincide for PERs as established by Jonsson, Larsen and Yi [21].

v ∈ supp(JdK m) ⇔ JdK m Iv 6= 0

Definition 5 (pRHL judgments). Programs G1 and G2 are equivalent w.r.t. precondition Ψ and postcondition Φ iff

Finally, let Jd1 K m1 =g Jd2 K m2 iff there exists a set X and a bijection g : X → X such that supp(Jd1 K m1 ) = supp(Jd2 K m2 ) = X
and Jd1 K m1 Ia = Jd2 K m2 I(g a) for all a in X. To apply rule
[R-Rand], it is necessary to exhibit a function f such that for all
memories m1 and m2 , Jd1 K m1 =f m1 m2 Jd2 K m2 . Thus, if
d1 = d2 = [0..n] for some constant n, and we take f to be the
identity function, the premise simplifies to the expected,

def

 G1 ∼ G2 : Ψ ⇒ Φ =
∀ m1 m2 . m1 Ψ m2 ⇒ JG1 K m1 ∼Φ JG2 K m2
Our approach slightly departs from Benton’s: rather than defining the rules for pRHL and proving them sound w.r.t. the meaning
of judgments, we place ourselves in a semantic setting and derive
the rules as lemmas. This allows to easily extend the system by deriving extra rules, or even to resort to the semantic definition if the
system turns out to be insufficient.
Figure 5 gathers some representative derived rules. To improve
readability, in the figure and in the remainder of the paper we
let ehii denote λm1 m2 . JeK mi = true, where e is a boolean
expression. As pRHL allows for arbitrary relations, we freely use
higher-order logic; in particular, PER and SYM are predicates over
relations that stand for partial equivalence relation and symmetric
relation respectively. There are two points worth noting. First, most
rules admit, in addition to their symmetrical version of Fig. 5, onesided (left and right) variants, e.g. for assignments

m1 Ψ m2 def
= ∀ v ∈ [0..n]. (m1 {v/x1 }) Φ (m2 {v/x2 })
Section 5.3 shows that the generality of the rule is required for
applications such as optimistic sampling.
It is often fruitful to understand pRHL judgments in terms
of the inability of the postcondition to separate between the two
commands of the judgment. Define two functions f and g to be
equivalent w.r.t. a predicate Φ iff
f =Φ g def
= ∀ m1 m2 . m1 Φ m2 ⇒ f (m1 ) = g(m2 )
The definition of pRHL judgments entails
9
 G1 ∼ G2 : Ψ ⇒ Φ =
f =Φ g
⇒ JG1 K m1 f = JG2 K m2 g
;
m1 Ψ m2

m1 Φ′ m2 def
= (m1 {Je1 Km1 /x1 }) Φ m2
 E1 , x1 ← e1 ∼ E2 , nil : Φ′ ⇒ Φ

(=JK )

4 The machine-checked rule requires that Φ, Φ′ are decidable, and uses Set-

3 An alternative would be to develop a logic in which Ψ and Φ are relations
over distributions. However, it is not clear whether such a logic would allow
a similar level of proof automation. This is left for future work.

valued existential quantification ∃Set in the composition for preconditions,
i.e. x (Ψ ◦ Ψ′ ) z def
= ∃Set y. x Ψ y ∧ y Ψ′ z.

7


<!-- pdf-page: 8 -->
 E1 , nil ∼ E2 , nil : Φ ⇒ Φ [R-Skip]

 E1 , c1 ∼ E2 , c2 : Φ ⇒ Φ′  E1 , c′1 ∼ E2 , c′2 : Φ′ ⇒ Φ′′
[R-Seq]
 E1 , c1 ; c′1 ∼ E2 , c2 ; c′2 : Φ ⇒ Φ′′

 E1 , x1 ← e1 ∼ E2 , x2 ← e2 : (λ m1 m2 . (m1 {Je1 Km1 /x1 }) Φ (m2 {Je2 Km2 /x2 })) ⇒ Φ [R-Ass]
m1 Ψ m2 def
=

Jd1 Km1 =f m1 m2 Jd2 Km2 ∧ ∀ v ∈ supp(Jd1 Km1 ). (m1 {v/x1 }) Φ (m2 {f m1 m2 v/x2 })
[R-Rand]
$ d ∼ E ,x
$
 E1 , x1 ←
1
2
2 ← d2 : Ψ ⇒ Φ

∀m1 m2 . m1 Ψ m2 ⇒ Je1 K m1 = Je2 K m2  E1 , c1 ∼ E2 , c2 : Ψ ∧ e1 h1i ⇒ Φ  E1 , c′1 ∼ E2 , c′2 : Ψ ∧ ¬e1 h1i ⇒ Φ
[R-Cond]
 E1 , if e1 then c1 else c′1 ∼ E2 , if e2 then c2 else c′2 : Ψ ⇒ Φ
∀m1 m2 . m1 Φ m2 ⇒ Je1 K m1 = Je2 K m2  E1 , c1 ∼ E2 , c2 : Φ ∧ e1 h1i ⇒ Φ
[R-Whl]
 E1 , while e1 do c1 ∼ E2 , while e2 do c2 : Φ ⇒ Φ ∧ ¬e1 h1i
 G1 ∼ G2 : Ψ′ ⇒ Φ′
 G1 ∼ G2 : Ψ ⇒ Φ SYM(Ψ)
 G2 ∼ G1 : Ψ ⇒ Φ

∀m1 m2 . m1 Ψ m2 ⇒ m1 Ψ′ m2
 G1 ∼ G2 : Ψ ⇒ Φ

SYM(Φ)

[R-Sym]

∀m1 m2 . m1 Φ′ m2 ⇒ m1 Φ m2

 G1 ∼ G : Ψ ⇒ Φ

[R-Sub]

 G ∼ G2 : Ψ ⇒ Φ PER(Ψ) PER(Φ)
[R-Tr]
 G1 ∼ G2 : Ψ ⇒ Φ

 G1 ∼ G2 : Ψ ∧ Ψ′ ⇒ Φ  G1 ∼ G2 : Ψ ∧ ¬ Ψ′ ⇒ Φ
[R-Case]
 G1 ∼ G2 : Ψ ⇒ Φ
Figure 5. Selection of derived rules of pRHL
By instantiating f and g to 11, one can observe that observational
equivalence enjoys some form of termination sensitivity

4.2 Observational equivalence
Observational equivalence is derived as an instance of relational
Hoare judgments in which pre and postconditions are restricted to
relations based on equality over a subset of variables. Given a set
X of variables, we define =X as

( G1 ∼ G2 : Ψ ⇒ Φ) ∧ m1 Ψ m2 ⇒ JG1 K m1 11 = JG2 K m2 11
This interpretation of pRHL judgments is strongly connected to the
relation between relational logics and information flow [3, 9]. We
extensively use (=JK ), and its variant (≤JK ) below, to fall back from
the world of pRHL into the world of probabilities, in which security
statements are expressed;
9
 G1 ∼ G2 : Ψ ⇒ Φ =
f ≤Φ g
⇒ JG1 K m1 f ≤ JG2 K m2 g (≤JK )
;
m1 Ψ m2

m1 =X m2 def
= ∀ x ∈ X. m1 x = m2 x
Then, the observational equivalence of G1 and G2 w.r.t. an input
set I and an output set O is defined as
 G1 ≃IO G2 def
=

 G1 ∼ G2 : =I ⇒ =O

All derived rules for pRHL can be specialized to the case of observational equivalence. For example, we have
 e1 ≃I e2
 E1 , c1 ≃IO E2 , c2
 E1 , c′1 ≃IO E2 , c′2
′
I
 E1 , if e1 then c1 else c1 ≃O E2 , if e2 then c2 else c′2

where f ≤Φ g def
= ∀ m1 m2 . m1 Φ m2 ⇒ f (m1 ) ≤ g(m2 ).
We conclude with an example that nicely illustrates some
$
{0, 1} and define
of the intricacies of pRHL. Let c = b ←
m1 Φ m2 def
= m1 b = m2 b. Then  c ∼ c : true ⇒ Φ.
Indeed, take µ such that µ 11h0,0i = µ 11h1,1i = 1/2 and
µ 11h0,1i = µ 11h1,0i = 0. One can check that µ ensures
JcK m ∼Φ JcK m′ for all m and m′ . This example shows why
the lifting of a binary relation involves an existential quantification,
and why it is not possible to always instantiate µ as the product
distribution in the definition of ∼Φ (one cannot establish the above
judgment using the product distribution). Perhaps more surprisingly,  c ∼ c : true ⇒ ¬Φ also holds. Indeed, take µ such that
µ 11h0,0i = µ 11h1,1i = 0 and µ 11h0,1i = µ 11h1,0i = 1/2. One can
check that µ ensures JcK m ∼¬Φ JcK m′ for all m and m′ . Thus,
the “obvious” rule

where  e1 ≃I e2 iff for every memories m1 and m2 , m1 =I m2
implies Je1 K m1 = Je2 K m2 .
To support automation, CertiCrypt implements a calculus of
variable dependencies and provides two functions, eqobsIn and
eqobsOut, that given a command c and a set O (respectively I)
of output (input) variables compute a set I (O) of input (output)
variables such that  E1 , c ≃IO E2 , c. CertiCrypt also provides
tactics for two variants of observational equivalence that are widely
used in game-based proofs, namely
ϕ G1 ≃IO G2
Ψ,Φ G1 ≃IO G2

def

=
=

def

 G1 ∼ G2 : =I ∧ ϕ ⇒ =O ∧ ϕ
 G1 ∼ G2 : =I ∧ Ψ ⇒ =O ∧ Φ

These tactics use a (sound but incomplete) weakest precondition
calculus for relational judgments.

 G1 ∼ G2 : Ψ ⇒ Φ
 G1 ∼ G2 : Ψ ⇒ Φ′
 G1 ∼ G2 : Ψ ⇒ Φ ∧ Φ′

5. Proof methods for bridging steps

is unsound. While this example may seem unintuitive or even
inconsistent if one reasons in terms of deterministic states, its
intuitive significance in a probabilistic setting is that neither of
the relations Φ and ¬Φ are enough to tell apart the two final
distributions.

CertiCrypt provides a powerful set of tactics and algebraic equivalences to automate bridging steps. Most tactics rely on an implementation of a certified optimizer for pW HILE , with the exception
of lazy sampling which has an ad hoc implementation. Algebraic

8


<!-- pdf-page: 9 -->
5.2 Lazy sampling
It is sometimes convenient to defer random choices in games until
they are actually needed, or conversely, to make random choices
as early as possible. The lazy sampling technique, allows to delay
the random sampling of a value until the point in the program
where it is first used. Conversely, eager sampling allows to choose
a random value, which would be otherwise sampled later, at the
beginning of a game. These techniques are presented in [8], where
the authors discuss some of its subtleties. In this section we present
a syntax-oriented criterion for the correctness of lazy sampling that
can be applied provided the sampling is adequately guarded. Here
by context we mean a program context with multiple holes that may
appear either in the main program or any of the procedures in the
environment.

E2 , c′2

 E1 , c1 ≃IO E2 , c2
Using the same idea, CertiCrypt provides algorithms for removing
only a common prefix (eqobs hd) or suffix (eqobs tl).
Second, CertiCrypt provides a tactic that given two commands
repeatedly tries to hoist their common instructions to obtain a
maximal common prefix5 , which can then be eliminated using the
previous rule. Its correctness is based on the rule
 E, c1 ≃IO11 E, c1  E, c2 ≃IO22 E, c2 modify(E, ci , Oi )
O1 ∩ O2 = ∅ I1 ∩ O2 = ∅ I2 ∩ O1 = ∅
 E, c1 ; c2 ∼ E, c2 ; c1 : = ⇒ =

Lemma 1 (Lazy/eager sampling). Let C[·] be a context, c1 and
c2 commands, e a boolean expression, d a distribution expression,
and z a variable, such that C[·] does not modify fv(e) ∪ fv(d) and
does not use z. Assume

where modify(E, c, X) is a semantic predicate expressing that only
variables in X are modified by the command c in the environment
E. This is formally expressed by ∀ m. range (λm′ . m =V\X
m′ ) (JE, cK m) which ensures that reachable final memories are
equal to the initial one except maybe on variables in X. The tactic
swap is based on the rule above and on an algorithm that overapproximates the set of modified variables.
Third, CertiCrypt allows performing dead code elimination relative to a set O of output variables (deadcode). The algorithm behaves more like an aggressive slicing algorithm, i.e. it removes portions of code that do not affect variables in O, and performs at the
same time branch prediction (replacing if true then c1 else c2 by
c1 ), branch coalescing (replacing if e then c else c by c), and selfassignment elimination. Its correctness relies on the rule

$ d; c ; if e then z $ d ∼ z $ d; c : (= ∧ eh1i) ⇒ =
1.  z ←
←
←
1
1
2.  c2 ∼ c2 : (= ∧ ¬eh1i) ⇒ (= ∧¬eh1i)
$ d; c else c and c′ = if e then c else c .
Let c = if e then z ←
1
2
1
2
$ d ∼ z $ d; C[c′ ] : (= ∧ eh1i) ⇒ =
Then,  C[c]; if e then z ←
←

Intuitively, in the above lemma e indicates whether z has not
been used in the game since it was last sampled. If it has not been
used, then it is perfectly fine to resample it. The first two hypotheses
ensure that e has exactly this meaning, c1 must set it to false if it
has used the value sampled in z, and c2 must not reset e if it is false.
$ d,
The first hypothesis is the one that allows to swap c1 with z ←
provided the value of z is not used in c1 . Note that, for clarity, we
have omitted environments in the above lemma, and so the second
hypothesis is not as trivial as it may seem because both programs
may have different environments.
Suppose we want to eagerly sample the answer that a random
oracle
$ d; L ← (x, y) :: L;
Ol (x) def
/ dom(L) then y ←
= if x ∈
return L[x]

modify(E1 , c, X) Lossless(E1 , c) fv(ϕ) ∩ X = ∅
 E1 , c ∼ E2 , nil : ϕ ⇒ ϕ
Optimizations based on dataflow analyses CertiCrypt has builtin, generic, support for such optimizations: given an abstract domain D (a semi-lattice) for the analysis, transfer functions for assignment and branching instructions, and an operator transforming
expressions in the language into their optimized versions (using the
result of the analysis), CertiCrypt automatically constructs the certified optimization function optim : C → D → C ×D. When given
a command c and an element δ ∈ D, this function transforms c into
gives to a particular query x′ , i.e. we want to transform Ol into
Oe (x) def
/ dom(L) then
= if x ∈
$ d;
if x = x′ then y ← y ′ else y ←
L ← (x, y) :: L
return L[x]
′
$ d; O (x) else O (x),
/ dom(L) then y ′ ←
Define Ol′ (x) def
= if x ∈
e
l
def
′
′
/ dom(L) then Oe (x) else Ol (x), both returnOe (x) = if x ∈
ing L[x]. Oracles Ol and Oe result semantically equivalent to Ol′

<!-- pdf-page: 10 -->
and Oe′ , respectively. Lemma 1 can be applied taking e = x′ ∈
/
dom(L), z = y ′ , and c1 = Oe (x), c2 = Ol (x) to safely replace
oracle Ol by oracle Oe in the environment of a program, sampling
y ′ at the beginning. Whenever a bound for the number of queries to
a random oracle is known in advance, the above trick can be iteratively applied to completely remove randomness from the oracle
code, as it is done in the proof of the Switching Lemma in Sec. 2.2.
