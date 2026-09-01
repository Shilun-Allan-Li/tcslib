<!-- generated-by: proofmatch local extraction -->
<!-- source-pdf-sha256: 52929dbaa9629cc3e229c78a6cb4860da8d2223064e05f7972c7f03993772747 -->
<!-- extractor: pdfminer.six v20260107 -->

<!-- pdf-page: 1 -->
Chapter 13

Circuit lowerbounds

Complexity theory’s Waterloo

We believe that NP does not have polynomial-sized circuits. We’ve seen that if true, this
= P. In the 1970s and 1980s, many researchers came to believe that the route
implies that NP
to resolving P versus NP should go via circuit lowerbounds, since circuits seem easier to reason
about than Turing machines. The success in this endeavor was mixed.

Progress on general circuits has been almost nonexistent: a lowerbound of n is trivial for any
function that depends on all its input bits. We are unable to prove even a superlinear circuit
lowerbound for any NP problem— the best we can do after years of eﬀort is 4.5n

o(n).

To make life (comparatively) easier, researchers focussed on restricted circuit classes, and were
successful in proving some decent lowerbounds. We prove some of the major results of this area and
indicate where researchers are currently stuck. In Chapter 22 we’ll explain some of the inherent
obstacles that need to be overcome to make further progress.

−

13.1 AC0 and H˚astad’s Switching Lemma

As we saw in Chapter 6, AC0 is the class of languages computable by circuit families of constant
(Constant depth circuits with
depth, polynomial size, and whose gates have unbounded fanin.
fanin 2 can only compute functions depending on a constant number of input bits.) The burning
question in the late 1970s was whether problems like Clique and TSP have AC0 circuits. However,
in 1981, Furst, Saxe and Sipser and independently, Ajtai, proved a lowerbound for a much simpler
function:

Theorem 13.1 ([?, ?])
Let
Then

AC0.

L

6∈

L

be the parity function. That is, for every x

0, 1
}

∈ {

n,

(x1, . . . , xn) =

n
i=1 xi (mod 2).

L

P

Often courses in digital logic design teach students how to do “circuit minimization” using
Karnaugh maps. Note that circuits talked about in those courses are depth 2 circuits, i.e. CNF or
DNF. Indeed, it is easy to show (using for example the Karnaugh map technique studied in logic

DRAFT

Web draft 2007-01-08 21:59
p13.1 (235)
Complexity Theory: A Modern Approach. © 2006 Sanjeev Arora and Boaz Barak. References and attributions are
still incomplete.

6


<!-- pdf-page: 2 -->
p13.2 (236)

13.1. AC0 AND H˚ASTAD’S SWITCHING LEMMA

design) that the parity function requires exponentially many gates if the depth is two. However,
those simple ideas do not seem to generalize to even depth 3 circuits.

−

The main tool in the proof of Theorem 13.1 is the concept of random restrictions. Let f be a
function computable by a depth d circuit and suppose that we choose at random a vast majority
n(cid:15) for some constant (cid:15) > 0 depending on d) of the input variables and assign to each such
(i.e., n
variable either 0 or 1 at random. We’ll prove that with positive probability, the function f subject
to this restriction is constant (i.e., either always zero or always one). Since the parity function
cannot be made a constant by ﬁxing values to a subset of the variables, it follows that it cannot be
computed by a constant depth circuit.

13.1.1 The switching lemma

Now we prove the main lemma about how a circuit simpliﬁes under a random restriction. A k-DNF
(resp. k-CNF) formula is an OR of AND’s (resp. AND or OR’s) where each AND (resp. OR)
involves at most k variables.

Lemma 13.2 (H˚astad’s switching lemma [Has86])
Suppose f is expressible as a k-DNF, and let ρ denote a random restriction that assigns random
values to t randomly selected input bits. Then for every s

2.

≥

Prρ[f

|ρ is not expressible as s-CNF ]

≤

s/2

(n

t)k10
−
n

(cid:18)

(cid:19)

(1)

where f

|ρ denotes the function f restricted to the partial assignment ρ.

We’ll typically use this lemma with k, s constant and t

√n in which case the guaranteed
c for some constant c. Note that by applying the lemma to the

≈

−

n

f , we can get the same result with the terms DNF and CNF interchanged.

bound on the probability will be n−
function

¬

Proving Theorem 13.1 from Lemma 13.2. Now we show how H˚astad’s lemma implies that
parity is not in AC0. We start with any AC0 circuit and assume that the circuit has been simpliﬁed
as follows (the simpliﬁcations are straightforward to do and are left as Exercises 1 and 2): (a) All
fanouts are 1; the circuit is a tree (b) All not gates to the input level of the circuit; equivalently,
the circuit has 2n input wires, with the last n of them being the negations of the ﬁrst n (c)
and
gates alternate —at worst this assumption doubles the depth of the circuit (d) The bottom level

∨

∧
has

gates of fanin 1.

∧
We randomly restrict more and more variables, where each step with high probability will reduce
the depth of the circuit by 1 and will keep the bottom level at a constant fanin. Speciﬁcally, letting
ni stand for the number of unrestricted variables after step i, we restrict ni −
√ni variables at step
i + 1. Since n0 = n, we have ni = n1/2i
. Let nb denote an upper bound on the number of gates in
the circuit and let ki = 10b2i. We’ll show that with high probability, after the ith restriction we’re
i circuit with at most ki fanin in the bottom level. Indeed, suppose that the
left with a depth-d
−
bottom level contains

gates and the level above it contains

gate computes is a ki-DNF and hence by Lemma 13.2, with probability 1

∨

gates. The function each such
k10
i
n1/2i+1

∨
, which

ki+1/2

−

(cid:16)

(cid:17)

Web draft 2007-01-08 21:59

∧

DRAFT



<!-- pdf-page: 3 -->
13.1. AC0 AND H˚ASTAD’S SWITCHING LEMMA

p13.3 (237)

∧

∨

−

1/(10nb) for large enough n, the function such a gate computes will be expressible
is at least 1
-gate above it, reducing the depth of the
as a ki+1-CNF. We can then merge this CNF with the
circuit by one (see Figures 13.1 and 13.2). The symmetric reasoning applies in the case the bottom
level consists of
gates— in this case we use the lemma to transform the ki-CNF of the level
above it into a ki+1-DNF. Note that we apply the lemma at most once per each of the at most nb
gates of the original circuit. By the union bound, with probability 9/10, if we continue this process
for d
2 at bottom level (i.e., a k-CNF
or k-DNF formula). If we then choose to restrict each variable with probability half (i.e., restrict
about half of the variables to a random value), this circuit will be reduced to a constant function
k. Since the parity function is not constant under any restriction of less
with probability at least 2−
than n variables, this proves Theorem 13.1. (cid:4)

2 steps, we’ll get a depth two circuit with fanin k = kd

−

−

Figure unavailable in pdf ﬁle.

Figure 13.1: Circuit before H˚astad switching transformation.

Figure unavailable in pdf ﬁle.

Figure 13.2: Circuit after H˚astad switching transformation. Notice that the new layer of ∧ gates can be collapsed
with the single ∧ parent gate, to reduce the number of levels by one.

13.1.2 Proof of the switching lemma (Lemma 13.2)

n
t

2t. Let Kt,s denote the set of restrictions ρ such that f

Now we prove the Switching Lemma. The original proof was more complicated; this one is due
to Razborov. Let f be expressible as a k-DNF on n variables. Let t be as in the lemma and let
Rt denote the set of all restrictions to t variables (note we can assume t > n/2). We have that
=
|ρ is not a s-CNF. We need to
|Rt|
by the right hand side of (1) to prove the lemma. We’ll do that by showing a
bound
/
Kt,s|
(cid:0)
(cid:1)
|
S where Z is the set of restrictions of at least t+s
one-to-one function mapping Kt,s into the set Z
t+sRt0) and S is some set of size 32ks. This will prove the lemma since at he
variables (i.e. Z =
and hence Z will be of size bounded by roughly n2s
.
range t0 (cid:29)
|Rt|
n
We leave verifying the exact bound as Exercise 3.

|Rt|

n/2,

∪t0

×

≈

n
t0

−
n

t0

t0

−

≥

−

n

n

n

s

t

(cid:0)

(cid:1)

(cid:16)

(cid:17)

(cid:0)

(cid:1)

Mapping Kt,s into Z
|ρ is not an
s-CNF. We need to map ρ in a one-to-one way into some restriction ρ∗ of at least t + s variables,
and some additional element in a set S of size at most 32ks.

Kt,s be a restriction ﬁxing t variables such that f

S. Let ρ

×

∈

Special case: each term has at most one “live” variable. To get some intuition for the
proof, consider ﬁrst the case that for each term t in the k-DNF formula for f , ρ either ﬁxed t to
the value 0 or left a single unassigned variable in t, in which case we say that t0s value is ? (ρ can’t
|ρ is not constant). We denote by x1, . . . , xs denote the
ﬁx a term to the value 1 since we assume f

DRAFT

Web draft 2007-01-08 21:59



<!-- pdf-page: 4 -->
p13.4 (238)

13.1. AC0 AND H˚ASTAD’S SWITCHING LEMMA

· · ·

1 to ρ,

ﬁrst s such unassigned variables, according to some canonical ordering of the terms for the k-DNF
|ρ would be expressible as an s-CNF). For
formula of f (there are more than s since otherwise f
each such variable xi, let termi be the ?-valued term in which xi appears. Let Ri be the operation
of setting xi to the value that ensures termi is true. We’ll map ρ to τ1 = R1R2 · · ·
Rsρ. That is,
, then apply R1 to ρ. The crucial insight is that given τ1,
apply Rs to ρ, then apply Rk
−
one can deduce term1: this is the ﬁrst term that is true in f
|τ1. One might think that the second
|τ1 is term2 but that’s not necessarily the case, since the variable x1 may have
term that is true in f
appeared several times, and so setting it to R1 may have set other terms to true (it could not have
xi, and hence
set other terms to false, since this would imply that f
¬
s that
is the constant one function). We thus supply as part of the mapping a string w1 ∈ {
0, 1, ?
tells us the assignment of the k variables of term1 in τ2 = R2 · · ·
Rsρ. Given that information we
can “undo” R1 and move from τ1 to τ2. Now in τ2, term2 is the ﬁrst satisﬁed term. Continuing
on this way we see that from τ1 (which is an assignment of at least t + s variables) and strings
w1, . . . , ws that are deﬁned as above, we can recover ρ, implying that we have a one-to-one mapping
that takes ρ into an assignment of at least t + s variables and a sequence in

|ρ includes an OR of xi and

0, 1, ?

ks.

}

{

}

−

1-CNF. Indeed, if for both possible assignments to x1 we get an s

The general case. We now consider the general case, where some terms might have more than
one unassigned variable in them. We let term1 be the ﬁrst ?-valued term in f
|ρ and let x1 be the
ﬁrst unassigned variable in term1. Once again, we have an operation R1 that will make term1 true,
although this time we think of R1 as assigning to all the k variables in term1 the unique value that
makes the term true. We also have an operation L1 assigning a value to x1 such that f
|L1ρ cannot
be expressed by an s
1-CNF
then f
|ρ is an s-CNF. We note that it’s not necessarily the case that x1’s value under L1ρ is diﬀerent
from its value under R1ρ, but it is the case that term1’s value is either ? or False under L1ρ (since
|L1ρ would be constant). We let term2 be the ﬁrst ?-valued term in f
otherwise f
|L1ρ (note that
term1) and let x2 be the ﬁrst unassigned variable in term2. Once again, we have an
term2 ≥
operation R2 such that term2 is the ﬁrst true term in f
|L2L1ρ
is not a s
2-CNF. Continuing in this way we come up with operations L1, . . . , Ls, R1, . . . , Rs such
that if we let ρi be the assignment Li · · ·
L1ρ (with ρ0 = ρ) then for 1
• termi is the ﬁrst ?-valued term in f

|R2L1ρ and operation L2 such that f
i

≤

−

≤

−

s:

|ρi−1.

• termi is the ﬁrst true-valued term in f

|Riρi−1.

• Li agrees with ρi
−

1 on all variables assigned a value by ρi

−

1.

• Ri agrees with ρi on all variables assigned a value by ρi.

i

≤

For 1

s, deﬁne τi to be RiRi+1 · · ·

Rsρs, and deﬁne τs+1 = ρs. We have that termi is
|τi: indeed, all the operations in τi do not change variables assigned values
1 and there termi is the ﬁrst ?-valued term. Thus τi cannot make any earlier term true.

≤
the ﬁrst true term in f
by ρi
However, since the last operation applied is Ri, termi is true in f

−

Let z1, . . . , zs and w1, . . . , ws be 2s strings in

s deﬁned as follows: zi describes the
0, 1, ?
}
{
values assigned to the k variables appearing in termi by ρi
1 and wi describes the value assigned to
−
termi’s variables by τi+1. Clearly, from termi, zi and the assignment ρi one can compute ρi
1 and
−

|τi.

Web draft 2007-01-08 21:59

DRAFT



<!-- pdf-page: 5 -->
13.2. CIRCUITS WITH “COUNTERS”:ACC
from termi, wi and the assignment τi one can compute τi+1. We’ll map ρ to τ1 and the sequence
z1, . . . , zs, w1, . . . , ws. Note that τ1 does assign values to at least s variables not assigned by ρ, and
that from τ1 we can ﬁnd term1 (as this is the ﬁrst true term in f
|τ1) and then using w1 recover
τ2 and continue in this way until we recover the original assignment ρ. Thus this mapping is a
one-to-one map from Tt,s to Z

p13.5 (239)

2ks. (cid:4)

0, 1, ?

× {

}

13.2 Circuits With “Counters”:ACC

One way to extend the AC0 lowerbounds of the previous section was to deﬁne a more general class
of circuits. What if we allow more general gates? The simplest example is a parity gate. Clearly,
an AC0 circuit provided with parity gates can can compute the parity function. But are there
still other functions that it cannot compute? Razborov proved the ﬁrst such lowerbound using his
Method of Approximations. Smolensky later extended this work and clariﬁed this method for the
circuit class considered here.

Normally we think of a modular computation as working with numbers rather than bit, but it

is suﬃcient to consider modular gates whose output is always 0/1.

Definition 13.3 (modular gates)
For any integer m, the M ODm gate outputs 0 if the sum of its inputs is 0 modulo m, and 1
otherwise.

Definition 13.4 (ACC)
For integers m1, m2, . . . , mk > 1 we say a language L is in ACC0[m1, m2, . . . , mk] if there exists a
with constant depth and polynomial size (and unbounded fan-in) consisting of
circuit family

,
∧

and M ODm1, . . . , M ODmk gates accepting L.

,
∨
The class ACC0 contains every language that is in ACC0(m1, m2, . . . , mk) for some k

¬

Cn}

{

0 and

≥

m1, m2, . . . , mk > 1.

Good lowerbounds are known only when the circuit has one kind of modular gate.

Theorem 13.5 (Razborov,Smolensky)
For distinct primes p and q, the function M ODp is not in ACC0(q).

We exhibit the main idea of this result by proving that the parity function cannot be computed

by an ACC0(3) circuit.
Proof: The proof proceeds in two steps.

Step 1. In the ﬁrst step, we show (using induction on h) that for any depth h M OD3 circuit on
n inputs and size S, there is a polynomial of degree (2l)h which agrees with the circuit on
S/2l fraction of the inputs. If our circuit C has depth d then we set 2l = n1/2d to obtain
1
a degree √n polynomial that agrees with C on 1

S/2n1/2d/2 fraction of inputs.

−

−

Step 2 We show that no polynomial of degree √n agrees with M OD2 on more than 49/50 fraction

of inputs.

DRAFT

Web draft 2007-01-08 21:59



<!-- pdf-page: 6 -->
p13.6 (240)

13.2. CIRCUITS WITH “COUNTERS”:ACC
Together, the two steps imply that S > 2n1/2d/2/50 for any depth d circuit computing M OD2,

thus proving the theorem. Now we give details.
Step 1. Consider a node g in the circuit at a depth h . (The input is assumed to have depth 0.)
, xn) over
If g(x1,
, xn) is the function computed at this node, we desire a polynomial ˜g(x1,
GF (3) with degree (2l)h, such that g(x1, . . . , xn) = ˜g(x1, . . . , xn) for “most” x1, . . . , xn ∈ {
0, 1
.
}
n
.
0, 1
GF (3), polynomial ˜g takes a value in
0, 1
We will also ensure that on every input in
}
{
}
{
This is without loss of generality since we can just square the polynomial. (Recall that the elements
of GF (3) are 0,

1, 1 and 02 = 0, 12 = 1 and (

1)2 = 1.)

· · ·

· · ·

⊆

We construct the approximator polynomial by induction. When h = 0 the “gate” is an input
wire xi, which is exactly represented by the degree 1 polynomial xi. Suppose we have constructed
approximators for all nodes up to height h

1 and g is a gate at height h.

−

−

−

1. If g is a NOT gate, then g =

1 or less.
f1 for some other gate f1 that is at height h
The inductive hypothesis gives an approximator ˜f1 for f1. Then we use ˜g = 1
˜f1 as the
approximator polynomial for g; this has the same degree as ˜f1. Whenever ˜f1 = f1 then ˜g = g,
so we introduced no new error.

−
−

¬

2. If g is a M OD3 gate with inputs f1, f2, . . . , fk, we use the approximation ˜g = (
−

1 < (2l)h. Since 02 = 0 and (

(2l)h

˜fi)2. The
k
i=0
1)2 = 1, we introduced

degree increases to at most 2
no new error.

×

−

P

3. If g is an AND or an OR gate, we need to be more careful. Suppose g =

I ˜fi. For an OR gate g =
approach would be to replace g with the polynomial Πi
∈
Morgan’s law gives a similar naive approximator 1
i
∈
these multiply the degree by k, the fanin of the gate, which could greatly exceed 2l.

I (1

−

−

k
i=0fi. The naive
∧
k
i=0fi De
∨
˜fi). Unfortunately, both of

Q

The correct solution involves introducing some error. We give the solution for OR; De Mor-
gan’s law allows AND gates to be handled similarly.

fi}
{
, Sl of

k
i=0fi, then g = 1 if and only if at least one of the fi = 1. Furthermore, by the random
If g =
∨
subsum principle (see Section ?? in Appendix A) if any of the fi = 1, then the sum (over
GF (3)) of a random subset of

is nonzero with probability at least 1/2.

{

· · ·

1, . . . , k

. Compute the l polynomials (

˜fj)2,
Randomly pick l subsets S1,
each of which has degree at most twice that of the largest input polynomial. Compute
the OR of these l terms using the naive approach. We get a polynomial of degree at most
1 = (2l)h. For any x, the probability over the choice of subsets that this polynomial
2l
diﬀers from OR( ˜f1, . . . , ˜fk) is at most 1
2l . So, by the probabilistic method, there exists a choice
for the l subsets such that the probability over the choice of x that this polynomial diﬀers from
OR( ˜f1,
2l . We use this choice of the subsets to construct the approximator.

, ˜fk) is at most 1

(2l)h

P

×

Si

}

−

∈

j

· · ·

Applying the above procedure for each gate gives an approximator for the output gate of degree
(2l)d where d is depth of the entire circuit. Each operation of replacing the gate by its approximator
polynomial introduces error on at most 1/2l fraction of all inputs, so the overall fraction of erroneous
inputs for the approximator is at most S/2l. (Note that errors at diﬀerent gates may aﬀect each
other. Error introduced at one gate may be cancelled out by errors at another gate higher up. We

Web draft 2007-01-08 21:59

DRAFT



<!-- pdf-page: 7 -->
13.2. CIRCUITS WITH “COUNTERS”:ACC

p13.7 (241)

are being pessimistic in applying the union bound to upperbound the probability that any of the
approximator polynomials anywhere in the circuit miscomputes.)
Step 2. Suppose that a polynomial f agrees with the M OD2 function for all inputs in a set
G0 ⊆
becomes some subset G of
which still has degree √n. Moreover,

G0|
|
1.) Then, G0
Consider the change of variables yi = 1 + xi (mod 3). (Thus 0
n, and f becomes some other polynomial, say g(y1, y2, . . . , yn),
}

0, 1n. If the degree of f is bounded by √n, then we show

49
2n.
50
1 and 1

→ −

1, 1

{−

(cid:0)
→

<

(cid:1)

M OD2(x1, x2, . . . , xn) =

1
0
(

Πn
Πn

1
i=1yi =
−
i=1yi = 1

⇒
⇒

(2)

G

∈

0, 1,

= 3|

50)2n

1
−

3(49

FG|
|

FG| ≤
|

. Clearly,
}

|, and we will show

Thus g(y1, y2, . . . , yn), a degree √n polynomial, agrees with Πn
i=1yi on G. This is decidedly odd,
and we show that any such G must be small. Speciﬁcally, let FG be the set of all functions
S : G

FG, there exists a polynomial gS which is a sum of monomials aI
G.

→ {
Lemma 13.6
For every S
n
2 + √n such that gS(x) = S(x) for all x
I
|
Proof: Let ˆS : GF (3)n
GF (3) be any function which agrees with S on G. Then ˆS can be
written as a polynomial in the variables yi. However, we are only interested in its values on
i has, without loss of
(y1, y2, . . . , yn)
∈ {−
1. Thus ˆS is a polynomial of degree at most n. Now consider any of its monomial
generality, ri ≤
terms Πi
∈

i = 1 and so every monomial Πi
∈

→
n, when y2
}

> n/2. We can rewrite it as

, whence Step 2 follows.

I yi of degree

I yi where

I yri

1, 1

| ≤

i
∈

Q

∈

I
|

|

Πi
∈

I yi = Πn

i=1yiΠi
∈

¯I yi,

which takes the same values as g(y1, y2, . . . , yn)Πi
∈
has degree at most n
2 + √n. (cid:4)

¯I yi over

1, 1
}

{−

(3)

n. Thus every monomial in ˆS

To conclude, we bound the number of polynomials whose every monomial with a degree at most

n
2 + √n. Clearly this number is #polynomials

3#monomials, and

≤

N

{

1
⊆ {

#monomials

≤

≤

(cid:12)
(cid:12)
(cid:12)

· · ·
n
i

(cid:18)

(cid:19)

n
Xi
2
≤

+√n

N

n

}| |

| ≤

n
2

+ √n

(cid:12)
(cid:12)
(cid:12)

Using knowledge of the tails of a binomial distribution (or alternatively, direct calculation),

49
50

2n

≤

(cid:4)

DRAFT

Web draft 2007-01-08 21:59

(4)

(5)

(6)



<!-- pdf-page: 8 -->
p13.8 (242)

13.3. LOWERBOUNDS FOR MONOTONE CIRCUITS

13.3 Lowerbounds for monotone circuits

A Boolean circuit is monotone if it contains only AND and OR gates, and no NOT gates. Such a
circuit can only compute monotone functions, deﬁned as follows.

Definition 13.7
For x, y
0, 1
}

0, 1

n, we denote x 4 y if every bit that is 1 in x is also 1 in y. A function f :
}
is monotone if f (x)

f (y) for every x 4 y.

∈ {

0, 1
{

n
}

→

{
Remark 13.8
An alternative characterization is that f is monotone if for every input x, changing a bit in x from
0 to 1 cannot change the value of the function from 1 to 0.

≤

It is easy to check that every monotone circuit computes a monotone function, and every mono-
tone function can be computed by a (suﬃciently large) monotone circuit. CLIQUE is a monotone
function since adding an edge to the graph cannot destroy any clique that existed in it. In this
section we show that the CLIQUE function can not be computed by polynomial (and in fact even
subexponential) sized monotone circuits:

Theorem 13.9 ([Raz85b, AB87])
Denote by CLIQUEk,n :
n-vertex graph G outputs 1 iﬀ G contains a k-vertex clique.
There exists some constant (cid:15) > 0 such that for every k

(n
2)
}

0, 1
{

→ {

0, 1

}

size less than 2(cid:15)√k that computes CLIQUEk,n.

≤

be the function that on input an adjacency matrix of an

n1/4, there’s no monotone circuit of

We believe CLIQUE does not have polynomial-size circuits even allowing NOT gates (i.e., that
NP * P/poly). In fact, a seemingly plausible approach to proving this might be to show that
for every monotone function f , the monotone circuit complexity of f is polynomially related to
the general (non-monotone) circuit complexity. Alas, this conjecture was refuted by Razborov
([Raz85a], see also [Tar88]).

13.3.1 Proving Theorem 13.9

Clique Indicators

{

⊆

0, 1
}

[n], let CS denote the function on

To get some intuition why this theorem might be true, lets show that CLIQUEk,n can’t be computed
(or even approximated) by subexponential monotone circuits of a very special form. For every
(n
2) that outputs 1 on a graph G iﬀ the set S is a clique
S
=k CS. We’ll now
in G. We call CS the clique indicator of S. Note that CLIQUEk,n =
prove that CLIQUEk,n can’t be computed by an OR of less than n√k/20 clique indicators.
K
|

= k at
|
⊆
be the following
random, and output the graph that has a clique on K and no other edges. Let
1] at random, and place an edge
distribution on n-vertex graphs: choose a function c : [n]
between u and v iﬀ c(u)
) = 0.
The fact that CLIQUEn,k requires an OR of at least n√k/20 clique indicators follows immediately
from the following lemma:

be the following distribution on n-vertex graphs: choose a set K

= c(v). With probability one, CLIQUEn,k(

) = 1 and CLIQUEn,k(

[n] with

Let

→

W

N

N

[n],

[k

−

Y

Y

⊆

S

S

|

|

Web draft 2007-01-08 21:59

DRAFT

6

