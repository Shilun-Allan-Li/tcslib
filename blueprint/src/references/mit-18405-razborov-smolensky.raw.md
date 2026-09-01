<!-- generated-by: proofmatch local extraction -->
<!-- source-pdf-sha256: d3f46480810510b7214c577966db129b442258da3e59cd7c9a4052b901cc9eba -->
<!-- extractor: pdfminer.six v20260107 -->

<!-- pdf-page: 1 -->
18.405J/6.841J: Advanced Complexity Theory

Spring 2016

(cid:47)(cid:72)(cid:70)(cid:87)(cid:88)(cid:85)(cid:72)(cid:3)(cid:26)(cid:29)(cid:3)(cid:53)(cid:68)(cid:93)(cid:69)(cid:82)(cid:85)(cid:82)(cid:89)(cid:16)(cid:54)(cid:80)(cid:82)(cid:79)(cid:72)(cid:81)(cid:86)(cid:78)(cid:92)

Scribe: Brian Chen

Scribe Date: Spring 2016  

Mohammad Bavarian

1 Intro

In the last lecture, we showed that PARITY ̸2 AC0: in other words, there is no bounded-depth,
polynomial-size circuit that computes PARITY.

Today, we will improve the theorem. Broadly speaking, there are two ways we might try to do so:
qualitatively (proving lower bounds on stronger circuit models) and quantitatively (proving tighter
bounds with the same circuit models). We will pursue the former direction today, in accordance
with the Sipser program, the direction of complexity theory research starting from the 80s and 90s.
The goal is to work our way up to understanding P=poly and from there P.

2 New Circuit Models

Here are some complexity classes that are targets of the Sipser program after AC0, listed as a series
of inclusions:

AC0 (cid:18) AC0[m] (cid:18) ACC0 (cid:18) TC0:

The complexity classes AC0[m] and ACC0 are based on circuits with bounded depth, just like
circuits in AC0, but they are more powerful because their circuits may include mod-m gates:
De(cid:12)nition 1. Let m (cid:21) 2 be an integer; then a mod-m gate is a gate that accepts unbounded fan-in
and outputs 1 iﬀ the number of inputs that are 1 is not 0 mod m. Formally, on inputs y1; : : : ; yk:

Modm(y1; : : : ; yk) =

{

0
1

if
if

∑
∑

(cid:17)

0 mod m
yi
yi ̸(cid:17) 0 mod m

:

De(cid:12)nition 2. For an integer m (cid:21) 2, the class AC0[m]
depth polynomial-size circuits with AND, OR, NOT, and mod-m gates.

consists of languages decidable by bounded-

The complexity class ACC0 is like AC0, except that it allows mod-m gates for arbitrary m instead
of just a (cid:12)xed one. The class TC0 instead uses threshold gates, which are more powerful than AND,
OR, and mod-m gates. Neither of these classes are involved in today’s main proof, though, so we
defer discussion and formal de(cid:12)nitions of these stronger classes to the end.

3 Main Theorem

Today, we will show the following theorem:

1



<!-- pdf-page: 2 -->
Theorem 3.

PARITY ̸2 AC0[3]:

In fact, any depth-d circuit using AND, OR, NOT, and mod-3 gates that computes PARITY must
have

SIZE (cid:21) 2Ω(n1=2d):

Our strategy will be to approximate any circuits in AC0[3] with a low-degree polynomial over F3,
and then to prove that low-degree polynomials cannot approximate PARITY that well, leading to
a contradiction.

3.1 Arithmetization

In the proof, we will view f0; 1gn as a subset of Fn

3 (where F3 is the (cid:12)eld with 3 elements).

Given a circuit C : f0; 1gn ! f
on inputs in the set f0; 1gn.

0; 1g, we will develop a polynomial C : Fn
3

~

! F3 that behaves like C

Now, there is a na(cid:127)(cid:16)ve way to do this:

(cid:15) Given a boolean b, computing NOT is just 1 (cid:0) b;

(cid:15) Given a list of booleans b1; b2; : : : ; bk 2 f0; 1g, computing AND is just taking the product

b1b2 (cid:1) (cid:1) (cid:1) bk;

(cid:15) Given a list of booleans b1; b2; : : : ; bk 2 f0; 1g, computing OR is, by de Morgan’s law, just

1 (cid:0) (1 (cid:0) b1) (cid:1) (cid:1) (cid:1) (1 (cid:0) bk);

(cid:15) Given a list of booleans b1; b2; : : : ; bk 2 f0; 1g, computing mod-3 is just the square of the sum
(b1 + b2 + (cid:1) (cid:1) (cid:1) + bk)2 (since 02 (cid:17) 0 and 12 (cid:17) 22 (cid:17) 1 mod 3; note that this generalizes to other
moduli m by taking the m (cid:0) 1th power in Fm).

The problem with this plan arises in the simulation of AND and OR gates when those gates are
not narrow. Unbounded fan-in can cause our polynomials to have very high degree, but we want
low-degree polynomials because we understand them better. So we will settle for an approximation,
~a C that behaves like C on a large fraction of, but not all, inputs.

3.2 Proof

We will divide our proof into two lemmas, which we will prove later. First, a de(cid:12)nition:

De(cid:12)nition 4. A polynomial p : Fn
3

! F

3 is called proper if it maps f0; 1g to f0; 1g.

n

Lemma 5. Let t be an integer, t (cid:21) 1, and let C be an AC0[3] circuit of depth d. Then there
exists a proper polynomial of degree at most (2t)d which agrees with C on at least the fraction
1 (cid:0) SIZE(C)=2t of all inputs in f0; 1gn.

In this lemma, t is a parameter which we will adjust later.

2



<!-- pdf-page: 3 -->
Lemma 6. Let g : Fn
3
PARITY on at most 49=50 of inputs in f0; 1gn.

! F3 be a proper polynomial with degree

p

(cid:20) n. Then g agrees with

(The constant 49=50 is not tight, but rather unimportant. For better results, we’d be more inter-
ested in improving

n, say, to n2=3.)

p

Assuming these two lemmas, we now give the proof of the main theorem:

Proof. Suppose for the sake of contradiction that PARITY 2 AC0[3], so that there is some (cid:12)xed
positive integer d such that, for all input sizes, there is a depth-d AC0[3] circuit that computes
PARITY. Let

and apply Lemma 5; then there is a proper polynomial p with degree at most
PARITY on 1 (cid:0) SIZE(C)

n1=2d of inputs. Then, by lemma 6,

p

n that agrees with

2

2

which implies

t =

n1=2d
2

SIZE(C)
n1=2d
2

2

(cid:21) 1
50

1

2n =2d

;

SIZE(C) (cid:21)

n1=2d
2

2

;

1
50

contradicting the polynomial size of C and concluding the proof. More generally, the same proof
shows that any bounded-depth circuit using AND, OR, NOT, and mod-3 gates that computes
PARITY must have at least this size.

4 Proof of First Lemma

Without loss of generality, assume the circuit consists only of mod-3, NOT, and OR gates. (AND
gates can be rewritten as a combination of one OR gate and many NOT gates using de Morgan’s
laws. Note that this increases the SIZE of the circuit by adding many NOT gates, but, as we shall
see, NOT gates do not aﬀect the size of our construction, so this is (cid:12)ne.)

Taking each layer in turn, we will approximate each gate with a low-degree polynomial. Speci(cid:12)cally,
we will approximate each gate in layer k (counting from the bottom) with a polynomial of degree
at most (2t)k.

Clearly, every input on the bottom layer is just a degree-1 polynomial, a monomial of the form xi,
so the base case works.

Now, suppose that we have approximated every polynomial in layer k with a polynomial of degree
at most (2t)k, and we wish to continue this to the next layer. Consider any gate on the (k + 1)th
layer:

(cid:15)

If it is a NOT gate and its input has been approximated with the polynomial f , we simply
approximate the output as the polynomial 1 (cid:0) f . This is an exact simulation of the NOT
gate! Also, it does not increase the degree of the input polynomial, which is why adding NOT
gates is unimportant.

~

~

3



<!-- pdf-page: 4 -->
(cid:15)

If it is a mod-3 gate and its inputs have been approximated with the polynomials fi, we
simply approximate the output as the polynomial
)

(

~

∑s

2

~fi

:

k=1

The degree of this polynomial is at most 2(2t)k (cid:21) (2t)k+1. This is also an exact simulation
of the mod-3 gate: if the inputs are all in f0; 1g, then the sum counts exactly how many of
them are 1 and the (cid:12)nal squaring maps 0 to 0 and non-zero to 1.

(cid:15) If it is an OR gate, we will (cid:12)nally need to use approximation. To exactly simulate an OR

gate with s inputs, we’d have to use something like the polynomial

1 (cid:0)

∏
s

i=1

(1

(cid:0)

~
fi);

which has degree s(2t)k ≫ (2t)k+1, so this does not work (unless the gate is narrow enough,
s (cid:21) 2t; but we cannot rely on that.) Instead, we will approximate the gate as follows. We
pick t random subsets L1; L2; : : : ; Lt (cid:18) f1; 2; : : : ; sg (where each element has an independent
1=2 chance of being in each subset), and approximate the OR gate with the polynomial

~f = 1 (cid:0)

0

0

@ (cid:0)
1

@

∏
t

i=1

∑

m

2Ti

1

2

1

A

A

:

~
fm

~

0, then

We observe that, if all inputs are
ery multiplicand in the product
every
is 1, and f = 0, which is correct. If any input, say fj, is 1, then each sum m2T fm has
probability (cid:21) 1=2 of being nonzero (Ti has probability 1=2 of including or excluding j, and
those give diﬀerent sums, of which at least one is nonzero); if any sum is nonzero,
then its
square is 1, the corresponding multiplicand is 0, and f = 1.
Thus, for all inputs, the OR simulation is correct with probability (cid:21) 1 (cid:0) 1=2t.

sum is 0,

∑

ev

~

~

~

i

Now, by applying a union-bound, we get a polynomial that disagrees with at most SIZE(C)=2t of
all possible inputs, and we are done! (Note that, in bounding the error, we did not need the full
size of the circuit, only the number of AND and OR gates.)

The proof again suggests the important about distinguishing between narrow and wide gates:
simulation of narrow OR gates can be done exactly in the degree we’ve allotted ourselves, whereas
simulation of wide OR gates is where the random selection becomes important.

4.1 Proof of Second Lemma

We recall the lemma statement: Let g be a proper polynomial with degree
with PARITY on at most 49/50 of inputs.

p

(cid:20) n. The g agrees

A natural question is where the fraction 49=50 comes from.
bound on the binomial distribution, which we will not prove:

It turns out it arises from a weak

4



<!-- pdf-page: 5 -->
Fact:

p
∑ n

n=2+

i=0

(

)

n
i

49(cid:20)
50

(cid:1) n:
2

Now, let us change bases f0; 1g ! f(cid:0)1; 1gn. More precisely, consider the polynomial

q(x1; : : : ; xn) = 1 + g(x1 + 1; : : : ; xn + 1):

∏

Then we observe that q maps f(cid:0)1; 1gn to f(cid:0)1; 1g, and after the change of base, PARITY becomes
xi. So ∏for each input (x1; : : : ; xn) 2 f0; 1gn, g agrees with
the simple product of every variable,
PARITY iﬀ q(x1 + 1; : : : ; xn + 1) agrees with
(xi + 1). Thus, we want to understand for how
many inputs the equation q(x1; : : : ; xn) = xi can hold.
! 3 and extend
Let G = fu 2 f(cid:0)1; 1gn j q(u) =
it to p : Fn
! F3. Note that, over (cid:12)nite (cid:12)elds, every function can be expressed as a polynomial,
3
so assume p is a polynomial. The idea below is that the properties of q and F3 will allow us to
simplify p to a low-degree polynomial without aﬀecting its behavior on G, which bounds the number
of possible ways one could have picked a function G ! F3 at the start, which in turns bounds jGj.

x u xg. Now, pick an arbitrary function p : G
2

∏

∏

F

First, express p as a sum of monomials:

∑

p =

a

i
i1;i2;:::;inx 1

1 xi2

2

(cid:1) (cid:1) (cid:1) xin
n :

Since we only care about p’s behavior on
i = 1 for any xi in this set, we
can reduce every ij mod 2. As a result, all ij 2 f0; 1g, and p becomes multilinear without changing
its behavior on G.

G 2 f(cid:0)1; 1gn, and every x2

Now, we can express p as the sum

∑

∏

p =

aS

xi

S

(cid:18)[n]

2S
i

(where [n] = f1; 2; : : : ; ng). Consider some S such that jSj (cid:21) n=2. Then

∏

∏

=

xi (cid:1)

∏

2S
i

2
i

S

i2[n]

xi;

again because every xi that is multiplied twice in the RHS simpli(cid:12)es to 1. By replacing the (cid:12)nal
product with q, we have:

∏

∏

=

xi (cid:1) q(x1; : : : ; xn)

2S
The degree of the RHS is now (cid:20) n=2 +
means that, for every term with degree > n=2 +
(cid:20) n=2 +

n without aﬀecting the behavior of p on G.

p

p

p

i

2S
i
n. Again, this equation is true for any (xi : : :) 2 G. This
n in p, we can replace it with a term of degree

Now, the space of remaining polynomials p are those polynomials that are multilinear and have
total degree (cid:20) n=2 +
(cid:20) 49 2n. But the
n. So its dimension (over F3) is less than
dimension over F3 of the choices for the original function p : G ! F3 is just jGj. Therefore,

p
∑n=2+
i=1

p

n
i

50

(

)

n

as desired.

jGj (cid:20)

49
50

2n;

5



<!-- pdf-page: 6 -->
5 Other Comments

5.1 Generalization

The main proof today generalizes to proving that mod-p gates are not in AC0[q] for any distinct
primes p; q. However, it does not generalize to composites, and indeed, when m is composite, it was
considerably diﬃcult to prove things about AC0[m]. For example, no good bounds were known for
AC0[6] for 30 years; this only changed recently. (Note that AC0[6] is more powerful than AC0[2]
and AC0[3], since a mod-6 gate can simulate a mod-2 gate by taking three copies of every input
and a mod-3 gate by taking two copies of every input.)

5.2 ACC0 and TC0

We de(cid:12)ne the stronger circuit models mentioned at the start of the notes:

De(cid:12)nition 7. ACC0 is the class of languages decidable by bounded-depth polynomial-size circuits
with AND, OR, NOT, and mod-m gates for any m. Equivalently, since only (cid:12)nitely many types of
mod-m gates can be used in any given circuit,

∪

ACC0 =

m1;:::;m

k2N

AC0[m1; m2; : : : ; mk]:

(For more than one integer m1; m2 : : : (cid:21) 2, the class AC0[m1; m2; : : :] consists of languages decidable
by bounded-depth polynomial-size circuits with AND, OR, NOT, and mod-mi gates for any i.)

De(cid:12)nition 8. Let m be an integer. A threshold gate is a gate that accepts unbounded fan-in and
outputs 1 iﬀ the number of inputs that are 1 is greater than or equal to m.

De(cid:12)nition 9. TC0 is the class of languages decidable by bounded-depth polynomial-size circuits
with threshold gates.

Remark.
powerful than AND gates, OR gates, and mod-m gates.

In our models of bounded-depth polynomial-size circuits, threshold gates are more

(cid:15) AND gates and OR gates are special cases of threshold gates, where m is set to either the

number of inputs or 1, respectively.

(cid:15) Mod-m gates can be built with a polynomial number of threshold gates and NOT gates
arranged with bounded depth. First, note that we can determine using threshold gates
whether the number of inputs that are 1 is exactly k for some k: we just copy all inputs
twice and test whether the number of true inputs is (cid:21) k and ̸(cid:21) k + 1 Suppose the number of
inputs is k. Then we can test whether the number of inputs that are true is 0; m; : : : for each
possible value it could take on; k is polynomial in n, so the number of possible values is also
only polynomial in n and the number of gates we need is also polynomial.

The consequence of all this is that TC0 is more powerful than ACC0.

6



<!-- pdf-page: 7 -->
5.3 Looking Forward

In the next lecture, we prove NEXP ̸(cid:18) ACC0, a result by Ryan Williams in 2010 that was the (cid:12)rst
result that went beyond today’s results.

It is also conjectured, but unproven, that MAJ ̸2 ACC0, where MAJ is the majority problem:
given a list of boolean inputs, is the majority of them true? Almost nothing is known about lower
bounds for TC0.

7



<!-- pdf-page: 8 -->
MIT OpenCourseWare
https://ocw.mit.edu

18.405J / 6.841J Advanced Complexity Theory

Spring 2016

For information about citing these materials or our Terms of Use, visit: https://ocw.mit.edu/terms.


