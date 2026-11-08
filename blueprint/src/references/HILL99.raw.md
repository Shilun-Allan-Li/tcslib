<!-- generated-by: proofmatch local extraction -->
<!-- source-pdf-sha256: 130039751e9f77848b6ddf8c5d97b0faf90a14f58860ce46a7f60fa0ab306bfb -->
<!-- extractor: pdfminer.six v20260107 -->

<!-- pdf-page: 1 -->
A Pseudorandom Generator

from any

One-way Function

Johan H(cid:23)astad

Russell Impagliazzo

Leonid A. Levin

Michael Luby

(cid:3)

y

z

x

Abstract

Pseudorandom generators are fundamental to many theoretical and applied aspects

of computing. We show how to construct a pseudorandom generator from

one-

any

way function. Since it is easy to construct a one-way function from a pseudorandom

generator, this result shows that there is a pseudorandom generator i(cid:11) there is a

one-way function.

Warning: Essentially this paper has been published in SIAM Journal on Com-

puting and is hence sub ject to copyright restrictions. It is for personal use

only.

1

Introduction

One of the basic primitives in the study of the interaction between randomness and feasible

computation is a pseudorandom generator.

Intuitively, a pseudorandom generator is a

(cid:3)

Department of Numerical Analysis and Computing Science, Royal Institute of Technology, Stockholm,

Sweden, email

. Research supported by the Swedish National Board for Technical

Johanh@nada.kth.se

Development.

y

Department of Computer Science, University of California at San Diego. Research partially done while

at U.C.Berkeley, email

. Research supported by NSF grant CCR 88-13632

Russel l@cs.ucsd.edu

z

Computer Science Department, Boston University, 111 Cummington St, Boston, MA 02215, email

Lnd@cs.bu.edu

. Research supported by NSF grant CCR-9015276.

x

International Computer Science Institute, Berkeley, California, and Computer Science Division, Uni-

versity of California at Berkeley, email

. Research partially done while on leave of

Luby@icsi.berkeley.edu

absence from the University of Toronto. Research supported by NSERC operating grant A8092, National

Science Foundation operating grant CCR-9016468, National Science Foundation operating grant CCR-

9304722, United States-Israel Binational Science Foundation grant No. 89-00312, United States-Israel

Binational Science Foundation grant No. 92-00226, and ESPRIT BR Grant EC-US 030.

1



<!-- pdf-page: 2 -->
polynomial time computable function g that stretches a short random string x into a

long string g(x) that \looks" random to any feasible algorithm, called an adversary. The

adversary tries to distinguish the string g(x) from a random string the same length as

g(x). The two strings \look" the same to the adversary if the acceptance probability

for both strings is essentially the same. Thus, a pseudorandom generator can be used

to e(cid:14)ciently convert a small amount of true randomness into a much larger number of

e(cid:11)ectively random bits.

The notion of randomness tests for a string evolved over time: from set-theoretic tests to

enumerable [Kol : 65], recursive and (cid:12)nally limited time tests. Motivated by cryptographic

applications, the seminal paper [BM : 82] introduces the idea of a generator which produces

its output in polynomial time such that its output passes a general polynomial time test.

The fundamental paper [Yao : 82] introduced the de(cid:12)nition of a pseudorandom generator

most commonly used today, and proves that this de(cid:12)nition and the original of [BM : 82]

are equivalent.

The robust notion of a pseudorandom generator, due to [BM : 82], [Yao : 82], should be

contrasted with the classical methods of generating random looking bits as described in,

e.g., [Knuth : 81]. In studies of classical methods, the output of the generator is considered

good if it passes a particular set of standard statistical tests. The linear congruential

generator is an example of a classical method for generating random looking bits that

pass a variety of standard statistical tests. However, [Boyar : 89] and [Kraw : 92] show

that there is a polynomial time statistical test which the output from this generator does

not pass.

The distinction between the weaker requirement that the output pass some particular

statistical tests and the stronger requirement that it pass all feasible tests is particularly

important in the context of many applications. As pointed out by [BM : 82], in crypto-

graphic applications the adversary must be assumed to be as malicious as possible, with

the only restriction on tests being computation time. A pseudorandom generator can be

directly used to design a private key cryptosystem secure against all such adversaries.

In the context of Monte Carlo simulation applications, a typical algorithm uses long ran-

dom strings, and a typical analysis shows that the algorithm produces a correct answer

with high probability if the string it uses is chosen uniformly. In practice, the long ran-

dom string is not chosen uniformly, as this would require more random bits than it is

typically reasonable to produce (and store). Instead, a short random string is stretched

into a long string using a simple generator such as a linear congruential generator, and

this long string is used by the simulation algorithm.

In general, it is hard to directly

analyze the simulation algorithm to prove that it produces the correct answer with high

probability when the string it uses is produced using such a method. A pseudorandom

generator provides a generic solution to this problem. For example, [Yao : 82] shows how

pseudorandom generators can be used to reduce the number of random bits needed for any

2



<!-- pdf-page: 3 -->
probabilistic polynomial time algorithm, and thus shows how to perform a deterministic

simulation of any polynomial time probabilistic algorithm in subexponential time based

on a pseudorandom generator. The results on deterministic simulation were subsequently

generalized in [BH : 89], [BFNW : 96].

Since the conditions are rather stringent, it is not easy to come up with a natural candidate

for a pseudorandom generator. On the other hand, there seem to be a variety of natural

examples of another basic primitive; the one-way function.

Informally, f is one-way if

it is easy to compute but hard on average to invert.

If P=NP then there are no one-

way functions, and it is not even known if P 6= NP implies there are one-way functions.

However, there are many examples of functions that seem to be one-way in practice and

that are conjectured to be one-way. Some examples of conjectured one-way functions

are the discrete logarithm problem modulo a large randomly chosen prime (see, e.g.,

[DH : 76]), factoring a number that is the product of two large randomly chosen primes

(see, e.g., [RSA : 78]), problems from coding theory (see, e.g., [McEl : 78], [GKL : 93]), and

the subset sum problem for appropriately chosen parameters (see, e.g., [IN : 96]).

The paper [BM : 82] is the (cid:12)rst to construct a pseudorandom generator based on a one-way

function. They introduce an elegant construction that shows how to construct a pseudo-

random generator based on the presumed di(cid:14)culty of the discrete logarithm problem.

The paper [Yao : 82] substantially generalizes this result by showing how to to construct a

pseudorandom generator from any one-way permutation. (Some of the arguments needed

in the proof were missing in [Yao : 82] and were later completed by [Levin : 87]. Also,

[Levin : 87] conjectured that a much simpler construction would work for the case of one-

way permutations, and this was eventually shown in [GL : 89].)

There are several important works that have contributed to the expansion of the condi-

tions on one-way functions under which a pseudorandom generator can be constructed.

[GMT : 82] and [Yao : 82] show how to construct a pseudorandom generator based on the

di(cid:14)culty of factoring, and this was substantially simpli(cid:12)ed in [ACGS : 88]. When f is a

one-way permutation, the task of inverting f (x) is to (cid:12)nd x. In the case when f is not

a permutation, the natural extension of successful inversion to (cid:12)nding any x

such that

0

f (x

) = f (x). The paper [Levin : 87] introduces one-way functions which remain one-way

0

after several iterations and shows them to be necessary and su(cid:14)cient for the construction

of a pseudorandom generator. The paper [GKL : 93] shows how to construct a pseudoran-

dom generator from any one-way function with the property that each value in the range

of the function has roughly the same number of preimages. This expanded the list of

conjectured one-way functions from which pseudorandom generators can be constructed

to a variety of non-number theoretic functions, including coding theory problems.

However, the general question of how to construct a pseudorandom generator from a one-

way function with no structural properties was left open. This paper resolves this question.

We give several successively more intricate constructions, starting with constructions for

3



<!-- pdf-page: 4 -->
one-way functions with a lot of structure and (cid:12)nishing with the constructions for one-way

functions with no required structural properties.

The current paper is a combination of the results announced in the conference papers

[ILL : 89] and [H(cid:23)as : 90].

1.1 Concepts and tools

Previous methods, following [BM : 82], rely on constructing a function that has an out-

put bit that is computationally unpredictable given the other bits of the output, but is

nevertheless statistically correlated with these other bits. [GL : 89] provide a simple and

natural input bit which is hidden from (a padded version of ) any one-way function. Their

result radically simpli(cid:12)es the previous constructions of pseudorandom generator from one-

way permutations, and in addition makes all previous constructions substantially more

e(cid:14)cient. We use their result in a fundamental way.

Our overall approach is di(cid:11)erent in spirit from previous constructions of pseudorandom

generators based on one-way functions with special structure. Previous methods rely on

iterating the one-way function many times, and from each iteration they extract a compu-

tationally unpredictable bit. The approach is to make sure that after many iterations the

function is still one-way. In contrast, as explained below in more detail, our approach con-

centrates on extracting and smoothing entropy in parallel from many independent copies

of the one-way function. Our overall construction combines this parallel approach with a

standard method for iteratively stretching the output of a pseudorandom generator.

The notion of computational indistinguishability provides one of the main conceptual tools

in our paper. Following [GM : 84] and [Yao : 82], we say that two probability distributions

D and E are computational ly indistinguishable if no feasible adversary can distinguish D

from E . In these terms, a pseudorandom generator is intuitively the following: Let g be

a polynomial time computable function that maps string of length n to longer strings

of length ‘

> n. Let X be a random variable that is uniformly distributed on strings

n

of length n and let Y be a random variable that is uniformly distributed on strings of

length ‘

. Then, g is a pseudorandom generator if g(X ) and Y are computationally

n

indistinguishable.

The Shannon entropy of a distribution is a good measure of its information content.

A fundamental law of information theory is that the application of a function cannot

increase entropy. For example, because X has n bits of entropy, g(X ) can also have

at most n bits of entropy (see Proposition 2.2.4). The work presented in this paper

focuses on a computational analog of Shannon entropy, namely computational entropy.

We say the computational entropy of g(X ) is at least the Shannon entropy of Y if g(X )

and Y are computationally indistinguishable. If g(X ) is a pseudorandom generator, the

4



<!-- pdf-page: 5 -->
computational entropy of g(X ) is greater than the Shannon entropy of its input X , and

in this sense g ampli(cid:12)es entropy.

We introduce the following generalizations of a pseudorandom generator based on com-

putational entropy. We say that g(X ) is a pseudoentropy generator if the computational

entropy of g(X ) is signi(cid:12)cantly more than the Shannon entropy of X . We say that g(X ) is

a false entropy generator if the computational entropy of g(X ) is signi(cid:12)cantly more than

the Shannon entropy of g(X ).

We show how to construct a false entropy generator from any one-way function, a pseu-

doentropy generator from any false entropy generator and (cid:12)nally a pseudorandom gener-

ator from any pseudoentropy generator. (The presentation of these results in the paper is

in reverse order.)

We use hash functions and their analysis in a fundamental way in our constructions. This

approach has its roots in [GKL : 93]. In [GL : 89], it turns out that the easily computable

bit that is hidden is the parity of a random subset of the input bits, i.e., the inner product

of the input and a random string. This random inner product can be viewed as a hash

function from many bits to one bit.

Due to its importance in such basic algorithms as primality testing, randomness has be-

come an interesting computational resource in its own right. Recently, various studies

for extracting good random bits from biased \slightly-random" sources that nevertheless

possess a certain amount of entropy have been made; these sources model the imperfect

physical sources of randomness, such as Geiger counter noise and Zener diodes, that would

have to actually be utilized in real life. (See [Blum : 84], [SV : 86], [Vaz : 87], [VV : 85],

[CG : 88], and [McIn : 87].) One of our main technical lemmas, (Lemma 4.5.1), can be

viewed as a hashing lemma which is used to manipulate entropy in various ways: it can

be viewed as a method for extracting close to uniform random bits from a slightly-random

source using random bits as a catalyst.

1.2 Outline

An outline of the paper is as follows:

In Section 2 we give notation, especially related to probability distributions and ensembles.

In Section 3, we de(cid:12)ne the basic primitives used in the paper and a general notion of

reduction between primitives. We spend a little more time on this than is conventional in

papers on cryptography, since we want to discuss the e(cid:11)ects of reductions on security in

quantitative terms.

Section 4 introduces the basic mechanisms for (cid:12)nding hidden bits and manipulating en-

5



<!-- pdf-page: 6 -->
tropy with hash functions. The main result of the section is a reduction from a false

entropy generator to a pseudorandom generator via a pseudoentropy generator.

In Section 5, we present a construction of a pseudorandom generator from a one-way

function where pre-image sizes can be estimated. Although such one-way functions are

very common, and so this is an important special case, the main reason for including this

is to develop intuition for general one-way functions.

Section 6 presents the most technically challenging construction, that of a false entropy

generator from any one-way function. Combined with Section 4, this yields the main result

of the paper, the construction of a pseudorandom generator from any one-way function.

In Section 7, we present a somewhat more direct and e(cid:14)cient construction of a pseudo-

random generator from any one-way function. It uses the ideas from Sections 4, 5, and

6, but avoids some redundancy involved in combining three generic reductions. Section 8

concludes by placing our results in the context of modern cryptographic complexity.

2 Basic notation

N is the set of natural numbers. If S is a set then ]S is the number of elements in S . If

S and T are sets then S n T is the set consisting of all elements in S that are not in T . If

a is a number, then jaj is the absolute value of a, dae is the smallest integer greater than

or equal to a, and log(a) is the logarithm base two of a.

Let x and y be bit strings. We let hx; yi denote the sequence x followed by y , and when

appropriate we also view this as the concatenation of x and y . If x 2 f0; 1g

then x

is

i

n

th

the i

bit of x, x

is hx

; : : : ; x

i, and x (cid:8) y is hx

(cid:8) y

; : : : ; x

(cid:8) y

i.

i;:::;j

i

j

1

1

n

n

An m (cid:2) n bit matrix x is indicated by x 2 f0; 1g

. We write x

to refer to the (i; j )-

(cid:2)

i;j

f

g

m

n

entry in x. We can also view x as a sequence x = hx

; : : : ; x

i of m strings, each of length

1

m

n, where in this case x

is the i

row of the matrix, or we can view x as a bit string of

i

th

length mn, which is the concatenation of the rows of the matrix.

The (cid:12) operation indicates matrix multiplication over GF[2]. If x 2 f0; 1g

appears to

n

the left of (cid:12) then it is considered to be a row vector, and if it appears to the right of

(cid:12) it is considered to be a column vector. Thus, if x 2 f0; 1g

and y 2 f0; 1g

then

n

n

x (cid:12) y =

x

(cid:1) y

mod 2. More generally, if x 2 f0; 1g

and y 2 f0; 1g

then x (cid:12) y

(cid:2)

(cid:2)

i=1

i

i

n

‘

m

m

n

is the ‘ (cid:2) n bit matrix, where the (i; j )-entry is r (cid:12) c, where r is the i

row of x and c is

th

P

th

the j

column of y .

6



<!-- pdf-page: 7 -->
2.1 Probability Notation

In general, we use capital and Greek letters to denote random variables and random

events. Unless otherwise stated, all random variables are independent of all other random

variables.

A distribution D on a (cid:12)nite set S assigns a probability D(x) (cid:21) 0 to each x 2 S , and thus

D(x) = 1. We say a random variable X is distributed according to D on S if for

x

S

2

all x 2 S , Pr[X = x] = D(x), and we indicate this by X 2

S . We write D : f0; 1g

to

‘

n

P

D

indicate that D is supported on strings of length ‘

. We sometimes, for convenience, blur

n

the distinction between a random variable and its distribution. If X

and X

are random

1

2

variables (that are not necessarily independent), then (X

jX

= x

) denotes the random

1

2

2

variable that takes on value x

with the conditional probability Pr[X

= x

jX

= x

] =

1

1

1

2

2

Pr[X

= x

^ X

= x

]= Pr[X

= x

].

1

1

2

2

2

2

If f is a function mapping S to a set T , then f (X ) is a random variable that de(cid:12)nes a

distribution E , where for all y 2 T , E (y) =

D(x). We let f (D) indicate the

distribution E .

x

S;f (x)=y

2

P

We let X 2

S indicate that X is uniformly distributed in S , i.e., for all x 2 S , Pr[X =

x] = 1=]S . We let U

indicate the uniform distribution on f0; 1g

, i.e., X is distributed

U

n

according to U

if X 2

f0; 1g

.

n

U

n

n

We sometimes want to indicate a random sample chosen from a distribution, and we do

this by using the same notation as presented above for random variables except that we

use lower case letters, i.e., x 2

S indicates that x is a (cid:12)xed element of S chosen according

to distribution D .

D

If X is a real-valued random variable, then E[X ] denotes the expected value X . If E is a

probabilistic event, then Pr[E ] denotes the probability that event E occurs.

De(cid:12)nition 2.1.1 (statistical distance)

Let D and E be distributions on a set S . The

statistical distance between D and E is

L

1

(D ; E ) =

jPr[D(x)] (cid:0) Pr[E (x)]j =2:

x

S

X

2

Proposition 2.1.2

For any function f with domain S and for any pair of distributions

D and E on S ,

(f (D); f (E )) (cid:20)

(D ; E ).

L

L

1

1

2.2 Entropy

The following de(cid:12)nition of entropy is from [Shan : 48].

7



<!-- pdf-page: 8 -->
De(cid:12)nition 2.2.1 (information and entropy)

Let D be a distribution on a set S . For

each x 2 S , de(cid:12)ne the information of x with respect to D to be

(x) = (cid:0) log(D(x)): Let

I

D

X 2

S . The (Shannon) entropy of D is

(D) = E[

(X )]: Let D

and D

be distributions

H

I

1

2

D

D

on S that are not necessarily independent, and let X

2

S and X

2

S . Then, the

1

2

1

2

D

D

conditional entropy of D

with respect to D

,

(D

jD

), is E

[

(X

jX

= x

)].

H

H

1

2

1

2

x

S

1

2

2

2

D

2

2

We sometimes refer to the entropy

(X ) of random variable X , which is equal to

(D).

H

H

We sometimes refer to the conditional entropy

(X

jX

) of X

conditioned on X

, which

H

1

2

1

2

is equal to

(D

jD

).

H

1

2

The following variant de(cid:12)nition of entropy is due to [Renyi : 70].

De(cid:12)nition 2.2.2 (Renyi entropy)

Let D be a distribution on a set S . The Renyi en-

tropy of D is

(D) = (cid:0) log(Pr[X = Y ]); where X 2

S and Y 2

S are independent.

H

Ren

D

D

There are distributions that have arbitrarily large entropy but have only a couple of bits

of Renyi entropy.

Proposition 2.2.3

H

H

For any distribution D ,

(D) (cid:20)

(D):

Ren

We sometimes use the following proposition implicitly. This proposition shows that a

function cannot increase entropy in a statistical sense.

Proposition 2.2.4

Let f be a function and let D be a distribution on the domain of f .

Then,

(f (D)) (cid:20)

(D).

H

H

The following de(cid:12)nition characterizes how much entropy is lost by the application of a

function f to the uniform distribution.

De(cid:12)nition 2.2.5 (degeneracy of

)

f

Let f : f0; 1g

! f0; 1g

and let X 2

f0; 1g

.

n

‘

n

n

The degeneracy of f is

(f ) =

(X jf (X )) =

(X ) (cid:0)

(f (X )):

D

H

H

H

n

U

2.3 Ensembles

We present all of our de(cid:12)nitions and results in asymptotic form. Ensembles are used to

make the asymptotic de(cid:12)nitions, e.g., to de(cid:12)ne primitives such as one-way functions and

pseudorandom generators, and to de(cid:12)ne the adversaries that try to break the primitives.

8



<!-- pdf-page: 9 -->
In all cases, we use n 2 N as the index of the ensemble and implicitly the de(cid:12)nition and/or

result holds for all values of n 2 N .

In our de(cid:12)nitions of ensembles, the input and output lengths are all polynomially related.

To specify this, we use the following.

De(cid:12)nition 2.3.1 (polynomial parameter)

We say parameter k

is a polynomial pa-

n

rameter if there is a constant c > 0 such that for al l n 2 N ,

1

c

(cid:20) k

(cid:20) cn

:

n

c

cn

We say k

is

-time polynomial parameter if in addition there is a constant c

> 0 such

P

n

0

that, for al l n, k

is computable in time at most c

n

.

n

0

0

c

In many uses of a polynomial parameter k

, k

is integer-valued, but it is sometimes the

n

n

case that k

is real-valued.

n

De(cid:12)nition 2.3.2 (function ensemble)

We let f : f0; 1g

! f0; 1g

denote a function

t

n

‘

n

ensemble, where t

and ‘

are integer-valued

-time polynomial parameters and where f

P

n

n

with respect to n is a function mapping f0; 1g

to f0; 1g

. If f is injective then it is

t

n

‘

n

a one-to-one function ensemble. If f is injective and ‘

= t

then it is a permutation

n

n

ensemble. We let f : f0; 1g

(cid:2) f0; 1g

! f0; 1g

denote a function ensemble with two

t

n

‘

n

m

n

inputs. In this case, we sometimes consider f as being a function of the second input for

a (cid:12)xed value of the (cid:12)rst input, in which case we write f

(y) in place of f (x; y).

x

De(cid:12)nition 2.3.3 (P-time function ensemble)

We say f : f0; 1g

(cid:2)f0; 1g

! f0; 1g

t

n

‘

n

m

n

is a T

-time function ensemble if f is a function ensemble such that, for al l x 2 f0; 1g

,

n

t

n

for al l y 2 f0; 1g

, f (x; y) is computable in time T

. We say f is a

-time function

P

‘

n

n

c

ensemble if there is a constant c such that, for al l n, T

(cid:20) cn

. We say f is a mildly non-

n

uniform

-time function ensemble if it is a

-time function ensemble except that it has

P

P

an additional input

cal led the advice, that is an integer-valued polynomial parameter

a

n

that is not necessarily

-time computable.

P

These de(cid:12)nitions generalize in a natural way to functions with more than two inputs.

Sometimes we describe functions that have a variable length inputs or outputs; in these

cases we implicitly assume that the string is padded out with a special blank symbol to

the appropriate length.

In some of our intermediate reductions, we use certain statistical quantities in order to

construct our new primitive. For example, we might use an approximation of the entropy

9



<!-- pdf-page: 10 -->
of a distribution in our construction of pseudoentropy generator. Although in many cases

these quantities are not easy to approximate, the number of di(cid:11)erent approximation values

they can take on is small. This is the reason for the de(cid:12)nition of a mildly non-uniform

-

P

time function ensemble in the above de(cid:12)nition. In all the de(cid:12)nitions we give below, e.g., of

one-way functions, false entropy generators, pseudoentropy generators, and pseudorandom

generators, there is also an analogous mildly non-uniform version. In Proposition 4.8.1,

we show how to remove mild non-uniformity in the (cid:12)nal construction of a pseudorandom

generator.

De(cid:12)nition 2.3.4 (range and preimages of a function)

Let f : f0; 1g

! f0; 1g

be

n

‘

n

a function ensemble. With respect to n, de(cid:12)ne

range

= ff (x) : x 2 f0; 1g

g:

f

n

For each y 2 range

, de(cid:12)ne

f

pre

(y) = fx 2 f0; 1g

: f (x) = yg:

f

n

De(cid:12)nition 2.3.5 (regular function ensemble)

We say function ensemble f : f0; 1g

!

n

‘

n

f0; 1g

is (cid:27)

-regular if ]pre

(y) = (cid:27)

for al l y 2 range

.

n

n

f

f

De(cid:12)nition 2.3.6 (

D

)

P

Let f : f0; 1g

! f0; 1g

be a

-time function ensemble. For

f

~

n

‘

n

z 2 range

, de(cid:12)ne the approximate degeneracy of z as

f

~

D

(z ) =

log(]pre

(z ))

:

f

f

l

m

Notice that

(z ) is an approximation to within an additive factor of 1 of the quantity

f

~

D

n (cid:0)

I

f (X )

(z ). Furthermore, E[

(f (X ))] is within an additive factor of 1 of the degeneracy

f

~

D

of f . If f is a (cid:27)

-regular function then, for each z 2 range

,

(z ) is within an additive

n

f

f

~

D

factor of 1 of log((cid:27)

), which is the degeneracy of f .

n

De(cid:12)nition 2.3.7 (probability ensemble)

We let D : f0; 1g

denote a probability en-

‘

n

semble, where ‘

is an integer-valued

-time polynomial parameter and where D with

P

n

respect to n is a probability distribution on f0; 1g

.

‘

n

De(cid:12)nition 2.3.8 (P-samplable probability ensemble)

We let D : f0; 1g

denote a

‘

n

probability ensemble that, with respect to n, is a distribution on f0; 1g

that can be gen-

‘

n

erated from a random string of length r

for some r

, i.e., there is a function ensemble

n

n

f : f0; 1g

! f0; 1g

such that if X 2

f0; 1g

then f (X ) has the distribution D . We

r

n

‘

n

r

n

say D is T

-samplable probability ensemble if, for al l x 2 f0; 1g

, f (x) is computable in

n

U

r

n

time T

. We say D is

-samplable if f is a

-time function ensemble, and D is mildly

P

P

n

non-uniformly

-samplable if f is a mild ly non-uniform

-time function ensemble.

P

P

10



<!-- pdf-page: 11 -->
De(cid:12)nition 2.3.9 (copies of functions and ensembles)

Let k

be integer-valued

P

-

n

time polynomial parameter. If D : f0; 1g

is a probability ensemble then D

: f0; 1g

‘

n

k

n

‘

k

n

n

is the probability ensemble where, with respect to parameter n, D

consists of the con-

k

n

catenation of k

independent copies of D . Similarly, if f : f0; 1g

! f0; 1g

is a

n

m

n

‘

n

function ensemble then f

: f0; 1g

! f0; 1g

is the function ensemble where, for

k

n

m

k

n

n

‘

k

n

n

y 2 f0; 1g

,

(cid:2)

k

m

n

n

k

n

f

(y) = hf (y

); : : : ; f (y

)i;

1

k

n

3 De(cid:12)nitions of primitives and reductions

Primitives described in this paper include one-way functions and pseudorandom genera-

tors. The primitives we describe can be used in cryptographic applications, but are also

useful as described in the introduction in other applications. In the de(cid:12)nition of the prim-

itives, we need to describe what it means for the primitive to be secure against an attack

by an adversary. We (cid:12)rst introduce adversaries and security, and then describe the basic

primitives that we use thereafter.

3.1 Adversaries and security

An adversary is, for example, trying to invert a one-way function or trying to distinguish

the output of a pseudorandom generator from a truly random string. The time-suc-

cess ratio of a particular adversary is a measure of its ability to break the cryptographic

primitive. (Hereafter, we use \primitive" in place of the more cumbersome and sometimes

misleading phrase \cryptographic primitive".) The security of a primitive is a lower bound

on the time-success ratio of any adversary to break the primitive.

In the constructions of some primitives, we allow both private and public inputs. A public

input is part of the output of the primitive and is known to the adversary at the time

it tries to break the primitive. When we construct one primitive based on another, the

constructed primitive often has public inputs. At (cid:12)rst glance it could seem that these

public inputs are not useful because an adversary knows them at the time it tries to break

the constructed primitive. On the contrary, public inputs turn out to be quite useful.

Intuitively, this is because their value is randomly chosen, and the adversary cannot a

priori build into its breaking strategy a strategy for all possible values.

The private input to a primitive is not directly accessible to the adversary. The security

parameter of a primitive is the length of its private input. This is because the private

input to the primitive is what is kept secret from the adversary, and thus it makes sense

to measure the success of the adversary in terms of this.

11



<!-- pdf-page: 12 -->
De(cid:12)nition 3.1.1 (breaking adversary and security)

An adversary A is a function

ensemble. The time-success ratio of A for an instance f of a primitive is de(cid:12)ned as

R

t

n

= T

=sp

(A), where t

is the length of the private input to f , and where T

is the

n

n

n

n

worst case expected running time of A over al l instances parameterized by n, and sp

(A) is

n

the success probability of A for breaking f . In this case, we say A is

-breaking adversary

R

for f . We say f is

-secure if there is no

-breaking adversary for f .

R

R

A mildly non-uniform adversary for a mild ly non-uniform

-time function ensemble f

P

that has advice

is a function ensemble A which is given

as an additional input. The

a

a

n

n

success probability and time-success ratio for a mild ly non-uniform adversary is the same

as for uniform adversaries.

The de(cid:12)nition of the success probability sp

(A) for f depends on the primitive in question,

n

i.e., this probability is de(cid:12)ned when the primitive is de(cid:12)ned. Intuitively, the smaller the

time-success ratio of an adversary for a primitive, the better the adversary is able to break

the primitive, i.e., it uses less time and/or has a larger success probability.

The above de(cid:12)nitions are a re(cid:12)nement of de(cid:12)nitions that appear in the literature. Pre-

viously, an adversary was considered to be breaking if it ran in polynomial time and had

inverse polynomial success probability. The advantage of the de(cid:12)nition introduced here is

that it is a more precise characterization of the security of a primitive. This is important

because di(cid:11)erent applications require di(cid:11)erent levels of security. For some applications

polynomial security is enough (e.g.,

= t

) and for other applications better security

R

t

n

n

10

is crucial (e.g.,

= 2

, or even better

= 2

).

R

R

t

n

t

n

2

log

(t

)

n

p

t

n

3.2 One-way function

De(cid:12)nition 3.2.1 (one-way function)

P

Let f : f0; 1g

! f0; 1g

be a

-time function

t

n

‘

n

ensemble and let X 2

f0; 1g

. The success probability of adversary A for inverting f is

t

n

U

sp

(A) = Pr[f (A(f (X ))) = f (X )]:

n

Then, f is a

-secure one-way function if there is no

-breaking adversary for f .

R

R

A function cannot be considered to be \one-way" in any reasonable sense in case the time

to invert it is smaller than the time to evaluate it in the forward direction. Thus, for

example, if there is an O(t

)-breaking adversary for f then it is not secure at all. On

n

the other hand, an exhaustive adversary that tries all possible inputs to (cid:12)nd an inverse is

(1)

t

n

O

t

(cid:1) 2

-breaking. Thus, the range of securities that can be hoped for fall between these

n

two extremes.

12



<!-- pdf-page: 13 -->
3.3 Pseudorandom generator

The following de(cid:12)nition can be thought of as the computationally restricted adversary

de(cid:12)nition of statistical distance. The original idea is from [GM : 84] and [Yao : 82].

De(cid:12)nition 3.3.1 (computationally indistinguishable)

Let D : f0; 1g

and E : f0; 1g

‘

n

‘

n

be probability ensembles. The success probability of adversary A for distinguishing D and

E is

sp

(A) = j Pr[A(X ) = 1] (cid:0) Pr[A(Y ) = 1]j

n

where X has distribution D and Y has distribution E . D and E are

-secure compu-

R

tationally indistinguishable if there is no

-breaking adversary for distinguishing D and

R

E .

The following alternative de(cid:12)nition of computationally indistinguishable more accurately

re(cid:13)ects the tradeo(cid:11) between the running time of the adversary and its success probability.

In the alternative de(cid:12)nition, success probability is de(cid:12)ned as sp

(A) = (sp

(A))

. This

0

n

n

2

is because it takes 1=sp

(A) trials in order to approximate sp

(A) to within a constant

0

n

n

factor.

De(cid:12)nition 3.3.2 (computationally indistinguishable (alternative))

Exactly the same

as the original de(cid:12)nition, except the success probability of adversary A is sp

(A) =

0

n

(sp

(A))

.

n

2

In all cases except where noted, the strength of the reduction is the same under either

de(cid:12)nition of computationally indistinguishable, and we (cid:12)nd it easier to work with the

(cid:12)rst de(cid:12)nition. However, there are a few places where we explicitly use the alternative

de(cid:12)nition to be able to claim the reduction is linear-preserving.

Strictly speaking, there are no private inputs in the above de(cid:12)nition, and thus by default

we use n as the security parameter. However, in a typical use of this de(cid:12)nition, D is

the distribution de(cid:12)ned by the output of a

-time function ensemble (and thus D is

P

P

-

samplable), in which case the length of the private input to this function ensemble is

the security parameter. In some circumstances, it is important that both D and E are

P

-samplable, e.g., this is the case for Proposition 4.6.2.

The paper [Yao : 82] originally gave the de(cid:12)nition of a pseudorandom generator as below,

except that we parameterize security more precisely.

De(cid:12)nition 3.3.3 (pseudorandom generator)

P

Let g : f0; 1g

! f0; 1g

be a

-time

t

n

‘

n

function ensemble where ‘

> t

. Then, g is a

-secure pseudorandom generator if the

R

n

n

probability ensembles g(U

) and U

are

R

-secure computational ly indistinguishable.

t

n

‘

n

13



<!-- pdf-page: 14 -->
The de(cid:12)nition of a pseudorandom generator only requires the generator to stretch the

input by at least one bit. The following proposition provides a general way to produce

a pseudorandom generator that stretches by many bits from a pseudorandom generator

that stretches by at least one bit. This proposition appears in [BH : 89] and is due to O.

Goldreich and S. Micali.

Proposition 3.3.4

Suppose g : f0; 1g

! f0; 1g

is a pseudorandom generator that

n

n+1

stretches by one bit. De(cid:12)ne g

(x) = g(x), and inductively, for al l i (cid:21) 1,

(1)

(i+1)

(i)

(i)

g

(x) = hg(g

(x)

); g

(x)

i:

1;:::;n

n+1;:::;n+i

f

g

f

g

Let k

be an integer-valued

-time polynomial parameter. Then, g

is a pseudorandom

P

n

(k

)

n

generator. The reduction is linear-preserving.

On page 16 we give a formal de(cid:12)nition of reduction and what it means to be linear-preser-

ving, but intuitively it means that g

as a pseudorandom generator is almost as secure

(k

)

n

as pseudorandom generator g .

3.4 Pseudoentropy and false-entropy generators

The de(cid:12)nitions in this subsection introduce new notions (interesting in their own right)

which we use as intermediate steps in our constructions.

The di(cid:11)erence between a pseudorandom generator and a pseudoentropy generator is that

the output of a pseudoentropy generator doesn’t have to be computationally indistinguish-

able from the uniform distribution, instead it must be computationally indistinguishable

from some probability ensemble D that has more entropy than the input to the generator.

Thus, a pseudoentropy generator still ampli(cid:12)es randomness so that the output random-

ness is more computationally than the input randomness, but the output randomness is

no longer necessarily uniform.

De(cid:12)nition 3.4.1 (computational entropy)

P

Let f : f0; 1g

! f0; 1g

be a

-time

t

n

‘

n

function ensemble and let s

be a polynomial parameter. Then, f has

-secure computa-

R

n

tional entropy s

if there is a

-time function ensemble f

: f0; 1g

! f0; 1g

such that

P

n

0

m

n

‘

n

f (U

) and f

(U

) are

-secure computational ly indistinguishable and

(f

(U

)) (cid:21) s

.

R

H

t

n

0

m

n

0

m

n

n

De(cid:12)nition 3.4.2 (pseudoentropy generator)

P

Let f : f0; 1g

! f0; 1g

be a

-time

t

n

‘

n

function ensemble and let s

be a polynomial parameter. Then, f is a

-secure pseu-

R

n

doentropy generator with pseudoentropy s

if f (U

) has

-secure computational entropy

R

n

t

n

t

+ s

.

n

n

14



<!-- pdf-page: 15 -->
If f is a pseudorandom generator then it is easy to see that it is also a pseudoentropy

generator. This is because f (U

) and U

are computationally indistinguishable and by

t

n

‘

n

de(cid:12)nition of a pseudorandom generator, ‘

> t

. Consequently,

(U

) = ‘

(cid:21) t

+ 1,

H

n

n

n

n

‘

n

i.e., f is a pseudoentropy generator with pseudoentropy at least 1.

A false entropy generator is a further generalization of pseudoentropy generator. A false

entropy generator doesn’t necessarily amplify the input randomness, it just has the prop-

erty that the output randomness is computationally more than it is statistically.

De(cid:12)nition 3.4.3 (false entropy generator)

P

Let f : f0; 1g

! f0; 1g

be a

-time

t

n

‘

n

function ensemble and let s

be a polynomial parameter. Then, f is a

-secure false

R

n

entropy generator with false-entropy s

if f (U

) has

-secure computational entropy

R

n

t

n

H

(f (U

)) + s

.

t

n

n

Note that, in the de(cid:12)nition of computational entropy, the function ensemble f

that is

0

computationally indistinguishable from f is required to be

-time computable. This is

P

consistent with the de(cid:12)nition of a pseudorandom generator, where the distribution that

the pseudorandom generator is indistinguishable from is the uniform distribution. There

is also a non-uniform version of computational entropy where f

is not necessarily

-time

P

0

computable, and corresponding non-uniform versions of a pseudoentropy generator and

false entropy generator. It turns out to be easier to construct a false entropy generator

f where f

is not necessarily

-time computable from a one-way function than it is to

P

0

construct a false entropy generator f where f

is

-time samplable. Using this approach

P

0

and a non-uniform version of Proposition 4.6.2, [ILL : 89] describe a non-uniform reduction

from a one-way function to a pseudorandom generator. However, a uniform reduction

using Proposition 4.6.2 requires that f

be

-time computable. Thus, one of the main

P

0

di(cid:14)culties in our constructions below is to build a false entropy generator f where f

is

0

P

-time computable.

3.5 Hidden bits

In the construction of a pseudorandom generator from a one-way function, one of the key

ideas is to construct from the one-way function another function which has an output bit

that is computationally unpredictable from the other output bits (it is \hidden") and yet

statistically somewhat predictable from the other output bits. This idea is used in the

original construction of a pseudorandom generator from the discrete logarithm problem

[BM : 82] and has been central to all such constructions since that time.

De(cid:12)nition 3.5.1 (hidden bit)

Let f : f0; 1g

! f0; 1g

and b : f0; 1g

! f0; 1g

t

n

‘

n

t

n

be

-time function ensembles. Let D : f0; 1g

be a

-samplable probability ensemble,

P

P

t

n

15



<!-- pdf-page: 16 -->
let X 2

f0; 1g

, and let (cid:12) 2

f0; 1g . Then, b(X ) is

-secure hidden given f (X ) if

R

t

n

D

U

hf (X ); b(X )i and hf (X ); (cid:12) i are

-secure computational ly indistinguishable.

R

3.6 Reductions

All of the results presented in this paper involve a reduction from one type of primitive to

another.

We make the following de(cid:12)nitions to quantify the strength of reductions. The particu-

lar parameterization of security and the di(cid:11)erent quantitative measures of the security

preserving properties of a reduction are derived from [Luby : 96], [HL : 92].

Intuitively, a reduction constructs from a (cid:12)rst primitive f on inputs of length t

a second

n

primitive g

on inputs of length t

. The reduction also speci(cid:12)es an oracle TM M

such

0

n

(cid:1)

(f )

(

)

that if there is an adversary A for breaking g

then M

is an adversary for breaking

(f )

(A)

f . How much security is preserved by the reduction is parameterized by S .

De(cid:12)nition 3.6.1 (reduction)

Let t

and t

be polynomial parameters and let S : N (cid:2)

n

0

n

+

+

(

)

<

! <

. An S - reduction from primitive 1 to primitive 2 is a pair of oracle TMs g

(cid:1)

and M

so that,

(cid:1)

(

)

(cid:15) For each

-time function ensemble f : f0; 1g

! f0; 1g

that instantiates primitive

P

t

n

‘

n

(f )

t

‘

n

n

0

0

1, g

: f0; 1g

! f0; 1g

instantiates primitive 2.

(f )

(cid:15) g

is a

-time function ensemble, and on inputs of length t

, only makes cal ls to

P

f on inputs of length t

.

n

0

n

(f )

(cid:15) Suppose A is an adversary with time-success ratio

R

0

0

t

n

for g

on inputs of length

t

. De(cid:12)ne

= S (n;

). Then, M

is an adversary with time-success ratio

R

R

0

0

n

t

n

0

t

n

(A)

R

for f on inputs of length t

.

t

n

n

To discuss the security preserving properties of the reduction, we compare how wel l A

breaks g

to how wel l M

breaks f on inputs of similar size. We say the reduction is

(f )

(A)

(cid:15) linear-preserving if:

= N

(cid:1) O(

).

R

R

N

O

0

N

(1)

(cid:15) poly-preserving if:

= N

R

(cid:1)

R

.

O

N

O

0

(1)

(1)

(N )

O

(1)

(1)

(cid:15) weak-preserving if:

= N

R

(cid:1)

R

.

O

N

O

0

(1)

O

N

16



<!-- pdf-page: 17 -->
A mildly non-uniform reduction has the same properties except that g

and M

are both

(cid:1)

(cid:1)

(

)

(

)

al lowed access to an integer-valued polynomial parameter

that depends on f . The same

a

n

notions of security preservation apply to mild ly non-uniform reductions.

f can always be broken in time exponential in t

. Therefore, if

(cid:21) 2

, or even

R

0

n

0

t

n

t

n

(cid:10)(1)

(cid:10)(1)

t

n

(A)

n

R

0

0

t

n

(cid:21) 2

= 2

in the case of a weak-preserving reduction, M

can ignore the

oracle and break f by brute force. Therefore, we can assume without loss of generality

that

(cid:20) 2

.

R

0

0

t

n

t

n

Obvious from the de(cid:12)nition of reduction are the following propositions, that say that

security is preserved by reductions, and that reductions can be composed:

Proposition 3.6.2

If (g

; M

) is a (mild ly non-uniform) S -reduction from primitive 1

(cid:1)

(cid:1)

(

)

(

)

to primitive 2 and f is a (mild ly non-uniform)

-time function ensemble that instanti-

P

ates primitive 1 with security

, then g

is a (mild ly non-uniform)

-time function

R

P

t

n

(f )

ensemblethat instantiates primitive 2 with security

.

R

0

0

t

n

Proposition 3.6.3

If (g

; M

) is a ( mild ly non-uniform) S

-reduction from primitive

1

1

1

(

)

(

)

(cid:1)

(cid:1)

1 to primitive 2, and if (g

; M

) is a ( mild ly non-uniform) S

-reduction from primitive 2

2

(

)

(

)

(cid:1)

(cid:1)

2

2

(

)

(cid:1)

(

)

(cid:1)

(g

)

(M

)

2

2

to primitive 3, then (g

; M

), is a (mild ly non-uniform) S -reduction from primitive

1

1

1 to primitive 3, where S (N ; R) = S

(N ; S

(N ; R)).

2

1

Although we phrase our de(cid:12)nitions in terms of asymptotic complexity, one can easily

interpret them for (cid:12)xed length inputs in the context of an actual implementation, just as

one does for algorithm analysis.

Clearly, in standard situations, t

(cid:21) t

and

R

R

0

(cid:21)

, and the closer these two inequali-

0

n

n

t

n

0

t

n

ties are to equalities the more the security of f is transferred to g . We now describe how

the slack in these inequalities a(cid:11)ects the security preserving properties of the reduction.

The number of calls M

makes to A is invariably either a constant or depends polyno-

(A)

mially on the time-success ratio of A, and thus

is at most polynomial in

R

R

0

. The

t

n

0

t

n

slackness in this inequality turns out not to be the ma jor reason for a loss in security in

the reduction, instead it primarily depends on how much larger t

is than t

. If t

is much

0

n

n

0

n

larger than t

then

is much larger as a function of t

than

R

n

t

n

n

R

0

0

t

n

is as a function of t

.

0

n

We can formalize this as follows.

Proposition 3.6.4

17



<!-- pdf-page: 18 -->
(cid:15) If t

= t

, M

runs in time polynomial in n (not counting the running time of A),

0

n

n

(A)

and sp

(M

) = sp

(A)=n

, then the reduction is linear-preserving.

n

n

O

(A)

(1)

(cid:15) If t

= O(t

), M

runs in time polynomial in

, and sp

(M

) = sp

(A)=n

,

R

0

O

0

n

n

0

t

n

n

n

O

(A)

(A)

(1)

(1)

then the reduction is poly-preserving.

(cid:15) If t

= t

, M

runs in time polynomial in

0

n

n

R

0

0

t

n

, and sp

(M

) = sp

(A)=n

,

n

n

O

O

O

(1)

(1)

(A)

(A)

(1)

then the reduction is weak-preserving.

It is important to design the strongest reduction possible. The techniques described in

this paper can be directly used to yield poly-preserving reductions from regular or nearly

regular (with polynomial time computable degree of regularity) one-way functions to pseu-

dorandom generators [Luby : 96], and this covers almost all of the conjectured one-way

functions. However, the reduction for general one-way functions is only weak-preserving.

4 Hidden bits, hash functions, and computational entropy

4.1 Constructing a hidden bit

How do we go about constructing a function such that one of its output bits is computa-

tionally unpredictable yet statistically correlated with its other output bits? The following

fundamental proposition of [GL : 89] (strengthened in [Levin : 93]) provides the answer.

Proposition 4.1.1

Let f : f0; 1g

! f0; 1g

be a one-way function. Then, X (cid:12) R is

n

‘

n

hidden given hf (X ); Ri, where X; R 2

f0; 1g

. The reduction is linear-preserving with

n

respect to the alternative de(cid:12)nition of computational ly indistinguishable.

U

Proposition 4.1.1 presents an elegant, simple and general method of obtaining a hidden

bit from a one-way function. We need the following stronger proposition of [GL : 89] (see

also [Levin : 93]) in some of our proofs.

Proposition 4.1.2

There is an oracle TM M with the fol lowing properties. Let A be

any adversary that accepts as input n bits and outputs a single bit. Then, M

on input

(A)

parameter (cid:14)

> 0 outputs a list L of n-bit strings with the fol lowing property: for any (cid:12)xed

n

n

x 2 f0; 1g

, if it is the case that

j Pr[A(R) = x (cid:12) R] (cid:0) Pr[A(R) 6= x (cid:12) R]j (cid:21) (cid:14)

;

n

where R 2

f0; 1g

, then, with probability at least 1=2, it is the case that x 2 L. (The

n

probability here only depends on the values of the random bits used by M

.) The running

U

(A)

18



<!-- pdf-page: 19 -->
time of M

is polynomial in n, 1=(cid:14)

and the running time of A. Also, the number of

(A)

n-bit strings in L is bounded by O(1=(cid:14)

).

n

n

2

The following proposition is an immediate consequence of Propositions 4.1.1 and De(cid:12)ni-

tion 3.5.1.

Proposition 4.1.3

Let f : f0; 1g

! f0; 1g

be a one-way function. Then, hf (X ); R; X(cid:12)

n

‘

n

Ri and hf (X ); R; (cid:12) i are computational ly indistinguishable, where X; R 2

f0; 1g

and

n

U

(cid:12) 2

f0; 1g . The reduction is linear-preserving with respect to the alternative de(cid:12)nition of

U

computational ly indistinguishable.

4.2 One-way permutation to a pseudorandom generator

We describe a way to construct a pseudorandom generator from any one-way permutation

which is substantially simpler (and has stronger security preserving properties) than the

original construction of [Yao : 82]. The construction and proof described here is due to

[GL : 89].

Proposition 4.2.1

Let f : f0; 1g

! f0; 1g

be a one-way permutation. Let x; r 2 f0; 1g

n

n

n

and de(cid:12)ne

-time function ensemble g(x; r) = hf (x); r; x (cid:12) ri. Then, g is a pseudorandom

P

generator. The reduction is linear-preserving with respect to the alternative de(cid:12)nition of

computational ly indistinguishable.

PROOF: Let X; R 2

f0; 1g

, and (cid:12) 2

f0; 1g . Because f is a permutation, hf (X ); R; (cid:12) i

n

is the uniform distribution on f0; 1g

. By Proposition 4.1.3, g(X; R) and hf (X ); R; (cid:12) i

U

U

2n+1

are computationally indistinguishable, where the reduction is linear-preserving with re-

spect to the alternative de(cid:12)nition of computationally indistinguishable.

The reason Proposition 4.2.1 works when f is a permutation is because:

(1)

f (X ) is uniformly distributed and hence already looks random.

(2)

For any x 2 f0; 1g

, f (x) uniquely determines x. So no entropy is lost by the appli-

n

cation of f ,

For a general one-way function neither (1) nor (2) necessarily holds. Intuitively, the rest

of the paper constructs a one-way function with properties (1) and (2) from a general

one-way function. This is done by using hash functions to smooth the entropy of f (X ) to

make it more uniform, and to recapture the entropy of X lost by the application of f (X ).

19



<!-- pdf-page: 20 -->
Proposition 4.2.1 produces a pseudorandom generator that only stretches the input by one

bit. To construct a pseudorandom generator that stretches by many bits, combine this

with the construction described previously in Proposition 3.3.4.

4.3 One-to-one one-way function to a pseudoentropy generator

We now describe a construction of a pseudoentropy generator from any one-to-one one-way

function. This construction, together with Theorem 4.6.4, yields a pseudorandom gener-

ator from any one-to-one one-way function. The overall construction is di(cid:11)erent in spirit

than the original construction of [GKL : 93]: it illustrates how to construct a pseudoen-

tropy generator in a particularly simple way using [GL : 89]. Although the assumptions

and the consequences are somewhat di(cid:11)erent, the construction is the same as described in

Proposition 4.2.1.

Proposition 4.3.1

Let f : f0; 1g

! f0; 1g

be a one-to-one one-way function. Let

n

‘

n

x; r 2 f0; 1g

and de(cid:12)ne

-time function ensemble g(x; r) = hf (x); r; x (cid:12) ri: Then, g is

P

n

a pseudoentropy generator with pseudoentropy 1. The reduction is linear-preserving with

respect to the alternative de(cid:12)nition of computational ly indistinguishable.

PROOF: Let X; R 2

f0; 1g

and (cid:12) 2

f0; 1g . Proposition 4.1.3 shows that g(X; R)

n

U

U

and hf (X ); R; (cid:12) i are computationally indistinguishable, where the reduction is linear-pre-

serving with respect to the alternative de(cid:12)nition of computationally indistinguishable.

Because f is a one-to-one function and (cid:12) is a random bit,

(f (X ); R; (cid:12) ) = 2n + 1, and

H

thus g(X; R) has pseudoentropy 1.

Note that it is not possible to argue that g is a pseudorandom generator. For example,

let f (x) = h0; f

(x)i where f

is a one-way permutation. Then, f is a one-to-one one-way

0

0

function and yet g(X; R) = hf (X ); R; X (cid:12) Ri is not a pseudorandom generator, because

the (cid:12)rst output bit of g is zero independent of its inputs, and thus its output can easily

be distinguished from a uniformly chosen random string.

4.4 Universal hash functions

The concept of a universal hash function, introduced in [CW : 79], has proved to have far

reaching and a broad spectrum of applications in the theory of computation.

De(cid:12)nition 4.4.1 (universal hash functions)

Let h : f0; 1g

(cid:2) f0; 1g

! f0; 1g

be

‘

n

n

m

n

a

-time function ensemble. Recal l from de(cid:12)nition 2.3.2 that for (cid:12)xed y 2 f0; 1g

, we

P

‘

n

20



<!-- pdf-page: 21 -->
view y as describing a function h

((cid:1)) that maps n bits to m

bits. Then, h is a (pairwise

y

n

independent) universal hash function if, for al l x 2 f0; 1g

, x

2 f0; 1g

n fxg, for al l

n

n

a; a

2 f0; 1g

,

0

m

n

where Y 2

f0; 1g

.

‘

n

U

Pr[(h

(x) = a) and (h

(x

) = a

)] = 1=2

;

0

0

Y

Y

0

2m

n

Intuitively, a universal hash function has the property that every distinct pair x and x

0

are mapped randomly and independently with respect to Y .

In all of our constructions of function ensembles using universal hash functions, the de-

scription of the hash function y is viewed as a public input to the function ensemble, and

thus is also part of the output. The following construction is a universal hash function is

due to [CW : 79].

De(cid:12)nition 4.4.2 (matrix construction)

Let

h : f0; 1g

(cid:2) f0; 1g

! f0; 1g

(n+1)m

n

n

m

n

be the fol lowing

-time function ensemble. For x 2 f0; 1g

and y 2 f0; 1g

,

P

(cid:2)

n

(n+1)

m

n

h

(x) = hx; 1i (cid:12) y .

y

We concatenate a 1 to x in the above de(cid:12)nition to cover the case when x = 0

. Hereafter,

n

whenever we refer to universal hash functions, one can think of the construction given

above. However, any universal hash function that satis(cid:12)es the required properties may be

used. We note that there are more e(cid:14)cient hash functions in terms of number of bits used

in speci(cid:12)cation. One such example is using Toeplitz matrices (see for example [GL : 89] or

[Levin : 93]). A Toeplitz matrix is a matrix which is constant on any diagonal, and thus

to specify an n (cid:2) m Toeplitz matrix we can specify values for the m + n (cid:0) 1 diagonals,

This is the simplest bit-e(cid:14)cient construction of a universal hash function, so we adopt it

as the default for the remaining paper.

4.5 Smoothing distributions with hashing

The following lemma is a key component in most of the subsequent reductions we describe.

Lemma 4.5.1

Let D : f0; 1g

be a probability ensemble that has Renyi entropy at least

n

m

. Let e

be a positive integer valued parameter. Let h : f0; 1g

(cid:2) f0; 1g

! f0; 1g

n

n

(cid:0)

‘

n

n

m

2e

n

n

be a universal hash function. Let X 2

f0; 1g

, Y 2

f0; 1g

, and Z 2

f0; 1g

.

(cid:0)

n

‘

n

m

2e

n

n

D

U

U

Then

L

1

(hh

(X ); Y i; hZ; Y i) (cid:20) 2

:

(cid:0)

Y

(e

+1)

n

21



<!-- pdf-page: 22 -->
This lemma is a generalization of a lemma that appears in [Sip : 83]. There, D is the

uniform distribution on a set S (cid:18) f0; 1g

with ]S = 2

. The papers [McIn : 87] and

n

m

n

[BBR : 88] also proved similar lemmas. For the special case of linear hash functions, this

lemma can be derived from [GL : 89] by considering unlimited adversaries. A generaliza-

tion to a broader class of hash functions appears in [IZ : 89].

The lemma can be interpreted as follows: The universal hash function smooths out the

Renyi entropy of X to the almost uniform distribution on bit strings of length almost m

.

n

The integer parameter e

controls the tradeo(cid:11) between the uniformity of the output bits

n

of the universal hash function and the amount of entropy lost in the smoothing process.

Thus, we have managed to convert almost all the Renyi entropy of X into uniform random

bits while maintaining our original supply of random bits Y .

PROOF: Let ‘ = ‘

, e = e

and m = m

and s = m (cid:0) 2e. For all y 2 f0; 1g

, a 2 f0; 1g

n

n

n

‘

s

and x 2 f0; 1g

, de(cid:12)ne (cid:31)(h

(x) = a) = 1 if h

(x) = a and 0 otherwise. We want to show

y

y

n

that

E

[

jE

[(cid:31)(h

(X ) = a)] (cid:0) 2

j]=2 (cid:20) 2

:

(cid:0)

(cid:0)

Y

X

Y

s

(e+1)

We show below that for all a 2 f0; 1g

,

s

a

0;1

s

2f

g

X

E

E

[(cid:31)(h

(X ) = a)] (cid:0) 2

(cid:20) 2

;

(cid:0)

(cid:0)

Y

X

Y

s

(s+e)

and from this the proof follows.

(cid:12)

(cid:12)

(cid:2)

(cid:12)

(cid:12)

(cid:3)

For any random variable Z , E[jZ j

] (cid:21) E[jZ j]

by Jensen’s Inequality. Letting Z =

2

2

E[(cid:31)(h

(X ) = a)] (cid:0) 2

, we see that it is su(cid:14)cient to show for all a 2 f0; 1g

,

Y

(cid:0)

s

s

E

[(E

[(cid:31)(h

(X ) = a)] (cid:0) 2

)

] (cid:20) 2

:

(cid:0)

(cid:0)

Y

X

Y

s

2

2(s+e)

Let X

2

f0; 1g

. Using some elementary expansion of terms, and rearrangements of

n

0

D

summation, we can write the above as

E

[E

[((cid:31)(h

(X ) = a) (cid:0) 2

)((cid:31)(h

(X

) = a) (cid:0) 2

)]]:

(cid:0)

0

(cid:0)

X;X

Y

Y

Y

0

s

s

For each (cid:12)xed value of X to x and X

to x

, where x 6= x

, the expectation with respect to

0

0

0

Y is zero because of the pairwise independence property of universal hash functions. For

each (cid:12)xed value of X to x and X

to x

, where x = x

,

0

0

0

E[((cid:31)(h

(x) = a) (cid:0) 2

)

] = 2

(1 (cid:0) 2

) (cid:20) 2

:

(cid:0)

(cid:0)

(cid:0)

(cid:0)

Y

s

2

s

s

s

Because the Renyi entropy of D is at least m, it follows that Pr[X = X

] (cid:20) 2

. Thus,

0

(cid:0)

m

the entire sum is at most 2

which is equal to 2

by the de(cid:12)nition of s.

(cid:0)

(cid:0)

(m+s)

2(s+e)

In this lemma, D is required to have Renyi entropy at least m

. In many of our appli-

n

cations, the distribution in question has at least Renyi entropy m

, and thus the lemma

n

22



<!-- pdf-page: 23 -->
applies because of Proposition 2.2.3. For other applications, we need to work with Shannon

entropy. The following technical result due to [Shan : 48] allows us to convert Shannon

entropy to Renyi entropy by looking at product distributions.

Proposition 4.5.2

Let k

be an integer-valued polynomial parameter.

n

(cid:15) Let D : f0; 1g

be a probability ensemble. There is a probability ensemble E : f0; 1g

n

nk

n

satisfying:

{ H

H

(E ) (cid:21) k

(D) (cid:0) nk

.

n

n

Ren

2=3

{ L

(E ; D

) (cid:20) 2

.

1

(cid:0)

k

n

k

n

1=3

(cid:15) Let D

: f0; 1g

and D

: f0; 1g

be not necessarily independent probability ensembles,

1

2

n

n

let let D = hD

; D

i. There is a probability ensemble E : f0; 1g

, with E = hE

; E

i,

1

2

1

2

2nk

n

satisfying:

{

H

Ren

For every value E

2 f0; 1g

such that Pr

[E

] > 0,

(E

jE

= E

) (cid:21)

1

1

2

1

1

nk

n

1

E

k

(D

jD

) (cid:0) nk

.

H

n

2

1

n

2=3

{ L

(E ; D

) (cid:20) 2

.

(cid:0)

1

k

n

k

n

1=3

Corollary 4.5.3

P

Let k

be an integer-valued

-time polynomial parameter.

n

(cid:15) Let D : f0; 1g

be a probability ensemble, let m

= k

(D) (cid:0) 2nk

, and let h :

H

n

n

n

n

2=3

p

n

nk

n

m

n

k

n

n

f0; 1g

(cid:2) f0; 1g

! f0; 1g

be a universal hash function. Let X

2

k

n

f0; 1g

0

(cid:2)

and let Y 2

f0; 1g

. Then,

(hh

(X

); Y i; U

) (cid:20) 2

.

L

1

Y

0

m

+p

n

n

(cid:0)

p

n

1

k

n

1=3

D

U

n

n

(cid:15) Let D

: f0; 1g

and D

: f0; 1g

be not necessarily independent probability ensembles,

1

2

and let D = hD

; D

i. Let m

= k

(D

jD

)(cid:0) 2nk

. Let h : f0; 1g

(cid:2) f0; 1g

!

H

1

2

n

n

2

1

n

2=3

p

n

nk

n

m

n

k

2n

n

f0; 1g

be a universal hash function. Let hX

; X

i 2

f0; 1g

and let Y 2

n

k

0

0

(cid:2)

1

2

p

n

D

1=3

1

k

n

U

f0; 1g

. Then,

(hh

(X

); Y ; X

i; hU

; X

i) (cid:20) 2

.

L

1

Y

m

+p

n

n

0

0

0

(cid:0)

2

1

1

PROOF:

Combine Proposition 4.5.2, Lemma 4.5.1, Proposition 2.1.2, and Proposi-

tion 2.2.3.

4.6 Pseudoentropy generator to a pseudorandom generator

Let f : f0; 1g

! f0; 1g

be a pseudoentropy generator with pseudoentropy s

.

In

n

n

‘

n

this subsection, we construct a pseudorandom generator based on f . We (cid:12)rst start with

two preliminary propositions. The following proposition is the computational analog of

Proposition 2.1.2.

23



<!-- pdf-page: 24 -->
Proposition 4.6.1

Let D : f0; 1g

and E : f0; 1g

be two probability ensembles and let

n

n

f : f0; 1g

! f0; 1g

be a

-time function ensemble. Let D and E be computation-

P

n

‘

n

al ly indistinguishable. Then, f (D) and f (E ) are computational ly indistinguishable. The

reduction is linear-preserving.

The following proposition (cid:12)rst appears in [GM : 84].

Proposition 4.6.2

P

Let k

be an integer-valued

-time polynomial parameter. Let D :

n

‘

n

‘

n

f0; 1g

and E : f0; 1g

be

-samplable probability ensembles. Let D and E be computa-

P

tional ly indistinguishable. Then, D

and E

are computational ly indistinguishable. The

k

n

k

n

reduction is weak-preserving.

More precisely, there is a probabilistic oracle TM M with the following properties: if A

is a

-breaking adversary for distinguishing D

and E

then M

is a

-breaking

R

R

0

nk

n

n

k

n

k

n

(A)

adversary for distinguishing D and E , where

is essentially equal to k

.

It is

R

R

n

n

0

nk

n

crucial that D and E are

-samplable because the sampling algorithms are used by M .

P

The reduction is only weak-preserving because distinguishing D

and E

with respect to

k

n

k

n

private inputs of length nk

only translates into distinguishing D and E on private inputs

n

of length n.

We now give the construction of a pseudorandom generator g from a pseudoentropy gen-

erator f .

Construction 4.6.3

P

Let f : f0; 1g

! f0; 1g

be a

-time function ensemble and let s

n

n

m

n

be a

-time polynomial parameter. Let k

= (d(2m

+ 1)=s

e)

and j

=

k

(n + s

) (cid:0) 2m

k

P

n

n

n

n

n

n

n

3

2=3

n

.

Let h : f0; 1g

(cid:2) f0; 1g

! f0; 1g

be a universal hash function. Let u 2 f0; 1g

,

(cid:2)

j

k

p

n

k

m

n

n

j

n

k

n

n

y 2 f0; 1g

, and de(cid:12)ne

-time function ensemble g(u; y) = hh

(f

(u)); yi:

P

y

p

n

k

n

Theorem 4.6.4

Let f and g be as described in Construction 4.6.3. Let f be a pseu-

doentropy generator with pseudoentropy s

. Then, g is a pseudorandom generator. The

n

reduction is weak-preserving.

PROOF:

Let f

: f0; 1g

! f0; 1g

be the

-time function ensemble that wit-

P

0

0

n

n

m

n

nesses the pseudoentropy generator of f as guaranteed in De(cid:12)nition 3.4.1 of computa-

tional entropy, i.e., f

(X

) and f (X ) are

-secure computationally indistinguishable and

R

0

0

H

(f

(X

)) (cid:21) n + s

, where X 2

f0; 1g

and X

2

f0; 1g

. Let U 2

f0; 1g

,

0

0

n

0

(cid:2)

W 2

f0; 1g

, and Y 2

f0; 1g

. By Proposition 4.6.2, f

(U ) and f

(W ) are

(cid:2)

0

k

n

n

0

n

U

U

U

p

n

k

n

k

n

n

n

0

n

k

n

n

U

U

computationally indistinguishable. From Proposition 4.6.1 it follows that g(U; Y ) =

k

n

k

n

hh

(f

(U )); Y i and hh

(f

(W )); Y i are computationally indistinguishable. Because

Y

Y

0

24



<!-- pdf-page: 25 -->
H

(f

(X

)) (cid:21) n + s

, by choice of k

and j

, using Corollary 4.5.3,

it follows that

0

0

n

n

n

L

1

(hh

(f

(W )); Y i; U

) (cid:20) 2

. Thus, it follows that g(U; Y ) and U

are

Y

0

j

+p

n

n

(cid:0)

j

+p

n

n

k

n

1=3

k

n

computationally indistinguishable. Note that by choice of k

, the output length j

+ p

n

n

n

of g is longer than its input length nk

+ p

.

n

n

4.7 False entropy generator to a pseudoentropy generator

Let f : f0; 1g

! f0; 1g

be a false entropy generator with false entropy s

.

In this

n

n

‘

n

subsection, we construct a mildly non-uniform pseudoentropy generator based on f . An

idea is to extract

(f (X )) bits of entropy out of X without compromising the false

f

~

D

entropy. (See page 10 for the de(cid:12)nition of

.) Let X 2

f0; 1g

. The ma jor obstacles

~

D

n

f

U

are that

is not necessarily a

-time function ensemble and that f could be a very

D

P

f

~

non-regular function, and thus the variance of

(f (X )) could be quite high as a function

f

~

D

of X , and we cannot guess its value consistently with accuracy.

Let k

be an integer-valued

-time polynomial parameter and let U 2

f0; 1g

. The

P

n

(cid:2)

k

n

n

intuition behind the following construction is that the false entropy of f

is k

times that

n

U

k

n

of f and that the degeneracy of f

is k

times that of f . Furthermore, if k

is large enough

n

n

k

n

then, with high probability with respect to U ,

n (f

(U )) is close to the degeneracy

f

~

D

k

k

n

k

n

of f

. Thus, we use a universal hash function h to extract roughly the degeneracy of

k

n

k

n

f

(U ) bits of entropy out of U without compromising the false entropy of f

(U ).

Construction 4.7.1

P

Let f : f0; 1g

! f0; 1g

be a

-time function ensemble. Let s

n

n

‘

n

be a

-time polynomial parameter and assume for simplicity that s

(cid:20) 1. Let

be an

P

e

n

n

approximation of

(f (X )) to within an additive factor of s

=8, where X 2

f0; 1g

. Fix

H

n

n

k

=

(4n=s

)

and j

=

k

(n (cid:0)

) (cid:0) 2nk

e

. Let h : f0; 1g

(cid:2) f0; 1g

! f0; 1g

n

n

n

n

n

n

3

p

n

nk

n

j

n

2=3

U

be a universal hash function. For u 2 f0; 1g

and r 2 f0; 1g

, de(cid:12)ne

-time function

P

l

m

(cid:6)

(cid:7)

(cid:2)

k

n

n

p

n

ensemble

g(

; u; r) = hf

(u); h

(u); ri:

e

n

r

k

n

Lemma 4.7.2

Let f and g be as described in Construction 4.7.1. Let f be a false entropy

generator with false entropy s

. Then, g is a mild ly non-uniform pseudoentropy generator

n

with pseudoentropy 1. The reduction is weak-preserving.

PROOF: Let Z 2

f0; 1g

. First, note that

(X jf (X )) = n (cid:0)

(f (X )) = n (cid:0)

.

H

H

e

n

j

n

U

>From this and Corollary 4.5.3 (letting X

= f (X ), X

= X in the corollary), it follows

1

2

1=3

that

(g(

; U; R; ); hf

(U ); Z; Ri) (cid:20) 2

.

L

e

n

(cid:0)

1

k

n

k

n

25



<!-- pdf-page: 26 -->
We now prove that g(

; U; R) has computational entropy at least p

+ nk

+ 1. Let

e

n

n

n

D : f0; 1g

be the

-samplable probability ensemble such that D and f (X ) are compu-

P

‘

n

tationally indistinguishable and such that

H

H

(D) (cid:21)

(f (X )) + s

:

n

Since D and f (X ) are computationally indistinguishable, hf

(U ); Z; Ri and hD

; Z; Ri

k

n

k

n

are computationally indistinguishable by Proposition 4.6.2, which together with the (cid:12)rst

claim implies that g(

; U; R) and hD

; Z; Ri are computationally indistinguishable. Now,

e

n

k

n

k

n

H

(D

; Z; R) (cid:21) k

(cid:1) (

(f (X )) + s

) + j

+ p

(cid:21) k

(

+ 7s

=8) + j

+ p

;

H

e

n

n

n

n

n

n

n

n

n

and because by choice of k

and j

this is at least p

+ nk

+ 1. Thus, g has computational

n

n

n

n

entropy at least p

+ nk

+ 1, and the lemma follows.

n

n

4.8 Mildly non-uniform to a uniform pseudorandom generator

Proposition 4.8.1

a

Let

be any value in f0; : : : ; k

g, where k

is an integer-valued

n

n

n

P

P

-time polynomial parameter. Let g : f0; 1g

(cid:2) f0; 1g

! f0; 1g

be a

-time

d

e

log(k

)

n

n

‘

n

function ensemble, where ‘

> nk

. Let x

2 f0; 1g

and de(cid:12)ne

-time function

P

n

n

0

(cid:2)

k

n

n

ensemble g

(x

) = (cid:8)

g(i; x

): Let g be a mild ly non-uniform pseudorandom generator

0

0

i=1

0

i

k

n

when the (cid:12)rst input is set to

. Then, g

is a pseudorandom generator. The reduction is

a

n

0

weak-preserving.

PROOF: Let X 2

f0; 1g

, X

2

f0; 1g

and Z 2

f0; 1g

. Suppose there is an

0

(cid:2)

n

k

n

n

‘

n

adversary A that has distinguishing probability

U

U

U

sp

(A) =

Pr[A(g

(X

)) = 1] (cid:0) Pr[A(Z ) = 1]

:

n

0

0

We describe an oracle TM M such that, for all i = 1; : : : ; k

, M

(i) has sp

(A) dis-

(cid:12)

(cid:12)

n

n

(cid:12)

(cid:12)

(A)

tinguishing probability for g(i; X ) and Z . For all i, the running time for M

(i) is the

(A)

running time for A plus the time to run compute the output of g on k

(cid:0) 1 inputs. Since

n

this works with respect to all i, in particular it works when i =

, from which the result

a

n

follows.

For each i = 1; : : : ; k

, M

(i) works as follows. On input u (and i), M

(i) randomly

n

(A)

(A)

generates x

; : : : ; x

; x

; : : : ; x

2

f0; 1g

and computes v = (cid:8)

g(j; x

) (cid:8) u: Then

0

0

0

0

1

i

1

i+1

k

n

j

=i

0

j

n

(A)

(cid:0)

U

M

(i) runs A on input v and outputs A(v). By the nature of (cid:8), if u is chosen randomly

according to Z then M

(i) = 1 with probability Pr[A(Z ) = 1], whereas if u is chosen

(A)

randomly according to g(i; X ) then M

(i) = 1 with probability Pr[A(g

(X

)) = 1]. Thus,

0

0

(A)

for each value of i, M

(i) has distinguishing probability sp

(A) for g(i; X ) and Z .

n

(A)

26

6


<!-- pdf-page: 27 -->
Note that it may be the case that, for most (cid:12)xed values of i 2 f1; : : : ; k

g, g(i; X ) is

n

completely predictable. On the other hand, even if there is a value

for each n such that

a

n

g(

; X ) is pseudorandom, the value of

may not be

-time computable. This is exactly

a

a

P

n

n

the case when the lemma is useful, i.e., it is useful to transform the mildly non-uniform

pseudorandom generator g into a pseudorandom generator g

.

0

Note in the given construction, the length of the output of g

on inputs of length nk

is

0

n

‘

> nk

, and thus g

stretches the input to a string of strictly greater length.

n

n

0

This reduction is only weak-preserving, and the reason is the usual one, i.e., the breaking

adversary for g

(X

) on inputs of length nk

is transferred into a breaking adversary for

0

0

n

g(i; X ) on inputs of length only n.

If g in Proposition 4.8.1 does not satisfy the property that ‘

> nk

, then for each (cid:12)xed

n

n

i we can use Proposition 3.3.4 to stretch the output of g(i; x) (viewed as a function of

x) into a string of length longer than nk

and then exclusive-or together the stretched

n

outputs.

4.9 Summary

Putting together the results in this section, we have:

(cid:15) A reduction from a one-way permutation to a pseudorandom generator.

(From

Subsection 4.2.)

(cid:15) A reduction from a one-to-one one-way function to a pseudorandom generator.

(Combining Subsections 4.3 and 4.6.)

(cid:15) A reduction from a pseudoentropy generator to a pseudorandom generator. (From

Subsection 4.6.)

(cid:15) A reduction from a false entropy generator to a pseudorandom generator. (Combin-

ing Subsections 4.7, 4.6, and 4.8.)

5 Extracting entropy from one-way functions

In this ection we show how to construct a pseudoentropy generator from any one-way

function f with the additional property that the number of inverses of f can be computed

in polynomial time, i.e., the function

is a

-time function ensemble. Combined with

D

P

f

~

the results summarized in Subsection 4.9, this gives a construction of a pseudorandom

generator from a one-way function with this property.

27



<!-- pdf-page: 28 -->
One of the reasons for giving the (cid:12)rst construction is because it illustrates some of the

additional ideas needed for our construction of a false entropy generator from any one-

way function. A general one-way function f does not necessarily have the property that

~

D

P

is a

-time function ensemble, and considerably more e(cid:11)ort is needed to construct a

f

pseudorandom generator from it. In the subsequent section, we describe how to construct a

false entropy generator from any one-way function. Combined with the results summarized

in Subsection 4.9, this gives a construction of a pseudorandom generator from any one-way

function.

5.1 One-way function with approximable pre-image sizes to a pseudoen-

tropy generator

To see where we get into trouble with the construction given in Proposition 4.3.1, suppose

f : f0; 1g

! f0; 1g

is a 2

-regular one-way function, and let X; R 2

f0; 1g

and

n

‘

n

n=4

n

U

(cid:12) 2

f0; 1g . Then, although hf (X ); R; X (cid:12) Ri and hf (X ); R; (cid:12) i are computationally

U

indistinguishable,

(f (X ); R; X (cid:12) R) is only about 7n=4 + 1, and thus we have lost about

H

n=4 bits of the input entropy through the application of f . Similarly, although X (cid:12) R is

hidden given hf (X ); Ri, it is also almost completely statistically uncorrelated.

The idea to overcome these problems is to create a new function which is the original

one-way function concatenated with the degeneracy of the function number of bits hashed

out of its input to regain the lost entropy. Then, Proposition 4.3.1 can be applied to

the new function to obtain a pseudoentropy generator. We (cid:12)rst show how to construct a

pseudoentropy generator in the case when

is a

-time function ensemble.

D

P

f

~

Construction 5.1.1

P

Let f : f0; 1g

! f0; 1g

be a

-time function ensemble and sup-

n

‘

n

pose that

is a

-time function ensemble. Let h : f0; 1g

(cid:2) f0; 1g

! f0; 1g

be a

D

P

f

~

p

n

n

n+2

universal hash function. For x 2 f0; 1g

and y 2 f0; 1g

, de(cid:12)ne

-time function ensemble

P

n

p

n

f

(x; y) = hf (x); h

(x)

; yi:

0

y

D

~

1;:::;

(f (x))+2

f

f

g

Lemma 5.1.2

Let f and f

be as described in Construction 5.1.1.

0

(1) Let f be a one-way function. Then, f

is a one-way function. The reduction is

0

poly-preserving.

(2) Let X 2

f0; 1g

and Y 2

f0; 1g

. Then,

(f

(X; Y )) (cid:21) n + p

(cid:0) 1=2.

H

0

n

n

p

n

U

U

PROOF of (1) :

Suppose adversary A inverts f

(X; Y ) with probability (cid:14)

in time T

.

0

n

n

We prove that the following oracle TM M using A on input z = f (x) (cid:12)nds x

2 pre

(z )

0

f

with probability at least (cid:14)

=128 when x 2

f0; 1g

.

3

n

n

U

28



<!-- pdf-page: 29 -->
Description of

:

M

(z )

(A)

Compute

(z ).

D

f

~

Choose (cid:11) 2

f0; 1g

.

~

D

f

(z )+2

Choose y 2

f0; 1g

.

U

p

n

U

If A(z ; (cid:11); y) outputs x

with f (x

) = z then output x

.

0

0

0

Let j

= 2 dlog(2=(cid:14)

)e. For all z 2 range

, for all y 2 f0; 1g

, de(cid:12)ne random variable

n

n

f

p

n

where W 2

pre

(z ). Then, the probability there is a (cid:13) 2 f0; 1g

such that A inverts

2+j

n

f

U

f on input hf (X ); h(cid:12)

; (cid:13) i; Y i is at least (cid:14)

.

f (X );Y

n

(cid:12)

= h

(W )

;

~

z ;y

y

D

1;:::;

(z )

j

f

n

f

(cid:0)

g

Fix z 2 range

, and let (cid:12)

2

f0; 1g

. By Lemma 4.5.1,

f

0

z

(cid:0)

U

~

D

f

(z )

j

n

L

1

(h(cid:12)

; Y i; h(cid:12)

; Y i) (cid:20) (cid:14)

=2:

z ;Y

0

z

n

2+j

n

Therefore, the probability there is a (cid:13) 2 f0; 1g

such that A inverts f on input

hf (X ); h(cid:12)

; (cid:13) i; Y i is at least (cid:14)

=2.

If we choose (cid:13) 2

f0; 1g

, we have the prob-

0

n

f (X )

U

2+j

n

ability that A inverts f (X ) on input hf (X ); h(cid:12)

; (cid:13) i; Y i is at least

0

f (X )

(2+j

)

n

n

(cid:14)

(cid:14)

n

3

2

(cid:0)

(cid:1)

(cid:21)

:

2

128

Note that this is the input distribution in the call to A within M

. Note also that the

(A)

run time of M

is dominated by the time to run A. Thus, the time-success ratio of M

(A)

(A)

for inverting f

is about 128T

=(cid:14)

.

0

n

n

3

PROOF of (2) :

Fix z 2 range

and let x; x

2 pre

(z ) such that x 6= x

. From the

f

f

0

0

properties of a universal hash function,

Pr[h

(x)

= h

(x

)

] = 2

(cid:20)

:

0

(cid:0)

Y

D

Y

D

~

~

1;:::;

(z )+2

1;:::;

(z )+2

f

f

f

g

f

g

4 (cid:1) ]pre

(z )

f

~

D

(

(z )+2)

f

1

By calculating the Renyi entropy it follows that

H

(f

(X; Y )) (cid:21) (cid:0) log

(cid:1) 2

= n + p

+ 2 (cid:0) log(5):

0

(cid:0)

n

5

n+p

n

4

(cid:18)

(cid:19)

The result follows since log(5) (cid:20) 5=2.

29



<!-- pdf-page: 30 -->
Corollary 5.1.3

Let f , h and f

be as described in Construction 5.1.1. Let r 2 f0; 1g

0

n

and de(cid:12)ne

-time function ensemble g(x; y ; r) = hf

(x; y); r; x (cid:12) ri: Let f be a one-way

P

0

function. Then, g is a pseudoentropy generator with pseudoentropy 1=2. The reduction is

poly-preserving.

PROOF: The proof is the same as the proof of Proposition 4.3.1. Let X; R 2

f0; 1g

,

n

Y 2

f0; 1g

, and (cid:12) 2

f0; 1g . From Lemma 5.1.2, part (1) and Proposition 4.1.3 it fol-

p

n

U

U

U

lows that g(X; Y ; R) and hf

(X; Y ); R; (cid:12) i are computationally indistinguishable, where the

0

reduction is poly-preserving. From Lemma 5.1.2, part (2) it follows that

(f

(X; Y ); R; (cid:12) ) (cid:21)

H

0

2n + p

+ 1=2. On the other hand, the input entropy to g(X; Y ; R) is 2n + p

, and thus it

n

n

follows that g has pseudoentropy 1=2.

Theorem 5.1.4

A pseudorandom generator can be constructed from a one-way function

f where

is a

-time function ensemble. The reduction is weak-preserving.

D

P

f

~

PROOF: Combine Construction 5.1.1 with Construction 4.6.3, and use Corollary 5.1.3

and Theorem 4.6.4.

The following theorem, an easy corollary of Theorem 5.1.4, was previously obtained by

[GKL : 93] using a di(cid:11)erent construction and proof techniques.

Theorem 5.1.5

Let f : f0; 1g

! f0; 1g

be a (cid:27)

-regular one-way function, where (cid:27)

n

n

n

‘

n

is a

-time polynomial parameter. Then, a pseudorandom generator can be constructed

P

from f . The reduction is weak-preserving.

PROOF: Note that in this case

(f (x)) = dlog((cid:27)

)e for all x 2 f0; 1g

. Further-

f

n

~

D

n

more, dlog((cid:27)

)e 2 f0; : : : ; ng. Using this, and combining Construction 5.1.1 with Con-

n

struction 4.6.3, and using Corollary 5.1.3 and Theorem 4.6.4 yields a mildly non-uniform

pseudorandom generator. Then, Theorem 4.8 shows how to construct a pseudorandom

generator from this.

Based on the ideas presented above, [Luby : 96] (Theorem 10.1 and Theorem 9.3) gives

versions of Theorem 5.1.4 and Theorem 5.1.5 where the reduction is poly-preserving when

the security parameter is

-time computable.

P

30



<!-- pdf-page: 31 -->
6 Any one-way function to a false entropy generator

6.1 Finding determined hidden bits

The (cid:12)nal step in the general construction of a pseudorandom generator from a one-way

function is to construct a false entropy generator from any one-way function. This is the

technically most di(cid:14)cult part of this paper. This construction uses some of the ideas from

Construction 5.1.1. Let

f : f0; 1g

! f0; 1g

(1)

n

‘

n

be a one-way function and let

h : f0; 1g

(cid:2) f0; 1g

! f0; 1g

(2)

d

e

p

n

n

n+

log(2n)

be a universal hash function. Similar to Construction 5.1.1, for x 2 f0; 1g

, i 2 f0; : : : ; n (cid:0) 1g

n

and r 2 f0; 1g

, de(cid:12)ne

-time function ensemble

P

p

n

f

(x; i; r) = hf (x); h

(x)

; i; ri:

(3)

0

r

1;:::;i+

log(2n)

f

d

eg

Note that from Lemma 5.1.2, the restricted function f

(x;

(f (x)); r) is an almost one-

0

f

~

D

to-one one-way function, except that this is not necessarily a

-time function ensemble

P

since

may not be a

-time function ensemble, and this is the main di(cid:14)culty we must

D

P

f

~

overcome.

Let X 2

f0; 1g

, R 2

f0; 1g

, Y 2

f0; 1g

and (cid:12) 2

f0; 1g . From the proof of

n

p(n)

n

Lemma 5.1.2 and Corollary 5.1.3, we claim and formalize below that if i (cid:20)

(f (X ))

f

~

D

U

U

U

U

then a time limited adversary cannot distinguish X (cid:12) Y from (cid:12) given Y and f

(X; i; R).

0

Let

T = fhx; iijx 2 f0; 1g

; i 2 f0; : : : ;

(f (x))gg

f

n

~

D

T = fhx; iijx 2 f0; 1g

; i 2 f

(f (x)) + 1; : : : ; n (cid:0) 1gg

f

n

~

D

Lemma 6.1.1

Let W = h

X ;

I i 2

T , R 2

f0; 1g

, Y 2

f0; 1g

, and (cid:12) 2

f0; 1g .

~

~

p(n)

n

U

U

U

U

Let f be a one-way function. Then,

hf

(W; R);

X (cid:12) Y ; Y i and hf

(W; R); (cid:12) ; Y i

0

0

~

are computational ly indistinguishable. The reduction is poly-preserving.

PROOF: Let A be a

-breaking adversary for distinguishing the two distributions. Then,

R

0

A is also a

-breaking adversary for hidden bit

X (cid:12) Y given hf

(W; R); Y i. Then, from

R

0

0

~

31



<!-- pdf-page: 32 -->
Proposition 4.1.2, there is an oracle TM M

such that M

is a

-breaking adversary

R

0

0

00

(A)

for inverting f

(W; R), where

(n) = n

(cid:1)

(n)

. Finally, we use the same idea

R

R

0

00

O

0

O

(1)

(1)

as in Lemma 5.1.2, i.e., the success probability of M

on input hf (x); (cid:11); i; Ri for (cid:11) 2

0

(A)

i+

log(2n)

(A)

U

f0; 1g

is at least inverse polynomial in the success probability of M

on input

d

e

0

f

(x; i; R) for each (cid:12)xed hx; ii 2 T . Consider the following oracle TM N : N

on input

0

A

f (x) chooses i 2

f0; : : : ; n (cid:0) 1g, (cid:11) 2

f0; 1g

, and r 2

f0; 1g

and runs M

d

e

0

i+

log(2n)

p

n

(A)

U

U

U

on input hf (x); (cid:11); i; ri. Since Pr[hx; ii 2 T ] (cid:21) 1=n when i 2

f0; : : : ; n (cid:0) 1g, it follows

A

U

that N

(f (X )) produces an inverse with probability at least 1=n times the probability

(A)

M

(f

(W; R)) produces an inverse.

0

0

If i (cid:21)

(f (X )) then X is almost completely determined by f

(X; i; R), and thus X (cid:12) Y

f

0

~

D

is almost completely determined by f

(X; i; R) and Y .

0

The interesting case is when i =

(f (X )), in which case, from Lemma 6.1.1, the adver-

f

~

D

sary is unable to distinguish X (cid:12) Y from (cid:12) given Y and f

(X; i; R), and yet from part (2)

0

of Lemma 5.1.2, X (cid:12) Y is almost completely determined by f

(X; i; R) and Y . It is from

0

this case that we can extract a little bit of false entropy.

6.2 Construction and Main Theorem

We now describe the construction of a false entropy generator g based on f

. Let

0

k

(cid:21) 125n

:

(4)

n

3

Part of the construction is to independently and randomly choose k

sets of inputs to f

,

n

0

and concatenate the outputs, In particular, let X

2

f0; 1g

, I

2

f0; 1g

,

0

(cid:2)

0

(cid:2)d

e

k

n

n

k

log(n)

n

R

2

f0; 1g

. Part of the construction is then f

(X

; I

; R

).

0

(cid:2)

0

0

0

0

k

p

n

n

U

U

k

n

U

Let I 2

f0; : : : ; n (cid:0) 1g, let

U

and let

p

D

= Pr[I (cid:20)

(f (X ))];

(5)

n

f

~

m

= k

(cid:0) 2k

:

p

(6)

n

n

n

n

2=3

We show later that it is su(cid:14)cient to have an approximation of

to within an additive

p

n

factor of 1=n for the entire construction to work. We need this to be able to claim that

g described below is mildly non-uniform. For now we assume we have the exact value of

p

n

. Let Y

2

f0; 1g

. The value of k

is chosen to be large enough so that with high

0

(cid:2)

n

k

n

n

probability it is the case that I

(cid:20)

(f (X

)) for at least m

of the k

possible values of

0

j

f

0

j

n

n

U

~

D

j , and in this case, from Lemma 6.1.1, X

(cid:12) Y

looks like a random bit to a time limited

0

0

j

j

adversary given Y

and f

(X

; I

; R

).

0

0

0

0

0

j

j

j

j

The problem is that we don’t know for which set of m

values of j the bit X

(cid:12) Y

looks

n

0

0

j

j

random to a time limited adversary. Instead, the idea is to hash m

bits out of all k

n

n

32



<!-- pdf-page: 33 -->
such bits and release the hashed bits. The intuition is that these m

hashed bits will look

n

random to a time limited adversary, even though there are really at most (

(cid:0) 1=n)k

p

n

n

bits of randomness left in these k

bits after seeing Y

and f

(X

; I

; R

), and thus there

n

0

0

0

0

0

k

n

are approximately m

(cid:0) (

(cid:0) 1=n)k

(cid:25) n

bits of false entropy. Let

p

n

n

n

2

h

: f0; 1g

(cid:2) f0; 1g

! f0; 1g

(7)

0

0

p

n

k

n

m

n

be a universal hash function, let U 2

f0; 1g

and de(cid:12)ne

-time function ensemble

P

0

p

n

g(

; X

; Y

; I

; R

; U ) = hh

(hX

(cid:12) Y

; : : : ; X

(cid:12) Y

i); f

p

(X

; I

; R

); U; Y

i:

(8)

0

0

0

0

0

0

0

0

0

0

0

0

0

0

n

U

1

1

k

k

n

n

U

k

n

Theorem 6.2.1

Let f be a one-way function and g be as described above in equations (1)

through (8). Then g is a mild ly non-uniform false entropy generator with false entropy

2

10n

. The reduction is weak-preserving.

PROOF: Let Z 2

f0; 1g

, and let

m

n

U

D = hh

(hX

(cid:12) Y

; : : : ; X

(cid:12) Y

i); f

(X

; I

; R

); U; Y

i:

0

0

0

0

0

0

0

0

0

0

U

1

1

k

k

n

n

k

n

E = hZ; f

(X

; I

; R

); U; Y

i:

0

0

0

0

0

k

n

Note that D is the distribution of the output of g , and E is the same except that the m

n

output bits of h

have been replaced by random bits. Lemma 6.3.1 shows that

(E ) (cid:21)

H

0

2

H

(D) + 10n

. Corollary 6.3.3 shows that if f is a one-way function then D and E are

computationally indistinguishable, where the overall reduction is weak-preserving.

What remains to prove Theorem 6.2.1 are the proofs of Lemma 6.3.1 and Lemma 6.3.2

of the next subsection.

(Corollary 6.3.3 follows immediately from Lemma 6.3.2 and

Lemma 6.1.1). Before we turn to this, we state the main result of this paper based

on Theorem 6.2.1.

Theorem 6.2.2

There are one-way functions i(cid:11) there are pseudorandom generators.

PROOF: That pseudorandom generators imply one-way functions follows from [Levin : 87].

The converse now follows from Theorem 6.2.1 and the results summarized in Subsec-

tion 4.9.

6.3 The Main Lemmas

Lemma 6.3.1 H

H

(E ) (cid:21)

(D) + 10n

.

2

33



<!-- pdf-page: 34 -->
PROOF:

The entropy of D and E excluding the (cid:12)rst m

bits is exactly the same.

n

The additional entropy in the (cid:12)rst m

bits of E is equal to m

. An upper bound on the

n

n

additional entropy in the (cid:12)rst m

bits of D is the additional entropy in hX

(cid:12) Y

; : : : ; X

(cid:12)

n

0

0

0

1

1

k

n

Y

i: For each j 2 f1; : : : ; k

g where I

<

(f (X

)), the amount of entropy added by

0

k

n

n

0

j

f

0

j

~

D

X

(cid:12) Y

is at most 1. On the other hand, under the condition that I

(cid:21)

(f (X

)),

0

0

j

j

0

j

f

0

j

~

D

X

(cid:12) Y

is determined by hf

(X

; I

; R

); Y

i with probability at least 1 (cid:0) 1=2n, and thus

0

0

0

0

0

0

0

j

j

j

j

j

j

the additional entropy under this condition is at most 1=2n. Since I

<

(f (X

))

0

j

f

0

j

~

D

with probability

(cid:0) 1=n, it follows that the additional entropy added by X

(cid:12) Y

is at

p

n

0

0

j

j

most

(cid:0) 1=2n. Therefore, the additional entropy in the (cid:12)rst m

bits of D is at most

p

n

n

k

(

(cid:0) 1=2n) = m

+ 2k

(cid:0) k

=2n < m

(cid:0) 10n

by choice of k

.

p

n

n

n

n

n

n

n

2=3

2

Lemma 6.3.2

Let A be an adversary with distinguishing probability

(cid:14)

= Pr[A(D) = 1] (cid:0) Pr[A(E ) = 1]

n

for D and E . (We assume without loss of generality that Pr[A(D) = 1] > Pr[A(E ) = 1].)

Let W = h

X ;

I i 2

T , R 2

f0; 1g

, Y 2

f0; 1g

, and (cid:12) 2

f0; 1g . There is an oracle

~

~

p(n)

n

TM M such that M

distinguishes between

U

U

U

U

(A)

hf

(W; R);

X (cid:12) Y ; Y i and hf

(W; R); (cid:12) ; Y i

0

0

~

with probability at least (cid:14)

=(16k

). The running time of M

is polynomial in the running

n

n

(A)

time of A.

The proof of Lemma 6.3.2 is the most technically involved in this paper. Before proving

this lemma, we give the main corollary to this lemma, and then give some motivation for

the proof of the lemma.

Corollary 6.3.3

Let f be a one-way function. Then, D and E are computational ly indis-

tinguishable. The reduction is weak-preserving.

PROOF: Combine Lemma 6.1.1 with Lemma 6.3.2.

We now give some intuition to the proof of Lemma 6.3.2. The oracle TM M

will

(A)

use a non-straightforward hybrid of distributions argument to be able to distinguish the

two distributions in the statement of the lemma. To give some intuition about this non-

straightforward hybrid, we (cid:12)rst describe a related straightforward hybrid argument that

we do not know how to implement e(cid:14)ciently.

Consider the following distribution. For j 2 f1; : : : ; k

g, let C

= 1 with probability

n

j

p

n

and C

= 0 with probability 1 (cid:0)

. For all j , if C

= 1 then let h

X

;

I

i 2

T , and if

p

~

~

j

n

j

0

0

j

j

U

34



<!-- pdf-page: 35 -->
C

= 0 then let h

X

;

I

i 2

T . Let R

; Y

and U be as de(cid:12)ned previously. If these random

j

0

0

0

0

~

~

j

j

U

variables are used to de(cid:12)ne a distribution using the same construction as used to de(cid:12)ne

D , with h

X

;

I

i replacing hX

; I

i, then the distribution is D , except that it is described

0

0

0

0

j

j

j

j

~

~

in a slightly di(cid:11)erent way. Now, suppose this distribution is altered as follows: if C

= 1

j

then change the j

input bit of h

from

X

(cid:12) Y

to B

2

f0; 1g . Call this distribution

th

~

U

0

0

j

j

j

U

D

.

0

From Lemma 6.1.1 intuitively it should be the case that a time limited adversary should

not be able to distinguish D from D

. On the other hand, it is not hard to see using

0

Lemma 4.5.1 that the statistical distance between D

and E is exponentially small in n.

0

Thus, if adversary A can distinguish between D and E , we should be able to use this to

distinguish hf

(W; R);

X (cid:12) Y ; Y i and hf

(W; R); (cid:12) ; Y i as in the statement of Lemma 6.3.2.

0

0

~

The question is whether we can really prove that D

is computationally indistinguishable

0

from D . Towards resolving this question, consider the following family of hybrid distri-

butions. For all j 2 f0; : : : ; k

g, let F

be the hybrid distribution between D and E

n

(j )

which is the same as D

up to position j and the same as D thereafter, i.e., it is the

0

same as D except that for all i (cid:20) j , if C

= 1 then change the i

input bit of h

from

i

U

th

~

(0)

(k

)

n

X

(cid:12) Y

to B

2

f0; 1g . Then, F

= D and F

(cid:25) E . Let J 2

f1; : : : ; k

g. Then,

0

0

i

i

i

n

(J

1)

(J )

U

U

E

[A(F

) (cid:0) A(F

)] = (cid:14)

=k

.

J

(cid:0)

n

n

An ine(cid:14)cient oracle TM could work as follows on input hf

(w; r); b; yi: The (cid:12)rst phase

0

(j )

chooses j 2

f1; : : : ; k

g, and chooses a sample from F

. If c

= 0 then the oracle TM

n

j

U

produces a random bit and stops. In the more interesting case, where c

= 1, it replaces

j

the inputs corresponding to the j

position in the sample according to f

(w; r) and y , and

0

th

th

the j

input bit of h

is set to b 2

f0; 1g . Then, the second phase runs the adversary

u

U

A on this input and outputs the bit produced by A. The distinguishing probability for

this oracle TM is (cid:14)

=k

. The problem is that this is not an e(cid:14)cient oracle TM, because it

n

n

may not be possible to e(cid:14)ciently uniformly sample from T and T as required. However,

it is possible to sample uniformly from f0; 1g

(cid:2) f0; : : : ; n (cid:0) 1g, and a

fraction of the

p

n

n

samples will be randomly distributed in T and a 1 (cid:0)

fraction of the samples will be

p

n

randomly distributed in T , and this simple idea is used to construct the e(cid:14)cient adversary

described below.

The e(cid:14)cient adversary M

described in detail in the proof of Lemma 6.3.2 proceeds in

(A)

two phases similar to the ine(cid:14)cient oracle TM described above. The (cid:12)rst phase of M

(A)

consists of k

stages, where stage j produces a coupled pair of distributions, D

and

n

(j )

(j )

E

, both of which are polynomially samplable. Each stage consists of using adversary A

and sampling from the distributions produced in the previous stage to produce the pair

of output distributions for the current stage. Initially, D

= D and E

= E , and it will

(0)

(0)

turn out that D

(cid:25) E

.

(k

)

(k

)

n

n

The (cid:12)rst j (cid:0) 1 positions in both D

and E

are already (cid:12)xed in essentially the same

(j )

(j )

35



<!-- pdf-page: 36 -->
way in D

and E

, and these positions will be (cid:12)xed the same way in D

and E

.

(cid:0)

(cid:0)

(j

1)

(j

1)

(j )

(j )

To (cid:12)ll in position j in D

and E

, many samples of hx

; i

i are drawn uniformly from

j

j

(j )

(j )

n

f0; 1g

(cid:2) f0; : : : ; n (cid:0) 1g, and then with high probability many of them will be in T and

many will be in T . We cannot directly tell for each sample whether it is in T or T . Thus,

we must use another criteria to decide which of the samples to keep to (cid:12)ll in position

j . The criteria used is to use the sample for which the distinguishing probability of A

between D

and E

is highest when the j

position is (cid:12)xed according to the sample.

(j )

(j )

th

(j )

(j )

(j )

(0)

(k

)

n

Let (cid:14)

= Pr[A(D

) = 1] (cid:0) Pr[A(E

) = 1]. Because (cid:14)

= (cid:14)

and (cid:14)

(cid:25) 0, it follows

n

that

E

[(cid:14)

(cid:0) (cid:14)

] (cid:21) (cid:14)

=k

:

(cid:0)

n

n

j

1;:::;k

U

n

2

f

g

(j

1)

(j )

It is because of this discrepancy between the value of (cid:14)

and (cid:14)

that f

can be inverted

(cid:0)

0

(j )

(j

1)

in the second phase.

Intuitively, stage j of the (cid:12)rst phase works as follows. A bit c

is chosen randomly to be

j

one with probability

and to be zero with probability 1 (cid:0)

. In the distribution D

,

p

p

n

n

(j )

th

k

n

the j

input hx

; i

; r

i to f

is chosen randomly, y

is chosen randomly, u is chosen

0

0

0

0

j

j

j

0

j

randomly, and then the j

input bit of h

is set to a random bit b

if c

= 1 and to the

0

u

j

j

th

correct inner product bit if c

= 0. In the distribution E

, the j

input of f

is set the

j

0

(j )

th

k

n

same way it is set in D

, and thus the two distributions D

and E

are correlated. The

(j )

(j )

(j )

choice of the j

inputs is done several times (c

is chosen only once at the beginning, i.e.,

j

th

it is not rechosen for each of the times) and each time the distinguishing probability of A

(j )

(j )

for D

and the corresponding E

is approximated, and the choice that maximizes the

di(cid:11)erence between these accepting probabilities determines how D

and E

are (cid:12)nally

(j )

(j )

set.

The second phase of M

chooses j 2

f1; : : : ; k

g and then uses the pair of distributions

(j )

(j )

U

n

D

and E

produced in the (cid:12)rst stage. The idea is to choose a random sample from

(A)

both D

and E

, modify portions of the D

part according to the input to M

, and

(j )

(j )

(j )

(A)

run A on both the modi(cid:12)ed D

sample and the E

sample and based on the outputs

(j )

(j )

produce a one bit output. The intuition is that the distinguishing probability will be (cid:14)

,

(j )

which on average over all j is at least (cid:14)

=k

.

n

n

We now turn to the formal proof of Lemma 6.3.2.

PROOF: (Of Lemma 6.3.2)

The oracle TM M

works as follows on input hf

(w; r); b; yi:

0

(A)

Phase 1 :

De(cid:12)ne D

= D and E

= E . Let B 2

f0; 1g

. Let (cid:26) = (cid:14)

=(16k

) and

n

n

(0)

(0)

k

n

U

36



<!-- pdf-page: 37 -->
(cid:28) = 64n

=(cid:26): Stage j = 1; : : : ; k

works as follows: Randomly choose c

2 f0; 1g so that

n

j

2

c

= 1 with probability

. Choose ^x

; : : : ; ^x

2

f0; 1g

and

i

; : : : ;

i

2

f0; : : : ; n (cid:0) 1g.

p

j

n

1

(cid:28)

1

(cid:28)

n

^

^

For each m 2 f1; : : : ; (cid:28) g, de(cid:12)ne w

= h ^x

;

i

i and let D

(w

) be the same as D

m

m

m

c

j

m

(cid:0)

U

U

^

(j

1)

(cid:0)

(j

1)

except that hX

; I

i is (cid:12)xed to w

and the j

input bit of h

is set to

0

0

m

0

j

j

th

^x

(cid:12) Y

if c

= 0

m

j

0

j

(

B

if c

= 1:

j

j

Similarly, de(cid:12)ne E

(w

) to be the same as E

except that hX

; I

i is (cid:12)xed to w

.

(cid:0)

m

(cid:0)

0

0

m

j

j

(j

1)

(j

1)

Let

(j

1)

(j

1)

(j

1)

(cid:14)

(w

) = Pr[A(D

(w

)) = 1] (cid:0) Pr[A(E

(w

)) = 1]:

(cid:0)

(cid:0)

(cid:0)

m

m

m

c

j

c

j

Using A and sampling O(n=(cid:26)

) times from D

(w

) and E

(w

), produce an esti-

(cid:0)

c

j

m

(cid:0)

m

2

(j

1)

(j

1)

(j

1)

mate (cid:1)

(w

) so that

c

j

m

(cid:0)

(j

1)

(j

1)

n

Pr[j(cid:1)

(w

) (cid:0) (cid:14)

(w

)j > (cid:26)] (cid:20) 2

:

(cid:0)

(cid:0)

(cid:0)

c

j

c

j

m

m

Let m

2 f1; : : : ; (cid:28) g be the index for which (cid:1)

(w

) is maximized. Set hx

; i

i = w

,

0

c

j

m

0

0

0

j

j

m

0

(j

1)

(cid:0)

(j )

(j )

(j

1)

(j

1)

D

= D

(w

), E

= E

(w

) and go to the next stage.

c

j

m

0

(cid:0)

m

0

(cid:0)

Phase 2 :

Pick j 2

f0; : : : ; k

(cid:0) 1g. Let D

(w; r; b; y) be the distribution D

except

(j )

(j )

U

n

rst

that f

(X

; I

; R

) is set to f

(w; r) and the j + 1

input bit of h

is set to b and

0

0

0

0

0

0

j+1

j+1

j+1

and Y

is set to y . Let E

(w; r; y) be the same as E

except that f

(X

; I

; R

)

0

j+1

0

0

0

0

j+1

j+1

j+1

(j )

(j )

is set to f

(w; r) and Y

is set to y . Let (cid:12) 2

f0; 1g , let D be a sample of D

(w; r; b; y)

0

0

j+1

(j )

(j )

U

and let E be a sample of E

(w; r; y). If A(D) = A(E ) then output (cid:12) else output A(D).

We now prove that the oracle adversary M

as just described distinguishes as claimed

(A)

in the lemma. Let w = hx; ii, d

(w; r; b; y) = E[A(D

(w; r; b; y))] and e

(w; r; y) =

(j )

(j )

(j )

E[A(E

(w; r; y))]. Then,

(j )

(A)

(j )

(j )

Pr[M

(f

(w; r); b; y) = 1] = 1=2 + (d

(w; r; b; y) (cid:0) e

(w; r; y))=2:

0

Also, it follows directly from the de(cid:12)nitions that,

(j )

(j )

(j )

E[d

(w; R; x (cid:12) Y ; Y ) (cid:0) e

(w; R; Y )] = (cid:14)

(w);

0

and

(j )

(j )

(j )

E[d

(w; R; (cid:12) ; Y ) (cid:0) e

(w; R; Y )] = (cid:14)

(w):

1

37



<!-- pdf-page: 38 -->
(j )

(A)

(j )

(j )

Let (cid:15)

= E[(cid:14)

(W ) (cid:0) (cid:14)

(W )]: Thus, the distinguishing probability of M

is

0

1

(A)

(A)

(j )

(j )

(j )

~

E[M

(f

(W; R);

X (cid:12)Y ; Y )](cid:0)E[M

(f

(W; R); (cid:12) ; Y )] = E

[(cid:14)

(W )(cid:0)(cid:14)

(W )]=2 = E

[(cid:15)

]=2;

0

0

j

j

0

1

where j 2

f0; : : : ; k

(cid:0) 1g in the last two expectations. To prove the lemma, it is su(cid:14)cient

U

(j )

n

to show that E

[(cid:15)

]=2 (cid:21) (cid:26), or equivalently,

j

E[

(cid:15)

] (cid:21) 2(cid:26)k

= (cid:14)

=8:

(9)

n

n

(j )

j

0;:::;k

1

n

2f

(cid:0)

g

X

The expectation here is over the random choices of M

in the (cid:12)rst phase. Let (cid:14)

=

(A)

(j )

Pr[A(D

) = 1] (cid:0) Pr[A(E

) = 1]: We prove (9) by showing below that

(j )

(j )

(a)

E[(cid:14)

] (cid:20) 2

. The expectation is over the random choices of M

in the (cid:12)rst phase.

(cid:0)

(k

)

n

n

(A)

(b)

E[(cid:14)

(cid:0) (cid:14)

] (cid:20) (cid:15)

+ 4(cid:26). The expectation is over random choices in the j + 1

(j )

(j+1)

(j )

rst

stage of phase 1 conditional on any set of choices in the previous stages.

From (a) and (b), and because (cid:14)

= (cid:14)

, it follows that

n

(0)

(cid:14)

=2 < (cid:14)

(cid:0) E[(cid:14)

]

n

n

(k

)

n

=

E[(cid:14)

(cid:0) (cid:14)

]

(j )

(j+1)

j

0;:::;k

1

n

2f

(cid:0)

g

X

(cid:20) 4k

(cid:26) + E[

(cid:15)

]

n

(j )

j

0;:::;k

1

n

2f

(cid:0)

g

X

= (cid:14)

=4 + E[

(cid:15)

];

n

(j )

j

0;:::;k

1

n

2f

(cid:0)

g

X

and this proves the bound in Equation 9. Thus, it su(cid:14)ces to prove (a) and (b) above.

PROOF of (a) :

p

Since Pr[c

= 1] =

, applying Cherno(cid:11) bounds (e.g., see [MR : 95]),

j

n

we get that, with probability at least 1 (cid:0) 2

,

(cid:0)

n

c

(cid:21) k

(cid:0) k

= m

+ k

:

p

j

n

n

n

n

n

2=3

2=3

j

0;:::;k

1

n

2f

(cid:0)

g

X

The entropy of the input to h

conditional on the rest of the bits of D

is at least

0

(k

)

n

c

. So, if this sum is at least m

+k

, applying Lemma 4.5.1,

(D

; E

) (cid:20)

j

n

n

L

1

2=3

(k

)

(k

)

n

n

j

0;:::;k

1

n

2f

(cid:0)

g

n

(k

)

n

(k

)

n

(k

)

n

n

2

. Thus, (cid:14)

= E[A(D

)] (cid:0) E[A(E

)] (cid:20) 2

.

(cid:0)

(cid:0)

P

38



<!-- pdf-page: 39 -->
PROOF of (b) :

Let

W 2

T , and recall that W 2

T . Then, since the j + 1’st input

(cid:22)

of h

is always X

(cid:12) Y

in D

,

0

0

0

j+1

j+1

U

U

(j )

(j )

(j )

(j )

(cid:22)

(cid:14)

=

E[(cid:14)

(W )] + (1 (cid:0)

)E[(cid:14)

(

W )]

p

p

n

n

0

0

=

E[(cid:14)

(W )] +

(E[(cid:14)

(W )] (cid:0) E[(cid:14)

(W )]) + (1 (cid:0)

)(E[(cid:14)

(

W )])

p

p

p

n

n

n

1

0

1

0

(cid:22)

(j )

(j )

(j )

(j )

=

E[(cid:14)

(W )] +

(cid:15)

+ (1 (cid:0)

)(E[(cid:14)

(

W )])

p

p

p

n

n

n

1

0

(j )

(j )

(j )

(cid:22)

(j )

(j )

(j )

(cid:22)

< (cid:15)

+

E[(cid:14)

(W )] + (1 (cid:0)

)(E[(cid:14)

(

W )])

p

p

n

n

1

0

We now show that E[(cid:14)

] (cid:21)

E[(cid:14)

(W )]+ (1(cid:0)

)(E[(cid:14)

(

W )])(cid:0) 4(cid:26), and this concludes

p

p

n

n

1

0

(j+1)

(j )

(j )

(cid:22)

the proof. Let c 2 f0; 1g and consider stage j in phase 1. From our choice of (cid:28) and the

fact that 1=n (cid:20)

(cid:20) 1 (cid:0) 1=n, it follows that, with probability at least 1 (cid:0) 2

, at least

p

n

(cid:0)

n

n=(cid:26) of the w

’s are in T , and at least n=(cid:26) of the w

’s are in T . It then follows using

m

m

Cherno(cid:11) bounds that

Pr[ max

f(cid:14)

(w

)g (cid:21) maxfE[(cid:14)

(W )]; E[(cid:14)

(

W )]g (cid:0) (cid:26)]

c

c

c

m

(j )

(j )

(j )

(cid:22)

1

m

(cid:28)

(cid:20)

(cid:20)

is at least 1 (cid:0) 2

: Also, with probability at least 1 (cid:0) 2

, (cid:1)

(w

) is within (cid:26) of the

(cid:0)

(j )

(cid:0)

c

m

n

n

(j )

corresponding (cid:14)

(w

), and thus (recalling how w

is chosen above in stage j )

c

m

m

0

(j )

(j )

(cid:14)

(w

) (cid:21) (cid:1)

(w

) (cid:0) (cid:26)

c

c

m

0

m

0

=

max

f(cid:1)

(w

)g (cid:0) (cid:26)

c

m

(j )

m

1;:::;(cid:28)

2f

g

(cid:21)

max

f(cid:14)

(w

)g (cid:0) 2(cid:26)

c

m

(j )

m

1;:::;(cid:28)

2f

g

(cid:21) maxfE[(cid:14)

(W )]; E[(cid:14)

(

W )]g (cid:0) 3(cid:26)

c

c

(j )

(j )

(cid:22)

with probability at least 1 (cid:0) 3 (cid:1) 2

. Let (cid:14)

be the value of (cid:14)

conditional on

(cid:0)

c

n

(j+1)

(j+1)

c

= c. From this we can conclude that

j+1

(j+1)

(j )

(j )

(cid:22)

E[(cid:14)

] (cid:21) maxfE[(cid:14)

(W )]; E[(cid:14)

(

W )]g (cid:0) 4(cid:26):

c

c

c

Since c

= 1 with probability

,

p

j+1

n

(j+1)

(j+1)

(j+1)

E[(cid:14)

] =

E[(cid:14)

] + (1 (cid:0)

)E[(cid:14)

]

p

p

n

n

1

0

(cid:21)

E[(cid:14)

(W )] + (1 (cid:0)

)(E[(cid:14)

(

W )]) (cid:0) 4(cid:26):

p

p

n

n

1

0

(j )

(j )

(cid:22)

39



<!-- pdf-page: 40 -->
Before we continue let us just check that a good approximation of

is su(cid:14)cient. Sup-

p

n

pose that

(cid:20)

p

~p

(cid:20)

+

and we do the entire construction with

p

~p

replacing

.

p

n

n

n

n

n

1

Enlarge T to density

by making it contain some elements hx; ii with i =

(f (x)) + 1.

n

f

n

~p

~

D

Lemma 6.1.1 is easily seen to remain valid and Lemma 6.3.1 just becomes more true in

that the entropy of D decreases. This implies that it is su(cid:14)cient to try O(n) di(cid:11)erent

values of

.

p

n

7 A Direct Construction

We have shown how to construct a false entropy generator from an arbitrary one-way

function, a pseudoentropy generator from a false entropy generator and (cid:12)nally a pseudo-

random generator from pseudoentropy generator. The combinations of these constructions

gives a pseudorandom generator from an arbitrary one-way function as stated in Theo-

rem 6.2.2. By literally composing the reductions given in the preceding parts of this paper,

we construct a pseudorandom generator with inputs of length n

from a one-way function

34

with inputs of length n. This is obviously not a suitable reduction for practical applica-

tions.

In this subsection, we use the concepts developed in the rest of this paper, but

provide a more direct and e(cid:14)cient construction. However, this construction still produces

a pseudorandom generator with inputs of length n

, which is clearly still not suitable for

10

practical applications. (A sharper analysis can reduce this to n

, which is the best we

8

could (cid:12)nd using the ideas developed in this paper.) The result could only be considered

practical if the pseudorandom generator had inputs of length n

, or perhaps even close to

2

n. (However, in many special cases of one-way functions, the ideas from this paper are

practical, see e.g., [Luby : 96].)

The improvement in the direct construction given here comes from the observation that

more than one of the reductions involves a product distribution, whereas only one product

distribution is needed for the overall proof.

We start with a one-way function f : f0; 1g

! f0; 1g

. We construct f

as in equation (3),

0

n

‘

n

and let

be the probability that I (cid:20)

(f (X )) as in the previous section. Let X =

p

D

n

f

~

hX; I ; Ri represent the input distribution to f

, and let c

be the length of X and c

the

0

n

0

n

length of f

(X ). Let

=

(f

(X )). Let b((cid:31); y) = x (cid:12) y . Set k

= 2000n

.

e

H

0

n

0

n

6

Intuitively, we generate pseudo-random bits as follows: Let X

= X

and Y

= Y

. We

0

0

k

n

k

n

(cid:12)rst compute f

(X

) and b

(X

; Y

). Intuitively, we are entitled to recapture

0

0

0

0

k

n

k

n

bits from X

, because this is the conditional entropy left after we have computed f

and

0

0

k

n

k

c

(cid:0)

hf

(X

); b

(X

; Y

)i

H

0

0

0

0

n

n

k

n

k

n

40



<!-- pdf-page: 41 -->
k

n

k

n

b

. We are entitled to recapture k

bits from the b

(X

; Y

) (since we get a hidden bit

p

n

n

0

0

out of each copy whenever I (cid:20)

(f (X ))). Finally, we should be able to extract

k

bits

f

n

n

~

D

e

k

n

from f

(X

), since

0

0

e

n

is the entropy of f

(X ). Since b(n) is almost totally predictable

0

for almost all inputs where I (cid:21)

(f (X )),

D

f

~

H

e

p

hf

(X ); b(X ; Y )i (cid:20)

+

(cid:0) 1=n + 1=(2n):

0

n

n

(See the proof of Lemma 6.3.1.) Thus, if we add up all the output bits, we are entitled

to k

(c

+ 1=(2n)), or k

=(2n) more bits than the input to f

. However, our methods

n

n

n

0

k

n

of extracting entropy are not perfect, so we need to sacri(cid:12)ce some bits at each stage; to

use Corollary 4.5.3, we need to sacri(cid:12)ce 2nk

at each stage, so we chose k

to satisfy

n

n

2=3

k

=(2n) > 6nk

n

n

2=3

Formally, let m

= k

(c

(cid:0)

(cid:0)

+ 1=(2n)) (cid:0) 2nk

, m

= k

(cid:0) 2nk

, and

e

p

p

n

n

n

n

n

n

0

n

n

n

n

2=3

2=3

m

= k

(cid:0) 2nk

. Let R

, R

, and R

be indices of hash functions so that h

maps

e

00

n

n

n

n

1

2

3

R

1

2=3

k

c

bits to m

bits, h

maps k

bits to m

bits and h

maps k

c

bits to m

bits.

n

n

n

R

n

2

0

n

R

3

n

0

n

00

n

Our construction is as follows:

Construction 7.0.4

g(X

; Y

; R

; R

; R

) = hh

(X

); h

(b

(X

; Y

)); h

(f

(X

)); Y

; R

; R

; R

i:

0

0

0

0

0

0

0

0

1

2

3

R

R

1

2

R

3

1

2

3

k

n

k

n

Theorem 7.0.5

If f is a one-way function and g is as in Construction 7.0.4, then g is

a mild ly non-uniform pseudorandom generator. The reduction is weak-preserving.

PROOF:

It is easy to check that g outputs more bits than it inputs.

As noted above, the conditional entropy of X given f

(X ) and b(X ; Y ) is at least c

(cid:0)

(cid:0)

e

0

n

n

p

n

+(1=2n). Thus, from Corollary 4.5.3, we have that hh

(X

); R

i is statistically indistin-

R

1

0

1

guishable from random bits given hf

(X

); b

(X

; Y

); Y

i. Hence, g(X

; Y

; R

; R

; R

)

0

0

0

0

0

0

0

1

2

3

k

n

k

n

is statistically indistinguishable from hZ

; h

(b

(X

; Y

)); h

(f

(X

)); Y

; R

; R

; R

i,

1

R

2

R

3

0

0

0

0

0

1

2

3

k

n

k

n

where Z

2

f0; 1g

. Now, from Lemmas 6.3.2 and 6.1.1, it follows that h

(b

(X

; Y

))

m

n

k

n

1

U

R

2

0

0

k

n

is computationally indistinguishable from random bits given hf

(X

); R

; Y

i. Thus,

0

0

2

0

g(X

; Y

; R

; R

; R

) is computationally indistinguishable from

0

0

1

2

3

hZ

; Z

; h

(f

(X

)); Y

; R

; R

; R

i;

0

0

0

1

2

R

1

2

3

3

k

n

0

m

n

k

n

where Z

2

f0; 1g

. Finally, from Corollary 4.5.3, hh

(f

(X

)); R

i is statistically

2

U

R

3

0

0

3

00

m

n

indistinguishable from hZ

; R

i, where Z

2

f0; 1g

. Thus, the output of g is compu-

3

3

3

U

tationally indistinguishable from a truly random output of the same length.

If we use hash functions constructed as Toeplitz matrices then O(m) bits is su(cid:14)cient to

construct a hash function on m bits and the inputs needed for the hash function is just a

constant fraction of all inputs. Then, the input length to g is O(nk

) = O(n

).

n

7

41



<!-- pdf-page: 42 -->
We still need to use Proposition 4.8.1 to get rid of the mild non-uniformity. From the

arguments above, it is clear that an approximation of both

and

that is within 1=(8n)

e

p

n

n

of their true values is su(cid:14)cient. Since 0 (cid:20)

(cid:20) n, and 0 (cid:20)

< 1, there are at most

e

p

n

n

3

3

O(n

) cases of pairs to consider. This means that we get a total of O(n

) generators,

each needing an input of length O(n

). Thus the total input size to the pseudorandom

7

generator is O(n

), as claimed.

10

8 Conclusions

A general problem is to characterize the conditions under which cryptographic applica-

tions are possible. By conditions we mean complexity theoretic conditions, e.g., P 6= NP,

the existence of one-way functions, etc. Examples of cryptographic applications are pri-

vate key cryptography, identi(cid:12)cation/authentication, digital signatures, bit commitment,

exchanging secrets, coin (cid:13)ipping over the telephone, etc.

For a variety of cryptographic applications it is known that a secure protocol can be

constructed from a pseudorandom generator, e.g., the work of [GGM : 86],

[LR : 88],

[GMR : 89], [Naor : 88], [GMW : 91], show that applications ranging from private key en-

cryption to zero-knowledge proofs can be based on a pseudorandom generator. The results

presented in this paper show that these same protocols can be based on any one-way func-

tion. The paper [NY : 89] gives a signature scheme that can be based on any one-way

permutation, and [Rom : 90], substantially improves this by basing such a scheme on any

one-way function.

Using the notion of a false entropy generator, [G : 89] shows that the existence of pseu-

dorandom generators is equivalent to the existence of a pair of

-samplable distributions

P

which are computationally indistinguishable but statistically very di(cid:11)erent.

The paper [IL : 89] provides complementary results; a one-way function can be constructed

from a secure protocol for any one of a variety of cryptographic applications, including

private key encryption, identi(cid:12)cation/authentication, bit commitment and coin (cid:13)ipping by

telephone. The paper [OW : 93] shows that a one-way function can be constructed from

any non-trivial zero-knowledge proof protocol. Thus, secure protocols for any of these

applications is equivalent to the existence of one-way functions.

The results described in this paper and the previous three paragraphs show that the

existence of a one-way function is central to modern complexity based cryptography.

Some applications seem unlikely to be shown possible based on any one-way function,

e.g., [IR : 89] give strong evidence that exchanging secrets over a public channel is an

application of this kind.

42



<!-- pdf-page: 43 -->
A fundamental issue is that of e(cid:14)ciency, both in size and time; the general construction

we give for a pseudorandom generator based on any one-way function increases the size

of the input by a large polynomial amount and thus is only weak-preserving. This is not

good news for practical applications; it would be nice to have a general poly-preserving or

a linear-preserving reduction.

9 Acknowledgements

This research evolved over a long period of time and was greatly in(cid:13)uenced by many people.

We thank Amos Fiat, Moni Naor, Ronitt Rubinfeld, Manuel Blum, Steven Rudich, Noam

Nisan, Lance Fortnow, Umesh Vazirani, Charlie Racko(cid:11), Oded Goldreich, Hugo Krawczyk,

and Silvio Micali for their insights and contributions to this work. We in particular thank

Charlie, Umesh and Manuel for their advice and enthusiasm, and Oded and Hugo for

exposing the fourth author to their wealth of insights on this problem. Finally, Oded’s

insightful comments on every aspect of earlier versions of this paper has improved the

presentation in many ways.

References

[ACGS : 88] Alexi, W., Chor, B., Goldreich, O., Schnorr, C.P., \RSA Rabin Functions:

Certain Parts Are As Hard As the Whole", SIAM J. on Computing, Vol. 17,

1988, pp. 194{209.

[BFNW : 96] L. Babai, L. Fortnow, N. Nisan, A. Wigderson, \BPP has Subexponential

Time Simulations unless EXPTIME has Publishable Proofs", Complexity

Theory, Vol 3, 1993, pp. 307{318.

[BBR : 88] Bennett, C., Brassard, G., Robert, J., \Privacy Ampli(cid:12)cation by Public Dis-

cussion", Siam J. on Computing, Vol. 17, No. 2, 1988, pp. 210{229.

[Blum : 84] Blum, M., \Independent Unbiased Coin Flips From a Correlated Biased

Source: A Finite State Markov Chain", 25

IEEE Symposium on Foun-

th

dations of Computer Science, 1984, pp. 425{433.

[BM : 82]

Blum, M., and Micali, S., \How to Generate Cryptographically Strong Se-

quences of Pseudo-Random Bits", SIAM J. on Computing, Vol. 13, 1984, pp.

850{864.

[BH : 89]

Boppana, R., Hirschfeld, R., \Pseudo-random generators and complexity

classes", S. Micali, ed., Advances in Computer Research, vol. 5, pp. 1{26,

JAI Press, 1989.

43



<!-- pdf-page: 44 -->
[Boyar : 89] Boyar, J. \Inferring Sequences Produced by Pseudo-Random Number Gen-

erators", Jour. of ACM, Vol. 36, No. 1, 1989, pp.129{141.

[CW : 79]

Carter, L., and M. Wegman, \Universal Classes of Hash Functions", JCSS,

1979, Vol. 18, pp. 143{154.

[CG : 88]

Chor, B., and O. Goldreich, \Unbiased Bits from Sources of Weak Random-

ness and Probabilistic Communication Complexity", SIAM J. on Computing,

Vol. 17, 1988, pp. 230{261.

[DH : 76]

Di(cid:14)e, D., and Hellman, M., \New directions in cryptography", IEEE Trans.

Inform. Theory, Vol. 22, 1976, pp. 644{654.

[G : 89]

Goldreich, O., \A Note on Computational Indistinguishability", ICSI Tech

Report TR-89-051, July 1989.

[GGM : 86] Goldreich, O., S. Goldwasser, and S. Micali, \How to Construct Random

Functions", J. of ACM, Vol. 33, No. 4, 1986, pp. 792{807.

[GKL : 93] Goldreich, O., Krawczyk, H. and Luby, M., \On the Existence of Pseudoran-

dom Generators", SIAM J. on Computing, Vol. 22, No. 6, December, 1993,

pp. 1163{1175.

[GL : 89]

Goldreich, O., and L.A. Levin, \A Hard-Core Predicate for any One-way

Function", 21

ACM Symposium on Theory of Computing, 1989, pp. 25{

rst

32.

[GMW : 91] Goldreich, O., Micali, S., and Wigderson, A., \Proofs that Yield Nothing

But their Validity or All Languages in NP have Zero-Knowledge Proofs", J.

of the ACM, Vol. 38, No. 3, July 1991, pp. 691{729.

[GM : 84]

Goldwasser, S. and Micali, S., \Probabilistic Encryption," JCSS, Vol. 28, No.

2, April 1984, pp. 270{299.

[GMR : 89] Goldwasser, S., Micali, S. and Racko(cid:11), C., \The Knowledge Complexity of

Interactive Proof Systems," SIAM J. on Computing, Vol. 18, No. 1, 1989,

pp. 186{208.

[GMT : 82] Goldwasser, S., Micali, S. and Tong, P., \Why and how to establish a pri-

vate code on a public network," 23

IEEE Symposium on Foundations of

rd

Computer Science, 1982, pp. 134{144.

[H(cid:23)as : 90]

H(cid:23)astad, J. \Pseudo-Random Generators under Uniform Assumptions", 22

nd

ACM Symposium on Theory of Computing, 1990, pp. 395{404.

[HL : 92]

Herzberg, A., Luby, M., \Public Randomness in Cryptography", proceedings

of CRYPTO 1992, ICSI technical report TR-92-068, October, 1992.

44



<!-- pdf-page: 45 -->
[IL : 89]

Impagliazzo, R. and Luby, M., \One-way functions are essential for informa-

tion based cryptography," 30

IEEE Symposium on Foundations of Com-

th

puter Science, 1989, pp. 230{235.

[ILL : 89]

Impagliazzo, R., Levin, L. and Luby, M, \Pseudo-random number generation

from one-way functions", 21

ACM Symposium on Theory of Computing,

rst

1989, pp. 12{24.

[IN : 96]

Impagliazzo, R., Naor, M., \E(cid:14)cient Cryptographic Schemes Provably as

Secure as Subset Sum", J. of Cryptology, Vol. 9, No. 4, pp. 192-216, 1996.

[IR : 89]

Impagliazzo, R. and Rudich, S., \Limits on the Provable Consequences of

One-way Functions", 21

ACM Symposium on Theory of Computing, 1989,

rst

pp. 44{56.

[IZ : 89]

Impagliazzo, R., and Zuckerman, D. \How to recycle random bits", 30

th

IEEE Symposium on Foundations of Computer Science, 1989, pp. 248{253.

[Knuth : 81] Knuth, D., Semi-Numerical Algorithm, The Art of Computer Programming,

Addison-Wesley, Second Edition, Vol. 2, Chapter 3, 1981. (Third Edition,

expected 1997).

[Kol : 65]

Kolmogorov, A. N., \Three Approaches to the Concept of the Amount of

Information", Probl. Inf. Transm., Vol 1, (1), 1965, pp. 1{7.

[Kraw : 92] Krawczyk, H., \How to Predict Congruential Generators", Journal of Algo-

rithms, Vol. 13, 1992. pp. 527{545.

[Levin : 87] Levin, L.A., \One-way Function and Pseudorandom Generators", Combina-

torica, Vol. 7, No. 4, 1987, pp. 357{363.

[Levin : 93] Levin, L.A., \Randomness and Non-determinism", \One-way Function and

Pseudorandom Generators", J. of Symb. Logic, Vol. 58, No. 3, 1993, pp.1102{

1103.

[Luby : 96] Luby, M.,

Pseudorandomness and Cryptographic Applications

,

Princeton Computer Science Notes, Princeton University Press, 1996.

[LR : 88]

Luby M., and Racko(cid:11), C., \How to Construct Pseudorandom Permutations

From Pseudorandom Functions", SIAM J. on Computing, Vol. 17, No. 2,

1988, pp. 373{386.

[McEl : 78] McEliece, R. J., \A public key cryptosystem based on algebraic coding the-

ory", DSN progress report, Jan.-Feb., 1978, Jet Propulsion Laboratory, Cal-

ifornia Institute of Technology.

45



<!-- pdf-page: 46 -->
[McIn : 87] McInnes, J., \Cryptography Using Weak Sources of Randomness," Tech.

Report 194/87, U. of Toronto, 1987.

[MR : 95] Motwani, R. and Raghavan, P.,

, Cambridge Uni-

Randomized Algorithms

versity Press, 1995.

[Naor : 88] Naor, M., \Bit Commitment using Pseudorandom Generators", J. of Cryp-

tology, Vol. 4, pp. 151{158, 1991. Preliminary version appears in Crypto 89,

pp. 123{132, 1990.

[NY : 89]

Naor, M. and Yung, M., \Universal One-way Hash Functions and Their Ap-

plications", 21

ACM Symposium on Theory of Computing, 1989, pp. 33{43.

rst

[OW : 93]

Ostrovsky, R and Wigderson, A., \One-way Functions are Essential for Non-

Trivial Zero-Knowledge", 2

Israel Symposium on the Theory of Computing

nd

and Systems, 1993, pp. 3{17.

[Renyi : 70] Renyi, A.,

, North-Holland, Amsterdam, 1970.

Probability Theory

[RSA : 78] Rivest, R., Shamir, A., and Adleman, L., \A method for obtaining digital

signatures and public-key cryptosystems", Comm. of the ACM, Vol. 21, 1978,

pp. 120{126.

[Rom : 90] Rompel, J., \One-way Functions are Necessary and Su(cid:14)cient for Secure Sig-

natures", 22

ACM Symposium on Theory of Computing, 1990, pp. 387{394.

nd

[SV : 86]

Santha, M. and Vazirani, U., \Generating Quasi-random Sequences from

Slightly-random Sources", JCSS, Vol. 33, No. 1, 1986, pp. 75{87.

[Shan : 48]

Shannon, C., \A Mathematical Theory of Communication", Bel l Systems

Technical Journal, 27, 1948, pp. 379{423 and pp. 623{656.

[Sip : 83]

Sipser, M., \A Complexity Theoretic Approach to Randomness", 15

ACM

th

Symposium on Theory of Computing, 1983, pp. 330{335.

[Vaz : 87]

Vazirani, U., \Towards a Strong Communication Complexity Theory or Gen-

erating Quasi-random Sequences from Two Communicating Slightly-random

Sources", Combinatorica, Vol. 7, No.4, 1987, pp. 375{392.

[VV : 85]

Vazirani, U. and Vazirani, V., \Random Polynomial Time is Equal to

Slightly-random Polynomial Time", 26

IEEE Symposium on Foundations

th

of Computer Science, 1985, pp. 417{428.

[Yao : 82]

Yao, A.C., \Theory and Applications of Trapdoor Functions", 23

IEEE

rd

Symposium on Foundations of Computer Science, 1982, pp. 80{91.

46


