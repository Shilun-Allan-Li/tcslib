<!-- generated-by: proofmatch local extraction -->
<!-- source-pdf-sha256: 63759bd909d5b75d76be750f9993ce95106bf03476e9e13d7791bd54f3a19ff9 -->
<!-- extractor: pdfminer.six v20260107 -->

<!-- pdf-page: 1 -->
Constant

Depth Circuits,

Fourier

Transform,

and

Learnability

NATHAN

LINIAL

Hebrew University,

Jenmdem,Israel

YISHAY

MANSOUR

Te[-Alio

University,

Tel-Aui[\

Israel

AND

NOAM NISAN

Hebrew UniLersi@ Jerusalem,

Israel

In this paper, Boolean

Abstract.
cube. The main result
the low-order
This result

coefficients.
implies

in ,4C0 are studied using harmonic

functions
is that an ACO Boolean function
of
functions
well by a real polynomial

An important
several new properties
they may be approximated

has almost all of

in -4C[’: Functions
of

analysis on the
on
lemma [8].
in AC() have low
low degree and they

is Hastad’s

its “power

spectrum”

ingredient

the proof

switching

of

“average sensitivity;”
cannot be pseudorandom function

generators.

Perhaps

the most

interesting

application

is an O(n POIYIOg(n‘)-time

tions in ACO. The algorithm observes the behavior of an AC’”
chosen inputs, and derives a good approximation
approximation
other

allows the algorithm to predict, with high probability,

chosen inputs.

the Fourier

randomly

for

function

algorithm for

learning

func-
on O(nPO’Y’Og(n)) randomly
This
on

the function.

the function

the value of

transform of

A preliminary
Foundations

version of

of Computer

this paper was published
Science.

IEEE, New York,

1989, pp. 574-579.

in Proceedings

of

the 30th Annual

Symposuun

on

The research of Y. Mansour was done while he was at
Massachusetts
of Technology,
tion (NSF) grant CCR 86-5727, Army Research Office (ARO)
ISEF fellowship.

and was partially

Institute

the Laboratory
supported

by National
program DALL

for Computer

Science,
Science Founda-
and
03-86-K-017,

The research of N. Linial was done while he was visiting
Stanford University.

IBM Almaden

Research Center

and

The research of N. Nisan was done while he was working
Massachusetts
and was partially
and ARO program DALL

of Technology
03-86-017.

Institute

at the Laboratory
supported

of Computer Science,
by NSF grant CCR 86-5727

and N. Nisan, Department

of Computer

Isrdel; Y. Mansour, Computer Science Department,

Science, Hebrew Univer-
Tel-Avw

Tel-Aviv University,

to copy without

addresses: N. Linial

Authors’
sity, Jerusalem,
Israel.
Permission
not made or distributed
of
Association
specific permission.
Q 1993 ACM 0004-5411/93/0700-0607

the publication

for Computing Machinery.

fee all or part of
for direct commercial

this material
advantage,

is granted provided
the ACM copyright

and its date appear, and notice is given that copying is by permission

that
the copies are
notice and the title
the

of

To copy otherwise,

or to republish,

requires a fee and/or

$01.50

Journal

of

the Asoclatiun

for Computing

Machinery,

Vol.

40, No

3. July

1993.

pp

607–620,



<!-- pdf-page: 2 -->
608

N. LINIAL

ET AL.

Categories and Subject Descriptors:
tion—probubikmc
cal Algorithms
[Mathematics of Computing]: Probabihty and Statistics—probabilistic algorithms;
Intelligence]: Learning—concept

F.1.2 [Computation by Abstract Devices]: Modes of Computa-
F.2. 1 [Analysis of Algorithms and Problem Complexity]: Numeri-
G.3
1.2.6 [Artificial

and problems—cornputatlons

on polynomials:

compzmzticm;

computations

learning

transforms,

of

General Terms: Algorithms,

Theory, Verification

Additional
complexity,

Key Words
Fourier

transform,

harmonic

analysis learning.

and Phrases: ACO circuits,

approximation,

Booledn

functions.

circuits.

1.

Introduction

Harmonic

analysis

is widely

used throughout

classical mathematics

(see [4]).

Recently,

Kahn

et al.

[9] suggested

using harmonic

analysis

on the hypercube

in

the study of Boolean

functions.

They

proved

some inequalities

which

Fourier

coefficients

of Boolean

functions

must

satisfy,

and derived

as a result

bounds

on the “influence”
used in [3]
CNF.

to obtain

of variables
lower

on Boolean
for

bounds

functions.

Harmonic

the size of decision

analysis was
and

trees, DNF,

In this paper, we study

how the conzputational

complexip

of Boolean

func-

tions

is related with

their

Fourier

transform.

Specifically,

we study

the Fourier

transform
inequality

of
that

functions

computable

by constant

the transform

of such functions

depth
satisfies.

circuits
This

and derive

an
is then

inequality

used to establish

new results

on complexity

and learnability

of constant

depth

circuits.

The best-known
large

lower
size to compute

bound

for constant

depth

the parity

function

circuits
[1, 5, 8, 20].

is that

they require
small

In fact,

depth

circuits

cannot

even decently

approximate

the parity

function

a very
constant

(see [81). This
Fourier
parity

coefficient
the input

of

fact

directly
bears
of ~ measures,
bits in S. Consequently,

on the Fourier
by definition,

transform,
the correlation
Fourier

each “high”

because

the Sth
~ the
of a

between
coefficient

function

computable

by a small

constant

depth

circuit

must

be very

small

(“high”

means

coefficients

corresponding

to sets of

large

cardinality).

Our Main
“high”

ual

Lemma

is an extension

Fourier

coefficient

small,

of
but

this

fact: Not
the

in fact

only
sum of

is each

individ-

squares

(the

“power

spectram”)

associated

with

all high Fourier

coefficients

is very

small.

Specifically:

MAIN

LEMMA.

Boolean

circuit

Let

function
f be a Boolean
of depth d and size M, and let

on n l’ariables

computable

by a

t be any integer. Then

x
n}.lsl>f

Sc{l

f(s)’

< 2&f2-’’’/2o,

where ~(S)

denotes

the Fourier

Transform off

at S.

The

first

application

of

this

lemma

is an

algorithm

for

learning

Boolean

functions.

To

learn

functions

computed

by a polynomial-size,

ACO

con-

stant-depth
behavior
allows
“low”

it
Fourier

of
to derive

circuit,
the circuit

the

algorithm

proceeds
on 0( np”’y’o~(”) ) inputs

as follows:
chosen

uniformly

It

first

observes
at random;

(with

high probability)

a very good approximation

coefficients

of

the function

computed

by the circuit.

the
this
to all
the
Since the

“high”
“power,”

coefficients
these

are guaranteed
of

approximations

by the Main

Lemma

to have

the “low”

Fourier

coefficients

little
very
are informa-



<!-- pdf-page: 3 -->
Constant Depth Circuits,

Fourier

Transform,

and Learnability

tive enough

to predict

the behavior

of

the circuit

on inputs

chosen

uniformly

random.

Since there

are only a few “low”

coefficients,

the approximation

be done “efficiently.”

609

at

can

There

are three

key ideas on which

this learning

algorithm

relies. The first

is

that

lower

bounds

(i.e.,

negative

results) may be used

to construct

learning

algorithms

(i.e.,

positive

results).

A

similar

phenomenon

appears

in the

study

of pseudorandom

generators,

where

lower

bounds

are used

in

order

to deterministically

simulate

randomized

algorithms

[13, 19]. The second

one says that
cients,

learning
an observation

can be achieved
that may be useful

through

estimating

the Fourier

elsewhere

as well. The

third

coeffi-
is the

application

of

real arithmetic

and real valued

functions

to approximate

Boolean

functions.
Our
introduced

polynomial
distribution

algorithm

does not

fall

into

by [18]. First

and foremost,

the
it

category
runs

distribution-fi-ee
in time O(rzpO1ylOg(“)) and not

learning,

of

in

time. Secondly,
on inputs,

it

learns

circuits

only under

the uniform

probability

and not under

an arbitrary

distribution.

On the positive

side,

the

concept

class being

learned

is substantially

richer

than

previously

achieved,

Earlier

positive

results

in learning

involve

classes whose

combinato-

rial

complexity

is much more

restricted,

for

example,

k-DNF

[18],

k-decision

lists [15], etc. Results

involving

richer

classes, as iVCl,

have been negative

(see

[10]).

Based
properties

on our Main
functions

of

Lemma,
in AC”.

we derive

a number

of additional

interesting

(1) Every

function

low degree.

in ACO can be approximated
the results

complements

This

well

by a real polynomial

of

[14] and [17],

showing

of
that

such an approximation

is possible

over

finite

fields.

(2) Every

function

in AC()

has low-average

sensitivity

to its input.

Changing

one bit of

the input

is very unlikely

to change

the value

of

the function,

when

the original

input

and the bit are chosen

at

random.

(3) Functions
sense of

in AC”

cannot

be pseudorandom

function

generators

in the

[6].

(4) Functions

in ACO cannot

distinguish

polynomially
(A polynomially

bounded

polylog-wise

bounded

distribution

between
independent
over Z:

uniform

distributions

and

probability
is a distribution

distributions.
in which

any

input

has probability

less than poly(n)/2”.)

The

paper

is organized

as follows:

Section

2 is devoted

to

notations

and

definitions.

It

includes

all

the

necessaxy

background

on Fourier

trans-

form on the
4 is devoted

hypercube.

The Main

Lemma

is proved

in section

to

the

learning

algorithm

and

Section

5 contains

3. Section
further

applications

of

the Main

Lemma.

2. Notation

2.1. FOURIER TRANSFORM.
functions

ered as real valued
on the cube is a 2 “-dimensional
by

fi

Boolean
{O, 1}”
real vector

functions
-

{ – 1, 1}. The set of all

space with

an inner

on n variables

will be consid-
functions
real
defined
product

(g>.f-)

= 2-”

Jrf(x)g(x)

= -E(d)



<!-- pdf-page: 4 -->
610

(where
= ~~-,

and as usual

the norm of a function

is defined:

11~11

N. LINIAL ET AL.

E is expectation)
which

is the Euclidean

norm.

Many

of

the elementa~

facts in harmonic

analysis maybe

interpreted

in the

following

way: Consider

the linear

space of

real

functions

defined

on a group,

a

choice

of a basis for

clever
basis is given by the characters
group
{1 ,.

this linear
of
and the basis is defined
XS:

..> n}, define

is the cube Z;

the function

the group

space may be very helpful.

at hand.

as follows:

In the present

This

special
the
For each subset S of

case,

x~(x~,

. . ..xn)

=

+ 1

– 1

{

if

if

Z,=~

x,

is even,

Z, ~s x,

is odd.

The following

properties

of

these functions

can all be easily verified:

—For

every A, B: X,4 XB = x~~~, where

AA B is the symmetric

difference

of

A and B.

—The

family

{ xs.}

for all S c {1 . . . n}

forms

an orthonormal

basis,

that

is,

if

A #B,

then

(x~,,y~)

= O, and for every A,

(x~,x~)

= 1.

Any

real-valued

function

on the cube can be uniquely

expressed

as a linear

combination

of

the XS‘s, namely,

X$ c~ xs, where

c~ are real

constants.

These

coefficients
function’s

(c being

Fourier

viewed
transform.

as a real

function

on the

cube)

For

aAfunction

~ and S c {1,...,

constitute
n},

the
the Sth

Fourier

coefficient

of S denoted

by ~(S)

is what was previously

called

c-~, that

is, ~ = ~~ ~(S)x~.

Since the XS’s are an orthonormal

basis, Fourier

coefficients

are found

via:

f(’$)= (“flxs).

For Boolean

~,

this specializes

to:

.f?S)

=Pr

~(x)

[

= @xl
1=s

–Pr

1[

jlx)

+

Oxl
1=s

,

1

where

xZ,
x = (xl,
The orthonormality

...,

x.)
of

is chosen

uniformly

at

random in {O, 1}”.

the basis implies

Parseval’s

identity:

llfll’ =

x
Sc{l..,

n}

f(s)’.

Note

that

if ~ is Boolean

then

11~11= 1.

Finally we define

the de~;ee of a Boolean

function,

deg( ~)

the largest
real

(multi-linear)

polynomial.

set S such that ~(S)

# O. Note

that

this equals

to be the size of
of ~ as a

the degree

2.2. ACO CIRCUITS.

An

AC()

circuit

consists

inputs

xl,

. . ..x~

and 21, ...,1,,.

Fanin

to the gates is unbounded.

of AND and OR gates, with
The size of

of

(i.e.,

the gates)

is bounded

the number

the circuit
its depth
leveled, where
the same level have the same type, which
description,
more
putable

by a constant. Without
i have all

see [5],
of depth

by an ACO circuits

gates at

detailed

level

their

inputs

is alternately

loss of generality,
from level
AND
set of
by AC O[d].

[8], and [20].) The

d is denoted

is bounded

by a polynomial

in n, and
the circuit
is
i – 1, all gates at
a

(For

and OR.
functions

com-



<!-- pdf-page: 5 -->
Constarzt Depth Circuitsj

Fourier

Transformj

and Learnability

611

2.3. RANDOM

RESTRICTION.

A restriction

variables

to O, 1, and *. The function

obtained

p is a mapping
from f(xl,

...,

of

the

input

x,, ) by applying

a

restriction

p,

is denoted

by fP,

its variables

are those

x,

for which

p(x,

) = *,

all other

variables

are set according

to p.

For

a set S=

{x,,,...,

x,,,}

and

a vector

R = (rl,

...,

rlsl) G {O, l}lsl,

let

S - R denote

the restriction

p, such that

p(x,,)

= rj,

for x,, ~ S, and P(X) = *,

for x @ S.

A random

restriction

with

a parameter

p is obtained

by setting

each

independently.
*1 = p,
abbreviate

We

choose

a value

from

{*, O, 1},

such

that

Pr[ p(xl)

and Pr[ p(xl)
the notation

= 1] = Pr[ p(x~) = O] = (1 – p)/2.

and write Pr[ * ] rather

than Pr[ p(x,

In many
) = *].

cases, we

xl,

=

2.4. MISCELLANEOUS.

The complement

of a set S c {1 . . . n}

is denoted

by

SC. For a real
negative

number
r,
and sigrz(0) = O.

the value

of sign(r)

is 1 if

r

is positive,

– 1 if

it

is

A minterm
that

property

of a Boolean
all of
setting

function

is a minimal

set of variables

them to one forces

the function

to be one.

with

the
(In the

restriction

language,

it

is a minimal

set of variables

S such that

f~ + Jx)

-

1.)

A maxterm is as minimal

set of variables

S that

forces

the function

to be zero

(i.e., ~$+,

- O).

3. Main

Lemma

Hastad’s

Switching

Lemma

[8] states

that ACO functions

tend

to simplify

in a

significant
the main
originally

way when

subjected

the present

tool of
made by Hastad.

to random restrictions.
article. We use a stronger
by Hastad

It was observed

This beautiful
statement
and Boppana

lemma
is
than the one
(see [8, p.

65])

that

the original

proof

yields

this stronger

version

as well.

LEMMA

1 (HASTAD).

Let

f be gillen by a CNF formula

where each clause has

size at most

t,

and

choose

a random

Pr[ p(x,)

= * ] = p). With probability

of at

restriction
least 1 – (5pt)’,

p with

parameter

p

(i.e.,

fP can be expressed as

a DNF formula

each clause of which

has size of at most s, and the clauses all

tZCCepl disjoint

sets of

inputs.

We require

the following

simple

corollary,

COROLLARY

1.

If

f

is given by a CNF

(or DNF ) of bottom fanin

at most

t,

and p is chosen at random with Pr[ * ] = p,

then

pr[deg(fP)

> s] < (5pt)’.

PROOF.

Whenever

fP satisfies

conditions

(1) and (2) of Hastad’s

lemma

the

following
for

also holds: For every

set S,
the same number

IS I > s, each clause

of strings

having

of

the DNF
even or odd parity

formula

on

fP accepts

exactly

S. This happens
the clause
the
number

clauses

(since

of strings

because

at
the clause

least one of
size is bounded
sets of

inputs

all accept

disjoint

having

even or odd parity

and
on S.

the variables

in S does not appear

by s). The corollary
thus

fP accepts

follows

in
since
an equal

Repeated

application

of Hastad’s

lemma

yields

the following

lemma.

q


<!-- pdf-page: 6 -->
612

N. LINIAL ET AL.

LEMMA 2.

Let

f be a Boolean

function

computed

by a circuit

of size M and

depth d. Then

P~[deg(fP)

> s)]

s M2-S,

where p is a random restriction

with

~r[*]=

1lod~d-1

“

PROOF.

We view the

restriction

p as obtained

by first

having

a random

restriction

with

Pr[ * ] = 1/10,

and then

d – 1 consecutive

restrictions

each

with Pr[ * ] = 1/(10

s).
probability,

With

high

after

the first

restriction,

at

the bottom level

of

the

circuit

all

fanins

are at most

s. To see this, we consider

two cases for each gate

at

the bottom level of

the original

circuit:

(1)

The original
fanin
was not eliminated

is at
by p,

least 2s.
is,

that

In this case,
that no input

the probability
to this gate got assigned

that

the gate

a O

(assuming
is at most 0.552’ < 2-’;

without

loss of generality

that

the bottom level

is an AND level)

(2)

The original

fanin

is at most 2s.

In this case,

the probability

that

at

least

s

inputs

got assigned

a *

is at most

2S 0. IS <2-’.

()

Thus,

the probability

failure

at

this stage is at most ml 2 ‘;, where ml

is the number

of gates

of

at

the bottom level.

We now apply

d – 2 more

restrictions

with Pr[ * ] = 1/( 10,s). After

each

of

these, we use Hastad’s

switching

lemma

to convert

the lower

two levels

from

to

DNF

CNF
levels (from the bottom)
of

distance

two

(or

vice

versa),

to one level,

collapse

the

the depth

second

third
by one. For each gate

and

from the

inputs,

probability

that

it

has

a minterm

and
reducing
the

(respectively,
that

some gate has a minterm

maxterm)

of size larger

than
(respectively,

s, is bounded
maxterm)

by 2-s. The probability

larger

than

s is no more

than ml 2 ‘$, where m,

is the number

of gates at

level
a CNF (or DNF)

i.

After

these d – 2 stages we are left with

formula

of bottom

fanin

at most

s. We now apply

the last

restriction

with Pr[ * ] = 1/(10,s)

and by

1 get a function
Corollary
this stage is at most 2‘s.

with

degree

at most

s. The probability

of

failure

at

To compute

the total

probability

of

failure,

we observe

that each gate of

the

original

circuit

contributed

2–’

probability

of

failure

exactly

once.

At

this point, we start

analyzing

the probability

of

its restrictions

having

how the Fourier

f
low degree. We start with

transform

of

to

relates
a lemma

relating
restrictions.

the Fourier

transform

of a function

f with

the

transforms

of

its

LEMMA

llariables.

3.
Then,

Let

f be a Boolean

fimction

and S an arbitra~

subset of

the

for any subset of

the uariables A:

f(A) = 2-’s” X X.4ns(R)i’+~(A

R l {O, I}ls’l

n ‘).

q


<!-- pdf-page: 7 -->
Constant Depth Circuits,

Fourier

Transform,

and Learnability

613

PROOF.

first

averaging

Recall

!(A)
that
over variables

f XA ].

= El[
in S and then

In the right-hand
in variables

side, we are simply
in S’. We can rewrite

the right-hand

side as:

First, we can rearrange

the summation

such that,

‘2-1s”1

~

‘2-ISI

~

RI l{0,

l)ISCI

R2G{0,1}IS

XAn Sc(Rl)XAn

S(R2)fS’+R$R2).

Note

that

XAn Sc(Rl)XAn

S(R2)

= X,4(X):

where

x, when

restricted

to the variables

in S’,

is RI and when

restricted

to

the variables

in S is Rz. Similarly,

fs. ~ ~JRz ) = f(x).

Furthermore,

averaging

over RI

and Rz

is like

averaging

over

x = {O, 1}”.

Finally,

by

definition

1S1+ IScl = n;

therefore,

we can rewrite

the expression

as,

which

is by definition

~(A).

LEMMA

4.

Let

f be a Boolean

function

and S an arbitray

subset. For any

BcS:

PROOF.

By Lemma

3

~(11 u C)’

=

~
Ccs’

~
Ccs’

2-IS(I

(

~
R l{0,

l)ISCI

x,uC(R)~,

+~((B

u C)

n S)

2.

)

Note

that

XB” C(R) = XC(R)

and

(B u C) n S = 1?. Therefore,

the

above

expression

equals:

Now we can simply multiply

and get

2-1s’1

x
RI={O,l)IS’I

~ &+RfB)&+RjB)
1

2-1s’1~XC(R1 @ R2)

Ccs’

[

.

R2G{0,1)ISCI

One can verify
otherwise

that
zero. Therefore,

the expression

between

the expression

the brackets
can be simplified

to

is one if RI = Rz and

2-ISCI

~

&+

R(B)2>

R= {O, l}ISCI

which

completes

the proof.

q
q


<!-- pdf-page: 8 -->
614

N. LINIAL ET AL.

LEMMA 5.

Let

f be a Boolean

function,

San

arbitra~

subset, and k an integer.

The?l

~

~(A)2

<F’r[deg(f~.+~)

> k],

.4,1,4 nSl>k

where R is a O– 1 assignment

to the variables

in SC chosen at random.

PROOF.

The main

idea

is the

following:

Consider

an arbitra~

assignment

R.

If deg( f~. ~ ~) s k,

then for any A, such that

IA n SJ > k,

the correspond-

ing

Fourier

coefficient

is

zero,

that

is,

theA other

On
xl ~1> ~ fs. ~ ~(B)2

hand,

since
is bounded

~$. ~ ~
by one. Therefore,

a Boolean
it

is

fYc+~(A
function,
is sufficient

n s) = o.
of
value

the

to show that

~ f(~)’=ER~&+~(B)2

Bl>k

[1

,4,1Ans[>k

.

1

Rewrite

the left-hand

side as

x
.4. /,4n Sl>k

f(A)2

=

~

~

~(D u B)2.

BcS,lBl>k

DcSC

By Lemma

4,

this equals

~

Q-IS’I

~

&+

R(B)2,

BcS,l

Bl>k

R=(O,

I)ISCI

which

can be rewritten

as

which

completes

the proof.

By averaging

sums as those

appearing

in Lemma

5 over

all subsets S,

the

sum of squares

of high coefficients

can be bounded.

LEMMA 6.

Let

f be a Boolean

function,

t an integer,

and O < p < 1. Then

where S is a subset
independently

chosen
with probability

random such

at
p, and pt ~ 8.

that

each

Latiable

appears

in its

PROOF.

Using

Chernoff

bounds,

the

probability

that

IA n S I > pt/2

is at

least
that

1 – exp( – tp/8)
the

probability

(see [7]).

In our
IA n S I > pt/2

case,

tp > 8;
at
is

therefore,
least

1/2.

we can assume
A

Each

set

of

contributes

flA)2

to at

least half of

the sets S, and the lemma

follows.

At

this point, we have developed

all

the necessary machinery

to prove

the

Main

Lemma.

q
q


<!-- pdf-page: 9 -->
Constant Depth Circuits,

Fourier

Transform,

and Learnability

615

LEMMA 7 (MAIN LEMMA).
of depth d and size M, and let

Let
f be a Boolean
t be any integer. Then

function

computed

by a circuit

PROOF. Fix p =

l\(lOt(~-

1)/~), and s = pt\2

= tl/d\20.

By Lemma

6,

where
probability

S is chosen
p. LJsing

at
Lemma

random
5,

such

that

each

variable

appears

in it with

this is bounded

from above by

1-

L

J

Consider
choosing

now the
S at

distribution

of

the

restriction

S’ + R induced

random such that each variable

appears

in it with

by
probability

first
p,

and then choosing

a random O– 1 assignment

R to the bits in S’. This is exactly

the same distribution

as choosing

a restriction

p at

random with Pr[ * ] = p.

since by our
above quantity

choice

of p and s, p s l/(lOdsd

- l), Lemma

2 applies

and the

is bounded

by

2A42-”

= 2&fp’’’/2o

4. Learning

Constant Depth Circuits

Theoretical

machine

learning

is mainly

concerned

with

learning

concepts,

i.e.,

functions.
Boolean
is fixed and known

The standard
to the learner who is trying

scenario

is the following:
to identify

A class of concepts

a specific member

the class that

is unknown

to him. To this

end,

the learner

observes

pairs

in

of

input/output

of

the concept.

Based

on these observations,

the learner

wishes

to find

some concept
of

Various models

that
learning

is “close”
differ

to the unknown
of
on a number

concept.
issues: First

is the way for

selecting

input/output

pairs

for

the learner

to observe:

They may be specified

by the
from some unknown

learning

algorithm,

randomly

chosen

from the

uniform

distribution,

distribution,

or even by an adversa~.

The other

issue is

when
as their
unknown
observation

are two concepts

probability

considered
to agree on inputs

“close”

to each other.
uniformly
used

drawn
distribution

This may be defined

at

random,

to select

inputs

from some
the
at

distribution,
stage.

or

from the

We consider

a learning

model with

two phases:

learning

and prediction.

In

the learning
with

f ( x). During

phase the algorithm
the prediction

is presented
phase the algorithm

randomly

chosen

inputs
presented

is-only

x, along
random

inputs

x,

and

must

a given
algorithm

distribution
if

D,

output
an

a

Prediction
is

called

f(~)7

an

for
(e, 8, D)

f( x).

For

prediction

algorithm

Pr~[~-disagrees

withfon

more

than

an E fraction

of

the

inputs

1

< S.

q


<!-- pdf-page: 10 -->
616

N. LINIAL ET AL.

We

present

an

(e, 8, U)

algorithm

for

learning

circuits

of

depth

d

and

size M, where

U is the

uniform

distribution.

For

every

fixed

d,

the

algorithm

runs in time

quasi-polynomial

in E, 8, and M.

In the learning

phase

the algorithm

derives

good approximations

to the Fourier

coefficients

of ~, and

in the prediction
value

of ~.

stage these

approximate

coefficients

are used to predict

the

4.1.

LEARNING

PHASE.

The

sample

points

xl,

. . . , Xn,

algorithm
where

observes

~ on m randomly

m = 4(2nk/~)ln(2n~/8)

and

chosen,
k =

(2O log(2m\6))~.

Its approximation

for

the Sth coefficient

of ~ is

For all

ISI < k, and as = O, for all

I,S > k.

40~o p~E~~~~~~N p~SE@ The predicted

value

of ~ on input

x is

f(x)

= sign

~

a~x~(x)

(

lSl<k

.

)

THEOREM

1.

The

abole

algorithm

is an

( .s, 8, U)

learning

algorithm

for

circuits

of depth d and size M, where U is the uniform distribution.

The

proof

of Theorem

1 uses the following

two lemmas:

Lemma

8 shows

with

high probability

all

low-order

coefficients

are approximated

well.

LEMMA

8

Pr

For

some

S,\Sl

<k,

I as –~(S)l

>

[

c]

J
2nk

<s

PROOF.

For

a subset

S, consider

the

random

~ariable

Ys = f(.x)x~(x).

expected
mates
through

value
this expected
a standard

of

Ys
value

by
is,
by averaging

definition,

f(S).

The

over m samples.

The

application

of Chernoff

bounds

(see [7]).

algorithm
lemma

The
esti-
follows

LEAMMA 9.

Let

f be a Boolean

ji.mction,

and g an arbitrary

jimction

such that

X$(f(S)

– j$(S))2 < ~,

then Pr[f(x)

+ sign(g(x))]

< ~.

PROOF.

Since

f

is a Boolean

function,

f(x)

# sign(g(x))

implies

that

If(x)
that
ity
equality,

– g(x)l

>1.

Note

that

Ilf – g112 = ~,,(~(x)

– g(x))’;

thus,

– @x)l
If(x)
Ilf – gll” = X~(f(S)

> ~ does

not

exceed
– ~(S))2 S e.

IIf – gllz.

Finally,

the probabil-
by Parseval’s

Based on the above lemmas, we prove Theorem

1.

PROOF OF THEOREM

k,

then

F(S)

= O. But

1.

f

Consider

the

function

g = Zls ~ ~ ay xs.

If

IS\ >

has

a circuit

of

depth

d and

size M,

and

an

application

of

the Main

Lemma

yields:

x (f(s)

lSl>k

-E(S))2 = ~ f(s)’

< ;.

lSl>k

q
q


<!-- pdf-page: 11 -->
Constant Depth Circuits,

Fourier

Transform,

and Learnability

617

By Lemma

8, with probability

of at

least 1 – 6,

there

holds

(~(S)

– ~(S))2

<

for every set 1S I < k. Whenever

disagrees with

this is the case g satisfies
f on no more

the conditions

than an e fraction

of

l/2nk

of Lemma

9, so

that

sign(g)

the inputs.

5. Further Corollaries

In this

section,

the Main

Lemma

is used to derive

some

new properties

of

functions

in ACO.

5.1. APPROXIMATIONS BY A Low DEGREE POLYNOMIAL.

As mentioned

pre-

viously, Boolean

functions

can be thought

of as taking

real values. So it makes

to

sense
polynomials.

approximate
This

them with

simple

functions

such

complements

the results

[14] and [17], showing

real
of

as low-degree
that

such

approximation

is possible

over

finite

fields.

LEMMA

10.

Let

f G AC O[d],

of degree at most O(log(n/~)~)

then for et’e~ c >0,
such that

IIf – PII c E.

there exists a po~nomial

p

PROOF.

Approximate

f by p = Zlsl ~ ~ f~S)ms, where ms = H, l s X,,

where

the input

bits

xl are taken

to have values

of 1 and – 1 (respectively,

false and

true). The lemma

becomes

a restatement

of

the Main

Lemma.

It

is interesting

to note that

the results

of

[14] and [17]

for polynomials

over

finite

fields

yield more

general,

weighted

approximations.

These weights

correspond
uniform

any probability

to
distribution.

5.2. Low AVERAGE

SENSITIVITY

distribution.

Our

results

apply

only

for

can

the

Definition

1.

Let

f be a Boolean

function,

and w l {O, 1}”. The sensitivity

of

f on w is the number

of hamming

neighbors

w‘ of w such that

f(w)

# f(w ‘).

The

auerage sensitivity

of

f,

s(f),

is the

average

over

all w l {0, 1}’

of

the

sensitivity

of

f on w.

This quantity measures

how on average

the value off

is sensitive

to changes

in the

input.

Equivalently,

average

sensitivity

can be defined

as the sum of

influences
it becomes:

of all variables

on f

(see [9])

in terms

of

the Fourier

transform

of

f

LEMMA 11.

For any Boolean

function

f:

s(f)

= XIW’(S)2.

s

Comment.

tions

discussed

In [9],

this appears
there map to {O, 1}, while

as 4Zsl Sl~(S)z,

because

the Boolean

func-

here the range

is {1, – 1}.

An application

of

the Main

Lemma

implies:

LEMMA

12.

For any fimction

f = ACO[dl,

we lzaL1es(f)

= O((logn)~).

The

bound

given

by

this

lemma

is not

far

from optimal

as the

parity

function
AC”[d].

on (log n) ‘– 1 bits has sensitivity

(log n)~– 1, and can be computed

in

q
q


<!-- pdf-page: 12 -->
618

N. LINIAL ET AL.

This

lemma

gives a general,

simple way to prove

has recently

found

some new applications.

In [16],

lower
it

bounds

for AC”,

is used to obtain

and
lower

bounds

on the number

of negations

required

by ACO circuits.

In [12],

it

is used

to show that universal

hashing

cannot

be done in AC”.

5.3. No

PSEUDORANDOM

FUNCTION

GENERATORS.

A

function

~:

{0. 1}”2 X {0, 1}’2 +
oracle

is called
Turing machine M running

{O, 1}

a pseudorandom
in polynomial

function

generator

time

can distinguish

no

if
between

random oracle

and the oracle

~(s,

as well

as constructions

* ), where
of such generators,

s is chosen

see [6].

at random.

a function

generator

that

outputs

one bit,

in contrast

to a string

For
(Here we
of

a truly
exact definitions
are using
bits.)

LEMMA

13.

There does not exist a pseudorandom

function

generator

in AC().

PROOF. The following
in order

functions,

algorithm exploits the low-average

sensitivity

of ACO

to distinguish

them from a truly

random one. The algorithm

chooses
result
wise,

If ~(x)

by x‘.
it guesses random function.

‘),

then

a random

x. Then,
= jlx

the algorithm

flips
the algorithm

a random bit

in x, denote

guesses ACO fimction;

the
other-

5.4. CORRELATION

WITH

t-WIsE

INDEPENDENT

PROBABILITY

DISTRIBUTIONS.

Consider

probability

t-wise

independent

distributions
if

for

on 2{’”

every

x,,

~‘ ‘II}. Such
. . . x,,

and

a distribution
every

.s,,

{O, 1} there
if
is that

holds K(X,
p is consl

“d

= q,

ered

. . . x,, =
as a real

q,) = 2 ‘f. An easy but useful
then
on the
function

cube,

in

K is called
. . . l,,
observation
it

is t-wise

iff

its Fourier

transform

vanishes

on all S of cardinality

between

1

independent
and t.
Such
generators
that
ically,

distributions
for

,4C0 [2, 13].

play

is polylog-wise
for a real

function

independent

in the

an important
Indeed,

role
is conjectured
is a pseudorandom
f on the cube and a probability

it

design

in [11]
generator

of pseudorandom
that any distribution

for ACO. Specif-
~ on it,

distribution

let J!ZP(f ) (respectively,
is chosen

according

E(f)

= Eu(

to ~ (respectively,

f )) be the expectation
The

uniformly).

of

f when

conjecture

the input
for

is that

~ = ACO[d]
and ~W( f ) does not exceed

and a (log d-l

rz)-wise independent

p the difference

0.1, say. Here we show a result

between
of a similar

13(f)
flavor

that

falls

short,

however,

of proving

the conjecture.

For

the purpose

of

this section

alone, Boolean

functions

map into

{O, 1}.

LEMMA

14.

Let

f be a Boolean

function

computable

by a circuit

of depth d and

size M and let p be a t-wise independent

probability

distribution,

then:

PROOF.

Notice

that

Ep(f)

= 2“(f,

p)

= 2n

z
Sc{l..

tz}

f(s)jMs),

the

where
characters.

equality

last
Since f maps

follows
kto

from the
{O, 1} its expectation

orthonormality

of
equals Eu( f ) = f(@),

the *basis

of
and

q


<!-- pdf-page: 13 -->
Constant Depth Circuits,

Fourier

Tmnsfom,

and Learnability

619

L(@) = 2-”.
Cauchy-Schwartz

AIso,

p

is

t-wise

independent

so

XS)

=

0,

for

1 s 1s1s t. BY

inequality

l%(f)

- Ew(f)l

= 2“

f(s)ji(s)

~ 2“

~
\sl>t

m“

An application

of

the Main

Lemma

completes

the proof.

The

quantity

II vII plays

an important

role

in the

above

bound.

Note

that

IIid = ~m;
tion (the probability

therefore,
that

II P112 is the collision
drawn

two random values

probability
independently

of

the distribu-
according

to

v have the same value).

In order

for our upper

bound

to be nontrivial

(i.e.,

less

than one),

II PII has to be exponentially

small. For example,

if K is polynomially

bounded,
meaningful

that

is,

for any x the probability

bound. Unfortunately,

p(x)
for our bound

< poZy(n)/2n,
to be meaningful,

then we get a

the distri-

bution

w has to be “fairly

close”

to the uniform

distribution.

ACKNOWLEDGMENTS.

We would

like to thank Mauricio

Robert

Sloan,

and Prasoon

Tiwari

for helpful

Karchmer,
discussions. We would

Mike Sipser,
to

like

thank

the anonymous

referees

whose

comments

helped

to both

improve

and

simplify

the presentation.

REFERENCES

~~-formulae

1. AJTAI. M.
on finite
2. AJTAI, M., AND WIGDERSON, A.
in computing
In Adwmces

circuits.
1989, pp. 199-222.

structure. Ann. Pure Appl.
Deterministic
simulation
research, Vol. 5. S. Micali,

24 (1983), 1-48.

Logic
of probabilistic

depth
ed. JAI Press, Greenwich, Ct.,

constant

3. BRANDMAN, Y., HENNESSY, J., AND ORLITSKY, A.
IEEE

size of decision trees and two level circuits.

A spectral
Trans. Corrzput.

4. DYM, H., AND MCKEAN, H. P.

Fourier

Series and Integrals.

Academic

1972.

lower bound technique

for

the

.?9, 2 (1990),

282–287.
Press, Orlando,

Fla..

5. FURST, M., SAKE, J., AND SIPSER, M.

Parity,

circuits,

and the polynomial-time

hierarchy.

Math.

Syst. Theory

17 (1984),

13-27.

6. GOLDREICH, O., GOLDWASSER, S., AND MICALI, S. How to construct

random functions.

J.

ACM 33, 4 (Oct. 1986), 792-807.
HAGERUP, T., AND RUB, C.

A guided tour

to Chernoff

bounds.

Inf

Proc.

Lett.

33 (1989),

7.

8.

9.

10.

11.

12.

13.

305-308.
HASTAD, J. AND BOPPANA, Computational
tion, MIT Press, Cambridge, Mass., 1986.
KAHN, J., KALAI, G., AND LINIAL, N.
of
the 29th Annual
Proceedings
N. Y., Oct.).
IEEE, New York,
KEARNS, M., AND VALIANT, L.
finite
In Proceedings
(Seattle, Wash., May). ACM, New York,
LINIAL, N., AND NISAN, N.

Approximate

automata.

of

Symposiam
1988, pp. 68-80.
Cryptographic

of Compating.

on Theoiy

ACM Symposium
1990, pp. 260-270.

Annual
York,
MANSOUR, Y., NISAN, N., AND TIWAR1, P.
hashing.
22nd Annual
(Baltimore, Md., May 12-14). ACM, New York,
NISAN, N., AND WIGDERSON, A.
Symposium
1988, pp. 2–12.

In Proceedings

cm Foundations

of Computer

Hardness

Science

the

of

limitations

for small depth circuits. Ph.D. disserta-

The influence

of variables

on Foundations

of Compater

on Boolean
Science

functions.

In
(White Plains,

limitations

on learning Boolean

formulae

and

the 21st Annual

ACM Symposium

on Theoiy

of Computing

1989, pp. 433-444.

inclusion-exclusion.

In Proceedings
the 22nd
(Baltimore, Md., May 12–14). ACM, New

of

The
ACM

computational
Symposium

complexity
Theory

on

of universal

of Computing.

1990, pp. 235-243.

vs. randomness.

In Proceedings

(White Plains, N. Y., Oct.)

of
the 29th Annual
IEEE, New York,

q


<!-- pdf-page: 14 -->
620

N. LINIAL

ET AL.

14. RAZBOROV, A. A.

Lower
AND, XOR. Math. Zarnetsk
Notes

./1 (1987), 333–338.

Learning

15. RIVEST, R.L.
16. SANTHA, M., AND WILSON, C.
of

Proceedings
New York, 1991, pp. 228-237.

the 8th Annual

bounds

for
41 (1987), 598-607

the size of circuits

of bounded

depth with

(in Russian). English

translation

basis
in Math

decision lists. Machine Leammg2 ,3(1987),229-246.

Polynomial
Svmposium

size circuits with a hmited number of negations.
on Aspects

of Theoretical

Computer

Science.

In
IEEE,

17. SMOLENSKY, R.

Algebraic

in the theory

of

lower

methods
the 19tll Annaal

In Proceedings

complexity.
York City, N. Y., May 25–27). ACM, New York,
A theory of
Theory and applications

18. VALIANT, L. G.
19. YAO. A. C.

the learnable.

of

of

Symposium
20. Y.40, A. C.

on Fowzdatzons
Separating

of Computer
the polynomial-time

Armua[
York,

Sympo,num

on Foundations

of Computer

1985, pp. 1-10.

ACM Symposwm

1987, pp. 77–82.

bounds
on Theoty

for Boolean
of Computmg

circuit
(New

Comrnun

ACM 27, 11 (Nov. 1984), 1134-1142.

trapdoor
Science.

In Proceedings

functions.
IEEE, New York,
by oracles.

of
1982, pp. 80-91.
In Proceedings
Sccence (Portland. Ore. Oct.).

hierarchy

of

the 26th
IEEE, New

the 23rd Annual

RECEIVED DECEMBER 1989: REVISED NOVEMBER 1991: ACCEPTED NOVEMBER 1991

Iournd

of

the Aswctatmn

for Cmnputmg

M~chmay,

Vol

40, No 3, .luly 1993


