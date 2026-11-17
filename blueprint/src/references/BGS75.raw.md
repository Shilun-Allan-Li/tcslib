<!-- generated-by: proofmatch local extraction -->
<!-- source-pdf-sha256: 2459e3840724ade8c7d3b9901042b49f88ed9c514b17e78cc7ee7fb8051b6e9f -->
<!-- extractor: pdfminer.six v20260107 -->

<!-- pdf-page: 1 -->
SIAM J. COMPUT.
Vol. 4, No. 4, December 1975

RELATIVIZATIONS OF THE

=? 4/ QUESTION*

THEODORE BAKERf, JOHN GILL:I: AND ROBERT SOLOVAY

Abstract. We investigate relativized versions of the open question of whether every language
accepted nondeterministically in polynomial time can be recognized deterministically in polynomial
time. For any set X, let x (resp. Ax) be the class of languages accepted in polynomial time by
deterministic (resp. nondeterministic) query machines with oracle X. We construct a recursive set A
such that a Wa. On the other hand, we construct a recursive set B such that B 4: VB.
Oracles X are constructed to realize all consistent set inclusion relations between the relativized
classes ,x, 4x, and co Xx, the family of complements of languages in Xx. Several related open
problems are described.

Key words,

computational complexity,

nondeterministic computation, query machines,

polynomial-bounded computation

question is whether r properly contains. Here

1. Introduction. An important problem in the theory of computation is to
characterize the power of nondeterministic computation. A fundamental open
is the class of languages
recognized in polynomial time by deterministic Turing machines, and 4r5 is
the class of languages accepted in polynomial time by nondeterministic Turing
machines. One reason for the importance of the
? ff question is that 5
and 4 are very natural classes of languages, invariant under reasonable changes
or 4r is the same class whether defined by computations
of machine model.
by one-tape Turing machines, multitape Turing machines, or random-access
? 4/’ question thus deals with the basic nature of computa-
machines. The
tion and not merely with minor aspects of our models of computers.

We can formulate a question similar to- ? 4 for other models of

? 4/’5 question
mathematical computers. In particular, we can relativize the
to the case of machines which compute with the aid of an oracle. When the oracle
answers membership questions about sets of binary strings, the resulting machine
class is formally quite similar to the class of Turing machines without oracle.
.9 4r question has an
The main result of this paper is that the relativized
affirmative answer for some oracles but a negative answer for other oracles.

We feel that this is further evidence of the difficulty of the

9. 4 question.
By slightly altering the machine model, we can obtain differing answers to the
relativized question. This suggests that resolving the original question requires
careful analysis of the computational power of machines. It seems unlikely that
ordinary diagonalization methods are adequate for producing an example of a
language in V but not in ; such diagonalizations, we. would expect, would
apply equally well to the relativized classes, implying a negative answer to all
questions, a contradiction. On the other hand, we do not
relativized

?

Received by the editors July 16, 1973, and in final revised form October 21, 1974. This work was
supported by JSEP Contract N-00014-67-A-0112-0044 and NSF Grant GK-43121 at Stanford Univer-
sity, and NSF Grant GP-38753X at the University of California, Berkeley.

" Department of Mathematics, Florida State University, Tallahassee, Florida 32306.

:t: Department of Electrical Engineering, Stanford University, Stanford, California 94305.
Department of Mathematics, University of California, Berkeley, California 94720.

431

y
c
a
v
i
r
p
-
s
m
r
e
t
/
g
r
o
.
m
a
i
s
.
s
b
u
p
e
/
/
:
s
p
t
t
h

e
e
s

;
t
h
g
i
r
y
p
o
c

r
o

e
s
n
e
c
i
l

M
A
I
S
o
t

t
c
e
j
b
u
s

n
o
i
t
u
b
i
r
t
s
i
d
e
R

.

2
5
.
4
1
2
.
2
5
1
.
6
3
1

o
t

6
2
/
5
0
/
1
1

d
e
d
a
o
l
n
w
o
D

 
 
 
 
 
 
 
 
 
 
 
 
 


<!-- pdf-page: 2 -->
432

THEODORE BAKER, JOHN GILL AND ROBERT SOLOVAY

feel that one can give a general method for simulating nondeterministic machines
by deterministic machines in polynomial time, since such a method should apply
as well to relativized machines and therefore imply affirmative answers to all
? X questions, also a contradiction. Our results suggest that
relativized
the study of natural, specific decision problems offers a greater chance of success
in showing

- V than constructions of a more general nature.

Our model for computation with the aid of an oracle is the query machine,
which is an extension of the multitape Turing machine as described in Hopcroft
and Ullman [2]. A multitape Turing machine consists of a finite-state control unit,
a read-only input tape, a finite number of worktapes, and optionally a write-only
output tape. A query machine, described by Cook [1 ], is a multitape Turing machine
with a distinguished worktape, called the query tape, and three distinguished states,
called the query state, the yes state, and the no state.

The action of a query machine is similar to that of a Turing machine with the
following extension. When a query machine enters its query state, the next opera-
tion of the machine is determined by an oracle. An oracle for a set X will place
the query machine into its yes state if the binary string written on the query tape
is an element of X; otherwise the oracle places the machine into the no state.
Since there is no chance for confusion, we will identify an oracle for a set X with
the set X itself.

A query machine is deterministic if its finite control specifies at most one
possible operation for each configuration of the machine; otherwise the machine
is. nondeterministic. Certain states of a query machine’s finite control are designated
a.s accepting states. A language is recognized by a deterministic query machine
with oracle X if the machine halts on all inputs and halts in an accepting state
just when the input string belongs to the language. The language accepted by a
nondeterministic query machine with oracle X is the set of input strings for which
some possible computation of the machine halts in an accepting state.

A query machine is polynomial-bounded if there is a polynomial p(n) such that
every computation of the machine on every input of length n halts within p(n)
steps, whatever oracle X is used. For any oracle X, we denote by x the class
of languages recognized by polynomial-bounded deterministic query machines
with oracle X, and we denote by x the class of languages accepted by poly-
nomial-bounded nondeterministic query machines with oracle X. The class of
languages whose complements are in /5x is denoted by co V’x.

Every query machine can be converted to a polynomial-bounded machine
by attaching a clock which terminates every computation of the machine that
exceeds some predetermined polynomial time bound. We can thereby produce a
list of polynomial-bounded query machines which perform all possible polynomial-
bounded computations. We will denote by Pi the ith deterministic polynomial-
bounded machine in this list and by NPi the ith nondeterministic polynomial-
bounded query machine. Without loss of generality, we can assume that pi(n) is
a strict upper bound on the length of any computation by P or NP with oracle X
+ hi. We indicate by use of a superscript
on an input of length n, where p(n)
when an oracle has been specified for a query machine; thus NP and p/X denote
query machines using oracle X.
We encode each finite sequence of binary strings x l, x2,’", x,, into the

y
c
a
v
i
r
p
-
s
m
r
e
t
/
g
r
o
.
m
a
i
s
.
s
b
u
p
e
/
/
:
s
p
t
t
h

e
e
s

;
t
h
g
i
r
y
p
o
c

r
o

e
s
n
e
c
i
l

M
A
I
S
o
t

t
c
e
j
b
u
s

n
o
i
t
u
b
i
r
t
s
i
d
e
R

.

2
5
.
4
1
2
.
2
5
1
.
6
3
1

o
t

6
2
/
5
0
/
1
1

d
e
d
a
o
l
n
w
o
D

 
 
 
 
 
 
 
 
 
 
 
 
 


<!-- pdf-page: 3 -->
RELATIVIZATIONS OF THE

=.9

QUESTION

433

Xm)l for every/=< m.

Xm) that is obtained from the string xa * x 2 *

binary string (Xl, X2,
* X
(over the alphabet {0, 1, *}) by replacing each occurrence of 0, 1, and * by 00, 01,
and 11, respectively. Both the encoding and decoding can be performed in time
/ IXml. Note that
bounded above by a linear function of Ixxl / Ix21 /
Ixil <-_ I(xa, X2,
Consider the canonical enumeration of binary strings" A, 0, 1, 00, 01, 10,
11,000, .... When convenient, we will identify the natural number with the ith
string in this enumeration. As usual, if x is a binary string, then x" denotes x con-
catenated with itself n times.
2 we shall construct an oracle A such that a /-A. By contrast, in
many other relations between the relativized, 4/N, and co f classes can be
3 we shall construct an oracle B such that n 4: n. We shall also show that

shown to hold for certain oracles. In
with the relativization of the Meyer-Stockmeyer N-hierarchy [6].

4, we describe open problems concerned

In

Some of the results of this paper have been discovered independently by
M. J. Fischer, R. Ladner, A. R. Meyer, and H. B. Hunt III. We have acknowledged
these independent contributions in the body of the paper.

2.

= A/’, relativized. In this section we construct a recursive oracle A
such that A ,A. We also prove that if A is any polynomial-space complete
language, then A 4A. We conclude the section by showing that whenever
A= A, there is a deterministic procedure using oracle A which finds an
accepting computation of NP.A, on input x, provided NP.A, accepts x" the running
time ofthis procedure is bounded above by a polynomial ofthe maximum computa-
tion time of NP on input x.
Our first observation is that for every oracle X, the class x contains

polynomial-complete sets.

DEFINITION. Let 5 be a class of languages. A set K in 5 is Cook-polynomial-
complete (or simply Cook-complete) in 5e if every language in 5 can be recognized
by a polynomial-bounded deterministic query machine using oracle K. A set K
in 5 is Karp-polynomial-complete (or Karp-complete) if for every set S in 5
there is a functionf(x) computable in polynomial time such that x S ,,f(x) K.
Every Karp-complete set is Cook-complete. Ladner, Lynch, and Selmon [4]
compare the polynomial-bounded reducibilities of Cook and Karp. Note that if

K is Cook-complete in 5e, then 5e_ #/.
#ttx)_ x, and dV#x_ #/tx)because K(X) is Cook-complete in ,x. There-
fore x_ x Q.E.D.

LEMMA 1. For any oracle X, define the language K(X) to be {(i, x, 0")" some
computation ofNP: accepts x in fewer than n steps}. Then K(X) is Karp-complete
in dl/x. In particular, x dVx ifand only ilK(X) #x.
Proof Clearly K(X) Vx. Now suppose S Vx, say S is accepted by
NP. If we let f(x)= (i, x, 0P’tlxl)), then f(x) is computable in polynomial time.
NP.x, accepts x ,, NP accepts x in < P(lxl) steps ,, (i, x, 0p’tlxl))
Now x S
K(X). Since S was arbitrary, we conclude that K(X) is Karp-complete in Ux.
Clearly, ifVx x, then K(X) x. Conversely, suppose K(X) x. Then

Remark. If/(X) is defined by {(i,x)’NP accepts x}, then/(x) does not
belong to x, since there is no uniform polynomial bound on running time of

y
c
a
v
i
r
p
-
s
m
r
e
t
/
g
r
o
.
m
a
i
s
.
s
b
u
p
e
/
/
:
s
p
t
t
h

e
e
s

;
t
h
g
i
r
y
p
o
c

r
o

e
s
n
e
c
i
l

M
A
I
S
o
t

t
c
e
j
b
u
s

n
o
i
t
u
b
i
r
t
s
i
d
e
R

.

2
5
.
4
1
2
.
2
5
1
.
6
3
1

o
t

6
2
/
5
0
/
1
1

d
e
d
a
o
l
n
w
o
D

 
 
 
 
 
 
 
 
 
 
 
 
 


<!-- pdf-page: 4 -->
434
THEODORE BAKER, JOHN GILL AND ROBERT SOLOVAY
machines NPi. Thus, although every language in x can be reduced to/(X)
in polynomial time,/(X) is not polynomial-complete.

The following result was also discovered, independently, by Albert Meyer

with Michael Fischer and by H. B. Hunt III.

THEOREM 1. There is an oracle A such that A
Proof We construct an oracle A such that A

{(i, x, 0")"NP.A,
accepts x in < n steps}. This is a valid inductive definition of a set. In a computation
of length < n, no string of length >_ n can be queried. To simulate NPA on input x
for < n steps, we need know only which elements of length < n __< 1(i, x, 0")l
belong to A. Therefore A is well-defined, and by definition A
K(A). Since
A )A, we conclude a ,/]/,,A by Lemma 1.
K(A)

K(A). Let A

Q.E.D.

Remarks. Kleene’s recursion theorem can also be used to produce a recursive
can be

K(A). The oracle A constructed in Theorem

oracle A such that A
recognized deterministically in exponential time.

We shall next show that there are naturally occurring languages A such that

A__

A language is said to be recognizable in polynomial space ifthere is a polynomial
p(n) and a deterministic Turing machine which recognizes the language and uses
no more than p(n) worktape squares on any input of length n. We denote by
the family of languages recognizable in polynomial space. We could define
to be the family of languages accepted in polynomial space by nondeterministic
Turing machines. But this definition is unnecessary because Savitch [9] has shown
that V’#5e
Se; every language accepted nondeterministically in space p(n)
can be recognized deterministically in space p(n)2.

,a.

A language S is log-space reducible to A if there is a functionf(x) computable
S ,co,f(x) A. The language A is polynomial-space
in space log (Ixl) such that x
complete if every language in #Se is log-space reducible to A. Since every function
computable in log space is computable in polynomial time, every polynomial-
space complete language is Karp-complete in Se. If A is polynomial-space
complete, then ’5

One example of a polynomial-space complete language is 1EQ, the set of
valid sentences in the first-order theory of equality. Other natural examples of
word problems which represent polynomial-space complete languages are given
by Stockmeyer and Meyer 10]. An artificial example of a polynomial-space
complete language is A
{(i, x, 0")" deterministic Turing machine Pi recognizes
x in space < n}.

Proof Suppose A is polynomial-space complete. Then A 5 and 5_ A.
Also 4/A_ V’Se, since every query made of the oracle for A can be answered
Therefore dt/A___ 4/’6 #6_ A.

THEOREM 2. If A is polynomial-space complete, then A [/’A.

in polynomial space without recourse to the oracle for A. But r6e ’6.

When A= tA, then every language S in y#A can be recognized in
polynomial time by some deterministic query machine with oracle A. In fact,
this deterministic machine P] can be constructed so that it "simulates" a non-
deterministic machine NP that accepts S; whenever NP on input x reaches a
nondeterministic branch point in its computation, the simulating machine P
correctly decides which branch to follow.

Q.E.D.

y
c
a
v
i
r
p
-
s
m
r
e
t
/
g
r
o
.
m
a
i
s
.
s
b
u
p
e
/
/
:
s
p
t
t
h

e
e
s

;
t
h
g
i
r
y
p
o
c

r
o

e
s
n
e
c
i
l

M
A
I
S
o
t

t
c
e
j
b
u
s

n
o
i
t
u
b
i
r
t
s
i
d
e
R

.

2
5
.
4
1
2
.
2
5
1
.
6
3
1

o
t

6
2
/
5
0
/
1
1

d
e
d
a
o
l
n
w
o
D

 
 
 
 
 
 
 
 
 
 
 
 
 


<!-- pdf-page: 5 -->
RELATIVIZATIONS OF THE

.9 /’ QUESTION

435

kA

LEMMA 2. Suppose A is an oracle such that

#/’A. Then for each non-
deterministic query machine NPi there is a deterministic query machine Pj such
that P’] on input x produces as output an accepting computation ofNP on input x,
whenever NP accepts x.
Proof A computation of a query machine NP is a sequence of instantaneous
descriptions of the machine. An instantaneous description is an encoding of the
total configuration of the machine, including the state of the finite control, contents
..., I,, of instantaneous
ofthe tapes, and locations oftape heads. A sequence I o, 11
descriptions of NP represents a computation ofNP if Ik encodes a configuration
of NP which can be reached in a single step from the configuration encoded by

We define COMP (X) to be the set of accepting computations of query

machines with oracle X. Specifically, COMP (X)
Io,I,... I is an accepting computation of NP on input x}. Note that
COMP (X)e x, and m < pi(]x[).

Let INIT (X) be the set of partial computations which are the initial parts

of accepting computations by machines with oracle X; that is,

INIT (X)

(i, x, 0’(11), Io, I, ..., I,) there exist I,_ , ..., I such that
p,(lx[) and (i, x, 0ei(), Io, I, ..., I) e COMP (X)}.

m

Then INIT (X)e Wx.
If A= A, then INIT(A) can be recognized by some deterministic
polynomial-bounded query machine with oracle A. Now suppose NP accepts
x. Then (i, x, OP(Ixl),[o) INIT (A), where I o is the instantaneous description of
the initial configuration of NP with input x. We can find an accepting computa-
tion of NP on x as follows’
We wish to determine a computation Io, I a,"", I such that m < p(lx])
and (i, x, 0p’(II), Io, I, ..., I,) e INIT (A) for each k _N m. To find I, suppose
we have already found Io, I,

INIT (A).

Determine in polynomial time an instantaneous description I, such that
(i, X, 0pi(lx]), I0,
Ik_ 1, Ik) INIT (A). (There are only finitely many possibilities
for I, since I, must be the instantaneous description of a configuration of NP
reachable in one step from the configuration described by I_.) Since NP
accepts x, we have (i, x, 0p’lxl), Io, I, "’", I)e COMP (A) for some m < p,(]x]).
Therefore we will find an accepting computation of NP on input x in a number
of steps at most a polynomial of p(lx]).
We shall use the method of the proof of Lemma 2 in the proof of

Q.E.D.

Theorem 6.

3.

# dV, relativized. In this section we show that there exist recursive
oracles X such that #xg Vx. (G denotes proper containment.) We shall
construct recursive sets B, C, D, E, and F such that

(i) B _: /B;
(ii) ,Ac is not closed under complementation;

y
c
a
v
i
r
p
-
s
m
r
e
t
/
g
r
o
.
m
a
i
s
.
s
b
u
p
e
/
/
:
s
p
t
t
h

e
e
s

;
t
h
g
i
r
y
p
o
c

r
o

e
s
n
e
c
i
l

M
A
I
S
o
t

t
c
e
j
b
u
s

n
o
i
t
u
b
i
r
t
s
i
d
e
R

.

2
5
.
4
1
2
.
2
5
1
.
6
3
1

o
t

6
2
/
5
0
/
1
1

d
e
d
a
o
l
n
w
o
D

 
 
 
 
 
 
 
 
 
 
 
 
 


<!-- pdf-page: 6 -->
436

THEODORE BAKER, JOHN GILL AND ROBERT SOLOVAY
(iii) o # o but o is closed under complementation"
(iv) e # .A;e and E Ve fq co
(v) F g yF f’)CO yF and /F # CO
(Recall that co x is the class of languages whose complements belong to
.A;x.) By suitable choices of oracles, all consistent set inclusion relations among

the relativized classes, V, and co

{x" there is y X such that
For any oracle X, define the language L(X)
Ixl}. Clearly L(X) Vx. In fact, L(X) can be accepted in linear time by a
lYl
query machine that writes on its query tape a nondeterministically chosen string y
of the same length as input x, then accepts x if and only if y belongs to X.

can be realized.

The following result was obtained independently by Richard Ladner.
Although the next theorem follows immediately from Theorems 4-7, we include
a direct proof in order to illustrate the basic techniques of this section.

0.

THEOREM 3. There is an oracle B such that
Proof. We construct a set B such that L(B) does not belong to n. The
construction of B proceeds in stages. We denote by B(i) the finite set of strings
placed into B prior to stage i. Recall that pi(n) is an upper bound on the lengths
of computations by P and NP for all oracles X and all inputs of length n.
Let no
Stage i. Choose n > ni so large that pi(n) < 2n. Run query machine Pi with
On. If P( accepts On, then place no strings into B at this
oracle B(i) on input xi
stage. Otherwise, if p/n( rejects 0n, then add to B the least string (that is, the earliest
occurring string in the canonical enumeration of binary strings) of length n not
queried during the computation of P( on input On. (Such a string exists because
not every string of length n can be queried by p{i on 0n;in p(n) steps, p/m can
ask at most pi(n) questions, and we have chosen n so that pi(n) < 2
the number
2n. (This will ensure that no string of
of strings of length n.) Finally, let ni+
length =< 2 is added to B at a later stage.) Go to the next stage.
The computation of P on input xi is the same whether B or B(i) is used as
oracle, because no string queried by P{ on input x is later added to or deleted
from B. At stage i, we ensure that Pf does not recognize L(B); by construction,
pi and hence Pf rejects xi iff some string of length Ix[ belongs to B, that is, iff
xi

L(B). Therefore L(B) does not belong to n.
The set B constructed in the proof of Theorem 3 is sparse; for every n, there
is at most one string x in B such that n __< Ixl < 2n. An obvious modification of the
proof ofTheorem 3 yields the following result" there are arbitrarily sparse recursive
sets such that 5n -=

Richard Ladner has shown that there are oracles B recognizable deter-

The proof of Theorem 3 makes use of the fact that we can query an oracle
about any number of length n in approximately n steps. We can therefore conclude

that L(B)e VN. Alternate models for query machines involve the notion of

oracle tapes. In one model, a query machine is supplied with a tape on which
are written the strings in the oracle set, separated by asterisks and listed in increas-
ing order. A variation of this model is obtained by supplying the query machine
with an oracle tape on which is written the characteristic function of the oracle
set. With these models of query machines, our proofs of Theorems 1-3 are no

# V.

ministically in exponential time such that

Q.E.D.

y
c
a
v
i
r
p
-
s
m
r
e
t
/
g
r
o
.
m
a
i
s
.
s
b
u
p
e
/
/
:
s
p
t
t
h

e
e
s

;
t
h
g
i
r
y
p
o
c

r
o

e
s
n
e
c
i
l

M
A
I
S
o
t

t
c
e
j
b
u
s

n
o
i
t
u
b
i
r
t
s
i
d
e
R

.

2
5
.
4
1
2
.
2
5
1
.
6
3
1

o
t

6
2
/
5
0
/
1
1

d
e
d
a
o
l
n
w
o
D

 
 
 
 
 
 
 
 
 
 
 
 
 


<!-- pdf-page: 7 -->
RELATIVIZATIONS OF THE i =.9 1/’ QUESTION

437

,/V, then x y,x for every oracle X.

longer valid. Paul Morris [7] has pointed out that with the oracle-tape models
for query machines, if
From Theorems and 3 we see that the answer to the question x ? x
depends on the oracle X. Kurt Mehlhorn [-5-] has shown that the family of oracles X
for which x yx is a "meagre" set in a space of recursive oracles. In this
sense, "most" oracles satisfy x x.

simpler.

The next result follows from Theorem 6, but again the direct proof is much
THEOREM 4. There is an oracle C such that c is not closed under comple-

mentation.

0.

Proof By a construction very similar to that of Theorem 3, we generate an
oracle C such that ,c does not contain E(c), the complement of L(C). Let C(i)
be the set of string placed into C before stage i, and let no

Stage i. Choose n > n so that p(n) < 2". (Thus n is greater than the length
of every string queried earlier in this construction.) Run nondeterministic query
0". If NP) accepts 0", then choose
machine NPi with oracle C(i) on input xi
any accepting computation and place into C some string of length n not queried
during this computation. Otherwise, place no string into C at this stage. Let
n+l
By construction, NPc accepts x iff some string of length Ixil belongs to C,
that is, iff x L(C). Consequently NP does not accept E(C). Therefore E(C)
does not belong to c. Q.E.D.

2", and go to next stage.

pendently, to Richard Ladner.

The next result is due to Albert Meyer with Michael Fischer and, inde-
THEOREM 5. There is an oracle D such that o :/: ro but dt/ is closed

under complementation.

Proof. It is easily seen that dl/’x is closed under complementation if and
only if (X) /x, where (X) is the complement of the Karp-complete
language K(X). We shall construct an oracle D such that (i) L(D) dV o
and (ii) u o iff u is a prefix of some string v in D such that Ivl
2lul. Then
o : o from (i); and K’(D) V from (ii) and so U is closed under
complementation.

At stage n in the construction, we decide the membership in D of all strings
of length n. In the course of the construction, some strings will be reserved for D,
that is, designated as nonmembers of D. An index
will be cancelled at some
stage when we ensure that pO does not recognize L(D). As usual, D(n) denotes
those strings placed into D prior to stage n.

Stage n

Stage n

2m. For every string z of length n

2m not reserved for D at an
earlier stage, determine the prefix u of z of length m. If u encodes a triple (i, x, 0),
then place z into D iff NP.,") does not accept x in fewer than steps.

>_ n has been reserved for , or if p(n) >_ 2m, then add no elements to D at this

2m + 1. Let be the least uncancelled index. If any string of length

stage. Otherwise, run Pi with oracle D(n) on input 0" and reserve for D all strings
of length >=n queried during this computation. If pgt,) accepts 0", then add no
elements to D. But if pot,) rejects 0", then add to D the least string of length n
not queried (and so not reserved for ). Finally cancel index i.
Every index is eventually cancelled, and when index

is cancelled at some

y
c
a
v
i
r
p
-
s
m
r
e
t
/
g
r
o
.
m
a
i
s
.
s
b
u
p
e
/
/
:
s
p
t
t
h

e
e
s

;
t
h
g
i
r
y
p
o
c

r
o

e
s
n
e
c
i
l

M
A
I
S
o
t

t
c
e
j
b
u
s

n
o
i
t
u
b
i
r
t
s
i
d
e
R

.

2
5
.
4
1
2
.
2
5
1
.
6
3
1

o
t

6
2
/
5
0
/
1
1

d
e
d
a
o
l
n
w
o
D

 
 
 
 
 
 
 
 
 
 
 
 
 


<!-- pdf-page: 8 -->
438

THEODORE BAKER, JOHN GILL AND ROBERT SOLOVAY

V’ and- 4

stage, we have guaranteed that P does not recognize L(D). Therefore L(D)
lo o.
At any odd stage 2m + 1, at most p(n) < 2" strings are reserved for D, and
so fewer than 2o + 2 +
strings of length 2m can be reserved
< 2
for D at odd stages before stage 2m. Therefore every string u of length rn is the
prefix of at least one string v of length 2m which is never reserved for D. By
construction, ueK’(D) iff u prefixes a number reD of length 21ul, and so
K(D) e f-o. Q.E.D.

+ 2

The next theorem gives an answer to a question posed by Albert Meyer.
THEORE 6. There is an oracle E such that

f-I co dV.

Proof The construction of E is considerably more complicated than that of
the preceding oracles. As usual, we guarantee that L(E) is not in E and so e
va Ve. But we must also ensure that whenever both S and its complement $
belong to g’e, then S in fact is in ’e.

Define e(n) inductively by e(0)

The rough idea of the proof is the following. By adding infinitely many new
elements to an oracle A such that A A, we obtain an oracle E such that
e :/: E. Now if we could quickly recognize the set E
A, then e g’e.
A, we can arrange the
Although we cannot quickly recognize the entire set E
construction so that whenever both S and its complement
are accepted in
polynomial time by nondeterministic query machines with oracle E, then we can
A, so that we can then combine
quickly recognize relevant portions of the set E
the machines accepting S and S into a deterministic machine to recognize S.
22"). Choose any oracle A
such that a= Va. Without any loss of generality, we can assume that A
contains no elements of length e(n) for any n > 0. The oracle E is obtained by
adding to A at stage n at most one string of length e(n). Let E(0)
A and let E(n)
denote the set of numbers placed into E before stage n. There are two types of
requirements to be satisfied in the construction of E. An unsatisfied requirement
(i, i) is vulnerable at stage n if pi(e(n)) < 2e("). An unsatisfied requirement (j, k)
1) < log2 (Ixl)
with j -Ta k is vulnerable at stage n if there is a string x such that e(n
<= e(n) <= max {pj(lxl), pk([xl)} < e(n + 1)and neither NPjnor NP with oracle E(n)
accepts x. We agree that requirement r has higher priority than requirement r2
just when r < r2.

0 and e(n + 1)

Stage n. We satisfy the requirement of highest priority that is vulnerable at
stage n. To satisfy requirement (j, k) with j 4: k, we simply add no string to E at
this stage. To satisfy requirement (i, i), we run Pi with oracle E(n) on input 0e(").
If P") rejects 0e"), then we add to E the least string of length e(n) not queried by
P") on input 0e") otherwise we add no new element to E.

not recognize L(E). Therefore L(E) g .

Every requirement (i, i) is eventually satisfied, since there are only finitely
many requirements of higher priority. Suppose requirement (i, i) is satisfied at
stage n. Then P rejects 0e(") iff there is a string in E of length e(n), and so Pf does
Now suppose S and $ belong to 4/E. We must show that S e ,e. Assume
NP accepts S and NPf accepts $. Note that requirement (j, k) is never satisfied,
else there would be a string x accepted by neither NPf nor NP. Let m be so
large that

y
c
a
v
i
r
p
-
s
m
r
e
t
/
g
r
o
.
m
a
i
s
.
s
b
u
p
e
/
/
:
s
p
t
t
h

e
e
s

;
t
h
g
i
r
y
p
o
c

r
o

e
s
n
e
c
i
l

M
A
I
S
o
t

t
c
e
j
b
u
s

n
o
i
t
u
b
i
r
t
s
i
d
e
R

.

2
5
.
4
1
2
.
2
5
1
.
6
3
1

o
t

6
2
/
5
0
/
1
1

d
e
d
a
o
l
n
w
o
D

 
 
 
 
 
 
 
 
 
 
 
 
 


<!-- pdf-page: 9 -->
RELATIVIZATIONS OF THE i __? dl/’ QUESTION

439

(i) for every x such that [xl > e(m) there is at most one n such that log2

(ii) if a requirement of higher priority than requirement (,j, k) is ever satisfied,

<= e(n) <__ max {pj([xl),
then it is satisfied before stage m.

We can decide S deterministically in polynomial time using oracle E by the

following procedure"

1). Only O(Ix]) strings need be queried here, since e(n

With input x, if Ix] < e(m), then use a finite table to decide if x e S. Otherwise
Ixl > e(m). Calculate the least n such that e(n) > log2 Ix[. Determine which elements
were added to E before stage n by querying the oracle E about all strings of lengths
e(0), e(1), ..., e(n
1)
-<_ log2 Ixl.
Now there are two cases. If e(n) > max {pj(Ixl), Pk(lXl)}, then no computation
of either NP or NP can query oracle E about any string of length >= e(n). There-
fore the computation ofNPion input x is the same with oracle E(n)as with oracle E.
Since we have already calculated E(n)- A, we can produce a query machine
NW")-i(,) which simulates NP(") but makes no queries about strings of length e(m)
for any m < n; these queries are answered without recourse to the oracle E(n) by
A. Clearly NPi(,) on input x gives the
using the finite table of elements of E(n)
same result with oracle A as with oracle E(n). Therefore NP accepts x if and only
if N/,,) accepts x, that is, iff (i(n), x, 0p(I’I))
K(A). (We can easily make sure
that NPi(.) has the same running time bound as NPi, and that the length of the
index i(n) is at most a polynomial of Ixl.) Since K(A) belongs to A, we can now
determine in polynomial time if NP accepts x.
In the other case, e(n) <__ max {p(Ixl), Pk(IX[)}. If neither NP nor NPk with
oracle E(n) accepted x, then requirement (j, k> would be satisfied at stage n.
But requirement (j, k) can never be satisfied, for then both NP and NP would
reject x. Therefore at least one of NP(") and lVrk
accepts x. As in the first case,
since we know E(n)- A, we can discover in polynomial time which machine
accepts x.
ITDE(n) accepts x, the argu-
ment is similar.) We must now determine if NP accepts x, where E might contain
a string of length e(n) not in E(n).
,/]/"lia and since we have already calculated E(n)
A, we can
use the method of Lemma 2 to find an accepting computation ofNP’) on input x.
Now we examine this computation to see if it represents a valid computation
when oracle E is used instead of E(n). Whenever a string y of length e(n) is queried
on x, we consult oracle E about y. There are two subcases.
by _._;
If no such y belongs to E, then the computation ofNP(’ on x is the same as
the computation of NP on x. Now NP(") accepts x, and so NP also accepts x.
We conclude that x 6 S.
on input x queries some string y of length e(n)
which belongs to E. By construction, there is at most one number in E of length
e(n). Thus we have correctly calculated E(n + 1)
A,
so we now know E(n + 1)
A. Using the method of the first case above, we can
finally determine which of machines NPj and NPk with oracle E(n + 1) accepts x.
Since e(n + 1)> max {pj(lxl),pk(lXl)}, no number of length >__e(n + 1) can be
queried by NPf or NPf on x, so NPf accepts x iff NPf’’+ 1, accepts x.
Q.E.D.

Suppose, to be definite, NPf") accepts x. (In case ,,k

In the other subcase, .._j

E(n). Earlier we found E(n)

Since iA

NpE(n)

NpE(n)

y
c
a
v
i
r
p
-
s
m
r
e
t
/
g
r
o
.
m
a
i
s
.
s
b
u
p
e
/
/
:
s
p
t
t
h

e
e
s

;
t
h
g
i
r
y
p
o
c

r
o

e
s
n
e
c
i
l

M
A
I
S
o
t

t
c
e
j
b
u
s

n
o
i
t
u
b
i
r
t
s
i
d
e
R

.

2
5
.
4
1
2
.
2
5
1
.
6
3
1

o
t

6
2
/
5
0
/
1
1

d
e
d
a
o
l
n
w
o
D

 
 
 
 
 
 
 
 
 
 
 
 
 


<!-- pdf-page: 10 -->
440

and

classes

THEODORE BAKER, JOHN GILL AND ROBERT SOLOVAY

Proof. We outline the construction. Let LI(F)

The next result accounts for the only remaining relation between relativized

THEOREM 7. There is an oracle F such that F_ ffF CI CO t/’F
In this section we have constructed oracles X such that Nx_ ,-x. The

y e F with lyl- Ixl}, and let L2(F)
with 10yl- Ixl}. Modify the construction of Theorem 4 so that
-co ff5F and L2(F) e 4 f) coF 5F. TO force L2(F)e/F fq co /-F,
we require that for every odd n there is a string 0y of length .n in F iff there is
no string y of length n in F. We omit the details.
principal method for showing that rx properly contains x is to ensure that
L(X) 4/x- x. It is easy to modify the proof of Theorem 3 to obtain an
oracle X for which L(X)e A/x, but every deterministic query machine, with
oracle X that recognizes L(X) requires exponential time for all but finitely many
inputs.

{x:lxl is even and there is
{x:lxl is odd and there is a string 0y e F

Q.E.D.

4. Open problems. We shall describe several open problems suggested by

Albert Meyer. First we recall another characterization of ff [6.

Q.E.D.

such that x L

predicate R(x, y) in

(:ly)[[y _< p(Ixl) & R(x, y)].

LMMA 3. A language L belongs to ,4/ iff there is a polynomial p(n) and a

One can draw analogies between the class

Proof. (.,=) Suppose x L. (:ly)[[y =< p(Ix[) & R(x, y)]. Then we can accept L
Clearly R(x, y) belongs to. We then choose a polynomial p(n) large enough that

in polynomial time by nondeterministically selecting a string y such that
<= p(Ixl) and accepting x if R(x, y) is true.
() If LI/’, then L is accepted by some query machine NPi. Define
predicate R(x, y) to hold iff y encodes an accepting computation ofNP on input x.
lYl < p(Ixl) whenever y encodes a computation of length =< pi(Ixl).
of languages recognizable in
of recursive (decidable) languages. We may
polynomial time and the class
consider a language "practically" decidable if it can be decided by some deter-
ministic polynomial-bounded procedure. From Lemma 3, / contains exactly
those languages definable by polynomial-bounded existential quantification over

predicates in. Similarly, co ff contains those languages definable by poly-
nomial-bounded universal quantification over predicates in. Thus t/ corres-
the class. Then E’+

Meyer and Stockmeyer [6] have defined a polynomial-bounded analogue
Ao to be
of the arithmetic hierarchy, the -hierarchy. They define Z o
is the class of languages definable by polynomial-bounded
existential quantification over predicates in FI; that is, LZ+a iff there is a
polynomial p(n) and a predicate R(x, y) in FI/ such that x L
& R(x, y)]. Similarly, FI+ contains exactly those languages definable by poly-
nomial-bounded universal quantification over predicates in E. (Equivalently,
L E/ iff there is a polynomial p(n) and a predicate R(x, yl, "’", Y) in
such that
x L , (:lyl)(Vy2)... (Qyi)[lyll, ly21, "’", lYil <= p(lxl)& g(x, Yl,’", Yi)], where
there are
is defined to be
the class of languages recognizable in polynomial time with the aid of an oracle
for some language in E if;that is, L Aff+l iff L s for some S in E. The ’-

alternations of polynomial-bounded quantifiers.) Aft+

ponds to Z in Kleene’s arithmetic hierarchy [8], while co

corresponds to H

(:ly)[ly =<

IIo

y
c
a
v
i
r
p
-
s
m
r
e
t
/
g
r
o
.
m
a
i
s
.
s
b
u
p
e
/
/
:
s
p
t
t
h

e
e
s

;
t
h
g
i
r
y
p
o
c

r
o

e
s
n
e
c
i
l

M
A
I
S
o
t

t
c
e
j
b
u
s

n
o
i
t
u
b
i
r
t
s
i
d
e
R

.

2
5
.
4
1
2
.
2
5
1
.
6
3
1

o
t

6
2
/
5
0
/
1
1

d
e
d
a
o
l
n
w
o
D

 
 
 
 
 
 
 
 
 
 
 
 
 


<!-- pdf-page: 11 -->
RELATIVIZATIONS OF THE # =.9 /"/ QUESTION

441

(ii) Z U 1-I_ A+ Z+ 0 H+ 1.

for every j

Hfor any

problem since

of [6] implies the following.

However, it is not known if any of the inclusions in (ii) are proper; the -hierarchy

hierarchy is {Zf, I-If, Af’i >_ 0}.
The -hierarchy shares several of the properties of the arithmetic hierarchy"
(i) LeZf Ee 1-I;

may consist of only a single class, namely, Z Hff A . One of the results
i. In particular, if , then E H Af

LEMMA 4 (Meyer-Stockmeyer). If2
From Lemma 4 we see that proving E Hf for any
is an immediate consequence.
Hff’x
It is easy to relativize the -hierarchy. For any oracle X, let Eft’x
Nx. Then Ee’x+ is the class of languages definable by polynomial-
_-A,X
S e E’x. The, X-hierarchy is {E’x, H’x, A’X’i. 0}.
bounded existential quantification over predicates in H’X"also. He’xg+ is the class
of languages definable by polynomial-bounded universal quantification over
predicates in E’x; and Af; contains languages L such that L e s for some
For the oracle A of Theorem 1, a a, hence the, A-hierarchy collapses
entirely. If D is the oracle of Theorem 5, then Eft’
Hf’; the ,D-
hierarchy consists of only two levels. If E is the oracle of Theorem 6, then E ’e

Properties (i) and (ii) hold for relativized -hierarchies, as does Lemma 4.

nf
for every i.
1 is a dicult

1, thenZf

zf

Ef’ (since Hf’

Ef’
Ef’e) andE’e
Several questions can be asked about relativized -hierarchies.
that the, X-hierarchy contains infinitely many distinct classes?
(i) Does there exist an oracle X such that E’x N Ei +
, X-hierarchy extends exactly
(ii) Does there exist an oracle X such that E_e’x NE.’x

levels?

,X

for all i, that is, such

E+,e’x that is,the

Ef’
Ef’e 0 Hf’e.

(iii) Does there exist an oracle X such that the N, X-hierarchy is not trivial

but Zf,x

Af; 

Z ,X Oi+ H+ for all 9.

(Only question (i) has an armative answer for the arithmetic hierarchy.)

An interesting open question, less general than (i)-(iii) is
(iv) Does there exist an oracle X such that Ef’x
n,x9
-2
We were unable to settle (iv) by the methods of this paper.

Acknowledgments. We wish to thank Richard Ladner, Albert Meyer, and
Michael Fischer for allowing us to report their results in this paper. We are
especially grateful to Albert Meyer for suggesting Theorem 6 and the open problems
of 4. We thank the referees for their corrections and suggestions.

REFERENCES
[1] S. A. CooK, The complexity of theorem-proving procedures, Proc. Third Annual ACM Symposium

on the Theory of Computing, Shaker Heights, Ohio, 1971, pp. 151-158.

[2] J. HOPCROFT AND J. ULLMAN, Formal Languages and their Relation to Automata, Addison-Wesley,

Reading, Mass., 1969.

[3] R. M. K,RP, Reducibility among combinatorialproblems, Complexity of Computer Computations,
R. E. Miller and J. W. Thatcher, eds., Plenum Press, New York, 1972, pp. 85-104.
[4] R. LADNER, N. LyNch aND A. SELMAN, Comparison ofpolynomial-time reducibilities, Proc. Sixth
Annual ACM Symposium .on the Theory of Computing, Seattle, Wash., 1974, pp. 110-121.

y
c
a
v
i
r
p
-
s
m
r
e
t
/
g
r
o
.
m
a
i
s
.
s
b
u
p
e
/
/
:
s
p
t
t
h

e
e
s

;
t
h
g
i
r
y
p
o
c

r
o

e
s
n
e
c
i
l

M
A
I
S
o
t

t
c
e
j
b
u
s

n
o
i
t
u
b
i
r
t
s
i
d
e
R

.

2
5
.
4
1
2
.
2
5
1
.
6
3
1

o
t

6
2
/
5
0
/
1
1

d
e
d
a
o
l
n
w
o
D

 
 
 
 
 
 
 
 
 
 
 
 
 


<!-- pdf-page: 12 -->
442

THEODORE BAKER JOHN GILL AND ROBERT SOLOVAY

[5] K. MEHLHORN, On the size of computable functions, Proc. 14th IEEE Symposium on Switching

and Automata Theory, Iowa City, Iowa, 1973, pp. 190-196.

[6] A. R. MEYER AND L. J. STOCKMEYER The equivalence problemfor regular expressions with squaring
requires exponential space, Proc. 13th IEEE Symposium on Switching and Automata Theory,
1972, pp. 125-129.

[7] P. H. MORRIS, personal communication.
[8] H. ROGERS, JR., Theory of Recursive Functions and Effective Computability, McGraw-Hill,

New York, 1967.

[9] W. J. SAVITCH, Relationships between nondeterministic and deterministic tape complexities, J.

Comput. System Sci., 4 (1970), pp. 177-192.

[10] L. J. STOCKMEVER AND A. R. MEYER, Word problems requiring exponential time." preliminary
report, Proc. Fifth Annual ACM Symposium on the Theory of Computing, Austin, Texas,
1973, pp. 1-9.

y
c
a
v
i
r
p
-
s
m
r
e
t
/
g
r
o
.
m
a
i
s
.
s
b
u
p
e
/
/
:
s
p
t
t
h

e
e
s

;
t
h
g
i
r
y
p
o
c

r
o

e
s
n
e
c
i
l

M
A
I
S
o
t

t
c
e
j
b
u
s

n
o
i
t
u
b
i
r
t
s
i
d
e
R

.

2
5
.
4
1
2
.
2
5
1
.
6
3
1

o
t

6
2
/
5
0
/
1
1

d
e
d
a
o
l
n
w
o
D

 
 
 
 
 
 
 
 
 
 
 
 
 

