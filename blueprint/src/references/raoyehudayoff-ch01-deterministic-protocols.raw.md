<!-- generated-by: proofmatch local extraction -->
<!-- source-pdf-sha256: fa052d8c95c0cb623ac076478337d47a58de2818d97a8061a841b025654819cf -->
<!-- extractor: pdfminer.six v20260107 -->

<!-- pdf-page: 1 -->
1

Deterministic Protocols

A protocol specifies a way for k parties who each have access
to different inputs to communicate about their inputs, in order to
learn about some property of all the inputs. Each of the k parties may
have access to different bits of information. We begin by giving some
interesting examples of communication problems. Many of these
examples will be discussed in much more detail in future chapters of
the book.

}

0, 1

∈ {

Equality Alice and Bob are given two n-bit strings x, y

n and
want to know if x = y. There is a trivial solution: Alice can send
her input to Bob, and Bob can let her know if x = y. This is a
deterministic1 protocol that takes n + 1 bits of communication, and
no deterministic protocol can do better. On the other hand, there is
a randomized1 protocol that uses only O(1) bits of communication:
the parties can hash their inputs and check that the hashes are the
same. There is a non-deterministic1 protocol that uses O(log n) bits
= yi, she
of communication: If Alice guessed an index i where xi 6
could send it to Bob and they could conﬁrm that their inputs are
not the same.

1 These terms will be made clear in due
course.

⊆

Cliques and Independent Sets Alice and Bob are given two sets A, B
[n] and both know a graph G on the vertex set [n], with the
promise that A is a clique and B is an independent set. They want
to know whether A intersects B or not. There is no one-way pro-
tocol that solves this problem efﬁciently using less than n bits of
communication. However, there is an interactive protocol that uses
O(log2 n) bits of communication. If A contains a vertex v of de-
gree less than n/2, Alice announces the name of the vertex. Either
v
B or Alice and Bob can safely discard all the non-neighbors
of v, since these cannot be a part of A. This reduces the size of the
graph by a factor of 2. Similarly, if B contains a vertex v of degree
at least n/2, Bob announces the name of v. Again, either v

A,

∈

∈



<!-- pdf-page: 2 -->
16 communication complexity

or Alice and Bob can safely discard all the neighbors of v which
reduces the size of the graph by a factor of 2. After at most log n
such steps, Alice and Bob will have determined the answer.

k-Disjointness Alice and Bob are given two sets A, B

[n], each

⊆

of size k, and want to know if the sets share a common element.
Alice can send her set over, which takes k log n bits of communi-
cation. There is a randomized protocol that uses only O(k) bits of
communication. Alice and Bob sample a random sequence of sets
in the universe, Alice announces the name of the ﬁrst set that con-
tains A. If A and B are disjoint, this eliminates half of B. Repeating
this procedure gives a protocol with O(k) bits of communication.
There is a non-deterministic protocol that uses O(log n) bits of
communication.

k-party Disjointness The input is k sets A1, . . . , Ak ⊆

[n], and there are
k parties. The i’th party knows all the sets except for the i’th one.
The parties want to know if there is a common element in all sets.
There is a deterministic protocol with O(n/2k) bits of communi-
cation, and this is known to be essentially the best protocol. We
know that no randomized protocol can have communication less
than √n/2k, but it is not known whether this bound is tight.

∈

3-Sum The input is three numbers x, y, z

[n]. Alice knows (x, y),
Bob knows (y, z) and Charlie knows (x, z). The parties want to
know whether or not x + y + z = n. Alice can tell Bob x, which
would allow Bob to announce the answer. This takes O(log n) bits
of communication. There is a deterministic protocol that com-
municates o(log n) bits, but one can show that any deterministic
protocol must communicate ω(1) bits. There is a randomized
protocol that communicates O(1) bits.

Pointer Chasing The input consists of two functions f , g : [n]
where Alice knows f and Bob knows g. Let a0, a1, . . . , ak ∈
deﬁned by setting a0 = 1, and ai = f (g(ai
pute ak. There is a simple k round protocol with communication
O(k log n) that solves this problem, but any protocol with fewer
than k rounds requires Ω(n) bits of communication.

1)). The goal is to com-

[n],
→
[n] be

−

Graph Connectivity The input is an undirected graph on the vertices
[n]. There are k parties, and the j’th party knows all of the edges
except those that touch the vertices of [(j
1)n/k, jn/k]. The parties
want to know whether 1 is connected to n in the graph. The trivial
deterministic protocol takes O(n2/k) bits of communication. One
can show that there is no randomized protocol with less than n/2k
bits of communication.

−



<!-- pdf-page: 3 -->
Deﬁning 2 party protocols

deterministic protocols

17

Let us define exactly what we mean by a 2 party deterministic
protocol. Suppose the inputs come from two sets
. A protocol
π is speciﬁed by a rooted tree, where every internal vertex v has 2
children. Every such vertex v is associated with either the ﬁrst or
second party, and a function fv :
(or fv :
0, 1
mapping an input of that party to a child of the vertex.

X → {

Y → {

0, 1

X

Y

}

}

)

,

∈ X × Y

Given inputs (x, y)

, the outcome of the protocol π(x, y) is
a leaf in the protocol tree, computed as follows. The parties begin by
setting the current vertex v to be the root of the tree. If the ﬁrst party
(resp. second party) is associated with the vertex v, she announces
the value of fv(x) (resp. fv(y)). Both parties set the current vertex
to be the child of v indicated by the value of fv . This process is
repeated until the current vertex is a leaf, and this leaf is the outcome
of the protocol.

Given a boolean function g :

X × Y → {

0, 1

}

we say that π

X × Y

computes g if π(x, y) determines g(x, y) for every input in
. It is
sometimes convenient to imagine that the leaves of the protocol tree
are labeled by the value of the function that was computed.
The communication complexity of the protocol π, denoted

, is
the depth of the protocol tree2. The communication complexity of
a function is c if there is protocol that computes the function with
c bits of communication, but no protocol can compute the function
with less than c bits of communication. The number of rounds of the
protocol is the maximum number of alternations that occur between
messages of the ﬁrst party and messages of the second party on any
root to leaf path in the tree. An efﬁcient protocol is one of minimal
communication complexity and minimal number of rounds.

π

k

k

Some basic observations:

Fact 1.1. For any protocol π, the number of rounds in
π

1.

k

k −

π

k

k

is always at most

Lemma 1.2. The number of leaves in the protocol tree for
2k

k.

π

π

k

k

is at most

Proof. We prove this by induction on the communication of the
protocol. When the communication is 0, the number of leaves is
exactly 20 = 1. In general, if the communication is
number of leaves in the left subtree and the right subtree of the root
is at most 2k
π
most 2

1 by induction, so the total number of leaves is at

, then the

k−
1 = 2k

2k

k−

k.

π

k

k

π

π

·

The setup is analogous for k party
Xk be k sets. A
protocols. Let
X2, . . . ,
X1,
k-party communication protocol deﬁnes
a way for k parties to communicate
information about their inputs, where
the i’th party gets an input from the set
Xi. Every vertex v is associated with a
party i and a function fv :
}

Xi → {

0, 1

In the special case that

=

=

Y

X

}

0, 1

n, and each of the functions fv is
{
restricted to being equal to a bit of the
input, the resulting protocol is called a
decision tree, a model worthy of study in
its own right.

One can easily generalize the deﬁni-
tions to handle functions that are not
boolean, but we restrict our attention to
booleann functions for simplicity.

For k-party protocols we may also
consider functions g :
D ⊆ X1, . . . ,
some domain
points in
become important when we study the
Number-on-Forehead model.

. This generalization will

Xk to

D → R

R

mapping

2 The length of the longest path from
root to leaf.

Example: Alice sends 2 bits, Bob sends
3 bits, Alice sends 1 bit. Number of
rounds is 2.



<!-- pdf-page: 4 -->
18 communication complexity

Balancing Protocols

Lemma 1.2 is tight exactly when the protocol tree is a balanced
binary tree. Does it make sense to ever have a protocol tree that is
not balanced? It turns out that one can always balance an unbalanced
tree.

Theorem 1.3. If π is a protocol with ` leaves, then there is a protocol that
computes the outcome π(x, y) with communication at most 2 log3/2

`.

To prove the theorem, we need a simple lemma about trees.

Lemma 1.4. In every protocol tree that has ` leaves, there is a vertex v such
that the subtree rooted at v contains r leaves, and `/3

2`/3.

r

≤

≤

Proof. Let r be the root of the protocol tree. Consider the sequence
of vertices r = v1, v2, . . . deﬁned as follows. v1 is the root of the tree,
and for each i, vi+1 is the child of vi that has the most leaves under it.
Let `i denote the number of leaves in the subtree rooted at vi. By the
`i/2, and `i+1 < `i. Since `1 = `,
deﬁnition of vi, we have that `i+1 ≥
and the sequence is decreasing until it hits 1, there must be some i for
which `/3

2`/3.

`i ≤

≤

In each step of the balanced protocol, the parties pick a vertex v
as promised by Lemma 1.4 and each verify whether their input is
consistent with the entire path leading up to v. If this is the case, the
parties repeat the procedure at the subtree rooted at v. If not, the
parties delete the vertex v from the protocol tree and continue the
protocol. In each step, the number of leaves of the protocol tree is
reduced by a factor of at least 2
steps.

3 , so there can be at most log3/2

` such

Rectangles

A very useful concept to understand communication protocols
is the concept of a rectangle in the inputs. A rectangle is a subset
R = A

, where A

and B

B

.

×

⊆ X × Y

⊆ X

⊆ Y

R.

Lemma 1.5. R is a rectangle if and only if whenever (x, y), (x0, y0)
then (x0, y), (x, y0)

∈
B is a rectangle, then (x, y), (x0, y0)
B. Thus (x, y0), (x0, y)
A

Proof. If R = A
R means
B. On the
that x, x0 ∈
other hand, if R is an arbitrary set with the given property, if R is
empty, it is a rectangle. If R is not empty, let (x, y)

×
A and y, y0 ∈

∈
×

∈

R,

∈

R be an element.

∈

Input: Alice knows x
knows y
, both know a
protocol π that has ` leaves.

, Bob

∈ X

∈ Y

Output: The outcome of the
protocol π.

while π has more than 1 leaf do

Find a vertex v as promised by
Lemma 1.4;
Alice and Bob exchange two
bits to conﬁrm that their
inputs are consistent with the
path in the protocol tree to v;
if both inputs are consistent with
v then

Replace π with the
subtree rooted at v;

else

end

Remove v from the
protocol tree, and replace
v’s parent with v’s sibling;

end
Output the unique leaf in π;

Figure 1.1: Rebalancing Protocol

Figure 1.2: A rectangle.

For k party protocols, a rectangle is the
cartesian product of k sets.



<!-- pdf-page: 5 -->
deterministic protocols

19

{

Deﬁne A =
the property of R, A
x0 ∈

x0 : (x0, y)
B
×
A

A, y0 ∈

B, so R

⊆

×

R

and B =

y0 : (x, y0)

∈
⊆
B. Thus R = A

}
R, and for every element (x0, y0)
B.

∈

{

}

R

. Then by
R,

∈

×

It turns out that every vertex of the protocol tree corresponds to

a rectangle of the inputs. For every vertex v, let Rv ⊆ X × Y
denote
the set of inputs (x, y) that would lead the protocol to pass through
the vertex v during the execution. For the root vertex r, we see that
Rr =
, so Rr is a rectangle. Now consider an arbitrary vertex v
X × Y
such that Rv = A
B is a rectangle. Let u, w be the children of v in the
protocol tree. Suppose the ﬁrst party is associated with v, and u is the
vertex that the players move to when fv(x) = 0. Then set

×

A0 =
A1 =

x

y

{

{

∈

∈

A : fv(x) = 0
A : fv(x) = 1

}

}

B, Rw = A1 ×
A0, A1 are a partition of A, and moreover Ru = A0 ×
Thus Ru, Rv are rectangles that partition v. Continuing in this way,
we get that Rv is a rectangle for every vertex in the protocol tree. We
have shown:

B.

Lemma 1.6. For every vertex v in the protocol tree, Rv is a rectangle.
Moreover, the rectangles given by all the leaves of the protocol tree form a
partition of the inputs.

A rectangle R is said to be monochromatic under g if g is con-
stant on R. In other words, for every two points (x, y), (x0 , y0 )
R,
∈
g(x, y) = g(x0 , y0 ). We say that the rectangle is 1-monochromatic
if the function takes on the value 1 on the rectangle. We shall use
Lemmas 1.2 and 1.6 to show that every function with small com-
munication complexity induces a small partition of the inputs into
monochromatic rectangles.

Figure 1.3: A partition of the space into
rectangles.

0
1
1
0
1
0
0
0
0
1
1
1

2

6
6
6
6
6
6
6
6
6
6
6
6
6
6
6
6
6
6
4

1 1
1 0
1 0
0 0
0 0
1 0
0 0
0 0
0 0
1 0
1 0
1 1

0
1
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

0 1
1 0
0 0
1 1
0 0
0 1
0 0
0 0
0 0
0 0
0 0
0 1

1
0
0
0
1
0
1
1
1
1
0
0

1
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

0 1
0 1
0 0
0 0
0 0
0 1
0 1
1 1
0 1
0 1
0 0
1 1

3

7
7
7
7
7
7
7
7
7
7
7
7
7
7
7
7
7
7
5

Figure 1.4: A 0-monochromatic rectan-
gle.

Suppose a protocol π computes a function g :

X × Y → {

, and

0, 1
}
Rv such

= g(x0, y0), then π cannot compute g, since the outcomes

let v be a leaf in π. If there are two inputs (x, y), (x0, y0)
that g(x, y)
of π(x, y) and π(x0, y0) are the same, and so must be incorrect in
at least one case. So every leaf v of the protocol corresponds to a
monochromatic rectangle Rv under g. Combining this fact with
Lemmas 1.2 and 1.6 gives:

∈

Theorem 1.7. If the communication complexity of g :
then

}
can be partitioned into at most 2c monochromatic rectangles.

X × Y → {

0, 1

is c,

X × Y

Figure 1.5: A partition into rectangles
that does not correspond to a protocol.

6


<!-- pdf-page: 6 -->
20 communication complexity

From Rectangles to Protocols

Given Theorem 1.7, one might wonder whether every partition
of the inputs can be realized by a protocol. While this is not true
(see Figure 1.5), we can show that a small partition of the inputs into
monochromatic rectangles under g can be used to give an efﬁcient
protocol for computing g. A partial answer to this question is given
by the following theorem3:

Theorem 1.8. If g admits 2c monochromatic rectangles whose union
, then there is a protocol that computes g with O(c2) bits of
is
communication.

X × Y

A key concept we will need to understand Yannakakis’s protocol
is the notion of two rectangles intersecting horizontally and vertically.
We say that two rectangles R = A
horizontally if A intersects A0, and intersect vertically if B intersects
B0. If x
A0 ×
Fact 1.9. If R, R0 are disjoint rectangles, they cannot intersect horizontally
and intersect vertically.

B and R0 = A0 ×

A
B0, proving:

B0, then (x, y)

B0 intersect

B and (x, y)

A0 and y

×

×

∈

∈

∈

∩

∈

∩

A

B

The parties are given inputs (x, y) and know a collection of

R

∈

×

R

. In

∈ R

that cover all inputs. The aim of the

B that is consistent with their input. If Alice announces

monochromatic rectangles
protocol is to ﬁnd a rectangle Rx,y such that (x, y)
each step, one of the parties will announce the name of a rectangle
R = A
such a rectangle, then it must be that x
discard all rectangles in
rectangle that contains (x, y) will not be discarded. Similarly, if Bob
announces R, then both parties can safely discard all rectangles that
do not horizontally intersect R. We shall show that there will always
be an R that one of the parties can announce that will allow for many
other rectangles to be discarded.
: g(R) = 0

that do not vertically intersect R. Any

A, so both parties can safely

Let

R

∈

}
: g(R) = 1

, be the set of rectangles that have
be the set of rectangles with

R0 =
value 0, and
value 1.

R
{
R1 =

∈ R
R
{

∈ R

}

Deﬁnition 1.10. Say that a rectangle R = (A

B)

∈ R0 is

×

3 Yannakakis, 1991; and Aho et al., 1983

An efﬁcient partition of the 1’s of the
input space into rectangles also leads to
an efﬁcient protocol (Exercise 1.2).

3

1

2

Figure 1.6: Rectangles 1 and 2 intersect
vertically, while rectangles 1 and 3
intersect horizontally.

• horizontally good if x

A, and R horizontally intersects at most half of

the rectangles in

∈
R1, and

• vertically good if y
R1.

rectangles in

∈

B, and R vertically intersects at most half of the



<!-- pdf-page: 7 -->
deterministic protocols

21

, Bob

∈ X

Input: Alice knows x
knows y
∈ Y
set of monochromatic
rectangles
contains (x, y).

R

whose union

, both know a

Output: g(x, y).

R1 is not empty do
while
if
R
∃
good then

∈ R0 that is horizontally
Alice sends Bob the name
of R;
Both parties discard all
rectangles from
R1 that
do not horizontally
intersect R;
else if
R
vertically good then

∈ R0 that is
Bob sends Alice the name
of R;
Both parties discard all
rectangles from
R1 that
do not vertically intersect
R;

∃

else

end

The parties output 1;

end
The parties output 0;

Figure 1.7: A Protocol from Monochro-
matic Rectangle Covers

4 Göös et al., 2015

Observe that Alice can compute which rectangles are horizontally
good, and Bob can ﬁnd all rectangles that are vertically good without
any communication.

Suppose g(x, y) = 0. Then there must be a rectangle Rx,y ∈ R0 that
R1 are disjoint from Rx,y, Fact
R1 can intersect Rx,y horizontally,

contains (x, y). Since the rectangles of
1.9 implies that every rectangle in
or vertically, but not both horizontally and vertically. Thus either
R1 intersect Rx,y horizontally, or
at most half of the rectangles in
at most half of them intersect Rx,y vertically. Moreover, any such
rectangle is consistent with both Alice and Bob’s input. So we have
shown:

Claim 1.11. Any rectangle of
good, or vertically good.

R0 that contains (x, y) is either horizontally

In each step of the protocol, one of the parties announce the name

of a rectangle that is either horizontally good or vertically good, if
such a rectangle exists. This leads to half of the rectangles in
being discarded. If no such rectangle exists, then it must mean that
no rectangle of
R1 can
survive at most c + 1 such discards, and a rectangle in the family
can be described with c bits of communication, the communication
complexity of the protocol is at most O(c2).

R0 covers (x, y), and so g(x, y) = 1. Since

R1

Open Problem 1.12. Recent work4 has shown that there is function g
under which the inputs can be partitioned into 2c monochromatic rectangles,
yet no protocol can compute g using o(c3/2) bits of communication. What
are the best parameters with which one can prove Theorem 1.8?

Some lower bounds

We turn to proving that some problems do not have efﬁcient
protocols. The easiest way to prove a lower bound is to use the
characterization provided by Theorem 1.7. If we can show that the
inputs cannot be partitioned into 2c monochromatic rectangles, or do
not have large monochromatic rectangles, then that proves that there
is no protocol computing the function with c bits of communication.

Using bounds on the size of Monochromatic Rectangles

Equality Consider the equality function EQ :

deﬁned as:

0, 1

{

n

}

× {

0, 1

n

}

→ {

0, 1

}

EQ(x, y) =

1 if x = y,

0 otherwise.






(1.1)



<!-- pdf-page: 8 -->
22 communication complexity

Alice can send Bob her input, and Bob can respond with the value
of a function, giving a protocol with communication n + 1. Is
there a protocol with communication n? Since any such protocol
induces a partition into 2n monochromatic rectangles, a ﬁrst
attempt at proving a lower bound might to try and show that
there is no large monochromatic rectangle. If we could prove that,
then we could argue that many monochromatic rectangles are
needed to cover the whole input. Unfortunately, equality does
have large monochromatic rectangles, for example, the rectangle
R =
. This is a rectangle that has density
1
4 , and it is monochromatic, since EQ(x, y) = 0 for every (x, y)
R.
Instead, we will try to show that equality does not have any large
1-monochromatic rectangle.

(x, y) : x1 = 0, y1 = 1

∈

{

}

= x0, then the points (x, x) and (x, x0) cannot be
Observe that if x
in the same monochromatic rectangle. Otherwise, by Lemma 1.5,
(x, x0) would also have to be included in this rectangle. Since the
rectangle is monochromatic, we would have EQ(x, x0) = EQ(x, x),
which is a contradiction. We have shown:

Claim 1.13. Every 1-monochromatic rectangle of EQ has size at most 1.

Since there are 2n inputs x where EQ(x, x) = 1, this means that
you need 2n rectangles just to cover the 1’s. Thus we have shown:

Theorem 1.14. The deterministic communication complexity of EQ is at
least n + 1.

Disjointness Next, consider the disjointness function, Disj : 2[n]

2[n]

→

1 deﬁned by:

Disj(X, Y) =




1 if X

Y = ∅,

∩

0 otherwise.

×

(1.2)


Alice can send her whole set X to Bob, which gives a protocol with
communication n + 1. Can we prove that this is optimal? Once
again, this function does have large monochromatic rectangles,
for example the rectangle R =
, but we
{
shall show that there are no large monochromatic 1-rectangles.
Indeed, suppose R = A
X0 =
AX and Y0 =
∪X
∈
+
Y0| ≤
X0|
so
|
=
B
A
R
| ≤
||
|

B is a 1- monochromatic rectangle. Let
BY. Then X0 and Y0 must be disjoint,
Y0|, so
2|

|
Claim 1.15. Every 1-monochromatic rectangle of Disj has size at most 2n.

∈
n. On the other hand,

2n. We have shown:

(X, Y) : 1

×
∪Y

X0|,

X, 1

| ≤

| ≤

|
|

2|

∈

∈

A

Y

B

}

|

|

On the other hand, the number of disjoint pairs (X, Y) is exactly
3n. That’s because for every element of the universe, there are

6


<!-- pdf-page: 9 -->
3 possibilities: to be in X, be in Y or be in neither. Thus, at least
3n/2n = 2(log 3
the 1’s of Disj, an so :

1)n monochromatic rectangles are needed to cover

−

deterministic protocols

23

We shall soon prove a stronger lower
bound for disjointness.

Theorem 1.16. The deterministic communication complexity of Disj is at
least (log 3

1)n.

−

Richness

Sometimes we need to understand asymmetric communication proto-
cols, where we need separate bounds on the communication complex-
ity of Alice and Bob. The concept of richnesst5 is useful here:

5 Miltersen et al., 1998

Deﬁnition 1.17. A function g :
if there is a set V
Uy ⊆ X

|
⊆
, with g(Uy, y) = 1.

Y,

V

|

}
X × Y → {
= v, such that for all y

0, 1

is said to be (u, v) rich
V, there is a set

∈

A rich function has large 1-monochromatic rectangles:

Lemma 1.18. If g :
}
for computing g where Alice sends at most a bits and Bob sends at most b
bits, then g admits a u

is (u, v) rich, and if there is a protocol

v
2a+b 1-monochromatic rectangle.

X × Y → {

0, 1

2a ×

, y

∈ Y

Proof. The statement is proved inductively. For the base case, if the
protocol does not communicate at all, then clearly g(x, y) = 1 for all
x

, and the statement holds.

∈ X
=
If Bob sends the ﬁrst bit of the protocol, then Bob partitions
Y
Y0 ∪ Y1. One of these two sets must have v/2 off the inputs y that
make g (u, v) rich. By induction, this set contains a u
1 1-
monochromatic rectangle, as required. On the other hand, if Alice
sends the ﬁrst bit, then this bit partitions
Every input y that has u 1’s must have u/2 1’s in either
Thus there must be v/2 choices of inputs y
for g restricted to
we get that there is a 1-monochromatic rectangle with dimensions
u/2
2a

X1.
X0,
X1.
X0 or
that have u/2 1’s

1 ×
Now let us see some examples where richness can be used to

or for g restricted to

1+b , as required.

into two sets

X0 × Y

X1 × Y

v/2
2a+b

2a ×

. By induction,

∈ Y

v/2

X

2a

−

−

−

prove lower bounds.

Lopsided Disjointness Suppose Alice is given a set X

[n] of size

⊆
k < n, and Bob is given a set Y
[n], and they want to compute
⊆
whether the sets are disjoint or not. Now the obvious protocol is
for Alice to send her input to Bob, which takes log (n
k) bits6. How-
ever, what can we say about the communication of this problem if
Alice is forced to send much less than log (n

k) bits?

To prove a lower bound, we need to analyze rectangles of a
certain shape. We restrict our attention to special family of sets for

6 In Chapter 2, we show that the
communication complexity of this
problem is at least log (n
k).



<!-- pdf-page: 10 -->
2 Y

X 3

Figure 1.8: An input with n = 12, k =
3, t = 2.

A

k

|

|

≥

1/k.

By the arithmetic-mean, geometric
mean inequality.

24 communication complexity

Alice and Bob. Let n = 2kt, and suppose Y contains exactly one
element of 2i
1, 2i, for each i, and that X contains exactly one
element from 2t(i

1) + 1, . . . , 2ti for each i.

−

−

Claim 1.19. If A
1/k
2kt

A

k

.

−

|

|

B is a 1-monochromatic rectangle, then

B

|

| ≤

×

X

∈

S

Proof. We claim that

X
∈
A X has ai elements in

|

S

A X

2t(i

| ≥
−

{

A

k
1) + 1, . . . , 2ti

1/k. Indeed, if the union
, then

|

|

}

1/k

X

=

k
∑
i=1

k

ai ≥

k
∏
i=1

ai

X

!

(cid:12)
(cid:12)
(cid:12)
(cid:12)
(cid:12)

A
[X
∈

(cid:12)
(cid:12)
(cid:12)
(cid:12)
(cid:12)
elements intersects every set of B. Thus,
S
at least k
S
possible choices for sets in B is at most 2kt
−

A

∈

|

|

A X cannot contain both 2i, 2i + 1 for any i, since one of these

A X determines
1/k elements of every set of B, and the number of

∈

X

A

k

|

|

1/k

.

The disjointness matrix here is at least (tk, 2kt)-rich, since every

choice Y allows for tk possible choices for X that are disjoint. By
Lemma 1.18, any protocol where Alice sends a bits and Bob sends
b bits induces a 1-monochromatic rectangle with dimensions
tk/2a

b, so Claim 1.19 gives:

2kt

a

−

−

×

2kt

−

a

−

b

a + b

⇒

≤

≥

We conclude:

kt/2a/k

2kt

−
n
2a/k+1 .

= k and Alice sends at most a bits
Theorem 1.20. If X, Y
|
and Bob sends at most b bits in a protocol computing Disj(X, Y), then
a + b

[n],

⊆

X

|

.

n
2a/k+1

≥

Span Suppose Alice is given a vector x

n, and Bob is given
0, 1
n. Their goal is ﬁgure out
a n/2 dimensional subspace V
whether or not x
V. As in the case of disjointness, we start by
claiming that the inputs do not have 1-monochromatic rectangles
of a certain shape:

∈ {
}

⊆ {

0, 1

∈

}

Claim 1.21. If A
2n2/2
n log

A

|.

−

|

B is a 1-monochromatic rectangle, then

B

|

| ≤

×

Proof. The set of x’s in the rectangle must span a subspace of
dimension at least log

. The number of n/2 dimensional sub-

A

|

|

spaces that contain the span of x is thus at most (
2n2/2

n log

A

|.

|

−

2n
log

) ≤

A

|

|

n/2

−

 


<!-- pdf-page: 11 -->
deterministic protocols

25

The problem we are working with is at least (2n/2, 2n2/4/n!)-
rich, since there are at least 2n2/4/n! subspaces, and each contains
2n/2 vectors. Applying Lemma 1.18 and Claim 1.21, we get that if
there is a protocol where Alice sends a bits and Bob sends b bits,

n2/4

⇒
n2/4

−

−
a(n + 1)

⇒

−

2n2/4
b

a

a

b/n!

−

−

n log n

n log n

−

−

n log 2n/2

a

−

−

2n2/2
na

b.

≤

≤

≤

Theorem 1.22. If Alice sends a bits and Bob sends b bits to solve the span
problem, then b

a(n + 1)

n log n.

n2/4

≥

−

−

Using Fooling Sets

Greater-than Our next example is the greater-than function, GT :

[n]

[n]

0, 1

}

→ {

×

deﬁned as:

GT(x, y) =

1 if x > y,

0 otherwise.




(1.3)

log n


The trivial protocol has communication complexity
and we shall show that this is tight. The methods we used for the
last two examples will surely not work here, because GT has large
0-monochromatic rectangles (like R =
)
and large 1 monochromatic rectangles (like R =
n/2, y < n/2
bound. Consider the set of n points S =

). Instead we shall use a fooling set to to prove the

(x, y) : x < n/2, y > n/2

(x, y) : x >

. We claim:

(x, x)

bits,

}

{

}

{

d

e

{

}

Claim 1.23. Two points of S cannot lie in the same monochromatic
rectangle.

Indeed, if R is monochromatic, and x < x0, but (x, x), (x0, x0)
∈
then since R is a rectangle, (x0, x)
R. This is contradicts the
fact that R is monochromatic, since GT(x0, x)
= GT(x0, x0). So
once again, we have shown that the number of monochromatic
rectangles must be at least n, proving:

∈

R,

Theorem 1.24. The deterministic communication complexity of GT is at
least log n.

Disjointness Fooling sets also allow us to prove tighter lower bounds
on the communication complexity of disjointness. Consider the
set S =
, namely X paired with its complement, for ev-
ery set X. Once again, we see that no monochromatic rectangle
can contain two such pairs, because if such a rectangle contained
= Y, then it would also contain (X, Y), but this
(X, X), (Y, Y) for X

(X, X)

{

}

6
6


<!-- pdf-page: 12 -->
26 communication complexity

last pair of sets must intersect, while the other two pairs are dis-
joint. Since S has 2n pairs, and at least one more monochromatic
rectangle is required, this proves:

Theorem 1.25. The deterministic communication complexity of disjoint-
ness is at least n + 1.

Krapchenko’s Method

. Since

n : ∑n

i=1 xi = 0 mod 2
and

We end this chapter with a clever idea of Krapchenko. Let
n : ∑n
, y

=
x
{
i=1 yi = 1
∈ {
Y
are disjoint, for every x
, there
= yi. Suppose Alice is given x and Bob is

0, 1
}
{
mod 2
Y
is an index i such that xi
given y, and they want to ﬁnd an index i. How much communication
is required?

}
∈ X

∈ Y

and

0, 1

=

X

X

∈

}

}

{

y

Perhaps the most trivial protocol is for Alice to send Bob her entire

string, but we can use binary search to do better. Since

∑
n/2
≤

i

xi + ∑
i>n/2

xi 6

yi mod 2,

yi + ∑
i>n/2

= ∑
n/2
i
≤
n/2 xi mod 2 and ∑i

≤

n/2, y

Alice and Bob can exchange ∑i
n/2 yi mod 2.
If these values are not the same, they can safely restrict their attention
to the strings x
n/2 and continue. On the other hand, if the
values are the same, they can continue the protocol on the strings
x>n/2, y>n/2. In this way, in every step they communicate 2 bits and
eliminate half of their input string, giving a protocol of communica-
tion complexity 2 log n.

≤

≤

≤

It is easy to see that log n bits of communication are necessary,
because that’s how many bits it takes to write down the answer.
Now we shall prove that 2 log n bits are necessary, using a variant of
fooling sets. Consider the set of inputs

We need at least n monochromatic
rectangles to cover pairs of the type
(0, ei), where ei is the i’th unit vector.

S =

(x, y)

{

∈ X × Y

: x, y differ in only 1 coordinate

.

}

·

−

2n

∈ X

1 inputs, since one can pick an input of S by picking

and ﬂipping any of the n coordinates. We will not be able to

S contains n
x
argue that every monochromatic rectangle must contain only one
element of S or bound the number of elements in any way. Instead,
we will prove that if such a rectangle does contain many elements of
S, then it is big:

Claim 1.26. Suppose R is a monochromatic rectangle that contains r
elements of S. Then

r2.

R

|

| ≥

The key observation here is that two elements (x, y), (x, y0)

cannot be in the same monochromatic rectangle. For if the rectangle
was labeled i, (x, y), (x, y0) must disagree in the i’th coordinate, but

S

∈

6


<!-- pdf-page: 13 -->
×
| ≥

|

since they both belong to S, that is the only coordinate on which they
disagree. Thus y = y0. Similarly we cannot have two distinct elements
(x, y), (x0, y)
∈
Thus, if R = A
R
proving that

S that belong to the same monochromatic rectangle.

B has r elements of S, we must have

| ≥

| ≥

r2.

A

r,

B

|

|

r,

Now suppose there are t monochromatic rectangles that cover

the set S, and the i’th rectangle covers ri elements of S. Then
∑t
i=1 ri, but since the rectangles are disjoint, 22n
i=1 r2
these facts and the Cauchy-Schwartz inequality:

∑t

≥

−

2

=
S
|
|
i . Using

22n

−

2

t
∑
i=1

r2
i ≥  

t
∑
i=1

≥

ri/√t

2

!

= n222n

2/t,

−

proving that t
≥
best one can do.

n2. This shows that the binary search protocol is the

Rectangle Covers

Given that rectangles play such a crucial role in the communica-
tion complexity of protocols, it is worth studying alternative ways to
measure the complexity of functions. Here we investigate what one
can say if we count the number of monochromatic rectangles needed
to cover all of the inputs.

Deﬁnition 1.27. We say that a boolean function has a 1-cover of size C if
there are C monochromatic rectangles whose union is all of the inputs that
evaluate to 1. We say that the function has a 0-cover of size C if there are C
monochromatic rectangles whose union is all of the inputs that evaluate to 0.

By Theorem 1.7, every function that admits a protocol with com-
munication c also admits a 1-cover of size at most 2c and a 0-cover of
size at most 2c. Conversely, Theorem 1.8 shows that small covers can
be used to give small communication.

Can the logarithm of the cover number be signiﬁcantly different

{

X, i

X, Y : i

from the communication complexity? Consider the disjointness
function, deﬁned in (1.2). For i = 1, 2, . . . , n, deﬁne the rectangle
Ri =
. Then we see that R1, R2, . . . , Rn form
a 0-cover for disjointness. So there is a 0 cover of size n, yet the the
communication complexity of disjointness is linear is n + 1. However,
we shall see in a later chapter that any 1-cover of disjointness must
have 2Ω(n) rectangles.

∈

∈

Y

}

Another interesting example is the k-disjointness function. Here

[n] of size k. We shall see in
Alice and Bob are given sets X, Y
Chapter 2 that the communication complexity of k-disjointness is

⊆

deterministic protocols

27

Rectangle covers have an interesting in-
terpretation in terms of non-deterministic
communication complexity. If a func-
tion has a 1-cover of size C, then given
any input that evaluates to 1, Alice and
Bob can non-deterministically guess the
name of a rectangle that covers their
input, and then check that their inputs
are consistent with the guessed rectan-
gles. On the other hand, if their inputs
correspond to a 0, no guess will con-
vince them that their input is a 1. One
can show that any non-deterministic
protocol for a function corresponds to a
1-rectangle cover!



<!-- pdf-page: 14 -->
28 communication complexity

at least log (n
k) ≈
disjointness using n rectangles.

k log(n/k). As above, there is a 0-cover of k-

k)2
Claim 1.28. k-disjointness has a 1-cover of size 22k ln((n

).

We prove Claim 1.28 using the probabilistic method. Sample a

{

⊆

(X, Y) : X

[n] and using the

random 0-rectangle by picking a random set S
rectangle R =
S, Y
all inputs X, Y where X is contained in S, and Y is contained in the
complement of S. Now sample t = 22k ln
independently. The probability that a particular disjoint pair X, Y is
2k. So the probability that the
included in any single rectangle is 2−
pair is excluded from all the rectangles is

. Namely, the set of

}
k)2
(n

such rectangles

[n]

⊆

⊆

(cid:16)

(cid:17)

S

\

2−

2k)t

(1

−

≤

2−

e−

2kt < (n

k)−

2

,

Fact: 1

x

−

≤

e−

x for x

0.

≥

by the choice of t. Since the number of disjoint pairs X, Y is at most
k)2
(n
, this means that the probability that any disjoint pair is ex-
cluded by the t rectangles is less than 1. So there must be t rectangles
that cover all the 1 inputs.

Setting k = log n, we have found 1-cover with t = 22 log n ln ( n
log n) =
O(n2 log2 n) rectangles. This example shows that Theorem 1.8 is tight,
at least when it comes to rectangle covers.

Direct-sums in Communication Complexity

If a function requires c bits of communication, how much commu-
nication is required to compute k copies of the function? Given a
function g :
(

, we deﬁne gk : (

× {
k by

→ {

n)k

n)k

0, 1

0, 1

0, 1

0, 1

×

}

}

{

}

n

n

0, 1
}
0, 1
}

{
→ {

{

}

g((x1, . . . , xk), (y1, . . . , yk)) = g(x1, y1), g(x2, y2), . . . , g(xk, yk).

7 Feder et al., 1995

We shall use many of the ideas we have developed so far to prove
that7:

Theorem 1.29. If g requires c bits of communication, then gk requires at
least k(√c

1) bits of communication.

log n

−

−

8 See Exercise 1.11

In fact, one can show that even computing the two bits

k
i=1g(xi, yi),
1) bits of communication8.

∧

k
i=1g(xi, yi) requires k(√c
log n
and
The main technical lemma we show is:

−

∨

−

Lemma 1.30. If gk can be computed with ` bits of communication, then the
inputs to g can be covered by 2n

`/k monochromatic rectangles.

2

·



<!-- pdf-page: 15 -->
Theorem 1.8 and Lemma 1.30 imply that g has a protocol with

communication (`/k + log n + 1)2. Thus,

deterministic protocols

29

c
`

≤

≥

⇒

(`/k + log n + 1)2
k(√c
1),

log n

−

−

as required.

Now we turn to proving Lemma 1.30. We ﬁnd the rectangles that

n denote
cover the inputs to g iteratively. Let S
the set of inputs to g that have not yet been covered by one of the
monochromatic rectangles we have found. Initially, S is the set of all
inputs. We claim:

⊆ {

× {

0, 1

0, 1

}

}

n

Claim 1.31. There is a rectangle that is monochromatic under g and covers
at least 2−

of the inputs from S.

`/k

S

|

|

Proof. Since gk can be computed with ` bits of communication, by
Theorem 1.7, the set Sk can be covered by 2
monochromatic rect-
angles, and so there must be some rectangle R that covers at least
2−

k of these inputs. For each i, deﬁne

S

`

`

|

|

Ri =

(x, y)

{

0, 1

∈ {

n

}

× {

0, 1

n :

}

∃

(a, b)

∈

R, ai = x, bi = y

,

}

which is a rectangle, since R is a rectangle. Moreover, since this
rectangle is monochromatic under gk, it must be monochromatic
under g. Now
, so there must be some i for which
S
Ri| ≥
2−
We repeatedly pick rectangles using Claim 1.31 until all of the

i=1 |

Ri|

| ≤

∏k

`/k

|
.

R

|

|

|

inputs to g are covered. After 2n2
inputs is at most

`/k steps, the number of uncovered

Fact: 1

x

−

≤

e−

x for x

0.

≥

22n

(1

·

−

`/k)2n2

2−

`/k

≤

22ne−

2−

`/k

·

`/k

2n2

= 22n

proving that this process will stop after at most 2n

·

Exercise 1.1

e−

2n < 1,

·
`/k steps.

2

Deﬁne the inner product of two n-bit strings x, y to be ∑n
mod 2. Use linear algebra to show that inner-product has no 0-
rectangle of size bigger than 2n. Conclude that the communication
complexity of inner-product is Ω(n).

i=1 xiyi

Exercise 1.2

Use ideas from Yannakakis’s protocol to show that if g :

X × Y →
1(1) can be partitioned into 2c rectangles, then g

is such that g−

0, 1
{
has communication complexity at most O(c2).

}



<!-- pdf-page: 16 -->
30 communication complexity

Exercise 1.3

Suppose Alice and Bob each get a subset of size k in the elements

[n], and want to know whether these sets intersect or not. Use the
fooling set method to show that at least log(

) bits are required.

n/k

b

c

Exercise 1.4

Suppose Alice gets a string x

n which has more 0’s than

0, 1
n that has more 1’s than 0’s.

}

∈ {
0, 1
}

1’s, and Bob gets a string y
∈ {
= yi. Use
They wish to communicate to ﬁnd a coordinate i where xi 6
Krapchenko’s method to show that at least 2 log n bits of communica-
tion are required.

Exercise 1.5

Show that almost all functions f

0, 1
communication Ω(n), where Alice gets x
0, 1

n, and they must evaluate f (x, y).

{

:

{

}

n

n

×

}
∈ {

0, 1

→ {
}

0, 1

require

}
n, Bob gets y

Exercise 1.6

Let X and Y be families of subsets of [n]. Assume for all x

|

Y the intersection of x and y contains at most 1 element, that

and y
∈
y
x
is,
∩
receives x
function f : X
→ {
deterministic complexity of f is O(log2(n)).

1. Deﬁne the communication problem as follows. Alice
X, Bob receives y

Y, and they with to evaluate the
. Show the

deﬁned as f (x, y) =

| ≤
∈

0, 1

×

∩

∈

Y

}

x

y

|

|

∈

X

∈

Exercise 1.7

Alice and Bob receive subsets of numbers X, Y

[n]. They wish

⊆

to output the median of X
Y. Exhibit a deterministic protocol
with O(log n) bits of communication. Show no protocol can do
asymptotically better.

∪

Exercise 1.8

Consider the partial function f :

0, 1

n

0, 1

n

0, 1

, where

{

}

× {

}

→ {

}

the inputs to the parties are interpreted as 2 n/2 bit strings and

f (x, x0, y, y0) =

1 if x = y and x0 6
0 if x

= y0,
= y and x0 = y0.






Show that there are 2n monochromatic rectangles under f . Use
fooling sets to show that the communication complexity of f is at
least Ω(n). This proves that an analogue of Theorem 1.8 does not
hold for partial functions.

6


<!-- pdf-page: 17 -->
deterministic protocols

31

Exercise 1.9

For a boolean function g, deﬁne g∧
k
i=1g(xi, yi). Show that if g∧

k by g(x1, x2, . . . , xk, y1, . . . , yk) =
`

k has a 1-cover of size 2

, then g has a

∧
1-cover of size 2

`/k.

Exercise 1.10

In this exercise, we will show9 that an optimal direct sum theorem

does not hold for the deterministic communication complexity of
relations. Consider the problem where Alice is given a subset X
⊆
of size t, and Bob is given no input. The players want to output an
element of X.

[n]

9 Alon and Orlitsky, 1995

1. Show that log(n

t + 1) bits of communication are required for

any deterministic protocol (and also sufﬁcient).

−

2. Show that if Alice is given k sets X1, . . . , Xk, each of size t, and the
parties want to compute an element from each of the sets, then
there is a deterministic protocol that communicates only

O(k log(n/t) + log(kn))

bits, which is signiﬁcantly less than k log(n

t + 1), when t = n/2.

−

Exercise 1.11

Hint: Pick a random subset of [n]k of
t)k
size (n/t)k ln (n
, and argue that it
Xk with positive
intersects X1 × · · · ×
probability.

n

n

{

}

0, 1

× {

Show that if g :

0, 1
communication, then computing
requires k(√c/2
small 1-cover using the protocol for computing
0-cover using the protocol for computing

0, 1
k
i=1g(xi, yi), and

→ {

log n

}
∧

−

−

}

requires c bits of
k
i=1g(xi, yi)

∨

k
i=1g(xi, yi), and

1) bits of communication. HINT: Find a

∨
k
i=1g(xi, yi).

∧



<!-- pdf-page: 18 -->

