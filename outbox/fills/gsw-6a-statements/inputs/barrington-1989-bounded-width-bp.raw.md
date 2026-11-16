<!-- generated-by: manual reading of page images of the passages used (DW-7); the PDF is a scan with no text layer -->
<!-- source-pdf-sha256: 06fd3eeccecf8e3e42c0e33f50356588ea9377b2f7d2642b4d3e0370f4ca7831 -->
<!-- extractor: pdftoppm (poppler 24.02.0) page images at 110-170 dpi, read visually; no OCR available; plain-text reading, layout not preserved -->
<!-- scope (physical page: passages): p1: header, title, abstract, Section 1; p2: Section 1 (end); p3: Section 3 (to Lemma 3); p4: Section 3 (Lemma 3 proof to the Corollary) -->
<!-- note: physical page p is printed page 149+p -->

<!-- pdf-page: 1 -->
Reprinted from JOURNAL OF COMPUTER AND SYSTEM SCIENCES          Vol. 38, No. 1, February 1989
All Rights Reserved by Academic Press, New York and London                 Printed in Belgium

Bounded-Width Polynomial-Size Branching Programs
Recognize Exactly Those Languages in NC^1

DAVID A. BARRINGTON*

Department of Computer and Information Science, University of Massachusetts,
Amherst, Massachusetts 01003

Received August 22, 1986; revised April 7, 1987

We show that any language recognized by an NC^1 circuit (fan-in 2, depth O(log n)) can be
recognized by a width-5 polynomial-size branching program. As any bounded-width
polynomial-size branching program can be simulated by an NC^1 circuit, we have that the
class of languages recognized by such programs is exactly nonuniform NC^1. Further, following
Ruzzo (J. Comput. System Sci. 22 (1981), 365-383) and Cook (Inform. and Control 64 (1985)
2-22), if the branching programs are restricted to be ATIME(log n)-uniform, they recognize
the same languages as do ATIME(log n)-uniform NC^1 circuits, that is, those languages in
ATIME(log n). We also extend the method of proof to investigate the complexity of the word
problem for a fixed permutation group and show that polynomial size circuits of width 4 also
recognize exactly nonuniform NC^1.   (c) 1989 Academic Press, Inc.

1. DEFINITIONS

Let [w] = {1, ..., w}. An instruction is a triple <j, f, g> in which j is the index of an
input variable x_j and f and g are maps from [w] to [w]. The meaning of an instruction
<j, f, g> is "evaluate to f if x_j = 1, otherwise evaluate to g." A width-w branching
program of length l (a w-BP) is a sequence of instructions <j_i, f_i, g_i> for 1 <= i <= l.
Given a 0-1 assignment x to the input variables x_1, ..., x_n, a branching program B yields
the function B(x) which is the composition of the functions produced by each of the
instructions. For example, let w = 2, let e be the identity function on w, and let (1 2) be
the transposition of w's two elements. Then the program consisting of instructions

    <7, (1 2), e> <4, e, (1 2)> <8, (1 2), e>

yields (1 2) if the exclusive OR of x_7, x-bar_4, and x_8 is one and yields e otherwise.
   To recognize a language L subset-of {0, 1}* we need a family of width-w branching
programs <B_n>, where B_n for each positive integer n takes n Boolean inputs.

  * This work is supported by NSF Grant MCS-8304769, by U.S. Air Force Grant AFOSR-82-0326,
and by an NSF Graduate Fellowship.
                                        150
0022-0000/89 $3.00
Copyright (c) 1989 by Academic Press, Inc.
All rights of reproduction in any form reserved.

<!-- pdf-page: 2 -->
                     BOUNDED-WIDTH BRANCHING PROGRAMS                              151

Length and size can then be viewed as functions of n. We say that <B_n> recognizes L if for
each n there is a set F_n of functions from [w], such that for all x in {0, 1}^n, x in L iff
B(x) in F_n.
   B is a permutation branching program (w-PBP) if each f_i and g_i is a permutation of [w].
In general we will use Greek letters for permutations.
   The traditional notion (e.g., in [10]) of a width-w branching program is of a rectangular
w by l array of nodes. Each node in row i is assigned an input variable and two out-edges
leading to nodes in row i + 1. Our model can be viewed this way but further requires that
each node in a column be assigned the same variable. This requirement may be enforced at a
cost of increasing the length polynomially and doubling the width. The traditional notion
also defines the recognition of a set by a branching program in a different way, by fixing a
start node (a source) and partitioning the sink nodes into accepting and rejecting. This
difference may be dealt with in a similar manner. Thus both models define the same class
BWBP of languages recognized by bounded-width polynomial-size branching programs. Our main
result is that BWBP is equal to (nonuniform) NC^1.
   In general we will speak of nonuniform circuits and branching programs, so that an NC^1
circuit will be simply a Boolean circuit with fan-in 2 and depth O(log n) (and hence
polynomial size). Uniformity considerations will be postponed until Section 6, where we will
make the appropriate definitions.

<!-- pdf-page: 3 -->
152                              DAVID A. BARRINGTON
[...]
                              3. THE MAIN RESULT

   We say that a 5-PBP B five-cycle recognizes a set A subset-of [2]^n if there exists a
five-cycle sigma (called the output) in the permutation group S_5 such that B(x) = sigma if
x in A and B(x) = e if x not-in A (e is the identity permutation). For example, using the
usual cycle notation for elements of S_5, the one-instruction program <1, (12345), e>
five-cycle recognizes the set A = {x: x_1 = 1} with output (12345).

   THEOREM 1. Let A be recognized by a depth d fan-in 2 Boolean circuit (we will assume that
the circuit consists of AND and OR gates with a bottom level of inputs and negated inputs).
Then A is five-cycle recognized by a 5-PBP B of length at most 4^d.

   LEMMA 1. If B five-cycle recognizes A with output sigma and tau is any five-cycle, then
there exists a 5-PBP B', of the same length as B, which five-cycle recognizes A with output
tau.

   Proof. Since sigma and tau are both five-cycles there exists some permutation theta with
tau = theta sigma theta^-1. To get B', simply change each instruction of B, replacing each
sigma_i and tau_i by theta sigma_i theta^-1 and theta tau_i theta^-1. [end of proof]

   LEMMA 2. If A can be five-cycle recognized in length l, so can its complement.

   Proof. Let B five-cycle recognize A with output sigma. Call the last instruction of B
<i, mu, nu>. Let B' be identical to B except for last instruction <i, mu sigma^-1,
nu sigma^-1>. Then B'(x) = e if x in A and B'(x) = sigma^-1 if x not-in A. Thus B'
five-cycle recognizes the complement of A. [end of proof]

   LEMMA 3. There are two five-cycles sigma_1 and sigma_2 in S_5 whose commutator is a
five-cycle. (The commutator of a and b is a b a^-1 b^-1.)

<!-- pdf-page: 4 -->
                     BOUNDED-WIDTH BRANCHING PROGRAMS                              153

   Proof. (12345)(13542)(54321)(24531) = (13254). [end of proof]

   EXAMPLE. Consider the 5-PBP

    <1, (12345), e> <2, (13542), e> <1, (54321), e> <2, (24531), e>

which yields (13254) as calculated above if x_1 = x_2 = 1. If either x_1 or x_2 is zero, the
yield is e because of cancellation. So this 5-PBP five-cycle recognizes the set
{x: x_1 = x_2 = 1}. We now generalize this construction to prove our theorem.

   Proof of Theorem 1. Let C be a depth d, fan-in 2 circuit of AND and OR gates, with a
bottom level of inputs and negated inputs. We will show by induction on d that the set
recognized by C can be five-cycle recognized by a 5-PBP. If d = 0, C has no gates and the set
A can easily be recognized by a one-instruction 5-PBP. Assume without loss of generality that
the output gate of C is an AND gate. If it is an OR gate, appeal to Lemma 2. Then the set A
recognized by C is an intersection A_1 cap A_2, where A_1 and A_2 are recognized by circuits
of depth d - 1 and thus are five-cycle recognized by B_1 and B_2 of length at most 4^(d-1).
Let B_1 and B_2 have the particular outputs sigma_1 and sigma_2 as defined in Lemma 3, and
B'_1 and B'_2 have outputs sigma_1^-1 and sigma_2^-1 (this last is possible by Lemma 1). Let B
be the concatenation B_1 B_2 B'_1 B'_2. B yields e unless the input is in both A_1 and A_2,
but yields the commutator of the two outputs if the input is in A. This commutator is a
five-cycle, and so B five-cycle recognizes A. B has length at most 4^d. Given a circuit and a
desired output, this proof gives a deterministic method of constructing the 5-PBP. [end of
proof]

   The following result is a nonuniform version of the well-known result that regular
languages can be recognized by NC^1 circuits. The proof in the uniform case essentially
appears in [30] and is given explicitly in [22].

   THEOREM 2. If A subset-of [2]^n is recognized by a w-BP B of length l, A is recognized by a
fan-in 2 circuit of depth O(log l), where the constant depends on w.

   Proof. Recall our notion of recognition--we say that B accepts x if B(x) is in some
arbitrary subset of the functions from [w] to [w]. We can represent such a function f by w^2
Boolean variables telling whether f(i) = j for each i and j. The composition of two such
functions so represented may be computed by a fixed circuit whose size depends only on w. Our
circuit for A will have a constant-depth section to find the function yielded by a each
instruction of B, a binary tree of composition circuits, and a constant-depth section at the
top to determine acceptance given the function yielded by B. [end of proof]

   COROLLARY. The classes of languages BWBP and nonuniform NC^1 are identical. They equal
the class of languages recognized by polynomial-length 5-PBPs.
