<!-- generated-by: proofmatch local extraction -->
<!-- source-pdf-sha256: 7251cb8e4bc5048cfd6ad113f14bc6d6d3c5a079e5dc33430b1cf36df5c21005 -->
<!-- extractor: pdfminer.six v20260107 -->

<!-- pdf-page: 1 -->
Essential Coding Theory

Venkatesan Guruswami

Atri Rudra1

Madhu Sudan

April 19, 2026

1Department of Computer Science and Engineering, University at Buffalo, SUNY. Work sup­

ported by NSF CAREER grant CCF-0844796.



<!-- pdf-page: 2 -->
2



<!-- pdf-page: 3 -->
Foreword

This book is based on lecture notes from coding theory courses taught by Venkatesan Gu­
ruswami at University at Washington and CMU; by Atri Rudra at University at Buffalo, 
SUNY and by Madhu Sudan at Harvard and MIT.

This version is dated April 19, 2026.  For the latest version, please go to

http://www.cse.buffalo.edu/faculty/atri/courses/coding-theory/book/

The material in this book is supported in part by the National Science Foundation under 
CAREER grant CCF-0844796.  Any opinions, findings and conclusions or recommendations 
expressed in this material are those of the author(s) and do not necessarily reflect the views 
of the National Science Foundation (NSF).

©Venkatesan Guruswami, Atri Rudra, Madhu Sudan, 2019.

This work is licensed under the Creative Commons Attribution-NonCommercial-NoDerivs 
3.0 Unported License.  To view a copy of this license, visit http://creativecommons.org/li­
censes/by-nc-nd/3.0/ or send a letter to Creative Commons, 444 Castro Street, Suite 900, 
Mountain View, California, 94041, USA.

3



<!-- pdf-page: 4 -->
4



<!-- pdf-page: 5 -->
Contents

I  The Basics

1 The Fundamental Question

1.1 Overview . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . .
1.2 Some Definitions and Codes . . . . . . . . . . . . . . . . . . . . . . . . . . .
1.3 Error Correction . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . .
1.4 Distance of a Code . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . .
1.5 Hamming Code . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . .
1.6 Hamming Bound . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . .
1.7 Generalized Hamming Bound . . . . . . . . . . . . . . . . . . . . . . . . . .
1.8 Family of codes . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . .
1.9 Exercises . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . .
1.10 Bibliographic Notes . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . .

2 A Look at Some Nicely Behaved Codes:  Linear Codes

2.1 Groups and Finite Fields . . . . . . . . . . . . . . . . . . . . . . . . . . . . .
. . . . . . . . . . . . . . . . . . . . . .
2.2 Vector Spaces and Linear Subspaces
2.3 Linear Codes and Basic Properties
. . . . . . . . . . . . . . . . . . . . . . .
. . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . .
2.4 Hamming Codes
2.5 Efficient Decoding of Hamming codes . . . . . . . . . . . . . . . . . . . . . .
2.6 Dual of a Linear Code . . . . . . . . . . . . . . . . . . . . . . . . . . . . . .
2.7 Exercises . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . .
2.8 Bibliographic Notes . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . .

3 Probability as Fancy Counting and the q-ary Entropy Function

3.1 A Crash Course on Probability . . . . . . . . . . . . . . . . . . . . . . . . .
3.2 The Probabilistic Method . . . . . . . . . . . . . . . . . . . . . . . . . . . .
3.3 The q-ary Entropy Function . . . . . . . . . . . . . . . . . . . . . . . . . . .
3.4 Exercises . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . .
3.5 Bibliographic Notes . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . .

II  The Combinatorics

5

11

1
1
3
5
10
14
17
19
21
23
25

27
27
30
33
36
37
39
40
48

49
49
56
57
64
65

67



<!-- pdf-page: 6 -->
4 What Can and Cannot Be Done-I

4.1 Asymptotic Version of the Hamming Bound . . . . . . . . . . . . . . . . . .
4.2 Gilbert-Varshamov Bound . . . . . . . . . . . . . . . . . . . . . . . . . . . .
4.3 Singleton Bound . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . .
4.4 Plotkin Bound . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . .
4.5 Exercises . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . .
4.6 Bibliographic Notes . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . .

69
69
70
75
76
84
89

5 The Greatest Code of Them All:  Reed-Solomon Codes

91
91
5.1 Polynomials and Finite Fields . . . . . . . . . . . . . . . . . . . . . . . . . .
97
5.2 Reed-Solomon Codes . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . .
5.3 Maximum Distance Separable Codes and Properties . . . . . . . . . . . . . .
99
5.4 Exercises . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . 101
5.5 Bibliographic Notes . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . 111

III  The Codes

113

6 When Polynomials Save the Day:  Polynomial Based Codes

115
6.1 The generic construction . . . . . . . . . . . . . . . . . . . . . . . . . . . . . 115
6.2 The low degree case
. . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . 117
6.3 The case of the binary field . . . . . . . . . . . . . . . . . . . . . . . . . . . 119
6.4 The general case
. . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . 120
6.5 Exercises . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . 127
6.6 Bibliographic Notes . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . 129

7 From Large to Small Alphabets:  Code Concatenation

131
7.1 Code Concatenation:  The basic idea . . . . . . . . . . . . . . . . . . . . . . 132
7.2 Zyablov Bound . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . 134
7.3 Advanced Concatenation and Strongly Explicit Constructions
. . . . . . . . 136
7.4 Summary of concatenation . . . . . . . . . . . . . . . . . . . . . . . . . . . . 139
7.5 Exercises . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . 140
7.6 Bibliographic Notes . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . 143

IV  The Algorithms

145

8 Efficient Decoding of Reed-Solomon Codes

147
8.1 Unique decoding of Reed-Solomon codes . . . . . . . . . . . . . . . . . . . . 147
8.2 List Decoding Reed-Solomon Codes . . . . . . . . . . . . . . . . . . . . . . . 153
8.3 Extensions . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . 171
8.4 Exercises . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . 173
8.5 Bibliographic Notes . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . 181

6



<!-- pdf-page: 7 -->
A Some Useful Facts

189
A.1 Some Useful Inequalities . . . . . . . . . . . . . . . . . . . . . . . . . . . . . 189
A.2 Some Useful Identities and Bounds . . . . . . . . . . . . . . . . . . . . . . . 191

B Basic Algebraic Algorithms

193
B.1 Executive Summary . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . 193
B.2 Groups, Rings, Fields . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . 193
B.3 Polynomials . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . 194
B.4 Vector Spaces . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . 196
B.5 Finite Fields . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . 199
B.6 Algorithmic aspects of Finite Fields . . . . . . . . . . . . . . . . . . . . . . . 205
B.7 Algorithmic aspects of Polynomials . . . . . . . . . . . . . . . . . . . . . . . 207
B.8 Exercises . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . 213

7



<!-- pdf-page: 8 -->
8



<!-- pdf-page: 9 -->
List of Figures

1.1 Decoding for Akash English, one gets “I need little little (trail)mix.” . . . . .
. . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . .
1.2 Coding process
1.3 Bad example for unique decoding. . . . . . . . . . . . . . . . . . . . . . . . .
Illustration for proof of Hamming Bound . . . . . . . . . . . . . . . . . . . .
1.4

3.1 The q-ary Entropy Function . . . . . . . . . . . . . . . . . . . . . . . . . . .

4.1 The Hamming and Gilbert-Varshamov (GV) bounds for binary codes . . . .
4.2 An illustration of Gilbert’s greedy algorithm for the first five iterations. . . .
4.3 Construction of a new code in the proof of the Singleton bound.
. . . . . . .
4.4 The Hamming, GV and Singleton bound for binary codes.
. . . . . . . . . .
4.5 R vs δ tradeoffs for binary codes
. . . . . . . . . . . . . . . . . . . . . . . .

1
7
14
18

58

71
72
76
77
79

7.1 Concatenated code Cout ◦ Cin.
7.2 The Zyablov bound for binary codes

. . . . . . . . . . . . . . . . . . . . . . . . . . 133
. . . . . . . . . . . . . . . . . . . . . . 135

8.1 A received word in 2-D space
. . . . . . . . . . . . . . . . . . . . . . . . . . 148
8.2 The closest polynomial to a received word . . . . . . . . . . . . . . . . . . . 149
8.3 The tradeoff between rate R and the fraction of errors that can be corrected 

by Algorithm 8.2.1. . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . 158
8.4 A received word in 2-D space for the second Reed-Solomon . . . . . . . . . . 160
8.5 An interpolating polynomial Q(X, Y ) for the received word in Figure 8.4. . . 161
8.6 The two polynomials that need to be output are shown in blue.
. . . . . . . 161
8.7 The tradeoff between rate R and the fraction of errors that can be corrected 

by Algorithm 8.2.1 and Algorithm 8.2.2.

. . . . . . . . . . . . . . . . . . . . 163
8.8 Multiplicity of 1 . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . 164
8.9 Multiplicity of 2 . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . 165
8.10 Multiplicity of 3 . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . 165
8.11 A received word in 2-D space for the third Reed-Solomon . . . . . . . . . . . 166
8.12 An interpolating polynomial Q(X, Y ) for the received word in Figure 8.11.
. 166
. . . . . . . 167
8.13 The five polynomials that need to be output are shown in blue.

9



<!-- pdf-page: 10 -->
10



<!-- pdf-page: 11 -->
Part I

The Basics

11



<!-- pdf-page: 12 -->


<!-- pdf-page: 13 -->
Chapter 1

The Fundamental Question

1.1  Overview

Communication is a fundamental need of our modern lives. In fact, communication is some­
thing that humans have been doing for a long time.  For simplicity, let us restrict ourselves 
to English.  It is quite remarkable that different people speaking English can be understood 
pretty well: even if e.g. the speaker has an accent. This is because English has some built-in 
redundancy, which allows for “errors” to be tolerated.  We will pick an example from one of 
the author’s experiences conversing with his two-year-old son, Akash.  When Akash started 
to speak his own version of English, which we will dub “Akash English,” we got examples 
such as the one illustrated below:

Figure 1.1:  Decoding for Akash English, one gets “I need little little (trail)mix.”

1



<!-- pdf-page: 14 -->
With some practice Akash’s parents were able to “decode” what Akash really meant.  In 
fact, Akash could communicate even if he did not say an entire word properly and gobbled 
up part(s) of word(s).

The above example shows that having redundancy in a language allows for communi­
cation even in the presence of (small amounts of) differences and errors.  Of course, in our 
modern  digital  world,  all  kinds  of  entities  communicate  (and  most  of  the  entities  do  not 
communicate in English, or any natural language for that matter).  Errors are also present 
in the digital world, so these digital communications also use redundancy.

Error-correcting codes (henceforth, just codes) are clever ways of representing data so 
that one can recover the original information even if parts of it are corrupted.  The basic 
idea is to judiciously introduce redundancy so that the original information can be recovered 
even when parts of the (redundant) data have been corrupted.

For example, when packets are transmitted over the Internet, some of the packets get 
corrupted  or  dropped.  Packet  drops  are  resolved  by  the  TCP  layer  by  a  combination  of 
sequence numbers and ACKs.  To deal with data corruption, the TCP/IP protocol uses a 
form of error correction called CRC Checksum [58].  From a theoretical point of view, the 
checksum is a terrible code since it does not have good error correction properties (for that 
matter so is English).  However, on the Internet, the current dominant mode of operation is 
to detect errors and if errors have occurred, then ask for retransmission.  This is the reason 
why the use of checksum has been hugely successful in the Internet. However, there are other 
communication applications where re-transmission is not an option.  Codes are used when 
transmitting data over the telephone line or via cell phones.  They are also used in deep 
space communication and in satellite broadcast (for example, TV signals are transmitted via 
satellite).  Indeed, asking the Mars Rover to re-send an image just because it got corrupted 
during transmission is not an option–this is the reason that for such applications, the codes 
used have always been very sophisticated.

Codes also have applications in areas not directly related to communication.  In particu­
lar, in the applications above, we want to communicate over space.  Codes can also be used 
to communicate over time.  For example, codes are used heavily in data storage.  CDs and 
DVDs work fine even in presence of scratches precisely because they use codes.  Codes are 
used in Redundant Array of Inexpensive Disks (RAID) [13] and error correcting memory [12]. 
Sometimes, in the Blue Screen of Death displayed by Microsoft Windows family of operating 
systems, you might see a line saying something along the lines of “parity check failed”–this 
happens when the code used in the error-correcting memory cannot recover from error(s). 
Also,  certain consumers of memory,  e.g.  banks,  do not want to suffer from even one bit 
flipping (this e.g.  could mean someone’s bank balance either got halved or doubled–neither 
of which are welcome1).  Codes are also deployed in other applications such as paper bar 
codes;  for example, the bar code used by UPS called MaxiCode [11].  Unlike the Internet 
example, in all of these applications, there is no scope for “re-transmission.”

In  this  book,  we  will  mainly  think  of  codes  in  the  communication  scenario.  In  this 

1This is a bit tongue-in-cheek:  in real life banks have more mechanisms to prevent one-bit flip from 

wreaking havoc.

2



<!-- pdf-page: 15 -->
framework, there is a sender who wants to send (say) k message symbols over a noisy channel. 
The sender first encodes the k message symbols into n symbols (called a codeword) and then 
sends it over the channel.  The receiver gets a received word consisting of n symbols.  The 
receiver then tries to decode and recover the original k message symbols.  Thus, encoding is 
the process of adding redundancy and decoding is the process of removing errors.

Unless mentioned otherwise, in this book we will make the following assumption: 

Note

The sender and the receiver only communicate via the channel.a In other words, other 
than some setup information about the code, the sender and the receiver do not have 
any other information exchange (other than of course what was transmitted over the 
channel).  In particular, no message is more likely to be transmitted over another.

aThe scenario where the sender and receiver have a “side-channel” is an interesting topic that has 

been studied but is outside the scope of this book.

The fundamental question that will occupy our attention for almost the entire book is 
the tradeoff between the amount of redundancy used and the number of errors that can be 
corrected by a code.  In particular, we would like to understand:

Comment out 4 lines below for tagging check

Question  1.1.1   (Main  Question). How  much  redundancy  do  we  need  to  correct  a  given 
amount of errors?  (We would like to correct as many errors as possible with as little redun­
dancy as possible.)

Note  that  maximizing  error  correction  and  minimizing  redundancy  are  contradictory 
goals:  a code with higher redundancy should be able to tolerate a greater number of errors. 
By the end of this chapter, we will see a formalization of this question.

Once we determine the optimal tradeoff, we will be interested in achieving this optimal 
tradeoff  with  codes  that  come  equipped  with  efficient encoding  and  decoding.  (A  DVD 
player that tells its consumer that it will recover from a scratch on a DVD by tomorrow 
is  not  exactly  going  to  be  a  best-seller.)  In  this  book,  we  will  primarily  define  efficient 
algorithms to be ones that run in polynomial time.2

1.2  Some Definitions and Codes

To formalize Question 1.1.1, we begin with the definition of a code.
Definition 1.2.1  (Code). A code of  block length n over an alphabet Σ is a subset of Σn. 
Typically, we will use q to denote the alphabet size |Σ|.3

2Readers unfamiliar with runtime analysis are referred to Appendix ??.  Coming back to the claim on 
efficiency– we are not claiming that this is the correct notion of efficiency in practice.  However, we believe 
that it is a good definition as the “first cut”– quadratic or cubic time algorithms are definitely more desirable 
than exponential time algorithms:  see Section ?? for more on this.

3Note that q need not be a constant and can depend on n: we’ll see codes in this book where this is true.

3



<!-- pdf-page: 16 -->
Remark 1.2.2. We note that the ambient space Σn can be viewed as a set of sequences, 
vectors or functions.  In other words, we can think of a vector (v1, . . . , vn) ∈ Σn as just the 
sequence v1, . . . , vn (in order) or a vector tuple (v1, . . . , vn) or as the function f : [n] → Σ
such that f (i) = vi.  Sequences assume least structure on Σ and hence are most generic. 
Vectors  work  well  when  Σ  has  some  structure  (and  in  particular  is  what  is  known  as  a 
field, which we will see next chapter).  Functional representation will be convenient when the 
set of coordinates has structure (e.g., [n] may come from a finite field of size n).  For now, 
however, the exact representation does not matter and the reader can work with representation 
as sequences.

We will also frequently use the following alternate way of looking at a code.  Given a 

code C ⊆ Σn, with |C| = M , we will think of C as a mapping of the following form:

C : [M ] → Σn.

(1.1)

In the above equation (1.1), we have used the notation [M ] for any integer M ≥ 1 to denote 
the set {1, 2, . . . , M }.

We will also need the notion of dimension of a code.

Definition 1.2.3  (Dimension of a code). Given a code C ⊆ Σn, its dimension is given by

k def= logq |C|.

Let us begin by looking at two specific codes.  Both codes are defined over Σ = {0, 1}
(also known as binary codes).  In both cases |C| = 24 and we will think of each of the 16
messages as a 4 bit vector.

We first look at the so-called parity code, which we will denote by C⊕.  Given a message 

(x1, x2, x3, x4) ∈ {0, 1}4, its corresponding codeword is given by

C⊕(x1, x2, x3, x4) = (x1, x2, x3, x4, x1 ⊕ x2 ⊕ x3 ⊕ x4),

(1.2)

where the ⊕ denotes the XOR (also known as the EXOR or Exclusive-OR) operator. In other 
words, the parity code appends the parity of the message bits (or takes the remainder of the 
sum of the message bits when divided by 2) at the end of the message.  For example, the 
message (1, 0, 0, 1) will have a 0 appended at the end while (1, 0, 0, 0) will have a 1 appended 
at the end.  Note that such a code uses the minimum amount of non-zero redundancy.

The second code we will look at is the so-called repetition code.  This is a very natural 
code (and perhaps the first code one might think of). The idea is to repeat every message bit 
a fixed number of times.  For example, we repeat each of the 4 message bits 3 times and we 
use C3,rep to denote this code.  Given a message (x1, x2, x3, x4) ∈ {0, 1}4, its corresponding 
codeword is given by

C3,rep(x1, x2, x3, x4) = (x1, x1, x1, x2, x2, x2, x3, x3, x3, x4, x4, x4).

(1.3)

4



<!-- pdf-page: 17 -->
Let us now try to look at the tradeoff between the amount of redundancy and the number 
of errors each of these codes can correct.  Even before we begin to answer the question, we 
need to define how we are going to measure the amount of redundancy.  One natural way 
to define redundancy for a code with dimension k and block length n is by their difference 
n − k.  By this definition, the parity code uses the least amount of redundancy.  However, 
one “pitfall” of such a definition is that it does not distinguish between a code with k = 100
and n = 102 and another code with dimension and block length 2 and 4, respectively.  The 
first  code  uses  0.02  bits  of  redundancy  per  message  bit  while  the  second  code  uses  1  bit 
of redundancy per message bit.  Thus, in the relative sense, the latter code is using more 
redundancy.  This motivates the following notion of measuring redundancy.

Definition 1.2.4  (Rate of a code). The rate of a code with dimension k and block length n
is given by

R def=

k
n

.

Note that the higher the rate, the lesser the amount of redundancy in the code.  Thus, 
when constructing or analyzing codes, we will be interested in lower bounding the rate of a 
code.  (Occasionally we will also be sloppy and say that a code “has rate R” when we really 
mean it “has rate at least R.”)  Also note that as k ≤ n,4

R ≤ 1.

In other words, the rate of a code is the average amount of real information in each of the 
n symbols transmitted over the channel.  So, in some sense, rate captures the complement 
of redundancy.  However, for historical reasons, we will deal with the rate R (instead of the 
more natural 1 − R) as our notion of redundancy.  Given the above definition, C⊕ and C3,rep
have rates of  4
3.  As expected, the parity code has a higher rate than the repetition 
code.

5 and  1

We  have  formalized  the  notion  of  redundancy  as  the  rate  of  a  code  as  well  as  other 
parameters of a code.  However, to formalize Question 1.1.1, we still need to formally define 
what it means to correct errors.  We do so next.

1.3  Error Correction

Before we formally define error correction, we will first formally define the notion of encoding.

Definition 1.3.1  (Encoding function). Let C ⊆ Σn.  An equivalent description of the code 
C is an injective mapping E : [|C|] → Σn called the encoding function.

Next  we  move  to  error  correction.  Informally,  we  can  correct  a  received  word  if  we 
can recover the  transmitted codeword (or  equivalently the  corresponding message).  This 
“reverse” process is called decoding.

4Further, in this book, we will always consider the case k > 0 and n < ∞ and hence, we can also assume 

that R > 0.

5



<!-- pdf-page: 18 -->
Definition 1.3.2  (Decoding function). Let C ⊆ Σn be a code.  A mapping D : Σn → [|C|]
is called a decoding function for C.

The definition of a decoding function by itself does not give anything interesting. What we 
really need from a decoding function is for the function to recover the transmitted message. 
To understand this notion, we first need to understand the nature of errors that we aim to 
tackle. In particular, if a transmitter transmits u ∈ Σn and the receiver receives v ∈ Σn, how 
do we quantify the amount of “error” that has happened during this transmission?  While 
multiple notions are possible, the most central one, and the one we will focus on for most 
of this book, is based on “Hamming distance,” a notion of distance that captures how close 
are two given sequences u and v.

Definition 1.3.3  (Hamming distance). Given two vectors u, v ∈ Σn the Hamming distance 
between u and v, denoted by ∆(u, v),  is the number of positions in which u and v differ. 
We also define the relative Hamming distance, denoted δ(u, v), to be the quantity δ(u, v) =
1
n∆(u, v).

Note that the relative Hamming distance normalizes the distance so that δ(u, v) always 
lies in the interval [0, 1] (for every n, Σ and strings u, v ∈ Σn).  This normalization will be 
useful when we study the asymptotic behavior of encoding and decoding functions, i.e., as 
n → ∞.  For now, though we will focus mostly on the (non-relative) Hamming distance.

The Hamming distance is a distance in a very formal mathematical sense: see Exercise 1.5. 
Note that the definition of Hamming distance depends only on the number of differences and 
not the nature of the difference. For example, consider the vectors u = 00000 and v = 10001. 
One can see that their Hamming distance is ∆(u, v) = 2. Now consider the vector w = 01010. 
Note that even though v ̸= w, we again have a Hamming distance ∆(u, w) = 2.

To return to the quantification of errors, from now on we will say that if u is transmitted 
and v is received then ∆(u, v) errors occurred during transmission. This allows us to quantify 
the performance of an encoding/decoding function, or equivalently the underlying code as 
we do next.

Definition 1.3.4  (t-Error Channel). An n-symbol t-Error Channel over the alphabet Σ is a 
function Ch : Σn → Σn that satisfies ∆(v, Ch(v)) ≤ t for every v ∈ Σn.

Definition 1.3.5  (Error Correcting Code). Let C ⊆ Σn be a code and let t ≥ 1 be an integer. 
C is said to be a t-error-correcting code if there exists a decoding function D such that for 
every message m ∈ [|C|] and every t-error channel Ch we have D (Ch(C(m))) = m.

Thus, a t-error-correcting code is one where there is a decoding function that corrects 
any  pattern  of  t  errors.  For  example,  consider  the  case  when  the  codeword  (0, 0, 0, 0)  is 
transmitted.  Then a 1-error-correcting code (over the alphabet {0, 1}) should be able to 
decode from any of the following received words:

(0, 0, 0, 0), (1, 0, 0, 0), (0, 1, 0, 0), (0, 0, 1, 0), (0, 0, 0, 1).

Figure 1.2 illustrates how the definitions we have examined so far interact.
We will also very briefly look at a weaker form of error recovery called error detection.

6



<!-- pdf-page: 19 -->
m ↦→ C(m)

v = Ch (C(m)) ↦→ m

Channel Ch

Encoding function

Decoding function

Figure 1.2:  Coding process

Definition 1.3.6  (Error detection code). Let C ⊆ Σn be a code and let t ≥ 1 be an integer. 
C is said to be a t-error-detecting code if there exists a detecting procedure D such that for 
every message m and every received vector v ∈ Σn satisfying ∆(C(m), v) ≤ t, it holds that 
D outputs a 1 if v = C(m) and 0 otherwise.  In other words

D(v) =

{︄
1
0

 if v = C(m)
 otherwise

.

Thus, a t-error-detecting code is one where if the transmission has at least one error and 
at most t errors, then the decoding function detects the error (by outputting 0).  Note that 
a t-error correcting code is also a t-error detecting code (but not necessarily the other way 
round):  see Exercise 1.1.  Although error detection might seem like a weak error recovery 
model, it is useful in settings where the receiver can ask the sender to re-send the message. 
For example, error detection is used quite heavily in the Internet.

Finally, we also consider a more benign model of errors referred to as “erasures,” where 
a  symbol  is  merely  (and  explicitly)  omitted  from  the  transmission  (as  opposed  to  being 
replaced by some other symbol).  More specifically, if a symbols is erased, then it is replaced 
by a special symbol “?” that is not a member of the alphabet Σ.  For example, if (0, 0, 0, 0)
was transmitted and the second symbols was erased by the channel, then the vector (0, ?, 0, 0)
will be received.

Definition 1.3.7  (t-Erasure Channel). An n-symbol t-Erasure Channel over the alphabet Σ
is a function Ch : Σn → (Σ ∪ {?})n that satisfies ∆(v, Ch(v)) ≤ t for every v ∈ Σn (where 
both arguments to ∆(·, ·) are viewed as elements of (Σ ∪ {?})n) and for every i ∈ [n] such 
that vi ̸= Ch(v)i we have Ch(v)i =?.

A coordinate i such that Ch(v)i =? is called an erasure.  We may now define erasure 

correcting codes analogously to error-correcting codes.

Definition  1.3.8   (Erasure  Correcting  Code).  Let  C ⊆ Σn  be  a  code  and  let  t ≥ 1  be 
an integer.  C is said to be a t-erasure-correcting code  if there exists a decoding function 
D  such  that  for  every  message  m ∈ [|C|]  and  for  every  t-erasure  channel  Ch  we  have 
D (Ch(C(m))) = m.

With the above definitions in place,  we are now ready to look at the error correcting 

capabilities of the codes we looked at in the previous section.

7



<!-- pdf-page: 20 -->
1.3.1  Error-Correcting Capabilities of Parity and Repetition Codes

In Section 1.2, we looked at examples of parity code and repetition code with the following 
properties:

C⊕ : q = 2, k = 4, n = 5, R = 4/5.
C3,rep : q = 2, k = 4, n = 12, R = 1/3.

We will start with the repetition code.  To study its error-correcting capabilities, we will 
consider the following natural decoding function.  Given a received word y ∈ {0, 1}12 (where 
recall the transmitted codeword is of the form (x1, x1, x1, x2, x2, x2, x3, x3, x3, x4, x4, x4) for 
some (x1, x2, x3, x4) ∈ {0, 1}4), divide it up into four consecutive blocks (y1, y2, y3, y4) where 
every block consists of three bits.  Then, for every block yi (1 ≤ i ≤ 4), output the majority 
bit as the message bit.  We claim this decoding function can correct any error pattern with 
at most 1 error (see Exercise 1.2.)  For example, if a block of 010 is received, since there 
are two 0’s we know the original message bit was 0.  In other words, we have argued the 
following error correcting capability of C3,rep:

Proposition 1.3.9. C3,rep is a 1-error correcting code.

However, it is not too hard to see that C3,rep cannot correct two errors.  For example, if 
both of the errors happen in the same block and a block in the received word is 010, then 
the original block in the codeword could have been either 111 or 000. Therefore in this case, 
no decoder can successfully recover the transmitted message.5

Thus,  we  have  pin-pointed  the  error-correcting  capabilities  of  the  C3,rep  code:  it  can 
correct one error, but not two or more.  However, note that the argument assumed that the 
error positions can be located arbitrarily.  In other words, we are assuming that the channel 
noise behaves arbitrarily (subject to a bound on the total number of errors).  However, we 
can model the noise differently.  We now briefly digress to look at this issue in slightly more 
detail.

Digression: Channel Noise.  As was mentioned above, until now we have been assuming 
the following noise model, which was first studied by Hamming:

Any error pattern can occur during transmission as long as the total number of 
errors is bounded.  Note that this means that the location as well as the nature6 
of the errors is arbitrary.

We will frequently refer to Hamming’s model as the Adversarial Noise Model. It is important 
to note that the atomic unit of error is a symbol from the alphabet. For example, if the error 
pattern7 is (1, 0, 1, 0, 0, 0) and we consider the alphabet to be {0, 1}, then the pattern has two 

5Recall we are assuming that the decoder has no side information about the transmitted message.
6For binary codes, there is only one kind of error:  a bit flip.  However, for codes over a larger alphabet, 
say {0, 1, 2}, 0 being converted to a 1 and 0 being converted into a 2 are both errors, but are different kinds 
of errors.

7If v is transmitted and Ch(v) is received then the ‘difference’ between Ch(v) and v is the error pattern. 

For binary alphabet the difference is the XOR operator.

8



<!-- pdf-page: 21 -->
errors (since the first and the third locations in the vector have a non-zero value, i.e. value of 
1). However, if our alphabet is {0, 1}3 (i.e. we think of the vector above as ((1, 0, 1), (0, 0, 0)), 
with (0, 0, 0) corresponding to the zero element in {0, 1}3), then the pattern has only one 
error.  Thus, by increasing the alphabet size we can also change the adversarial noise model. 
As the book progresses, we will see how error correction over a larger alphabet is easier than 
error correction over a smaller alphabet.

However, the above is not the only way to model noise.  For example, we could also have 

following error model:

No more than 1 error can happen in any contiguous three-bit block.

First  note  that,  for  the  error  model  above,  no  more  than  four  errors  can  occur  when  a 
codeword in C3,rep is transmitted.  (Recall that in C3,rep, each of the four bits is repeated 
three times.)  Second, note that the decoding function that takes the majority vote of each 
block  can  successfully  recover  the  transmitted  codeword  for  any  error  pattern,  while  in 
the worst-case noise model it could only correct at most one error.  This channel model is 
admittedly contrived, but it illustrates the point that the error-correcting capabilities of a 
code (and a decoding function) are crucially dependent on the noise model.

A  popular  alternate  noise  model  is  to  model  the  channel  as  a  stochastic  process.  As 
a  concrete  example,  let  us  briefly  mention  the  binary  symmetric  channel  with  crossover 
probability 0 ≤ p ≤ 1, denoted by BSCp, which was first studied by Shannon.  In this model, 
when a (binary) codeword is transferred through the channel, every bit flips independently 
with probability p.

Note that the two noise models proposed by Hamming and Shannon are in some sense 
two  extremes:  Hamming’s  model  assumes  no  knowledge  about  the  channel  (except  that 
a  bound  on  the  total  number  of  errors  is  known8  while  Shannon’s  noise  model  assumes 
complete knowledge about how noise is produced.  In this book, we will consider only these 
two extreme noise models.  In real life, the situation often is somewhere in between.

For real life applications, modeling the noise model correctly is an extremely important 
task, as we can tailor our codes to the noise model at hand. However, in this book we will not 
study this aspect of designing codes at all, and will instead mostly consider the worst-case 
noise model.  Informally, if one can communicate over the worst-case noise model, then one 
could use the same code to communicate over nearly every other noise model with the same 
amount of noise.

We now return to C⊕ and examine its error-correcting capabilities in the worst-case noise 
model.  We claim that C⊕ cannot correct even one error.  Suppose y = 10000 is the received 
word. Then we know that an error has occurred, but we do not know which bit was flipped. 
This is because the two codewords u = 00000 and v = 10001 differ from the received word y
in exactly one bit.  As we are assuming that the receiver has no side information about the 
transmitted codeword, no decoder can know what the transmitted codeword was.

8A bound on the total number of errors is necessary; otherwise, error correction would be impossible: 

see Exercise 1.3.

9



<!-- pdf-page: 22 -->
Thus, from an error-correction point of view, C⊕ is a terrible code (as it cannot correct 
even  1  error).  However,  we  will  now  see  that  C⊕  can  detect  one  error.  Consider  Algo­
rithm 1.3.1.

Algorithm 1.3.1 Error Detector for Parity Code
Input: Received word y = (y1, y2, y3, y4, y5)
Output: 1 if y ∈ C⊕ and 0 otherwise

1: b ← y1 ⊕ y2 ⊕ y3 ⊕ y4 ⊕ y5
2: return 1 ⊕ b ▷ If there is no error, then b = 0 and hence we need to “flip” the bit for 

the answer

Note that when no error has occurred during transmission, yi = xi for 1 ≤ i ≤ 4 and 
y5 = x1 ⊕ x2 ⊕ x3 ⊕ x4, in which case b = 0 and we output 1 ⊕ 0 = 1 as required. If there is a 
single error then either yi = xi ⊕ 1 (for exactly one 1 ≤ i ≤ 4) or y5 = x1 ⊕ x2 ⊕ x3 ⊕ x4 ⊕ 1. 
It can be check that in this case, b = 1.  In fact, one can extend this argument to obtain the 
following result (see Exercise 1.4).

Proposition 1.3.10. The parity code C⊕ can detect an odd number of errors.

Let us now revisit the example that showed that one cannot correct one error using C⊕. 
Recall, we considered two codewords in C⊕, u = 00000 and v = 10001 (which are codewords 
corresponding  to  messages  0000  and  1000,  respectively).  Now  consider  the  scenarios  in 
which u and v are each transmitted and a single error occurs resulting in the received word 
r = 10000.  Thus, given the received word r and the fact that at most one error can occur, 
the  decoder  has  no  way  of  knowing  whether  the  original  transmitted  codeword  was  u  or 
v.  Looking back at the example, it is clear that the decoder is “confused” because the two 
codewords u and v do not differ in many positions.  This notion is formalized in the next 
section.

1.4  Distance of a Code

We now turn to a new parameter associated with a code that we call the minimum distance 
of a code.  As we will see later,  minimum distance is connected to the other parameters, 
including the error-correction and error-detection capacity of the code.  However, due to the 
cleanliness of the definition, it will often be the first of the parameters we will explore when 
studying a new error-correcting code.

Definition  1.4.1   (Minimum  distance).  Let  C ⊆ Σn.  The  minimum  distance  (or  just
distance) of C, denoted ∆(C), is defined to be

∆(C) = min

c1̸=c2∈C

∆(c1, c2).

10



<!-- pdf-page: 23 -->
We also define the relative minimum distance of C to be δ(C), is defined to be

δ(C) = min

c1̸=c2∈C

δ(c1, c2).

In other words, ∆(C) is the minimum distance between two distinct codewords in C. We 
note that the repetition code C3,rep has distance 3 (recall (1.3)).  Indeed, any two distinct 
messages will differ in at least one of the message bits.  After encoding, the difference in one 
message bit will translate into a difference of three bits in the corresponding codewords. For 
example

C3,rep(0, 0, 0, 0) = (0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0) and C3,rep(1, 0, 0, 0) = (1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0).

We now claim that the distance of C⊕ is 2. This is a consequence of the following observa­
tions.  If two messages m1 and m2 differ in at least two places then ∆(C⊕(m1), C⊕(m2)) ≥ 2
(even if we just ignored the parity bits). If two messages differ in exactly one place then the 
parity bits in the corresponding codewords are different, which implies a Hamming distance 
of 2 between the codewords.  For example,

C⊕(1, 0, 0, 0) = (1, 0, 0, 0, 1) and C⊕(1, 0, 0, 1) = (1, 0, 0, 1, 0).

Thus, C⊕ has a smaller distance than C3,rep and can correct less number of errors than C3,rep. 
This suggests that a larger distance implies greater error-correcting capabilities.  The next 
result formalizes this intuition.  As we will see, minimum distance exactly captures both the 
ability to recover from errors as also the notion of erasures (Definition 1.3.8).

Proposition 1.4.2. Given a code C, the following are equivalent:

1. C has minimum distance d ≥ 2,

2. If d is odd, C can correct (d − 1)/2 errors.

3. C can detect d − 1 errors.

4. C can correct d − 1 erasures.

Remark 1.4.3. Property (2) above for even d is slightly different.  In this case,  one can 
correct up to  d

2 − 1 errors but cannot correct  d

2  errors.  (See Exercise 1.6.)

Before we prove Proposition 1.4.2, let us apply it to the codes C⊕ and C3,rep which have 
distances of 2 and 3, respectively.  Proposition 1.4.2 implies the following facts that we have 
already proved:

• C3,rep can correct 1 error (Proposition 1.3.9).

• C⊕ can detect 1 error but cannot correct 1 error (Proposition 1.3.10).

11



<!-- pdf-page: 24 -->
The  proof  of  Proposition  1.4.2  will  need  the  following  decoding  function.  Maximum 
likelihood decoding (MLD) is a well-studied decoding method for error correcting codes. The 
MLD function outputs the codeword c ∈ C,  which is as close as possible to the received 
word in Hamming distance (with ties broken arbitrarily).9 More formally, the MLD function 
denoted by DM LD : Σn → C is defined as follows.  For every y ∈ Σn,

DM LD(y) = arg min
c∈C

∆(c, y).

Algorithm 1.4.1 is a naive implementation of the MLD.

Algorithm 1.4.1 Naive Maximum Likelihood Decoder
Input: Received word y ∈ Σn
Output: DM LD(y)

1: Pick an arbitrary c ∈ C and assign z ← c
2: for every c′ ∈ C such that c ̸= c′ do
if ∆(c′, y) < ∆(z, y) then
3:  
4:  
5: return z

z ← c′

Proof  of  Proposition  1.4.2  We  will  complete  the  proof  in  two  steps.  First,  we  will 
show  that  if  property  1  is  satisfied  then  so  are  properties  2,  3  and  4  (we  prove  this  via 
three implications (1) implies (2), (1) implies (3) and (1) implies (4)).  Then we show that 
if  property  1  is  not  satisfied  then  none  of  the  properties  2,  3  or  4  hold  (again  via  the 
corresponding three implications).

Item 1. implies 2.  Assume C has distance d.  We first prove 2 (for this case assume that 
d = 2t + 1).  We now need to show that there exists a decoding function such that for all 
error patterns with at most t errors it always outputs the transmitted message.  We claim 
that the MLD function has this property. Assume this is not so and let c1 be the transmitted 
codeword and let y be the received word.  Note that

∆(y, c1) ≤ t.

(1.4)

As  we  have  assumed  that  MLD  does  not  work,  DM LD(y) = c2 ̸= c1.  Note  that  by  the 
definition of MLD,

∆(y, c2) ≤ ∆(y, c1).

(1.5)

9Technically, as per Definition 1.3.2, a decoder should output a message while MLD outputs a codeword. 
However,  since  we  only  consider  code  of  distance  at  least  one  in  this  book,  there  is  a  bijection  between 
codewords and message so this syntatic difference does not matter.

12



<!-- pdf-page: 25 -->
Consider the following set of inequalities:

∆(c1, c2) ≤ ∆(c2, y) + ∆(c1, y)
≤ 2∆(c1, y)
≤ 2t
= d − 1,

(1.6)
(1.7)
(1.8)
(1.9)

where (1.6) follows from the triangle inequality (see Exercise 1.5), (1.7) follows from (1.5) 
and (1.8) follows from (1.4).  (1.9) implies that the distance of C is at most d − 1, which is 
a contradiction.

Item  1.  implies  3.  We now show that property 3 holds.  That is,  we need to describe 
an algorithm that can successfully detect whether errors have occurred during transmission 
(as long as the total number of errors is bounded by d − 1).  Consider the following error 
detection algorithm:  check if the received word y = c for some c ∈ C (this can be done via 
an exhaustive check).  If no errors occurred during transmission, y = c1, where c1 was the 
transmitted codeword and the algorithm above will accept (as it should). On the other hand 
if 1 ≤ ∆(y, c1) ≤ d − 1, then by the fact that the distance of C is d, y ̸∈ C and hence the 
algorithm rejects, as required.

Item 1. implies 4.  Finally, we prove that property 4 holds.  Let y ∈ (Σ ∪ {?})n be the 
received word.  First we claim that there is a unique c = (c1, . . . , cn) ∈ C that agrees with y
(i.e.  yi = ci for every i such that yi ̸= ?).  Indeed, for the sake of contradiction, assume that 
this is not true, i.e.  there exists two distinct codewords c1, c2 ∈ C such that both c1 and c2
agree with y in the unerased positions.  Note that this implies that c1 and c2 agree in the 
positions i such that yi ̸= ?.  Thus, ∆(c1, c2) ≤ |{i|yi = ?}| ≤ d − 1, which contradicts the 
assumption that C has distance d.

Given the uniqueness of the codeword c ∈ C that agrees with y in the unerased position, 
an algorithm to find c is as follows: go through all the codewords in C and output the desired 
codeword.

Item ¬1. implies ¬2.  For the other direction of the proof, assume that property 1 does 
not hold, that is, C has distance d − 1.  We now show that property 2 cannot hold:  i.e., for 
every decoding function there exists a transmitted codeword c1 and a received word y (where 
∆(y, c1) ≤ (d − 1)/2) such that the decoding function cannot output c1.  Let c1 ̸= c2 ∈ C
be codewords such that ∆(c1, c2) = d − 1 (such a pair exists as C has distance d − 1).  Now 
consider a vector y such that ∆(y, c1) = ∆(y, c2) = (d − 1)/2.  Such a y exists as d is odd 
and by the choice of c1 and c2.  Figure 1.3 gives an illustration of such a y (matching color 
implies that the vectors agree on those positions).

Now, since y could have been generated if either of c1 or c2 were the transmitted code­

word, no decoding function can work in this case.10

10Note that this argument is just a generalization of the argument that C⊕ cannot correct 1 error.

13



<!-- pdf-page: 26 -->
Figure 1.3:  Bad example for unique decoding.

Item ¬1. implies ¬3.  For the remainder of the proof, assume that the transmitted word 
is c1 and there exists another codeword c2 such that ∆(c2, c1) = d − 1.  To see why property 
3 is not true, let y = c2.  In this case, either the error detecting algorithm detects no error, 
or it declares an error when c2 is the transmitted codeword and no error takes place during 
transmission.

Item  ¬1.  implies  ¬4.  We  finally  argue  that  property  4  does  not  hold.  Let  y  be  the 
received word in which the positions that are erased are exactly those where c1 and c2 differ. 
Thus, given y both c1 and c2 could have been the transmitted codeword, and no algorithm 
■
for correcting (at most d − 1) erasures can work in this case. 

Proposition 1.4.2 implies that Question 1.1.1 can be reframed as

Question 1.4.4   (Main question:  reframed). What is the largest rate R that a code with 
distance d can have?

We  have  seen  that  the  repetition  code  C3,rep  has  distance  3  and  rate  1/3.  A  natural 

follow-up question (which is a special case of Question 1.4.4) is to ask

Question 1.4.5  (Special case of Question 1.4.4). Can we have a code with distance 3 and 
rate R > 1
3?

1.5  Hamming Code

With the above question in mind, let us consider the so-called Hamming code, which we will 
denote by CH. Given a message (x1, x2, x3, x4) ∈ {0, 1}4, its corresponding codeword is given 

14

d−12n−d+1c1c2yd−12Figure1.3:Badexampleforuniquedecoding.¬1.implies¬3.Fortheremainderoftheproof,assumethatthetransmittedwordisc1andthereexistsanothercodewordc2suchthat∆(c2,c1)=d−1.Toseewhyproperty3isnottrue,lety=c2.Inthiscase,eithertheerrordetectingalgorithmdetectsnoerror,oritdeclaresanerrorwhenc2isthetransmittedcodewordandnoerrortakesplaceduringtransmission.¬1.implies¬4.Weﬁnallyarguethatproperty4doesnothold.Letybethereceivedwordinwhichthepositionsthatareerasedareexactlythosewherec1andc2differ.Thus,givenybothc1andc2couldhavebeenthetransmittedcodeword,andnoalgorithmforcorrecting(atmostd−1)erasurescanworkinthiscase.■Proposition1.4.2impliesthatQuestion1.1.1canbereframedasQuestion1.4.1.WhatisthelargestrateRthatacodewithdistancedcanhave?WehaveseenthattherepetitioncodeC3,rephasdistance3andrate1/3.Anaturalfollow-upquestion(whichisaspecialcaseofQuestion1.4.1)istoaskQuestion1.4.2.Canwehaveacodewithdistance3andrateR>13?34

<!-- pdf-page: 27 -->
by

CH(x1, x2, x3, x4) = (x1, x2, x3, x4, x2 ⊕ x3 ⊕ x4, x1 ⊕ x3 ⊕ x4, x1 ⊕ x2 ⊕ x4).

It can be verified that this code has the following parameters:

CH : q = 2, k = 4, n = 7, R = 4/7.

We will show shortly that CH has a distance of 3.  We would like to point out that we 
could have picked the three parities differently.  The reason we mention the three particular 
parities above is due to historical reasons.  We leave it as an exercise to define an alternate 
set of parities such that the resulting code still has a distance of 3:  see Exercise 1.9.

Before we move on to determining the distance of CH, we will need another definition.

Definition 1.5.1  (Hamming Weight). Let q ≥ 2.  Given any vector v ∈ {0, 1, 2, . . . , q − 1}n, 
its Hamming weight, denoted by wt(v) is the number of non-zero symbols in v.

For example, if v = 01203400, then wt(v) = 4.
We now look at the distance of CH.

Proposition 1.5.2. CH has a distance of 3.

Proof.  We will prove the claimed distance by using two properties of CH:

and

min
c∈CH ,c̸=0

wt(c) = 3,

min
c∈CH ,c̸=0

wt(c) = min

c1̸=c2∈CH

∆(c1, c2)

(1.10)

(1.11)

The proof of (1.10) follows from a case analysis on the Hamming weight of the message bits. 
Let us use x = (x1, x2, x3, x4) to denote the message vector.

• Case 0:  If wt(x) = 0, then CH(x) = 0, which means we do not have to consider this 

codeword.

• Case 1:  If wt(x) = 1 then at least two parity check bits in (x2 ⊕ x3 ⊕ x4, x1 ⊕ x3 ⊕

x4, x1 ⊕ x2 ⊕ x4) are 1 (see Exercise 1.10).  So in this case, wt(CH(x)) ≥ 3.

• Case 2:  If wt(x) = 2 then at least one parity check bit in (x2 ⊕ x3 ⊕ x4, x1 ⊕ x3 ⊕

x4, x1 ⊕ x2 ⊕ x4) is 1 (see Exercise 1.11).  So in this case, wt(CH(x)) ≥ 3.

• Case 3:  If wt(x) ≥ 3 then those message bits themselves imply that wt(CH(x)) ≥ 3.

Thus,  we can conclude that  min

wt(c) ≥ 3.  Further,  note that wt(CH(1, 0, 0, 0)) = 3, 

c∈CH ,c̸=0

which implies that  min

wt(c) ≤ 3. This along with the lower bound that we just obtained 

c∈CH ,c̸=0

proves (1.10).

15



<!-- pdf-page: 28 -->
We now turn to the proof of (1.11).  For the rest of the proof, let x = (x1, x2, x3, x4) and 
y = (y1, y2, y3, y4) denote the two distinct messages.  Using associativity and commutativity 
of the ⊕ operator, we obtain that

CH(x) + CH(y) = CH(x + y),

where the “+” operator is just the bit-wise ⊕ of the operand vectors11.  Further, it can be 
verified that for two vectors u, v ∈ {0, 1}n, we have:

(see Exercise 1.12).  Thus, we have

∆(u, v) = wt(u + v)

min
x̸=y∈{0,1}4

∆(CH(x), CH(y)) = min

x̸=y∈{0,1}4

wt(CH(x + y))

= min

x̸=0∈{0,1}4

wt(CH(x)),

where the second equality follows from the observation that {x + y|x ̸= y ∈ {0, 1}n} = {x ∈
{0, 1}n|x ̸= 0}.  Recall that wt(CH(x)) = 0 if and only if x = 0 and this completes the proof 
of (1.11).  Combining (1.10) and (1.11), we conclude that CH has a distance of 3.

The second part of the proof could also be shown in the following manner.  It can be 
verified that the Hamming code is the set {x · GH|x ∈ {0, 1}4}, where GH is the following 
matrix (where we think x as a row vector).12

⎛

⎜
⎜
⎝

GH =

1 0 0 0 0 1 1
0 1 0 0 1 0 1
0 0 1 0 1 1 0
0 0 0 1 1 1 1

⎞

⎟
⎟
⎠

.

For example, the first column in GH gives the first codeword bit of x1 and the fifth column 
of GH gives the codeword bit x2 ⊕ x3 ⊕ x4.

In fact, any binary code (of dimension k and block length n) that is generated13 by a 
k × n matrix is called a binary linear code.  (Both C⊕ and C3,rep are binary linear codes: see 
Exercise 1.13.)  This implies the following simple fact.

Lemma 1.5.3. For any binary linear code C and any two messages x and y, C(x) + C(y) =
C(x + y).

11E.g.  (0, 1, 1, 0) + (1, 1, 1, 0) = (1, 0, 0, 0).
12Indeed (x1, x2, x3, x4) · GH = (x1, x2, x3, x4, x2 ⊕ x3 ⊕ x4, x1 ⊕ x3 ⊕ x4, x1 ⊕ x2 ⊕ x4), as desired.
13That is,  C = {x · G|x ∈ {0, 1}k},  where addition is the ⊕ operation and multiplication is the AND 

operation.

16

 


<!-- pdf-page: 29 -->
For any binary linear code, we have a generator matrix G. The following sequence 
Proof. 
of equalities (which follow from the distributivity and associativity properties of the Boolean 
EXOR and AND operators) proves the lemma:

C(x) + C(y) = x · G + y · G

= (x + y) · G
= C(x + y).

We stress that in the lemma above, x and y need not be distinct.  Note that due to the 
fact that b ⊕ b = 0 for every b ∈ {0, 1}, x + x = 0, which along with the lemma above implies 
that C(0) = 0.14 We can infer the following result from the above lemma and the arguments 
used to prove (1.11) in the proof of Proposition 1.5.2.

Proposition 1.5.4. For any binary linear code, its minimum distance is equal to the mini­
mum Hamming weight of any non-zero codeword.

Thus, we have seen that CH has distance d = 3 and rate R = 4

7 while C3,rep has distance 
d = 3 and rate R = 1
3.  Thus, the Hamming code is provably better than the repetition code 
(in terms of the tradeoff between rate and distance) and thus, answers Question 1.4.5 in the 
affirmative.  The next natural question is

Question 1.5.5  (Codes better than CH). Can we have a distance 3 code with a rate higher 
than that of CH?

We will address this question in the next section.

1.6  Hamming Bound

Now we switch gears to present our first tradeoff between redundancy (in the form of the 
dimension  of  a  code)  and  its  error-correction  capability  (in  the  form  of  its  distance).  In 
particular, we will first prove a special case of the so-called Hamming bound for a distance 
of 3.

We begin with another definition.

Definition 1.6.1  (Hamming Ball). For any vector x ∈ [q]n,

B(x, e) = {y ∈ [q]n|∆(x, y) ≤ e}.

In other words, a Hamming ball of radius e, centered at x, contains all vectors within 

Hamming distance at most e of x.

Next, we prove an upper bound on the dimension of every code with distance 3.

14This of course should not be surprising as for any matrix G, we have 0 · G = 0.

17

 


<!-- pdf-page: 30 -->
Theorem 1.6.2   (Hamming bound for d = 3). Every binary code with block length n, di­
mension k, distance d = 3 satisfies

k ≤ n − log2(n + 1).

Proof. 
3):

Given any two codewords, c1 ̸= c2 ∈ C, the following is true (as C has distance15

B(c1, 1) ∩ B(c2, 1) = ∅.

(1.12)

See Figure 1.4 for an illustration.

Figure 1.4: Hamming balls of radius 1 are disjoint. The figure is technically not correct: the 
balls above are actually balls in the Euclidean space, which is easier to visualize than the 
Hamming space.

Note that for all x ∈ {0, 1}n (see Exercise 1.16),

|B(x, 1)| = n + 1.

(1.13)

Now consider the union of all Hamming balls centered around some codeword; their union 
is a subset of {0, 1}n.  In other words,

⃓
⃓
⃓
⃓
⃓

⋃︂

c∈C

⃓
⃓
⃓
B(c, 1)
⃓
⃓

≤ 2n.

(1.14)

15Assume  that  y ∈ B(c1, 1) ∩ B(c2, 1),  that  is  ∆(y, c1) ≤ 1  and  ∆(y, c2) ≤ 1.  Thus,  by  the  triangle 

inequality ∆(c1, c2) ≤ 2 < 3, which is a contradiction.

18



<!-- pdf-page: 31 -->
As (1.12) holds for every pair of distinct codewords,

⃓
⃓
⃓
⃓
⃓

⋃︂

c∈C

⃓
⃓
⃓
B(c, 1)
⃓
⃓

=

=

∑︂

c∈C
∑︂

c∈C

|B(c, 1)|

(n + 1)

= 2k · (n + 1),

(1.15)

(1.16)

where (1.15) follows from (1.13) and (1.16) follows from the fact that C has dimension k. 
Combining (1.16) and (1.14), we get

2k(n + 1) ≤ 2n,

or equivalently

2n
n + 1
Taking log2 of both sides we get the desired bound:

2k ≤

.

k ≤ n − log2(n + 1).

Thus, Theorem 1.6.2 shows that for n = 7, CH has the largest possible dimension for 
any binary code of block length 7 and distance 3 (as for n = 7, n − log2(n + 1) = 4).  In 
particular, it also answers Question 1.5.5 for n = 7 in the negative.  Next, will present the 
general form of Hamming bound.

1.7  Generalized Hamming Bound

We start with a new notation.

Definition 1.7.1. A code C ⊆ Σn with dimension k and distance d will be called an (n, k, d)Σ
code.  We will also refer to it as an (n, k, d)|Σ| code.

We now proceed to generalize Theorem 1.6.2 to any distance d (from d = 3).

Theorem 1.7.2  (Hamming Bound for any d). For every (n, k, d)q code

k ≤ n − logq

⎛

⎜
⎝

⌋︂

⌊︂ d−1
2
∑︂

i=0

(︃n
i

)︃

(q − 1)i

⎞

⎟
⎠ .

19

 


<!-- pdf-page: 32 -->
Proof. 
notational convenience, let e = ⌊︁ d−1
is true (as C has distance16 d):

2

The proof is a straightforward generalization of the proof of Theorem 1.6.2.  For 
⌋︁.  Given any two codewords, c1 ̸= c2 ∈ C, the following 

We claim that for all x ∈ [q]n,

B(c1, e) ∩ B(c2, e) = ∅.

|B(x, e)| =

)︃

(q − 1)i.

e
∑︂

i=0

(︃n
i

(1.17)

(1.18)

Indeed  any  vector  in  B(x, e)  must  differ  from  x  in  exactly  0 ≤ i ≤ e  positions.  In  the 
summation, (︁n
)︁ is the number of ways of choosing the differing i positions and in each such 
position, a vector can differ from x in q − 1 ways.

i

Now consider the union of all Hamming balls centered around a codeword.  Obviously, 

their union is a subset of [q]n.  In other words,

⃓
⃓
⃓
⃓
⃓

⋃︂

c∈C

⃓
⃓
⃓
B(c, e)
⃓
⃓

≤ qn.

As (1.17) holds for every pair of distinct codewords,

⃓
⃓
⃓
⃓
⃓

⋃︂

c∈C

⃓
⃓
⃓
B(c, e)
⃓
⃓

=

∑︂

c∈C

|B(c, e)|

= qk

e
∑︂

i=0

)︃

(︃n
i

(q − 1)i,

(1.19)

(1.20)

where (1.20) follows from (1.18) and the fact that C has dimension k. Combining (1.20) and 
(1.19) and taking logq of both sides we will get the desired bound:

k ≤ n − logq

(︄ e

∑︂

i=0

(︃n
i

)︃

(q − 1)i

)︄

.

Note that the Hamming bound gives a partial answer to Question 1.4.4.  In particular, 

any code of distance d can have rate R at most

1 −

logq

(︁∑︁e

i=0

(︁n
i

)︁(q − 1)i)︁

n

.

Further, the Hamming bound also leads to the following definition:

16Assume  that  y ∈ B(c1, e) ∩ B(c2, e),  that  is  ∆(y, c1) ≤ e  and  ∆(y, c2) ≤ e.  Thus,  by  the  triangle 

inequality, ∆(c1, c2) ≤ 2e ≤ d − 1, which is a contradiction.

20

 


<!-- pdf-page: 33 -->
Definition 1.7.3. Codes that meet Hamming bound are called perfect codes.

In other words, a perfect code leads to the following perfect “packing”: if one constructs 
⌋︁ around all the codewords, then we would cover the entire 

Hamming balls of radius ⌊︁ d−1
ambient space, i.e.  every possible vector will lie in one of these Hamming balls.

2

One example of perfect code is the (7, 4, 3)2 Hamming code that we have seen in this 
chapter (so is the family of general Hamming codes that we will see in the next chapter).  A 
natural question to ask is if

Question 1.7.4  (Perfect Codes). Other than the Hamming codes, are there any other perfect 
(binary) codes?

We will see the answer in Section 2.4.

1.8  Family of codes

Until now, we have mostly studied specific codes with fixed block lengths and dimensions. 
However, when we perform an asymptotic study of codes, it makes more sense to talk about 
a family of codes and study their asymptotic rate and distance.  We define these notions 
next.

Definition 1.8.1  (Code families, Rate and Distance). Let {ni}i≥1 be an increasing sequence 
of block lengths and suppose there exists sequences {ki}i≥1 , {di}i≥1 and {qi}i≥1 such that for 
all i ≥ 1 there exists an (ni, ki, di)qi code Ci.  Then the sequence C = {Ci}i≥1 is a family of 
codes.  The rate of C is defined as

R(C) = lim
i→∞

}︃

,

{︃ ki
ni

when the limit exists.  The relative distance of C is defined as

δ(C) = lim
i→∞

}︃

,

{︃ di
ni

when the limit exists. If for all i ≥ 1, qi = q then C is referred to as a family of q-ary codes.17
18

For instance, we will in Section 2.4 see that Hamming code of Section 1.5 can be extended 
to an entire family of codes.  Specifically, CH = {Ci}i∈Z+, with Ci being an (ni.ki, di)-code 
with ni = 2i − 1, ki = 2i − i − 1, di = 3 and thus,

R(CH) = lim
i→∞

1 −

i
2i − 1

= 1,

17In all codes we will study these limits will exist, but of course it is possible to construct families of codes 

where the limits do not exist.

18While a central goal is to understand q-ary families of codes, families over growing alphabets turn out 

to be useful both to illustrate ideas and to get interesting q-ary families.

21



<!-- pdf-page: 34 -->
and

δ(CH) = lim
i→∞

3
2i − 1

= 0.

A significant focus of this text from now on will be on families of codes. This is necessary 
as we will be studying the asymptotic behavior of algorithms on codes, which does not make 
sense for a fixed code.  For example, when we say that a decoding algorithm for a code C
takes O(n2) time, we would be implicitly assuming that C is a family of codes and that the 
algorithm has an O(n2) running time when the block length is large enough.  From now on, 
unless mentioned otherwise, whenever we talk about a code, we will be implicitly assuming 
that we are talking about a family of codes.

Given that we can only formally talk about asymptotic run time of algorithms, we now 

also state our formal notion of efficient algorithms: 

Note

We’ll call an algorithm related to a code of block length n to be efficient if it runs in 
time polynomial in n.

For all the specific codes that we will study in this book, the corresponding family of 
codes will be a “family” in a more natural sense. By this we mean that all the specific codes 
in a family of codes will be the “same” code except with different parameters.  A bit more 
formally, we will consider families {Ci}i≥1, where given only the ‘index’ i, one can compute 
a sufficient description of Ci efficiently.19

Finally, the definition of a family of codes allows us to present the final version of the big 
motivating question for the book. The last formal version of the main question we considered 
was Question 1.4.4, where we were interested in the tradeoff of rate R and distance d.  The 
comparison was somewhat unfair because R was a ratio while d was an integer.  A more 
appropriate comparison should be between rate R and the relative distance δ.  Further, we 
would be interested in tackling the main motivating question for families of codes,  which 
results in the following final version:

Question  1.8.2   (Main Question- formal). Given  q,  what  is  the  optimal  tradeoff  between 
R(C) and δ(C) that can be achieved by some family C of q-ary codes?

A natural special case of Question 1.8.2 is whether the rate and relative distance of a 
family of codes can be simultaneously positive.  We formulate this special case as a separate 
question below.

Question 1.8.3  (Asymptotically Good Codes). Does there exist a constant q and a q-ary 
family of codes C such that R(C) > 0 and δ(C) > 0 hold simultaneously?

Codes  that  have  the  above  property  are  called  asymptotically  good.  For  the  curious 
reader, we will present many asymptotically good codes in the rest of this book, though a 
priori the existence of these is not immediate.

19We stress that this is not always going to be the case.  In particular, we will consider “random” codes 

where this efficient constructibility will not be true.

22



<!-- pdf-page: 35 -->
1.9  Exercises

Exercise  1.1.  Show  that  every  t-error  correcting  code  is  also  t-error  detecting  but  not 
necessarily the other way around.

Exercise 1.2. Prove Proposition 1.3.9.

Exercise 1.3. Show that for every integer n, there is no code with block length n that can 
handle arbitrary number of errors.

Exercise 1.4. Prove Proposition 1.3.10.

Exercise 1.5. A distance function on Σn (i.e.  d : Σn × Σn → R) is called a metric if the 
following conditions are satisfied for every x, y, z ∈ Σn:

1. d(x, y) ≥ 0.

2. d(x, y) = 0 if and only if x = y.

3. d(x, y) = d(y, x).

4. d(x, z) ≤ d(x, y) + d(y, z).  (This property is called the triangle inequality.)

Prove that the Hamming distance is a metric.

Exercise 1.6. Let C be a code with distance d for even d.  Then argue that C can correct 
up to d/2 − 1 many errors but cannot correct d/2 errors.  Using this or otherwise, argue that 
if a code C is t-error correctable then it either has a distance of 2t + 1 or 2t + 2.

Exercise 1.7. In this exercise, we will see that one can convert arbitrary codes into code 
with slightly different parameters:

1. Prove that if there exists an (n, k, d)Σ code then there also exists an (n − 1, k, d − 1)Σ
code.  Specifically, show how to convert an (n, k, d)Σ code C into an (n − 1, k, d − 1)Σ
code.

2. For odd d, prove that if an (n, k, d)2 code exists, then there also exists an (n+1, k, d+1)2
code.  Specifically, show how to convert an (n, k, d)2 code C into an (n + 1, k, d + 1)2
code.

Note:  Your conversion should not assume anything else about the code other than the pa­
rameters of the code C.  Also your conversion should work for every n, k, d ≥ 1 and every 
Σ.

23



<!-- pdf-page: 36 -->
Exercise  1.8.  In  this  problem  we  will  consider  a  noise  model  that  has  both  errors  and 
erasures.  In particular, let C be an (n, k, d)Σ code.  As usual a codeword c ∈ C is transmitted 
over the channel and the received word is a vector y ∈ (Σ ∪ {?})n, where as before a ? denotes 
an erasure.  We will use s to denote the number of erasures in y and e to denote the number 
of (non-erasure) errors that occurred during transmission.  To decode such a vector means 
to output a codeword c ∈ C such that the number of positions where c disagree with y in the 
n − s non-erased positions is at most e.  For the rest of the problem assume that

2e + s < d.

(1.21)

1. Argue that the output of the decoder for any C under (1.21) is unique.

2. Let C be a binary code (but not necessarily linear).  Assume that there exists a decoder 
D that can correct from < d/2 many errors in T (n) time.  Then under (1.21) one can 
perform decoding in time O(T (n)).

Exercise 1.9. Define codes other than CH with k = 4, n = 7 and d = 3.
Hint:  Refer to the proof of Proposition 1.5.2 to figure out the properties needed from the three parities.

Exercise 1.10. Argue that if wt(x) = 1 then at least two parity check bits in (x2 ⊕ x3 ⊕
x4, x1 ⊕ x2 ⊕ x4, x1 ⊕ x3 ⊕ x4) are 1.

Exercise 1.11. Argue that if wt(x) = 2 then at least one parity check bit in (x2 ⊕ x3 ⊕
x4, x1 ⊕ x2 ⊕ x4, x1 ⊕ x3 ⊕ x4) is 1.

Exercise 1.12. Prove that for any u, v ∈ {0, 1}n, ∆(u, v) = wt(u + v).

Exercise 1.13. Argue that C⊕ and C3,rep are binary linear codes.

Exercise 1.14. Let G be a generator matrix of an (n, k, d)2 binary linear code.  Then G has 
at least kd ones in it.

Exercise 1.15. Argue that in any binary linear code, either all codewords begin with a 0 of 
exactly half of the codewords begin with a 0.

Exercise 1.16. Prove (1.13).

Exercise  1.17.  Show  that  there  is  no  binary  code  with  block  length  4  that  achieves  the 
Hamming bound.

Exercise 1.18. (∗) There are n people in a room, each of whom is given a black/white hat 
chosen uniformly at random (and independent of the choices of all other people). Each person 
can see the hat color of all other people, but not their own.  Each person is asked if they wish 
to guess their own hat color.  They can either guess, or abstain.  Each person makes their 
choice without knowledge of what the other people are doing.  They either win collectively, 
or lose collectively.  They win if at least one person does not abstain and all the people who 
don’t abstain guess their hat color correctly. They lose if all people abstain, or if some person 
guesses their color incorrectly.  Your goal below is to come up with a strategy that will allow 
the n people to win with pretty high probability.  We begin with a simple warm-up:

24



<!-- pdf-page: 37 -->
1. Argue that the n people can win with probability at least  1
2.

Next we will see how one can really bump up the probability of success with some careful 
modeling, and some knowledge of Hamming codes.  (Below are assuming knowledge of the 
general Hamming code (see Section 2.4).  If you do not want to skip ahead, you can assume 
that n = 7 in the last part of this problem.)

2. Lets say that a directed graph G is a subgraph of the n-dimensional hypercube if its 
vertex set is {0, 1}n and if u → v is an edge in G,  then u and v differ in at most 
one coordinate.  Let K(G) be the number of vertices of G with in-degree at least one, 
and out-degree zero.  Show that the probability of winning the hat problem equals the 
maximum, over directed subgraphs G of the n-dimensional hypercube, of K(G)/2n.

3. Using the fact that the out-degree of any vertex is at most n, show that K(G)/2n is at 

most  n

n+1 for any directed subgraph G of the n-dimensional hypercube.

4. Show that if n = 2r − 1, then there exists a directed subgraph G of the n-dimensional 

hypercube with K(G)/2n = n
Hint:  This is where the Hamming code comes in.

n+1.

1.10  Bibliographic Notes

Coding theory owes its origin to two remarkable papers: one by Shannon [65] and the other by 
Hamming [35] both of which were published within a couple of years of each other. Shannon’s 
paper defined the BSCp channel (among others) and defined codes in terms of its encoding 
function.  Shannon’s paper also explicitly defined the decoding function.  Hamming’s work 
defined the notion of codes as in Definition 1.2.1 as well as the notion of Hamming distance. 
Both the Hamming bound and the Hamming code are (not surprisingly) due to Hamming. 
The specific definition of Hamming code that we used in this book was the one proposed 
by Hamming and is also mentioned in Shannon’s paper (which pre-dates Hamming’s) with 
attribution to Hamming. The notion of erasures was defined by Elias [23]. Most exercises of 
this chapter are based on [35].  The hat problem in Exercise 1.18 is from Ebert, Merkle and 
Vollmer [22].

25



<!-- pdf-page: 38 -->
26



<!-- pdf-page: 39 -->
Chapter 2

A Look at Some Nicely Behaved 
Codes:  Linear Codes

One motivation for the topic of this chapter is the following question: How we can represent 
a code? Or more specifically, how many bits does it take to describe a code C : [q]k −→ [q]n? 
In general, a code C : [q]k −→ [q]n can be stored using nqk symbols from [q] (n symbols for 
each of the qk codewords) or nqk log q bits. For constant rate codes, this is exponential space, 
which is prohibitive even for modest values of k like k = 100.  A natural question is whether 
we can do better.  To have any hope of doing so, a succinct representation the code must 
have some extra structure.  It turns out that one broad class of codes that do possess extra 
structure than general codes, is what are called linear codes.  We have already seen binary 
linear codes in Section 1.5, that is: C ⊆ {0, 1}n is a linear code if for all c1, c2 ∈ C, c1+c2 ∈ C, 
where the “+” denotes bit-wise XOR. In this chapter, we will see more general linear codes. 
We will see that they not only offer enough structure to get succinct representations, but 
they also possess several other nice properties.

To define general linear codes, we first need to introduce general finite fields and vector 

spaces over such fields and we do so first before returning to codes.

2.1  Groups and Finite Fields

To define linear subspaces, we will need to work with (finite) fields. At a high level, we need 
finite fields since when we talk about codes, we deal with finite symbols/numbers and we 
want to endow these symbols with the same math that makes arithmetic over real numbers 
work.  Finite fields accomplish this precise task.  We begin with a quick overview of fields. 
We start with the more elementary notion of a group.

Definition 2.1.1. A group G is given by a pair (S, ◦), where S is the set of elements and ◦
is a function S × S → S with the following properties:

• Closure: For every a, b ∈ S, we have a ◦ b ∈ S.

27



<!-- pdf-page: 40 -->
• Associativity: ◦ is associative:  that is, for every a, b, c ∈ S, a ◦ (b ◦ c) = (a ◦ b) ◦ c.

• Identity: There exists distinct a special elements e ∈ S such that for every a ∈ S we 

have a ◦ e = e ◦ a = a.

• Inverse:  For every a ∈ S, there exists its unique  inverse a−1 such that a ◦ a−1 =

a−1 ◦ a = e.

If G = (S, ◦) satisfies all the properties except the existence of inverses then G is called a 
monoid.  We say G is commutative if for every a, b ∈ S, a ◦ b = b ◦ a.

We often use the same letter to denote the group (or other algebraic structures) and the 

set of elements.

We now turn to the definition of a field.  Informally speaking, a field is a set of elements 
on which one can do addition, subtraction, multiplication and division and still stay in the 
set.

Definition 2.1.2. A field F is given by a triple (S, +, ·), where S is the set of elements and 
+, · are functions S × S → S with the following properties:

• Addition:  (S, +) form a commutative group with identity element denoted 0 ∈ S.

• Multiplication: (S \{0}, ·) form a commutative group with identity element 1 ∈ S \{0}.1

• Distributivity: · distributes over +: that is, for every a, b, c ∈ S, a · (b + c) = a · b + a · c.

Again we typically use the same letter to denote the field and its set of elements. We also 
use −a to denote the additive inverse of a ∈ F and a−1 to denote the multiplicative inverse 
of a ∈ F \ {0}.

We note that in the above definition we have not explicitly argued that a · 0 = 0 = 0 · a
for any a ∈ S. (Technically this means (S, ·) is a commutative monoid.)  This is because this 
property is implied by Definition 2.1.2– see Exercise 2.1.

With the usual semantics for + and ·, R (set of real number) is a field, but Z (set of 
integers) is not a field as division of two integers results in a rational number that need not 
be an integer (the set of rational numbers itself is a field though:  see Exercise 2.2).  In this 
course, we will exclusively deal with finite fields.  As the name suggests these are fields with 
a finite set of elements.  (We will overload notation and denote the size of a field |F| = |S|.) 
The following is a well known result.

Theorem 2.1.3  (Size of Finite Fields). Every finite field has size ps for some prime p and 
integer s ≥ 1.  Conversely for every prime p and integer s ≥ 1 there exists a field F of size 
ps.

1Note that we do not include 0 since it does not have a multiplicative inverse.

28



<!-- pdf-page: 41 -->
One example of a finite field that we have seen is the field with S = {0, 1}, which we will 
denote by F2 (we have seen this field in the context of binary linear codes). For F2, addition 
is the XOR operation, while multiplication is the AND operation.  The additive inverse of 
an element in F2 is the number itself while the multiplicative inverse of 1 is 1 itself.

Let p be a prime number.  Then the integers modulo p form a field, denoted by Fp (and 
also by Zp), where the addition and multiplication are carried out modulo p.  For example, 
consider F7, where the elements are {0, 1, 2, 3, 4, 5, 6}.  We have (4 + 3) mod 7 = 0 and 4 · 4
mod 7 = 2. Further, the additive inverse of 4 is 3 as (3+4) mod 7 = 0 and the multiplicative 
inverse of 4 is 2 as 4 · 2 mod 7 = 1.

More formally, we prove the following result.

Lemma 2.1.4. Let p be a prime.  Then Fp = ({0, 1, . . . , p − 1}, +p, ·p) is a field, where +p
and ·p are addition and multiplication modulo p.

Proof. 
The properties of associativity, commutativity, distributivity and identities hold 
for integers and hence, they hold for Fp.  The closure property follows since both the “addi­
tion” and “multiplication” are done modulo p, which implies that for any a, b ∈ {0, . . . , p−1}, 
a +p b, a ·p b ∈ {0, . . . , p − 1}.  Thus, to complete the proof, we need to prove the existence of 
unique additive and multiplicative inverses.

Fix an arbitrary a ∈ {0, . . . , p − 1}.  Then we claim that its additive inverse is p − a
mod p.  It can be verified that a + p − a = 0 mod p.  Next we argue that this is the unique 
additive  inverse.  To  see  this  note  that  the  sequence  a, a + 1, a + 2, . . . , a + p − 1  are  p
consecutive numbers and thus,  exactly one of them is a multiple of p,  which happens for 
b = p − a mod p, as desired.

Now fix an a ∈ {1, . . . , p − 1}. Next we argue for the existence of a unique multiplicative 
universe a−1.  Consider the set of numbers T = {a ·p b|b ∈ {1, . . . , p − 1}}.  We claim that 
all these numbers are unique.  To see this, note that if this is not the case, then there exist 
b1 ̸= b2 ∈ {0, 1, . . . , p − 1}  such  that  a · b1 = a · b2 mod p,  which  in  turn  implies  that 
a · (b1 − b2) = 0 mod p. Since a and b1 − b2 are non-zero numbers, this implies that p divides 
a · (b1 − b2). Further, since a and |b1 − b2| are both at most p − 1, this implies that multiplying 
a and (b1 − b2) mod p results in p, which is a contradiction since p is prime.  Thus, we have 
argued that |T | = p − 1 and since each number in T  is in [p − 1], we have that T = [p − 1]. 
Thus, we can conclude that there exists a unique element b such that a · b = 1 mod p and 
thus, b is the required a−1.

One  might  think  that  there  could  be  different  finite  fields  with  the  same  number  of 

elements.  However, this is not the case:

Theorem 2.1.5. For every prime power q there is a unique finite field with q elements (up 
to isomorphism2).

Thus, we are justified in just using Fq to denote a finite field on q elements.

2An isomorphism φ : S → S′ is a bijective map (such that F = (S, +, ·) and F′ = (S′, ⊕, ◦) are fields) 
where for every a1, a2 ∈ S, we have φ(a1 + a2) = φ(a1) ⊕ φ(a2) and φ(a1 · a2) = φ(a1) ◦ φ(a2).  In other 
words, an ismorphisms is a map between representations that ‘preserves’ the effect of operators on elements.

29

 


<!-- pdf-page: 42 -->
2.2  Vector Spaces and Linear Subspaces

Definition  2.2.1   (Vector  Space).  A  vector  space  V   over  a  field  F  is  given  by  a  triple 
(T, +, ·) such that (T, +) form a commutative group and ·, referred to as the scalar product, 
is a function F×T → T  such that for every a, b ∈ F and u, v ∈ T  we have (a+b)·u = a·u+b·u
and a · (u + v) = a · u + a · v.

The most common vector space we will focus on is Fn with + representing coordinatewise 

addition in F and a · u representing the coordinatewise scaling of u by a.
We are finally ready to define the notion of linear subspaces of Fn.

Definition 2.2.2  (Linear Subspace). A non-empty subset S ⊆ Fn is a linear subspace if the 
following properties hold:

1. For every x, y ∈ S, x + y ∈ S, where the addition is vector addition over F (that is, do 

addition componentwise over F).

2. For every a ∈ F and x ∈ S, a · x ∈ S, where the multiplication is done componentwise 

over F.

Here is a (trivial) example of a linear subspace of F3
5:

S1 = {(0, 0, 0), (1, 1, 1), (2, 2, 2), (3, 3, 3), (4, 4, 4)}.

(2.1)

Note that for example (1, 1, 1) + (3, 3, 3) = (4, 4, 4) ∈ S1 and 2 · (4, 4, 4) = (3, 3, 3) ∈ S1 as 
required by the definition. Here is another somewhat less trivial example of a linear subspace 
over F3
3:

S2 = {(0, 0, 0), (1, 0, 1), (2, 0, 2), (0, 1, 1), (0, 2, 2), (1, 1, 2), (1, 2, 0), (2, 1, 0), (2, 2, 1)} .

(2.2)

Note that (1, 0, 1) + (0, 2, 2) = (1, 2, 0) ∈ S2 and 2 · (2, 0, 2) = (1, 0, 1) ∈ S2 as required.

Remark 2.2.3. Note that the second property implies that 0 is contained in every linear sub­
space.  Further for any subspace over F2, the second property is redundant:  see Exercise 2.5.

Before we state some properties of linear subspaces, we state some relevant definitions.

Definition 2.2.4  (Span). Given a set B = {v1, . . . , vℓ}.  The span of B is the set of vectors

ai · vi

⃓
⃓ai ∈ Fq for every i ∈ [ℓ]

}︄

.

{︄ ℓ

∑︂

i=1

30



<!-- pdf-page: 43 -->
Definition 2.2.5  (Linear (in)dependence of vectors). We say that v1, v2, . . . vk are linearly 
independent if for every 1 ≤ i ≤ k and for every (k −1)-tuple (a1, a2, . . . , ai−1, ai+1, . . . , ak) ∈
Fk−1
q

,

vi ̸= a1v1 + . . . + ai−1vi−1 + ai+1vi+1 + . . . + akvk.

In other words, vi is not in the span of the set {v1, . . . , vi−1, vi+1, . . . , vn} for every 1 ≤ i ≤ k. 
We say that v1, v2, . . . vk are linearly dependent if they are not linearly independent.

For example the vectors (1, 0, 1), (1, 1, 1) ∈ S2 are linearly independent since

• a1 · (1, 0, 1) = (a1, 0, a1) ̸= (1, 1, 1) for any a1 ∈ {0, 1}.

• a2 · (1, 1, 1) = (a2, a2, a2) ̸= (1, 0, 1) for any a2 ∈ {0, 1}.

Definition 2.2.6  (Rank of a matrix). The rank of matrix in Fk×k
of linearly independent rows (or columns).  A matrix in Fk×n
have full rank.

q

q

 is the maximum number 
 with rank min(k, n) is said to 

One  can  define  the  row  (column)  rank  of  a  matrix  as  the  maximum  number  of  linearly 
independent rows (columns).  However, it is a well-known theorem that the row rank of a 
matrix is the same as its column rank.  For example, the matrix below over F3 has full rank 
(see Exercise 2.6):

G2 =

)︃

(︃ 1 0 1
0 1 1

.

(2.3)

Any linear subspace satisfies the following properties (the full proof can be found in any 

standard linear algebra textbook).

Theorem 2.2.7. If S ⊆ Fq

n is a linear subspace then

1. |S| = qk for some k ≥ 0.  The parameter k is called the dimension of S.

2. There exists at least one set of linearly independent vectors v1, ..., vk ∈ S called basis 
elements  such  that  every  x ∈ S  can  be  expressed  as  x = a1v1 + a2v2 + ... + akvk
where ai ∈ Fq for 1 ≤ i ≤ k.  In other words, there exists a full rank k × n matrix 
G (also known as a generator matrix) with entries from Fq such that every x ∈ S, 
x = (a1, a2, . . . , ak) · G where

⎛

⎜
⎜
⎜
⎝

G =

←− v1 −→
←− v2 −→
...
←− vk −→

⎞

⎟
⎟
⎟
⎠

.

3. There exists a full rank (n − k) × n matrix H (called a parity check matrix) such that 

for every x ∈ S, HxT = 0.

31



<!-- pdf-page: 44 -->
4. G and H are orthogonal, that is, G · H T = 0.

Proof Sketch. 
Property 1. We begin with the proof of the first property.  For the sake of contradiction, 
let us assume that qk < |S| < qk+1, for some k ≥ 0.  Iteratively, we will construct a set of 
linearly independent vectors B ⊆ S such that |B| ≥ k + 1.  Note that by the definition of a 
linear subspace the span of B should be contained in S.  However, this is a contradiction as 
the size of the span of B is at least3 qk+1 > |S|.

To complete the proof, we show how to construct the set B in a greedy fashion.  In the 
first step pick v1 to be any non-zero vector in S and set B ← {v1} (we can find such a 
vector as |S| > qk ≥ 1).  Now say after the step t (for some t ≤ k), |B| = t.  Now the size of 
the span of the current B is qt ≤ qk < |S|.  Thus there exists a vector vt+1 ∈ S \ B that is 
linearly independent of vectors in B.  Set B ← B ∪ {vt+1}.  Thus, we can continue building 
B until |B| = k + 1, as desired.

Property 2.  We first note that we can pick B = {v1, . . . , vk} to be any set of k linearly 
independent vectors– this just follows from the argument above for Property 1.1.  This is 
because the span of B is contained in S.  However, since |S| = qk and the span of B has qk
vectors, the two have to be the same.

Property 3.  Property 3 above follows from another fact that every linear subspace S has a 
null space N ⊆ Fn
q  such that for every x ∈ S and y ∈ N , ⟨x, y⟩ = 0. Further, it is known that 
N  itself is a linear subspace of dimension n − k.  (The claim that N  is also a linear subspace 
follows from the following two facts: for every x, y, z ∈ Fn
q , (i) ⟨x, y + z⟩ = ⟨x, y⟩ + ⟨x, z⟩ and 
(ii) for any a ∈ Fq, ⟨x, ay⟩ = a · ⟨x, y⟩.)  In other words, there exists a generator matrix H
for it.  This matrix H is called the parity check matrix of S.

Property 4.  See Exercise 2.9.

As examples, the linear subspace S1 in (2.1) has as one of its generator matrices

and as one of its parity check matrices

G1 = (︁ 1 1 1 )︁

H1 =

(︃ 1 2 2
2 2 1

)︃

.

Further, the linear subspace S2 in (2.2) has G2 as one of its generator matrices and has the 
following as one of its parity check matrices

H2 = (︁ 1 1 2 )︁ .

Finally, we state another property of linear subspaces that is useful.

3See Exercise 2.8.

32

 
 


<!-- pdf-page: 45 -->
Lemma 2.2.8. Given matrix G of dimension k × n that is a generator matrix of subspace 
S1 and matrix H of dimension (n − k) × n that is a parity check matrix of subspace S2 such 
that GH T = 0, then S1 = S2.

Proof.  We first prove that S1 ⊆ S2.  Given any c ∈ S1, there exists x ∈ Fk
c = xG.  Then,

q  such that 

H · cT = H · (xG)T = HGT xT = (︁GH T )︁T

xT = 0,

which implies that c ∈ S2, as desired.

To complete the proof note that as H has full rank, its null space (or S2) has dimension 
n−(n−k) = k (this follows from a well known fact from linear algebra called the rank-nullity 
theorem).  Now as G has full rank, the dimension of S1 is also k.  Thus, as S1 ⊆ S2, it has to 
be the case that S1 = S2.4

2.3  Linear Codes and Basic Properties

We now return to the topic of codes and introduce the central concept for this chapter as 
well as much of this text.

Definition 2.3.1  (Linear Codes). Let q be a prime power (i.e.  q = ps for some prime p and 
q  is a linear code if it is a linear subspace of Fn
integer s ≥ 1).  C ⊆ Fn
q .  If C has dimension 
k and distance d then it will be referred to as an [n, k, d]q or just an [n, k]q code.

Theorem 2.2.7 now gives two alternate characterizations of an [n, k]q linear code C: first, 
C is generated by a k × n generator matrix G.  Second, C is defined by a (n − k) × n parity 
check matrix H.  Since these are important concepts for us, we define these formally below 
before giving examples and consequences.

Definition 2.3.2  (Generator and Parity Check Matrices). If C is an [n, k]q linear code then 
there exists a matrix G ∈ Fk×n

 of rank k satisfying

q

C = {x · G|x ∈ Fk

q }.

G is referred to as a generator matrix of C.  In other words, the code C is the set of all 
possible linear combinations of rows of G.

If  C  is  an  [n, k]q  linear  code  then  there  exists  a  matrix  H ∈ F(n−k)×n

  of  rank  n − k

q

satisfying

C = {y ∈ Fn

q |H · yT = 0}.

H is referred to as a parity check matrix of C.

4If not, S1 ⊂ S2 which implies that that |S2| ≥ |S1| + 1.  The latter is not possible if both S1 and S2

have the same dimension.

33

 


<!-- pdf-page: 46 -->
Note that we require G and H to have full row rank (i.e.,  the rows of G are linearly 
independent and the same holds for H).  Sometimes we will consider matrices M ∈ Fm×n
that are not of full row rank. These can still be used to generate a code C = {{x · G|x ∈ Fm
q }
though the code C will not be an [n, m]q code. We will still refer to C as the code generated 
by M  in such a case, though the phrase “generator matrix” will be reserved for full rank 
matrices.

q

Note that neither the generator matrix nor the parity check matrix are unique for a given 
code. However, all generator matrices (and parity check matrices) have the same dimensions, 
i.e. all are k × n (and (n − k) × n respectively) matrices. We give examples of these matrices 
for the case of the [7, 4, 3]2 Hamming code below.

• The [7, 4, 3]2 Hamming code has the following generator matrix:

⎛

⎜
⎜
⎝

G =

1 0 0 0 0 1 1
1 0 0 1 0 1
0
0 1 0 1 1 0
0
0 0 1 1 1 1
0

⎞

⎟
⎟
⎠

• The following matrix is a parity check matrix of the [7, 4, 3]2 Hamming code:

⎛

⎝

H =

0 0 0 1 1 1 1
1 1 0 0 1 1
0
0 1 0 1 0 1
1

⎞

⎠

Indeed, it can be easily verified that G · H T = 0.  Then Lemma 2.2.8 proves that H is 
a parity check matrix of the [7, 4, 3]2 Hamming code.

We  now  look  at  some  consequences  of  the  above  characterizations  of  an  [n, k]q  linear 
code C.  We started this chapter with a quest for succinct representation of a code.  Note 
that both the generator matrix and the parity check matrix can be represented using O(n2)
symbols from Fq.  Note that this is much smaller than the exponential representation of a 
general code.  More precisely we have the following result on succinct representations of a 
linear code (see also Exercise 2.11):

Proposition 2.3.3. Any [n, k]q linear code can be represented with min(nk, n(n−k)) symbols 
from Fq.

There is an encoding algorithm for C that runs in O(n2) (in particular O(kn)) time– given 
q , the corresponding codeword C(m) = m · G, where G is the generator 

a message m ∈ Fk
matrix of C.  (See Exercise 2.12.)

Proposition 2.3.4. For any [n, k]q linear code, given its generator matrix, encoding can be 
done with O(nk) operations over Fq.

34



<!-- pdf-page: 47 -->
There is an error-detecting algorithm for C that runs in O(n2).  This is a big improve­
ment over the naive brute force exponential time algorithm (that goes through all possible 
codewords c ∈ C and checks if y = c).  (See Exercise 2.13.)

Proposition 2.3.5. For any [n, k]q linear code, given its parity check matrix, error detection 
can be performed in O(n(n − k)) operations over Fq.

Next, we look at some alternate characterizations of the distance of a linear code.

2.3.1  On the Distance of a Linear Code

Linear codes admit a nice characterization of minimum distance in terms of the Hamming 
weight of non-zero codewords, which we have seen for the special case of binary linear codes 
(Proposition 1.5.4).  Recall that we use wt(x) to denote the Hamming weight of a vector 
x ∈ Σn, i.e., the number of non-zero coordinates in x.

Proposition 2.3.6. For every [n, k, d]q code C, we have

d = min
c∈C,
c̸=0

wt(c).

Proof. 
than the minimum weight and d is no less than the minimum weight.

To show that d is the same as the minimum weight we show that d is no more 

First, we show that d is no more than the minimum weight. We can see this by considering 
∆(0, c′) where c′ is the non-zero codeword in C with minimum weight; its distance from 0 is 
equal to its weight.  Thus, we have d ≤ wt(c′), as desired.

Now, to show that d is no less than the minimum weight,  consider c1 ̸= c2 ∈ C such 
that ∆(c1, c2) = d.  Note that c1 − c2 ∈ C (this is because −c2 = −1 · c2 ∈ C, where −1
is the additive inverse of 1 in Fq and c1 − c2 = c1 + (−c2), which is in C by the definition 
of linear codes).  Now note that wt(c1 − c2) = ∆(c1, c2) = d, since the non-zero symbols in 
c1 − c2 occur exactly in the positions where the two codewords differ. Further, since c1 ̸= c2, 
c1 − c2 ̸= 0, which implies that the minimum Hamming weight of any non-zero codeword in 
C is at most d.

Next, we look at another property implied by the parity check matrix of a linear code.

Proposition 2.3.7. For every [n, k, d]q code C with parity check matrix H, d equals the size 
of the smallest subset of columns of H that are linearly dependent.

Proof. 
By Proposition 2.3.6, we need to show that the minimum weight of a non-zero 
codeword in C is the minimum number of linearly dependent columns. Let t be the minimum 
number of linearly dependent columns in H. To prove the claim we will show that t ≤ d and 
t ≥ d.

35

 


<!-- pdf-page: 48 -->
For the first direction, Let c ̸= 0 ∈ C be a codeword with wt(c) = d.  Now note that, 
by  the  definition  of  the  parity  check  matrix,  H · cT = 0.  Working  through  the  matrix 
multiplication, this gives us that ∑︁n
i=1 ciH i = 0, where
↑
↑
H 1 H 2
↓
↓

↑
· · · H n
↓

↑
· · · H i
↓

H =

⎛

⎝

⎞

⎠

and c = (c1, . . . , cn).  Note that we can skip multiplication for those columns for which the 
corresponding  bit  ci  is  zero,  so  for  H · cT   to  be  zero,  those  H i  with  ci
̸= 0  are  linearly 
dependent.  This means that d ≥ t, as the columns corresponding to non-zero entries in c
are one instance of linearly dependent columns.

H i1 + . . . + c′

For the other direction, consider the minimum set of columns from H, H i1, H i2, . . . , H it
it ∈ Fq
that are linearly dependent. This implies that there exists non-zero elements c′
itH it = 0.  (Note that all the c′
such that c′
ij  are non-zero as no set of less than 
ii
t columns are linearly dependent.)  Now extend c′
j = 0
for j ̸∈ {i1, . . . , it}.  Note that we have H · (c′)T = 0 and thus, we have c′ ∈ C.  This in turn 
implies that d ≤ wt(c′) = t (where recall t is the minimum number of linearly independent 
columns in H).

it to the vector c′ such that c′

i1, . . . , c′

i1, . . . , c′

2.4  Hamming Codes

We now change gears and look at the general family of linear codes, which were discovered 
by Hamming.  So far, we have seen the [7, 4, 3]2 Hamming code (in Section 1.5).  In fact, for 
any r ≥ 2 there is a [2r − 1, 2r − r − 1, 3]2 Hamming code.  Thus in Section 1.5, we have seen 
this code for r = 3.

Definition 2.4.1  (Binary Hamming Codes). For any positive integer r, define the matrix 
Hr ∈ Fr×(2r−1)
 to be the r × (2r − 1) matrix whose ith column Hi
r is the binary representation 
of i, for 1 ≤ i ≤ 2r − 1.  (Note that such a representation is a vector in {0, 1}r.)

2

The [2r − 1, 2r − r − 1]2 Hamming code, denoted by CH,r, is the code with parity check 

matrix Hr.

In other words, the general [2r − 1, 2r − r − 1]2 Hamming code is the code

For example, for the case we have seen (r = 3),

{c ∈ {0, 1}2r−1|Hr · cT = 0}.

⎛

⎝

H3 =

0 0 0 1 1 1 1
0 1 1 0 0 1 1
1 0 1 0 1 0 1

⎞

⎠ ,

and the resulting code was a [7, 4, 3]2 code.

Next we argue that the above Hamming code has distance 3 (in Proposition 1.5.2, we 

argued this for r = 3).

36

 


<!-- pdf-page: 49 -->
Proposition 2.4.2. The Hamming code [2r − 1, 2r − r − 1, 3]2 has distance 3.

No two columns in Hr are linearly dependent.  If they were, we would have Hi

r +
Proof. 
Hj
r = 0, but this is impossible since they differ in at least one bit (being binary representations 
of integers, i ̸= j).  Thus, by Proposition 2.3.7, the distance is at least 3.  It is at most 3, 
since (e.g.)  H1

r + H2

r + H3

r = 0.

Now note that under the Hamming bound for d = 3 (Theorem 1.6.2), k ≤ n−log2(n+1), 
so  for  n = 2r − 1,  k ≤ 2r − r − 1.  Hence,  the  Hamming  code  is  a  perfect  code.  (See 
Definition 1.7.3.)

In Question 1.7.4, we asked which codes are perfect codes. Interestingly, the only perfect 

binary codes are the following:

• The Hamming codes which we just studied.

• The trivial [n, 1, n]2 codes for odd n (which have 0n and 1n as the only codewords): 

see Exercise 2.24.

• Two codes due to Golay [28].

2.5  Efficient Decoding of Hamming codes

We have shown that the Hamming code has a distance of 3 and thus, by Proposition 1.4.2, can 
correct one error.  However, this is a combinatorial result and does not give us an efficient 
algorithm.  One  obvious  candidate  for  decoding  is  the  MLD  function  (Algorithm  1.4.1). 
Unfortunately, the only implementation of MLD that we know is the one in Algorithm 1.4.1, 
which will take time 2Θ(n), where n is the block length of the Hamming code.

However, we can do much better.  Consider the following simple algorithm:  given the 
received word y, first check if it is indeed a valid codeword.  If it is, we are done.  Otherwise, 
flip each of the n bits and check if the resulting vector is a valid codeword.  If so, we have 
successfully decoded from one error.  If none of the checks are successful, then we declare 
a  decoding  failure.  Algorithm  2.5.1  formally  presents  this  algorithm  (where  CH,r  is  the 
[2r − 1, 2r − r − 1, 3]2 Hamming code).5

It can be verified that Algorithm 2.5.1 can correct up to 1 error.  If each of the checks 
y′ ∈ CH,r can be done in T (n) time, then the time complexity of the proposed algorithm 
will be O(nT (n)).  Note that since CH,r is a linear code (and dimension k = n − O(log n)) 
by Proposition 2.3.5, we have T (n) = O(n log n). Thus, the proposed algorithm has running 
time O(n2 log n).

Note that Algorithm 2.5.1 can be generalized to work for any linear code C with distance 
2t + 1 (and hence, can correct up to t errors):  go through all possible error vectors z ∈ [q]n

5Formally speaking, a decoding algorithm should return the transmitted message x but Algorithm 2.5.1 
actually returns CH,r(x).  However, since CH,r is a linear code, it is not too hard to see that one can obtain 
x  from  CH,r(x)  in  O(n3)  time:  see  Exercise  2.25.  Further,  for  CH,r  one  can  do  this  in  O(n)  time:  see 
Exercise 2.26.

37

 


<!-- pdf-page: 50 -->
Algorithm 2.5.1 Naive Decoder for Hamming Code
Input: Received word y
Output: c if ∆(y, c) ≤ 1 else Fail
1: if y ∈ CH,r then
return y
2:  
3: for i = 1 . . . n do
y′ ← y + ei
4:  
if y′ ∈ CH,r then
5:  
return y′
6:  
7: return Fail

▷ ei is the ith standard basis vector

(with wt(z) ≤ t) and check if y − z is in the code or not. Algorithm 2.5.2 presents the formal 
algorithm (where C is an [n, k, 2t + 1]q code).

Algorithm 2.5.2 Decoder for Any Linear Code
Input: Received word y
Output: c ∈ C if ∆(y, c) ≤ t else Fail
1: for i = 0 . . . t do
2:  
3:  
4:  
5:  
6: return Fail

if y − z ∈ C then
return y − z

for S ⊆ [n] such that |S| = i do

for z ∈ Fn

q  such that wt(zS) = wt(z) = i do

The number of error patterns z considered by Algorithm 2.5.2 is6 ∑︁t

)︁(q − 1)i ≤
O((nq)t). Furthermore by Proposition 2.3.5, Step 4 can be performed with O(n2) operations 
over Fq.  Thus, Algorithm 2.5.2 runs with O(nt+2qt) operations over Fq, which for q being a 
small polynomial in n, is nO(t) operations. In other words, the algorithm will have polynomial 
running  time  for  codes  with  a  constant  distance  (though  the  running  time  would  not  be 
practical even for moderate values of t).

(︁n
i

i=0

However, it turns out that for Hamming codes there exists a decoding algorithm with an 
O(n2) running time.  To see this, first note that if the received word y has no errors, then 
Hr · yT = 0.  If not, then y = c + ei, where c ∈ C and ei is the unit vector with the only 
nonzero element at the i-th position.  Thus, if Hi

r stands for the i-th column of Hr,

Hr · yT = Hr · cT + Hr · (ei)T = Hr · (ei)T = Hi
r,

where the second equality follows as Hr · cT = 0, which in turn follows from the fact that 
c ∈ C.  In other words, Hr · yT  gives the location of the error.  This leads to Algorithm 2.5.3.
Note that Hr is an r × n matrix where n = 2r − 1 and thus, r = Θ(log n).  This implies 
Step  1  in  Algorithm  2.5.3,  which  is  a  matrix  vector  multiplication  can  be  done  in  time 

6Recall (1.18).

38



<!-- pdf-page: 51 -->
Algorithm 2.5.3 Efficient Decoder for Hamming Code
Input: Received word y
Output: c if ∆(y, c) ≤ 1 else Fail
1: b ← Hr · yT . 
2: Let i ∈ [n] be the number whose binary representation is b
3: if y − ei ∈ CH then 
4:  
5: return Fail

return y − ei

O(n log n).  By  a  similar  argument  and  by  Proposition  2.3.5  Step  3  can  be  performed  in 
O(n log n) time, and therefore Algorithm 2.5.3 overall runs in O(n log n) time.  Thus,

Theorem  2.5.1.  The  [n = 2r − 1, 2r − r − 1, 3]2  Hamming  code  is  1-error  correctable. 
Furthermore, decoding can be performed in time O(n log n).

2.6  Dual of a Linear Code

Until  now,  we  have  thought  of  parity  check  matrix  as  defining  a  code  via  its  null  space. 
However, we are not beholden to think of the parity check matrix in this way.  A natural 
alternative is to use the parity check matrix as a generator matrix.  The following definition 
addresses this question.

Definition 2.6.1   (Dual of a code). Let H be a parity check matrix of a code C, then the 
code generated by H is called the dual of C.  The dual of a code C is denoted by C ⊥.

It is obvious from the definition that if C is an [n, k]q code, then C ⊥ is an [n, n − k]q
code.  Applying duality to the Hamming codes and a close relative, we get two families of 
codes described below.

Definition 2.6.2  (Simplex and Hadamard Codes). For positive integer r the Simplex Code 
CSim,r is the code generated by Hr.  (Equivalently CSim,r = C ⊥
H,r.)  For positive integer r the 
Hadamard Code  CHad,r is the [2r, r]2 code generated by the r × 2r matrix H ′
r obtained by 
adding the all zero column to (say in front of columns in) Hr.

We claim that CSim,r and CHad,r are [2r − 1, r, 2r−1]2 and [2r, r, 2r−1]2 codes respectively. 
The claimed block length and dimension follow from the definition of the codes, while the 
distance follows from the following result.

Proposition 2.6.3. CSim,r and CHad,r both have distances of 2r−1.

Proof.  We  first  show  the  result  for  CHad,r.  In  fact,  we  will  show  something  stronger: 
every non-zero codeword in CHad,r has weight exactly equal to 2r−1 (the claimed distance 

39



<!-- pdf-page: 52 -->
follows from Proposition 2.3.6).  Consider a message x ̸= 0.  Let its ith entry be xi = 1.  x is 
encoded as

c = (x1, x2, . . . , xr)(H 0

r , H 1
r  is the binary representation of 0 ≤ j ≤ 2r − 1 (that is, the set set of vector H j

where H j
r  is 
exactly the set of all the vectors in {0, 1}r). Further note that the jth bit of the codeword c is 
⟨x, H j
r ⟩. Group all the columns of the generator matrix into pairs (u, v) such that v = u + ei
(i.e.  v and u are the same except in the ith position).  For example for r = 3 and i = 2, the 
paired up columns are marked with the same color below:

r , . . . , H 2r−1

),

r

⎛

⎝

0 0 0 0 1 1 1 1
0 0 1 1 0 0 1 1
0 1 0 1 0 1 0 1

⎞

⎠

Notice that this partitions all the columns into 2r−1 disjoint pairs.  Then,

⟨x, v⟩ = ⟨x, u + ei⟩ = ⟨x, u⟩ + ⟨x, ei⟩ = ⟨x, u⟩ + xi = ⟨x, u⟩ + 1.

Thus we have that ⟨x, v⟩ is the negation of ⟨x, u⟩, i.e. exactly one of ⟨x, v⟩ and ⟨x, u⟩ is 1. As 
the choice of the pair (u, v) was arbitrary, we have proved that for any non-zero codeword c
such that c ∈ CHad,r, wt(c) = 2r−1.

For the simplex code, we observe that all codewords of CHad,r are obtained by padding a 
0 to the beginning of the codewords in CSim,r, which implies that all non-zero codewords in 
CSim,r also have a weight of 2r−1, which completes the proof.

We remark that the family of Hamming code has a rate of 1 and a (relative) distance of 0
while the families of Simplex/Hadamard codes have a rate of 0 and a relative distance of 1/2. 
Thus neither gives a positive answer to Question 1.8.3 and so the quest for an asymptotically 
good code remains ongoing for now (and we will get to these in future chapters).

2.7  Exercises

Exercise 2.1. Let (S, +, ·) be a field (as per Definition 2.1.2). Then argue that a·0 = 0·a = 0
for every a ∈ S.

Exercise 2.2. Prove that the set of rationals (i.e.  the set of reals of the form  a
a and b ̸= 0 are integers), denoted by Q, is a field.

b , where both 

Exercise 2.3. Let q be a prime power.  Let x ∈ Fq such that x ̸∈ {0, 1}.  Then prove that for 
any n ≤ q − 1:

n
∑︂

i=0

xi =

xn+1 − 1
x − 1

.

40

 


<!-- pdf-page: 53 -->
Exercise 2.4. The main aim of this exercise is to prove the following identity that is true 
for any α ∈ Fq:

αq = α

(2.4)

To make progress towards the above we will prove a sequence of properties of groups.  A 
group G is a pair (S, ◦) where the operator ◦ : G × G → G such that ◦ is commutative7 and 
the elements of S are closed under ◦.  Further, there is a special element ι ∈ S that is the 
identity element and every element a ∈ S has an inverse element b ∈ S such that a ◦ b = ι. 
Note that a finite field Fq consists of an additive group with the + operator (and 0 as additive 
identity) and a multiplicative group on the non-zero elements of Fq (which is also denoted 
by F∗

q) with the · operator (and 1 as the multiplicative identity).8
For the rest of the problem let G = (S, ·) be a multiplicative group with |G| = m.  Prove 

the following statements.

1. For any β ∈ G, let o(β) be the smallest integer o such that βo = 1.  Prove that such 
an o ≤ m always exists.  Further, argue that T = {1, β, . . . , βo−1} also forms a group. 
(T, ·) is called a sub-group of G and o(β) is called the order of β.

2. For any g ∈ G, define the coset (w.r.t.  T ) as

gT = {g · β|β ∈ T }.

Prove that if h−1 · g ∈ T  then gT = hT  and gT ∩ hT = ∅ otherwise.  Further argue that 
these cosets partition the group G into disjoint sets.

3. Argue that for any g ∈ G, we have |gT | = |T |.

4. Using the above results or otherwise, argue that for any β ∈ G, we have

βm = 1.

5. Prove (2.4).

Exercise 2.5. Prove that for q = 2, the second condition in Definition 2.2.2 is implied by 
the first condition.

Exercise 2.6. Prove that G2 from (2.3) has full rank.

Exercise  2.7.  In  this  problem  we  will  look  at  the  problem  of  solving  a  system  of  linear 
equations over Fq.  That is, one needs to solve for unknowns x1, . . . , xn given the following 
m linear equations (where ai,j, bi ∈ Fq for 1 ≤ i ≤ m and 1 ≤ j ≤ n):

a1,1x1 + a1,2x2 + · · · + a1,nxn = b1.

7Technically, G is an abelian group.
8Recall Definition 2.1.2.

41



<!-- pdf-page: 54 -->
a2,1x1 + a2,2x2 + · · · + a2,nxn = b2.
...
am,1x1 + am,2x2 + · · · + am,nxn = bm.

1. (Warm-up) Convince yourself that the above problem can be stated as A · xT = bT , 

where A is an m × n matrix over Fq, x ∈ Fn

q  and b ∈ Fm
q .

2. (Upper Triangular Matrix) Assume n = m and that A is upper triangular,  i.e.  all 
diagonal elements (ai,i) are non-zero and all lower triangular elements (ai,j, i > j) are 
0.  Then present an O(n2) time9 algorithm to compute the unknown vector x.

3. (Gaussian Elimination) Assume that A has full rank (or equivalently a rank of n.)

(a) Prove that the following algorithm due to Gauss converts A into an upper trian­
gular matrix.  By permuting the columns if necessary make sure that a1,1 ̸= 0. 
(Why can one assume w.l.o.g. that this can be done?) Multiply all rows 1 < i ≤ n
with  a1,1
 and then subtract a1,j from the (i, j)th entry 1 ≤ j ≤ n.  Recurse with 
ai,1
the same algorithm on the (n − 1) × (n − 1) matrix A′ obtained by removing the 
first row and column from A.  (Stop when n = 1.)

(b) What  happens  if  A  does  not  have  full  rank?  Show  how  one  can  modify  the 
algorithm above to either upper triangulate a matrix or report that it does not 
have full rank.  (Convince yourself that your modification works.)

(c) Call a system of equations A · xT = bT  consistent if there exists a solution to 
x ∈ Fn
q .  Show that there exists an O(n3) algorithm that finds the solution if the 
system of equations is consistent and A has full rank (and report “fail” otherwise).

4. (m < n case) Assume that A has full rank, i.e.  has a rank of m.  In this scenario 
either the system of equations is inconsistent or there are qn−m solutions to x.  Modify 
the algorithm from above to design an O(m2n) time algorithm to output the solutions 
(or report that the system is inconsistent).

• Note  that  in  case  the  system  is  consistent  there  will  be  qn−m  solutions,  which 
might be much bigger than O(m2n).  Show that this is not a problem as one can 
represent the solutions as system of linear equations.  (I.e.  one can have n − m
“free” variables and m “bound” variables.)

5. (m > n case) Assume that A has full rank, i.e.  a rank of n.  In this scenario either 
the system of equations is inconsistent or there is a unique solution to x.  Modify the 
algorithm from above to design an O(m2n) time algorithm to output the solution (or 
report that the system is inconsistent).

9For this problem, any basic operation over Fq takes unit time.

42



<!-- pdf-page: 55 -->
6. (Non-full rank case) Give an O(m2n) algorithm for the general case, i.e.  the m × n
matrix A need not have full rank.  (The algorithm should either report that the system 
of equations is inconsistent or output the solution(s) to x.)

Exercise 2.8. Prove that the span of k linearly independent vectors over Fq has size exactly 
qk.

Exercise 2.9. Let G and H be a generator and parity check matrix of the same linear code 
of dimension k and block length n.  Then G · H T = 0.

Exercise 2.10. Let C be an [n, k]q linear code with a generator matrix with no all zeros 
columns.  Then for every position i ∈ [n] and α ∈ Fq, the number of codewords c ∈ C such 
that ci = α is exactly qk−1.

Exercise 2.11. Prove Proposition 2.3.3.

Exercise 2.12. Prove Proposition 2.3.4.

Exercise 2.13. Prove Proposition 2.3.5.

Exercise  2.14.  A  set  of  vector  S ⊆ Fn
q   is  called  t-wise  independent  if  for  every  set  of 
positions I with |I| = t, the set S projected to I has each of the vectors in Ft
q appear the 
same number of times.  (In other words,  for every choice of I ⊆ [n] with |I| = t,  if one 
picks a vector (X1, . . . , Xn) uniformly at random from S then the variables {Xi|i ∈ I} are 
distributed uniformly and independently random over Fq).

Prove that any linear code C whose dual C ⊥ has distance d⊥ is (d⊥ −1)-wise independent.

Exercise  2.15. A  set  of  vectors  S ⊆ Fk
2  is  called  ε-biased  sample  space  if  the  following 
property holds.  Pick a vector X = (x1, . . . , xk) uniformly at random from S.  Then X has 
bias at most ε, that is, for every I ⊆ [k],

⃓
⃓
⃓
⃓
⃓

Pr

(︄

∑︂

i∈I

)︄

xi = 0

− Pr

(︄

∑︂

i∈I

xi = 1

)︄⃓
⃓
⃓
⃓
⃓

≤ ε.

We will look at some connections of such sets to codes.

1. Let C be an [n, k]2 code such that all non-zero codewords have Hamming weight in the 

range [︁(︁ 1−ε

)︁ n, (︁ 1+ε

)︁ n]︁.  Then there exists an ε-biased space of size n in Fk
2.

2

2

2. Let  C be an  [n, k]2 code such that all  non-zero codewords have  Hamming weight in 
2 + γ)︁ n]︁ for some constant 0 < γ < 1/2.  Then there exists an 

2 − γ)︁ n, (︁ 1

the range [︁(︁ 1
ε-biased space in Fk

2 of size nO(γ−1·log(1/ε)).

43



<!-- pdf-page: 56 -->
Exercise 2.16. Let C be an [n, k, d]q code.  Let y = (y1, . . . , yn) ∈ (Fq ∪ {?})n be a received 
word10 such that yi =? for at most d − 1 values of i.  Present an O(n3) time algorithm that 
outputs a codeword c = (c1, . . . , cn) ∈ C that agrees with y in all un-erased positions (i.e., 
ci = yi if yi ̸=?) or states that no such c exists.  (Recall that if such a c exists then it is 
unique.)

Exercise 2.17. In the chapter, we did not talk about how to obtain the parity check matrix 
of a linear code from its generator matrix.  In this problem, we will look at this “conversion” 
procedure.

(a) Prove that any generator matrix G of an [n, k]q code C (recall that G is a k × n matrix) 
can be converted into another equivalent generator matrix of the form G′ = [Ik|A], where 
Ik is the k × k identity matrix and A is some k × (n − k) matrix.  By “equivalent,” we 
mean that the code generated by G′ has a linear bijective map to C.
Note that the code generated by G′ has the message symbols as its first k symbols in the 
corresponding codeword.  Such codes are called systematic codes.  In other words, every 
linear code can be converted into a systematic code.  Systematic codes are popular in 
practice as they allow for immediate access to the message symbols.

(b) Given an k × n generator matrix of the form [Ik|A], give a corresponding (n − k) × n
parity check matrix.  Briefly justify why your construction of the parity check matrix is 
correct.

Hint:  Try  to  think  of  a  parity  check  matrix  that  can  be  decomposed  into  two  submatrices:  one 
will be closely related to A and the other will be an identity matrix, though the latter might not be a 
k × k matrix).

(c) Use part (b) to present a generator matrix for the [2r − 1, 2r − r − 1, 3]2 Hamming code.

Exercise 2.18. So far in this book we have seen that one can modify one code to get another 
code with interesting properties (for example, the construction of the Hadamard code from 
the Simplex code from Section 2.6 and Exercise 1.7).  In this problem you will need to come 
up with more ways of constructing new codes from existing ones.

Prove the following statements (recall that the notation (n, k, d)q code is used for general 
codes with qk codewords where k need not be an integer, whereas the notation [n, k, d]q code 
stands for a linear code of dimension k):

1. If there exists an (n, k, d)2m code, then there also exists an (nm, km, d′ ≥ d)2 code.

2. If there exists an [n, k, d]2m code, then there also exists an [nm, km, d′ ≥ d]2 code.

3. If there exists an [n, k, d]q code, then there also exists an [n − d, k − 1, d′ ≥ ⌈d/q⌉]q code.

10A ? denotes an erasure.

44



<!-- pdf-page: 57 -->
4. If there exists an [n, k, δn]q code, then for every m ≥ 1, there also exists an

(nm, k/m, (1 − (1 − δ)m) · nm)qm code.

5. If there exists an [n, k, δn]2 code, then for every odd m ≥ 1, there also exists an

[︁nm, k, 1

2 · (1 − (1 − 2δ)m) · nm]︁

2 code.

Note:    In all the parts, the only things that you can assume about the original code are only 
the parameters given by its definition– nothing else!

Exercise 2.19. Let C1 be an [n, k1, d1]q code and C2 be an [n, k2, d2]q code.  Then define a 
new code as follows:

C1 ⊖ C2 = {(c1, c1 + c2)|c1 ∈ C1, c2 ∈ C2}.

Next we will prove interesting properties of this operations on codes:

1. If Gi is the generator matrix for Ci for i ∈ [2], what is a generator matrix for C1 ⊖ C2?

2. Argue that C1 ⊖ C2 is an [2n, k1 + k2, d def= min(2d1, d2)]q code.

3. Assume there exists algorithms Ai for code Ci for i ∈ [2] such that:  (i) A1 can decode 
from  e  errors  and  s  erasures  such  that  2e + s < d1  and  (ii)  A2  can  decode  from 
⌊(d2 − 1)/2⌋ errors.  Then argue that one can correct ⌊(d − 1)/2⌋ errors for C1 ⊖ C2.
Hint:  Given a received word (y1, y2) ∈ Fn
received word for A1.

q , first apply A2 on y2 − y1. Then create an intermediate 

q × Fn

4. We will now consider a recursive construction of a binary linear code that uses the ⊖

operator.  For integers 0 ≤ r ≤ m, we define the code C(r, m) as follows:

• C(r, r) = Fr

zeroes vector in Fr
2.

2 and C(0, r) is the code with only two codewords: the all ones and all 

• For 1 < r < m, C(r, m) = C(r, m − 1) ⊖ C(r − 1, m − 1).

Determine the parameters of the code C(r, m).

Exercise 2.20. Let C1 be an [n1, k1, d1]2 binary linear code, and C2 an [n2, k2, d2] binary 
linear code.  Let C ⊆ Fn1×n2
 be the subset of n2 × n1 matrices whose rows belong to C1 and 
whose columns belong to C2.  C is called the tensor of C1 and C2 and is denoted by C1 ⊗ C2.

2

Prove that C is an [n1n2, k1k2, d1d2]2 binary linear code.
Further, if G1 and G2 are generator matrices of C1 and C2, construct a genertor matrix 
of C1 ⊗ C2 from G1 and G2.  In particular, argue that given G1 and G2, a generator matrix 
of C1 ⊗ C2 can be computed in polynomimal time.
Hint:  For the latter problem, it might be useful to think of the codewords and messages as vectors instead of 
matrices.

45



<!-- pdf-page: 58 -->
Exercise 2.21. In Section 2.4 we considered the binary Hamming code.  In this problem we 
will consider the more general q-ary Hamming code.  In particular, let q be a prime power 
and r ≥ 1 be an integer.  Define the following r × n matrix Hq,r, where each column is an 
non-zero vector from Fr

q such that the first non-zero entry is 1.  For example,
(︃0 1 1 1
1 0 1 2

H3,2 =

)︃

In this problem we will derive the parameters of the code.  Define the generalized Hamming 
code CH,r,q to be the linear code whose parity check matrix is Hq,r.  Argue that

1. The block length of CH,r,q is n = qr−1
q−1 .

2. CH,q,r has dimension n − r.

3. CH,q,r has distance 3.

Exercise 2.22. In Section 2.6, we considered the binary Hadamard code. In this problem we 
will consider the more general q-ary Hadamard code.  In particular, let q be a prime power 
and r ≥ 1 be an integer.  Define the following r × qr matrix H q,r, where each columns in a 
vector in Fr
q. In this problem we will derive the parameters of the code. Define the generalized 
Hadamard code CHad,r,q to be the linear code whose parity check matrix is H q,r.  Argue that

1. The block length of CHad,r,q is n = qr.

2. CHad,q,r has dimension r.

3. CHad,q,r has distance 

(︂

)︂

· n.

1 − 1
q

Exercise 2.23. Design the best 6-ary code (family) with distance 3 that you can.

Hint:  Start with a 7-ary Hamming code.

Exercise 2.24. Prove that the [n, 1, n]2 code for odd n (i.e.  the code with the all zeros and 
all ones vector as it only two codewords) attains the Hamming bound (Theorem 1.7.2).

Exercise 2.25. Let C be an [n, k]q code with generator matrix G.  Then given a codeword 
c ∈ C one can compute the corresponding message in time O(kn2).

Exercise 2.26. Given a c ∈ CH,r, one can compute the corresponding message in time O(n).

Exercise 2.27. Let C be an (n, k)q code.  Prove that if C can be decoded from e errors in 
time T (n), then it can be decoded from n + c errors in time O((nq)c · T (n)).

Exercise 2.28. Show that the bound of kd of the number of ones in the generator matrix of 
any binary linear code (see Exercise 1.14) cannot be improved for every code.

46



<!-- pdf-page: 59 -->
Exercise 2.29. Let C be a linear code.  Then prove that (︁C ⊥)︁⊥ = C.

Exercise 2.30. Note that for any linear code C, the codewords 0 is in both C and C ⊥. Show 
that there exists a linear code C such that it shares a non-zero codeword with C ⊥.

Exercise 2.31. We go into a bit of diversion and look at how finite fields are different from 
infinite fields (e.g. R). Most of the properties of linear subspaces that we have used for linear 
codes (e.g.  notion of dimension, the existence of generator and parity check matrices, notion 
of duals) also hold for linear subspaces over R.11  One trivial property that holds for linear 
subspaces over finite fields that does not hold over R is that linear subspaces over Fq with 
dimension k has size qk (though this is a trivial consequence that Fq is a finite field while R
is an infinite field).  Next, we consider a more subtle distinction.

Let S ⊆ Rn be a linear subspace over R and let S⊥ is the dual of S.  Then show that

S ∩ S⊥ = {0} .

By contrast,  linear subspaces over finite fields can have non-trivial intersection with their 
duals (see e.g.  Exercise 2.30).

Exercise 2.32. A linear code C is called self-orthogonal if C ⊆ C ⊥.  Show that

1. The binary repetition code with even number of repetitions is self-orthogonal.

2. The Hadamard code CHad,r is self-orthogonal.

Exercise 2.33. A linear code C is called self dual if C = C ⊥.  Show that for

1. Any self dual code has dimension n/2.

2. Prove that the following code is self-dual

{(x, x)|x ∈ Fk

2}.

Exercise 2.34. Given a code C a puncturing of C is another code C ′ where the same set 
of positions are dropped in all codewords of C.  More precisely, if C ⊆ Σn and the set of 
punctured positions is P ⊆ [n], then the punctured code is {(ci)i̸∈P |(c1, . . . , cn) ∈ C}.

Prove that a linear code with no repetitions (i.e. there are no two positions i ̸= j such that 
for every codeword c ∈ C, ci = ci) is a puncturing of the Hadamard code.  Hence, Hadamard 
code is the “longest” linear code that does not repeat.

11A linear subspace S ⊆ Rn is the same as in Definition 2.2.2 where all occurrences of the finite field Fq

is replaced by R.

47



<!-- pdf-page: 60 -->
Exercise 2.35. In this problem we will consider the long code.  For the definition, we will 
use the functional way of looking at the ambient space as mentioned in Remark 1.2.2.  A 
long code of dimension k is a binary code such that the codeword corresponding to x = Fk
2, 
is  the  function  f : {0, 1}2k → {0, 1}  defined  as  follows.  For  any  m ∈ {0, 1}Fk
2 ,  we  have 
f ((mα)α∈Fk

) = mx.  Derive the parameters of the long code.

Finally, argue that the long code is the code with the longest block length such that the 
codewords do not have a repeated coordinate (i.e.  there does not exists i ̸= j such that for 
every codeword c, ci = cj).  (Contrast this with the property of Hadamard code above.)

2

Exercise  2.36. Given  a  linear  code  C ⊆ Fn
2 ,  define  its  generating  function  to  be  a  2n-
variate polynomial over variables x = (x1, . . . , xn) and y = (y1, . . . , yn) given by GC(x, y) =
∑︁
.  For w ∈ {0, . . . , n}, 
Czw  be  the 

C  denote  the  number  of  codewords  of  weight  w  and  let  AC(z) = ∑︁n

w∈C Pw(x, y) where Pw(x, y) =

{i∈[n]|wi=0} xi

{i∈[n]|wi=1} yi

w=0 Aw

(︂∏︁

(︂∏︁

)︂

)︂

·

let  Aw
“weight enumerator” polynomial of C.

1. For every w ∈ Fn

2 , prove that Pw(x + y, x − y) = ∑︁

v∈Fn
2

(−1)⟨v,w⟩Pv(x, y).

2. Prove that GC⊥(x, y) = 1

|C| GC(x + y, x − y).

3. Prove that AC(z) = GC(1, . . . , 1, z, . . . , z).

4. Prove that AC⊥(z) = (1+z)n

|C| AC

(︁ 1−z
1+z

)︁.

5. Conclude  that  Aw

C⊥ = 1

|C|

tributions  of  the  weights  (A0
distributions of weights (A0

∑︁n

(︁∑︁u

u=0 Au
C
C, . . . , An
C⊥, . . . , An

)︁(︁n−u
w−i

i=0(−1)i(︁u

)︁)︁.  In  other  words,  the  dis­
C)  of  the  primal  code  completely  determine  the 
C⊥) of the dual code!

i

2.8  Bibliographic Notes

The background material on algebra is essentially folklore.  Readers interested in a more 
extensive treatment are referred to classical texts such as by Artin [3].  For a perspective 
focussing more on finite fields, see the text by Lidl and Niederreiter [47].  Linear codes arose 
already in the paper of Hamming [35] and were systematically studied by Slepian [69].  The 
answer to Question 1.7.4 was given by van Lint [72] and Tietavainen [71].  Hadamard codes 
(Definition  2.6.2)  are  named  after  the  work  of  mathematician  Jacques  Hadamard  and  in 
particular the notion of Hadamard matrices which are self-orthogonal matrices with +1/-1 
entries.

Exercises 2.14 and 2.15 come from the theory of pseudorandomness, which we will cover 
more extensively in Chapter ??. The long codes in Exercise 2.35 were introduced by Bellare, 
Goldreich  and  Sudan  [5].  Exercise  2.36  is  based  on  the  MacWilliams  Identity  proved  by 
MacWilliams [48].

48



<!-- pdf-page: 61 -->
Chapter 3

Probability as Fancy Counting and 
the q-ary Entropy Function

In the chapters to come we will explore questions of the form:  “Given n, k, d and q does an 
(n, k, d)q code exist?” To answer such questions, we will apply the “probabilistic method” — 
the method that demonstrates the existence of an object with a given property by showing 
that a randomly chosen object has the property with positive probability.  To elaborate on 
this sentence, we need to introduce the basic language and tools of probability theory which 
we do in Section 3.1.

We then introduce the probabilistic method in Section 3.2.  We even apply the method 

to answer a very simple question:

Question 3.0.1. Does there exist a [2, 2, 1]2 code?

We note that the answer to the above question is trivially yes:  just pick the generator 
matrix to be the 2 × 2 identity matrix. But our proof will have the advantage of generalizing 
to broader settings, though we save the generalizations for later chapters.

Finally in Section 3.3 we introduce the “entropy function” which turns out to be central 

in the understanding of limits of codes (both existence and non-existence).

3.1  A Crash Course on Probability

In this section we review basic concepts in probability theory, specialized to the needs of this 
book.  Specifically„ we introduce distributions, events and random variables, and give some 
tools to analyze them.

In this book, we will only consider probability distributions defined over finite spaces. In 

particular, given a finite domain D, a probability distribution is defined as a function

p : D → [0, 1] such that 

p(x) = 1,

∑︂

x∈D

where [0, 1] is shorthand for the interval of all real numbers between 0 and 1.

49



<!-- pdf-page: 62 -->
G
M0,0,0,0
M0,0,0,1
M0,0,1,0
M0,0,1,1
M0,1,0,0
M0,1,0,1
M0,1,1,0
M0,1,1,1

U(G) V00 V01 V10 V11
0
0
1
1
1
1
2
2
1
0
0
1
2
1
1
2

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
1
1
1
1

1
16
1
16
1
16
1
16
1
16
1
16
1
16
1
16

G
M1,0,0,0
M1,0,0,1
M1,0,1,0
M1,0,1,1
M1,1,0,0
M1,1,0,1
M1,1,1,0
M1,1,1,1

U(G) V00 V01 V10 V11
1
0
2
1
0
1
1
2
2
0
1
1
1
1
0
2

0
0
0
0
0
0
0
0

1
1
1
1
2
2
2
2

1
16
1
16
1
16
1
16
1
16
1
16
1
16
1
16

Table  3.1:  Uniform  distribution  over  F2×2
(Eq. (3.1) defines the notation used in the G/first column of the tables.)

2

  along  with  values  of  four  random  variables. 

An event E is a predicate over the domain D, i.e.  it maps every element of D to “true” 
or  “false”.  Equivalently  an  event  is  a  subset  of  the  domain  D,  i.e.,  those  elements  that 
are  mapped  to  true.  We  switch  between  “logical”  or  ”set-theoretic”  notation  to  denote 
combinations of events.  So the disjunction of events E1 and E2 may be denoted E1 ∨ E2 or 
E1 ∪ E2.  Similarly, the conjunction of E1 and E2 may be denoted E1 ∧ E2 or E1 ∩ E2; and 
the negation of E1 may be denote ¬E1 or E1.

In this book, we will primarily deal with the following special distribution:

Definition 3.1.1  (Uniform Distribution). The uniform distribution over D, denoted by U D, 
is given by

1
|D|
Typically, we will drop the subscript when the domain D is clear from the context.

 for every x ∈ D.

(x) =

Pr
U D

For example, consider the domain D = F2×2

, i.e.  the set of all 2 × 2 matrices over F2. 
2
(Note that each such matrix is a generator matrix of some [2, 2]2 code.) The first two columns 
of Table 3.1 list the elements of this D along with the corresponding probabilities for the 
uniform distribution, with Mb00,b10,b10,b11 denoting the following matrix

Mb00,b10,b10,b11 =

(︃b00
b10

)︃

.

b10
b11

(3.1)

Typically, we will be interested in a real-valued function defined on D and how it behaves 
under a probability distribution defined over D.  This is captured by the notion of a random 
variable1:
Definition  3.1.2   (Random  Variable). Let  D  be  a  finite  domain  and  I ⊂ R  be  a  finite2 
subset.  Let p be a probability distribution defined over D.  A random variable is a function:
V : D → I.

1We note that the literature on probability theory allows for more general random variables, but for our 

purposes we restrict only to real-valued ones.

2In general, I need not be finite.  However, for this book this definition suffices.

50



<!-- pdf-page: 63 -->
The expectation of V  is defined as

E[V ] =

∑︂

x∈D

p(x) · V (x).

For example, given (i, j) ∈ {0, 1}2, let Vij denote the random variable Vij(G) = wt ((i, j) · G), 

.  The last four columns of Table 3.1 list the values of these four random 

for any G ∈ F2×2
variables.

2

Of particular interest in this book will be binary random variables, i.e., with I = {0, 1}. 
In particular, given an event E over D, we will define its indicator variable to be a function 
⊮E : D → {0, 1} such that for any x ∈ D:

⊮E(x) =

{︄
1
0

 if x ∈ E
 otherwise.

For example,

⊮V01=0

)︃)︃

(︃(︃0 1
0 0

= 1 and ⊮V01=0

)︃)︃

(︃(︃0 1
1 1

= 0.

In most cases we will shorten this notation to ⊮E(x) or simply ⊮E.  Finally, sometimes we 
will abuse notation and use E instead of ⊮E.

As a further use of indicator variables, consider the expectations of the four indicator 

variables:

E [⊮V00=0] = 16 ·

= 1.

1
16

E [⊮V01=0] =

E [⊮V10=0] =

E [⊮V11=0] =

4 ·

4 ·

4 ·

1
16
1
16
1
16

=

=

=

1
4
1
4
1
4

.

.

.

(3.2)

(3.3)

(3.4)

3.1.1  Some Useful Results

Before we proceed, we record a simple property of indicator variables that will be useful. 
(See Exercise 3.1.)

Lemma 3.1.3. Let E be any event.  Then

E [⊮E] = Pr [E is true] .

Next, we state a simple yet useful property of expectation of a sum of random variables:

51



<!-- pdf-page: 64 -->
Proposition 3.1.4  (Linearity of Expectation). Given random variables V1, . . . , Vm defined 
over the same domain D and with the same probability distribution p, we have
[︄ m
∑︂

m
∑︂

]︄

E

Vi

=

E [Vi] .

Proof. 

For notational convenience, define V = V1 + · · · + Vm.  Thus, we have

i=1

i=1

E[V ] =

=

=

=

∑︂

x∈D

∑︂

x∈D
m
∑︂

i=1
m
∑︂

i=1

V (x) · p(x)

)︄

Vi(x)

· p(x)

(︄ m
∑︂

i=1

∑︂

x∈D

Vi(x) · p(x)

E[Vi].

(3.5)

(3.6)

(3.7)

(3.8)

In the equalities above, (3.5) and (3.8) follow from the definition of expectation of a random 
variable.  (3.6) follows from the definition of V  and (3.7) follows by switching the order of 
the two summations.

As an example, we have

E [⊮V01=0 + ⊮V10=0 + ⊮V11=0] =

3
4

(3.9)

Frequently, we will need to deal with the probability of the union of events.  We will use 

the following result to upper bound such probabilities:

Proposition 3.1.5  (Union Bound). Given m binary random variables A1, . . . , Am, we have
]︄

)︄

[︄(︄ m
⋁︂

m
∑︂

Pr

Ai

= 1

≤

Pr [Ai = 1] .

Proof. 

For every i ∈ [m], define

i=1

i=1

Si = {x ∈ D|Ai(x) = 1}.

Then we have

Pr

[︄(︄ m
⋁︂

i=1

)︄

]︄

Ai

= 1

=

≤

=

52

∑︂

p(x)

i=1Si

x∈∪m
m
∑︂

∑︂

p(x)

x∈Si

Pr[Ai = 1].

i=1
m
∑︂

i=1

(3.10)

(3.11)

(3.12)

 


<!-- pdf-page: 65 -->
In the above, (3.10) and (3.12) follow from the definition of Si.  (3.11) follows from the fact 
that some of the x ∈ ∪iSi get counted more than once.

We remark that the union bound is tight when the events are disjoint.  (In other words, 

using the notation in the proof above, when Si ∩ Sj = ∅ for every i ̸= j.)

As an example, let A1 = ⊮V01=0, A2 = ⊮V10=0 and A3 = ⊮V11=0.  Note that in this case 
the event A1 ∨ A2 ∨ A3 is the same as the event that there exists a non-zero m ∈ {0, 1}2 such 
that wt(m · G) = 0.  Thus, the union bound implies (that under the uniform distribution 
over F2×2

)

2

Pr [︁There exists an m ∈ {0, 1}2 \ {(0, 0)},  such that wt(mG) = 0]︁ ≤

3
4

.

(3.13)

Finally, we present three bounds on the probability of a random variable deviating sig­

nificantly from its expectation.  The first bound holds for any random variable:

Lemma 3.1.6   (Markov Bound). Let V  be a non-negative random variable.  Then for any 
t > 0,

In particular, for any a ≥ 1,

Pr[V ≥ a · E[V ]] ≤

Pr[V ≥ t] ≤

E[V ]
t

.

1
a

.

The second bound follows from the first bound by substituting t = a · E[V ]. Thus, 
Proof. 
to complete the proof, we argue the first bound. Consider the following sequence of relations:

∑︂

i∈[t,∞)

i · Pr[V = i]

E[V ] =

∑︂

i · Pr[V = i] +

i∈[0,t)
∑︂

i · Pr[V = i]

≥

i≥t

∑︂

≥ t ·

Pr[V = i]

i≥t
= t · Pr[V ≥ t].

(3.14)

(3.15)

(3.16)

(3.17)

In the above relations, (3.14) follows from the definition of expectation of a random variable 
and the fact that V  is non-negative.  (3.15) follows as we have dropped some non-negative 
terms. (3.16) follows by noting that in the summands i ≥ t. (3.17) follows from the definition 
of Pr[V ≥ t].

The proof is complete by noting that (3.17) implies the claimed bound.

The  second  bound  is  stated  in  terms  of  the  variance of  a  random  variable,  which  we 

define first:

53

 
 


<!-- pdf-page: 66 -->
Definition 3.1.7  (Variance). Let V  be a random variable.  Its variance is defined as

Var [V ] = E

[︂(︁V 2 − E [V ])︁2]︂

.

The standard deviation of V  is defined as σ [V ] = √︁

Var [V ].

We have the following bound:

Lemma 3.1.8   (Chebyschev Bound). Let V  be a random variable such that Var [V ] ̸= 0. 
Then for any t > 0, we have

Pr [|V − E [V ]| ≥ t] ≤

Var [V ]
t2

.

Proof. 

The claim follows from the the following sequence of relations:

Pr [|V − E [V ]| ≥ t] = Pr [︁(V − E [V ])2 ≥ t2]︁

E [︁(V − E [V ])2]︁
t2

Var [V ]
t2

.

≤

=

In the above the inequality follows from Markov’s inequality (Lemma 3.1.6) and the last 
equality follows from definition of variance.

The third bound works only for sums of independent random variables.  We begin by 

defining independent random variables:

Definition 3.1.9  (Independence). Two random variables A and B are called independent 
if for every a and b in the ranges of A and B respectively, we have

Pr[A = a ∧ B = b] = Pr[A = a] · Pr[B = b].

For example, for the uniform distribution in Table 3.1, let A denote the bit G0,0 and B
denote the bit G0,1.  It can be verified that these two random variables are independent. 
In fact, it can be verified all the random variables corresponding to the four bits in G are 
independent random variables.  (We’ll come to a related comment shortly.)

Another related concept that we will use is that of probability of an event happening 

conditioned on another event happening:

Definition 3.1.10  (Conditional Probability). Given two events A and B defined over the 
same domain and probability distribution, we define the probability of A conditioned on B as

Pr[A|B] =

Pr[A and B]
Pr[B]

.

54

 


<!-- pdf-page: 67 -->
For example, note that

Pr[⊮V01=1|G0,0 = 0] =

4/16
1/2

=

1
2

.

The above definition implies that two events A and B are independent if and only if 
Pr[A] = Pr[A|B]. We will also use the following result later on in the book (see Exercise 3.2):

Lemma 3.1.11. For any two events A and B defined on the same domain and the probability 
distribution:

Pr[A] = Pr[A|B] · Pr[B] + Pr[A|¬B] · Pr[¬B].

Next,  we  state  a  deviation  bound  that  asserts  that  the  sum  of  independent  random 
variables takes values close to its expectation with high probability.  We only state it for 
sums of binary random variables, which is the form that will be needed in the book.  We 
refer to this bound as the “Chernoff bound” though we note that this is part of a larger body 
of work and the bibliographic notes give more details.

Theorem 3.1.12  (Chernoff Bound). Let X1, . . . , Xm be independent binary random variables 
and define X = ∑︁ Xi.  Then the multiplicative Chernoff bound states that for 0 < ε ≤ 1,

Pr [|X − E(X)| > εE(X)] < 2e−ε2E(X)/3,

and the additive Chernoff bound states that

Pr [|X − E(X)| > εm] < 2e−ε2m/2.

We omit the proof, which can be found in any standard textbook on randomized algo­

rithms.

Finally,  we present an alternate view of uniform distribution over product spaces and 
then use that view to prove a result that we will use later in the book.  Given probability 
distributions p1 and p2 over domains D1 and D2 respectively, we define the product distribu­
tion p1 × p2 over D1 × D2 as follows:  every element (x, y) ∈ D1 × D2 under p1 × p2 is picked 
by choosing x from D1 according to p1 and y is picked independently from D2 under p2. This 
leads to the following observation (see Exercise 3.4).

Lemma 3.1.13. For any m ≥ 1, the distribution U D1×D2×···×Dm is identical3 to the distribu­
tion U D1 × U D2 × · · · × U Dm.

For  example,  the  uniform  distribution  in  Table  3.1  can  be  described  equivalently  as 
follows:  pick each of the four bits in G independently and uniformly at random from {0, 1}.

We conclude this section by proving the following result:

3We say two distributions p1 and p2 on D are identical if for every x ∈ D, p1(x) = p2(x).

55



<!-- pdf-page: 68 -->
Lemma 3.1.14. Given a non-zero vector m ∈ Fk
over Fq, the vector m · G is uniformly distributed over Fn
q .

q  and a uniformly random k × n matrix G

Let the (j, i)th entry in G (1 ≤ j ≤ k, 1 ≤ i ≤ n) be denoted by gji.  Note that 
Proof. 
as G is a random k × n matrix over Fq, by Lemma 3.1.13, each of the gji is an independent 
uniformly random element from Fq. Now, note that we would be done if we can show that for 
every 1 ≤ i ≤ n, the ith entry in m·G (call it bi) is an independent uniformly random element 
from Fq.  To finish the proof, we prove this latter fact.  If we denote m = (m1, . . . , mk), then 
bi = ∑︁k
j=1 mjgji.  Note that the disjoint entries of G participate in the sums for bi and bj for 
i ̸= j. Given our choice of G, this implies that the random variables bi and bj are independent. 
Hence, to complete the proof we need to prove that bi is a uniformly independent element 
of Fq.  The rest of the proof is a generalization of the argument we used in the proof of 
Proposition 2.6.3.

Note that to show that bi is uniformly distributed over Fq, it is sufficient to prove that 
bi takes every value in Fq equally often over all the choices of values that can be assigned to 
g1i, g2i, . . . , gki.  Now, as m is non-zero, at least one of the its element is non-zero.  Without 
loss of generality assume that m1 ̸= 0. Thus, we can write bi = m1g1i +∑︁k
j=2 mjgji. Now, for 
every fixed assignment of values to g2i, g3i, . . . , gki (note that there are qk−1 such assignments), 
bi takes a different value for each of the q distinct possible assignments to g1i (this is where 
we use the assumption that m1 ̸= 0).  Thus, over all the possible assignments of g1i, . . . , gki, 
bi takes each of the values in Fq exactly qk−1 times, which proves our claim.

3.2  The Probabilistic Method

The probabilistic method is a very powerful method in combinatorics which can be used to 
show the existence of objects that satisfy certain properties.  In this course, we will use the 
probabilistic method to prove existence of a code C with certain property P.  Towards that 
end,  we  define  a  distribution  D  over  all  possible  codes  and  prove  that  when  C  is  chosen 
according to D:

Pr [C has property P] > 0 or equivalently Pr [C doesn’t have property P] < 1.

Note that the above inequality proves the existence of C with property P.

As an example consider Question 3.0.1.  To answer this in the affirmative, we note that 
the set of all [2, 2]2 linear codes is covered by the set of all 2 × 2 matrices over F2.  Then, we 
let D be the uniform distribution over F2×2
.  Then by Proposition 2.3.6 and (3.13), we get 
that

2

[There is no [2, 2, 1]2 code] ≤

Pr
U F2×2
2

3
4

< 1,

which by the probabilistic method answers the Question 3.0.1 in the affirmative.

For the more general case, when we apply the probabilistic method, the typical approach 
will be to define (sub-)properties P1, . . . , Pm such that P = P1 ∧ P2 ∧ P3 . . . ∧ Pm and show 

56

 


<!-- pdf-page: 69 -->
that for every 1 ≤ i ≤ m:

Pr [C doesn’t have property Pi] = Pr [︁Pi

]︁ <

1
m

.

Finally, by the union bound, the above will prove that4 Pr [C doesn’t have property P] < 1, 
as desired.

As  an  example,  an  alternate  way  to  answer  Question  3.0.1  in  the  affirmative  is  the 
following.  Define P1 = ⊮V01≥1, P2 = ⊮V10≥1 and P3 = ⊮V11≥1.  (Note that we want a [2, 2]2
code that satisfies P1 ∧ P2 ∧ P3.)  Then, by (3.2), (3.3) and (3.4), we have for i ∈ [3],

Pr [C doesn’t have property Pi] = Pr [︁Pi

]︁ =

1
4

<

1
3

,

as desired.

Finally, we mention a special case of the general probabilistic method that we outlined 
above. In particular, let P denote the property that the randomly chosen C satisfies f (C) ≤ b. 
Then we claim (see Exercise 3.5) that E[f (C)] ≤ b implies that Pr[C has property P] > 0. 
Note that this implies that E[f (C)] ≤ b implies that there exists a code C such that f (C) ≤ b.

3.3  The q-ary Entropy Function

Finally, in this chapter we introduce a fundamental function — the “entropy” function — 
that plays a central role in the analysis of the limits of codes.  For example, in Section 4.1 
of Chapter 4 we will show how this function captures an upper bound on the rate of codes 
as a function of the relative distance.  Later in Section 4.2 of Chapter 4 we will see that this 
function captures a lower bound on the rate of codes obtained by the probabilistic method.

We begin with the definition of the entropy function.

Definition 3.3.1  (q-ary Entropy Function). Let q be an integer and x be a real number such 
that q ≥ 2 and 0 ≤ x ≤ 1.  Then the q-ary entropy function is defined as follows:

Hq(x) = x logq(q − 1) − x logq(x) − (1 − x) logq(1 − x).

Figure 3.1 presents a pictorial representation of the Hq function for the first few values 
of q.  For the special case of q = 2, we will drop the subscript from the entropy function 
and denote H2(x) by just H(x), that is, H(x) = −x log x − (1 − x) log(1 − x), where log x is 
defined as log2(x) (we are going to follow this convention for the rest of the book).

Under the lens of Shannon’s entropy function, H(x) denotes the entropy of the distri­
bution over {0, 1} that selects 1 with probability x and 0 with probability 1 − x.  However, 
there is no similar analogue for the more general Hq(x).  The reason why this quantity will 
turn out to be so central in this book is that it is very closely related to the “volume” of a 
Hamming ball.  We make this connection precise in the next subsection.

4Note that P = P1 ∨ P2 ∨ · · · ∨ Pm.

57



<!-- pdf-page: 70 -->
Figure 3.1:  A plot of Hq(x) for q = 2, 3 and 4.  The maximum value of 1 is achieved at 
x = 1 − 1/q.

3.3.1  Volume of Hamming Balls

It turns out that in many of our combinatorial results, we will need good upper and lower 
bounds on the volume of a Hamming ball.  Next we formalize the notion of the volume of a 
Hamming ball:

Definition 3.3.2  (Volume of a Hamming Ball). Let q ≥ 2 and n ≥ r ≥ 1 be integers.  Then 
the volume of a Hamming ball of radius r is given by

V olq(r, n) = |Bq(0, r)| =

)︃

(q − 1)i.

r
∑︂

i=0

(︃n
i

The choice of 0 as the center for the Hamming ball above was arbitrary: since the volume 
of a Hamming ball is independent of its center (as is evident from the last equality above), 
we could have picked any point as the center.

We will prove the following result:

Proposition 3.3.3. Let q ≥ 2 be an integer and 0 ≤ p ≤ 1 − 1

q  be a real number.  Then:

(i) V olq(pn, n) ≤ qHq(p)n; and

(ii) for large enough n, V olq(pn, n) ≥ qHq(p)n−o(n).

58

 0 0.1 0.2 0.3 0.4 0.5 0.6 0.7 0.8 0.9 1 0 0.2 0.4 0.6 0.8 1Hq(x)  --->x  --->q=2q=3q=4

<!-- pdf-page: 71 -->
Proof.  We start with the proof of (i).  Consider the following sequence of relations:

1 = (p + (1 − p))n

=

=

≥

=

=

≥

=

n
∑︂

i=0
pn
∑︂

i=0
pn
∑︂

i=0
pn
∑︂

i=0
pn
∑︂

i=0
pn
∑︂

i=0
pn
∑︂

i=0

(︃n
i
(︃n
i

(︃n
i
(︃n
i
(︃n
i
(︃n
i
(︃n
i

)︃

pi(1 − p)n−i

)︃

pi(1 − p)n−i +

n
∑︂

i=pn+1

(︃n
i

)︃

pi(1 − p)n−i

)︃

pi(1 − p)n−i

)︃

(q − 1)i

(︃ p

)︃i

q − 1

(1 − p)n−i

)︃

(q − 1)i(1 − p)n

)︃

(q − 1)i(1 − p)n

(︃

(︃

)︃i

p
(q − 1)(1 − p)

)︃pn

p
(q − 1)(1 − p)

)︃

(q − 1)i

(︃ p

)︃pn

q − 1

(1 − p)(1−p)n

≥ V olq(pn, n)q−Hq(p)n.

(3.18)

(3.19)

(3.20)

(3.21)

(3.22)

In the above,  (3.18) follows from the binomial expansion.  (3.19) follows by dropping the 
(q−1)(1−p) ≤ 1 (as5 p ≤ 1 − 1/q).  Rest 
second sum and (3.20) follows from the facts that 
of the steps except (3.22) follow from rearranging the terms.  (3.22) follows as q−Hq(p)n =
(︂ p
q−1

(1 − p)(1−p)n.

)︂pn

p

(3.22) implies that

which proves (i).

1 ≥ V olq(pn, n)q−Hq(p)n,

We now turn to the proof of part (ii). For this part, we will need Stirling’s approximation 

for n! (Lemma A.1.2).

5Indeed, note that 

p

(q−1)(1−p) ≤ 1 is true if  p

1−p ≤ q−1

1 , which in turn is true if p ≤ q−1

q , where the last 

step follows from Lemma A.2.1.

59



<!-- pdf-page: 72 -->
By the Stirling’s approximation, we have the following inequality:

)︃

(︃ n
pn

=

>

=

n!
(pn)!((1 − p)n)!
(n/e)n
(pn/e)pn((1 − p)n/e)(1−p)n ·

1

ppn(1 − p)(1−p)n · ℓ(n),

1
√︁2πp(1 − p)n

· eλ1(n)−λ2(pn)−λ2((1−p)n)

where ℓ(n) = eλ1(n)−λ2(pn)−λ2((1−p)n)

√︁2πp(1−p)n

.

Now consider the following sequence of relations that complete the proof:

V olq(pn, n) ≥

)︃

(q − 1)pn

(︃ n
pn

>

(q − 1)pn

ppn(1 − p)(1−p)n · ℓ(n)

≥ qHq(p)n−o(n).

(3.23)

(3.24)

(3.25)

(3.26)

In the above (3.24) follows by only looking at the last term in the sum that defined V olq(pn, n). 
(3.25) follows from (3.23) while (3.26) follows from the definition of Hq(·) and the fact that 
for large enough n, ℓ(n) is q−o(n).

Next, we consider how the q-ary entropy function behaves for various ranges of its pa­

rameters.

3.3.2  Other Properties of the q-ary Entropy function

This  section  uses  asymptotic  analysis  in  few  places.  Reader  who  wish  to  brush  up  their 
knowledge of asymptotic analysis are referred to Appendix ??.

We begin by recording the behavior of the q-ary entropy function for large q.

Proposition 3.3.4. For small enough ε, 1 − Hq(ρ) ≥ 1 − ρ − ε for every 0 < ρ ≤ 1 − 1/q
if and only if q is 2Ω(1/ε).

Proof.  We first note that by definition of Hq(ρ) and H(ρ),

Hq(ρ) = ρ logq(q − 1) − ρ logq ρ − (1 − ρ) logq(1 − ρ)

= ρ logq(q − 1) + H(ρ)/ log2 q.

Now if q ≥ 21/ε, we get that

Hq(ρ) ≤ ρ + ε
as  logq(q − 1) ≤ 1  and  H(ρ) ≤ 1.  Thus,  we  have  argued  that  for  q ≥ 21/ε,  we  have 
1 − Hq(ρ) ≥ 1 − ρ − ε, as desired.

60

 


<!-- pdf-page: 73 -->
Next, we consider the case when q = 2o(1/ε). We begin by claiming that for small enough 

ε,

Indeed, logq(q − 1) = 1 + (1/ ln q) ln(1 − 1/q) = 1 − O
q ≥ 1/ε2 (and small enough ε).

if q ≥ 1/ε2 then  logq(q − 1) ≥ 1 − ε.
)︂

(︂ 1
q ln q

Finally, if q = 2o(︁ 1

ε

)︁

, then for fixed ρ,

H(ρ)/ log q = ε · ω(1).

,6 which is at least 1 − ε for 

Then for q = 2o(︁ 1

ε

)︁

 (but q ≥ 1/ε2) we have

ρ logq(q − 1) + H(ρ)/ log q ≥ ρ − ε + ε · ω(1) > ρ + ε,

which implies that

1 − Hq(ρ) < 1 − ρ − ε,
as desired.  For q ≤ 1/ε2, Lemma 3.3.5 shows that 1 − Hq(ρ) ≤ 1 − H1/ε2(ρ) < 1 − ρ − ε, as 
desired.

We will also be interested in how Hq(x) behaves for fixed x and increasing q:

Lemma 3.3.5. Let q ≥ 2 be an integer and let 0 ≤ ρ ≤ 1 − 1/q, then for any real m ≥ 1
such that

(︃

qm−1 ≥

1 +

)︃q−1

1
q − 1

,

(3.27)

we have

Hq(ρ) ≥ Hqm(ρ).

Proof. 
that ρ ∈ (0, 1 − 1/q].

Note that Hq(0) = Hqm(0) = 0.  Thus, for the rest of the proof we will assume 

As observed in the proof of Proposition 3.3.4, we have

Hq(ρ) = ρ ·

log(q − 1)
log q

+ H(ρ) ·

1
log q

.

Using this, we obtain

Hq(ρ) − Hqm(ρ) = ρ

(︃ log(q − 1)
log q

−

log(qm − 1)
m log q

)︃

+ H(ρ)

(︃ 1
log q

−

1
m log q

)︃

.

The above in turn implies that

1
ρ

· m log q · (Hq(ρ) − Hqm(ρ)) = log(q − 1)m − log(qm − 1) +

H(ρ)
ρ

(m − 1)

6The last equality follows from the fact that by Lemma A.2.2, for 0 < x < 1, ln(1 − x) = −O(x).

61

 


<!-- pdf-page: 74 -->
H(1 − 1/q)
1 − 1/q
(︃

≥ log(q − 1)m − log(qm − 1) +

(m − 1)

(3.28)

= log(q − 1)m − log(qm − 1) + (m − 1)

log

(︄

(︄

(q − 1)m
qm − 1

·

(︃ q

)︃m−1

q − 1

(q − 1) · qm−1 · q

)︄

m−1
q−1

)︄

m−1
q−1

· q

qm − 1

= log

= log

≥ 0

)︃

q
q − 1

+

log q
q − 1

(3.29)

In the above (3.28) follows from the fact that H(ρ)/ρ is decreasing7 in ρ and that ρ ≤ 1−1/q. 
(3.29) follows from the claim that

(q − 1) · q

m−1

q−1 ≥ q.

Indeed the above follows from (3.27).

Finally, note that (3.29) completes the proof.

Since (1 + 1/x)x ≤ e (by Lemma A.2.5),  we also have that (3.27) is also satisfied for 
ln q .  Further, we note that (3.27) is satisfied for every m ≥ 2 (for any q ≥ 3), which 

m ≥ 1 + 1
leads to the following (also see Exercise 3.6):

Corollary 3.3.6. Let q ≥ 3 be an integer and let 0 ≤ ρ ≤ 1 − 1/q, then for any m ≥ 2, we 
have

Hq(ρ) ≥ Hqm(ρ).

Next, we look at the entropy function when its input is very close to 1.

Proposition 3.3.7. For small enough ε > 0,

(︃

Hq

1 −

)︃

− ε

1
q

≤ 1 − cqε2,

where cq is a constant that only depends on q.

The intuition behind the proof is the following.  Since the derivative of Hq(x) is 
Proof. 
zero at x = 1 − 1/q, in the Taylor expansion of Hq(1 − 1/q − ε) the ε term will vanish.  We 

7Indeed, H(ρ)/ρ = log(1/ρ) − (1/ρ − 1) log(1 − ρ).  Note that the first term is decreasing in ρ.  We claim 
that the second term is also decreasing in ρ – this e.g. follows from the observation that −(1/ρ−1) ln(1−ρ) =
(1 − ρ)(1 + ρ/2! + ρ2/3! + · · · ) = 1 − ρ/2 − ρ2(1/2 − 1/3!) − · · · is also decreasing in ρ.

62

 


<!-- pdf-page: 75 -->
will now make this intuition more concrete.  We will think of q as fixed and 1/ε as growing. 
In particular, we will assume that ε < 1/q.  Consider the following equalities:
)︃

(︃

)︃

)︃

Hq(1 − 1/q − ε) = −

1 −

− ε

logq

= − logq

1
q
(︃1
q
[︃

1
ln q

(︃

1 −

(︃

= 1 −

ln

1 −

= 1 + o(ε2) −

1
ln q

= 1 + o(ε2) −

[︃

−

1
ln q

(︃ 1
q

logq

)︃

)︃

+

−

+ ε

)︃)︃

(︃1 − 1/q − ε
q − 1
(︃ 1
q
(︃ 1
q
ε2q2
2(q − 1)2 −
ε2q2

εq
q − 1
εq
q − 1
εq
q − 1

+ ε

ln

−

−

−

)︃

)︃

[︃

(︃ 1
q

+ ε

+ ε

logq
(︃ 1 − (εq)/(q − 1)
1 + εq

)︃

)︃]︃

(︃ 1 − (εq)/(q − 1)
1 + εq
)︃ (︃

+ ε

−

(︃ 1
q

εq
q − 1
)︃]︃

ε2q2
2

−

−

2(q − 1)2 − εq +
ε2q2
2(q − 1)2
)︃ (︃
εq2
q − 1
ε2q2
q − 1

ε2q3(q − 2)
2(q − 1)2
]︃
ε2q2(q − 2)
2(q − 1)2

εq
q − 1
(︃ 1
q
ε2q2
2(q − 1)2 +

+ ε

−

−

+

−

)︃]︃

= 1 + o(ε2) −

[︃

−

1
ln q

+ o(ε2)

= 1 −

≤ 1 −

ε2q2
2 ln q(q − 1)
ε2q2
4 ln q(q − 1)

(3.30)

(3.31)

(3.32)

(3.30) follows from the fact that for |x| < 1, ln(1 + x) = x − x2/2 + x3/3 − . . . (Lemma A.2.2) 
and by collecting the ε3 and smaller terms in o(ε2).  (3.31) follows by rearranging the terms 
and by absorbing the ε3 terms in o(ε2). The last step is true assuming ε is small enough.

Next, we look at the entropy function when its input is very close to 0.

Proposition 3.3.8. For small enough ε > 0,
(︃ 1
log q

Hq (ε) = Θ

· ε log

)︃)︃

.

(︃ 1
ε

Proof. 

By definition

Hq(ε) = ε logq(q − 1) + ε logq(1/ε) + (1 − ε) logq(1/(1 − ε)).

Since all the terms in the RHS are positive we have

Hq(ε) ≥ ε log(1/ε)/ log q.

(3.33)

63

 


<!-- pdf-page: 76 -->
Further, by Lemma A.2.2, (1 − ε) logq(1/(1 − ε)) ≤ 2ε/ ln q for small enough ε.  Thus, this 
implies that

Hq(ε) ≤

2 + ln(q − 1)
ln q

1
ln q

)︃

(︃ 1
ε

· ε +

· ε ln

.

(3.34)

(3.33) and (3.34) proves the claimed bound.

We will also work with the inverse of the q-ary entropy function.  Note that Hq(·) on 
q (y) = x such that 

the domain [0, 1 − 1/q] is a bijective map into [0, 1].  Thus, we define H −1
Hq(x) = y and 0 ≤ x ≤ 1 − 1/q.  Finally, we will need the following lower bound:

Lemma 3.3.9. For every 0 < y ≤ 1 − 1/q and for every small enough ε > 0,

where c′

q ≥ 1 is a constant that depends only on q.

H −1

q (y − ε2/c′

q) ≥ H −1

q (y) − ε,

It  is  easy  to  check  that  H −1
Proof. 
y ∈ [0, 1].  This  implies  that  the  derivative  of  H −1
(H −1
enough) δ > 0,

q (y)  is  a  strictly  increasing  convex  function  when 
q (y)  increases  with  y.  In  particular, 
q )′(y) for every 0 ≤ y ≤ 1.  In other words, for every 0 < y ≤ 1, and (small 

q )′(1) ≥ (H −1

H −1

q (y) − H −1

q (y − δ)

H −1

q (1) − H −1

q (1 − δ)

≤

δ

.

δ

Proposition 3.3.7 along with the facts that H −1
the proof if one picks c′

q = max(1, 1/cq) and δ = ε2/c′
q.

q (1) = 1−1/q and H −1

q

 is increasing completes 

3.4  Exercises

Exercise 3.1. Prove Lemma 3.1.3.

Exercise 3.2. Prove Lemma 3.1.11.

Exercise  3.3. In  this  exercise,  we  will  see a  common  use  of  the  Chernoff  bound (Theo­
rem 3.1.12).  Say we are trying to determine an (unknown) value x ∈ F to which we have 
access to via a randomized algorithm A that on input (random) input r ∈ {0, 1}m outputs an 
estimate A(r) of x such that

[A(r) = x] ≥

Pr
r

+ γ,

1
2

for some 0 < γ < 1
x with probability at least 1 − e−t.
Hint:  Call A with independent random bits and take majority of the answer and then use the Chernoff bound.

2. Then show that for any t ≥ 1 with O

 calls to A one can determine 

)︂

(︂ t
γ2

Exercise 3.4. Prove Lemma 3.1.13.

64

 
 


<!-- pdf-page: 77 -->
Exercise 3.5. Let P denote the property that the randomly chosen C satisfies f (C) ≤ b. 
Then E[f (C)] ≤ b implies that Pr[C has property P] > 0.

Exercise 3.6. Prove that for any Q ≥ q ≥ 2 and ρ ≤ 1 − 1/q, we have HQ(ρ) ≤ Hq(ρ).

Exercise 3.7. Prove that for p < 1

2, we have H2(p) ≤ O (p log p).

3.5  Bibliographic Notes

The Chernoff bounds of this chapter come from a family of bounds on the concentration 
of  sums  of  random  variables  around  their  expectation.  They  originate  with  the  work  of 
Chernoff [14] though Chernoff himself attributes the bound to personal communication with 
Rubin [4, Page 340].  These bounds and variations are ubiquitous in information theory and 
computer science — see for instance [15, 54, 53]. Proofs of various concentration bounds can 
e.g.  be found in [17].

The use of the probabilistic method in combinatorics seems to have originated in the 
early 40s and became especially well known after works of Erdös, notably [24].  Shannon’s 
adoption of the method in [65] is one of the first applications in a broader setting. For more 
on the probabilistic method, see the book by Alon and Spencer [2].

The  entropy  function  also  dates  back  to  Shannon  [65].  Shannon’s  definition  is  more 
general  and  applies  to  discrete  random  variables.  Our  specialization  to  a  two  parameter 
function (namely a function of q and p) is a special case derived from applying the original 
definition to some special random variables.

65



<!-- pdf-page: 78 -->
66



<!-- pdf-page: 79 -->
Part II

The Combinatorics

67



<!-- pdf-page: 80 -->


<!-- pdf-page: 81 -->
Chapter 4

What Can and Cannot Be Done-I

In this chapter, we will try to tackle Question 1.8.2.  We will approach this trade-off in the 
following way:

If we fix the relative distance of the code to be δ, what is the best rate R that 
we can achieve?

While we will not be able to pin down the exact optimal relationship between R and δ, we 
will start establishing some limits.  Note that an upper bound on R is a negative result in 
that it establishes that codes with certain parameters do not exist. Similarly, a lower bound 
on R is a positive result.

In this chapter, we will consider only one positive result, i.e.  a lower bound on R called 
the Gilbert-Varshamov bound in Section 4.2. In Section 4.1, we recall a negative result that 
we have already seen– Hamming bound and state its asymptotic version to obtain an upper 
bound on R.  We will consider two other upper bounds:  the Singleton bound (Section 4.3), 
which gives a tight upper bound for large enough alphabets (but not binary codes) and the 
Plotkin bound (Section 4.4), which gives a stronger upper bound than Singleton bound for 
binary codes.

4.1  Asymptotic Version of the Hamming Bound

We have already seen an upper bound in Section 1.7 due to Hamming.  However, we had 
stated this as an upper bound on the dimension k in terms of n, q and d.  In this section we 
convert this into a relation on R versus δ.

Consider any (n, k, d)q code with rate R = k/n and relative distance δ = d/n.  Recall 

that Theorem 1.7.2 implies the following:

R =

k
n

≤ 1 −

logq V olq

(︁⌊︁ d−1
2

⌋︁ , n)︁

n

69



<!-- pdf-page: 82 -->
Recall further that Proposition 3.3.3 states the following lower bound on the volume of a 
Hamming ball:

(︃⌊︃ d − 1

⌋︃

)︃

, n

≥ qHq

)︂

(︂ δ
2

n−o(n).

V olq

2

Taking logarithms to base q of both sides above, and dividing by n yields that the second 
term in the right hand side of the inequality above is lower bounded by Hq(δ/2)−o(1), where 
the o(1) term tends to 0 as n → ∞.  Thus Theorem 1.7.2 implies that for a q-ary of code C
of rate R, relative distance δ and block length n, we have:

R ≤ 1 − Hq

)︃

(︃ δ
2

+ o(1),

(4.1)

where the o(1) term tends to 0 as n → ∞.  Thus for an infinite family of q-ary codes C, by 
taking limits as n → ∞, we get the following asymptotic Hamming bound (see Exercise 4.1).

Proposition  4.1.1   (Asymptotic  Hamming  Bound). Let  C  be  an  infinite  family  of  q-ary 
codes with rate R = R(C) and relative distance δ = δ(C).  Then we have:

R ≤ 1 − Hq

)︃

.

(︃ δ
2

Figure  4.1  gives  a  pictorial  description  of  the  asymptotic  Hamming  bound  for  binary 

codes.

4.2  Gilbert-Varshamov Bound

Next, we will switch gears by proving our first non-trivial lower bound on R in terms of δ. 
(In fact, this is the only positive result on the R vs δ tradeoff question that we will see in 
this book.)  In particular, we will prove the following result:

Theorem 4.2.1   (Gilbert-Varshamov Bound). Let q ≥ 2.  For every 0 ≤ δ < 1 − 1
q  there 
exists a family of q-ary codes C with rate R(C) ≥ 1 − Hq(δ) and relative distance δ(C) ≥ δ. 
If q is a prime power then there exists such a q-ary family of linear codes.  Furthermore, for 
every 0 ≤ ε ≤ 1 − Hq(δ) and integer n, if a matrix G is picked uniformly from Fk×n
 for 
k = n(1 − Hq(δ) − ε), then G generates a code of rate 1 − Hq(δ) − ε and relative distance at 
least δ with probability strictly greater than 1 − q−εn.

q

The bound of the theorem is referred to as the GV bound.  For a pictorial description of 
the GV bound for binary codes, see Figure 4.1.  We will present the proofs for general codes 
and linear codes in Sections 4.2.1 and 4.2.2 respectively.

In what follows we first prove the existence of a non-linear code of rate 1 − Hq(δ) and 
relative distance at least δ. Later we show how to get a linear code, and with high probability 
(when ε > 0).  (Note that the existence of a linear code is implied by the final part using 
ε = 0.)

70



<!-- pdf-page: 83 -->
Figure 4.1:  The Hamming and GV bounds for binary codes.  Note that any point below the 
GV bound is achievable by some code while no point above the Hamming bound is achievable 
by any code.  In this part of the book we would like to push the GV bound as much up as 
possible while at the same time try and push down the Hamming bound as much as possible.

4.2.1  Greedy Construction

We  will  prove  Theorem  4.2.1  for  general  codes  by  a  greedy  construction  described  next: 
Fix an integer n and let d = δn.  Start with the empty code C ⊆ [q]n and then keep on 
adding strings to C that are at Hamming distance at least d from all the existing words in 
C.  Algorithm 4.2.1 presents a formal description of the algorithm and Figure 4.2 illustrates 
the first few executions of this algorithm.

Algorithm 4.2.1 Gilbert’s Greedy Code Construction
Input: n, q, d
Output: A code C ⊆ [q]n of distance d ≥ 1
1: C ← ∅
2: while there exists a v ∈ [q]n such that ∆(v, c) ≥ d for every c ∈ C do
3:   Add v to C
4: return C

We claim that Algorithm 4.2.1 terminates and the C that it outputs has distance d. The 
latter is true by step 2, which makes sure that in Step 3 we never add a vector c that will 
make the distance of C fall below d.  For the former claim, note that, if we cannot add v
at some point, we cannot add it later.  Indeed, since we only add vectors to C, if a vector 
v ∈ [q]n is ruled out in a certain iteration of Step 2 because ∆(c, v) < d, then in all future 

71

 0 0.1 0.2 0.3 0.4 0.5 0.6 0.7 0.8 0.9 1 0 0.2 0.4 0.6 0.8 1RδHamming boundGV bound

<!-- pdf-page: 84 -->
Figure 4.2:  An illustration of Gilbert’s greedy algorithm for the first five iterations.

iterations, we have ∆(v, c) < d and thus, this v will never be added in Step 3 in any future 
iteration.

The  running  time  of  Algorithm  4.2.1  is  qO(n).  To  see  this,  note  that  Step  2  in  the 
worst-case could be repeated for every vector in [q]n, that is at most qn times.  In a naive 
implementation, for each iteration, we cycle through all vectors in [q]n and for each vector 
v ∈ [q]n, iterate through all (at most qn) vectors c ∈ C to check whether ∆(c, v) < d.  If no 
such c exists, then we add v to C.  Otherwise, we move to the next v.  However, note that 
we can do slightly better– since we know that once a v is “rejected” in an iteration, it’ll keep 
on being rejected in the future iterations, we can fix up an ordering of vectors in [q]n and for 
each vector v in this order, check whether it can be added to C or not. If so, we add v to C, 
else we move to the next vector in the order.  This algorithm has time complexity O(nq2n), 
which is still qO(n).

Further, we claim that after termination of Algorithm 4.2.1

B(c, d − 1) = [q]n.

⋃︂

c∈C

This  is  because  if  the  above  is  not  true,  then  there  exists  a  vector  v ∈ [q]n \ C,  such 
that ∆(v, c) ≥ d and hence v can be added to C.  However, this contradicts the fact that 
Algorithm 4.2.1 has terminated.  Therefore,

⃓
⃓
⃓
⃓
⃓

⋃︂

c∈C

⃓
⃓
⃓
B(c, d − 1)
⃓
⃓

= qn.

72

(4.2)



<!-- pdf-page: 85 -->
It is not too hard to see that

which by (4.2) implies that

∑︂

c∈C

|B(c, d − 1)| ≥

⃓
⃓
⃓
⃓
⃓

⋃︂

c∈C

⃓
⃓
⃓
B(c, d − 1)
⃓
⃓

,

|B(c, d − 1)| ≥ qn

∑︂

c∈C

or since the volume of a Hamming ball is translation invariant,

V olq(d − 1, n) ≥ qn.

∑︂

c∈C

Since ∑︁

c∈C V olq(d − 1, n) = V olq(d − 1, n) · |C|, we have

|C| ≥

qn
V olq(d − 1, n)

≥

qn
qnHq(δ)
= qn(1−Hq(δ)),

as desired.  In the above, (4.3) follows from the fact that

V olq(d − 1, n) ≤ V olq(δn, n)

≤ qnHq(δ),

(4.3)

(4.4)

where the second inequality follows from the upper bound on the volume of a Hamming ball 
in Proposition 3.3.3.

We thus conclude that for every q, n and δ there exists a code of rate at least n(1−Hq(δ)). 

We state this formally as a lemma below.

Lemma  4.2.2. For every pair of positive integers n, q and real δ ∈ [0, 1] there exists an 
(n, k, δn)q code satisfying qk ≥

qn
V olq(d−1,n) .

In particular, for every positive integer q and real δ ∈ [0, 1 − 1/q] there exists an infinite 

family of q-ary codes C of rate R and distance δ satisfying R ≥ 1 − Hq(δ).

It  is  worth  noting  that  the  code  from  Algorithm  4.2.1  is  not  guaranteed  to  have  any 
special structure.  In particular, even storing the code can take exponential space.  We have 
seen in Proposition 2.3.3 that linear codes have a much more succinct representation. Thus, 
a natural question is:

Question 4.2.3. Do linear codes achieve the R ≥ 1 − Hq(δ) tradeoff that the greedy con­
struction achieves?

Next, we will answer the question in the affirmative.

73



<!-- pdf-page: 86 -->
4.2.2  Linear Code Construction

Now we will show that a random linear code, with high probability, lies on the GV bound. 
The construction is a use of the probabilistic method (Section 3.2).

Proof of Theorem 4.2.1. 
exists a k × n matrix G of full rank (for k = (1 − Hq(δ) − ε)n) such that
For every m ∈ Fk

q \ {0}, wt(mG) ≥ d.

By Proposition 2.3.6,  we are done if we can show that there 

We will prove the existence of such a G by the probabilistic method.  Pick a random linear 
code by picking a random k × n matrix G where each of kn entries is chosen uniformly and 
independently at random from Fq.  Fix m ∈ Fk
q \ {0}.  Recall that by Lemma 3.1.14, for a 
random G, mG is a uniformly random vector from Fn
q .  Thus, for every non-zero vector m, 
we have

[wt(mG) < d] =

Pr
G

V olq(d − 1, n)
qn

≤

qnHq(δ)
qn
≤ q−k · q−εn,

(4.5)

(4.6)
where (4.5) follows from the fact that the condition wt(mG) < d is equivalent to the condition 
that mG ∈ B(0, d − 1) and the fact that mG is uniformly random in Fn
q , (4.5) follows from 
(4.4) and (4.6) uses k ≤ n(1 − Hq(δ) − ε).  There are qk − 1 non-zero vectors m and taking 
the union over all such vectors and applying the union bound (Lemma 3.1.5) we have

[There exists a non-zero m s.t.  wt(mG) < d] ≤ (qk − 1) · q−k · q−εn

Pr
G

< q−ε·n.

q

Fix a matrix G ∈ Fk×n
 such that for every non-zero M we have wt(mG) ≥ d. The argument 
above has shown that a random matrix has this property with probability strictly greater 
than 1 − q−εn.  By Proposition 2.3.6 this implies that the code generated by G has distance 
at least d.  To conclude the theorem we only need to argue that the code has dimension k, 
i.e., that G has full rank. But this also follows immediately from the property that for every 
ε ≥ 0, we have that the probability that the code generated by a uniformly random matrix 
has  distance  less  than  or  equal  to  d  is  strictly  less  than  1.  Thus  using  the  probabilistic 
method we conclude there exists a matrix G such that the code it generates in an [n, k, d]q
code.  Furthermore if ε > 0 then the probability that the code does not have distance d is 
exponentially small, specifically at most qεn.

To conclude we need to verify that the code generated by G has dimension k, i.e., that 
G has full rank.  But note that an equivalent definition of G not having full rank is that 
there exists a non-zero vector M such that mG = 0.  But the existence of such a vector m
would imply wt(mG) = 0 < d contradicting the property that for every non-zero M we have 
wt(mG) ≥ d.  We thus conclude that G generates a code of rate k/n = 1 − Hq(δ) − ε and 
relative distance δ.  The theorem follows.

74

 


<!-- pdf-page: 87 -->
Discussion.  We now digress a bit to stress some aspects of the GV bound and its proof. 
First, note that that proof by the probabilistic method shows something stronger than just 
the existence of a code, but rather gives a high probability result.  Furthermore, as pointed 
out explicitly for the non-linear setting in Lemma 4.2.2, the result gives a lower bound not 
only in the asymptotic case but also one for every choice of n and k.  The proof of the GV 
bound in the non-linear case gives a similar non-asymptotic bound in the linear setting also.
Note that we can also pick a random linear code by picking a random (n − k) × n parity 

check matrix.  This also leads to a alternate proof of the GV bound:  see Exercise 4.2.

Finally, we note that Theorem 4.2.1 requires δ < 1 − 1

q .  An inspection of Gilbert and 
Varshamov’s proofs shows that the only reason the proof required that δ ≤ 1 − 1
q  is because 
it is needed for the volume bound (recall the bound in Proposition 3.3.3)– V olq(δn, n) ≤
qHq(δ)n– to hold.  It is natural to wonder if the above is just an artifact of the proof or if 
better codes exist.  This leads to the following question:

Question 4.2.4. Does there exists a code with R > 0 and δ > 1 − 1
q ?

We will return to this question in Section 4.4.

4.3  Singleton Bound

We will now change gears again and prove an upper bound on R (for fixed δ).  We start by 
proving the Singleton bound.

Theorem 4.3.1  (Singleton Bound). For every (n, k, d)q code,

k ≤ n − d + 1.

Consequently,  if  C  is  an  infinite  family  of  codes  of  rate  R  and  relative  distance  δ  then 
R ≤ 1 − δ.

Note  that  the  asymptotic  bound  hold  for  any  family  of  codes,  even  those  where  the 

alphabet may grow (arbitrarily) with the length of the code.

Proof.  We  start  by  proving  the  non-asymptotic  bound  first.  The  asymptotic  version 
follows easily and is shown at the end.

Let c1, c2, . . . , cM  be the codewords of an (n, k, d)q code C.  Note that we need to show 
i to be the prefix of the codeword ci of length n − d + 1

M ≤ qn−d+1. To this end, we define c′
for every i ∈ [M ].  See Figure 4.3 for a pictorial description. 

We now claim that for every i ̸= j, c′

j.  For the sake of contradiction, assume that 
there exits an i ̸= j such that c′
j.  Notice this implies that ci and cj agree in all the 
first n − d + 1 positions, which in turn implies that ∆(ci, cj) ≤ d − 1.  This contradicts the 
fact that C has distance d.  Thus, M  is the number of prefixes of codewords in C of length 
n − d + 1, which implies that M ≤ qn−d+1 as desired.

i = c′

i ̸= c′

75



<!-- pdf-page: 88 -->
Figure 4.3:  Construction of a new code in the proof of the Singleton bound.

To  get  the  asymptotic  bound,  assume  some  infinite  family  of  codes  C  has  rate  R =
R(C) = 1 − δ + ε for some ε > 0.  Then there must exist an n > 2/ε and a code Cn ∈ C
that is an (n, k, d)q code with k ≥ n(1 − δ + ε) and d ≥ δn.  By our choice of n we thus have 
k ≥ n − d + 2 contradicting the non-asymptotic bound proved above.

Figure  4.4  presents  a  pictorial  description  of  the  asymptotic  version  of  the  Singleton 
bound.  It is worth noting that the bound is independent of the alphabet size.  As is evident 
from Figure 4.4, the Singleton bound is worse than the Hamming bound for binary codes. 
However, this bound is better for larger alphabet sizes.  In fact, we will look at a family of 
codes called Reed-Solomon codes in Chapter 5 that meets the Singleton bound.  However, 
the alphabet size of the Reed-Solomon codes increases with the block length n.  Thus,  a 
natural follow-up question is the following:

Question 4.3.2. Given a fixed q ≥ 2, does there exist a q-ary code that meets the Singleton 
bound?

We’ll see an answer to this question in the next section.

4.4  Plotkin Bound

In  this  section,  we  will  study  the  Plotkin  bound,  which  will  answer  Questions  4.2.4  and 
4.3.2.  We start by stating the bound.

76

 


<!-- pdf-page: 89 -->
Figure 4.4:  The Hamming, GV and Singleton bound for binary codes.

Theorem 4.4.1  (Plotkin bound). The following hold for any code C ⊆ [q]n with distance 
at least d:

1. If d =

2. If d >

)︂

)︂

(︂

(︂

1 − 1
q

1 − 1
q

n, |C| ≤ 2qn.

n, |C| ≤

qd
qd−(q−1)n .

δ ≥ 1 − 1

Note that the Plotkin bound (Theorem 4.4.1) implies that a code with relative distance 
q , must necessarily have R = 0, which answers Question 4.2.4 in the negative.
Before proving Theorem 4.4.1,  we make a few remarks.  We first note that the upper 
bound  in  the  first  part  of  Theorem  4.4.1  can  be  improved  to  2(q − 1)n  for  q ≥ 2.  (See 
Exercise 4.13.) Second, it can be shown that this bound is tight for q = 2. (See Exercise 4.14.) 
Third, the statement of Theorem 4.4.1 gives a trade-off only for relative distance greater than 
1 − 1/q.  However, as the following corollary shows, the result can be extended to work for 
0 ≤ δ ≤ 1 − 1/q.  (See Figure 4.5 for an illustration for binary codes.)

Corollary 4.4.2. Let C be an infinite family of q-ary codes with relative distance 0 ≤ δ ≤
1 − 1

q  and rate R.  Then

R ≤ 1 −

(︃ q

)︃

q − 1

δ.

Proof. 
R = 1 −

Assume  for  contradiction  that  C  is  an  infinite  family  of  q-ary  codes  with  rate 
(︂ q
)︁
q−1

δ + ε for some ε > 0.  Let C ∈ C be a code of block length n ≥ 3

ε · log (︁ 1

)︂

ε

77

 0 0.2 0.4 0.6 0.8 1 0 0.2 0.4 0.6 0.8 1RδHamming boundGV boundSingleton bound

<!-- pdf-page: 90 -->
with  distance  d ≤ δn  and  message  length  k ≥ Rn.  We  argue  now  that  an  appropriate 
“shortening” of C yields a code contradicting Theorem 4.4.1.

Partition  the  codewords  of  C  so  that  codewords  within  a  partition  agree  on  the  first 
− 1.  (We will see later why this choice of n′ makes sense.) 

⌋︂

⌊︂ qd
q−1

n − n′ symbols, where n′ =
In particular, for every x ∈ [q]n−n′

, define the ‘prefix code’

Cx = {(cn−n′+1, . . . cn) | (c1 . . . cN ) ∈ C, (c1 . . . cn−n′) = x} .

⌋︂

⌊︂ qd
q−1

In other words Cx consists of the n′-length suffixes of all codewords of C that start with the 
string x.)

By definition Cx is a q-ary code of block length n′ =

− 1. We claim that it also has 
distance at least d for every x:  To see this, suppose for some x, c1 ̸= c2 ∈ Cx, ∆(c1, c2) < d. 
But this yields two codewords of C, namely (x, c1) and (x, c2), a Hamming distance is less 
than d from each other, contradicting the assumption that ∆(C) ≥ d.
)︂
1 − 1
q

d  (by  definition  of  n′)  and  thus,  d >

n′.  Applying  Theo­

Since  n′ <

(︂ q
q−1

)︂

(︂

rem 4.4.1 to Cx we get that

|Cx| ≤

qd

qd − (q − 1)n′ ≤ qd ≤ qn,

(4.7)

where the second inequality follows from the fact that qd − (q − 1)n′ is a positive integer and 
the third is immediate from d ≤ n.

We now use the bound on |Cx| for all x to get a bound on |C|. Note that by the definition 

of Cx:

which by (4.7) implies that

|C| =

∑︂

|Cx| ,

x∈[q]n−n′

|C| ≤

∑︂

x∈[q]n−n′

qn = qn−n′+1+ log n

log q ≤ qn− q

(︂
q−1 d+1+log n ≤ qn

1−δ· q

q−1 +ε

)︂

,

where the first inequality uses the definition of n′ and the final inequality uses the fact that 
(︂ q
ε · log (︁ 1
n ≥ 3
δ + ε.  Since this holds for every ε > 0 the 
q−1
corollary follows.

)︁.  We conclude that R ≤ 1 −

)︂

ε

Note that Corollary 4.4.2 implies that for any q-ary code of rate R and relative distance 
δ (where q is a constant independent of the block length of the code), R < 1 − δ.  In other 
words, this answers Question 4.3.2 in the negative.

Let us pause for a bit at this point and recollect the bounds on R versus δ that we have 
proved till now, which are all depicted in Figure 4.5 (for q = 2).  The GV bound is the best 
known lower bound at the time of writing of this book. Better upper bounds are known and 
we will see one such trade-off (called the Elias-Bassalygo bound) in Section ??.

78

 


<!-- pdf-page: 91 -->
Figure 4.5:  The current bounds on the rate R vs.  relative distance δ for binary codes.  The 
GV bound is a lower bound on R while the other three bounds are upper bounds on R.

Now, we turn to the proof of Theorem 4.4.1, for which we will need two more lemmas. The 
first lemma deals with vectors over real spaces.  We quickly recap the necessary definitions. 
Consider a vector v in Rn, that is, a tuple of n real numbers.  This vector has (Euclidean) 
norm ∥v∥ = √︁v2
n, and is a unit vector if and only if its norm is 1.  The inner 
product of two vectors, u and v, is ⟨u, v⟩ = ∑︁
i ui · vi.  The following lemma gives a bound 
on the number of vectors that can exist such that every pair is at an obtuse angle with each 
other.

2 + . . . + v2

1 + v2

Lemma 4.4.3  (Geometric Lemma). Let v1, v2, . . . , vm ∈ RN  be non-zero vectors.

1. If ⟨vi, vj⟩ ≤ 0 for all i ̸= j, then m ≤ 2N .

2. Let vi be unit vectors for 1 ≤ i ≤ m.  Further, if ⟨vi, vj⟩ ≤ −ε < 0 for all i ̸= j, then 

m ≤ 1 + 1

ε .1

(Both items 1 and 2 are tight:  see Exercises 4.15 and 4.16.)  The proof of the Plotkin 
bound will need the existence of a map from codewords to real vectors with certain properties, 
which the next lemma guarantees.

Lemma 4.4.4  (Mapping Lemma). For every q and n, there exists a function f : [q]n −→ Rnq
such that for every c1, c2 ∈ [q]n we have

⟨f (c1), f (c2)⟩ = 1 −

(︃ q

)︃ (︃ ∆(c1, c2)

)︃

q − 1

n

.

1Note that since vi and vj are both unit vectors, ⟨vi, vj⟩ is the cosine of the angle between them.

79

 0 0.2 0.4 0.6 0.8 1 0 0.2 0.4 0.6 0.8 1RδHamming boundGV boundSingleton bound

<!-- pdf-page: 92 -->
Consequently we get:

1. For every c ∈ [q]n, ∥f (c)∥ = 1.

2. If ∆(c1, c2) ≥ d then we have ⟨f (c1), f (c2)⟩ ≤ 1 −

(︂ q
q−1

)︂ (︁ d
n

)︁ .

We defer the proofs of the Geometric Lemma and the Mapping Lemma to the end of the 

section and turn instead to proving Theorem 4.4.1 using the lemmas.

Let C = {c1, c2, . . . , cm} be a q-ary code of block length n and 
Proof of Theorem 4.4.1. 
distance d.  Let f : [q]n → Rnq be the function from Lemma 4.4.4.  Then for all i we have 
that f (ci) is a unit length vector in Rnq.  Furthermore for all i ̸= j, we have

⟨f (ci), f (cj)⟩ ≤ 1 −

(︃ q

q − 1

)︃ d
n

.

Thus f (c1), . . . , f (cm) give us unit vectors in Rnq to which we can apply Lemma 4.4.3 and 
this will yield the upper bounds claimed on m = |C| in the theorem statement.
1 − 1
q

For part 1 of the theorem, if d =

, then for all i ̸= j, we have

n = (q−1)n

(︂

)︂

q

⟨f (ci), f (cj)⟩ ≤ 0.

So by the first part of Lemma 4.4.3, m ≤ 2nq, as desired.

For part 2, if d >

n then for all i ̸= j we have

)︂

(︂ q−1
q

⟨f (ci), f (cj)⟩ ≤ 1 −

(︃ q

q − 1

)︃ d
n

= −

(︃ qd − (q − 1)n
(q − 1)n

)︃

.

(︂ qd−(q−1)n
Let ε def=
(q−1)n
and ε to get m ≤ 1 + (q−1)n

)︂

qd−(q−1)n =

qd

qd−(q−1)n, as desired.

> 0.  We can apply the second part of Lemma 4.4.3 to f (c1), . . . , f (cm)

4.4.1  Proof of Geometric and Mapping Lemmas

We now prove Lemmas 4.4.3 and 4.4.4.  We start with Lemma 4.4.3, namely the Geometric 
Lemma.

Proof of Lemma 4.4.3.  We prove both parts using linear algebra over the reals.

We start by proving the first part of the lemma.  This part is also linear algebraic but 

involves a few more steps.

We first focus on a subset of the m vectors that has a positive inner product with some 
fixed vector u.  Specifically we pick u to be a generic vector in RN  so that ⟨u, vi⟩ ̸= 0 for 
every i. Such vector exists since the set of vectors satisfying ⟨u, vi⟩ = 0 is a dimension N − 1
linear subpace of RN  (since vi ̸= 0). And the union of N  such linear subspaces (one for each 
i ∈ [N ]) cannot cover all of RN .

80

 


<!-- pdf-page: 93 -->
Assume w.l.o.g.  that at least half of the vi’s have a positive inner product with u (if not 
we can work with −u instead) and assume further that these are the first ℓ ≥ m/2 vectors by 
renumbering the vectors. We now show that v1, . . . , vℓ are linearly independent. This suffices 
to prove the first part, since linear independence implies ℓ ≤ N  and thus m ≤ 2ℓ ≤ 2N .

Assume for contradiction that there is a linear dependency among the vectors v1, . . . , vℓ, 
i.e., there exist α1, . . . , αℓ with at least one αi ̸= 0 such that ∑︁
i∈[ℓ] αizi = 0.  Note we can 
assume that at least one αi is positive since if all are non-negative we can negate all αi’s to 
get a positive αi. Further, by renumbering the indices we can assume that there exists k ≥ 1
such that α1, . . . , αk > 0 and αk+1, . . . , αℓ ≤ 0.

Let w = ∑︁k

i=1 αivi By the definition of αi’s we have that w = − ∑︁ℓ

j=k+1 αjvj.  We first 

argue that w ̸= 0 by using the vector u.  Note that we have

⟨u, w⟩ = ⟨u,

k
∑︂

i=1

αivi⟩ =

k
∑︂

i=1

αi⟨u, vi⟩ ≥ α1⟨u, v1⟩ > 0.

We thus conclude w has a non-zero inner product with some vector and hence can not be 
the zero vector.

But now we have the following contradiction:

0 < ⟨w, w⟩ =

⟨︄ k

∑︂

ℓ
∑︂

αivi, −

⟩︄

αjvj

= −

k,ℓ
∑︂

αiαj⟨vi, vj⟩ ≤ 0,

i=1

j=k+1

i=1,j=k+1

i=1 αivi = − ∑︁ℓ

where the first inequality uses w ̸= 0, the first equality uses the two definitions of w namely 
w = ∑︁k
j=k+1 αjvj, and the final inequality holds for every term in the sum­
mation.  Specifically  for  every  0 ≤ i ≤ k  and  k + 1 ≤ j ≤ ℓ  we  have  αi ≥ 0,  αj ≤ 0
and ⟨vi, vj⟩ ≤ 0 and so −αiαj⟨vi, vj⟩ ≤ 0.  We conclude that v1, . . . , vℓ must be linearly 
independent and this proves the first part of the lemma.

We now move on to the proof of the second part. Define z = v1 + . . . + vm. Now consider 

the following sequence of relationships:

∥z∥2 =

m
∑︂

i=1

∥vi∥2 + 2

⟨vi, vj⟩ ≤ m + 2 ·

∑︂

i<j

)︃

(︃m
2

· (−ε) = m(1 − εm + ε).

The inequality follows from the facts that each vi is a unit vector and the assumption that 
for every i ̸= j, ⟨vi.vj⟩ ≤ −ε.  As ∥z∥2 ≥ 0,

Since m ≥ 1, we have that

or

m(1 − εm + ε) ≥ 0.

1 − εm + ε ≥ 0

εm ≤ 1 + ε.

Thus, we have m ≤ 1 + 1

ε , as desired.

81



<!-- pdf-page: 94 -->
Alternate  proof  of  first  part.  We  now  present  an  alternate  proof  of  the  first  result, 
which we do by induction on n.  Note that in the base case of N = 0, we have m = 0, which 
satisfies the claimed inequality m ≤ 2N .

In the general case, we have m ≥ 1 non-zero vectors v1, . . . , vm ∈ RN  such that for every 

i ̸= j,

⟨vi, vj⟩ ≤ 0.

(4.8)

Since rotating all the vectors by the same amount does not change the sign of the inner 
product (nor does scaling any of the vectors), w.l.o.g. we can assume that vm = ⟨1, 0, . . . , 0⟩. 
For 1 ≤ i ≤ m − 1, denote the vectors as vi = ⟨αi, yi⟩, for some αi ∈ R and yi ∈ RN −1. Now, 
for any i ̸= 1, ⟨v1, vi⟩ = 1 · αi + ∑︁m
i=2 0 = αi.  However, we know from (4.8) that ⟨v1, vi⟩ ≤ 0, 
which in turn implies that

αi ≤ 0.

(4.9)

Next, we claim that at most one of y1, . . . , ym−1 can be the all zeroes vector, 0.  If not, 

assume w.l.o.g., that y1 = y2 = 0.  This in turn implies that

⟨v1, v2⟩ = α1 · α2 + ⟨y1, y2⟩
= α1 · α2 + 0
= α1 · α2
> 0,

where the last inequality follows from the subsequent argument.  As v1 = ⟨α1, 0⟩ and v2 =
⟨α2, 0⟩ are non-zero, we have that α1, α2 ̸= 0.  (4.9) then implies that α1, α2 < 0.  However, 
⟨v1, v2⟩ > 0 contradicts (4.8).

Thus, w.l.o.g., assume that y1, . . . , ym−2 are all non-zero vectors.  Further, note that for 
every i ̸= j ∈ [m − 2], ⟨yi, yj⟩ = ⟨vi, vj⟩ − αi · αj ≤ ⟨vi, vj⟩ ≤ 0.  Thus, we have reduced 
problem on m vectors with dimension N  to an equivalent problem on m − 2 vectors with 
dimension N − 1.  By induction we have m − 2 ≤ 2(N − 1) and thus implying m ≤ 2N .

Finally, we prove the Mapping Lemma, i.e., Lemma 4.4.4.

Proof of Lemma 4.4.4.  We begin by defining a map φ : [q] → Rq which essentially satisfies 
the  requirements  of  the  lemma  statement  for  the  case  n = 1  (up  to  some  normalization 
constant).  Then, we essentially apply φ separately to each coordinates of a word to get the 
map f : [q]n → Rnq that satisfies the claimed properties.  We now fill in the details.

Let ei denote the unit vector along the ith direction in Rq, i.e.,
⟨︄

⟩︄

ei =

0, 0, . . . ,

, . . . , 0

.

1
⏞⏟⏟⏞
ithposition

∑︁

Let  e = 1
q
otherwise.  Note also ⟨e, ei⟩ = ⟨e, e⟩ = 1/q for every i.

i∈[q] ei = ⟨1/q, 1/q, . . . , 1/q⟩.  Note  that  we  have  ⟨ei, ej⟩ = 1  if  i = j  and  0

82

 


<!-- pdf-page: 95 -->
Now we define φ : [q] → Rq to be φ(i) = ei − e.  For every pair i, j ∈ [q] we have

⟨φ(i), φ(j)⟩ = ⟨ei − e, ej − e⟩ = ⟨ei, ej⟩ − ⟨ei, e⟩ − ⟨e, ej⟩ + ⟨e, e⟩ = ⟨ei, ej⟩ − 1/q.

Thus, for every i ∈ [q], we get:

∥φ(i)∥2 = ⟨ei, ei⟩ − 1/q =

(q − 1)
q

.

Also for every i ̸= j ∈ [q], we have:

⟨φ(i), φ(j)⟩ = −

1
q

.

(4.10)

(4.11)

We are now ready to define our final map f : [q]n → Rnq. For every c = (c1, . . . , cn) ∈ [q]n, 

define

f (c) =

√︃ q

n(q − 1)

· (φ(c1), φ(c2), . . . , φ(cn)) .

(The multiplicative factor 

is a unit vector.)

√︂ q

n(q−1)  will be used to ensure below that f (c) for every c ∈ [q]n

To complete the proof, we will show that f  satisfies the claimed properties.  We begin 

with condition 1.  Note that

∥f (c)∥2 =

q
(q − 1)n

·

n
∑︂

i=1

∥φ(i)∥2 = 1,

where the first equality follows from the definition of f  and the second equality follows from 
(4.10).

We now turn to the second condition. For notational convenience, define c1 = (x1, . . . , xn)

and c2 = (y1, . . . , yn).  Consider the following sequence of relations:

⟨f (c1), f (c2)⟩ =

n
∑︂

⟨f (xℓ), f (yℓ)⟩

⟨φ(xℓ), φ(yℓ)⟩ +

∑︂

]︄

(︃

⟨φ(xℓ), φ(yℓ)⟩

·

)︃

q
n(q − 1)

ℓ=1
[︄

∑︂

[︄

ℓ:xℓ̸=yℓ

∑︂

=

=

=

ℓ:xℓ=yℓ
(︃ q − 1
q

)︃]︄

(︃

·

)︃

q
n(q − 1)

ℓ:xℓ̸=yℓ

[︃
∆(c1, c2)

∑︂

+

ℓ:xℓ=yℓ

)︃

)︃

(︃ −1
q
(︃ −1
q
(︃

= 1 − ∆(c1, c2)
(︃ q

= 1 −

q
n(q − 1)
)︃ (︃ ∆(c1, c2)

q − 1

n

)︃

,

+ (n − ∆(c1, c2))
)︃ [︃1
q

q − 1
q

+

]︃

(︃ q − 1
q

)︃]︃

(︃

·

q
n(q − 1)

)︃

(4.12)

(4.13)

as desired.  In the above, (4.12) is obtained using (4.11) and (4.10) while (4.13) follows from 
the definition of the Hamming distance.

83

 


<!-- pdf-page: 96 -->
4.5  Exercises

Exercise 4.1. Given an infinite family of q-ary codes C of relative distance , and ε > 0
prove that there exists an n0 such that for all n ≥ n0, if Cn ∈ C is an [n, k]q code, then 
k/n < 1 − Hq(δ/2) + ε.  Use this to conclude Proposition 4.1.1.

Exercise 4.2. Pick a (n−k)×n matrix H over Fq at random. Show that with high probability 
the code whose parity check matrix is H achieves the GV bound.

Exercise 4.3. Recall the definition of an ε-biased space from Exercise 2.15.  Show that there 
exists an ε-biased space of size O(k/ε2).

Hint:  Recall part 1 of Exercise 2.15.

Exercise 4.4. Argue that a random linear code as well as its dual both lie on the corresponding 
GV bound.

Exercise 4.5. In Section 4.2.2, we saw that random linear code meets the GV bound.  It is 
natural to ask the question for general random codes.  (By a random (n, k)q code, we mean 
the following:  for each of the qk messages,  pick a random vector from [q]n.  Further,  the 
choices for each codeword is independent.)  We will do so in this problem.

1. Prove  that  a  random  q-ary  code  with  rate  R > 0  with  high  probability  has  relative 
q (1 − 2R − ε).  Note that this is worse than the bound for random 

distance δ ≥ H −1
linear codes in Theorem 4.2.1.

2. Prove that with high probability the relative distance of a random q-ary code of rate 
q (1 − 2R) + ε.  In other words, general random codes are worse than 

R is at most H −1
random linear codes in terms of their distance.
Hint:  Use Chebyshev’s inequality (Lemma 3.1.8).

Exercise 4.6. We saw that Algorithm 4.2.1 can compute an (n, k)q code on the GV bound 
in time qO(n).  Now the construction for linear codes is a randomized construction and it 
is natural to ask how quickly can we compute an [n, k]q code that meets the GV bound.  In 
this problem, we will see that this can also be done in qO(n) deterministic time, though the 
deterministic algorithm is not that straight-forward anymore.

1. Argue that Theorem 4.2.1 gives a qO(kn) time algorithm that constructs an [n, k]q code 
on the GV bound.  (Thus, the goal of this problem is to “shave” off a factor of k from 
the exponent.)

2. A k × n Toeplitz Matrix A = {Ai,j}k , n

i=1, j=1 satisfies the property that Ai,j = Ai−1,j−1. 
In other words, any diagonal has the same value.  For example, the following is a 4 × 6

84



<!-- pdf-page: 97 -->
Toeplitz matrix:

⎛

⎜
⎜
⎝

1 2 3 4 5 6
7 1 2 3 4 5
8 7 1 2 3 4
9 8 7 1 2 3

⎞

⎟
⎟
⎠

A random k × n Toeplitz matrix T ∈ Fk×n
row and column uniformly (and independently) at random.
Prove the following claim:  For any non-zero m ∈ Fk
distributed over Fn

q , that is for every y ∈ Fn

q

q , Pr [m · T = y] = q−n.

 is chosen by picking the entries in the first 

q , the vector m · T  is uniformly 

Hint:  Write down the expression for the value at each of the n positions in the vector m · T  in terms 
of the values in the first row and column of T .  Think of the values in the first row and column as 
variables.  Then divide these variables into two sets (this “division” will depend on m) say S and S. 
Then argue the following:  for every fixed y ∈ Fn
q  and for every fixed assignment to variables in S, 
there is a unique assignment to variables in S such that mT = y.

3. Briefly argue why the claim in part 2 implies that a random code defined by picking 
its generator matrix as a random Toeplitz matrix with high probability lies on the GV 
bound.

4. Conclude that an [n, k]q code on the GV bound can be constructed in time qO(k+n).

Exercise 4.7. Show that one can construct the parity check matrix of an [n, k]q code that 
lies on the GV bound in time qO(n).

Exercise 4.8. So far in Exercises 4.6 and 4.7,  we have seen two constructions of [n, k]q
code on the GV bound that can be constructed in qO(n) time.  For constant rate codes, at the 
time of writing of this book, this is fastest known construction of any code that meets the GV 
bound.  For k = o(n), there is a better construction known, which we explore in this exercise.
We begin with some notation.  For the rest of the exercise we will target a distance of 

d = δn.  Given a message m ∈ Fk

q  and an [n, k]q code C, define the indicator variable:

Further, define

Wm(C) =

{︃ 1 if wt(C(m)) < d

0

otherwise.

D(C) =

∑︂

Wm(C).

m∈Fk

q \{0}

We will also use D(G) and Wm(G) to denote the variables above for the code C generated by 
G.

Given  an  k × n  matrix  M ,  we  will  use  M i  to  denote  the  ith  column  of  M   and  M ≤i
to denote the column submatrix of M  that contains the first i columns.  Finally below we 

85



<!-- pdf-page: 98 -->
will use G to denote a uniformly random k × n generator matrix and G to denote a specific 
instantiation of the generator matrix.  We will arrive at the final construction in a sequence 
of steps.  In what follows define k < (1 − Hq(δ))n for large enough n.

1. Argue that C has a distance d if and only if D(C) < 1.

2. Argue that E [D(G)] < 1.

3. Argue that for any 1 ≤ i < n and fixed k × n matrix G,

E [︁D(G)|G≤i = G≤i, Gi+1 = v

]︁ ≤ E [︁D(G)|G≤i = G≤i]︁ .

min
v∈Fk
q

4. We are now ready to define the algorithm to compute the final generator matrix G: see 
Algorithm 4.5.1.  Prove that Algorithm 4.5.1 outputs a matrix G such that the linear 
code  generated  by  G  is  an  [n, k, δn]q  code.  Conclude  that  this  code  lies  on  the  GV 
bound.

5. Finally, we will analyze the run time of Algorithm 4.5.1.  Argue that Step 2 can be 
implemented in poly (︁n, qk)︁ time.  Conclude Algorithm 4.5.1 can be implemented in 
time poly (︁n, qk)︁.

Hint:  It might be useful to maintain a data structure that keeps track of one number for every non-zero 
m ∈ Fk

q  throughout the run of Algorithm 4.5.1.

Algorithm 4.5.1 qO(k) time algorithm to compute a code on the GV bound
Input: Integer parameters 1 ≤ k ̸= n such that k < (1 − Hq(δ)n)
Output: An k × n generator matrix G for a code with distance δn

1: Initialize G to be the all 0s matrix
2: for every 1 ≤ i ≤ n do 
3:   Gi ← arg minv∈Fk
4: return G

q

]︁
E [︁D(G)|G≤i = G≤i, Gi+1 = v

▷ This initialization is arbitrary

Exercise 4.9. In this problem we will derive the GV bound using a graph-theoretic proof, 
which is actually equivalent to the greedy proof we saw in Section 4.2.1.  Let 1 ≤ d ≤ n and 
q ≥ 1 be integers.  Now consider the graph Gn,d,q = (V, E), where the vertex set is the set of 
all vectors in [q]n.  Given two vertices u ̸= v ∈ [q]n, we have the edge (u, v) ∈ E if and only if 
∆(u, v) < d. An independent set of a graph G = (V, E) is a subset I ⊆ V  such that for every 
u ̸= v ∈ I, we have that (u, v) is not an edge.  We now consider the following sub-problems:

1. Argue that any independent set C of Gn,d,q is a q-ary code of distance d.

86



<!-- pdf-page: 99 -->
2. The degree of a vertex in a graph G is the number of edges incident on that vertex. 
Let ∆ be the maximum degree of any vertex in G = (V, E).Then argue that G has an 
independent set of size at least  |V |

∆+1.

3. Using parts 1 and 2 argue the GV bound.

Exercise  4.10. In  this  problem  we  will  improve  slightly  on  the  GV  bound  using  a  more 
sophisticated graph-theoretic proof.  Let Gn,d,q and N  and ∆ be as in the previous exercise 
(Exercise 4.9).  So far we used the fact that Gn,d,q has many vertices and small degree to 
prove it has a large independent set,  and thus to prove there is a large code of minimum 
distance d.  In this exercise we will see how a better result can be obtained by counting the 
number of “triangles” in the graph.  A triangle in a graph G = (V, E) is a set {u, v, w} ⊂ V
of three vertices such that all three vertices are adjancent, i.e., (u, v), (v, w), (w, u) ∈ E.  For 
simplicity we will focus on the case where q = 2 and d = n/5,  and consider the limit as 
n → ∞.

1. Prove that a graph on N  vertices of maximum degree ∆ has at most O(N ∆2) triangles.

2. Prove that the number of triangle in graph Gn,d,2 is at most

∑︂

2n ·

0≤e≤3d/2

)︃

(︃n
e

· 3e.

Hint:  Fix u and let e count the number of coordinates where at least one of v or w disagree 
with u.  Prove that e is at most 3d/2.

3. Simplify the expression in the case where d = n/5 to show that the number of triangles in 

Gn,n/5,2 is O(N · ∆2−η) for some η > 0.

4. A famous result in the “probabilistic method” shows (and you don’t have to prove this), that 
if a graph on N  vertices of maximum degree ∆ has at most O(N · ∆2−η) triangles, then it 
has an independent set of size Ω( N
∆ log ∆).  Use this result to conclude that there is a binary 
code of block length n and distance n/5 of size Ω(n2n/(︁ n
)︁).  (Note that this improves over 
the GV-bound by an Ω(n) factor.)

n/5

Exercise 4.11. Use part 1 from Exercise 1.7 to prove the Singleton bound.

Exercise 4.12. Let C be an (n, k, d)q code.  Then prove that fixing any n − d + 1 positions 
uniquely determines the corresponding codeword.

Exercise 4.13. Our goal in this problem is to improve the bound in part 1 in Theorem 4.4.1. 
Towards that end,

1. Prove that the following holds for every k ≥ 1.  There exists k + 1 vectors vk

⃦
⃦vk
i

⃦
2 = 1 for every i ∈ [k + 1] and (2) ⟨︁
2
⃦

i , vk
vk
j

i ∈ Rk for 
⟩︁ = − 1
k  for 

i ∈ [k + 1] such that (1) 
every i ̸= j ∈ [k + 1].

87



<!-- pdf-page: 100 -->
2. Using the above part, or otherwise, prove the following result.  Let C be a q code of 
n.  Then |C| ≤ 2(q − 1)n.  (Note that this is a 

block length n and distance 
factor q/(q − 1) better than part 1 in Theorem 4.4.1.)

1 − 1
q

(︂

)︂

Exercise 4.14. Prove that the bound in Exercise 4.13 is tight for q = 2– i.e.  there exists 
binary codes C with block length n and distance n/2 such that |C| = 2n.

Exercise 4.15. Prove that part 1 of Lemma 4.4.3 is tight.

Exercise 4.16. Prove that part 2 of Lemma 4.4.3 is tight.

Exercise 4.17. In this exercise we will prove the Plotkin bound (at least part 2 of Theo­
rem 4.4.1) via a purely combinatorial proof.
Given an (n, k, d)q code C with d >

n define

(︂

)︂

1 − 1
q

∑︂

S =

∆(c1, c2).

c1̸=c2∈C

For the rest of the problem think of C has an |C| × n matrix where each row corresponds to 
a codeword in C.  Now consider the following:

1. Looking at the contribution of each column in the matrix above, argue that

(︃

S ≤

1 −

)︃

1
q

· n|C|2.

2. Look at the contribution of the rows in the matrix above, argue that

S ≥ |C| (|C| − 1) · d.

3. Conclude part 2 of Theorem 4.4.1.

Exercise  4.18.  In  this  exercise,  we  will  prove  the  so  called  Griesmer  Bound.  For  any 
[n, k, d]q, prove that

n ≥

k−1
∑︂

i=0

⌉︃

.

⌈︃ d
qi

Hint:  Recall Exercise 2.18.

Exercise 4.19. Use Exercise  4.18 to prove part 2 of Theorem 4.4.1 for linear codes.

Exercise 4.20. Use Exercise  4.18 to prove Theorem 4.3.1 for linear codes.

88



<!-- pdf-page: 101 -->
4.6  Bibliographic Notes

Theorem 4.2.1 was proved for general codes by Gilbert ([27]) and for linear codes by Var­
shamov ([73]).  Hence,  the bound is called the Gilbert-Varshamov bound.  The Singleton 
bound (Theorem 4.3.1) is due to Singleton [68], though versions of this result with the same 
simple proof seem to have appeared earlier in the work of Joshi [39] who only states the 
bound for the case q = 2.  For larger (but still constant) values of q, better lower bounds 
than the GV bound (i.e., results on the existence of codes) are known.  In particular, for 
every prime power q ≥ 49, there exist linear codes, called algebraic geometric (or AG) codes 
that outperform the corresponding GV bound2. AG codes are out of the scope of this book. 
An introduction to this class of codes can be found, for instance, in a survey by Hholdt, van 
Lint, and Pellikaan [37].  Exercise 4.10 is from the work of Jiang and Vardy [38]. 

2AG codes are only defined for q being a square or a prime and achieve a rate R ≥ 1 − δ − 1√

q−1 .  The 
lower bound of 49 comes from the fact that it is the smallest square of a prime for which this bound improves 
on the q-ary GV bound.

89



<!-- pdf-page: 102 -->
90



<!-- pdf-page: 103 -->
Chapter 5

The Greatest Code of Them All: 
Reed-Solomon Codes

Reed-Solomon codes have been studied a lot in coding theory, and are ubiquitous in practice. 
These codes are basic and based only very elementary algebra.  Yet they are optimal in the 
sense that they exactly meet the Singleton bound (Theorem 4.3.1).  For every choice of n
and k satisfying k ≤ n there is a Reed-Solomon code of dimension k, block length n and 
distance n − k + 1.  As if this were not enough, Reed-Solomon codes turn out to be more 
versatile:  they are fully explicit and they have many applications outside of coding theory. 
(We will see some applications later in the book.)

These  codes  are  defined  in  terms  of  univariate  polynomials  (i.e.  polynomials  in  one 
unknown/variable) with coefficients from a finite field Fq. It turns out that polynomials over 
Fp, for prime p, also help us describe finite fields Fps, for s > 1. We start with a quick review 
of polynomials over finite fields (for a more careful review, please see Appendix B). This will 
allow us to define Reed-Solomon codes over every field Fq, which we do in the second part 
of this chapter.  Finally in the third part of this chapter we discuss “Maximum Distance 
Separable” (MDS) codes, which are codes that meet the Singleton bound.  We discuss their 
properties (which in turn are also properties of the Reed-Solomon codes, since they are MDS 
codes).

5.1  Polynomials and Finite Fields

We start by reviewing the notion of a (univariate) polynomial over a field and define basic 
notions such as degree, evaluation and root of a polynomial.  We conclude with the “degree 
mantra” that relates the degree to the number of roots.

We begin with the formal definition of a (univariate) polynomial.

Definition 5.1.1. A polynomial over a variable X and a finite field Fq is given by a finite 
sequence (f0, f1, . . . , fd) with fi ∈ Fq and is denoted by F (X) = ∑︁d
i=0 fiX i.  The degree of 
F (X), denoted deg(F ), is the largest index i such that fi ̸= 0.

91



<!-- pdf-page: 104 -->
For example, 2X 3 + X 2 + 5X + 6 is a polynomial over F7 of degree 3.  We ignore leading 
zeroes in the definition of a polynomial.  For example 0X 4 + 2X 3 + X 2 + 5X + 6 is the same 
polynomial as 2X 3 + X 2 + 5X + 6.

Next, we define some useful notions related to polynomials. We begin with the notion of 

degree of a polynomial.

We let Fq[X] denote the set of polynomials over Fq, that is, with coefficients from Fq. 
Let F (X), G(X) ∈ Fq[X] be polynomials.  Then Fq[X] has the following natural operations 
defined on it:

Addition:

F (X) + G(X) =

max(deg(F ),deg(G))
∑︂

(fi + gi)X i,

i=0

where the addition on the coefficients is done over Fq.  For example, over F2,

X + (1 + X) = X · (1 + 1) + 1 · (0 + 1) = 1

(recall that over F2, 1 + 1 = 0).1

Multiplication:

F (X) · G(X) =

deg(F )+deg(G)
∑︂

⎛

⎝

min(i,deg(F ))
∑︂

⎞
⎠ X i,

fj · gi−j

i=0

j=0

where all the operations on the coefficients are over Fq.  For example, over F2, X(1 +
X) = X + X 2; (1 + X)2 = 1 + 2X + X 2 = 1 + X 2, where the latter equality follows 
since 2 ≡ 0 mod 2.

Next, we define evaluations of a polynomial.

Definition 5.1.2. Given a polynomial F (X) ∈ Fq[X] and α ∈ Fq, the evaluation of F (X)
at α, denoted F (α) is ∑︁deg F

i=0 fiαi.  Note that F (α) ∈ Fq.2

Finally, polynomials don’t have multiplicative inverses, but one can divide polynomials 
by each other and get quotients and residues.  The following proposition defines this notion 
and states some basic properties.

1This  will  be  a  good  time  to  remember  that  operations  over  a  finite  field  are  much  different  from 

operations over integers/reals.  For example, over reals/integers X + (X + 1) = 2X + 1.

2While this definition requires the coefficients of F  and α to come from the same field, it also extends 
naturally to the case where one of these is from a field FQ extending Fq.  Since Fq ⊆ FQ, if α ∈ Fq and 
F (X) ∈ FQ[X] then the evaluation is well-defined since α ∈ FQ.  If F (X) ∈ Fq[X] then we use the fact that 
Fq[X] ⊆ FQ[X] to get a definition of F (α).  In both cases F (α) ∈ FQ.

92



<!-- pdf-page: 105 -->
Proposition 5.1.3  (Polynomial Division). Given polynomial f (X), g(X) ∈ Fq[X] there exist 
unique polynomials q(X), the quotient, and r(X), the remainder, with deg(r) < deg(g) such 
that f (X) = q(X)g(X) + r(X).  If g(X) = X − α for α ∈ Fq, then r(X) is the degree 0
polynomial f (α), i.e., the evaluation of f  at α.

Definition 5.1.4. α ∈ Fq is a root of a polynomial F (X) if F (α) = 0.

For instance, 1 is a root of 1 + X 2 over F2.
We now state a basic property of polynomials, the “Degree Mantra”, that will be crucial 
to our use of polynomials to build error-correcting codes.  We also introduce the notion of 
irreducible polynomials whose existence is closely related to the existence of finite fields of 
prime power size.  Finally, motivated by the need to make fields and field operations fully 
constructive, we briefly remark on the construction of irreducible polynomials.

Proposition 5.1.5  (“Degree Mantra”). A nonzero polynomial f (X) of degree t over a field 
Fq has at most t distinct roots in Fq.

Proof.  We will prove the theorem by induction on t. If t = 0, we are done. Now, consider 
f (X) of degree t > 0.  If f  has no roots then we are done, else let α ∈ Fq be a root of f .  Let 
g(X) = X − α.  By the fundamental rule of division of polynomials (Proposition 5.1.3) we 
have that f (X) = (X − α)q(X) + f (α) = (X − α)q(X).  It follows that the degree of q(X)
satisfies deg(f ) = 1 + deg(q), and thus deg(q) = t − 1.  Note further that if β ̸= α is a root 
of f  then we have that q(α) = f (β) · (β − α)−1 and so β is also a root of q.  By induction 
we have that q has at most t − 1 roots, and this f  has at most t distinct roots (the at most 
t − 1 roots of q plus the root at α).

The codes we will construct in this chapter do not need any more algebra,  except to 
describe the finite fields that they work over.  To understand finite fields beyond those of 
prime size, we now describe some more basic properties of polynomials.

5.1.1  Irreducibility and Field Extensions

We will start with a special class of polynomials, called irreducible polynomials, which are 
analogous to how prime numbers are special for natural numbers.

Definition 5.1.6. A polynomial F (X) is irreducible if for every G1(X), G2(X) such that 
F (X) = G1(X)G2(X), we have min(deg(G1), deg(G2)) = 0

For example, 1 + X 2 is not irreducible over F2, as

(1 + X)(1 + X) = 1 + X 2.

However, 1 + X + X 2 is irreducible, since its non-trivial factors have to be from the linear 
terms X or X + 1.  However, it can be checked that neither is a factor of 1 + X + X 2.  (In 

93

 


<!-- pdf-page: 106 -->
fact, one can show that 1 + X + X 2 is the only irreducible polynomial of degree 2 over F2– 
see Exercise 5.4.)  A word of caution:  if a polynomial E(X) ∈ Fq[X] has no root in Fq, it 
does not mean that E(X) is irreducible. For example consider the polynomial (1 + X + X 2)2
over F2– it does not have any root in F2 but it obviously is not irreducible.

The main reason we consider irreducibility of polynomials in this book is that irreducible 
polynomials lead us to non-prime fields.  Just as the set of integers modulo a prime is a 
field,  so is the set of polynomials modulo an irreducible polynomial,  and these fields can 
have non-prime size.  We start by first asserting that they form a field;  and then turn to 
properties such as size later.

Theorem 5.1.7. Let E(X) be an irreducible polynomial of degree s ≥ 2 over Fp, p prime. 
Then the set of polynomials in Fp[X] modulo E(X), denoted by Fp[X]/E(X), is a field.

The proof of the theorem above is similar to the proof of Lemma 2.1.4, so we only sketch 

the proof here.  In particular, we will explicitly state the basic tenets of Fp[X]/E(X).

• Elements are polynomials in Fp[X] of degree at most s − 1. Note that there are ps such 

polynomials.

• Addition:  (F (X) + G(X)) mod E(X) = F (X) mod E(X) + G(X) mod E(X) =
F (X) + G(X).  (Since F (X) and G(X) are of degree at most s − 1, addition modulo 
E(X) is just plain polynomial addition.)

• Multiplication:  (F (X) · G(X)) mod E(X) is the unique polynomial R(X) with de­
gree at most s − 1 such that for some A(X), R(X) + A(X)E(X) = F (X) · G(X)

• The additive identity is the zero polynomial, and the additive inverse of any element 

F (X) is −F (X).

• The  multiplicative  identity is  the  constant  polynomial  1.  It  can  be  shown  that  for 

every element F (X), there exists a unique multiplicative inverse (F (X))−1.

For example, for p = 2 and E(X) = 1 + X + X 2, F2[X]/(1 + X + X 2) has as its elements

{0, 1, X, 1 + X}.

The additive inverse of any element in F2[X]/(1 + X + X 2) is the element itself while the 
multiplicative inverses of

in F2[X]/(1 + X + X 2) are

1, X and 1 + X

1, 1 + X and X

respectively.

Next we turn to the size of the field Fq[x]/E(X) for an irreducible polynomial E.

94



<!-- pdf-page: 107 -->
Lemma 5.1.8. Let E(x) ∈ Fq[x] be an irreducible polynomial of degree s.  Then Fq[x]/E(x)
is a field of size qs.

This  follows  from  the  fact  that  the  elements  of  Fq[x]/E(x)  are  in  one  to  one 
Proof. 
correspondence with set of remainders of all polynomials in Fq[X] when divided by E(X)
which in turn is simply the set of all polynomials of degree less than s.  The number of such 
polynomials equals qs (there are q possibilities for the coefficient of X i for every 0 ≤ i <
s).

Thus a natural question to ask is if an irreducible polynomials exist for every degree. 
Indeed,  they  do.  The  following  theorem  asserts  this  and  the  reader  may  find  a  proof  in 
Appendix B.

Theorem 5.1.9. For all s ≥ 2 and Fp, there exists an irreducible polynomial of degree s
over Fp.  In fact, the number of such monic irreducible polynomials is Θ

)︃
.

(︃ ps
s

The result is true even for general finite fields Fq and not just prime fields but we stated 

the version over prime fields for simplicity.

Now recall that Theorem 2.1.5 states that for every prime power ps, there is a unique 

field Fps.  This along with Theorems 5.1.7, Lemma 5.1.8 and 5.1.9 imply that:

Corollary 5.1.10. The field Fps is Fp[X]/E(X), where E(X) is an irreducible polynomial 
of degree s.

The facts about irreducible polynomials listed above give sufficient information not only 
to determine when finite fields exist, but also how to represent them so as to be able to add, 
multiply or invert elements, given an irreducible polynomial of degree s over Fp.  To make 
our ability to work with fields completely algorithmic we need one more ingredient — one 
that allows us to find an irreducible polynomial of degree s in Fp fast.  We now turn to this 
question.

5.1.2  Finding Irreducible Polynomials

Given any monic 3 polynomial E(X) of degree s, it can be verified whether it is an irreducible 
polynomial by checking if the following two conditions hold (where gcd(F (X), G(X)) is the 
greatest common denominator (or factor) of polynomials F (X) and G(X)):

• gcd(E(X), X qs − X) = E(X), and

• For every t ̸∈ {1, s} that divides s, we have gcd(E(X), X qt − X) = 1

3I.e. the coefficient of the highest degree term is 1. It can be checked that if E(X) = esX s + es−1X s−1 +

· · · + 1 is irreducible, then e−1

s

· E(X) is also an irreducible polynomial.

95

 


<!-- pdf-page: 108 -->
This is true as every irreducible polynomial in Fq[X] of degree exactly s divides the poly­
nomial  X qs − X  (see  Proposition  B.5.14).  Since  Euclid’s  algorithm  for  computing  the 
gcd(F (X), G(X)) can be implemented in time polynomial in the minimum of deg(F ) and 
deg(G) and log q (see Section B.7.2), this implies that checking whether a given polynomial 
of degree s over Fq[X] is irreducible can be done in time poly(s, log q).  It turns out we can 
improve upon the complexity of checking whether a given polynomial is irreducible slightly 
(see Exercise 5.5).

We now turn to the question of finding an irreducible polynomial, given q and s. A brute 
force algorithm can simply enumerate all monic polynomials of degree s over Fq and test 
each one for irreducibility.  This takes poly(qs) time.  To get a more efficient algorithm we 
use randomness and Theorem 5.1.9, while will give us a Las Vegas algorithm4 to generate an 
irreducible polynomial of degree s over Fq.  We give the code below, but note that the idea 
of the algorithm is to keep on generating random polynomials until it comes across an irre­
ducible polynomial (Theorem 5.1.9 implies that the algorithm will check O (ps) polynomials 
in expectation).  Algorithm 5.1.1 presents the formal algorithm.

Algorithm 5.1.1 Generating Irreducible Polynomial
Input: Prime power q and an integer s > 1
Output: A monic irreducible polynomial of degree s over Fq
1: b ← 0
2: while b = 0 do
3:   F (X) ← X s + ∑︁s−1
4:  
5:  
6:  
7:  
8:  
9: return F (X)

if gcd(F (X), X qs − X) = F (X) then

if gcd(F (X), X qt − X) ̸= 1) then

for all t ̸∈ {1, s} that divides s do

b ← 1.

b ← 0.

i=0 fiX i, where each fi is chosen uniformly at random from Fq.

The above discussion implies the following:

Corollary 5.1.11. There is a Las Vegas algorithm to generate an irreducible polynomial of 
degree s over any Fq in expected time poly(s, log q).

The above implies that we can ‘construct’ a finite field Fq in in randomized poly(log q)
time.  (See Exercise 5.6 for more including details on what it means to ‘construct’ a finite 
field.)

This concludes our discussion of polynomials, polynomial arithmetic and properties of 

polynomials.  We now turn to using them to building codes.

4A  Las  Vegas  algorithm  is  a  randomized  algorithm  which  always  succeeds  and  we  consider  its  time 

complexity to be its expected worst-case run time.

96



<!-- pdf-page: 109 -->
5.2  Reed-Solomon Codes

Recall that the Singleton bound (Theorem 4.3.1) states that for every (n, k, d)q code, k ≤
n − d + 1.  Next, we will study Reed-Solomon codes, which meet the Singleton bound (i.e. 
satisfy k = n − d + 1) but have the unfortunate property that q ≥ n.  Note that this implies 
that the Singleton bound is tight, at least for q ≥ n.

We begin with the definition of Reed-Solomon codes.

Definition 5.2.1  (Reed-Solomon code). Let Fq be a finite field, and choose n and k satisfying 
k ≤ n ≤ q.  Fix a sequence α = (α1, α2, ...αn) of n distinct elements (also called evaluation 
points) from Fq. We define an encoding function for Reed-Solomon code RSq[α, k] : Fk
q → Fn
q
as  follows.  Map  a  message  m = (m0, m1, ..., mk−1)  with  mi ∈ Fq  to  the  degree  k − 1
polynomial.

where

m ↦→ fm(X),

fm(X) =

k−1
∑︂

i=0

miX i.

(5.1)

Note that fm(X) ∈ Fq[X] is a polynomial of degree at most k − 1.  The encoding of m is the 
evaluation of fm(X) at all the αi’s :

RSq[α, k](m) = (fm(α1), fm(α2), ..., fm(αn)) .

When  q, α  and  k  are  known  from  context,  we  suppress  them  in  the  notation  and  simply 
refer to the map as RS.  We call the image of this map, i.e., the set {RS[m]|m ∈ Fk
q }, the 
Reed-Solomon code or RS code. A common special case is n = q −1 with the set of evaluation 
points being F∗ def= F \ {0}.

For example, the first row below are all the codewords in the [3, 2]3 Reed-Solomon codes 
where the evaluation points are F3 (and the codewords are ordered by the corresponding mes­
sages from F2
3 in lexicographic order where for clarity the second row shows the polynomial 
fm(X) for the corresponding m ∈ F2

3 in gray):

(0,0,0),  (1,1,1),  (2,2,2),  (0,1,2),  (1,2,0),  (2,0,1),  (0,2,1),  (1,0,2),  (2,1,0) 
2X+2
X+1,

2X+1,

X+2,

2X,

X,

0,

1,

2,

Notice  that  by  definition,  the  entries  in  {α1, ..., αn}  are  distinct  and  thus,  must  have 

n ≤ q.

In what follows we will describe the basic properties of Reed-Solomon codes. In principle 
we should refer to the codes as RSq[α, k] since all the parameters are needed to specify the 
code.  However for notation simplicity we will assume k, n, q, and α1, . . . , αn ∈ Fq are fixed 
and satisfy k ≤ n ≤ q allowing us to refer to the resulting code as simply RS.  (Thus all 
results below hold for every such choice of k, n, q and α1, . . . , αn.)

Claim 5.2.2. RS codes are linear codes.

97



<!-- pdf-page: 110 -->
The  proof  follows  from  the  fact  that  if  a ∈ Fq  and  f (X), g(X) ∈ Fq[X]  are 
Proof. 
polynomials of degree ≤ k − 1, then af (X) and f (X) + g(X) are also polynomials of degree 
≤ k − 1.  In particular, let messages m1 and m2 be mapped to fm1(X) and fm2(X) where 
fm1(X), fm2(X) ∈ Fq[X] are polynomials of degree at most k − 1 and because of the mapping 
defined in (5.1), it can be verified that:

and

In other words,

fm1(X) + fm2(X) = fm1+m2(X),

afm1(X) = fam1(X).

RS(m1) + RS(m2) = RS(m1 + m2)

aRS(m1) = RS(am1).

Therefore RS is a [n, k]q linear code.

The second and more interesting claim is the following:

Claim 5.2.3. The minimum distance of RS is n − k + 1.

The claim on the distance follows from Proposition 5.1.5 which asserted that every non-
zero polynomial of degree k − 1 over Fq[X] has at most k − 1 roots.  The proof below uses 
this to prove a lower bound on the distance.  The upper bound follows from the Singleton 
Bound (Theorem 4.3.1).  Details below.

Fix arbitrary m1 ̸= m2 ∈ Fk

q .  Note that fm1(X), fm2(X) ∈ Fq[X]
Proof of Claim 5.2.3. 
are distinct polynomials of degree at most k−1 since m1 ̸= m2 ∈ Fk
q . Then fm1(X)−fm2(X) ̸=
0 also has degree at most k − 1.  Note that wt(RS(m2) − RS(m1)) = ∆(RS(m1), RS(m2)). 
The weight of RS(m2) − RS(m1) is n minus the number of zeroes in RS(m2) − RS(m1), which 
is equal to n minus the number of roots that fm1(X) − fm2(X) has among {α1, ..., αn}. That 
is,

∆(RS(m1), RS(m2)) = n − |{αi | fm1(αi) = fm2(αi)}|.

By Proposition 5.1.5, fm1(X)−fm2(X) has at most k −1 roots. Thus, the weight of RS(m2)−
RS(m1) is at least n−(k−1) = n−k+1. Therefore d ≥ n−k+1, and since the Singleton bound 
(Theorem 4.3.1) implies that d ≤ n − k + 1, we have d = n − k + 1.5 The argument above also 
shows that distinct polynomials fm1(X), fm2(X) ∈ Fq[X] are mapped to distinct codewords. 
(This is because the Hamming distance between any two codewords is at least n − k + 1 ≥ 1, 
where the last inequality follows as k ≤ n.)  Therefore, the code contains qk codewords and 
has dimension k.  The claim on linearity of the code follows from Claim 5.2.2.

5See Exercise 5.2 for an alternate direct argument.

98

 
 


<!-- pdf-page: 111 -->
We thus have an exact understanding of the dimension and distance of the Reed-Solomon 
codes, which we summarize in the theorem below.  The theorem also notes that the param­
eters match those of the Singleton Bound.  Recall that the Plotkin bound (Corollary 4.4.2) 
implies that to achieve the Singleton bound, the alphabet size cannot be a constant.  Thus, 
some growth of q with n is unavoidable to match the Singleton bound, and the Reed-Solomon 
codes match it with q ≥ n.

Theorem 5.2.4. RS is a [n, k, n − k + 1]q code.  That is,  RS codes match the Singleton 
bound.

Finally,  we  describe  a  generator  matrix  for  RS  codes.  Such  a  matrix  is  guaranteed 
to exist  by Claim  5.2.2,  but  now we give  an  explicit  one.  By  Definition  5.2.1,  any basis 
fm1, ..., fmk of polynomial of degree at most k − 1 gives rise to a basis RS(m1), ..., RS(mk) of 
the code.  A particularly nice polynomial basis is the set of monomials 1, X, ..., X i, ..., X k−1. 
The corresponding generator matrix, whose ith row (numbering rows from 0 to k − 1 ) is

and this generator matrix is called the Vandermonde matrix of size k × n:

(αi

1, αi

2, ..., αi

j, ..., αi
n)

⎛

⎜
⎜
⎜
⎜
⎜
⎜
⎜
⎜
⎜
⎜
⎝

1
α1
α2
1
...
αi
1
...
αk−1
1

1
α2
α2
2
...
αi
2
...
αk−1
2

1
1
· · ·
αj
α2
· · ·
j
...
. . .
αi
· · ·
j
...
. . .
· · · αk−1

j

⎞

⎟
⎟
⎟
⎟
⎟
⎟
⎟
⎟
⎟
⎟
⎠

1
1
· · ·
αn
α2
· · ·
n
...
. . .
αi
· · ·
n
...
. . .
· · · αk−1

n

The class of codes that match the Singleton bound have their own name, which we define 

and study next.

5.3  Maximum Distance Separable Codes and Proper­

ties

Definition 5.3.1  (MDS codes). An (n, k, d)q code is called Maximum Distance Separable 
(MDS) if d = n − k + 1.

Thus, Reed-Solomon codes are MDS codes.
Next, we prove an interesting property of an MDS code C ⊆ Σn with integral dimension 

k.  We begin with the following notation.

Definition 5.3.2. For every subset of indices S ⊆ [n] of size exactly k  and a code C ⊆ Σn, 
CS is the set of all codewords in C projected onto the indices in S.

99



<!-- pdf-page: 112 -->
MDS  codes  have  the  following  nice  property  that  we  shall  prove  for  the  special  case  of 
Reed-Solomon codes first and subsequently for the general case as well.

Proposition  5.3.3.  Let  C ⊆ Σn  of  integral  dimension  k  be  an  MDS  code,  then  for  all 
S ⊆ [n] such that |S| = k, we have |CS| = Σk.

Before proving Proposition 5.3.3 in its full generality,  we present its proof for the special 
case of Reed-Solomon codes.
Consider any S ⊆ [n] of size k and fix an arbitrary v = (v1, . . . , vk) ∈ Fk
q , we need to show 
that there exists a codeword c ∈ RS (assume that the RS code evaluates polynomials of 
degree at most k − 1 over α1, . . . , αn ⊆ Fq) such that cS = v. Consider a generic degree k − 1
polynomial F (X) = ∑︁k−1
i=0 fiX i.  Thus, we need to show that there exists F (X) such that 
F (αi) = vi for all i ∈ S,  where |S| = k.

For notational simplicity, assume that S = [k]. We think of fi’s as unknowns in the equations 
that arise out of the relations F (αi) = vi.  Thus, we need to show that there is a solution to 
the following system of linear equations:

(︁ p0 p1

· · · pk−1

)︁

⎛

⎜
⎜
⎜
⎜
⎜
⎝

1
α1
α2
1
...
αk−1
1

1
αi
α2
i
...
αk−1
i

⎞

⎟
⎟
⎟
⎟
⎟
⎠

1
αk
α2
k
...
αk−1
k

=

⎞

⎟
⎟
⎟
⎟
⎟
⎠

⎛

⎜
⎜
⎜
⎜
⎜
⎝

v1
v2
v3
...
vk

The above constraint matrix is a Vandermonde matrix and is known to have full rank (see 
Exercise 5.3). Hence, by Exercise 2.7, there always exists a unique solution for (p0, . . . , pk−1). 
This completes the proof for Reed-Solomon codes.

Next, we prove the property for the general case which is presented below

Proof  of  Proposition  5.3.3.  Consider  a  |C| × n  matrix  where  each  row  represents  a 
codeword in C.  Hence, there are |C| = |Σ|k rows in the matrix.  The number of columns 
is equal to the block length n of the code.  Since C is Maximum Distance Separable,  its 
distance d = n − k + 1.

̸= cj ∈ C,  the 
Let  S ⊆ [n]  be  of  size  exactly  k.  It  can  be  verified  that  for  every  ci
corresponding projections ci
S ∈ CS are not the same.  As otherwise △(ci, cj) ≤ d − 1, 
which is not possible as the minimum distance of the code C is d. Therefore, every codeword 
in C gets mapped to a distinct codeword in CS. As a result, |CS| = |C| = |Σ|k. As CS ⊆ Σk, 
(cid:50)
this implies that CS = Σk, as desired. 

S and cj

Proposition 5.3.3 implies an important property in pseudorandomness: see Exercise 5.14 

for more.

100



<!-- pdf-page: 113 -->
5.4  Exercises

Exercise 5.1. Prove that every function f : Fq → Fq is equivalent to a polynomial P (X) ∈
Fq[X] of degree at most q − 1:  that is, for every α ∈ Fq

Furthermore, prove the choice of this polynomial P  is unique.

f (α) = P (α).

Exercise 5.2. For every [n, k]q Reed-Solomon code, i.e., for every RSq[α, k] for every choice 
of k ≤ n ≤ q and α = (α1, . . . , αn), exhibit two codewords that are at Hamming distance 
exactly n − k + 1.

Exercise 5.3. Let α1, . . . , αk be distinct elements in a field F.  Consider the k × k Van­
dermonde matrix V (α1, . . . , αk) whose (i, j)’th entry is αj−1
 for i, j ∈ {1, 2, . . . , k}.  Prove 
that V (α1, . . . , αk) has full rank.  Use this property to prove that a Reed-Solomon code of 
dimension k can efficiently correct n − k erasures.

i

Exercise 5.4. Prove that X 2 + X + 1 is the unique irreducible polynomial of degree two over 
F2.

Exercise 5.5. Let s ≥ 1 be an integer and let r be the number of prime divisors of s and 
let τ (s) be the number of divisors of s.  In this problem we will consider the number of gcd
operations we need to decide whether a given polynomial of degree s is irreducible or not.

1. Prove that τ (s)−1 calls to gcd are enough to decide if a degree s polynomial is irredicible 

or not.
Hint:  This is what is used in Algorithm 5.1.1.

2. Let p1, . . . , pr be the prime divisors of s.  Then prove that a degree s polynomial E(X)

is irreducible iff

• gcd(E(X), X qs − X) = E(X), and

• For every i ∈ [r], we have gcd

(︂

E(X), X q

s

pi − X

)︂

= 1

3. Using the above part or otherwise argue that r + 1 calls to gcd are enough to decide 
if a degree s polynomial is irredicible or not.  Further, argue that this is exponentially 
fewer calls than the result in the first part.
Hint:  Prove and then use the fact that τ (s) ≥ 2r.

Exercise 5.6. In this problem we will consider what it means to ‘construct’ a finite field. 
For simplicity, assume that q = ps for some s ≥ 1.  A representation of a finite field Fq is a 
triple (S, θ, f ) where S ⊂ {0, 1}∗ with |S| = ps is set of representations of elements on Fq, 
θ is some ‘auxiliary’ representation and a bijection f : Fps → S.  For every α ∈ Fps, f (α)
is the representation Also implicit in this definition is given α, β ∈ Fs
p how one computes 

101



<!-- pdf-page: 114 -->
f (α) + f (β), −f (α), f (α) · f (β). Further, one needs to identify the additive and multiplicative 
identities in S.  Finaly, given a non-zero element α ∈ Fps, compute f (α)−1.  The auxiliary 
representation θ can be used to implement these operations.

We call a representation efficient of all of the operations can be supported in poly(log q)
time.  In this problem we will explore the problem of constructing an efficient representation 
of a finite field in poly(log q) (randomized) time.

1. Let E(X) be an irreducible polynomial of degree s. Given E(X), prove that the repreen­
tation Fp[X]/E(X) (i.e.  θ = E(X) and for every u ∈ Fs
p,6 f (u) = fu(X) as per (5.1) 
and the additive and multiplicative identities are the 0 and 1 polynomials) is an efficient 
representation.

Hint:  The following fact might be useful:  for every α ∈ F∗

q, αq−2 = α−1.

2. Using the above part or otherwise prove that for every prime p and integer s ≥ 1, an 
efficient representation of Fps can be computed in (randomized) poly(s log p) time.

Exercise  5.7.  In  Exercise  2.17,  we  saw  that  any  linear  code  can  be  converted  in  to  a 
systematic  code.  In  other  words,  there  is  a  map  to  convert  Reed-Solomon  codes  into  a 
systematic one.  In this exercise the goal is to come up with an explicit encoding function 
that results in a systematic Reed-Solomon code.

In  particular,  given  the  set  of  evaluation  points  α1, . . . , αn,  design  an  explicit  map  f
from Fk
q  to a polynomial of degree at most k − 1 such that the following holds.  For every 
message m ∈ Fk
q , if the corresponding polynomial is fm(X), then the vector (fm(αi))i∈[n] has 
the message m appear in the corresponding codeword (say in its first k positions).  Further, 
prove that this map results in an [n, k, n − k + 1]q code.

Exercise 5.8. Let α ⊆ Fq
that

q be a vector enumerating all the elements of the field Fq.  Prove 

(RSq[α, k])⊥ = (RSq[α, q − k]) .

that is, the dual of these Reed-Solomon code are Reed-Solomon codes themselves.  Conclude 
that the class of Reed-Solomon codes contain self-dual code (see Exercise 2.33 for a definition).

Exercise 5.9. We have defined Reed-Solomon codes as evaluation codes. They are sometimes 
also defined in an alternate way, as coefficients of polynomials with pre-specified roots, and 
this exercise will demonstrate the equivalence of the two ways.

Let Fq be a field, and F∗
q be the multiplicative group of its nonzero elements. Let n = q − 1
and let α be a generator of F∗
q so that the vector α = (1, α, . . . , αn−1) has all distinct elements 
and αn = 1.  Consider the Reed-Solomon code over a field Fq with evaluation points being α:

RSq[α, k] = {(p(1), p(α), . . . , p(αn−1)) | p(X) ∈ F[X] has degree ≤ k − 1}.

6Note that there is a bijection between Fps  to Fs

p and hence we can define f  on Fs

p instead of Fps .

102



<!-- pdf-page: 115 -->
Prove that

RSq[α, k] = {(c0, c1, . . . , cn−1) ∈ Fn | C(αℓ) = 0 for 1 ≤ ℓ ≤ n − k ,

 where C(X) = c0 + c1X + · · · + cn−1X n−1} .

(5.2)

Hint:  Exercise 2.3 might be useful.

Exercise 5.10  (Generalized Reed-Solomon Codes). 

For a field F with |F| ≥ n, an n-tuple α = (α1, α2, . . . , αn) of n distinct elements of F, 
and a vector v = (v1, v2, . . . , vn) ∈ (F∗)n of n (not necessarily distinct) nonzero  elements 
from F, the Generalized Reed-Solomon code GRSF[α, k, v] is defined as follows:

GRSF[α, k, v] = {(v1 ·p(α1), v2 ·p(α2), . . . , vn ·p(αn)) | p(X) ∈ F[X] has degree < k} . (5.3)

(In particular, note that RSq[α, k] = GRSFq [α, k, (1, . . . , 1)].)

1. Prove that GRSF[α, k, v] is an [n, k, n − k + 1]F linear code.

2. Prove that the dual code of GRSF[α, k, v] is

GRSF[α, k, v]⊥ = GRSF[α, n − k, u]

for u = (u1, u2, . . . , un) ∈ (F∗)n where for i = 1, 2, . . . , n,

ui =

1

∏︁

vi

j̸=i(αi − αj)

.

Hint: First show that it suffices to prove that for every polynomial p of degree < k and every polynomial 
q of degree < n − k, it is the case that ∑︁n
i=1 uivip(αi)q(αi) = 0.  Next, express an arbitrary polynomial 
h  of  degree  < n  in  terms  of  the  Lagrange  polynomials  Li  that  satisfy  Li(αj) = 1  if  i = j  and  0
otherwise.  Apply to the polynomial h = p · q and use the fact that the coefficient of xn−1 in h is zero.

3. Prove that the dual of RS[α, k], when α enumerates all elements of F∗

q, is the variant 
of a Reed-Solomon code that maps a message polynomial m(X) with degree < n − k to 
evaluations of X · m(X) on α.

4. Derive Exercise 5.8 as a corollary of Part 2.

Exercise 5.11. In this problem we will look at a very important class of codes called BCH 
codes7.

Fix  an  integer  m  and  let  q = 2m  and  n = q − 1.  Let  non-zero  elements  of  the  field 
F2m be {η1, . . . , ηn} and let α = (η1, . . . , ηn).  Given non-negative integer k ≤ n, the binary 
BCH code, denoted CBCH = CBCH(m, k), is defined as RS2m[α, k] ∩ Fn
2 .  In other words CBCH
consists of those codewords in the Reed-Solomon code RS2m[α, k] all of whose coordinates lie 
in the subfield F2 ⊆ F2m.

7The acronym BCH stands for Bose-Chaudhuri-Hocquenghem, the discoverers of this family of codes.

103



<!-- pdf-page: 116 -->
1. Let d = n − k + 1.  Prove that CBCH is a binary linear code of distance at least d and 

dimension at least n − (d − 1) log2(n + 1).

Hint:    Use the characterization (5.2) of the Reed-Solomon code from Exercise 5.9.

2. Prove a better lower bound of n − ⌈︁ d−1

2

⌉︁ log2(n + 1) on the dimension of CBCH.

Hint:  There are redundant checks among the parity checks (5.2) defining CBCH, using the fact that 
the coefficients are in F2.

3. For d = 3, CBCH is the same as another code we have seen.  What is that code?

4. Define the subcode of CBCH with a global parity check, i.e., the condition c1 + c2 + · · · +
cn = 0 (over F2). Let d be an even integer. Show how to use the BCH code with a global 
parity check to construct a binary linear code of distance at least d and dimension at 
least n − (d/2 − 1) log2(n + 1) − 1.

5. Conclude that for all n of the form 2m − 1 and integers d, 2 ≤ d < n/ log2(n1), one can 
log2(n+1)−1.

construct an [n, k′, d′]2 binary linear code with d′ ≥ d and k′ ≥ n−

⌋︂

⌊︂ d−1
2

6. Prove that the 

⌊︂ d−1
2
Hint:  What does the Hamming bound say?

⌋︂

 factor cannot be any smaller.

Exercise  5.12. In  this  exercise,  we  will  consider  BCH-like  codes  in  the  theme  of  Exer­
cise 5.11, but applied to the GRS codes of Exercise 5.10.  Consider the Generalized Reed-
Solomon code CGRS = GRSF[α, k, v] defined in (5.3) of dimension k and block length n over 
a field F = F2m.  Now, define its binary intersection code C ∗ := CGRS ∩ Fn
2 , which will be the 
object of study in this exercise.

1. Prove that C ∗ is a code of distance at least d := n − k + 1.

2. Prove that C ∗ is a binary linear code of rate at least 1 − (n−k)m

n

.

Hint:  How many parity checks are needed to define this code?

3. Let c ∈ Fn

2  be a nonzero binary vector.  Prove that for every choice of the evaluation 
points sequence α there are at most (2m−1)k choices of the vector v for which c ∈ CGRS.

4. Using the above,  prove that if the integer D satisfies Vol2(n, D − 1) < (2m − 1)n−k
)︁), then there exists a vector v ∈ (F∗)n such that the 

(where Vol2(n, D − 1) = ∑︁D−1
minimum distance of the binary code C ∗ is at least D.

(︁n
i

i=0

5. Using parts 2 and 4 above, prove that the family of codes GRSF[α, k, v] ∩ Fn

2  contains 

binary linear codes that meet the Gilbert-Varshamov bound.

104



<!-- pdf-page: 117 -->
Exercise 5.13. Recall the definition of Hadamard codes from Section 2.6:  the [2r, r, 2r−1]2
Hadamard code is generated by the r × 2r matrix whose ith (for 0 ≤ i ≤ 2r − 1) column is 
the binary representation of i.  This exercise gives a polynomial view of Hadamard codes.

Specifically, prove that the Hadamard codeword for the message (m1, m2, . . . , mr) ∈ {0, 1}r
is  the  evaluation  of  the  (multivariate)  polynomial  m1X1 + m2X2 + · · · + mrXr  (where 
X1, . . . , Xr are the r variables) over all the possible assignments to the variables (X1, . . . , Xr)
from {0, 1}r.

Using the definition of Hadamard codes above (re)prove the fact that the code has distance 

2r−1.

Exercise 5.14. Recall the definition of t-wise independence from Exercise 2.14, namely, a 
set S ⊆ Fn
q  is said to be a t-wise independent source (for some 1 ≤ t ≤ n) if for every I ⊆ [n]
with |I| = t, a uniformly random sample (X1, . . . , Xn) from S satisfies the property that the 
variables {Xi|i ∈ I} are uniform and independent over Fq.  (Note that such a sample can 
be obtained using log2 |S| random bits.)  We will explore properties of these objects in this 
exercise.

1. Let C be a linear code that does not have any coordinate that is 0 for every codeword. 

Prove that C is a 1-wise independent source.

2. Prove that every [n, k]q MDS code is a k-wise independent source but is not a k +1-wise 

independent source.

3. Using Part 2 or otherwise, prove that there exists a k-wise independent source S ⊆ Fm
q
of size at most qk for q ≥ m.  Now show how to pick q so that S can be viewed as 
a k-wise independent source in Fm log2 q
 of size at most (2m)k.  Finally set m and q
as functions of n and k to show that k · (log2 n − log2 log2 n + O(1))-random bits are 
enough to sample from a k-wise independent source over Fn
2 .

2

4. For 0 < p ≤ 1/2, we say the n binary random variables X1, . . . , Xn are p-biased and 
t-wise independent if any of the t random variables are independent and Pr [Xi = 1] = p
for every i ∈ [n].  For the rest of the problem, let p be a power of 1/2.  Then show 
that any t · log2(1/p)-wise independent random variables can be converted into t-wise 
independent p-biased random variables.  Conclude that one can construct such sources 
with t log2(1/p)(1+log2 (n log2(1/p))) uniformly random bits. Then improve this bound 
to t(1 + max(log2(1/p), log2 n)) uniformly random bits.

Exercise  5.15. In this exercise,  we improve over the randomness used in Part 3 of Ex­
ercise 5.14 to sample from a k-wise independent source over Fn
2 ,  by nearly a factor of 2. 
Specifically, use Exercises 2.14 and 5.11 part 5 to prove the following: for every integers n, k
with 1 ≤ k ≤ n, at most ⌊ k
2 ⌋ log2(2n)) random bits are enough to compute n-bits that are 
k-wise independent.

Exercise 5.16. In many applications, errors occur in “bursts”—i.e., all the error locations 
are contained in a contiguous region (think of a scratch on a DVD or disk).  In this problem 
we will use how one can use Reed-Solomon codes to correct bursty errors.

105



<!-- pdf-page: 118 -->
An error vector e ∈ {0, 1}n is called a t-single burst error pattern if all the non-zero bits 
in e occur in the range [i, i + t − 1] for some 1 ≤ i ≤ n = t + 1.  Further, a vector e ∈ {0, 1}n
is called a (s, t)-burst error pattern if it is the union of at most s t-single burst error pattern 
(i.e.  all non-zero bits in e are contained in one of at most s contiguous ranges in [n]).

We call a binary code C ⊆ {0, 1}n to be (s, t)-burst error correcting if one can uniquely 
decode from any (s, t)-burst error pattern.  More precisely, given an (s, t)-burst error pattern 
e and any codeword c ∈ C, the only codeword c′ ∈ C such that (c + e) − c′ is an (s, t)-burst 
error pattern satisfies c′ = c.

1. Prove that if C is (st)-error correcting (in the sense of Definition 1.3.5),  then it is 
also (s, t)-burst error correcting.  Conclude that for every ε > 0, there exists code with 
rate Ω(ε2) and block length n that is (s, t)-burst error correcting for every s, t such that 
s · t ≤ (︁ 1

4 − ε)︁ · n.

2. Prove that for every rate R > 0 and for large enough n, there exist (s, t)-burst error 
)︁.  In particular, one can correct 
2 − ε fraction of burst-errors (as long as each burst is “long enough”) with rate 

)︁ · n and t ≥ Ω (︁ log n

2

ε

correcting as long as s · t ≤ (︁ 1−R−ε
from  1
Ω(ε) (compare this with item 1).
Hint:  Use Reed-Solomon codes.

Exercise 5.17. In this problem, we will consider the number-theoretic counterpart of Reed-
Solomon codes.  Let 1 ≤ k < n be integers and let p1 < p2 < · · · < pn be n distinct primes. 
Denote K = ∏︁k
i=1 pi.  The notation ZM  stands for integers modulo M , 
i.e., the set {0, 1, . . . , M − 1}.  Consider the Chinese Remainder code defined by the encoding 
map E : ZK → Zp1 × Zp2 × · · · × Zpn defined by:

i=1 pi and N = ∏︁n

E(m) = (m mod p1, m mod p2, · · · , m mod pn) .

(Note that this is not a code in the usual sense we have been studying since the symbols at 
different positions belong to different alphabets.  Still notions such as distance of this code 
make sense and are studied in the question below.)

E(m2)i and bi = 0 otherwise.  Prove that ∏︁n

Suppose that m1 ̸= m2.  For 1 ≤ i ≤ n, define the indicator variable bi = 1 if E(m1)i ̸=
i=1 pbi
Use the above to deduce that when m1 ̸= m2, the encodings E(m1) and E(m2) differ in 

i > N /K.

at least n − k + 1 locations.
Exercise 5.18. In this problem, we will consider derivatives over a finite field Fq.  Unlike 
the  case  of  derivatives  over  reals,  derivatives  over  finite  fields  do  not  have  any  physical 
interpretation but as we shall see shortly, the notion of derivatives over finite fields is still a 
useful concept.  In particular, given a polynomial f (X) = ∑︁t
i=0 fiX i over Fq, we define its 
derivative as

t−1
∑︂

f ′(X) =

(i + 1) · fi+1 · X i.

Further, we will denote by f (i)(X), the result of applying the derivative on f i times.  In this 
problem, we record some useful facts about derivatives.

i=0

106



<!-- pdf-page: 119 -->
1. Define R(X, Z) = f (X + Z) = ∑︁t

i=0 ri(X) · Z i.  Then for every j ≥ 1,

f (j)(X) = j! · rj(X).

2. Using part 1 or otherwise, show that for every j ≥ char(Fq),8 f (j)(X) ≡ 0.

3. Let j < char(Fq).  Further,  assume that for every 0 ≤ i < j,  f (i)(α) = 0 for some 

α ∈ Fq.  Then prove that (X − α)j divides f (X).

4. Finally,  prove the following generalization of the degree mantra (Proposition 5.1.5). 
Let f (X) be a non-zero polynomial of degree t and m ≤ char(Fq).  Then there exists at 
⌋︁ distinct elements α ∈ Fq such that f (j)(α) = 0 for every 0 ≤ j < m.
most ⌊︁ t

m

Exercise  5.19. In this exercise,  we will consider a code that is related to Reed-Solomon 
codes and uses derivatives from Exercise 5.18.  These codes are called derivative codes.

Let m ≥ 1 be an integer parameter and consider parameters k < char(Fq) and n such 
that m < k < nm.  Then the derivative code with parameters (n, k, m) is defined as follow. 
Consider any message m ∈ Fk
q  and let fm(X) be the message polynomial as defined for the 
Reed-Solomon code.  Let α1, . . . , αn ∈ Fq be distinct elements.  Then the codeword for m is 
given by

⎛

⎜
⎜
⎜
⎝

fm(α1)
f (1)
m (α1)
...
f (m−1)
m

fm(α2)
f (1)
m (α2)
...
(α1) f (m−1)

m

(α2)

fm(αn)
· · ·
f (1)
m (αn)
· · ·
...
...
· · · f (m−1)
m

(αn)

⎞

.

⎟
⎟
⎟
⎠

1. Prove that the above code is linear over Fq, meaning that if c1, c2 ∈ (Fm

q )n are codewords, 
then so is αc1 + βc2 for all α, β ∈ Fq.  Here we define αv for α ∈ Fq and v ∈ Fm
q  as 
multiplication of coordinates of v by α, and as usual αc1 is componentwise multiplication 
of symbols of c1 by α.

2. Prove that the above code has rate k/(nm) and distance at least n − ⌊︁ k−1

m

⌋︁.

Exercise  5.20.  In  this  exercise,  we  will  consider  another  code  related  to  Reed-Solomon 
codes that are called Folded Reed-Solomon codes.  We will see a lot more of these codes in 
Chapter ??.

Let m ≥ 1 be an integer parameter and let α1, . . . , αn ∈ Fq are distinct elements such 

that for some element γ ∈ F∗

q, the sets

{αi, αiγ, αiγ2, . . . , αiγm−1},

(5.4)

8char(Fq) denotes the characteristic of Fq.  That is, if q = ps for some prime p, then char(Fq) = p.  Any 

natural number i in Fq is equivalent to i mod char(Fq).

107



<!-- pdf-page: 120 -->
are pair-wise disjoint for different i ∈ [n]. Then the folded Reed-Solomon code with parameters 
(m, k, n, γ, α1, . . . , αn) is defined as follows.  Consider any message m ∈ Fk
q  and let fm(X) be 
the message polynomial as defined for the Reed-Solomon code.  Then the codeword for m is 
given by:

⎛

⎜
⎜
⎜
⎝

fm(α1)
fm(α1 · γ)
...

fm(α2)
fm(α2 · γ)
...

fm(α1 · γm−1) fm(α2 · γm−1)

fm(αn)
fm(αn · γ)
...

· · ·
· · ·
...
· · · fm(αn · γm−1)

⎞

.

⎟
⎟
⎟
⎠

Prove that the above code has rate k/(nm) and distance at least n − ⌊︁ k−1

m

⌋︁.

Exercise 5.21. In this problem we will see that Reed-Solomon codes, derivative codes (Ex­
ercise 5.19) and folded Reed-Solomon codes (Exercise 5.20) are all essentially special cases 
of a large family of codes that are based on polynomials. We begin with the definition of these 
codes.

Let m ≥ 1 be an integer parameter and define m < k ≤ n. Further, let E1(X), . . . , En(X)
be n polynomials over Fq, each of degree m. Further, these polynomials pair-wise do not have 
any non-trivial factors (i.e. gcd(Ei(X), Ej(X)) has degree 0 for every i ̸= j ∈ [n].) Consider 
any  message  m ∈ Fk
q   and  let  fm(X)  be  the  message  polynomial  as  defined  for  the  Reed-
Solomon code.  Then the codeword for m is given by:

(fm(X) mod E1(X), fm(X) mod E2(X), . . . , fm(X) mod En(X)) .

In the above we think of fm(X) mod Ei(X) as an element of Fqm.  In particular, given given 
a polynomial of degree at most m − 1, we will consider any bijection between the qm such 
polynomials and Fqm.  We will first see that this code is MDS and then we will see why it 
contains Reed-Solomon and related codes as special cases.

1. Prove that the above code has rate k/(nm) and distance at least n − ⌊︁ k−1

m

⌋︁.

2. Let α1, . . . , αn ∈ Fq be distinct elements.  Define Ei(X) = X − αi.  Prove that for this 

special case the above code (with m = 1) is the Reed-Solomon code.

3. Let α1, . . . , αn ∈ Fq be distinct elements.  Define Ei(X) = (X − αi)m.  Prove that for 
this special case the above code is the derivative code (with an appropriate mapping 
from polynomials of degree at most m − 1 and Fm
q , where the mapping could be different 
for each i ∈ [n] and can depend on Ei(X)).

4. Let α1, . . . , αn ∈ Fq be distinct elements and γ ∈ F∗

q such that (5.4) is satisfied.  Define 
Ei(X) = ∏︁m−1
j=0 (X − αi · γj). Prove that for this special case the above code is the folded 
Reed-Solomon code (with an appropriate mapping from polynomials of degree at most 
m − 1 and Fm
q , where the mapping could be different for each i ∈ [n] and can depend 
on Ei(X)).

108



<!-- pdf-page: 121 -->
Exercise  5.22.  In  this  exercise  we  will  develop  a  sufficient  condition  to  determine  the 
irreducibility of certain polynomials called the Eisenstein’s criterion.

Let F (X, Y ) be a polynomial of Fq.  Think of this polynomial as over X with coefficients 
as polynomials in Y  over Fq.  Technically, we think of the coefficients as coming from the 
ring of polynomials in Y  over Fq.  We will denote the ring of polynomials in Y  over Fq as 
Fq(Y ) and we will denote the polynomials in X with coefficients from Fq(Y ) as Fq(Y )[X].

In particular, let

F (X, Y ) = X t + ft−1(Y ) · X t−1 + · · · + f0(Y ),

where each fi(Y ) ∈ Fq(Y ).  Let P (Y ) be a prime for Fq(Y ) (i.e.  P (Y ) has degree at least 
one and if P (Y ) divides A(Y ) · B(Y ) then P (Y ) divides at least one of A(Y ) or B(Y )).  If 
the following conditions hold:

(i) P (Y ) divides fi(Y ) for every 0 ≤ i < t; but

(ii) P 2(Y ) does not divide f0(Y )

then  F (X, Y )  does  not  have  any  non-trivial  factors  over  Fq(Y )[X]  (i.e.  all  factors  have 
either degree t or 0 in X).

In the rest of the problem, we will prove this result in a sequence of steps:

1. For the sake of contradiction assume that F (X, Y ) = G(X, Y ) · H(X, Y ) where

G(X, Y ) =

t1∑︂

i=0

gi(Y ) · X I and H(X, Y ) =

t2∑︂

i=0

hi(Y ) · X i,

where 0 < t1, t2 < t.  Then prove that P (Y ) does not divide both of g0(Y ) and h0(Y ).
For the rest of the problem WLOG assume that P (Y ) divides g0(Y ) (and hence does 
not divide h0(Y )).

2. Prove that there exists an i∗ such that P (Y ) divide gi(Y ) for every 0 ≤ i < i∗ but P (Y )

does not divide gi∗(Y ) (define gt(Y ) = 1).

3. Prove  that  P (Y )  does  not  divide  fi(Y ).  Conclude  that  F (X, Y )  does  not  have  any 

non-trivial factors, as desired.

Exercise 5.23. We have mentioned objects called algebraic-geometric (AG) codes, that gen­
eralize Reed-Solomon codes and have some amazing properties: see for example, Section 4.6. 
The  objective  of  this  exercise  is  to  construct  one  such  AG  code,  and  establish  its  rate  vs 
distance trade-off.

Let p be a prime and q = p2.  Consider the equation

Y p + Y = X p+1

(5.5)

over Fq.

109



<!-- pdf-page: 122 -->
1. Prove that there are exactly p3 solutions in Fq × Fq to (5.5).  That is, if S ⊆ F2

q is 

defined as

then |S| = p3.

S = {︁(α, β) ∈ F2

q | βp + β = αp+1}︁

2. Prove that the polynomial F (X, Y ) = Y p + Y − X p+1 is irreducible over Fq.

Hint:  Exercise 5.22 could be useful.

3. Let n = p3.  Consider the evaluation map ev : Fq[X, Y ] → Fn

q  defined by

ev(f ) = (f (α, β) : (α, β) ∈ S) .

Prove that if f ̸= 0 and is not divisible by Y p + Y − X p+1, then ev(f ) has Hamming 
weight at least n − deg(f )(p + 1), where deg(f ) denotes the total degree of f .
Hint:    You are allowed to make use of Bézout’s theorem, which states that if f, g ∈ Fq[X, Y ] are 
nonzero polynomials with no common factors, then they have at most deg(f )deg(g) common zeroes.

4. For an integer parameter ℓ ≥ 1, consider the set F ℓ of bivariate polynomials

F ℓ = {f ∈ Fq[X, Y ] | deg(f ) ≤ ℓ, degX(f ) ≤ p}

where degX(f ) denotes the degree of f  in X.
Prove that F ℓ is an Fq-linear space of dimension (ℓ + 1)(p + 1) − p(p+1)

2

.

5. Consider the code C ⊆ Fn

q  for n = p3 defined by

C = {ev(f ) | f ∈ F ℓ} .

Prove that C is a linear code with minimum distance at least n − ℓ(p + 1).

6. Deduce a construction of an [n, k]q code with distance d ≥ n − k + 1 − p(p − 1)/2.

(Note that Reed-Solomon codes have d = n − k + 1,  whereas these codes are off by 
p(p−1)/2 from the Singleton bound. However they are much longer than Reed-Solomon 
codes, with a block length of n = q3/2, and the deficiency from the Singleton bound is 
only o(n).)

Exercise 5.24. Since Reed-Solomon codes are linear codes, by Proposition 2.3.5, one can 
do error detection for Reed-Solomon codes in quadratic time.  In this problem, we will see 
that one can design even more efficient error detection algorithm for Reed-Solomon codes. In 
particular, we will consider data streaming algorithms (see Section ?? for more motivation 
on this class of algorithms).  A data stream algorithm makes a sequential pass on the input 
taking only poly-logarithmic time on each location in the input and uses only poly-logarithmic 
space.  In this problem we show that there exists a randomized data stream algorithm to solve 
the error detection problem for Reed-Solomon codes.  We do so by first defining a problem 
unrelated to Reed-Solomon codes that can be solved by a data stream algorithm. (The solution 

110



<!-- pdf-page: 123 -->
will actually use Reed-Solomon codes, but this use is accidental and unrelated to the goal of 
the second part.)  In the second part of the problem we will solve the error-detection problem 
for Reed-Solomon codes in the data-streaming setting using the solution to the first part as a 
black-box.

1. For a sequence σ = ((i1, αi), . . . , (in, αn)) ∈ ([m] × Fq)n define y = y(σ) ∈ Fm

q  to be 
the vector given by yℓ = ∑︁
{j∈[n]|ij =ℓ} αj for ℓ ∈ [m].  Give a randomized data stream 
algorithm that given as input a sequence σ = ((i1, α1), . . . , (in, αn)) ∈ ([m] × Fq)n that 
outputs 0 if and only if y = y(σ) = 0, with probability at least 2/3.  Your algorithm 
should take at most polylog(q(m + n)) time per position of input σ and use at most 
O(log q(m + n)) space.  For simplicity, you can assume that given an integer t ≥ 1 and 
prime power q, the algorithm has oracle access to an irreducible polynomial of degree t
over Fq.
Hint:  Instead of computing and storing the vector y, you should compute E(y)j, i.e., the jth coordinate 
of an appropriate error-correcting encoding function E : Fℓ
q , where j ∈ [L] is chosen uniformly 
at random.  To ensure this coordinate of the encoding function can be computed quickly, you may use 
a Reed-Solomon code.

q → FL

2. Given [q, k]q Reed-Solomon code C (i.e.  with the evaluation points being Fq), present 
a data stream algorithm for error detection of C with O(log q) space and polylogq time 
per position of the received word.  The algorithm should work correctly with probability 
at least 2/3. You should assume that the data stream algorithm has access to the values 
of k and q (and knows that C has Fq as its evaluation points).
Hint:  Part 1 and Exercise 5.8 should be helpful.

5.5  Bibliographic Notes

Reed-Solomon codes were invented by Reed and Solomon [61] in the form described in Defini­
tion 5.2.1, i.e., as evaluations of polynomials. Later, Gorenstein and Zierler [29] showed that 
for specific choices of α, the resulting Reed-Solomon code is actually a “BCH code”.  (This 
is the connection explored in Exercise 5.9.)  BCH codes were themselves discovered slightly 
earlier in the independent works of Bose and Ray-Chaudhuri [9] and Hocquenghem [36]. We 
note that the original definitions of BCH codes used the coefficients of polynomials to repre­
sent codewords (analogous to the alternate definition of Reed-Solomon codes in Exercise 5.9). 
The equivalent definition of these codes used in Exercise 5.11 as subcodes of Reed-Solomon 
codes, again uses the above mentioned connection from [29].

The Chinese Remainder Codes in Exercise 5.17 are due to Mandelbaum [49]. The Deriva­
tive Codes in Exercise 5.19 are due to Rosenbloom and Tsfasman [63].  They form an im­
portant subclass of Multiplicity Codes invented by Kopparty, Saraf and Yekhanin [44].  The 
Folded Reed-Solomon codes in Exercise 5.20 were introduced by Krachovsky [45] and high­
lighted by the work of Guruswami and Rudra [32].  Exercise 5.21 is based on the work of 
Guruswami and Kopparty [30].

111



<!-- pdf-page: 124 -->
112



<!-- pdf-page: 125 -->
Part III

The Codes

113



<!-- pdf-page: 126 -->


<!-- pdf-page: 127 -->
Chapter 6

When Polynomials Save the Day: 
Polynomial Based Codes

As we saw in Chapter 5, the Reed-Solomon codes give a remarkable family of codes with 
optimal  dimension  vs.  distance  tradeoff.  They  even  match  the  Singleton  bound  (recall 
Theorem 4.3.1), get k = n − d + 1 for a code of block length n, distance d and dimension 
k.  However they achieve this remarkable  performance only over large alphabets,  namely 
when the alphabet size q ≥ n.  In fact, so far in this book, we have not seen any explicit 
asymptotically  good  code  other  than  a  Reed-Solomon  code.  This  naturally  leads  to  the 
following question (which is a weaker form for Question ??):

Question 6.0.1. Do there exist explicit asymptotically good codes for small alphabets q ≪ n?

In this chapter we study an extension of Reed-Solomon codes, called the (generalized) 
Reed-Muller codes, that lead to codes over smaller alphabets while losing in the dimension-
distance tradeoff (but under certain settings do answer Question 6.0.1 in the affirmative).

The main idea is to extend the notion of functions we work with, to multivariate func­
tions.  (See Exercise 5.1 for equivalence between certain Reed-Solomon codes and univariate 
functions.)  Just working with bivariate functions (functions on two variables), allows us to 
get codes of block  length  n = q2,  and more variables can increase  the length  further for 
the  same  alphabet  size.  We  look  at  functions  of  total  degree at  most  r.  Analysis  of  the 
dimension of the code reduces to simple combinatorics. Analysis of the distance follows from 
“polynomial-distance” lemmas (see Lemmas 6.2.2, 6.3.1 and 6.4.1), whose use is ubiquitous 
in algebra, coding theory and computer science, and we describe these in the sections below. 
We start with the generic construction.

6.1  The generic construction

Recall that for a monomial Xd = X d1
next extend this to the definition of the degree of a polynomial:

2 · · · X dm

1 · X d2

m  its total degree is d1 + d2 + · · · + dm.  We 

115



<!-- pdf-page: 128 -->
Definition 6.1.1. The total degree of a polynomial P (X) = ∑︁
d cdXd over Fq (i.e.  every 
cd ∈ Fq) is the maximum over d such that cd ̸= 0, of the total degree of Xd.  We denote the 
total degree of P  by deg(P ).

For example, the degree of the polynomial 3X 3Y 4 + X 5 + Y 6 is 7.
In turns out that when talking about Reed-Muller codes, it is convenient to switch back 
and forth between multivariate functions and multivariate polynomials.  We can extend the 
q → Fq let deg(f ) be the minimal degree 
notion above to functions from Fm
of a polynomial P ∈ Fq[X1, . . . , Xm] (where Fq[X1, . . . , Xm] denotes the set of all m-variate 
polynomials with coefficients from Fq) such that f (α) = P (α) for every α ∈ Fm
q .  Note that 
since (by Exercise 2.4) for every a ∈ Fq we have aq − a = 0, it follows that a minimal degree 
polynomial does not contain monomials with degree more than q − 1 any single variable.  In 
what follows,

q → Fq. For f : Fm

(p) to denote the degree of polynomial p in variable Xi and 
(f ) to denote the degree of (the minimal polynomial corresponding to) a function f  in 

Definition 6.1.2. We use degXi
degXi
variable Xi.

For example degX(3X 3Y 4 + X 5 + Y 6) = 5 and degY (3X 3Y 4 + X 5 + Y 6) = 6. Further, in 

this notation we have for every function f : Fm

q → Fq, degXi

(f ) ≤ q − 1 for every i ∈ [m].

Reed-Muller codes are given by three parameters:  a prime power q and positive integers 
m and r, and consist of the evaluations of m-variate polynomials of degree at most r over 
all of the domain Fm
q .

Definition 6.1.3  (Reed-Muller Codes). The Reed-Muller code with parameters q, m, r, de­
noted RM(q, m, r), is the set of evaluations of all m-variate polynomials in Fq[X1, . . . , Xm]
of total degree at most r and individual degree at most q − 1 over all points in Fm
q .  Formally

RM(q, m, r) def= {︁f : Fm

q → Fq| deg(f ) ≤ r}︁ .

For example consider the case of m = q = 2 and r = 1. Note that all bivariate polynomials 
over F2 of degree at most 1 are 0, 1, X1, X2, 1+X1, 1+X2, X1+X2 and 1+X1+X2. Thus, we 
have that (where the evaluation points for (X1, X2) are ordered as (0, 0), (0, 1), (1, 0), (1, 1)):

RM(2, 2, 1) = {(0, 0, 0, 0), (1, 1, 1, 1), (0, 0, 1, 1), (0, 1, 0, 1), (1, 1, 0, 0), (1, 0, 1, 0), (0, 1, 1, 0), (1, 0, 0, 1)} .

Also note that RM(q, m, 1) is almost the Hadamard code (see Exercise 5.9).

The Reed-Muller code with parameters (q, m, r) clearly has alphabet Fq and block length 
n = qm.  Also it can be verified that RM(q, m, r) is a linear code (see Exercise 6.1.)  This 
leads to the following question, which will be the primary focus of this chapter:

Question 6.1.4. What are the dimension and distance of an RM(q, m, r) code?

The dimension of the code is the number of m-variate monomials of degree at most r, 
with the condition that degree in each variable is at most q − 1.  No simple closed form 
expression for this that works for all choices of q, m and r is known, so we will describe the 
effects only in some cases.  The distance analysis of these codes takes a little bit more effort 
and we will start with two simple settings before describing the general result.

116



<!-- pdf-page: 129 -->
6.2  The low degree case

We start by considering RM(q, m, r) when r < q, i.e., the degree is smaller than the field 
size.  We refer to this setting as the “low-degree” setting.

Dimension.  The dimension of RM(q, m, r) in the low-degree case turns out to have a nice 
closed form, since we do not have to worry about the constraint that each variable has degree 
at most q − 1:  this is already imposed by restricting the total degree to at most r ≤ q − 1. 
This leads to a nice expression for the dimension:
Proposition 6.2.1. The dimension of the Reed Muller code RM(q, m, r) equals (︁m+r
r < q.

)︁ when 

r

Proof. 

The dimension equals the size of the set

{︄

D =

(d1, . . . , dm) ∈ Zm|di ≥ 0 for all i ∈ [m],

}︄

di ≤ r

,

m
∑︂

i=1

(6.1)

since for every (d1, . . . , dm) ∈ D, the monomial X d1
m  is a monomial of degree at most 
r and these are all such monomials.  The closed form expression for the dimension follows 
by a simple counting argument.  (See Exercise 6.2).

1 · · · X dm

Distance.  Next we turn to the analysis of the distance of the code.  To understand the 
distance we will first state and prove a simple fact about the number of zeroes a multivariate 
polynomial can have.  (We will have three versions of this in this chapter - with the third 
subsuming  the  first  (Lemma  6.2.2)  and  second  (Lemma  6.3.1),  but  the  first  two  will  be 
slightly simpler to state and remember.)

Lemma 6.2.2  (Polynomial Distance Lemma (low-degree case)). Let f ∈ Fq[X1, . . . , Xm] be 
a non-zero polynomial with deg(f ) ≤ r.  Then the fraction of zeroes of f  is at most  r

q , i.e.,

|{a ∈ Fm

q |f (a) = 0}|
qm

≤

r
q

.

We make couple of remarks.  First note that the above lemma for m = 1 is the degree 
mantra (Proposition 5.1.5).  We note that for every m ≥ 1 the above lemma is tight (see 
Exercise  6.3).  However,  there  exists  polynomials  for  which  the  lemma  is  not  tight  (see 
Exercise 6.4).

Proof of Lemma 6.2.2. 
probability that f (a) = 0 is at most  deg(f )
random from Fm

q

q .  We claim that this holds by induction on m.

Note that the lemma statement is equivalent to saying that the 
 when a = (a1, . . . , am) is chosen uniformly at 

We will prove the lemma by induction on m ≥ 1.  Note that the base case follows from 
the degree mantra (Proposition 5.1.5). Now consider the case of m > 1 (and we assume that 

117

 


<!-- pdf-page: 130 -->
the lemma is true for m − 1). To apply inductive hypothesis we first write f  as a polynomial 
in Xm with coefficients that are themselves polynomials in X1, . . . , Xm−1.  So let

f = f0X 0

m + f1X 1

m + . . . ftX t
m,

where each fi(X1, . . . , Xm−1) is a polynomial from Fq[X1, . . . , Xm−1] and deg(fi) ≤ r − i. 
Furthermore let t be the largest index such that ft is not zero.  Now we consider picking 
a ∈ Fm
, and then 
we pick am uniformly from Fq.  Let

q  in two steps: We first pick (a1, . . . , am−1) uniformly at random from Fm−1

q

f (a1,...,am−1)(Xm) = f0(a1, . . . , am−1)X 0

m + · · · + . . . ft(a1, . . . , am−1)X t
m.

We consider two possible events:

E 1 = {(a1, . . . , am)|ft(a1, . . . , am−1) = 0}

and

E 2 = {((a1, . . . , am)|ft(a1, . . . , am−1) ̸= 0 and f (a1,...,am−1)(am) = 0}.

By the inductive hypothesis, we have that

Pr [E 1] ≤

r − t
q

,

(6.2)

since deg(ft) ≤ r − t and ft ̸= 0.

For every (a1, . . . , am−1) ∈ Fm−1

 such that ft(a1, . . . , am−1) ̸= 0 we also have that the 
univariate polynomial f (a1,...,am−1)(Xm) is non-zero and of degree at most t, and so by the 
degree  mantra  it  has  at  most  t  roots.  It  follows  that  for  every  such  (a1, . . . , am−1)  the 
probability, over am, that f (a1,...,am−1)(am) = 0 is at most  t
q .  In turn, it now immediately 
follows that

q

Pr [E 2] ≤

.

(6.3)

t
q

Finally, we claim that if neither E 1 nor E 2 occur, then f (a) ̸= 0.  This is immediate from 
the  definitions  of  E 1  and  E 2,  since  if  f (a1, . . . , am) = 0,  it  must  either  be  the  case  that 
ft(a1, . . . , am−1) = 0  (corresponding  to  E 1)  or  it  must  be  that  ft(a1, . . . , am−1) ̸= 0  and 
f (a1,...,am−1)(am) = 0 (covered by E 2). Note that this implies that Pra[f (a) = 0] ≤ Pr [E 1 ∪ E 2]. 
The lemma now follows from the fact that

[f (a) = 0] ≤ Pr [E 1 ∪ E 2] ≤ Pr [E 1] + Pr [E 2] ≤

Pr
a

r
q

,

where the second inequality follows from the union bound (Proposition 3.1.5) and the final 
inequality follows from (6.2) and (6.3).

118

 


<!-- pdf-page: 131 -->
Comparison with other codes

The lemmas above, while quite precise may not be fully transparent in explaining the asymp­
totics of the performance of the Reed-Muller codes, or contrast them with other codes we 
have seen.  We mention a few basic facts here to get a clearer comparison.

If we set m = 1 and r = k − 1, then we get the Reed-Solomon codes evaluated on all of 
Fq (see Chapter 5).  If we set m = k − 1, r = 1 and q = 2, then we get family of extended 
Hadamard codes (extended by including all Hadamard codewords and their complements). 
For more on this, see Exercise 5.9.

Thus Reed-Muller codes generalize some previously known codes - some with large alpha­
bets and some with small alphabets.  Indeed if we wish the alphabet to be small compared 
to the block length, then we can pick m to be a constant.  For instance if we choose m = 2, 
we get codes of length n over an alphabets of size 
n, while for a given choice of relative 
distance δ, the code has rate at least  (1−δ)2
.  In general for larger values of m, the code has 
alphabet size n1/m and rate at least  (1−δ)m
.  (See Exercise 6.5.)  Thus for small values of m
and fixed positive distance δ < 1 there is a rate R > 0 such that, by choosing q appropriately 
large, one get codes on infinitely long block length n and alphabet n1/m with rate R and 
distance δ, which answers Question 6.0.1 in the affirmative.

√

m!

2

This is one of the simplest such families of codes with this feature.  We will do better in 
later in the book (e.g.  Chapter 7), and indeed get alphabet size q independent of n with 
R > 0 and δ > 0.  But for now this is best we have.

6.3  The case of the binary field

Next we turn to a different extreme of parameter choices for the Reed-Muller codes.  Here 
we fix the alphabet size q = 2 and see what varying m and r gets us.

Since we will prove a stronger statement later in Lemma 6.4.1, we only state the distance 

of the code RM(2, m, r) below, leaving the proof to Exercise 6.6.

Lemma 6.3.1   (Polynomial distance (binary case)). Let f  be a non-zero polynomial from 
(f ) ≤ 1 for every i ∈ [m].  Then |{a ∈ Fm
F2[X1. . . . , Xm] with degXi
2 |f (a) ̸= 0}| ≥ 2m−deg(f ).

Further, it can be established that the bound in Lemma 6.3.1 is tight (see Exercise 6.7).
The  dimension  of  the  code  is  relatively straightforward  to  analyze.  The  dimension  is 
again  given  by  the  number  of  monomials  of  degree  at  most  r.  Since  the  degree  in  each 
variable is either zero or one, this just equals the number of subsets of [m] of size at most r. 
Thus we have:

Proposition 6.3.2. For any r ≤ m, the dimension of the Reed-Muller code RM(2, m, r) is 
exactly ∑︁r

)︁.

(︁m
i

i=0

Lemma 6.3.1 and Proposition 6.3.2 imply the following result:

119



<!-- pdf-page: 132 -->
Theorem  6.3.3. For  every  r ≤ m,  the  Reed-Muller  code  RM(2, m, r)  is  a  code  of  block 
length 2m, dimension ∑︁r

)︁ and distance 2m−r.

(︁m
i

i=0

Again, to get a sense of the asymptotics of this code, we can fix τ > 0 and set r = τ · m
and let m → ∞.  In this case we get a code of block length n (for infinitely many n) with 
rate roughly nH(τ )−1 and distance n−τ  (see Exercise 6.8).  So both the rate and the distance 
tend to zero at a rate that is a small polynomial in the block length but the code has a 
constant sized alphabet.  (Note that this implies that we have made some progress towards 
answering Question ??.)

6.4  The general case

We now turn to the general case, where q is general and r is allowed to be larger than q − 1. 
We will try to analyze the dimension and distance of this code.  The distance turns out to 
still have a clean expression, so we will do that first.  The dimension does not have a simple 
expression describing it exactly, so we will give a few lower bounds that may be generally 
useful (and are often asymptotically tight).

6.4.1  The general case:  Distance

Lemma 6.4.1   (Polynomial distance (general case)). Let f  be a non-zero polynomial from 
Fq[X1. . . . , Xm] with degXi
(f ) ≤ q − 1 for every i ∈ [m] and deg(f ) ≤ r.  Furthermore, let 
s, t be the unique non-negative integers such that t ≤ q − 2 and

s(q − 1) + t = r.

Then

|{a ∈ Fm

q |f (a) ̸= 0}| ≥ (q − t) · qm−s−1 ≥ qm− r

q−1 .

Hence, RM(q, m, r) has distance at least qm− r

q−1 .

Before proving the lemma we make a few observations:  The above lemma clearly gen­
eralizes both Lemma 6.2.2 (which corresponds to the case s = 0) and Lemma 6.3.1 (where 
q = 2, s = r − 1 and t = 1).  In the general case the second lower bound is a little simpler to 
apply and it shows that the probability that a polynomial is non-zero at a uniformly chosen 
point in Fm
q  is at least q−r/(q−1).  Finally, we note that Lemma 6.4.1 is tight for all settings 
of parameters (see Exercise 6.9).

Proof of Lemma 6.4.1. 
The proof is similar to the proof of Lemma 6.2.2 except we take 
advantage of the fact that the degree in a single variable is at most q − 1.  We also need to 
prove some simple inequalities.

As in the proof of Lemma 6.2.2 we prove that for a random choice of a = (a1, . . . , am) ∈

Fm

q , the probability that f (a) ̸= 0 is at least

(q − t) · q−(s+1).

120

(6.4)



<!-- pdf-page: 133 -->
Note  that  in  contrast  to  the  proof  of  Lemma  6.2.2  we  focus  on  the  good  events  —  the 
polynomial being non-zero — rather than on the bad events.

We prove the lemma by induction on m.  In the case of m = 1 we have by the degree 
q .  If r < q − 1

mantra (Proposition 5.1.5) that the probability that f (a1) ̸= 0 is at least  q−r
we have s = 0 and t = r and so the expression in (6.4) satisfies

(q − t) · q−1 =

q − r
q

≤ Pr[f (a1) ̸= 0].

If r = q − 1 we have s = 1 and t = 0, but then again we have that (6.4) equals

q · q−2 =

q − (q − 1)
q

≤ Pr[f (a1) ̸= 0],

where the inequality follows from the degree mantra.

Now we turn to the inductive step.  Assume the hypothesis is true for (m − 1)-variate 
m where fi ∈ Fq[X1, . . . , Xm−1] with fb ̸= 0. Note 0 ≤ b ≤

polynomials and let f = ∑︁b
q − 1 and deg(fb) ≤ r − b.  Let E be the event of interest to us, i.e.,

i=0 fiX i

E = {(a1, . . . , am)|f (a1, . . . , am) ̸= 0}.

Let

E 1 = {(a1, . . . , am−1)|fb(a1, . . . , am−1) ̸= 0}.

We first bound Pr [E|E 1].  Fix a1, . . . , am−1 such that fb(a1, . . . , am−1) ̸= 0 and let

P (Z) =

b
∑︂

i=0

fi(a1, . . . , am−1)Z i.

Note P  is a non-zero polynomial of degree b and we have

Pr[f (a1, . . . , am) = 0|a1, . . . , am−1] = Pr
am

[P (am) ̸= 0].

Since by the degree mantra, a univariate polynomial of degree b has at most b roots, we have

We conclude

[P (am) ̸= 0] ≥

Pr
am

q − b
q

.

Pr [E|E 1] ≥ 1 −

b
q

.

Next we will bound Pr [E 1].  This will allow us to lower bound the probability of E since

Pr [E] ≥ Pr [E and E 1] = Pr [E 1] · Pr [E|E 1] .

121



<!-- pdf-page: 134 -->
Recall that deg(fb) ≤ r − b.  Write r − b = s′(q − 1) + t′ where s′, t′ ≥ 0 and t′ ≤ q − 2.  By 
induction we have

Pr [E 1] = Pr[fb(a1, . . . , am−1) ̸= 0] ≥ (q − t′) · q−(s′+1).

Putting the two bounds together, we get

Pr [E] ≥ Pr [E|E 1] · Pr [E 1] ≥

q − b
q

· (q − t′) · q−(s′+1).

We are now left with a calculation to verify that the bound above is indeed lower bounded 
by (q − t) · q−(s+1) and we do so in Claim 6.4.2 using the facts that t, t′ ≤ q − 2, b ≤ q − 1, 
r = s(q − 1) + t, and r − b = s′(q − 1) + t′.  In the claim further below (Claim 6.4.3), we also 
prove (q − t) · q−(s+1) ≥ q−r/(q−1) and this concludes the proof of the lemma.

Claim 6.4.2. If q, r, s, t, s′, t′, b are non-negative integers such that r = s(q − 1) + t, r − b =
s′(q − 1) + t′, t, t′ ≤ q − 2 and b ≤ q − 1 then we have

q − b
q

· (q − t′) · q−(s′+1) ≥ (q − t) · q−(s+1).

The proof breaks up in to two cases depending on s − s′. Note that an equivalent 
Proof. 
definition of s and s′ are that these are the quotients when we divide r and r − b respectively 
by q − 1.  Since 0 ≤ b ≤ q − 1, it follows that either s′ = s or s′ = s − 1.  We consider the 
two cases separately.

If s = s′ we have t = t′ + b and then it suffices to show that
q − b
q

· (q − t′) ≥ q − (t′ + b).

In turn this is equivalent to showing

(q − b)(q − t′) ≥ q(q − (t′ + b)).

But this is immediate since the expression on the left is

(q − b)(q − t′) = q2 − (b + t′)q + bt′ = q(q − (b + t′)) + bt′ ≥ q(q − (b + t′)),

where the final inequality uses bt′ ≥ 0.

If s = s′ + 1 we have a bit more work.  Here we have t + q − 1 = t′ + b and it suffices to 

show that

q − b
q

· (q − t′) · q ≥ (q − t) = (2q − (t′ + b + 1)).

Write q − b = α and q − t′ = β.  The expression on the left above simplifies to αβ and on 
the right to α + β − 1.  Since b, t′ ≤ q − 1, we also have α, β ≥ 1.  So it suffices to show that 
αβ ≥ α + β − 1.  This is true since αβ = α + α(β − 1) and we have α(β − 1) ≥ β − 1 since 
α ≥ 1 and β − 1 ≥ 0.

We thus conclude that the inequality holds for both s = s′ and s = s′ + 1 and this yields 

the claim.

122

 
 


<!-- pdf-page: 135 -->
Claim 6.4.3. Let q, r, s, t be non-negative real numbers such that q ≥ 2, r = s(q − 1) + t and 
t ≤ q − 2.  Then

(q − t) · q−(s+1) ≥ q−r/(q−1).

We remark that while the inequality is quite useful, the proof below is not particularly 
insightful.  We include it for completeness, but we recommend that the reader skip it unless 
necessary.

Proof of Claim 6.4.3.  We have four parameters in the inequality above. We will simplify 
it in steps removing parameters one at a time.  First we get rid of r by substituting r =
s(q − 1) + t.  So it suffices to prove:

(q − t) · q−(s+1) ≥ q−(s(q−1)+t)/(q−1) = q−s · q−t/(q−1).

We can get rid of q−s from both sides (since the remaining terms are non-negative) and so 
it suffices to prove:

q − t
q

≥ q−t/(q−1).

Let  fq(t) = t
q + q−t/(q−1) − 1.  The  inequality  above  is  equivalent  to  proving  fq(t) ≤ 0
for  0 ≤ t ≤ q − 2.  We  use  some  basic  calculus  to  prove  the  above.  Note  that  the  first 
and  second  derivatives  of  fq  with  respect  to  t  are  given  by  f ′
q−1q−t/(q−1)  and 
q (t) = (ln(q)/(q − 1))2 q−t/(q−1). In particular the second derivative is always positive which 
f ′′
means fq(t) is maximized at one of the two end points of the interval t ∈ [0, q − 2].  We have 
fq(0) = 0 ≤ 0 as desired and so it suffices to prove that

q(t) = 1

q − ln q

fq(q − 2) = q−(q−2)/(q−1) −

2
q

≤ 0.

Multiplying the expression above by q we have that it suffices to show q1/(q−1) ≤ 2 which in 
turn is equivalent to proving q ≤ 2q−1 for every q ≥ 2.  The final inequality follows easily 
from Bernoulli’s inequality (Lemma A.1.4) 1 + kx ≤ (1 + x)k which holds for every x ≥ −1
and k ≥ 1. In our case we substitute x = 1 and k = q −1 to conclude q ≤ 2q−1 as desired.

6.4.2  The general case:  Dimension

For integers q, m, r let

{︄

Sq,m,r =

d = (d1, . . . , dm) ∈ Zm|0 ≤ di ≤ q − 1 for all i ∈ [m] and ,

}︄

di ≤ r

(6.5)

m
∑︂

i=1

and let

Kq,m,r = |Sq,m,r|.

We start with the following, almost tautological, proposition.

123

 


<!-- pdf-page: 136 -->
Proposition 6.4.4. For every prime power q and integers m ≥ 1 and r ≥ 0, the dimension 
of the code RM(q, m, r) is Kq,m,r.

Follows  from  the  fact  that  for  every  d = (d1, . . . , dm) ∈ Sq,m,r  the  associated 
Proof. 
monomial Xd = X d1
m  is a monomial of degree at most r and individual degree at 
most q − 1.  Thus these monomials (i.e., their evaluations) form a basis for the Reed-Muller 
code RM(q, m, r).  (See Exercise 6.10.)

1 · · · X dm

The definition of Kq,m,r does not give a good hint about its growth so below we give a 
few bounds on Kq,m,r that help estimate its growth.  Specifically the proposition below gives 
a  lower  bound  K −
q,m,r  on  Kq,m,r  that  are  (1)  given  by  simple 
expressions and (2) within polynomial factors of each other for every setting of q, m, and r.

q,m,r  and  an  upper  bound  K +

Proposition 6.4.5. For integers q ≥ 2, m ≥ 1 and r ≥ 0, let
)︃}︃

{︃

K +

q,m,r

≜ min

qm,

(︃m + r
r

and let

{︄

K −

q,m,r

≜

{︂

max
max {︁(︁m

)︁, 1

qm/2, qm − K +

(︁⌊︁ 2r+m

q,m,(q−1)m−r
⌋︁)︁m}︁

}︂

 if  r ≥ (q − 1)m/2
 if  r < (q − 1)m/2

m
Then there are universal constants c1, c2 (c1 < 3.1 and c2 < 8.2 suffice) such that

2

r

K −

q,m,r ≤ Kq,m,r ≤ K +

q,m,r ≤ c1 · (K −

q,m,r)c2

.

Proof.  We tackle the inequalities in order of growing complexity of the proof.  In our 
bounds we use the fact that Kq,m,r is monotone non-decreasing in q as well as r (when other 
parameters are fixed)– see Exercise 6.11.

First we prove Kq,m,r ≤ K +

q,m,r.  On the one hand we have

Kq,m,r ≤ Kq,m,(q−1)m = qm,

which follows by ignoring the total degree restriction and on the other hand we have

Kq,m,r ≤ Kr,m,r =

(︃m + r
r

)︃
,

whereas here we ignored the individual degree restriction.

Next we show K −

q,m,r ≤ Kq,m,r. First we consider the case r ≥ (q − 1)m/2. Here we argue 
via symmetry.  Consider a map that maps vectors d = (d1, . . . , dm) ∈ Zm with 0 ≤ di < q to 
d = (q −1−d1, . . . , q −1−dm). The map d → d is a one-to-one map which maps vectors with 
∑︁
i di < (q − 1)m − r.  In other words either d ∈ {0, . . . , q − 1}m

i di > r to vectors with ∑︁

is in Sq,m,r or d ∈ Sq,m,(q−1)m−r, thus establishing

Kq,m,r = qm − Kq,m,(q−1)m−r.

124

 


<!-- pdf-page: 137 -->
Since r ≥ (q − 1)m/2 we have (q − 1)m − r ≤ r and so

which in turn implies

Kq,m,r ≥ Kq,m,(q−1)m−r,

Kq,m,r ≥ qm/2.

This  establishes  Kq,m,r ≥ K −
(q − 1)m/2, first let q′ = ⌊︁ 2r+m

m

⌋︁.  We have

q,m,r  when  r ≥ (q − 1)m/2.  Next,  turning  to  the  case  r <

since r ≥ (q′ − 1)m/2, and this yields

Kq,m,r ≥ Kq′,m,r ≥ (q′)m/2

Finally we also have

Kq,m,r ≥ (q′)m/2 =

(︃⌊︃ 2r + m

⌋︃)︃m

m

1
2

.

Kq,m,r ≥ K2,m,r =

r
∑︂

i=0

)︃

(︃m
i

≥

)︃

(︃m
r

,

thus establishing Kq,m,r ≥ K −

q,m,r when r < (q − 1)m/2.

Finally we turn to the inequalities showing K +

q,m,r ≤ c1 · (K −

q,m,r)c2.  If r ≥ (q − 1)m/2 we 

have

qm
2

≤ K −

q,m,r ≤ K +

q,m,r ≤ qm

establishing K +

q,m,r ≤ 2K −

q,m,r.  Next we consider the case r < m/2.  In this case we have

K −

q,m,r ≥

)︃

(︃m
r

≥ (m/r)r ≥ 2r.

On the other hand we also have
(︃m + r
r

(︃ e(m + r)
r

≤

)︃

)︃r

≤

(︃ e · (3/2) · m
r

)︃r

=

(︃ 3e
2

)︃r

·

(︂ m
r

)︂r

.

From  2r ≤ K −
q,m,r ≤ (︁m+r
K +

q,m,r  we  get  (︁ 3e
)︁ we get

2

r

)︁r ≤ (K −

q,m,r)log2(3e/2).  Combining  with  (︁ m

r

)︁r ≤ K −

q,m,r  and 

K +

q,m,r ≤

)︃r

(︃ 3e
2

)︂r

·

(︂ m
r

≤ (K −

q,m,r)1+log2(3e/2)

.  Finally, we consider the case m/2 ≤ r < (q − 1)m/2.  In this range we have

⌋︃

⌊︃ 2r + m
m

= 1 +

⌋︃

⌊︃ 2r
m

≥ 1 +

r
m

=

m + r
m

.

125



<!-- pdf-page: 138 -->
Thus

K −

q,m,r ≥

1
2

(︃⌊︃ 2r + m

⌋︃)︃m

m

≥

(︃ m + r
m

1
2

)︃m

)︃m

≥

(︃3
2

1
2

On the other hand we have

K +

q,m,r ≤

)︃

(︃m + r
m

≤

(︃ e(m + r)
m

)︃m

= em ·

)︃m

(︃m + r
m

.

.

Again we have (︁ m+r
Thus  in  all  cases  we  have  K +
c1 = 2c2 < 8.2, as desired.

)︁m ≤ 2K −

m

q,m,r and em ≤ (2K −
q,m,r ≤ c1 · (K −

q,m,r)log2(3e/2) and so K +
q,m,r)c2  for  c2 = 1 + log2(3e/2) < 3.1  and 

q,m,r ≤ (2K −

q,m,r)1+log2(3e/2). 

We now give a few examples of codes that can be derived from the bounds above,  to 
illustrate the variety offered by Reed-Muller codes.  In each of the cases we set one or more 
of the parameters among alphabet size, rate, (relative) distance or absolute distance to a 
constant and explore the behavior in the other parameters.  In all cases we use Lemma 6.4.1 
to lower bound the distance and Proposition 6.4.5 to lower bound the dimension.

Example 6.4.6  (RM Codes of constant alphabet size and (relative) distance.). Fix q and 
r < q − 1 and consider m → ∞.  Then the Reed-Muller codes RM(q, m, r) are [N, K, D]q
codes with block length N = qm, distance D = δ · N  for δ = 1 − r/q, with dimension

K ≥

)︃

(︃m
r

≥

)︂r

(︂ m
r

=

(︃ logq N
r

)︃r

.

In other words Reed-Muller codes yield codes of constant alphabet size and relative distance 
with dimension growing as an arbitrary polynomial in the logarithm of the block length.

Example 6.4.7   (Binary RM Codes of rate close to 1 with constant (absolute) distance.). 
Fix q = 2 and d and let m → ∞. Then the Reed-Muller codes RM(2, m, m−d) are [N, K, D]2
codes with N = 2m, D = 2d and

K ≥ N −

)︃
(︃log2 N + d
d

≥ N − (log2 N )d.

(See Exercise 6.12 for bound on K.)  Note that the rate → 1 as N → ∞.

Example 6.4.8  (RM codes of constant rate and relative distance over polynomially small 
alphabets.). Given any ε > 0 and let m = ⌈︁ 1
⌉︁ and now consider q → ∞ with r = q/2.  Then 
the Reed-Muller codes RM(q, m, r) are [N, K, D]q codes with N = qm, D = N

ε

2  and

K ≥

)︃m

(︃ q + m
m

1
2

≥

1
2mm · N.

Expressed in terms of N  and ε, the codes have length N , dimension Ω (︁ε1/ε)︁ · N  and relative 
distance 1/2 over an alphabet of size N ε.

126

 


<!-- pdf-page: 139 -->
Another natural regime is to consider the case of constant rate 1/2: see Exercise 6.13 for 

more.

Finally  we  mention  a  range  of  parameters  that  has  been  very  useful  in  the  theory  of 
computer science.  Here the alphabet size is growing with N , but very slowly.  But the code 
has a fixed relative distance and dimension that is polynomially related to the block length.

Example 6.4.9   (RM Codes over polylogarithmic alphabets with polynomial dimension.). 
Given 0 < ε < 1, let q → ∞ and let r = q/2 and m = qε.  Then the Reed-Muller codes 
RM(q, m, r) are [N, K, D]q codes with N = qm, D = N

2  and

K ≥

)︃m

(︃ q + m
m

1
2

≥

1
2

(︁q1−ε)︁m =

1
2

· N 1−ε.

Expressed in terms of N  and ε, the codes have length N , dimension Ω(N 1−ε) and relative 
distance 1/2 over an alphabet of size (log N )1/ε.  (See Exercise 6.14 for claim on the bound 
on q.)

6.5  Exercises

Exercise 6.1. Prove that any RM(q, m, r) is a linear code.

Exercise 6.2. Prove that for D as defined in (6.1), we have

|D| =

(︃m + r
r

)︃

.

Exercise 6.3. Show that Lemma 6.2.2 is tight in the sense that for every prime power q
and integers m ≥ 1 and 1 ≤ r ≤ q − 1, there exists a polynomial with exactly r · qm−1 roots.

Exercise 6.4. Show that Lemma 6.2.2 is not tight for most polynomials.  In particular show 
that for every prime power q and integers m ≥ 1 and 1 ≤ r ≤ q − 1, a random polynomial 
in Fq[X1, . . . , Xm] of degree r has qm−1 expected number of roots.

Exercise 6.5. Show that the Reed-Muller codes of Section 6.2 give rise to codes of relative 
√
n
distance δ (for any 0 < δ < 1) and block length n such that they have alphabet size of  m
and rate at least  (1−δ)m

.

m!

Exercise 6.6. Prove Lemma 6.3.1.

Exercise 6.7. Prove that the lower bound in Lemma 6.3.1 is tight.

Exercise 6.8. Show that there exists a binary RM code with block length n, rate nH(τ )−1 and 
relative distance n−τ  for any 0 < τ < 1/2.

127



<!-- pdf-page: 140 -->
Exercise 6.9. Prove that the (first) lower bound in Lemma 6.4.1 is tight for all settings of 
the parameters.

Exercise 6.10. Prove that the evaluations of Xd for every d ∈ Sq,m,r (as in (6.5)) form a 
basis for RM(q, m, r).

Exercise 6.11. Prove that Kq,m,r is monotone non-decreasing in q as well as r (when other 
parameters are fixed).

Exercise 6.12. Prove the claimed bound on K in Example 6.4.7.

Exercise  6.13.  Determine  the  smallest  alphabet  q  for  which  a  RM  code  has  (absolute) 
distance that goes to infinity with the block length.  Determine an asymptotically tight bound 
on the distance of this code, as a function of the block length.

Exercise 6.14. Prove the claimed bound on q in Example 6.4.9.

Exercise 6.15. In this problem we will talk about the dual of Reed-Muller codes, which turn 
out to be Reed-Muller codes (with a different degree) themselves.  We do so in a sequence of 
sub-problems:

1. Show that for 1 ≤ j ≤ q − 1

if and only if j = q − 1.
Hint:  Use Exercise 2.3.

αj ̸= 0

∑︂

α∈Fq

2. Prove that for any m ≥ 1 and 1 ≤ j1, . . . , jm ≤ q − 1,

∑︂

m
∏︂

cj1
i = 0

(c1,...,cm)∈Fm
q

i=1

if and only if j1 = j2 = · · · = jm = q − 1.

3. Using the above or otherwise, show that for any 0 ≤ r < (q − 1) − s, we have

RM(q, m, r)⊥ = RM(q, m, m(q − 1) − r − 1).

128



<!-- pdf-page: 141 -->
6.6  Bibliographic Notes

The name Reed-Muller codes goes back to the first two papers introducing this code.  The 
binary version of these codes were invented by Muller in [55], and Reed gave a non-trivially 
fast decoder for these codes in [60]. The latter work is especially significant in the algorithmic 
context in that it is the first setting allowing a polynomial time decoder correcting errors 
(up to half the distance) where the brute force decoders (enumerating all possible codeword 
or all possible error locations) take super polynomial time in the length of the code.

The polynomial distance lemmas (Lemmas 6.3.1, 6.2.2, and 6.4.1) date back at least to 
Ore [56].  Versions of this lemma appear in Muller [55] and Schwartz [64], Zippel [76] and 
DeMillo and Lipton [16].

129



<!-- pdf-page: 142 -->
130



<!-- pdf-page: 143 -->
Chapter 7

From Large to Small Alphabets:  Code 
Concatenation

Recall  Question  ??:  Is  there  an  explicit  asymptotically  good  binary  code  (that  is,  rate 
R > 0 and relative distance δ > 0)?  Recall that the word “explicit code” was defined in 
Definition ?? and then strengthened in Definition ??.  Specifically Definition ?? deems a 
linear code to be explicit if we can construct its generator matrix in polynomial time.  And 
Definition ?? defines a linear code to be strongly explicit if we can compute every entry of 
the generator matrix in poly-logarithmic time.  In this chapter we will seek asymptotically 
good binary codes for each of these definitions of explicitness. To do we will introduce a new 
way of combining codes called “code concatenation”.

Before we get into the main tool introduced in this chapter, let us briefly recall all the 
explicit binary codes we have seen so far.  In Section 2.4 we introduced the Hamming code, 
which has rate R = 1 − O(log n/n) and relative distance δ = O(1/n) for block length n.  In 
Section 2.6 we introduced the Hadamard code, which has rate R = O(log n/n) and relative 
distance 1/2.  Both of these codes have extremely good values of one of two parameters, 
rate or relative distance,  at the expense of the other parameter,  which has an extremely 
poor value.  It turns out we can turn Reed-Solomon codes, which are naturally codes over 
a large alphabet, into binary codes with some loss in relative distance.  Specifically given 
an [n, k, n − k + 1]q Reed-Solomon code we can write elements of Fq as ⌈log q⌉ bit strings 
and this gives a code that maps messages in Fk
q  to {0, 1}n⌈log q⌉.  The distance of this code 
is at least n − k + 1.  And if q = n = 2s then we can actually make this a linear code over 
F2 giving a [n log n, k log n, n − k + 1]2 code.  (See Exercise ??.)  We refer to these codes as 
binary-RS codes.  Thus, if we set k = n/2 for instance, then we get a code of rate 1/2 with 
relative distance Ω(1/ log n).  This yields a code which seems to get closer to the target of 
being asymptotically good, but still falls short.1  Table 7.1 summarizes these codes. 

In this chapter we will try to improve the performance of the binary-RS codes by getting 
a better (and general) technique to convert large alphabet codes into binary codes. Note that 

1One way to capture the requirement that a code of rate R and distance δ is asymptotically good is to 
require Rδ = Ω(1).  The Hamming code achieved Rδ = Θ(1/n) and the Hadamard code was mildly better 
with product Θ(log n/n).  The binary RS codes achieve Rδ = Θ(1/ log n) which is significantly better.

131



<!-- pdf-page: 144 -->
Code
Hamming
Hadamard

Binary-RS

R
1 − O (︁ log n
n
)︁
O (︁ log n

n

)︁

1
2

O

δ
O (︁ 1

n

)︁

1
2
(︂ 1
log n

n

R · δ
O (︁ 1
)︁
O (︁ log n
n
(︂ 1
O
log n

)︁
)︂

)︂

Table 7.1:  Strongly explicit binary codes that we have seen so far.

the reason for the (relatively) poor distance of the binary-RS codes is that the bit vectors 
corresponding to two different symbols of F2s may only differ by one bit.  Thus if x, y ∈ Fn
qs
differ in d positions, their binary representations as element of Fns
2  may still differ in only d
positions.

Is there a way to do better?  What would be ideal is a way to represent elements of F2s
as O(s) bit strings, but with the property that representations of two different elements of 
F2s differ in many, specifically Ω(s), coordinates.  But this is exactly the notion of an error-
correcting code!  And the requirements on the length and distance correspond to requiring 
the code to be asymptotically good.  So all we need, to get an explicit asymptotically good 
binary error-correctincg code, is an asymptotically good binary error-correcting code.

The last sentence above may seem to have landed us in the same spot where we started, 
but closer examination reveals we have made progress.  Specifically we may not need the 
code being used to represent elements of F2s (we will call this the ”inner code” from now) 
to be explicit.  Specifically our eventual goal is to build an “outer code” of length 2s and we 
have time polynomial in 2s to build the generator matrix to get an explicit outer code.  Our 
inner code on the other hand has messages of length s and we have time polynomial in 2s
to build its generator matrix.  This is a much weaker requirement than the requirement of 
polynomial time construction and this is what leads to the codes of this section.

In what follows we introduce the notion of code concatenation that formalize the steps 
outlined above, and use them to build explicit codes.  We start with the most basic form 
of this notion in Section 7.1 and use them to get explicit asymptotically-good binary codes. 
Then, in Section 7.3, we use a more involved form of code concatenation and analysis to get 
strongly explicit asymptotically-good binary codes.

7.1  Code Concatenation:  The basic idea

A (basic) concatenated code is constructed from two codes:  an outer code (which we will 
denote Cout) and an inner code (which we will denote Cin).  We first use Cout to encode the 
message to get (c0, . . . , cN −1) and then use the Cin to encode each symbol ci in the codeword 
in Cout.2  This construction is also illustrated in Figure 7.1.

2Note that unlike the usual meaning of concatenation (e.g.  string concatenation in computing), code 
concatenation does not concatenate codewords as strings.  Rather, this is a recursive construction where the 
outer code is used to reduce the block length we need from the inner code.

132



<!-- pdf-page: 145 -->
Figure 7.1:  Concatenated code Cout ◦ Cin.

We now formally define a concatenated code. For q ≥ 2, k ≥ 1 and Q = qk, consider two 

codes which we call outer code and inner code:

Cout : [Q]K → [Q]N ,

Cin : [q]k → [q]n.
Note that the alphabet size of Cout exactly matches the number of messages for Cin, which 
means that we can have a bijection between [Q = qk] and [q]k (this means we can use Cin to 
encode any symbol in a codeword in Cout).  Then given m = (m1, . . . , mK) ∈ [Q]K, we have 
the code Cout ◦ Cin : [q]kK → [q]nN  defined as

Cout ◦ Cin(m) = (Cin(Cout(m)1), . . . , Cin(Cout(m)N )) ,

where

Cout(m) = (Cout(m)1, . . . , Cout(m)N ) .

We now look at some properties of a concatenated code.

Theorem 7.1.1. If Cout is an (N, K, D)qk code and Cin is an (n, k, d)q code, then Cout ◦ Cin
is an (nN, kK, dD)q code.  In particular, if Cout (Cin resp.)  has rate R (r resp.)  and relative 
distance δout (δin resp.)  then Cout ◦ Cin has rate Rr and relative distance δout · δin.

The  first  claim  immediately  implies  the  second  claim  on  the  rate  and  relative 
Proof. 
distance of Cout ◦ Cin.  The claims on the block length, dimension and alphabet of Cout ◦ Cin
follow  from  the  definition.3  Next,  we  show  that  the  distance  is  at  least  dD.  Consider 
arbitrary m1 ̸= m2 ∈ [Q]K.  Then by the fact that Cout has distance D, we have

∆ (Cout (m1) , Cout (m2)) ≥ D.

3Technically, we need to argue that the qkK messages map to distinct codewords to get the dimension 
of kK.  However, this follows from the fact, which we will prove soon, that Cout ◦ Cin has distance dD ≥ 1, 
where the inequality follows for d, D ≥ 1.

133



<!-- pdf-page: 146 -->
Define

which along with the lower bound on distance above implies

S = {i ∈ [N ]|Cout (m1)i ̸= Cout (m2)i} ,

Then for each position i ∈ S, we have

|S| ≥ D.

∆ (Cin (Cout (m1)i) , Cin (Cout (m2)i)) ≥ d,

(7.1)

(7.2)

as Cin has distance d.  Since there are at least D such positions (from (7.1)), (7.2) implies

∆ (Cout ◦ Cin (m1) , Cout ◦ Cin (m2)) ≥ dD.

The proof is complete as the choices of m1 and m2 were arbitrary.

If Cin and Cout are linear codes,  then so is Cout ◦ Cin.  Indeed,  this can be proved for 
example, by defining a generator matrix for Cout ◦ Cin in terms of the generator matrices of 
Cin and Cout.  The proof is left as an exercise.

7.2  Zyablov Bound

We now instantiate outer and inner codes in Theorem 7.1.1 to obtain a new lower bound on 
the rate given a relative distance.  We’ll initially just state the lower bound (which is called 
the Zyablov bound) and then we will consider the explicitness of such codes.

We begin with the instantiation of Cout.  Note that this is a code over a large alphabet, 
and we have seen an optimal code over large enough alphabet:  Reed-Solomon codes (Chap­
ter 5).  Recall that the Reed-Solomon codes are optimal because they meet the Singleton 
bound  4.3.1.  Hence,  let  us  assume  that  Cout  meets  the  Singleton  bound  with  rate  of  R, 
i.e.  Cout has relative distance δout ≥ 1 − R.  For Cout ◦ Cin to be an asymptotically good 
code, Cin needs to have rate r > 0 and relative distance δin > 0 (i.e.  Cin also needs to be 
an asymptotically good code).  As noted earlier,  this is precisely the kind of code we are 
looking for to answer Question ??!  However, the saving grace will be that k can be much 
smaller than the block length of the concatenated code and hence,  we can spend “more” 
time searching for such an inner code.  But we set aside the question of explicitness for now 
and ask — what kind of parameters a concatenated code can give.

Fix ε > 0. Suppose Cin meets the GV bound (Theorem 4.2.1) with rate of r and thus has 
q (1 − r) − ε. Then by Theorem 7.1.1, Cout ◦ Cin has rate of rR and 

q (1 − r) − ε).  Expressing R as a function of δ and r, we get the following:

relative distance δin ≥ H −1
δ = (1 − R)(H −1

R = 1 −

δ
q (1 − r) − ε

H −1

.

134

 


<!-- pdf-page: 147 -->
Figure 7.2:  The Zyablov bound for binary codes.  For comparison,  the GV bound is also 
plotted.

Then optimizing over the choice of r, we get that the rate of the concatenated code satisfies

{︃

R ≥ lim
ε→0

max
0<r<1−Hq(δ+ε)

(︃

r

1 −

δ
q (1 − r) − ε

H −1

)︃}︃

,

where the bound of r < 1 − Hq(δ + ε) is necessary to ensure that R > 0.  This lower bound 
on the rate is called the Zyablov bound.  See Figure 7.2 for a plot of this bound for binary 
codes. 

To get a feel for how the bound behaves, consider the case when δ = 1

2 − γ where γ → 0. 
We claim that the Zyablov bound states that R ≥ Ω(γ3). (Recall that the GV bound for the 
same δ has a rate of Ω(γ2).)  The proof of this claim is left as an exercise (see Exercise 7.3).
Note that the Zyablov bound implies that for every δ > 0, there exists a (concatenated) 
code with rate R > 0.  However, we already knew about the existence of an asymptotically 
good code by the GV bound (Theorem 4.2.1). Thus, a natural question to ask is the following:

Question 7.2.1. Does there exist an explicit code on the Zyablov bound?

We will focus on linear codes in seeking an answer to the question above because linear 
codes have polynomial size representation. Let Cout be an [N, K]Q Reed-Solomon code where 
N = Q − 1 (evaluation points being F∗
Q with Q = qk).  This implies that k = Θ(log N ). 
However, we still need an efficient construction of an inner code that lies on the GV bound. 

135



<!-- pdf-page: 148 -->
We  do  not  expect  to  construct  such  a  Cin  in  time  poly(k)  as  that  would  answer  Open 
Question ??!  However, since k = O(log N ), note that an exponential time (in k) algorithm 
is still a polynomial (in N ) time algorithm.

There are two options for this exponential (in k) time construction algorithm for Cin:

• Perform an exhaustive search among all generator matrices for one satisfying the re­
quired property for Cin. One can do this because the Varshamov bound (Theorem 4.2.1) 
states that there exists a linear code which lies on the GV bound. This will take qO(kn)
time.  Using k = rn (or n = O(k)), we get qO(kn) = qO(k2) = N O(log N ), which is upper 
bounded by (nN )O(log(nN )), a quasi-polynomial time bound.

• The second option is to construct Cin in qO(n) time and thus use (nN )O(1) time overall. 

See Exercise 4.6 for one way to construct codes on the GV bound in time qO(n).

Using the latter construction we thus get an explicit family of codes on the Zyablov bound.

Theorem 7.2.2. For every prime power q, there exists an explicit q-ary code that achieves the 
)︂
Zyablov bound. Specifically for every ε > 0 there exists an algorithm that, given δ ∈
and n, outputs in time polynomial in n, the generator matrix of a code of block length n and 
rate

0, 1 − 1
q

[︂

R ≥

max
0<r<1−Hq(δ+ε)

r

1 −

(︃

δ
q (1 − r) − ε

H −1

)︃

.

This answers Question 7.2.1 in the affirmative.
A somewhat unsatisfactory aspect of this construction (in the proof of Theorem 7.2.2) is 
that one needs a brute force search for a suitable inner code (which sufficed though for the 
polynomial construction time).  A natural followup question is

Question 7.2.3. Does there exist a strongly explicit asymptotically good code?

We tackle this question in the next section using a more sophisticated form of concaten­

tation.

7.3  Advanced Concatenation and Strongly Explicit Con­

structions

In this section we describe strongly explicit codes that are built using the idea of concate­
nation,  but  with  some  extra  twists.  The  specific  family  of  codes  we  describe  are  due  to 
Justesen and we refer to the codes as the Justesen codes. The key insight behind these codes 
is that the arguments in the previous section can be generalized while still preserving the 
parameters of the Zyablov bound.  Specifically we may:

1. Pick N  different inner codes, one for each of the N  coordinates of the outer codeword.

136



<!-- pdf-page: 149 -->
2. It suffices if most (but not necessarily all) of these inner codes lie on the GV bound.

The reason that these options useful are that we already know how to design families of 
codes “explicitly” with the property that most of the codes are very good.  As a concrete 
example of such an ensemble,  the ensemble of all linear codes have this property (this is 
exactly what Varshamov proved).  It is only when we need to pick one that is good that we 
have a problem.  But by now allowing an entire ensemble of “inner codes” we have managed 
to reduce the task of code construction to a task we know how to solve.

The one catch with implementing the above idea is that the desired ensemble of inner 
codes must have exactly N  such codes, each containing N  codewords (of length O(log N )). 
This is much smaller than, say, the number of linear codes of length O(log N ) — the number 
of such codes is 2Θ(log2 N ) which is in fact greater than any polynomial in N .

In what follows we will describe a new construction of an ensemble and this will lead us 

to the Justesen code.  We now turn to the details.

The Justesen code is specified by an (N, K, D)qk outer code (Cout) and N  different in­
in : 1 ≤ i ≤ N ).  Formally, the concatenation of these codes, denoted by Cout ◦
)︁, is defined as follows: given a message m ∈ [︁qk]︁K
, let the outer codeword be de­

ner codes (C i
(︁C 1
in, . . . , C N
noted by (c1, . . . , cN ) def= Cout(m). Then Cout◦(︁C 1

)︁ (m) = (C 1

in(c2), . . . , C n

in, . . . , C N

in(c1), C 2

in

in

in(cN )).

For the inner family of codes we will use the following result, which shows that there is 

a set or ensemble of codes most of which lie on the Gilbert-Varshamov bound.

Theorem 7.3.1.   Let ε > 0.  There exists an ensemble of inner codes C 1
rate 1
2, where N = qk − 1, such that for at least (1 − ε)N  values of i, C i
≥ H −1

in, C 2

in, . . . , C N

in  of 
in has relative distance 

2 − ε)︁.
(︁ 1

q

In fact, this ensemble is the following:  for α ∈ F∗

q  is 
in(x) = (x, αx). This ensemble is called the Wozencraft ensemble. We claim that 
qk is linear and is strongly explicit.  (The proof is left as an exercise.)

qk, the inner code C α

defined as C α
in for every α ∈ F∗
C α

q → F2k

in : Fk

7.3.1  Justesen code
For the Justesen code, the outer code Cout is a Reed-Solomon code evaluated over F∗
qk of 
rate R, with 0 < R < 1.  The outer code Cout has relative distance δout = 1 − R and block 
length of N = qk − 1.  The set of inner codes is the Wozencraft ensemble {C α
qk  from 
Theorem 7.3.1. So the Justesen code is the concatenated code C ∗ def= Cout ◦ (C 1
in, . . . , C N
in )
with the rate  R

2 .  The following proposition estimates the distance of C ∗.

in}α∈F∗

in, C 2

Proposition 7.3.2. Let ε > 0.  C ∗ has relative distance at least (1 − R − ε) · H −1

q

2 − ε)︁
(︁ 1

Proof. 
where

Consider m1 ̸= m2 ∈ (Fqk)K.  By the distance of the outer code |S| ≥ (1 − R)N , 

S = {︁i|Cout(m1)i ̸= Cout(m2)i

}︁ .

137



<!-- pdf-page: 150 -->
2 − ε)︁ · 2k. Otherwise, the 
(︁ 1
in has distance at least d def= H −1
Call the ith inner code good if C i
inner code is considered bad.  Note that by Theorem 7.3.1, there are at most εN  bad inner 
codes.  Let Sg be the set of all good inner codes in S, while Sb is the set of all bad inner 
codes in S.  Since Sb ≤ εN ,

q

|Sg| = |S| − |Sb| ≥ (1 − R − ε)N.

For each good i ∈ S, by definition we have
m1)︁

∆ (︁C i

(︁Cout

(︁

in

)︁ , C i

in

i

(︁Cout

(︁

m2)︁

i

)︁)︁ ≥ d.

(7.3)

(7.4)

Finally, from (7.3) and (7.4), we obtain that the distance of C ∗ is at least

(1 − R − ε) · N d = (1 − R − ε)H −1

q

)︃

− ε

N · 2k,

(︃ 1
2

as desired.

Since the Reed-Solomon codes as well as the Wozencraft ensemble are strongly explicit 

(see Exercise 7.4), the above result implies the following:

Corollary  7.3.3. The  concatenated  code  C ∗  from  Proposition  7.3.2  is  an  asymptotically 
good code and is strongly explicit.

Thus, we have now satisfactorily answered Question 7.2.3 modulo Theorem 7.3.1, which 

we prove next.

Proof of Theorem 7.3.1.  Fix y = (y1, y2) ∈ F2k
or y2 ̸= 0 are not possible.  We claim that y ∈ C α
a simple case analysis. First, note that if y ∈ C α

q \ {0}. Note that this implies that y1 ̸= 0
in for at most one α ∈ F∗
2k.  The proof is by 
in, then it has to be the case that y2 = α · y1.

• Case 1:  y1 ̸= 0 and y2 ̸= 0, then y ∈ C α

in, where α = y2
y1

.

• Case 2:  y1 ̸= 0 and y2 = 0,  then y /∈ C α

product of two elements in F∗

2k also belongs to F∗

in for every α ∈ F∗
2k).

2k (as αy1 ̸= 0 since the 

• Case 3:  y1 = 0 and y2 ̸= 0, then y /∈ C α

in for every α ∈ F∗

2k (as αy1 = 0).

Now assume that wt(y) < H −1

2 − ε)︁). Since y ∈ C α
(︁ 1

q (1 − ε)n.  Note that if y ∈ C α

in, then C α
in is “bad”(i.e.  has 
in for at most one value of α, the total number 

relative distance < H −1
of bad codes is at most

q

{︃

⃓
⃓
⃓
⃓

y|wt(y) < H −1

q

(︃ 1
2

)︃

− ε

· 2k

}︃⃓
⃓
⃓
⃓

≤ V olq

(︃

H −1
q

(︃ 1
2
( 1
2 −ε))·2k

)︃

)︃

− ε

· 2k, 2k

(7.5)

≤ qHq(H −1

q

138

 


<!-- pdf-page: 151 -->
=

2 −ε)·2k

= q( 1
qk
q2εk
< ε(qk − 1)
= εN.

(7.6)
(7.7)

In the above, (7.5) follows from our good old upper bound on the volume of a Hamming ball 
(Proposition 3.3.3) while (7.6) is true for large enough k.  Thus, for at least (1 − ε)N  values 
of α, C α

in has relative distance at least H −1

2 − ε)︁, as desired.  (cid:50)
(︁ 1

q

7.4  Summary of concatenation

In this chapter we saw how to use a simple (in retrospect) idea to build codes over small 
alphabets explicitly from explicit codes over large alphabets.  Specifically, by concatenating 
an outer code of distance D and an inner code of distance d, we can obtain a code of distance 
at  least  ≥ Dd  (Theorem  7.1.1).  Dd  is  called  the  concatenated  code’s  designed  distance. 
The  combinatorial  performance  of  these  codes  is  captured  by  the  Zyablov  bound  —  see 
Theorem 7.2.2 and Figure 7.2.  The Zyablov bound may be a bit complex to understand on 
its own so we elaborate a bit here, by focusing on the two extreme cases of maximal distance 
and maximal rate. When the distance of a binary code is 1/2−ε where ε → 0, the GV bound 
assure a code of rate Ω(ε2), whereas the Zyablov bound achieves rate that is roughly Ω(ε3)
(ignoring poly log 1/ε factors). (See Exercise 7.3 for details.) On the other extreme when the 
distance of the code is δ → 0, the GV bound assures us of codes of rate 1−O(δ log 1/δ), while 
δ) (again ignoring poly log 1/δ
the Zyablov bound only achieves a rate of roughly 1 − O(
factors) — see Part (4) of Exercise 7.12.  The Zyablov bound is not known to be improvable 
in the high-distance regime using variations of concatenation. However at the other extreme 
of low-rate, a variation of concatenation due to Blokh and Zyablov does improve significantly 
on the Zyablov bound.  The resulting Blokh-Zyablov bound approaches the GV bound upto 
polylogarithmic  factors  in  δ.  Exercise  7.12  describes  the  variation  and  illustrates  how  it 
improves on the rate in the low-distance regime.

√

Turning to the algorithm aspects results presented in this chapter,  for asymptotically 
good codes, we have obtained polynomial time construction of such codes (Theorem 7.2.2) 
thereby making them “explicit”.  We also showed how to get strongly explicit construction 
of such codes (Corollary 7.3.3), i.e., constructions where the entries of the generator matrix 
can be constructed in polynomial time.  Further, since these codes were linear, we also get 
polynomial  time  encoding.  However,  the  following  natural  question  about  decoding  still 
remains unanswered.

Question 7.4.1. Can we decode concatenated codes up to half their designed distance in 
polynomial time?

We will answer this question in Chapter ??.

139



<!-- pdf-page: 152 -->
7.5  Exercises

Exercise  7.1. Let  us  define  a  code  C ⊆ Fn
2   to  be  a  binary  RS  code  if  there  exists  q =
2t,  n′,  a  Reed-Solomon  code  C ′ ⊆ Fn′
2  such  that  C =
{(φ(x1), . . . , φ(xn′)) | (x1, . . . , xn′) ∈ C ′))}. (In other words C is obtained by taking codewords 
of C ′ and writing elements of Fq as t bit binary strings.)  For every 0 ≤ R ≤ 1 and integer 
t, prove that there exist linear binary RS codes of block length n = t2t, rate R and relative 
distance at least  1−R
log n.

q   and  a  bijective  map  φ : Fq → Ft

Exercise  7.2. Prove that the concatenation of two linear codes is linear.  Specifically let 
q  be an Fq linear code of dimension k.  Then 
Cout ⊆ FN
prove that Cout ◦ Cin is an Fq-linear code.  Describe the generator matrix of Cout ◦ Cin.

qk be an Fqk-linear code and let Cin ⊆ Fn

Exercise 7.3. Prove that Theorem 7.2.2 yields explicit binary codes of distance δ = 1/2 − γ
and rate R = Ω(γ3) for every γ > 0.  Specifically show that there exists a constant η > 0
such that for all γ > 0 there exists an explicit family of binary codes of relative distance at 
least 1/2 − γ and rate at least η · γ3.

2 be an F2-linear bijection.  Recall 
Exercise 7.4. Given positive integer t, let φ : F2t → Ft
that  the  Wozencraft  ensemble  of  codes  is  the  collection  of  codes  {Cα ⊆ F2t
2t}
2
where Cα is given by the encoding map Eα : β ↦→ φ(β) ◦ φ(αβ) for every β ∈ F2t.  (Thus 
Eα : F2t → {F 2t
2 .  Recall further that the Justesen code of rate 1/4 is given by the encoding 
map EJustesen : Ftk
2t  where k = 2t−1
and C(x) = ∑︁k−1

 given by (φ(c0), . . . , φ(ck−1)) ↦→ (Eα(P (α))α∈F
i=0 cixi for every (c0, . . . , ck−1) ∈ Fk
2t.

2 → F2t2t

| α ∈ F∗

2

1. Prove that for every α ∈ F∗

2t, the code Cα is a linear code.

2. Prove that the Justesen code is a linear code.

3. Prove  that  the  Justesen  code  is  strongly  explicit,  i.e.,  give  a  generator  matrix  G ∈
 that generates the Justesen code such that there is a poly(t) time algorithm 

Fkt×2t2t
computing the (i, j)th entry of the generator matrix, given (i, j) ∈ [kt] × [2t2t].

2

Exercise 7.5. Prove that a random code in the Wozencraft ensemble achieves capacity on 
BSCp for every p < H −1(1/2).  Specifically, given ε > 0 and p = H −1(1/2) − ε, prove that 
there exists γ > 0 such that for every t there exists α ∈ Ft
2 → Ft
such that for every m ∈ Ft

2 and a decoding map D : F2t

2 we have

2

Pr
e∼BSC(p)

[D(Eα(m) + e) ̸= m] ≤ 2−γt.

Exercise 7.6. Let us say that linear codes C1, . . . , CM ⊆ Fn
2  if (i) All 
codes are of the same size (so |Ci| = |Cj| for all i, j ∈ [M ]); and (ii) They have the minimal 
possible intersection i.e., Ci ∩ Cj = {0n} for all i ̸= j.

2  form a packing in Fn

140



<!-- pdf-page: 153 -->
1. Prove that if C1, . . . , CM  form a packing, and d is such that ∑︁d−1

(︁n
i

)︁ < M  then there 

i=1

exists i ∈ [M ] such that ∆(Ci) ≥ d.

2. Extend  the  Wozencraft  ensemble  to  get  codes  of  rate  1/ℓ  and  distance  approaching 

H −1(1 − 1/ℓ) for (constant) every positive integer ℓ.

3. Extend the notion of a “packing’ to a notion of ‘uniform cover” so as to build codes of 

rate 1 − 1/ℓ and distance H −1(1/ℓ).

2t be a Reed-Solomon code of rate ε.  Let CHad,t ⊆ F2t

Exercise 7.7. Let CRS ⊆ F2t
2  be the 
Hadamard code of dimension t and block length 2t (from Definition 2.6.2).  Prove that their 
concatenation yields an [n = 4t, k = t2t]2 linear code where every non-zero codeword has 
Hamming weight in the interval [︁(1 − ε) n
]︁.  Conclude that there exists an explicit 
2 , (1 + ε) n
ε-biased space in Fk

(︂ k2

2 of size O

)︂

.

2

ε2 log2 k

Exercise 7.8. In this exercise we prove that (generalized) concatenated codes with the inner 
code having logarithmic length can achieve the asymptotic Gilbert-Varshamov bound.  Specif­
ically, let CRS be an [N, K, N − K + 1]N  code where N = 2t.  Let C 1, . . . , C N ⊆ Ft
2 be random 
independent linear codes of rate 1 (i.e., each is given by an random linear map (possibly with 
a non-trivial kernel) from FN → Ft
2 chosen uniformly and independently from the set of all 
such mappings).  Prove that the concatenated code C = CRS ◦ (C 1, . . . , C N ) has, with high 
probability, rate R = K/N  and relative distance approaching H −1(1 − R).

Exercise 7.9. This exercise explores the relative distance of duals of concatenated codes. 
Part (1) shows that most concatenated codes have very poor dual distance.  Part (2) shows 
that with some care we can get a dual code of modest relative distance.

1. Let C = Cout ◦ Cin be a linear concatenated code where Cin is an [n, k]q code for some 

k < n.  Prove that the minimum distance of C ⊥ is at most k + 1.

2. Prove that if C = Cout ◦ Cin is a linear concatenated code where Cin is an [n, n]q code, 

then the relative minimum distance of C ⊥ is at least δ(C ⊥

out)/n.

Exercise 7.10. Given prime power q and integer r ≤ q2,  the Hermitian code Hq,r is an 
explicit [n, k, d]q2 code for n = q3, k = (︁r+1
)︁ and d = n−rq. Given ε > 0 and K0, give a choice 
of parameters q, r, t such that the concatenation of the Hermitian code Hq,r with the Hadamard 
)︂5/2}︃)︃

{︃

(︃

2

code CHad,t yields an [N, K]2 binary code with K ≥ K0, N = O
with the weight of every non-zero codeword lying in the interval [(1−ε) N
there exists an explicit ε-biased space in FK

2  ot size at most O

max

{︃

(︃

max

2 , (1+ε) N
2 ]. Conclude 
)︂5/2}︃)︃
(︂ √
K
K 5/2,
ε

. (In 

K 5/2,

(︂ √
K
ε

particular when ε = 1/K this improves up the concatenation of Reed-Solomon codes with 
Hadamard codes from Exercise 7.7, by achieving N = O(K 15/4) as opposed to N = O(K 4).)

141



<!-- pdf-page: 154 -->
Exercise 7.11. Show that one can get a fully explicit asymptotically good code using a two-
stage  concatenation  with  two  outer  layers  of  Reed-Solomon  codes  and  an  inner  code  that 
is selected from an exponentially large ensemble of codes.  Specifically show that there exist 
Reed-Solomon codes C1 and C2 and a code C3 chosen from,  say,  a Wozencraft ensemble, 
such that C1 ◦ C2 ◦ C3 is fully explicit and asymptotically good.

Exercise 7.12. In this exercise we will describe a more careful and advanced concatenation 
scheme that significantly improves upon the Zyablov bound for high rates.  Given positive 
integers c, and t1, . . . , tc with t1 + · · · + tc = t, a c-level concatenation of type (t1, . . . , tc) is 
q → (Fti
given by c + 1 Fq-linear codes C 1
q )n for i ∈ [c] and 
Cin : Ft
out)◦Cin is a code mapping 
Fk
q → FnT
q , let 
xi = (xi

q → FT
q  for k = k1 + · · · + kc given as follows.  Given m = (m1, . . . , mc) with mi ∈ Fki
1, . . . , xi

q . The concatenated code, denoted C = (C 1

out : Fki
out ×· · ·×C c

j).  Then C(m) = (yj)j∈[n].

q )n and let yj = Cin(x1

n) = Cout(mi) ∈ (F ti

out and Cin with C i

out, . . . , C c

j , . . . , xc

The power of the multilevel concatenation described above comes from analyzing the per­
formance of Cin carefully as follows: We say that Cin has (t1, . . . , tc)-type distance (δ1, . . . , δc)
in defined below has distance δ(C i
if for every i ∈ [c] the code C i
in = {︁Cin(0t1+···ti−1mi)|mi ∈ Fti+···+tc
C i

in) ≥ δi:
}︁ .

q

In  other  words  the  distance  type  measures  not  only  the  distance  of  the  code  Cin  but  also 
subcodes obtained by restricting messages whose prefixes are zeroes. Every code Cin of distance 
δ  has  (t1, . . . , tc)-type  distance  (δ, . . . , δ),  but  for  most  codes  we  can  get  better  values  of 
δ2, δ3, . . . ,.  Part (2) of the exercise below proves this, while Part (3) shows how this allows 
us to use codes of C 2
out, . . . of higher rate than may be allowed by a vanilla use of the 
Zyablov bound.  In turn this bumps up the rate of our final code.

out, C 3

1. Let Ri = ki

tin  denote the rate of the code C i

out and let τi = ti

the redundancy of a code of rate R.  Verify that the rate of C is R = t
T
redundancy  ¯R ≤ (1 − t/T ) + ∑︁c
i=1 τi

¯Ri.  Verify that C is Fq-linear.

t .  Let  ¯R := 1 − R denote 
∑︁
i τiRi and its 

2. Fix  ε > 0.  Prove  that  there  exists  δ > 0  such  that  a  random  linear  code  Cin  has 
T (ti +· · ·+tc), 

(t1, . . . , tc)-type distance (δ1, . . . , δc), where δi = H −1
with probability at least 1 − exp(−δT ).

q (1−ri)−ε and ri = 1

3. Prove that the minimum distance of C is mini{δi · δ(C i

out)}.

Hint:  Given m = (m1, . . . , mc) consider the smallest i such that mi ̸= 0 and prove that C(m) has 
weight at least δiCoutδ(C i

out)nT . 

4. Fix ε > 0.  In the following parts, let q be large enough so that H −1
q (1 − R) ≥ 1 − R − ε
for every R ∈ [0, 1].  Prove that Zyablov bound (see Theorem 7.2.2) on the rate RZ of 
√
√
codes of minimum distance δ satisfies 1 − 2

δ − ε ≤ RZ ≤ 1 −

δ.

5. For every δ, ε > 0 for sufficiently large q, prove that for every sufficiently large N  there 
out) ◦ Cin of length N , distance 

exists a q-ary two level concatenated code C = (C 1

out × C 2

142



<!-- pdf-page: 155 -->
δ − O(ε) and rate 1 − δ2/3 − O(ε).
Hint:  Let γ = t1
in!)  are on the 
Singleton bound, prove that the redundancy of C can be upper bounded by ρ + γδ/ρ + δ/γ.  Optimize 
over δ and γ.

 and ρ = δ(Cin).  Ignoring ε and assuming all codes (including C 2

t1+t2

6. Extend the idea above so that for every δ > 0, positive integer c, and ε > 0, we get 

concatenated codes of distance δ − ε and rate at least 1 − Oc(δ1−1/c) − ε.

Remark 7.5.1. We note that the exercise above can be carried out with q = 2 to get codes of 
distance δ and rate 1 − Oc(H2(δ)1−1/c) − ε) also, at the price of some slightly more complex 
expressions in the calculations.

7.6  Bibliographic Notes

Code concatenation was first proposed by Forney [25].  In addition to the introduction of 
the technique, Forney also gave decoding algorithms for concatenated codes that were strong 
enough to achieve convergence to Shannon capacity with polynomial time algorithms. These 
algorithms, and the convergence to capacity will be covered in later chapters (in particular 
in Chapter ??).  The tradeoff between rate and distance of these codes were explored by 
Zyablov [77] and in particular the Zyablov bound (see Theorem 7.2.2) is from there.

The Justesen codes were constructed by Justesen [41].  The Wozencraft ensembles were 
first reported by Massey [51] who attributes them to a personal communication with Wozen­
craft.  The low-rate variant of these ensembles from Part (2) of Exercise 7.6 is due to Wel­
don [40].

The multilevel concatenation from Exercise 7.12 is due to Blokh and Zyablov [8], who 
also give a closed form expression for optimized versions of these codes, called the Blokh-
Zyablov bound.  The exact expression is somewhat complex, involving some integrals, and 
omitted from this book. Instead Exercise 7.12 gives a flavor of the implications of this bound 
focussing on the high-rate regime. We refer the reader to the survey article by Dumer [19] for 
further details on the Blokh-Zyablov bound as well as other aspects of concatenated codes.

143



<!-- pdf-page: 156 -->
144



<!-- pdf-page: 157 -->
Part IV

The Algorithms

145



<!-- pdf-page: 158 -->


<!-- pdf-page: 159 -->
Chapter 8

Efficient Decoding of Reed-Solomon 
Codes

In this chapter, we consider the task of decoding Reed-Solomon codes.  We know that if the 
number of errors is less than half the minimum distance of the code, then the received word 
uniquely determines the codeword.  In this chapter we start with an efficient algorithm that 
computes the codeword, given the corrupted received word.  We then generalize this algo­
rithm to a list decoding algorithm that efficiently achieves the Johnson bound (Theorem ??), 
i.e., given a received word that was obtained from the transmitted codeword with number of 
errors being bounded by the Johnson radius for this code, our algorithm efficiently outputs 
a small list of words that includes the transmitted word.

8.1  Unique decoding of Reed-Solomon codes

i=0 ciX i or equivalently its coefficients (c0, . . . , ck−1) ∈ Fk

Consider the [n, k, d = n − k + 1]q Reed-Solomon code with evaluation points (α1, · · · , αn). 
(Recall Definition 5.2.1.)  In this section we solve the “unique decoding” problem associated 
with  this  code.  We  start  by  recalling  this  problem.  Here  the  message  is  a  polynomial 
P (X) = ∑︁k−1
q .  Its encoding is the 
vector  (P (α1), . . . , P (αn)) ∈ Fn
q .  The  transmission  introduces  errors  and  results  in  some 
received vector y = (y1, . . . , yn) ∈ Fn
q .  The number of errors is the quantity e = |{i ∈ [n] |
yi ̸= P (αi)}|.  The goal of “unique decoding” is to recover P  from y provided e < n−k+1
, 
i.e., when the number of errors is less than half the minimum distance.  We summarize the 
resulting problem below:

2

Problem 8.1.1  (Reed-Solomon Unique Decoding). Consider the following problem:

• Input:  Code Parameters:  Fq, (α1, . . . , αn) ∈ Fn

q  and k.  Received word:  y ∈ Fn
q .

• Output:  P (X) ∈ Fq[X] of degree less than k such that e := |{i ∈ [n] | yi ̸= P (αi)}| <

n−k+1
2

 if such a polynomial exists and fail otherwise.

147



<!-- pdf-page: 160 -->
8.1.1  Motivating the decoding algorithm

We will now do a syntactic shift that will help us better visualize the decoding problem and 
algorithm (in fact all problems and algorithms in this chapter).  In this view, we will think 
of  y  as  the  set  of  ordered  pairs  {(α1, y1), (α2, y2), . . . , (αn, yn)},  that  is,  as  a  collection  of 
“points” in “2-D space.” See Figure 8.1.1 for an illustration.  From now on, we will switch 
back and forth between our usual vector interpretation of y and this new geometric notation.

Figure  8.1:  An  illustration  of  a  received  word  for  a  [14, 2]  Reed-Solomon  code 
(we  have  implicitly  embedded  the  field  Fq  in  the  set  {−7, . . . , 7}).  The  evalu­
ation  points  are  (−7, −5, −4, −3, −2, −1, 0, 1, 2, 3, 4, 5, 6, 7)  and  the  received  word  is 
(−7, 5, −4, −3, 2, −4, 0, 1, −2, 3, 4, −5, −2, 7).

Further, let us assume that there exists a polynomial P (X) of degree at most k − 1 such 

that

∆ (y, (P (αi))n

i=1) ≤ e.

Alternatively, this means for at least n − e locations i ∈ [n], we have P (αi) = yi.  (Recall 
that if such a P (X) exists then it is unique.)  See Figure 8.2 for an illustration.

We will use reverse engineering to design a unique decoding algorithm for Reed-Solomon 
codes. We will assume that we somehow know P (X) and then prove some identities involving 
the coefficients of P (X).  Then, to design the algorithm, we will just use the identities and 
try to solve for P (X). Towards this end, let us assume that we also magically got our hands 
on a polynomial E(X) such that

Definition  8.1.2   (Error-Locator  Polynomial). A  non-zero  polynomial  E(X)  is  called  an 
error-locator polynomial if for all i ∈ [n] we have:

E (αi) = 0 if yi ̸= P (αi) .

148



<!-- pdf-page: 161 -->
Figure 8.2:  An illustration of the closest codeword P (X) = X for the received word from 
Figure 8.1.1.  Note that we are considering polynomials of degree 1, which are “lines.”

In other words, the roots of the error location polynomials include the locations where 
P  and y disagree (i.e.  there is an error).  We remark that there exists such a polynomial of 
degree at most e.  In particular, consider the polynomial:

E(X) =

∏︂

(X − αi) .

i:yi̸=P (αi)

Now we claim that for every 1 ≤ i ≤ n,

yiE (αi) = P (αi) E (αi) .

(8.1)

To see why (8.1) is true, we consider the following two cases:

1. If yi ̸= P (αi), then both sides of (8.1) are 0 (as E(αi) = 0).

2. On the other hand, if yi = P (αi), then multiplying both sides by E(αi) preserves the 

equality and so (8.1) holds in this case also.

All the discussion above does not seem to have made any progress as both E(X) and 
P (X) are unknown.  Indeed, the task of the decoding algorithm is to find P (X).  Further, if 
E(X) is known then one can easily compute P (X) from y (the proof is left as an exercise). 
However, note that we can now try and do reverse engineering.  If we think of coefficients 
of P (X) (of which there are k) and the coefficients of E(X) (of which there are e + 1) as 
variables, then we have n equations from (8.1) in e + k + 1 variables.  From our bound on 
e,  this  implies  we  have  more  equations  than  variables.  Thus,  if  we  could  solve  for  these 

149



<!-- pdf-page: 162 -->
unknowns, we would be done.  However, there is a catch– these n equations are quadratic 
equations, which in general are NP-hard to solve (see Definition ?? for more on NP-hardness). 
However, note that for our choice of e, we have e + k − 1 ≪ n. Next, we will exploit this with 
a trick that is sometimes referred to as linearization.  The idea is to introduce new variables 
so that we can convert the quadratic equations into linear equations. Care must be taken so 
that the number of variables after this linearization step does not exceed the (now linear) 
n equations.  If we can do this,  we will be in familiar territory as we know how to solve 
linear equations over a field (e.g.  by Gaussian elimination).  (See Section 8.5 for some more 
discussion on the hardness of solving quadratic equations and the linearization technique.)

To perform linearization, define N (X) def= P (X)·E (X). Note that N (X) is a polynomial 
of degree less than or equal to e + k − 1.  Further, if we can find N (X) and E (X), then we 
are done.  This is because we can compute P (X) as follows:

P (X) =

N (X)
E (X)

.

In particular, the definitions above require N (X) to be a multiple of E(X) and finding 
N (X) and E(X) such that N (X) is a mulitple of E(X) retains all the computational hardness 
of the problem at hand. The main idea in the Welch-Berlekamp algorithm is to “forget” the 
constraint that E(X) should divide N (X) and focus on the remaining constraints: So N (X)
should still have degree at most k + e − 1, E(X) should still have degree at most e, and 
for every i, we should have N (αi) = yi · E(αi).  This suggests a simple algorithm which we 
present below and then present the arguably subtle analysis of its correctness.  (Note that 
switching from P (X) · E(X) to N (X) is the so-called linearization.  It simplifies the search, 
but may have completely changed the problem being solved.  The analysis will aim to show 
that this switch still solves our target problem!)

8.1.2  Welch-Berlekamp Algorithm

At  a  high  level,  the  Welch-Berlekamp  algorithm  finds  two  low-degree  polynomials  N (X)
and E(X) that together “explain” all the input pairs.  Specifically the polynomials satisfy 
N (αi) = yi · E(αi) for all i.  The algorithm outputs N (X)/E(X) provided this ratio is a 
polynomial of the right degree with few errors.  Details of what is “high” and “right” are 
given in Algorithm 8.1.1 which formally states the algorithm.

8.1.3  Analysis of the Welch-Berlekamp Algorithm

As stated, apart from Step 1, all other steps of the algorithm are clearly efficiently imple­
mentable.  Step 1 is also efficiently implementable but we defer the proof of this for now. 
Instead we assume it can be solved efficiently as specified, and turn to analyzing the correct­
ness of Algorithm 8.1.1.

150



<!-- pdf-page: 163 -->
Algorithm 8.1.1 Welch-Berlekamp Algorithm
Input: n ≥ k ≥ 1, 0 < e < n−k+1
2
Output: Polynomial P (X) of degree at most k − 1 or fail.
1: Compute a non-zero polynomial E(X) of degree exactly e, and a polynomial N (X) of 

 and n pairs {(αi, yi)}n

i=1 with αi distinct

degree at most e + k − 1 such that

yiE(αi) = N (αi)

1 ≤ i ≤ n.

(8.2)

2: if E(X) and N (X) as above do not exist or E(X) does not divide N (X) then
return fail
3:  
4: P (X) ← N (X)
E(X) .
5: if ∆(y, (P (αi))n
return fail
6:  
7: else
8:  

i=1) > e then

return P (X)

Correctness of Algorithm 8.1.1.  Note that if Algorithm 8.1.1 does not output fail, then 
the algorithm produces a correct output.  Thus, to prove the correctness of Algorithm 8.1.1, 
we just need the following result.

Theorem  8.1.3.  If  (P (αi))n
most  k − 1)  and  at  most  e < n−k+1
Welch-Berlekamp algorithm outputs P (X).

2

i=1  is  transmitted  (where  P (X)  is  a  polynomial  of  degree  at 
i=1) ≤ e),  then  the 

  errors  occur  (i.e.  ∆(y, (P (αi))n

Note that the above implies that the Welch-Berlekamp algorithm can correct RS codes 

of rate R for up to  1−R

2  fraction of errors.

The proof of the theorem above follows from the following two claims.

Claim 8.1.4. There exist a pair of polynomials E∗(X) and N ∗(X) that satisfy Step 1 such 
that  N ∗(X)

E∗(X) = P (X).

Proof.  We just take E∗(X) to be an error-locating polynomial for P (X) and let

N ∗(X) = P (X)E∗(X),

where deg(N ∗(X)) ≤ deg(P (X)) + deg(E∗(X)) ≤ e + k − 1.  In particular, define E∗(X) as 
the following polynomial of degree exactly e:

E∗(X) = X e−∆(︁

y,(P (αi))n

i=1

)︁ ∏︂

(X − αi).

1≤i≤n|yi̸=P (αi)

(8.3)

By definition, E∗(X) is a non-zero polynomial of degree exactly1 e with the following prop­
erty:

E∗(αi) ̸= 0

=⇒ yi = P (αi).

1The term X e−∆(︁y,(P (αi))n

i=1

)︁

i was introduced to make sure the degree is exactly e.

151



<!-- pdf-page: 164 -->
We now argue that E∗(X) and N ∗(X) satisfy (8.2).  Note that if E∗(αi) = 0, then N ∗(αi) =
P (αi)E∗(αi) = yiE∗(αi) = 0.  When E∗(αi) ̸= 0, we know P (αi) = yi and so we still have 
P (αi)E∗(αi) = yiE∗(αi), as desired.

Given the claim above, we now have that for the condition in Step 2, a pair of polynomials 
satisfying (8.2) does exist.  So the only way our algorithm can output fail is if it finds a pair 
of polynomials (E′, N ′) such that N ′/E′ ̸= P .  To show this can not happen, we now claim 
that for any pair of solutions ((N1(X), E1(X)) and (N2(X), E2(X)) that satisfy Step 1, we 
have  N1(X)
E2(X) .  Combined with Claim 8.1.4 this implies that the ratio N ′/E′ = P  for 
any solution produced in Step 1.

E1(X) = N2(X)

Claim 8.1.5. If any two distinct solutions (E1(X), N1(X)) ̸= (E2(X), N2(X)) satisfy Step 
1, then they will satisfy

N1(X)
E1(X)

=

N2(X)
E2(X)

.

Proof. 

Let us define polynomial R(X) with degree at most 2e + k − 1 as follows:

R(X) = N1(X)E2(X) − N2(X)E1(X).

(8.4)

Note that the degrees of each of the polynomials N1(X)E2(X) and N2(X)E1(X) is at most 
2e + k − 1. Thus R(X) is also a polynomial of degree at most 2e + k − 1. Furthermore, from 
Step 1 we have, for every i ∈ [n] ,

N1(αi) = yiE1(αi)

and N2(αi) = yiE2(αi).

(8.5)

We use this to show that R(αi) = 0 for every 1 ≤ i ≤ n.  Specifically we have

R(αi) = N1(αi)E2(αi) − N2(αi)E1(αi)

= (yiE1(αi))E2(αi) − (yiE2(αi))E1(αi)
= 0,

(8.6)

where the first equality is by the definition of R(X) (8.4) , and the second one is obtained 
by substituting N1(αi) and N2(αi) using (8.5). Thus R(X) is a polynomial of degree at most 
2ek − 1 with n zeroes.  By our choice of e < n−k+1
 we have 2e + k − 1 < n, thereby proving 
R is identically zero by the degree mantra (Proposition 5.1.5).

2

Using the definition of R again, we thus have N1(X)E2(X) ≡ N2(X)E1(X).  Note that 

as E1(X) ̸= 0 and E2(X) ̸= 0, this implies that  N1(X)

E1(X) = N2(X)

E2(X) , as desired.

From Claim 8.1.4 it follows that there exists a pair of polynomials 
Proof of Theorem 8.1.3. 
(N1, E1)  satisfying  (8.2),  with  the  further  property  that  N1(X)/E1(X) = P (X).  Thus 
Step  1  must  produce  some  pair  (N2, E2)  satisfying  (8.2).  By  Claim  8.1.5  it  follows  that 
N2(X)/E2(X) = N1(X)/E1(X) = P (X).  Thus Algorithm 8.1.1 correctly outputs P (X) in 
Step 8.

152

 
 
 


<!-- pdf-page: 165 -->
Implementation of Algorithm 8.1.1.  We now argue that Algorithm 8.1.1 can be solved 
in polynomial time, specifically using at most O(n3) steps, where a single step may involve 
some field operations over Fq.

Inspecting the algorithm, we see that other than Steps 1, 2 and 4, all other steps are 
simple bookkeeping tasks that can easily in O(n) steps.  Steps 2 and 4 require the division 
of N (X) by E(X) which can also be done (using long division) with O(n2) steps.  The only 
remaining  Step  to  analyze  is  Step  1.  Here,  the  idea  is  to  note  that  this  step  essentially 
involves  solving  a  linear  system  with  n + 1  equations  in  at  most  n + 1  variables,  as  we 
elaborate below.

Denote E(X) = ∑︁e

j=0 EjX j and N (X) = ∑︁e+k−1

j=0 NjX j.  The task of finding E(X) and 
N (X) is the same as finding the coefficients E0, . . . , Ee and N0, . . . , Ne+k−1, which we treat 
hereon  as  variables.  (Note  that  we  have  e + 1 + e + k = 2e + k + 1 ≤ n + 1  variables, 
where the inequality follows from our bound on e.)  Now note that each of the constraints 
yiE(αi) = N (αi) is a linear equation in the variables. So (8.2) is essentially a linear system of 
equations in some variables. But we are not done: One more constraint needs to be enforced, 
namely that E(X) has degree exactly e.  This amounts to saying Ee ̸= 0, but this is not a 
linear constraint. However if we replace this with the constraint Ee = 1, then we get a linear 
system with n + 1 equations.  In other words, we have a system of n + 1 linear equations in 
at most n + 1 variables, which can be solved in O(n3) time2.  We claim this solves the task 
in Step 1.  To see this note that every solution to our linear system is also a solution to the 
task defined in Step 1 — in particular Ee = 1 forces the degree of E(X) to be exactly e as 
required.  Conversely suppose Step 1 has a solution E(X) and N (X) with Ee ̸= 0.  Then 
note that E′(X) = E−1
· N (X) also form a solution to Step 1, 
with the coefficient of X e in E′(X) being exactly one.  So if Step 1 has a solution, then so 
does our linear system.  We conclude that Step 1 can be correctly solved in O(n3) time by 
solving this linear system.  Thus the entire algorithm described above runs in O(n3) time.

· E(X) and N ′(X) = E−1

e

e

Thus, we have proved that Algorithm 8.1.1 runs in polynomial time. We have thus proven 

the following theorem.

Theorem 8.1.6. The Reed-Solomon Unique Decoding can be solved in O(n3) time.

Recall that the above is a restatement of the error decoding part of Theorem ??.  Thus, 
this fills in the final missing piece from the proofs of Theorem ?? (decoding certain concate­
nated codes up to half of their design distance) and Theorem ?? (efficiently achieving the 
BSCp capacity).

8.2  List Decoding Reed-Solomon Codes

Recall Question ??, which asks if there is an efficient list decoding algorithm for a code of rate 
R fraction of errors, i.e., up to the Johnson bound (Theorem ??) 
R > 0 that can correct 1−

√

2See Exercise 2.7 for the claimed runtime.  Also see Section 8.5 for pointers on more efficient implemen­

tations.

153



<!-- pdf-page: 166 -->
for the code, assuming the code meets the Singleton bound and achieves δ = 1 − R.  In the 
rest of  this  chapter we answer this  question  affirmatively by showing that  Reed-Solomon 
codes of rate R can be efficiently list-decoded up to 1 −
R fraction of errors. Note that this 
gives us an explicit code answering Question ??.  To this end, we will present a sequence of 
algorithms for (list) decoding Reed-Solomon codes that will list-decode from an increasing 
fraction of errors, till we ultimately answer Question ??.

√

Before we talk about the algorithms, we restate the (list) decoding problem for Reed-

Solomon codes.

Problem 8.2.1  (Reed-Solomon List Decoding). Consider the following problem:

• Input:  Code Parameters:  Fq, (α1, . . . , αn) ∈ Fn

q  and k and e.  Received word:  y =

(y1, . . . , yn) ∈ Fn
q .

• Output:  A list (set) of all polynomials P (X) ∈ Fq[X] of degree less than k such that 

t := |{i ∈ [n] | yi = P (αi)}| ≥ n − e.

Our main goal of course is to make t as small as possible or e as large as possible.  The 
nk.  In contrast the unique 

Johnson bound in this setting would allow t to be as small as 

√

.  (Note that by the AM-GM inequality we 

decoding setting corresponds to the t >
nk ≤ n+k

always have 

√

2 .)

n + k
2

8.2.1  Structure of the (list-)decoding algorithms

We  start  by  reviewing  the  Welch-Berlekamp  algorithm  in  Algorithm  8.1.1,  which  we  re­
state below in a slightly different form (that will be useful in developing the subsequent list 
decoding algorithms).

• Step 1: Find polynomials N (X) of degree k + e − 1, and E(X) of degree e such that

N (αi) = yiE(αi),  for every 1 ≤ i ≤ n

• Step 2:  If Y − P (X) divides Q(X, Y ) := Y E(X) − N (X), then output P (X) (assuming 

∆(y, (P (αi))n

i=1) ≤ e).

Note that Y − P (X) divides Q(X, Y ) in Step 2 above if and only if3 P (X) = N (X)

E(X) , 

which is exactly what Step 4 does in Algorithm 8.1.1.

Rewriting the Welch-Berlekamp Algorithm yet another time, note that we can interpret 

the algorithm as having an “interpolation” step and a “root-finding” step as follows:

• Step 1: (Interpolation Step) Find non-zero Q(X, Y ) such that Q(αi, yi) = 0, 1 ≤ i ≤ n.

3Indeed Q(X, Y ) = E(X)

(︂

Y − N (X)
E(X)

)︂

, which means Y − N (X)

E(X)  is the only linear (in Y ) factor of Q(X, Y ).

154



<!-- pdf-page: 167 -->
• Step 2: (Root Finding Step) If Y − P (X) is a factor of Q(X, Y ), then output P (X)

(assuming it is close enough to the received word).

In particular, in the Welch-Berlekamp algorithm we require that Q(X, Y ) = Y E(X) −
N (X) so that the condition Q(αi, yi) = 0 is equivalent to the condition N (αi) = yiE(αi). 
The terminology “interpolation” alludes to the fact that Step 1 aims to find an algebraic 
explanation of the data, which is essentially what polynomial interpolation does.  The term 
“root-finding” comes from viewing Q(X, Y ) ∈ Fq[X, Y ] as a polynomial QX(Y ) ∈ (Fq[X])[Y ], 
i.e., a polynomial in Y  with coefficients from the ring Fq[X]. In this view, a root of QX would 
be some element P (X) ∈ Fq[X] such that QX(P (X)) = 0 or equivalently Y − P (X) divides 
Q(X, Y ).

The efficient implementation of the algorithm above relies on the fact that Interpolation 
Step can be solved by solving a linear system (possibly with some minor variations), and the 
Root-Finding step is easy in the special case where Q(X, Y ) is linear in Y , i.e., Q(X, Y ) =
E(X)Y − N (X) and the root must be N (X)/E(X) if one exists.

All the list decoding algorithms that we will consider in this chapter will have the same 
two-step structure.  The algorithms will differ in how exactly Step 1 is implemented, but 
in  all  cases  we  will  aim  to  set  the  problem  up  so  that  it  can  be  solved  by  solving  some 
linear system.  We also make a key observation that will effectively ‘take care of’ Step 2
for us.  Note that Step 2 can be implemented if one can factorize the bivariate polynomial 
Q(X, Y ) (and then only retain the linear factors of the form Y − P (X)).  Fortunately, it 
is  known  that  factoring  bivariate  polynomials  can  be  done  in  polynomial  time.  We  will 
need in particular the ability to find roots of bivariate polynomials in polynomial time, as 
captured in Theorem B.7.9.  (See also the proof of this theorem for the algorithmic ideas 
behind polynomial factorization.)

Armed  with  these  tools  we  are  now  ready  to  present  our  algorithms  for  list-decoding 
Reed-Solomon codes.  We will present three instantiations of the algorithm, which we call 
the “Basic List-Decoder”, the “Weighted-Degree List-Decoder” and the “Multiplicity List-
Decoder”.  They offer the following tradeoffs (for an [n, k] RS code with rate R = k

n ):

Frac.  of errors
t

√

Basic LD Weighted-Deg.  LD Multiplicity LD
2R
1 − 2
√
2

1 −
√

1 −
√

2nk

nk

nk

√

√

R

R

We start with the Basic List-Decoder.

8.2.2  Basic List-Decoder

The main insight in the list decoding algorithm that if we allow the degree of the poslynomial 
Q(X, Y ) to be sufficiently large then its existence is easy to establish (and so Step 1 will 
succeed.  However using too high a degree makes Q useless.  The key is to control its degree 
carefully so that the existence proof goes through, while it remains useful in Step 2.  Here 
we will use the degree restrictions, along with the degree mantra (Proposition 5.1.5), to show 

155



<!-- pdf-page: 168 -->
that Step 2 will succeed too (and find all polynomials that agree with the received word 
often).

In the Basic version of the list-decoder we restrict the degree of Q is a very simple way - 
by separately considering its degrees in X and Y  and restricting each separately.  We recall 
the definition of maximum degree of a variable.

Definition  8.2.2.  degX(Q)  is  the  maximum  degree  of  X  in  any  monomial  of  Q(X, Y ). 
Similarly, degY (Q) is the maximum degree of Y  in any monomial of Q(X, Y )

For  example,  for  Q(X, Y ) = X 2Y 3 + X 4Y 2,  degX(Q) = 4  and  degY (Q) = 3.  Given 

degX(Q) = a and degY (Q) = b, we can write

Q(X, Y ) =

cijX iY j,

∑︂

0≤i≤a,
0≤j≤b

where the coefficients cij ∈ Fq. Note that the number of coefficients is equal to (a + 1)(b + 1).
The  main  idea  in  the  first  list  decoding  algorithm  for  Reed-Solomon  code  is  to  place 
bounds on degX(Q) and degY (Q) for Step 1. The bounds are chosen so that there are enough 
variables to guarantee the existence of a Q(X, Y ) with the required properties. We will then 
use these bounds along with the degree mantra (Proposition 5.1.5) to argue that Step 2
works.  Algorithm 8.2.1 presents the details.  Note that the while this algorithm generalizes 
the spirit of the Welch-Berlekamp algorithm, our analysis will show that its performance is 
incomparable.  (I.e., there exist choices of (n, k, t) where the Basic List-Decoder recovers P
while the Welch-Berlekamp algorithm does not, and vice versa.)

Algorithm 8.2.1 The Basic List-Decoder for Reed-Solomon Codes
Input: n ≥ k ≥ 1, ℓ ≥ 1, e = n − t and n pairs {(αi, yi)}n
Output: (Possibly empty) list of polynomials P (X) of degree at most k − 1
1: Step 1 Find a non-zero Q(X, Y ) with degX(Q) ≤ ℓ, degY (Q) ≤

i=1

 such that

n
ℓ

Q(αi, yi) = 0, 1 ≤ i ≤ n.

(8.7)

2: Step 2: Factor Q(X, Y ) into irreducible factors Q1(X, Y ), . . . , Qm(X, Y ).
3: L ← ∅
4: for every factor Qj(X, Y ) = Y − Pj(X) of Q(X, Y ) do
5:  
6:  
7: return L

i=1) ≤ e and deg(Pj) ≤ k − 1 then

Add Pj(X) to L.

if ∆(y, (Pj(αi))n

Note that Step 1 and Step 2 are really the main steps in the algorithm, with remaining 
steps  being  some  simple  post-processing  to  prune  the  output  list.  We  now  analyze  the 
runtime and correctness.

156



<!-- pdf-page: 169 -->
Run time analysis.  The run time of the algorithm is clearly polynomial conditioned on 
Steps 1 and 2 being solvable in polynomial time.  Step 1 needs to find the coefficients of 
ℓ };j∈{0,...,ℓ} in Fq
the polynomial Q(X, Y ), i.e., find assignments to the variables {Qij}i∈{0,..., n
such that not all Qij’s are zero and satisfying (8.7).  Since each constraint from (8.7) is a 
homogenous linear constraint on the variables, this amounts to finding a non-trivial (non-
zero) solution to a homogenous linear system, which can be done in polynomial time (using 
say Gaussian Elimination). Turning to Step 2, this amounts to finding the root of a bivariate 
polynomial which can be done in polynonmial time using Theorem B.7.9.  We conclude that 
the Basic List-Decoder can be implemented in polynomial time.

Correctness of Algorithm 8.2.1.  We claim first that Step 1 always returns a non-zero 
polynomial Q satisfying (8.7).  This obviously true if and only if there exists a polynomial 
satisfying this condition and we argue this below.

Lemma 8.2.3. For every input sequence {(αi, yi)}n
satisfies (8.7).

i=1, there exists a non-zero Q(X, Y ) that 

To ensure the correctness of Step 1, we will need to ensure that the number of 
Proof. 
coefficients for Q(X, Y ) (which is (ℓ + 1)(n/ℓ + 1)) is larger than the number of constraints 
in (8.7) (which is n).  Indeed, note that we have
)︂

(ℓ + 1) ·

+ 1

> ℓ ·

= n.

(︂n
ℓ

n
ℓ

We need to argue that the final L in Step 6 contains all the polynomials P (X) that need 

to be output.  In other words, we need to show that

Lemma 8.2.4. If P (X) of degree ≤ k −1 agrees with Y  in at least t positions, then Y −P (X)
divides Q(X, Y ).

Proof. 

Towards this end, we define

R(X) def= Q(X, P (X)).

Note  that  Y − P (X)  divides  Q(X, Y )  if  and  only  if  R(X) ≡ 0.  Thus,  we need  to  show 
R(X) ≡ 0.  For the sake of contradiction, assume that R(X) ̸≡ 0.  Note that

deg(R) ≤

≤

degX(Q) + deg(P ) · degY (Q)
n(k − 1)
ℓ

ℓ +

.

In the above the first inequality follows from the definition of R(X) while the second inequal­
ity follows from our assumptions on degX(Q) and degY (Q). On the other hand, if P (αi) = yi
then (8.7) implies that

Q(αi, yi) = Q(αi, P (αi)) = 0.

157

 


<!-- pdf-page: 170 -->
Thus, αi is a root of R(X).  In other words, R has at least t roots.  Note that the degree 
mantra (Proposition 5.1.5) this will lead to a contradiction if t > deg(R), which will be true 
if

t > ℓ +

n(k − 1)
ℓ

.

If we pick ℓ = √︁n(k − 1), we will have t > 2√︁n(k − 1).  Thus, we have shown that:

Theorem 8.2.5. Algorithm 8.2.1 can list decode Reed-Solomon codes of rate R from 1−2
fraction of errors.  Further, the algorithm can be implemented in polynomial time.

√

R

The claim on the efficient run time follows as Step 1 can be implemented by Gaussian 
elimination and for Step 3, all the factors of Q(X, Y ) (and in particular all linear factors of 
the form Y − P (X)) can be computed using e.g.  the algorithm from [43].

R is better than the unique decoding bound of  1−R

2  for R < 0.07. 
R fraction of errors guaranteed by the Johnson bound.  See 

√

The bound 1 − 2

√

This is still far from the 1 −
Figure 8.2.2 for an illustration.

Figure 8.3:  The tradeoff between rate R and the fraction of errors that can be corrected by 
Algorithm 8.2.1.

158

 


<!-- pdf-page: 171 -->
8.2.3  Algorithm 2

To motivate the next algorithm, recall that in Algorithm 8.2.1, in order to prove that the 
root finding step (Steps 3-6 in Algorithm 8.2.1) works, we defined a polynomial R(X) def=
Q(X, P (X)).  In particular, this implied that deg(R) ≤ degX(Q) + (k − 1) · degY (Q) (and 
we had to select t > degX(Q) + (k − 1) · degY (Q)).  One shortcoming of this approach is 
that the maximum degree of X and Y  might not occur in the same term.  For example, in 
the polynomial X 2Y 3 + X 4Y 2, the maximum X and Y  degrees do not occur in the same 
monomial.  The main insight in the new algorithm is to use a more “balanced” notion of 
degree of Q(X, Y ):

Definition 8.2.6. The (1, w) weighted degree of the monomial X iY j is i + wj.  Further, the 
(1, w)-weighted degree of Q(X, Y ) (or just its (1, w) degree) is the maximum (1, w) weighted 
degree of its monomials.

For example, the (1, 2)-degree of the polynomial XY 3 +X 4Y  is max(1+3·2, 4+2·1) = 7. 
Also note that the (1, 1)-degree of a bivariate polynomial Q(X, Y ) is its total degree (or the 
“usual” definition of degree of a bivariate polynomial).  Finally,  we will use the following 
simple lemma (whose proof we leave as an exercise):

Lemma 8.2.7. Let Q(X, Y ) be a bivariate polynomial of (1, w) degree D.  Let P (X) be a 
polynomial such that deg(P ) ≤ w.  Then we have

deg (Q(X, P (X))) ≤ D.

Note that a bivariate polynomial Q(X, Y ) of (1, w) degree at most D can be represented 

as follows:

where ci,j ∈ Fq.

Q(X, Y ) def=

∑︂

ci,jX iY j,

i+wj≤D
i,j≥0

The new algorithm is basically the same as Algorithm 8.2.1, except in the interpolation 
step, where we compute a bivariate polynomial of bounded (1, k − 1) degree. Before we state 
the precise algorithm, we will present the algorithm via an example.  Consider the received 
word in Figure 8.4.

Now we want to interpolate a bivariate polynomial Q(X, Y ) with a (1, 1) degree of 4
that “passes” through all the 2-D points corresponding to the received word from Figure 8.4. 
Figure 8.5 shows such an example.

Finally, we want to factorize all the linear factors Y − P (X) of the Q(X, Y ) from Fig­
ure 8.5.  Figure 8.6 shows the two polynomials X and −X such that Y − X and Y + X are 
factors of Q(X, Y ) from Figure 8.5.

We now precisely state the new list decoding algorithm in Algorithm 8.2.2. The algorithm 

description needs the following condition:

Q(αi, yi) = 0, 1 ≤ i ≤ n.

(8.8)

159



<!-- pdf-page: 172 -->
Figure 8.4:  An illustration of a received word for the [14, 2] Reed-Solomon code from Fig­
ure 8.1.1 (where again we have implicitly embedded the field Fq in the set {−7, . . . , 7}). Here 
we have considered e = 9 errors which is more than what Algorithm 8.1.1 can handle.  In 
this case, we are looking for lines that pass through at least 5 points.  By comparison for 
unique decoding, we would need t ≥ n+k
2 = 8, which is higher than the agreement of 
5 we want to handle with list decoding.

2 = 14+2

Proof of Correctness of Algorithm 8.2.2.  As in the case of Algorithm 8.2.1, to prove 
the correctness of Algorithm 8.2.2, we need to do the following:

• (Interpolation  Step)  Ensure  that  the  number  of  coefficients  of  Q(X, Y )  is  strictly 

greater than n.

• (Root Finding Step) Let R(X) def= Q(X, P (X)).  We want to show that if P (αi) ≥ yi

for at least t values of i, then R(X) ≡ 0.

To begin with, we argue why we can prove the correctness of the root finding step.  Note 

that since Q(X, Y ) has (1, k − 1) degree at most D, Lemma 8.2.7 implies that

deg(R) ≤ D.

Then using the same argument as we used for the correctness of the root finding step of 
Algorithm 8.2.1, we can ensure R(X) ≡ 0 if we pick

t > D.

Thus, we would like to pick D to be as small as possible.  On the other hand, Step 1 will 
need D to be large enough (so that the number of variables is more than the number of 

160



<!-- pdf-page: 173 -->
Figure 8.5:  An interpolating polynomial Q(X, Y ) for the received word in Figure 8.4.

Figure 8.6:  The two polynomials that need to be output are shown in blue.

161



<!-- pdf-page: 174 -->
Algorithm 8.2.2 The Second List Decoding Algorithm for Reed-Solomon Codes
Input: n ≥ k ≥ 1, D ≥ 1, e = n − t and n pairs {(αi, yi)}n
Output: (Possibly empty) list of polynomials P (X) of degree at most k − 1

i=1

1: Find a non-zero Q(X, Y ) with (1, k − 1) degree at most D, such that (8.8) is satisfied.
2: L ← ∅
3: for every factor Y − P (X) of Q(X, Y ) do
4:  
5:  
6: return L

i=1) ≤ e and deg(P ) ≤ k − 1 then

Add P (X) to L.

if ∆(y, (P (αi))n

constraints in (8.8).  Towards that end, let the number of coefficients of Q(X, Y ) be

N = ⃓
⃓
⌋︁, which 
To bound N , we first note that in the definition above, j ≤ ⌊︁ D
will be the list-size output by the algorithm. Consider the following sequence of relationships:

{︁(i, j)|i + (k − 1)j ≤ D, i, j ∈ Z+}︁⃓
⃓
⌋︁. Define L = ⌊︁ D

k−1

k−1

L
∑︂

D−(k−1)j
∑︂

1

N =

j=1

L
∑︂

j=0

L
∑︂

j=0

=

=

i=0

(D − (k − 1)j + 1)

(D + 1) − (k − 1)

L
∑︂
j

j=0

= (D + 1)(L + 1) −

(k − 1)L(L + 1)
2

(2D + 2 − (k − 1)L)

(D + 2)

=

≥

≥

)︃

L + 1
2
(︃ L + 1
2
D(D + 2)
2(k − 1)

.

(8.9)

(8.10)

In the above, (8.9) follows from the fact that L ≤ D

k−1 and (8.10) follows from the fact 

that  D

k−1 − 1 ≤ L.

Thus,  the  interpolation  step  succeeds  (i.e.  there  exists  a  non-zero  Q(X, Y )  with  the 

required properties) if

The choice

D(D + 2)
2(k − 1)

> n.

D =

⌈︂√︁2(k − 1)n

⌉︂

162



<!-- pdf-page: 175 -->
suffices by the following argument:

D(D + 2)
2(k − 1)

>

D2
2(k − 1)

≥

2(k − 1)n
2(k − 1)

= n.

Thus  for  the  root  finding  step  to  work,  we  need  t >
following result:

⌉︂
⌈︂√︁2(k − 1)n

,  which  implies  the 

√

Theorem  8.2.8.  Algorithm  2  can  list  decode  Reed-Solomon  codes  of  rate  R  from  up  to 
1 −
2R fraction of errors.  Further, the algorithm runs in polynomial time, and outputs a 
list of size at most O(1/

R).

√

Algorithm  2  runs  in  polynomial  time  as  Step  1  can  be  implemented  using  Gaussian 
elimination (and the fact that the number of coefficients is O(n)), while the root finding step 
can be implemented by any polynomial time algorithm to factorize bivariate polynomials. 
Further, we note that 1 −
2R beats the unique decoding bound of (1 − R)/2 for R < 1/3. 
See Figure 8.2.3 for an illustration. 

√

Figure 8.7:  The tradeoff between rate R and the fraction of errors that can be corrected by 
Algorithm 8.2.1 and Algorithm 8.2.2.

8.2.4  Algorithm 3

163

 


<!-- pdf-page: 176 -->
Finally, we present the list decoding algorithm for Reed-Solomon codes, which can correct 
√
1 −
R fraction of errors. The main idea is to add more restrictions on Q(X, Y ) (in addition 
to its (1, k − 1)-degree being at most D). In particular, the restriction is as follows: for some 
integer parameter r ≥ 1, we will insist on Q(X, Y ) having r roots at (αi, yi), 1 ≤ i ≤ n (we 
will come to the formal definition of this shortly).

This change will have the following implications:

1. The number of equations (on the coefficients of Q) will increase but the number of 
coefficients will remain the same.  This seems to be bad, as this results in an increase 
in D (which in turn would result in an increase in t).

2. However, this change also increases the number of roots of R(X) and this gain in the 

number of roots more than compensates for the increase in D.

To  motivate  the  definition  of  multiplicity  of  a  root  of  a  bivariate  polynomial,  let  us 

consider the following simplified examples. 

Figure 8.8:  Multiplicity of 1

In Figure 8.8 the curve Q(X, Y ) = Y − X passes through the origin once and has no 

term of degree 0.

In Figure 8.9, the curve Q(X, Y ) = (Y − X)(Y + X) passes through the origin twice and 

has no term with degree at most 1.

In Figure 8.10, the curve Q(X, Y ) = (Y − X)(Y + X)(Y − 2X) passes through the origin 
thrice and has no term with degree at most 2.  More generally, if r lines pass through the 
origin, then note that the curve corresponding to their product has no term with degree at 
most r − 1.  This leads to the following more general definition:

164



<!-- pdf-page: 177 -->
Figure 8.9:  Multiplicity of 2

Figure 8.10:  Multiplicity of 3

Definition 8.2.9. Q(X, Y ) has r roots at (0, 0) if Q(X, Y ) doesn’t have any monomial with 
degree at most r − 1.

The definition of a root with multiplicity r at a more general point follows from a simple 

translation:

Definition 8.2.10. Q(X, Y ) has r roots at (α, β) if Qα,β(X, Y ) def= Q(x + α, y + β) has r
roots at (0, 0).

165



<!-- pdf-page: 178 -->
Before we state the precise algorithm, we will present the algorithm with an example. 

Consider the received word in Figure 8.11. 

Figure 8.11:  An illustration of a received word for the [10, 2] Reed-Solomon code (where we 
have implicitly embedded the field Fq in the set {−9, . . . , 11}).  Here we have considered 
e = 6 errors,  which is more than what Algorithm 8.2.2 can decode.  In this case,  we are 
looking for lines that pass through at least 4 points.

Now we want to interpolate a bivariate polynomial Q(X, Y ) with (1, 1) degree 5 that 
“passes  twice”  through  all  the  2-D  points  corresponding  to  the  received  word  from  Fig­
ure 8.11.  Figure 8.12 shows such an example. 

Figure 8.12:  An interpolating polynomial Q(X, Y ) for the received word in Figure 8.11.

Finally, we want to factorize all the linear factors Y − P (X) of the Q(X, Y ) from Fig­

166



<!-- pdf-page: 179 -->
ure 8.12.  Figure 8.13 shows the five polynomials of degree one are factors of Q(X, Y ) from 
Figure 8.12. 

Figure 8.13:  The five polynomials that need to be output are shown in blue.

(In fact, Q(X, Y ) exactly decomposes into the five lines.)
Algorithm 8.2.3 formally states the algorithm.  The algorithm uses the following condi­

tion:

Q(αi, yi) = 0,  with multiplicity r for every 1 ≤ i ≤ n.

(8.11)

Algorithm 8.2.3 The Third List Decoding Algorithm for Reed-Solomon Codes
Input: n ≥ k ≥ 1, D ≥ 1, r ≥ 1, e = n − t and n pairs {(αi, yi)}n
Output: (Possibly empty) list of polynomials P (X) of degree at most k − 1

i=1

1: Find a non-zero Q(X, Y ) with (1, k − 1) degree at most D, such that (8.11) is satisfied.
2: L ← ∅
3: for every factor Y − P (X) of Q(X, Y ) do
4:  
5:  
6: return L

i=1) ≤ e and deg(P ) ≤ k − 1 then

Add P (X) to L.

if ∆(y, (P (αi))n

Correctness of Algorithm 8.2.3.  To prove the correctness of Algorithm 8.2.3, we will 
need the following two lemmas (we defer the proofs of the lemmas above to Section 8.2.4):
)︁ constraints for each i on the coeffi­
Lemma 8.2.11. The constraints in (8.11) imply (︁r+1
cients of Q(X, Y ).

2

Lemma 8.2.12. R(X) def= Q(X, P (X)) has r roots for every i such that P (αi) = yi. In other 
words, (X − αi)r divides R(X).

167



<!-- pdf-page: 180 -->
Using arguments similar to those used for proving the correctness of Algorithm 8.2.2, to 

argue the correctness of the interpolations step we will need

D(D + 2)
2(k − 1)

> n

(︃r + 1
2

)︃
,

where the LHS is an upper bound on the number of coefficients of Q(X, Y ) as before from 
(8.10) and the RHS follows from Lemma 8.2.11.  Note that the above is equiivalen to

which in turn is equiivalent to

D(D + 2)
(k − 1)

> n(r + 1)r,

D2 + 2D > n(k − 1)(r + 1)r.

We note that for the above to hold, the choice

D =

⌈︂√︁(k − 1)nr(r + 1)

⌉︂

works.  Thus, we have shown the correctness of Step 1.

For the correctness of the root finding step, we need to show that the number of roots 
of R(X) (which by Lemma 8.2.12 is at least rt) is strictly bigger than the degree of R(X), 
which from Lemma 8.2.7 is D.  That is we would be fine we if have,

which is the same as

which in turn will follow if we pick

tr > D,

t >

D
r

,

⌈︄√︄

(︃

t =

(k − 1)n

1 +

)︃⌉︄

.

1
r

If we pick r = 2(k − 1)n, then we will need

⌈︄√︃

t >

(k − 1)n +

⌉︄

.

1
2

The above is satisfied if we have t ≥
Thus, we have shown

√

kn (since we have for any n ≥ 1, −n + 1/2 < 0). 

√

Theorem 8.2.13. Algorithm 8.2.3 can list decode Reed-Solomon codes of rate R from up to 
1 −

R fraction of errors.  Further, the algorithm runs in polynomial time.

168



<!-- pdf-page: 181 -->
The claim on the run time follows from the same argument that was used to argue the 
polynomial running time of Algorithm 8.2.2. Thus, Theorem 8.2.13 shows that Reed-Solomon 
codes can be efficiently decoded up to the Johnson bound.  For an illustration of fraction of 
errors correctable by the three list decoding algorithms we have seen, see Figure 8.2.3.

A natural question to ask is if Reed-Solomon codes of rate R can be list decoded beyond 
√

R fraction of errors.  The answer is still not known:

1 −

Open  Question  8.2.14. Given a Reed-Solomon code of rate R,  can it be efficiently list 
decoded beyond 1 −

R fraction of errors?

√

Recall that to complete the proof of Theorem 8.2.13, we still need to prove Lemmas 8.2.11 

and 8.2.12, which we do next.

Proof of key lemmas

Proof of Lemma 8.2.11.   Let

Q(X, Y ) =

∑︂

ci,jX iY j

i,j
i+(k−1)j≤D

and

We will show that

Qα,β(X, Y ) = Q(X + α, Y + β) =

cα,β
i,j X iY j.

∑︂

i,j

i,j  are homogeneous linear combinations of ci,j’s.

(i) cα,β
(ii) If Qα,β(X, Y ) has no monomial with degree < r, then that implies (︁r+1

)︁ constraints 

2

on cα,β

i,j ’s.

Note that (i) and (ii) prove the lemma.  To prove (i), note that by the definition:

Qα,β(X, Y ) =

cα,β
i,j X iY j

∑︂

i,j

∑︂

=

ci′,j′(X + α)i′(Y + β)j′

i′,j′
i′+(k−1)j′≤D

(8.12)

(8.13)

Note that, if i > i′ or j > j′, then cα,β
X iY j from (8.12) and (8.13), we obtain

i,j  doesn’t depend on ci′,j′

.  By comparing coefficients of 

ci′,j′

(︃i′
i

)︃(︃j′
j

)︃

αi′−iβj′−j,

cα,β
i,j =

∑︂

i′>i
j′>j

169



<!-- pdf-page: 182 -->
which  proves  (i).  To  prove  (ii),  recall  that  by  definition  Qα,β(X, Y )  has  no  monomial  of 
degree < r.  In other words,  we need to have constraints cα,β
i,j = 0 if i + j ≤ r − 1.  The 
number of such constraints is

|{(i, j)|i + j ≤ r − 1, i, j ∈ Z≥0}| =

)︃

(︃r + 1
2

,

where the equality follows from the following argument.  Note that for every fixed value of 
0 ≤ j ≤ r − 1, i can take r − j values.  Thus, we have that the number of constraints is

r−1
∑︂

j=0

r − j =

r
∑︂

ℓ=1

ℓ =

)︃

(︃r + 1
2

,

as desired.

We now re-state Lemma 8.2.12 more precisely and then prove it.

Lemma 8.2.15. Let Q(X, Y ) be computed by Step 1 in Algorithm 8.2.3.  Let P (X) be a 
polynomial of degree ≤ k − 1, such that P (αi) = yi for at least t > D
r  many values of i, then 
Y − P (X) divides Q(X, Y ).

Proof. 

Define

R(X) def= Q(X, P (X)).

As usual, to prove the lemma, we will show that R(X) ≡ 0.  To do this, we will use the 
following claim.

Claim 8.2.16. If P (αi) = yi, then (X − αi)r divides R(X), that is αi is a root of R(X) with 
multiplicity r.

Note that by definition of Q(X, Y ) and P (X),  R(X) has degree ≤ D.  Assuming the 
above  claim  is  correct,  R(X)  has  at  least  t · r  roots.  Therefore,  by  the  degree  mantra 
(Proposition 5.1.5), R(X) is a zero polynomial as t · r > D. We will now prove Claim 8.2.16. 
Define

and

Pαi,yi(X) def= P (X + αi) − yi,

Rαi,yi(X) def= R(X + αi)

= Q(X + αi, P (X + αi))
= Q(X + αi, Pαi,yi(X) + yi)
= Qαi,yi(X, Pαi,yi(X)),

(8.14)

(8.15)
(8.16)
(8.17)
(8.18)

where (8.16), (8.17) and (8.18) follow from the definitions of R(X), Pαi,yi(X) and Qαi,yi(X, Y )
respectively.

170

 


<!-- pdf-page: 183 -->
By (8.15) if Rαi,yi(0) = 0, then R(αi) = 0. So, if X divides Rαi,yi(X), then X − αi divides 
R(X).  (This  follows  from  a  similar  argument  that  we  used  to  prove  Proposition  5.1.5.) 
Similarly, if X r divides Rαi,yi(X), then (X − αi)r divides R(X).  Thus, to prove the lemma, 
we will show that X r divides Rαi,yi(X).  Since P (αi) = yi when αi agrees with yi, we have 
Pαi,yi(0) = 0.  Therefore, X is a root of Pαi,yi(X), that is, Pαi,yi(X) = X · g(X) for some 
polynomial g(X) of degree at most k − 1.  We can rewrite

Rαi,yi(X) =

∑︂

i′,j′

i′,j′ X i′(Pαi,yi(X))j′ =
cαi,yi

i′,j′ X i′(Xg(X))j′.
cαi,yi

∑︂

i′,j′

Now for every i′, j′ such that cαi,yi
̸= 0, we have i′ + j′ ≥ r as Qαi,yi(X, Y ) has no monomial 
i′,j′
of degree < r.  Thus X r divides Rαi,yi(X), since Rαi,yi(x) has no non-zero monomial X ℓ for 
any ℓ < r.

8.3  Extensions

We  now  make  some  observations  about  Algorithm  8.2.3.  In  particular,  the  list  decoding 
algorithm is general enough to solve more general problems than just list decoding.  In this 
section, we present an overview of these extensions.

Recall that the constraint (8.11) states that Q(X, Y ) has r ≥ 0 roots at (αi, yi), 1 ≤ i ≤ n. 
However, our analysis did not explicitly use the fact that the multiplicity is same for every 
i.  In particular, given non-zero integer multiplicities wi ≥ 0, 1 ≤ i ≤ n, Algorithm 8.2.3 can 
be generalized to output all polynomials P (X) of degree at most k − 1, such that

∑︂

wi >

i:P (αi)=yi

⌜
⃓
⃓
⎷2(k − 1)

n
∑︂

i=1

)︃

(︃wi + 1
2

.

(8.19)

(We leave the proof as an exercise.) Note that till now we have seen the special case wi = r, 
1 ≤ i ≤ n.

Further, we claim that the αi’s need not be distinct for the all of the previous arguments 
to go through.  In particular, one can generalize Algorithm 8.2.3 even further to prove the 
following (the proof is left as an exercise):

Theorem 8.3.1. There is an algorithm that, given positive integer weights wi,α for every 
1 ≤ i ≤ n and α ∈ F, runs in time polynomial in n and ∑︁
i,α wi,α and outputs all polynomials 
P (X) of degree at most k − 1 such that

∑︂

i

wi,P (αi) >

⌜
⃓
⃓
⎷(k − 1)

n
∑︂

∑︂

i=1

α∈F

w2

i,α.

171

 


<!-- pdf-page: 184 -->
We leave the proof as an exercise.  (See Exercise 8.13.  The exercise also shows how the 
assumption that the weights are integers can be relaxed in exchange for a lesser order loss 
in the agreement parameter.)

The theorem above will be useful to solve the following generalization of list decoding 

called soft decoding.

Definition 8.3.2. Under soft decoding problem, the decoder is given as input a set of non-
negative weights wi,α(1 ≤ i ≤ n, α ∈ Fq) and a threshold W ≥ 0.  The soft decoder needs to 
output all codewords (c1, c2, . . . , cn) in q-ary code of block length n that satisfy:

n
∑︂

i=1

wi,ci ≥ W.

Note that Theorem 8.3.1 solves the soft decoding problem with

⌜
⃓
⃓
⎷(1 + ε)(k − 1)

W =

n
∑︂

∑︂

i=0

α∈F

w2

i,α ,

for every ε > 0.

Consider the following special case of soft decoding where wi,yi = 1 and wi,α = 0 for 
α ∈ F \ {yi} (1 ≤ i ≤ n).  Note  that  this  is  exactly  the  list  decoding  problem  with  the 
received  word  (y1, . . . , yn).  Thus,  list  decoding  is  indeed  a  special  case  of  soft  decoding. 
Soft decoding has practical applications in settings where the channel is analog.  In such a 
situation,  the “quantizer” might not be able to pinpoint a received symbol yi with 100%
accuracy.  Instead, it can use the weight wi,α to denote its confidence level that ith received 
symbol was α.

Finally, we consider a special case of soft decoding called list recovery, which has appli­

cations in designing list decoding algorithms for concatenated codes.

Definition 8.3.3   (List Recovery). Let C ⊆ Fn
q  be a code.  For parameters ε ∈ [0, 1] and 
integers 0 ≤ ℓ ≤ q and L we say that C is (ε, ℓ, L)-list recoverable if for all sequence of sets 
S1, . . . , Sn with |Si| ≤ ℓ for all i, there are at most L codewords c = (c1, . . . , cn) ∈ C satisfying 
|{i ∈ [n]|ci ∈ Si}| ≥ t := (1 − ε)n.  We say that C is (ε, ℓ, L)-efficiently-list recoverable if 
there is a polynomial time algorithm to find all such codewords.

We leave the proof that list recovery is a special case of soft decoding as an exercise. 
Finally, we claim that Theorem 8.3.1 implies the following result for list recovery (the proof 
is left as an exercise):

Theorem 8.3.4. For every k ≤ n ≤ q the [n, k]q Reed-Solomon code is ((1−√︁(k − 1)ℓ/n), ℓ, poly(n))-
efficiently list recoverable.

172



<!-- pdf-page: 185 -->
8.4  Exercises

Exercise 8.1. Recall from Exercise 5.9 that Reed-Solomon codes can be viewed alternatively 
as being obtained as the sequence of coefficients of univariate polynomials that are multiples 
of some fixed polynomial G(X) of degree n − k that has as roots α1, . . . , αn−k, where α is a 
primitive nth root of unity in Fq.  In this exercise we will describe Peterson’s algorithm for 
decoding such codes.

Let G(X) ∈ Fq[X] be a polynomial of degree n − k with roots α, α2, αℓ where α ∈ Fqs is 

some element in an extension field of order at least n.  Let

C = {(c0, . . . , cn−1) |  such that ∃M (X) ∈ F<k
q

[X]s.t.

n−1
∑︂

i=0

ciX i = M (X) · G(X)},

be the code containing the sequence of coefficients of multiples of G(X).  Let (c0, . . . , cn−1)
be a transmitted codeword and let C(X) = ∑︁n−1
i=0 ciX i.  Let (y0, . . . , yn−1) be a received word 
with yi = ci + zi.  Let T = {i|zi ̸= 0} be the set of error locations.  The key to Peterson’s 
algorithm are the following three polynomials:
Error-Locator Polynomial: E(X) = ∏︁
Error-Descriptor Polynomial: Γ(X) = ∑︁

i∈T (1 − αiX).
i∈T ziαi ∏︁

j∈T \{i}(1 − αjX).
s=1 Z(αs)X s−1 where Z(X) = ∑︁n−1

Syndrome Polynomial: S(X) = ∑︁ℓ
As the name suggests, the Error-Locator contains enough information to locate the errors and 
the Error-Descriptor contains information about the value of the errors, given the locations 
of the error.  The Syndrome Polynomial is so-called because by definition it depends only 
on the error and not the message.  Actually all three of the polynomials have this feature, 
but as we will see below, the Syndrome Polynomial can be easily computed from the received 
message,  and in turn it has enough information to allow for recovery of (proxies of) the 
Error-Locator and Error-Descriptor.

i=0 ziX i.

1. Using G(αj) = 0 for 1 ≤ j ≤ ℓ prove that Z(αj) = Y (αj) where Y (X) = ∑︁n−1
Conclude that S(X) can be computed in polynomial time from the received word.

i=0 yiX i. 

2. [The Key Equation:] Prove that E(X) · S(X) ≡ Γ(X) (mod X ℓ).

3. Using the fact that α has order at least n, prove that gcd(E(X), Γ(X)) = 1.

4. Prove that E(X) is invertible modulo X ℓ.

5. Using the two parts above, prove that if E1(X)·S(X) = Γ1(X) (mod X ℓ) and max{deg(E1)+

deg(Γ), deg(E) + deg(Γ1)} < ℓ} then E divides E1.

6. Using the above give a polynomial time algorithm to correct up to (ℓ − 1)/2 errors.

Hint:  Show how to compute an E1 of degree at most ℓ/2 and Γ1 of degree at most (ℓ − 1)/2 satisfying 
E1(X) · S(X) = Γ1(X) (mod X s).  Use the roots of E1 to locate a superset of the errors and erase 
those locations.  Apply erasure decoding to the remaining coordinates of the received word.

173



<!-- pdf-page: 186 -->
Exercise  8.2.  Notice  that  one  way  to  interpret  the  decoding  problem  above  is  that  we 
have access to the values of a “sparse” univariate polynomial (namely Z(X) and its values 
Z(α), . . . , Z(αℓ)) and we wish to recover the polynomial Z in its coefficient representation. 
Indeed the solution above can be generalized to solve this more general problem, as we see 
below.

Say that a polynomial Z(X) = ∑︁n−1

i=0 ∈ Fq[X] is t-sparse if at most t of its coefficients 

are non-zero.

1. Suppose ℓ ≥ 2t and α ∈ Fq has order at least n.  Prove that for every β1, . . . , βℓ there 
is at most one t-sparse polynomial Z of degree less than n such that Z(αi) = βi for 
every i.

2. In  this  part  you  will  show  how  to  recover  the  terms  (exponents  of  monomials  and 
coefficients) of Z in time polynomial in t by modifying the algorithm from the previous 
problem.  Define S(X) = ∑︁ℓ

i=1 Z(αi)X i−1.

(a) Suppose t = 1 and so Z(X) = c · αd.  Prove that S(X) ≡ cαd

1−αdX (mod X ℓ).

(b) Now let t be general and let Z(X) = ∑︁t

i=1 ciX di. Prove that S(X) ≡

(︂∑︁t

i=1

ciαdi
1−αdi X

)︂

(mod X ℓ).

(c) Using the fact that α has order at least n, conclude that there exist relatively prime 
polynomials Γ(X) and E(X) of degree at most t − 1 and t respectively with E(X)
being invertible modulo X ℓ such that S(X) ≡ Γ(X)

E(X) (mod X ℓ).

(d) Show  that  if  Γ1(X)  and  E1(X)  are  polynomials  of  degree  at  most  t − 1  and  t

respectively satisfying S(X) ≡ Γ1(X)

E1(X) (mod X ℓ), then E(X) divides E1(X).

(e) Using the conditions above, show how to compute polynomials Γ1(X) and E1(X)
of degree at most t − 1 and t respectively such that S(X) ≡ Γ1(X)
E1(X) (mod X ℓ) and 
E1(0) = 1.  Further show how to compute the coefficients c1, . . . , ct and exponents 
d1, . . . , dt of Z(X).

Conclude that given a degree bound n and a sparsity bound t with n < q, there exist 2t
points α1, . . . , α2t in Fq such that the evaluations of a t-sparse degree n polynomial Z(X) on 
these 2t points uniquely specify Z and Z can be efficiently recovered from these evaluations.

Exercise 8.3. 

For a finite field Fqm, recall the Trace map Tr as follows:  for x ∈ Fqm

Tr(x) = x + xq + xq2 + · · · + xqm−1 .

(See Appendix B.5.5 for properties of this map.)

174



<!-- pdf-page: 187 -->
1. Let C ⊆ Fn

qm be a linear code, and C ⊥ ⊆ Fn

qm its dual.  Define C|Fq = C ∩ Fn

q  to be the 

subfield subcode of C.

Prove that

(C|Fq )⊥ = Tr(C ⊥)

where Tr(C ⊥) = {Tr(c) | c ∈ C ⊥}.

Hint:  Prove both the inclusions, starting with the easier inclusion Tr(C ⊥) ⊆ (C|Fq )⊥.  For the harder 
direction, use the fact that to prove A ⊆ B it suffices to prove that for every a ∈ A and b ∈ B⊥, 
⟨a, b⟩ = 0.

2. Show that

and

dim(C) ≤ dim(Tr(C)) ≤ m · dim(C) ,

dim(C) − (m − 1)(n − dim(C)) ≤ dim(C|Fq ) ≤ dim(C) ,
where for a linear space X ⊆ Fn, dim(X) stands for its dimension as a F-vector space.

Exercise 8.4. 

In  this  problem,  you  will  prove  that  the  following  “ultimate”  form  of  Reed-Solomon 

decoding is NP-hard over exponentially large fields.

Reed-Solomon Bounded Distance Decoding (Decision) Problem  Consider the 

following problem:

• Input:  Code Parameters:  Fq, (α1, . . . , αn) ∈ Fn

q  and k.  Received word:  y ∈ Fn

q  and 

error parameter t.

• Output:  Yes if there exists P (X) ∈ Fq[X] of degree less than k such that e := |{i ∈

[n] | yi ̸= P (αi)}| ≤ t and No otherwise.

You may assume that the following problem is NP-hard.  Finite Field Subset Sum: 

Consider the following problem:

• Input:  A set S = {γ1, . . . , γn} ⊆ F2m, an element β ∈ F2m, and an integer 1 ≤ k < n.

• Output:  Is there a nonempty subset  T ⊆ {1, 2, . . . , n} with |T | = k + 1 such that 

∑︁

i∈T γi = β?

Hint:  Use  q = 2m,  αi = γi  and  t = n − k − 1.  Define  y ∈ (F2m)n  as  follows:  yi = αk+1
i = 1, 2, . . . , n.

i − βαk

i   for 

Exercise 8.5. Using the previous problem prove that the Minimum Distance Problem (defined 
below) is NP-hard over exponentially large fields.

Minimum Distance (Decision) Problem  Consider the following problem:

175



<!-- pdf-page: 188 -->
• Input:  Fq, G ∈ Fk×n

q

, d ∈ Z+

• Output:  Yes  if  there  exists  a  non-zero  codeword  of  weight  at  most  d  in  the  code 

generated by G (i.e., x ∈ Fk

q  such that 0 < wt(xG) ≤ d) and No otherwise.

Hint:  Use the code generated by the Reed-Solomon code from the previous exercise and the vector y.  Prove 
that the new code has distance n−k −1 if and only if y is at distance at most n−k −1 from the Reed-Solomon 
code.

Exercise 8.6. In this problem we introduce the list-recovery problem for Reed-Solomon codes. 
Your task is to show that this problem is solved by adapting one of the list-decoding algorithms.

List Recovery Problem (for RS codes)  Consider the following problem:
• Input: Code Parameters: Fq, (α1, . . . , αn) ∈ Fn

q  and k. Error parameters e, ℓ. Received 

lists:  S1, . . . , Sn with Si ⊆ Fq, |Si| ≤ ℓ.

• Output:  A  list  of  all  polynomials  P (X) ∈ Fq[X]  of  degree  less  than  k  such  that 

|{i ∈ [n] | P (αi) /∈ Si}| ≤ e.

Adapt Algorithm 8.2.3 (the algorithm that decodes Reed-Solomon codes up to the Johnson 
bound) to show that List Recovery Problem for Reed-Solomon codes can be solved in polynomial 
time provided e < n −
nℓk.  In particular, if e = 0, conclude that the list-recovery problem 
can be solved efficiently if ℓ < n/k.

√

Exercise 8.7. In this exercise, you will show that the list recovery guarantee achieved by the 
above algorithm is tight when e = 0, in the sense that when ℓ = ⌈ n
k ⌉, there are settings where 
there are super-polynomially many (i.e., nω(1)) polynomials in the output list.

Let r be a fixed prime power.  Let n = q = rm and k = rm−1

r−1 .  Prove that there are at 
 polynomials f ∈ Fq[X]≤k such that f (a) ∈ Fr for every a ∈ Fq.  Deduce that the 

least r2m
Reed-Solomon list recovery algorithm cannot be improved to work for ℓ = ⌈ n

k ⌉ in general.

rm−1
r−1  always belongs to the subfield Fr (why?). So the polynomials fβ(X) := (X +β)

Hint: For x ∈ Frm, x
for β ∈ Frm  take values in Fr on evaluation points in Frm.  Show that the set {fβ}β∈{α0,...,αk−1} includes 2m
linearly independent polynomials over Fr.  You may find it useful to note, using Lucas’s theorem, that there 
)︁
are 2m values of index ℓ ∈ {0, . . . , k − 1} such that 

 is non-zero in Fr. 

rm−1
r−1

(︁k
ℓ

Remark:  Note  that  the  set  of  list  of  polynomials  that  we  are  using  in  this  exercise  are 
Fr-subfield subcodes of Reed-Solomon codes, also known as BCH codes — see Exercise 5.11. 
What you are proving is thus a lower bound on the dimension of BCH codes.  Note further 
that this is a regime of parameters where the lower bound proved in Exercise 5.11 is trivial 
thus necessitating a new analysis.

Exercise 8.8. In this exercise we prove that there exist some bad configurations for list-
decoding Reed-Solomon codes when errors exceed half the minimum distance.

Fix an [n, k, d]q code C.

176



<!-- pdf-page: 189 -->
1. For every integer e prove that the expected number of codewords of C in a uniformly 
)︁(q − 1)e · qk−n.

chosen ball of radius e is at least (︁n

e

2. Prove  that  if  k = n − nε  and  C  is  an  [n, k, d]n-Reed-Solomon  code,  then  there  is 
2(1−ε) that has exp(nε) codewords.  Conclude that for high-rate Reed-
a ball of radius 
Solomon codes, list-decoding from strictly more than half the minimum-distance requires 
exponential sized lists.

d

Exercise 8.9. 

In this exercise, we will explore some “bad list-decoding configurations” for Reed-Solomon 
codes, namely a center of a Hamming ball of bounded radius (in fact, close to the Johnson 
radius) that contains many codewords.  For this, we first need to develop some machinery 
related to linearized and subspace polynomials.

In this exercise we let q = ps be a prime power.  (We won’t need that p itself is a prime, 
though  that  would  be  a  valid  choice.)  We  say  that  a  set  P ⊆ Fq[X]  of  polynomials  is  a 
(k, b, t)-nice-family if there exists a set S with |S| ≤ b such that every polynomial P ∈ P is 
(1) supported on the monomials {x0, . . . , xk−1} ∪ {xi|i ∈ S}, and (2) has at least t zeroes in 
Fq.

1. Prove that if P is a (k, b, t)-nice-family then there exists a Hamming ball of radius n − t
q containing at least |P|/qb codewords of RSq[Fq, k], i.e., the Reed-Solomon code of 

in Fq
dimension k over Fq obtained by evaluating degree k − 1 polynomials at all of Fq.

To construct nice families we will use polynomials that vanish on Fp-subspaces of Fq.  The 
next few parts show that such polynomials are “linearized” polynomials and thus are sparse.
α∈S(X − α).  Recall that V ⊆ Fq is an Fp-subspace is for all 
α ∈ Fp and β, γ ∈ V  we have αβ, β + γ ∈ V .  The following parts show that if V  is an Fp
subspace then ZV (X) is a linearized polynomial.

For S ⊆ Fq let ZS(X) = ∏︁

2. Prove that for every α ∈ V  and β ∈ Fq, ZV (α + β) = ZV (β).

3. Let QV (X, Y ) := ZV (X + Y ) − ZV (X) − ZV (Y ).  Using the previous part prove that 

QV (α, β) = QV (β, α) = 0 for every α ∈ V  and β ∈ Fq.

4. Prove that deg(QV (X, Y )) < |V |.  Conclude that ZV (X + Y ) = ZV (X) + ZV (Y ).

5. Prove that for every α ∈ Fp, ZV (αZ) = αZV (X).

6. Use the above to conclude that ZV (X) is a linearized polynomial, i.e., it is of the form 

∑︁logp |V |
i=0

ciX pi

.

We now return to the task of constructing a nice family.

7. Prove that the number of Fp subspaces in Fq of dimension v is at least pv(s−v).

8. Let P = {ZV (X)|V  is an Fp-subspace of Fq, dim(V ) = v}.  Prove that for every integer 

a with 0 ≤ a ≤ v, P is a (pa, v − a, pv)-nice family.

177



<!-- pdf-page: 190 -->
9. Set  parameters  so  as  to  prove  the  following:  For  every  δ > 0  and  c < ∞  there 
exists R > 0 and infinitely many choices of N  for which there exists a ball of radius 
N − R 1
2 +δN  that contains Ω(N c) codewords of an [N, RN ]N  RS code.  For every δ > 0, 
conclude that there is no polynomial time algorithm to decode from 1 − R 1
2 +δ fraction 
errors from every Reed-Solomon code of rate R.

Exercise  8.10. A Kakeya set in Fn
q  such that K contains a line in 
q  there exists a point x ∈ Fn
every direction.  Formally, K is a Kakeya set if for every y ∈ Fn
q
such that the line {x + a · y mod a ∈ Fq} ⊆ K.  In this exercise you will use the polynomial 
method to prove that size of any Kakeya set K must satisfy |K| ≥ (︁q+n−2

q  is a subset K ⊆ Fn

)︁.

n−1

1. Prove that for any set K with |K| < (︁d+n−1
P  such that P (a) = 0 for every a ∈ K.

n−1

)︁ there is a homogeneous degree d polynomial 

2. For every x ∈ Fn

q  and y ∈ Fn

q \ {0} prove that on the line ℓ = ℓx,y := {x + t · y | t ∈ Fq}, 
the  restriction  of  a  homogeneous  degree  d  polynomial  P   to  the  line  ℓ  has  the  form 
Pℓ(t) = P (y) · td + gx,y(t) where deg(gx,y) < d.

3. If a set K contains a line ℓx,y and P  is a homogeneous degree d polynomial with d < q

that is zero on K, then prove that P (y) = 0.

4. Conclude that if |K| < (︁q+n−2

)︁ then K can not be a Kakeya set.

n−1

Exercise 8.11. One can define a number-theoretic counterpart of Reed-Solomon codes, called 
Chinese Remainder codes, as follows.  Let 1 ≤ k < n be integers and let p1 < p2 < · · · < pn
i=1 pi and N = ∏︁n
be n distinct primes.  Denote K = ∏︁k
i=1 pi.  The notation ZM  stands for 
integers modulo M , i.e., the set {0, 1, . . . , M − 1}.  Consider the Chinese Remainder code 
defined by the encoding map E : ZK → Zp1 × Zp2 × · · · × Zpn defined by:

E(m) = (m mod p1, m mod p2, · · · , m mod pn) .

(Note that this is not a code in the usual sense we have been studying since the symbols 
at different positions belong to different alphabets.  Still notions such as distance of this code 
make sense and are studied in the questions below.)

1. Suppose  that  m1 ̸= m2.  For  1 ≤ i ≤ n,  define  the  indicator  variable  bi = 1  if 

E(m1)i ̸= E(m2)i and bi = 0 otherwise.  Prove that ∏︁n
Use the above to deduce that when m1 ̸= m2, the encodings E(m1) and E(m2) differ in 
at least n − k + 1 locations.

i > N /K.

i=1 pbi

2. This exercise examines how the idea behind the Welch-Berlekamp decoder can be used 

to decode these codes.
Suppose r = (r1, r2, . . . , rn) is the received word where ri ∈ Zpi.  By Part (a), we know 
there can be at most one m ∈ ZK such that

178



<!-- pdf-page: 191 -->
∏︂

i ≤ √︁N /K .
pbi

i:E(m)i̸=ri

(8.20)

(Be sure you see why this is the case.)  The exercises below develop a method to find 
the unique such m, assuming one exists.
In what follows, let r be the unique integer in ZN  such that r mod pi = ri for every 
i = 1, 2, . . . , n (note that the Chinese Remainder theorem guarantees that there is a 
unique such r).

√

(a) Assuming an m satisfying (8.20) exists, prove that there exist integers y, z with 
N K and 1 ≤ z ≤ √︁N /K such that y ≡ rz (mod N ).
(b) Prove also that if y, z are any integers satisfying the above conditions,  then in 

0 ≤ y <

fact m = y/z.

(Remark: A pair of integers (y, z) satisfying above can be found by solving the integer 
linear program with integer variables y, z, t and linear constraints:  0 < z ≤ √︁N /K; 
N K. This is an integer program in a fixed number of dimensions 
and 0 ≤ z·r−t·N <
and can be solved in polynomial time.  Faster, easier methods are also known for this 
special problem.)

√

3. Instead of condition (8.20) what if we want to decode under the more natural condition 
for Hamming metric, that is |{i : E(m)i ̸= ri}| ≤ n−k
2 ?  Using ideas similar to GMD 
decoding, show how this can be done by calling the above decoder many times, by erasing 
the last i symbols for each choice of 1 ≤ i ≤ n.

Exercise 8.12. 

In  this  problem,  we  develop  a  more  abstract  view  of  the  Reed-Solomon  decoding  al­
gorithm.  This  enables  extending  the  apprpach  to  other  Reed-Solomon-like  codes,  such  as 
algebraic-geometric codes (and also encompasses the algorithm for the Chinese Remainder 
codes described above).

First  we  give  some  definitions.  Let  F  be  a  field.  For  u, v ∈ Fn,  define  u ∗ v =
(u1v1, u2v2, . . . , unvn) ∈ Fn be the component-wise product.  For U, V ⊆ Fn, define U ∗ V =
{u ∗ v | u ∈ U, v ∈ V }.

The idea of the abstract decoding procedure is that given a code C capable of correcting 
e errors (i.e., its distance exceeds 2e) that we want to decode, we construct an error-locator 
code  E,  such  that  E ∗ C  is  contained  in  another  linear  code  N   that  has  large  distance. 
Specifically, we want codes E and N  to have the following properties:

• dim(E) > e.

• E ∗ C ⊆ N .

• dist(N ) > e.

179



<!-- pdf-page: 192 -->
• dist(C) > n − dist(E)

Consider the following decoding algorithm for C.  Given as input r ∈ Fn with Hamming 

distance at most e from some codeword c ∈ C, the goal of the algorithm is to find c.

Step 1: Find a ∈ E and b ∈ N , a ̸= 0, such that a ∗ r = b.

Step 2: For each i, if ai = 0, set si =?, and oherwise set si = ri.  Perform erasure decoding 
(for the code C) on the resulting vector s, to find a c ∈ C such that ci = si whenever 
si ̸=?.

Output c.

The exercises below justify the algorithm, proving its efficiency and correctness.  Again, 
we assume that the input r ∈ Fn satisfies the property that there is a c ∈ C with ∆(r, c) ≤ e
(such a c is then unique, due to the assumed e-error correction property of C).

1. Prove that a, b as in Step 1 exist.

2. Prove that the algorithm can be implemented in polynomial time, given generator ma­

trices of C, N, E.

3. Prove that for every (a, b) satisying the condition of Step 1, a ∗ c = b.

4. Prove that if a ∗ c′ = b for some c′ ∈ C, then c′ = c.

5. Conclude the correctness of the algorithm.

6. If C is an [n, n − 2e] Reed-Solomon code, what are E and N  in the above abstraction 

that correspond to the Welch-Berlekamp algorithm covered in lecture?

Exercise 8.13. In this exercise we prove Theorem 8.3.1.

1. Give an algorithm that takes as input positive integer weights wi,α for every 1 ≤ i ≤ n
i,α wi,α and outputs all polynomials 

and α ∈ F, runs in time polynomial in n and ∑︁
P (X) of degree at most k − 1 such that

∑︂

i

wi,P (αi) >

⌜
⃓
⃓
⎷(k − 1)

n
∑︂

∑︂

i=0

α∈F

w2

i,α.

Hint:  Scale the weights wi by a sufficiently large polynomial in n and ∑︁
Eq. (8.19) implies the bound above.

i,α wi,α so that the bound in 

180



<!-- pdf-page: 193 -->
2. Give an algorithm that takes as input ε > 0 and positive (real) weights wi,α for every 
1 ≤ i ≤ n and α ∈ F, runs in time polynomial in n and 1/ε and outputs all polynomials 
P (X) of degree at most k − 1 such that

∑︂

i

wi,P (αi) > (1 + ε) ·

⌜
⃓
⃓
⎷(k − 1)

n
∑︂

∑︂

i=0

α∈F

w2

i,α.

Hint:  Scale the weights and then round them down to integers bounded by poly(n/ε) and then apply 
Part (1). 

8.5  Bibliographic Notes

The first polynomial time algorithm for decoding certain families of Reed-Solomon codes is 
essentially due to Peterson [59].  (Note that this algorithm was discovered in 1960, before 
polynomial  time  complexity  was  even  proposed  as  the  standard  notion  of  efficiency  and 
remains one of the most sophisticated polynomial time algorithms to this day.)  Peterson’s 
algorithm was presented only for decoding binary cyclic BCH codes. It was soon extended to 
cover cyclic BCH codes over general fields, which include classes of Reed-Solomon codes, by 
Gorenstein and Zierler [29].  These lead to the algorithm developed in Exercise 8.1.  A faster 
implementation of this algorithm was later  developed by Berlekamp [7] and  Massey [52]. 
All of these algorithms works for the alternate view of Reed-Solomon codes via polynomial 
multiplication as described in Exercise 5.9.  The algorithm working for all Reed-Solomon 
codes described in Section 8.1 is due to Welch and Berlekamp [75] with the exposition based 
on that of Gemmell and Sudan [26].  Algorithm 8.2.2, the list-decoding algorithm for Reed-
Solomon codes from Section 8.2 is due to Sudan [70].  Algorithm 8.2.3 from Section 8.2.4 is 
due to Guruswami and Sudan [33].

Exercise 8.2 is based on the work of Ben-Or and Tiwari.  (The specific formulation used 
here is based on an exposition of Kumar [46].) Exercises 8.4 and 8.5 are based on the work of 
Guruswami and Vardy [34]. Exercise 8.7 is based on the work of Guruswami and Rudra [31]. 
Exercise 8.8 is based on the works of Justesen and Høholdt [42] and Dumer, Micciancio and 
Sudan [18].  Exercise 8.9 is from the work of Ben-Sasson, Kopparty and Radhakrishnan [6]. 
Exercise  8.10  is  based  on  the  work  of  Dvir  [21].  Exercise  8.11  is  based  on  the  work  of 
Mandelbaum  [50].  Exercise  8.12  is  based  on  the  works  of  Duursma  and  Kötter  [20]  and 
Pellikaan [57].

181



<!-- pdf-page: 194 -->
182



<!-- pdf-page: 195 -->
Bibliography

[1] Manindra  Agrawal,  Neeraj  Kayal,  and  Nitin  Saxena.   PRIMES  Is  in  P.   Annals  of 

Mathematics, 160(2):781–793, 2004.

[2] Noga Alon and Joel Spencer.  The Probabilistic Method.  John Wiley, 1992.

[3] M. Artin.  Algebra.  Prentice-Hall Of India Pvt. Limited, 1996.

[4] John Bather.  A conversation with herman chernoff.  Statistical Science, 11(4):335–350, 

1996.

[5] Mihir  Bellare,  Oded  Goldreich,  and  Madhu  Sudan.    Free  bits,  pcps,  and 
nonapproximability-towards tight results.  SIAM J. Comput., 27(3):804–915, 1998.

[6] Eli  Ben-Sasson,  Swastik  Kopparty,  and  Jaikumar  Radhakrishnan.   Subspace  polyno­
mials  and  limits  to  list  decoding  of  reed-solomon  codes.   IEEE  Trans.  Inf.  Theory, 
56(1):113–120, 2010.

[7] Elwyn R. Berlekamp.  Algberaic Coding Theory.  McGraw-Hill, New York, NY, 1968.

[8] E.  L.  Blokh  and  V.  V.  Zyablov.   Coding  of  generalized  concatenated  codes.   Probl. 
Peredachi  Inf.,  10(3):45–50,  1974.    English  Translation  in  Problems  of  Information 
Transmission, 10:3(218–222), 1974.

[9] R. C. Bose and D. K. Ray-Chaudhuri.  On a class of error correcting binary group codes. 

Information and Control, 3:68–79, 1960.

[10] P.S. Bullen.  Handbook of Means and Their Inequalities.  Mathematics and Its Applica­

tions. Springer Netherlands, 2010.

[11] Donald G. Chandler,  Eric P. Batterman,  and Govind Shah.  Hexagonal,  information 
encoding article, process and system.  US Patent Number 4,874,936, October 1989.

[12] C. L. Chen and M. Y. Hsiao.  Error-correcting codes for semiconductor memory ap­
plications:  A  state-of-the-art  review.    IBM  Journal  of  Research  and  Development, 
28(2):124–134, 1984.

183



<!-- pdf-page: 196 -->
[13] Peter M. Chen, Edward K. Lee, Garth A. Gibson, Randy H. Katz, and David A. Pat­
terson.  RAID: High-performance, reliable secondary storage.  ACM Computing Surveys, 
26(2):145–185, 1994.

[14] Herman Chernoff.  A measure of asymptotic efficiency for tests of a hypothesis based on 
the sum of observations.  Annals of Mathematical Statistics, 23(4):493–507, December 
1952.

[15] Thomas M. Cover and Joy A. Thomas.  Elements of Information Theory.  John Wiley 

& Sons, Inc., second edition edition, 2005.

[16] Richard A. DeMillo and Richard J. Lipton.  A probabilistic remark on algebraic program 

testing.  Inform. Process. Lett., 7(4):193–195, 1978.

[17] Devdatt  P.  Dubhashi  and  Alessandro  Panconesi.   Concentration  of  Measure  for  the 

Analysis of Randomized Algorithms.  Cambridge University Press, 2009.

[18] Ilya Dumer,  Daniele Micciancio,  and Madhu Sudan.  Hardness of approximating the 
minimum  distance  of  a  linear  code.   IEEE  Trans.  Information  Theory,  49(1):22–37, 
2003.

[19] Ilya I. Dumer.  Concatenated codes and their multilevel generalizations.  In V. S. Pless 
and W. C. Huffman, editors, Handbook of Coding Theory, volume 2, pages 1911–1988. 
North Holland, 1998.

[20] Iwan M. Duursma and Ralf Kötter.  Error-locating pairs for cyclic codes.  IEEE Trans. 

Inf. Theory, 40(4):1108–1121, 1994.

[21] Zeev Dvir.  On the size of Kakeya sets in finite fields.  Journal of the American Mathe­

matical Society, 22:1093–1097, 2009.

[22] Todd Ebert, Wolfgang Merkle, and Heribert Vollmer.  On the autoreducibility of random 

sequences.  SIAM J. Comput., 32(6):1542–1569, 2003.

[23] Peter Elias.  Coding for two noisy channels.  In Cherry, editor, Informtion Theory, pages 

61–74. Butterworth, 1956.

[24] Paul Erdös.  Some remarks on the theory of graphs.  Bulletin of the American Mathe­

matical Society, 53:292–294, 1947.

[25] G. David Forney.  Concatenated Codes.  MIT Press, Cambridge, MA, 1966.

[26] Peter Gemmell and Madhu Sudan.  Highly resilient correctors for multivariate polyno­

mials.  Information Processing Letters, 43(4):169–174, 1992.

[27] E. N. Gilbert.  A comparison of signalling alphabets.  Bell System Technical Journal, 

31:504–522, 1952.

184



<!-- pdf-page: 197 -->
[28] M. J. E. Golay.  Notes on digital coding.  Proceedings of the IRE, 37:657, 1949.

[29] Daniel Gorenstein and Neal Zierler.  A class of error-correcting codes in pm symbols. 
Journal of the Society for Industrial and Applied Mathematics, 9(2):207–214, 1961.

[30] Venkatesan  Guruswami  and  Swastik  Kopparty.    Explicit  subspace  designs.   Comb., 

36(2):161–185, 2016.

[31] Venkatesan Guruswami and Atri Rudra.  Limits to list decoding reed-solomon codes. 

IEEE Transactions on Information Theory, 52(8):3642–3649, August 2006.

[32] Venkatesan Guruswami and Atri Rudra.  Explicit codes achieving list decoding capacity: 
Error-correction with optimal redundancy.  IEEE  Trans.  Inf.  Theory,  54(1):135–150, 
2008.

[33] Venkatesan Guruswami and Madhu Sudan.  Improved decoding of Reed-Solomon and 
algebraic-geometry codes.  IEEE Transactions on Information Theory, 45(6):1757–1767, 
1999.

[34] Venkatesan Guruswami and Alexander Vardy.  Maximum-likelihood decoding of reed-

solomon codes is np-hard.  IEEE Trans. Information Theory, 51(7):2249–2256, 2005.

[35] Richard  W.  Hamming.   Error  Detecting  and  Error  Correcting  Codes.   Bell  System 

Technical Journal, 29:147–160, April 1950.

[36] A. Hocquenghem.  Codes correcteurs d’erreurs.  Chiffres (Paris), 2:147–156, 1959.

[37] Tom  Hholdt,  J.  H.  van  Lint,  and  Ruud  Pellikaan.    Algebraic  geometry  codes.    In 
W.  C.  Huffamn  V.  S.  Pless  and  R.  A.Brualdi,  editors,  Handbook  of  Coding  Theory. 
North Holland, 1998.

[38] Tao  Jiang  and  Alexander  Vardy.   Asymptotic  improvement  of  the  gilbert-varshamov 
bound on the size of binary codes.  IEEE Trans. Inf. Theory, 50(8):1655–1664, 2004.

[39] D.  D.  Joshi.   A  note  on  upper  bounds  for  minimum  distance  codes.   Inf.  Control., 

1(3):289–295, 1958.

[40] E. J. Weldon Jr.  Justesen’s construction-the low-rate case (corresp.).  IEEE Trans. Inf. 

Theory, 19(5):711–713, 1973.

[41] J. Justesen.  Class of constructive asymptotically good algebraic codes.  IEEE Trans. 

Inform. Theory, pages 652–656, Sep 1972.

[42] Jørn Justesen and Tom Høholdt.  Bounds on list decoding of MDS codes.  IEEE Trans. 

Inf. Theory, 47(4):1604–1609, 2001.

[43] Erich  Kaltofen.   Polynomial-time  reductions  from  multivariate  to  bi-  and  univariate 

integral polynomial factorization.  SIAM J. Comput., 14(2):469–489, 1985.

185



<!-- pdf-page: 198 -->
[44] Swastik  Kopparty,  Shubhangi  Saraf,  and  Sergey  Yekhanin.    High-rate  codes  with 

sublinear-time decoding.  J. ACM, 61(5):28:1–28:20, 2014.

[45] Victor Yu. Krachkovsky.  Reed-solomon codes for correcting phased error bursts.  IEEE 

Trans. Inf. Theory, 49(11):2975–2984, 2003.

[46] Mrinal Kumar.  Personal Communication, May 2024.

[47] Rudolf Lidl and Harald Niederreiter.  Introduction to Finite Fields and their applications. 

Cambridge University Press, Cambridge, MA, 1986.

[48] Florence Jessie MacWilliams.  A theorem on the distribution of weights in a systematic 

code.  Bell Systems Technical Journal, 42:79–94, 1963.

[49] David  Mandelbaum.   Error  correction  in  residue  arithmetic.   IEEE  Transactions  on 

Computers, C-21(6):538–545, 1972.

[50] David  M.  Mandelbaum.    On  a  class  of  arithmetic  codes  and  a  decoding  algorithm 

(corresp.).  IEEE Trans. Inf. Theory, 22(1):85–88, 1976.

[51] James L. Massey.  Threshold Decoding.  MIT Press, Cambridge, MA, USA, 1963.  129 

pages.

[52] James L. Massey.  Shift-register synthesis and BCH decoding.  IEEE Trans. Inf. Theory, 

15(1):122–127, 1969.

[53] Michael Mitzenmacher and Eli Upfal.  Probability and Computing:  Randomized Algo­

rithms and Probabilistic Analysis.  Cambridge University Press, 2005.

[54] Rajeev Motwani and Prabhakar Raghavan.  Randomized Algorithms.  Cambridge Uni­

versity Press, 1995.

[55] David E. Muller.  Application of boolean algebra to switching circuit design and to error 

detection.  Trans. I.R.E. Prof. Group on Electronic Computers, 3(3):6–12, 1954.

[56] Øystein Ore.  Über höhere kongruenzen (German) [About higher congruences].  Norsk 

Mat. Forenings Skrifter, 1(7):15, 1922.  (see [?, Theorem 6.13]).

[57] Ruud Pellikaan.  On decoding by error location and dependent sets of error positions. 

Discret. Math., 106-107:369–381, 1992.

[58] Larry  L.  Peterson  and  Bruce  S.  Davis.   Computer  Networks:  A  Systems  Approach. 

Morgan Kaufmann Publishers, San Francisco, 1996.

[59] W.  Wesley  Peterson.   Encoding  and  error-correction  procedures  for  Bose-Chaudhuri 

codes.  IEEE Transactions on Information Theory, 6:459–470, 1960.

186



<!-- pdf-page: 199 -->
[60] I. Reed.  A class of multiple-error-correcting codes and the decoding scheme.  Transac­

tions of the IRE Professional Group on Information Theory, 4(4):38–49, 1954.

[61] Irving S. Reed and Gustav Solomon.  Polynomial codes over certain finite fields.  SIAM 

Journal on Applied Mathematics, 8(2):300–304, 1960.

[62] Herbert  Robbins.   A  remark  on  Stirling’s  formula.   Amer.  Math.  Monthly,  62:26–29, 

1955.

[63] M. Yu. Rosenbloom and M. A. Tsfasman.  Codes for the m-metric.  Problemy Peredachi 

Informatsii, 33(1):55–63, 1997.

[64] Jacob T. Schwartz.  Fast probabilistic algorithms for verification of polynomial identities. 

J. ACM, 27(4):701–717, October 1980.

[65] Claude E. Shannon.  A mathematical theory of communication.  Bell System Technical 

Journal, 27:379–423, 623–656, 1948.

[66] Victor  Shoup.   New  algorithms  for  finding  irreducible  polynomials  over  finite  fields. 

Math. Comp., 54:435–447, 1990.

[67] Victor Shoup.  A computational introduction to number theory and algebra.  Cambridge 

University Press, 2006.

[68] R. Singleton.  Maximum distance q -nary codes.  Information Theory, IEEE Transactions 

on, 10(2):116 – 118, apr 1964.

[69] David Slepian.  A class of binary signaling alphabets.  The Bell System Technical Journal, 

35(1):203–234, 1956.

[70] Madhu Sudan.  Decoding of Reed Solomon codes beyond the error-correction bound.  J. 

Complexity, 13(1):180–193, 1997.

[71] Aimo  Tietavainen.   On  the  nonexistence  theorems  for  perfect  error-correcting  codes. 

SIAM Journal of Applied Mathematics, 24(1):88–96, 1973.

[72] Jacobus  H.  van  Lint.   Nonexistence  theorems  for  perfect  error-correcting  codes.   In 
Proceedings  of  the  Symposium  on  Computers  in  Algebra  and  Number  Theory,  pages 
89–95, 1970.

[73] R. R. Varshamov.  Estimate of the number of signals in error correcting codes.  Doklady 

Akadamii Nauk, 117:739–741, 1957.

[74] Joachim von zur Gathen and Jürgen Gerhard.  Modern Computer Algebra.  Cambridge 

University Press, 3 edition, 2013.

[75] Lloyd R. Welch and Elwyn R. Berlekamp.  Error correction of algebraic block codes. 

US Patent Number 4,633,470, December 1986.

187



<!-- pdf-page: 200 -->
[76] Richard Zippel.  Probabilistic algorithms for sparse polynomials.  In Edward W. Ng, 
editor, Proc. International Symp. of Symbolic and Algebraic Computation (EUROSAM), 
volume 72 of LNCS, pages 216–226. Springer, 1979.

[77] V. V. Zyablov.  An estimate of the complexity of constructing binary linear cascade 
codes.  Probl. Peredachi Inf., 7(1):5–13, 1971.  English Translation in Problems of Infor­
mation Transmission, 7:1(3–10), 1971.

188



<!-- pdf-page: 201 -->
Appendix A

Some Useful Facts

A.1  Some Useful Inequalities

Recall that the binomial coefficient for integers a ≤ b, defined as

)︃

(︃b
a

=

b!
a!(b − a)!

.

We begin with a simple lower bound on the binomial coefficient:

Lemma A.1.1. For all integers 1 ≤ a ≤ b, we have

)︃

(︃b
a

≥

)︃a

.

(︃ b
a

Proof. 

The following sequence of relations completes the proof:

)︃

(︃b
a

=

a−1
∏︂

i=0

b − i
a − i

≥

a−1
∏︂

i=0

b
a

=

)︃a

.

(︃ b
a

In the above, the first equality follows from definition and the inequality is true since b ≥ a
and i ≥ 0.

We state the next set of inequalities without proof (see [62] for a proof):

Lemma A.1.2  (Stirling’s Approximation). For every integer n ≥ 1, we have

where

√

2πn

)︂n

(︂n
e

eλ1(n) < n! <

√

2πn

)︂n

(︂ n
e

eλ2(n),

λ1(n) =

1
12n + 1

 and λ2(n) =

1
12n

.

189

 


<!-- pdf-page: 202 -->
We prove another inequality involving Binomial coefficient.

Lemma A.1.3. For all integers 1 ≤ a ≤ b, we have

)︃

(︃b
a

≤

)︃a

.

(︃ eb
a

Proof. 

First note that

)︃

(︃b
a

=

b(b − 1) · · · (b − a + 1)
a!

≤

ba
a!

.

The final bound follows from the fact that

a! >

)︂a

,

(︂ a
e

which in turns follows from the following relationships:

aa
a!

<

∞
∑︂

i=0

ai
i!

= ea.

We next state Bernoulli’s inequality:

Lemma A.1.4  (Bernoulli’s Inequality). For every real numbers k ≥ 1 and x ≥ −1, we have

(1 + x)k ≥ 1 + kx.

Proof Sketch.  We only present the proof for integer k.  For the full proof see e.g. [10].

For the base case of k = 1, the inequality holds trivially.  Assume that the inequality 
holds for some integer k ≥ 1 and to complete the proof, we will prove it for k + 1.  Now 
consider the following inequalities:

(1 + x)k+1 = (1 + x) · (1 + x)k
≥ (1 + x) · (1 + kx)
= 1 + (k + 1)x + kx2
≥ 1 + (k + 1)x,

as desired.  In the above, the first inequality follows from the inductive hypothesis and the 
second inequality follows from the fact that k ≥ 1.

Lemma A.1.5. For |X| ≤ 1,

√

1 + x ≤ 1 +

x
2

−

x2
16

.

190

 
 


<!-- pdf-page: 203 -->
Proof. 

Squaring the RHS we get

(︃

1 +

)︃2

x
2

−

x2
16

= 1 +

x2
4

+

x4
256

+ x −

x2
16

−

x3
32

= 1 + x +

3x2
16

−

x3
32

+

x4
256

≥ 1 + x,

as desired.

We will also use the Cauchy-Schwarz inequality:

Lemma A.1.6. For any vector x, y ∈ Rn, we have

|⟨x, z⟩| ≤ ∥x∥2 · ∥z∥2.

A.2  Some Useful Identities and Bounds

We start off with an equivalence between two inequalities.

Lemma A.2.1. Let a, b, c, d > 0.  Then  a

b ≤ c

d if and only if  a

a+b ≤ c

c+d .

Proof. 

Note that  a

b ≤ c

d  if and only if

The above is true if and only if

b
a

≥

d
c

.

b
a

+ 1 ≥

d
c

+ 1,

which is same as  a

a+b ≤ c

c+d.

Next, we state some infinite sums that are identical to certain logarithms (the proofs are 

standard and are omitted).

Lemma A.2.2. For |x| < 1,

ln(1 + x) = x −

x2
2!

+

x3
3!

− · · · .

We can use the above to prove some bounds on ln(1 + x) (we omit the proof):

Lemma A.2.3. For 0 ≤ x < 1, we have

and for 0 ≤ x ≤ 1/2, we have

x − x2/2 ≤ ln(1 + x) ≤ x,

−x − x2 ≤ ln(1 − x) ≤ −x.

191

 
 


<!-- pdf-page: 204 -->
We can use the above bounds to further prove boounds on the (binary) entropy function:

Lemma A.2.4. For x ≤ 1/4, we have

1 − 5x2 ≤ H(1/2 − x) ≤ 1 − x2.

Proof. 
using the approximations for ln(1 + x) from Lemma A.2.3, we have, for x < 1/4,

By definition H(1/2 − x) = 1 − 1/2 log(1 − 4x2) + x log(1 − 2x)/(1 + 2x), and 

H(1/2 − x) ≤ 1 +

· (4x2 + 16x4) +

· x2 +

2
ln 2

· x3 +

1
ln 2
8
ln 2

· x4

· (−2x2) −

1
ln 2

· (2x2 − 2x3)

= 1 −

1
2 ln 2
2
ln 2
x2
ln 2
≤ 1 − x2.

≤ 1 −

(A.1)

In the above, (A.1) follows by using our assumption that x ≤ 1/4.
Using the other sides of the approximations we also have:

· (4x2) +

1
ln 2

· (−2x2 − 4x3) −

1
ln 2

· (2x2)

H(1/2 − x) ≥ 1 +

1
2 ln 2
3x2
ln 2
≥ 1 − 5x2,

≥ 1 −

where the second inequality uses our assumption that x ≤ 1/4.

The following fact follows from the well-known fact that limx→∞(1 + 1/x)x = e:

Lemma A.2.5. For every real x > 0,

(︃

1 +

)︃x

1
x

≤ e.

192

 


<!-- pdf-page: 205 -->
Appendix B

Basic Algebraic Algorithms

B.1  Executive Summary

In this appendix we include some basic facts about abstract algebra that were used through­
out the book.  Readers who are comfortable with their background in algebra should feel 
free to skip it entirely.  However, this background should include both aspects introduced 
by finiteness — most fields we work with are finite,  and so are the vector spaces defined 
over  them  —  and  computation —  the  mere  existence  of  a  nice  algebraic  structure  is  not 
good enough for us, we need to know how to carry out basic, and not so basic operations 
over these structures efficiently.  If you are not very comfortable with these settings you will 
find the appropriate sections of this appendix more useful.  The opening paragraph of each 
section summarizes the main aspects covered in the section and the reader may use them to 
decide if they wish to read further.

Some of the material in this appendix appears earlier in the book (e.g.  Sections 2.1, 2.2 
and 5.1).  Finally, this coverage of algebra in this appendix is not exhaustive and the reader 
is referred to the book by Lidl and Niederreiter [47] for more matetrial (and proofs) on finite 
fields and the book by Shoup for more details on the basic algebraic algorithms [67].

B.2  Groups, Rings, Fields

The title of this section says it all.  We cover, very tersely, the definition of a group, a ring, 
and a field.

We begin with some terminology.  We consider binary operations over some set of ele­
ments.  Given a set X such a binary operator would be a function ◦ : X × X → X, and 
we usually use a ◦ b to denote ◦(a, b), for a, b ∈ X.  We say the operator ◦ is associative if 
a ◦ (b ◦ c) = (a ◦ b) ◦ c, for every a, b, c ∈ X.  For associative operations it is customary to 
drop the parenthesis. We say the operator ◦ is commutative if a ◦ b = b ◦ a for every a, b ∈ X. 
We say an element e ∈ X is an identity for ◦ if a ◦ e = e ◦ a = a for every a ∈ X.  Identities 
are,  by definition,  unique if they exist,  since if e1, e2 ∈ X were identities,  we would have 
e1 = e1 ◦ e2 = e2.  Given a ∈ X and operator ◦ with inverse e we say that a is is invertible 

193



<!-- pdf-page: 206 -->
with respect to ◦ if there exists an element a−1 ∈ X such that a ◦ a−1 = a−1 ◦ a = e.  Often 
◦ will be clear from context in which case we will refer to a as simply invertible.

Definition B.2.1   (Group). Given a set G and a binary operation ◦ over G, we say that 
(G, ◦) is a group if ◦ is associative, has an identity, and every element of G is invertible.  A 
group (G, ◦) is said to be an abelian group if ◦ is also commutative.

Examples of groups include the integers with addition, the non-zero rationals with mul­
tiplication and the set of permutations (one-to-one functions) on any finite set under the 
composition operation.

Definition B.2.2   (Ring). A finite set R with two binary operations + and · are said to 
form a ring if (1) (R, +) form an abelian group, (2) · is associative and has an identity and 
(3) · distributes over +, i.e., for every a, b, c ∈ R we have a · (b + c) = (a · b) + (a · c) and 
have (b + c) · a = (b · a) + (c · a).  The ring (R, +, ·) is said to be a commutative ring if · is 
commutative.

Examples include the integers over addition and multiplication (a commutative ring) and 
the set of k ×k integer matrices (for any positive integer k) under matrix addition and matrix 
multiplication (which forms a non-commutative ring for k ≥ 2).

Definition B.2.3   (Field). A set F with operations + and · forms a field if (F, +, ·) is a 
commutative ring, and (F \ {0}, ·) is a group where 0 denotes the identity for +.

Examples of fields include the rationals, the reals, the complexes (all under addition and 
multiplication) and (more interestingly to us) the integers modulo any prime number p (see 
Lemma 2.1.4 for the latter).

It is customary in rings and fields to let 0 denote the additive identity, 1 the multplicative 
identity and to let −a denote the additive inverse of a and a−1 the multiplicative inverse of 
a.  It is also customary to abbreviate a + (−b) to a − b.

B.3  Polynomials

In this section we will introduce polynomial rings,  mention when they satisfy the unique 
factorization property, describe the ‘remainder algorithm’, and describe the evaluation map 
and the polynomial distance property (where the latter is a re-statement of the degree mantra 
(Proposition 5.1.5)).

Definition  B.3.1   (Formal  Polynomials).  Let  (R, +, ·)  be  a  commutative  ring  with  iden­
tity 0.  The set of formal polynomials over R in indeterminate X, denoted R[X], is given 
by finite formal sums R[X] = {∑︁d
i=0 fiX i|f0, . . . , fd ∈ R; d ∈ Z≥0}, under the equivalence 
∑︁d
i=0 fiX i if fd = 0.  (The term formal refers to the fact that the summa­
tion, and the terms X i are just formal symbols and do not have operational meaning, yet. 
So  really  polynomials  are  just  finite  sequences  of  elements  from  R  under  the  equivalence 
(f0, . . . , fd, 0) ∼= (f0, . . . , fd).)

i=0 fiX i = ∑︁d−1

194



<!-- pdf-page: 207 -->
Basic terminology The elements fi are referred to as the coefficients of f , the symbols X i
i=0 fiX i, its 

as the monomials of f  and the product fiX i as the terms of f .  For f = ∑︁d
degree, denoted degX(f ) or simply deg(f ), is the largest integer e such that fe ̸= 0.

Addition The sum of two polynomials f = ∑︁d

is the polynomial ∑︁d
with zeroes we can always arrange it so that they have the same number of terms.)

i=0 fiX i and g = ∑︁d
i=0 giX i, denoted f + g, 
i=0(fi + gi)X i.  (Note that by padding the coefficients of f  and g

Multiplication Finally, the product of f = ∑︁d
(︂∑︁e
sometimes simply f g), is given by ∑︁d+e

i=0 fiX i g = ∑︁e
X i.
j=0 fi−j · gj

)︂

i=0

i=0 giX i, denoted f · g (or 

The following proposition follows immediately from the definitions above.

Proposition B.3.2. For every commutative ring R, R[X] is a commutative ring under the 
sum and product of polynomials.

In fact R inherits many properties of R and in particular the notion of “unique factor­

ization” which we describe next.

Definition  B.3.3   (Unique  Factorization  Domains).  Let  R  be  a  commutative  ring.  An 
element u ∈ R is said to be a unit if it has a multiplicative inverse in R.  Elements a and 
b  are  said  to  be  associates  if  there  exists  a  unit  u  such  that  a = b · u.  (Note  that  being 
associates is an equivlence relationship.)  Element a ∈ R is said to be irreducible if a = b · c
implies either b or c is a unit.  A factorization of a ∈ R is a sequence b1, . . . , bk such that 
a = b1 · b2 · · · bk and none of the bi’s are units.  The bi are referred to as the factors of a in 
this factorization.  Ring R is a factorization domain if for non-zero every a ∈ R that is not 
a unit, there is a finite bound ka such that every factorization of a has at most ka factors.  A 
factorization domain R is a unique factorization domain (UFD) if every non-zero, non-unit 
element has a unique irreducible factorization, upto associates. I.e., if a = b1 · · · bk = c1 · · · cℓ
and the bi’s and cj’s are irreducible, then k = ℓ and there exists a bijection π : [k] → [ℓ] such 
that bi and cπ(i) are associates, for every i ∈ [k].

Since every non-zero element of a field is a unit, every field is a UFD.

Proposition B.3.4. Every field is a UFD.

A central result in basic commutative algebra is the following lemma of Gauss.

Lemma B.3.5  (Gauss). If R is a UFD, then so is R[X].

We omit the proof of the above lemma here, but point out its implications.  It allows us 
to build many interesting rings from a simple base case, namely a field. Given a field F, F[X]
is a UFD. So is (F[X])[Y ].  Now we could have gone in the other direction and created the 
ring (F[Y ])[X] and this would be a UFD too. However if X and Y  commute (so XY = Y X) 
then the rings (F[X])[Y ] and (F[Y ])[X] are isomorphic under the isomorphism that preserves 

195



<!-- pdf-page: 208 -->
F and sends X → X and Y → Y . So we tend to compress the notation and refer to this ring 
as F[X, Y ], the ring of “bivariate” polynomials over F.  Rings of univariate and mutlivariate 
polynomials play a central role in algebraic coding theory.

We now turn to the notion of polynomial division with remainder that lead us to some 

important notions associated with polynomials.

Let f ∈ R[X] and let f = ∑︁d

i=0 fiX i with fd ̸= 0.  f  is said to be monic if fd is a unit in 

R.

Proposition B.3.6. Given a monic polynomial f , and general polynomial p there exists a 
unique pair of polynomials q (for quotient) and r (for remainder) such that p = q · f + r and 
deg(r) < deg(f ).

See Exercise B.1 for a proof.
The function p ↦→f (q, r) described is often referred to as the ‘division algorithm’ (since 
it is the outcome of long division).  A special case that is of great interest to us is when 
f = X − α for α ∈ R.  In this case the remainder is polynomial of degree at most 0, and 
so can be associated with an element of R.  Denote this element p(α) (since it depends only 
on p and α) and we get the “evaluation” map which maps elements of R[X] × R to R.  The 
remainder p(α) can be worked out explicitly and is given by the simple form below (where 
the uniqueness follows from Proposition B.3.6).

Proposition B.3.7. Given p = ∑︁d
i=0 piαi.  Then 
there exists a unique q ∈ R[X] such that p = q · (X − α) + p(α).  It follows that p(α) = 0 if 
and only if X − α divides p(X).

i=0 piX i ∈ R[X] and α ∈ R, let p(α) = ∑︁d

Finally using Proposition B.3.7 and the fact that F[X] is a UFD, we get the following 

the following central fact about univariate polynomials.

Lemma B.3.8  (Polynomial Distance Lemma). Let f ̸= g ∈ F[X] be polynomials of degree 
at most d.  Then there exist at most d elements α ∈ F such that f (α) = g(α).

Let  h = f − g.  We  have  h  is  non-zero  and  of  degree  at  most  d.  Let  S =
Proof. 
{α|f (α) = g(α)}.  Then we have (X − α) divides h for every α ∈ S.  Furthermore, by the 
unique factorization property we have ˜h = ∏︁
α∈S(X − α) divides h.  But if ˜h divides h, then 
deg(˜h) ≤ deg(h) and deg(˜h) = |S|.  We conclude |S| ≤ d.

B.4  Vector Spaces

In this section we introduce vector spaces over fields and describe two basic views of describ­
ing a finite dimensional vector space: first via its generators (and the generator matrix) and 
next via constraints on the vector space (and its parity check matrix).  We first start with 
a quick overview of matrices and the corresponding notation and then move on to vector 
spaces.

196

 


<!-- pdf-page: 209 -->
B.4.1  Matrices and Vectors
In this book, a vector of length n over the field F (i.e.  x ∈ Fn) is a row vector1.  E.g., we 
have x = (︁0 1 3 4 0)︁ ∈ F4
5.  Given two vectors u, v ∈ Fn, their inner product is defined 
as

n
∑︂

⟨u, v⟩ =

ui · vi,

i=1
where the multiplication and addition are over F.

A matrix M ∈ Fk×n is a two-dimensional array/vector, where we refer to the (i, j)’th 
entry (for (i, j) ∈ [k]×[n]) as Mi,j (or Mij if the two indices are clear without being separated 
by a comma). We will use Mi,· as the i’th row and M·,j as the jth column of M  respectively.

So e.g.  consider G ∈ F2×3

3

 as follows:

G =

)︃

(︃1 0 1
0 2 1

.

In the above G1,2 = 2, G1,· = (︁1 0 1)︁ and G·,2 =

)︃
.

(︃0
2

The transpose of a matrix M ∈ Fk×n, denoted by M T  is an n × k matrix over F such that 

for any (j, i) ∈ [n] × [k], we have

j,i = Mij.
Note that if k = 1, then the above says that for a row vector x ∈ Fn, its transpose xT  is a 
column vector.

The product of two matrices A ∈ Fk×n and B ∈ Fn×m is a matrix C ∈ Fk×m such that 

M T

for any (i, j) ∈ [k] × [m], we have

Ci,j = ⟨Ai,·, B·,j⟩ .

B.4.2  Definition and Properties of Vector Spaces

This section will repeat some of the material from Section 2.2.  We begin with the definition 
of a vector space:

Definition B.4.1  (Vector Space). Over a field F, a vector space is given by a triple (V, +, ·)
where (V, +) is a commutative group and · : F × V → V  distributes over addition, so that 
α · (u + v) = α · u + α · v for every α ∈ F and u, v ∈ V .  It is customary to denote the identity 
of the group (V, +) by 0 and to refer to V  as an F-vector space.

1We acknowledge that this is different from the usual assumption in linear algebra that all vectors are 
column vectors.  We are assuming row vectors to be consistent with how message vectors are assumed to be 
row vectors in coding theory.

197



<!-- pdf-page: 210 -->
The  simplest  example  of  an  F-vector  space  is  Fn,  whose  elements  are  sequences  of  n
elements  of  F.  The  sum  is  coordinate-wise  summation  and  product  is  “scalar”  product, 
so if u = (u1, . . . , un), v = (v1, . . . , vn) and α ∈ F then u + v = (u1 + v1, . . . , un + vn) and 
α·u = (α·u1, . . . , α·un). Essentially these are the only vector spaces (as we will make precise 
soon), but representations of the vectors is important to us, and will make a difference.

Definition B.4.2  (Dimension of a vector space).

A sequence of vectors v1, . . . , vk ∈ V  are said to be linearly independent if ∑︁k

i=1 βi · vi = 0

implies that β1 = · · · = βk = 0.  v1, . . . , vk ∈ V  are said to linearly dependent otherwise.

V  is said to be finite dimensional of dimension k if every sequence of k + 1 vectors from 

V  is linearly dependent and there exists a sequence of length k that is linearly independent.

A linearly independent set v1, . . . , vk ∈ V  is said to form a basis for V  if V  has dimension 

k.

Every F-vector space of dimension k is isomorphic to Fk as described by the following 

proposition.

Proposition B.4.3. If v1, . . . , vk for a basis for an F-vector space V , then V = {∑︁k
vi|β1, . . . , βk ∈ F} and the map (β1, . . . , βk) ↦→ ∑︁k

i=a βi ·
i=1 βi · vi is an isomorphism from Fk to V .

The point we wish to stress now is that even though all vector spaces are isomorphic, 
different spaces do lead to different codes with different error-correction properties, and these 
properties are not preserved by such isomorphisms.  So not all k-dimensional vector spaces 
are identical for our purposes. We will specially be interested in k-dimensional vector spaces 
contained in Fn, and how these can be represented succinctly in matrix form.

Definition B.4.4  (Generator Matrix, Parity Check Matrix). A matrix G ∈ Fk×n is said to 
be a generator matrix of an F-vector space V ⊆ Fn if the rows of G are linearly independent 
in Fn and V = {x · G|x ∈ Fk}.  The rows of G form a basis of V .  A matrix H ∈ F(n−k)×n is 
said to be a parity check matrix of an F-vector space V ⊆ Fn if the rows of H are linearly 
independent and V = {y ∈ Fn|H · yT = 0}.  Given a vector space V  with parity check matrix 
H, its dual space, denoted V ⊥, is the vector space generated by H, i.e., V ⊥ = {x·H|x ∈ Fn−k}.

Our goal below is to show that every space has a generator matrix and a parity check 
matrix.  The former is obvious from definitions.  If V ⊆ Fn is a k-dimensional vector space, 
then it has a basis v1, . . . , vk and if we build a matrix G with these vectors as its rows, then 
G satisfies the conditions of the generator matrix.

We sketch the idea for construction of a parity check matrix. We say that a k × k matrix 
R forms a row operation if either (i) Rii = 1, and Rij = 0 for all but one pair i ̸= j ∈ [k] or 
(ii) is a permutation matrix that swaps two rows. We say that  ˜G is obtained from G by row 
operations, denoted G (cid:59) ˜G, if  ˜G = Rm · Rm−1 · · · R1 · G where the Ri’s are row operations. 
Note that if G is a generator matrix for V  then so is  ˜G.  Gaussian elimination allows us to 
“simplify” G till its columns are special, and in particular after permuting the columns  ˜G
would look like [Ik|A] where Ik denotes the k × k identity matrix.  Assume for simplicity 

198



<!-- pdf-page: 211 -->
that  ˜G = [Ik|A] (without permuting columns).  Now let H be given by H = [−AT |In−k].  It 
can be verified that  ˜G · H T = 0 and so G · H T = 0.  Furthermore all rows of H are linearly 
independent and so H satisfies the conditions of the parity check matrix of V .  We conclude 
with the following.

Proposition B.4.5. If V ⊆ Fn is a k-dimensional vector space then it has a generator matrix 
G ∈ Fk×n and a parity check matrix H ∈ F(n−k)×n.  Furthermore its dual V ⊥ is generated by 
H, has dimension n − k, and has G as its parity check matrix.  Finally (V ⊥)⊥ = V .

Before concluding we mention one important difference from the case of orthoganility of 
real vectors.  For vector spaces over finite fields it is possible that there are non-zero vectors 
in V ∩ V ⊥ and indeed even have V = V ⊥.  (See Exercise 2.31 for more on this.)

B.5  Finite Fields

In this section we describe the existence and uniqueness of finite fields. We also describe the 
basic maps going from prime fields to extensions and vice versa.  Parts of this section will 
repeat material from Section 2.1 and 5.1.

B.5.1  Prime Fields
We start by describing a field of size p, for any prime number p. Let Zp be the set of integers 
{0, . . . , p − 1}.  For integer a and postive integer b, let a mod b denote the unique integer c
in Zp such that b divides a − c.  Let +p be the binary operation on Zp that maps a and b to 
(a + b) mod p.  Let ·p map a and b to (ab) mod p.  We have the following (see Section 2.1 
for a proof).

Proposition B.5.1. (Zp, +p, ·p) form a field of cardinality p.

Given a finite field F, its characteristic, denoted char(F), is the smallest positive integer 
p such that p · 1 = 1 + 1 + · · · + 1 = 0.  (See Exercise B.2 for why such a finite characteristic 
exists.)

Proposition  B.5.2.  For  every  finite  field  F,  char(F)  is  a  prime.  Furthermore,  F  is  a 
Zp-vector space, where p = char(F).  Thus F has cardinality pn for prime p and integer n.

Let p = char(F).  We first note that p is the smallest integer such that p · a = 0
Proof. 
for any non-zero element of F.  This is so since p · a = p · 1 · a = 0, and if p · a = 0 then so is 
p · a · a−1 = p · 1.  Next we note that if p = qr then for the element w = q · 1 ∈ F, we have 
w · r = 0 which contradicts the minimality of p.

Next  we  note  that  (F, +, ◦)  satisfy  the  conditions  of  a  Zp-vector  space  where  i ◦ a =
(a + · · · + a) (i times), for i ∈ Zp and a ∈ F.  We conclude that |F| = pn where n is the 
dimension of the vector space (F, +, ◦) and p = char(F).

199

 


<!-- pdf-page: 212 -->
We conclude now by claiming that Zp is the unique field of cardinality p.

Proposition B.5.3. For any prime p, there is a unique field of cardinality p upto isomor­
phism.

Proof. 
It can be verified that the map 1F → 1 extends to an isomorphism (see Exercise B.3).

Let F be a field of cardinality p.  By Proposition B.5.2 we have that char(F) = p. 

The uniqueness of the field of cardinality p allows us to call it Fp in the future.

B.5.2  Extension fields and subfields

We now move towards determining when non-prime fields exists. While the answer is simple 
(they exist for every number of the form pn for prime p and positive integer n), proving when 
they exist requires some structural understanding of how fields behave.

We will first present a basic property of all finite fields that is crucial when working with 

fields.

We recall a basic result about finite groups (see Exercise B.4) for a proof for the abelian 

case).

Proposition B.5.4. If (G, ·) is a finite group with identity 1, then for every a ∈ G, we have 
a|G| = 1.

Proposition B.5.5. Let F be a field of cardinality q.  The every element α ∈ F is a root of 
the polynomial X q − X and so X q − X = ∏︁

α∈F(X − α).

If α = 0, then it is trivial to see that is a root of X q − X.  If α ̸= 0, then it is 
Proof. 
a member of a group (F \ {0}, ·) and so by Proposition B.5.4, satisfies α|F\{0}| = 1.  Thus, 
αq−1 = 1, and finally αq = α, as desired.

Let K be a field and F ⊆ K be a set that is closed under addition and multiplication. 
Then F is itself a field and we denote if F (cid:1) K to denote that it is a subfield of K.  We say 
K (cid:3) F to denote that K extends F.

Proposition B.5.6. If K (cid:3) F then K is an F-vector space and so |K| = |F|n where n is the 
dimension of K as an F-vector space.  Furthermore there is a unique copy of F in K.

The fact that K is a vector space follows from the definitions, and thus the claim 
Proof. 
about its cardinality.  The fact that there is a unique copy of F follows from the fact that 
the elements of F satisfy X q − X = 0, where q = |F| and there can be at most q roots of this 
polynomial.

200

 
 
 


<!-- pdf-page: 213 -->
B.5.3  Existence of Finite Fields

In what follows we will rely heavily on the modular reduction of polynomials.  Following the 
notation of previous sections, for field F and f, g ∈ F[X], we let f mod g be the remainder 
when f  is divided by g - so deg(f mod g) < deg(g) and g divides f − (f mod g).  Let 
f +g h = (f + h) mod g and let f ·g h = (f h) mod g. Recall that an irreducible polynomial 
in Fq[X] is one that does not have any non-trivial factor (recall Definition 5.1.6).

Proposition B.5.7. Let F be a finite field of cardinality q and let g ∈ F[X] be an irreducible 
polynomial of degree n.  Then (F[X]/g, +g, ·g) form a field of cardinality qn.

Essentially all fields can be obtained in the above manner, but to prove this fact, we need 
to prove that there is an irreducible polynomial of degree n over Fp for every p and unfortu­
nately this proof is not much simpler than proving the existence of a field of cardinality pn. 
So we prove the existence directly, or rather sketch a proof of this fact.

The  rough  idea  of  the  proof  is  as  follows:  First  we  establish  that  every  polynomial 
f ∈ F[X] splits completely (into linear factors) over some extension K of F.  To do this we 
work slowly, working away at one irreducible factor of f  at a time. If g is such an irreducible 
factor, we consider the field2 L = F[Z]/g(Z) and note that Z is a root of g,3 and hence of 
f , in L and so f  splits more in L.  We continue this process till f  splits completely in some 
field K.

Now we work with a very special polynomial f , namely f (X) = X pn − X in the ring 
Fp[X] and let K be a field in which f  splits completely.  Now let S ⊆ K be the set S =
{α ∈ K|f (α) = 0}.  We  note  that  this  set,  miraculously,  is  closed  under  addition  and 
multiplication.  The latter is easy:  f (α) = 0 if and only if αpn = α.  So if f (α) = f (β) = 0
then αpn = α and βpn = β and so (αβ)pn = αpnβpn = αβ and so αβ ∈ S.  For the former we 
explicitly highlight another crucial fact in finite fields.

Proposition B.5.8. Let K be a field of characteristic p and let A, B ∈ K[X, Y ].  Then for 
all positive integers n we have (A + B)pn = Apn + Bpn

.

The proof of the lemma above follows immediately from the fact that (︁p

)︁ mod p is 0
unless p divides i (see Exercise B.5).  And while the lemma is stated for very general A and 
B, we only need it for A, B ∈ K itself.  However we state it generally since it is fundamental 
to working over extension fields and indeed we will see a few applications later.

i

Returning to our quest to prove that S is closed under addition, let us apply the above 
proposition to α, β ∈ S. We get that (α + β)pn = αpn + βpn = α + β and so S is closed under 
addition as well.  What we will show next is that S has exactly pn elements and so is a field 
of size pn (it is closed under addition and multiplication and the rest of the properties follow 
from the fact that S is a subseteq of a field K).

First  note  that  S  has  all  roots  of  f .  We  note  further  that  f   has  no  multiple  roots. 
In  general  this  is  proved  by  looking  at  derivatives  etc.,  but  in  this  case  we  can  do  it  by 

2Recall Theorem 5.1.7.
3This is because g(Z) ≡ 0 in L.

201



<!-- pdf-page: 214 -->
inspection.  We wish to show that (X − α)2 does not divide X pn − X, but this is the same 
as showing that Z 2 does not divide (Z + α)pn − (Z + α) = Z pn − Z + αpn − α, but the latter 
polynomial has a coefficient of −1 ̸= 0 for Z and so is not divisible by Z 2. We conclude that 
since S has all roots of X pn − X and this polynomial has pn distinct roots, and so |S| ≥ pn. 
On the other hand since every element of S is a root of X pn − X and this polynomial has at 
most pn roots, we conclude that |S| = pn and so there exists a field of cardinality pn.  Thus 
we get the following theorem (the first part follows from Proposition B.5.2 and the second 
part follows from Proposition B.5.7).

Theorem B.5.9. If F is a finite field, then it has characteristic p for some prime p and its 
cardinality is pn for positive integer n.  Conversely, for every prime p and positive integer n, 
there is a field of cardinality pn.

B.5.4  Uniqueness of finite fields

We start by proving that every finite field has a multiplicative generator.  To do so we need 
to understand cyclic groups a bit better.

The cyclic group of order n is the group Zn = {0, . . . , n−1} with addition modulo n being 
the binary operation.  This group clearly has an element of order n (namely the number 1). 
Let N =(G, m) denote the number of elements of order exactly m in G and let N (G, m) denote 
the number of elements of order dividing m in G.  We have N (G, m) = ∑︁
k|m N =(G, k).  For 
the cyclic group, we have for every k|n, N (Zn, k) = k and N =(Zn, k) ≥ 0.  (The latter is 
trivial and for the former see Exercise B.6.)

We now turn to understanding (F∗, ·) the group of non-zero elements of F under multi­

plication.

Lemma  B.5.10.  Let  q = |F|  and  n = q − 1.  We  claim  that  for  every  k  dividing  n, 
N (F∗, k) = N (Zn, k) and N =(F∗, k) = N =(Zn, k).

The claim is straightforward for N (F∗, k).  We have that every α ∈ F∗ is a root of 
Proof. 
the polynomial X n − 1 and since X k − 1 divides4 X n − 1, k elements of F∗ must be roots of 
this polynomial also.  We thus have N (F∗, k) = k = N (Zn, k).

For the claim about N =(F∗, k), we use induction and the inductive formula.  We have 
∑︁
ℓ|k N =(F∗, ℓ) = N (F∗, k) = k = N (Zn, k) = ∑︁
ℓ|k N =(Zn, ℓ).  But since by induction we 
have N =(F∗, ℓ) = N =(Zn, ℓ) for ℓ < k, we may conclude that the remaining term N =(F∗, k) =
N =(Zn, k).

We say that an element ω ∈ F is primitive if ωi ̸= 1 for i < |F| − 1 and ω|F|−1 = 1.  Since 
N =(F∗, n) counts the number of primitive elements, Lemma B.5.10 implies that the number 
of primitive elements is at least one.  Indeed, if p is the smallest prime divisor of n, then 
we have that N =(F∗, n) = N (F∗, n) − N (F∗, n/p) − N (F∗, p) = n − n/p − p > 0, assuming 
p < n/p.  Otherwise if n = p2, then we have N =(F∗, n) = N (F∗, n) − N (F∗, p) = n − p > 0. 
If n itself is a prime then we have N =(F∗, n) = N (F∗, n) = n > 0.

4See Exercise B.7.

202

 


<!-- pdf-page: 215 -->
Proposition B.5.11. Every finite field F has a primitive element.  Consequently the multi­
plicative group is cyclic.

We now describe a weaker form of special element in F.  Let K extend F.  We say that 
α ∈ K is an F-generator for K if for every element β ∈ K there is a polynomial p ∈ F[X]
such that β = p(α).

Proposition B.5.12. Let K be a finite field and let ω be a primitive element in K.  Then 
for every subfield F (cid:1) K we have that ω is an F-generator of K.  As a consequence, for every 
K (cid:3) F there is an F-generator in K.

Proof. 
and |K| = qn.

Consider the lowest degree polynomial p ∈ F[X] such that p(ω) = 0.  Let |F| = q

We  claim  that  deg(p) = n.  If  deg(p) > n,  we  have  that  1, ω, ω2, . . . , ωn  are  linearly 
independent  over  F  and  so  K  has  size  strictly  larger  than  qn.  Now  if  deg(p) < n,  then 
consider the polynomials X, X 2, X 3, . . . , X qn−1 modulo p ∈ F[X].  Since we have only qdeg(p)
options for the residues, two of these must be equal modulo p and so there exist i ̸= j and 
f ∈ F[X] such that X i = X j + p · f .  Substituting X = ω yields ωi = ωj + p(ω)f (ω) = ωj. 
But this contradicts the assumption that ω is a primitive element.

Finally,  note that every non-zero element β ∈ K can be written as the polynomial qj

mod p(X) evaluated at X = ω for some 0 ≤ j < qn. 

Generators are useful in that they show that the only way to construct field extensions 

is via irreducible polynomials.

Proposition B.5.13. Let K (cid:3) F and let α be an F-generator of K. Then, if p is the minimal 
polynomial in F[X] such that p(α) = 0,  we have p is irreducible and K is isomorphic to 
F[X]/p.

Irreducibility of p follows from its minimality (see Exercise B.8). The isomorphism 
Proof. 
is obtained by fixing F (cid:1) K and letting α ↦→ X.  We leave it to the reader to verify that this 
extends to an isomorphism (uniquely)– see Exercise B.9.

We are almost ready to prove uniqueness of finite fields.  We need one more fact about 

irreducible polynomials to do so.

Proposition B.5.14. If f ∈ Fp[X] is irreducible of degree n, then f  divides X pn − X.

Consider the field K = Fp[X]/(f ).  This is a field of cardinality pn and so every 
Proof. 
element α ∈ K satisfies αpn = α.  In particular X ∈ K also satisfies this,  implying that 
X pn − X = 0( mod f ) and so f  divides X pn − X.

We now turn to proving uniqueness of finite fields.

Theorem B.5.15. For every prime p and integer n, there is a unique field of cardinality pn
up to isomorphism.

203

 
 
 


<!-- pdf-page: 216 -->
Suppose K, L are both fields of cardinality pn.  Both fields contain a unique copy 
Proof. 
of  Fp,  and  by  mapping  1K  to  1L  and  extending  additively,  we  get  a  partial  isomorphism 
between these copies of Fp.  Now we show how to extend it.  Let α ∈ K be a Fp-generator 
and let f ∈ Fp[X] be its minimal polynomial.  Since f  is irreducible of degree n, we have 
that f (X) divides the polynomial X pn − X (see Proposition  B.5.14).

Using the fact that X pn − X = ∏︁

β∈L(X − β), we conclude that L contains a root β of 
f .  We assert (see Exercise B.10) that the map that sends α ↦→ β is an isomorphism from K
to L.

B.5.5  The Trace and Norm maps

We conclude this section with two basic polynomials that have some very nice regularity 
property when dealing with finite fields and their extensions.

Definition B.5.16. Let F = Fq and let K = Fqn. Then the Trace function Tr = TrK→F is the 
function obtained by the evaluation of the polynomial Tr(X) = X + X q + X q2 + · · · + X qn−1
. 
The Norm function is obtained by evaluation of N (X) = X 1+q+q2+···+qn−1

.

The Norm and Trace functions are important because they map elements of K to the 

subfield F and they do so in a nice uniform way.  We mention some properties below.

Proposition B.5.17. 

1. Trace is a F-linear map, i.e., for every α ∈ F and β, γ ∈ K, we have Tr(α · β + γ) =

α · Tr(β) + Tr(γ).

2. Norm is multiplicative, i.e., N (β · γ) = N (β)N (γ)

3. Trace is a qn−1-to-one map from K to F.

4. Norm is a (qn − 1)/(q − 1)-to-one map from K∗ to F∗.

Proof.  We prove each of the four items in order:

1. The F-linearity follows from the facts that (αβ + γ)qi = αqiβqi + γqi

 and αqi = α.

2. The multiplicativity is obvious from definition.

3. For β ∈ K we have Tr(β)q = βq + · · · βqn = βq + · · · + βqn−1 + 1 = Tr(β) and so the 
range of Tr is F.  Since Tr is a polynomial of degree qn−1 is can take on any value in 
the range at most qn−1 times.  But it has a domain of size qn and range of size q, so it 
must take on every value exactly qn−1 times.

4. The is similar to Part (3) above.  By Exercise B.11, we have that N (β)q = N (β) and 
furthermore note that by definition, N (β) is non-zero iff β ̸= 0. We then use the degree 
of N  and counting to determine that it is a regular function on non-zero values.

204

 


<!-- pdf-page: 217 -->
The Trace function from K → F is especially important since it captures all F-linear 

maps from K → F, as explained below.

Proposition B.5.18. A function L : K → F is F-linear if and only if there exists λ ∈ K
such that L(β) = Tr(λβ) for every β ∈ K.

Proof. 

First note that f (β) = Tr(λβ) is obviously F-linear since

f (αβ + γ) = Tr(λ(αβ + γ)) = Tr(λαβ) + Tr(λγ) = α Tr(λβ) + Tr(λγ) = αf (β) + f (γ)

for every α ∈ F and β, γ ∈ K (where in the above we used Propositon B.5.17). This concludes 
one direction of the proposition.

To see the converse we employ a counting argument.  First note that if λ ̸= 0 then the 
function fλ(β) = Tr(λβ) is not identically zero.  (To see this, note that fλ(Z), viewed as a 
polynomial in Z has degree |K|/|F| and it is a non-zero polynomial since the coefficient of 
Z is non-zero.)  By linearity this implies that fλ ̸= fτ  if λ ̸= τ  since fλ − fτ = fλ−τ ̸= 0. 
So, including λ = 0, we have at least |K| distinct linear functions of the form fλ(·).  We now 
note there are also at most |K| such functions.  To see this let β1, . . . , βn ∈ K be F-linearly 
independent elements of K(i.e., ∑︁n
i=1 αiβi ̸= 0 if (α1, . . . , αn) ∈ Fn \ {0}). Since K is a degree 
n extension of F we know such a sequence exists and furthermore the βi’s generate K in that 
for every β ∈ K there exist α1, . . . , αn ∈ F such that β = ∑︁
i αiβi.  We note that a linear 
function L : K → F is completely determined by its values at β1, . . . , βn,  since for every 
β = ∑︁
i αiL(βi).  Thus the 
number of linear functions is upper bounded by |{(L(β1), . . . , L(βn)) ∈ Fn}| ≤ |F|n = |K|. 
We conclude that these are exactly |K| functions that are F-linear from K → F, and these 
are exactly the Trace functions.

i αiβi ∈ K with α1, . . . , αn ∈ F, we have L(β) = L(∑︁

i αiβi) = ∑︁

B.6  Algorithmic aspects of Finite Fields

In this section we show how finite fields may be represented and field operations computed 
efficiently.

Let q = pt for prime p and positive integer t.  We consider how to work with Fq — the 

field on q elements.

We start by noticing that if O(q2) space is not imposing,  then four tables — one for 
addition, and one for multiplication, and one each for additive and multiplicative inverses 
would suffice for working with fields, with each field operation now requiring a single table 
look up.  In what follows we give more succinct descriptions that still allow moderately fast 
(some polynomial in log q) operations.

205

 
 


<!-- pdf-page: 218 -->
B.6.1  Prime Fields

We start with the case of t = 1. Here there is not much to do. The most natural representa­
tion of the field is by specifying the prime p which takes log2 p + 1 = log q + 1 bits to specify. 
The most complex part of addition and multiplication is the computation of the remainder 
of the operation modulo p, and this takes at most O((log p)2) steps by the naive method. 
More sophisiticated algorithms can bring this compexity down to O((log p)(log log p)2).

B.6.2  General fields as vectors

For general fields, we can adopt one of two approaches.  The first of these uses less of the 
knowledge that we have about finite fields, but helps abstract away many issues. In this view 
we use the isomorphism between Fpt and Ft
p to represent elements of the former as vectors 
in Ft
p.  This, thus represents elements of Fq by O(log q) bits which is nice.  This also tells us 
how to add in Fq since it is simply coordinatewise Fp-addition.  However this representation 
by  itself  is  not  sufficient  to  do  Fq-multiplication.  To  multiply  elements  we  enhance  this 
representation by maintaining t2 vectors wij ∈ Ft
p with wij = ei ·ej where the ei’s are the unit 
vectors (so ei = (0, . . . , 0, 1, 0, . . . , 0) is 1 in the ith coordinate and zero elsewhere). Now given 
u = (u1, . . . , ut) and v = (v1, . . . , vt) we can compute u · v = ∑︁t
j=1 uivjwij.  This leads 
to a roughly O(t3(log p)2) = O((log q)3) time algorithm for multiplying in Fq while requiring 
O(t3 log p) bits to store p and the vectors wij.  While not the most efficient representation, 
this may afford a clean representation that may be sufficient in several settings.

∑︁t

i=1

B.6.3  General fields as polynomial rings
Our final representation uses the fact that the field Fpt is isomorphic to Fp[X]/(g) for any 
irreducible polynomial g of degree t.  Here, a field element is simply a polynomial in Fp[X]
of degree strictly less than t which is maintained as a vector of coefficients.  Addition is just 
coordinate-wise addition, whereas multiplication is polynomial multiplication followed by a 
remainder computation modulo g. Thus addition takes time O(t(log p)2) while mutliplication 
naively takes time O(t2(log p)2). The only ingredients that need to be remembered to do field 
operations are the integer p and the polynomial g ∈ Fp[X], all of which take O(t log p) bits. 
So this representation definitely outperforms the generic representation via vector spaces in 
almost all senses (though we might find the vector space view helpful when discussing certain 
operations with codes).

B.6.4  Finding primes and irreducible polynomials

The final question that remains to be discussed is how hard is to find the ingredients that 
describe a field.  Of course, this depends on how the field is described, and the most natural 
one may be by giving the cardinality q of the field.

Given  q = pt,  it  is  straightforward  to  enumerate  all  candidate  (p, t)  pairs  such  that 
q = pt — there are only log q possible values of t and thus log q such integers.  Only one of 

206



<!-- pdf-page: 219 -->
these, the one with the largest t could correspond to prime p.  Testing if an integer is prime 
can be done efficiently with randomization, and thanks to a recent breakthrough [1] even 
deterministically in time polynomial in log q.

When t = 1 no further works needs to be done.  If t > 1 one needs to find an irreducible 
polynomial g of degree t and this can be a challenge.  There are several possible solutions 
here:

Randomized It is known (and can actually be proved with a little effort, given the ingredi­
ents of this chapter) that a random polynomial g ∈ Fp[X] of degree t is irreducible with 
probability at least 1/t.  Furthermore, irreducibility can be tested (see next section) 
in time poly(log q).  Thus repeatedly sampling random polynomials till an irreducible 
polynomial is found takes expected time poly(log q).  (See Algorithm 5.1.1.)

Deterministic Shoup [66] gave an algorithm to deterministically find an irreducible poly­
nomial of degree t in Fp[X] in time poly(t, p).  Notice that this dependence is slower 
than one may hope for in terms of p, but works well when p is small (say, smaller than 
t).

Explicit In some rare cases, i.e., a few choices of p and t, explicit polynomials are known 
that are irreducible.  These may be used when the field size seems appropriate.  One 
such family of irreducible polynomials is given in the following proposition.

Proposition B.6.1   ([47]). Let p = 2 and t = 2 · 3ℓ for any non-negative integer ℓ.  Then 
the polynomial X t + X t/2 + 1 is irreducble in F2[X].

B.7  Algorithmic aspects of Polynomials

In this section we review basic facts about algorithmic aspects of manipulating polynomials. 
We start with basic tasks and move to more complex tasks ending with factoring and root-
finding.

B.7.1  Adding, Multiplying, Dividing

Given  two  polynomials  f, g ∈ Fq[X]  of  degree  at  most  n,  they  can  be  added  with  O(n)
operations in Fq and no more needs to be said.  f  and g can also be multiplied with O(n2)
operations by the standard long multiplication.  Similarly the quotient and remainder ob­
tained when dividing f  by g can be computed wih O(n2) operations using the long division 
algorithm.  More efficient algorithms do exist for both these tasks making O(n(log n)c) field 
operations, for some constant c.  (See [74] for this and other references for this section.)

207



<!-- pdf-page: 220 -->
B.7.2  Greatest Common Divisor

Perhaps the most surprising algorithm in algebra is that of finding greatest common divisors 
(of integers or polynomials), and would be even more so, if it were not for over 2000 years 
of exposure.  To explain, let us look at the definition of the problem.

Definition B.7.1  (Greatest Common Divisor). Given polynomials f, g ∈ F[X], their greatest 
common  divisor,  denoted  gcd(f, g),  is  the  maximal  degree  polynomial  h(X)  with  leading 
coefficient being 1 such that h divides f  and g.

The natural algorithm for finding gcd(f, g) would be to factor f  and g into irreducible 
factors, and then to take all common factors (with multiplicity) and take their product to 
get h.  Unfortunately this reduces gcd to factoring which goes in the wrong direction.  (As 
we will see below, factoring can also be solved efficiently for polynomials, but by reduction 
to gcd computation.)

But fortunately, we can employ Euclid’s algorithm which uses the following algorithmic 
reduction:  If deg(g) < deg(f ) and g does not divide f ,  then gcd(f, g) = gcd(g, r) where 
f = q · g + r with deg(r) < deg(g) is as given by the division algorithm.  This simple fact 
turns out to be algorithmically effective reducing the (sum of the) degree of the polynomials 
in a single step of polynomial division, and thus leading to a polynomial time algorithm for 
finding the greatest common divisor.

Once again the steps of this algorithm can be combined in clever ways to get an imple­

mentation in O(n(log n)c) time.

B.7.3  Factoring and Root-Finding

Finally, one of the most striking tasks related to polynomials that turns out to have a poly­
nomial time algorithm is the factorization of polynomials.  Polynomials, even multivariate 
ones, can be factored extremely efficiently with randomization and this is a consequence of 
many years of research in algebraic computing.  We won’t give the strongest results here, 
since even stating the result is non-trivial. For our purposes it will suffice to know that poly­
nomials in Fq[X] of degree n can be factored in time poly(n, log q).  We state this general 
result, and prove a very special case of it.

Theorem B.7.2. There exists a constant c and a randomized algorithm running in expected 
time O((n log q)c) that factors polynomials of degree n in Fq[X].  Furthermore, if q = pt for 
prime t, then there is a deterministic algorithm with running time O((npt)c) for factoring.

To  give  an  idea  behind  this  powerful  algorithm,  we  consider  a  simple  special  case  of 

root-finding.

Definition  B.7.3   (Root-Finding  Problem).  The  input  to  the  root  finding  problem  is  a 
polynomial f ∈ Fq[X] of degree at most n (given as a list of coefficients f0, . . . , fn ∈ Fq). 
The task is to find all α ∈ Fq that are roots of f , i.e., to output the set {α ∈ Fq|f (α) = 0}.

208



<!-- pdf-page: 221 -->
We now turn towards the root-finding algorithm.  The algorithm relies crucially on the 
algorithm for computing greatest common divisors (mentioned in the previous section) and 
two additional facts. First we use the fact X q − X = ∏︁
(X − α) to algorithmic advantage 
as follows.

α∈Fq

Lemma B.7.4. A polynomial f ∈ Fq[X] has a root in Fq if and only if gcd(f, X q − X) ̸= 1.
The proof is immediate.  If f  has a root α, then X − α divides gcd(f, X q − X)
Proof. 
and so their gcd can’t be trivial. Conversely a factor of X q − X is of the form ∏︁
α∈S(X − α)
for some S ⊆ Fq, and so gcd(f, X q − X) must be of this form.  If the gcd is non-trivial, then 
S must be non-empty implying that for every α ∈ S we have X − α divides f  and thus f
has a root in S ⊆ Fq.

The step above is almost algorithmic, but to verify this, we need to stress that the gcd
of f  and X q − X can be computed in time polynomial in deg(f ) and log q.  We explain how 
this can be done in the next few paragraphs, taking a detour on sparse polynomials.  But 
assuming this can be done, this provides a natural starting point for a root finding algorithm. 
Given f  we compute g = gcd(f, X q − X).  If g ̸= 1, then we take the set S1 of roots of g
and the set S2 of roots of f /g and output S1 ∪ S2.  The set S2 can be computed recursively 
(since f /g has smaller degree than f ), but for S1 we need some new ideas to determine how 
to compute the roots of g, when g splits into linear and distinct factors over Fq.  To get to 
this point we will use the fact that X q − X splits into some high-degree sparse factors and 
this will turn out to be crucial to finding S.  Indeed the sparsity of X q − X and its factors 
are heavily used concepts and we now take a detour to explain these effects.

Sparse high degree polynomials
We start with some terminology.  We say that a polynomial h ∈ F[X] is t-sparse if at most 
t of its coefficients are non-zero.  Every polynomial h is thus (deg(h) + 1)-sparse, but often 
the sparsity can be smaller, and this will be useful.  One sparse polynomial that is already 
motivated by the earlier discussion is X q − X, which is 2-sparse.  We will see a few more 
below.

Lemma  B.7.5.  Let  f ∈ F[X]  be  a  polynomial  of  degree  n  and  let  h ∈ F [X]  be  a  t-
sparse  polynomial  of  degree  D.  Then  h mod f   and  gcd(f, h)  can  be  computed  in  time 
poly(n, t, log D).

It obviously suffices to compute h mod f  in time poly(n, t, log D) and then one 
Proof. 
can use  Euclid’s algorithm  to  compute  gcd(f, h) = gcd(f, h mod f ) in  time  poly(n).  In 
turns out that if h = ∑︁t
i=1 hiX di and we can compute hiX di mod f  in time poly(n, log di)
for  every  i,  then  we  can  add  the  results  in  time  poly(n, t)  to  get  h mod f .  Finally,  we 
note that X d mod f  can be computed by repeated squaring.  Let d = ∑︁log2 d
j=0 dj2j.  We can 
first compute the sequence of polynomials gj = X 2j
j−1 mod f  by repeatedly 
squaring the output of the previous step.  Then we can compute X d mod f = ∏︁log2 d
j=0 (gj)dj
by using log d more multiplications, yielding the desired result.

mod f = g2

209

 
 


<!-- pdf-page: 222 -->
The lemma above shows that sparse polynomials can be used effectively.  The following 
lemma shows that the central sparse polynomial also has sparse factorizations, and this will 
be useful later.

Proposition B.7.6.

1. Let Fq be a field of odd characteristic (and so q is odd). Then X q − X = X · (X (q−1)/2 −
1) · (X (q−1)/2 + 1).  In particular X q − X factors into three 2-sparse polynomials of 
degree at most q/2.

2. Let q = 2t for integer t ≥ 2.  Then (X q − X) = Tr(X) · (Tr(X) − 1) where Tr(X) =
 is the Trace map from Fq to F2. In particular 

T rFq→F2(X) = X + X 2 + X 4 + · · · + X 2r−1
X q − X factors into two (2 + log2 q)-sparse polynomials of degree q/2.

Proof. 
(q − 1)/2 is an integer.

The case of odd q is obvious by inspection.  Only aspect to be stressed is that 

For the case of even q, we use the fact that the trace map is a map from Fq to F2. So every 
α ∈ Fq satisfies Tr(α) = 0 or Tr(α) = 1.  It follows that X − α divides Tr(X) · (Tr(X) − 1)
for every α.  Consequently X q − X divides Tr(X) · (Tr(X) − 1).  The identity X q − X =
Tr(X) · (Tr(X) − 1) now follows from the fact that both polynomials have the same degree 
and have leading coefficient 1.

The existence of such sparse polynomials with many roots is one of the remarkable aspects 
of finite fields and leads to many algorithmic effects.  We demonstrate this by showing how 
this is utilized in root-finding.

Univariate Root finding algorithm

We now complete the root-finding algorithm.  Recall that by letting g = gcd(f, X q − X) we 
can reduce to the case of polynomials that split into distinct linear factors in Fq.  We now 
focus on this case.  We will also focus on the case of odd q for simplicity, though all we will 
use is the fact that X q − X splits into sparse factors of degree at most q/2.

If we were lucky, then g would have two roots α and β with X − α dividing (X (q−1)/2 − 1)
and X − β not dividing it.  Then we would have that g1 = gcd(g, X (q−1)/2 − 1) would be a 
non-trivial factor of g and we could recurse on g1 and g2 = g/g1. The key to the randomized 
root-finding is that by an appropriate affine change of variables, we can try to arrange to be 
“lucky”.

Specifically, fix a ∈ F∗

q and b ∈ Fq and let ga,b(X) = g((X − b)/a). We have the following 

proposition.

Proposition B.7.7. Let g ∈ Fq[X] have α ̸= β as its roots.  Then we have:

1. The coefficients of ga,b can be computed efficiently given a, b and the coefficients of g.

2. ga,b has aα + b and aβ + b as its roots.

210

 


<!-- pdf-page: 223 -->
3. If a ∈ F∗

q and b ∈ Fq are chosen uniformly at random independently, then the probability 

that exactly one of aα + b and aβ + b is a root of X (q−1)/2−1 is at least 1/2.

Parts (1) and (2) are straightforward to verify.  For part (3) we note that for any 
Proof. 
q and b ∈ Fq such that 
pair of distinct elements γ, δ ∈ Fq there is exactly one pair a ∈ F∗
aα + b = γ and aβ + b = δ. Since the fraction of distinct pairs γ, δ ∈ Fq such that exacty one 
of them comes from a set of size (q − 1)/2 (the set of roots of X (q−1)/2 − 1) is at least 1/2
(the exact formula is 1/2 + 1/(2q)) we have that the probability that exactly one of aα + b
and aβ + b is a root of X (q−1)/2−1 is at least 1/2.

We  conclude  by  giving  the  full  root-finding  algorithm  and  summary  of  analysis  of  its 

run-time.

Algorithm B.7.1 Root-Find(Fq, f )
Input: Fq, f (X) ∈ Fq[X]
Output: Fq roots of f (X)

1: g ← gcd(f, X q − X)
2: if g = 1 then
return ∅
3:  
4: return Linear-Root-Find(Fq, g) ∪ Root-Find(Fq, (f /g))

Algorithm B.7.2 Linear-Root-Find(Fq, g)
Input: Fq, g(X) ∈ Fq(X)
Output: Fq roots of g(X) if g(X) divides X q − X

1: if deg(g) = 1 then
2:  

return  {α} where g = X − α

q and b ∈ Fq uniformly independently

3: repeat
4:   Pick a ∈ F∗
ga,b ← g((X − b)/a)
5:  
h1 ← gcd(ga,b, X (q−1)/2−1)
6:  
g1 ← h1(aX + b)
7:  
8: until 0 < deg(g1) < deg(g)
9: return Linear-Root-Find(Fq, g1) ∪ Linear-Root-Find(Fq, (g/g1))

Lemma  B.7.8.  Root-Find(Fq, f )  outputs  the  multiset  of  roots  of  f   in  expected  time 
poly(n, log q).

Let n = deg(f ).  It is straightforward to see that Root-Find makes at most n
Proof. 
calls to Linear-Root-Find. (This is a very weak estimate, but we leave out optimizations 

211

 


<!-- pdf-page: 224 -->
here, in favor of simplicity.) By Proposition B.7.7, Part (3), we have that the loop in Linear-
Root-Find will be executed an expected constant number of times before a non-trivial split 
is found.  Finally, the degrees of the polynomials in the two recursive calls add up to deg(g)
and so this leads to a tree of recurvie calls of size at most n with each internal node and 
leaf performing poly(n, log q) work (to compute the various gcds, and the transformation of 
variables).  Thus the overall expected running time is poly(n, log q).

For the curious reader we also give a brief sketch of the deterministic algorithm running 
in  time  poly(n, p, t)  where  q = pt  for  prime  p.  Given  g(X) ∈ Fq[X]  this  algorithm  first 
find a polynomial f (X) with 0 < deg(f ) < deg(g) such that f (X)p − f (X) ≡ 0 mod g(X). 
The reason this can be found efficiently is that the search for f  is a linear system over Fp
(we omit the details of this step).  And the reason such a polynomial even exists is that if 
g(X) = g1(X) · g2(X) where g1 and g2 are relatively prime then choosing any a ̸= b ∈ Fp
and letting f (X) = a mod g1(X) and f (X) = b mod g2(X) yields such a polynomial.  By 
the  Chinese  Remainder  Theorem  such  a  polynomial  exists  and  has  degree  less  than  that 
of g1(X) · g2(X).  So the linear system we wish to solve has a solution and in such a case 
a  solution  can  be  found  efficiently.  Having  found  such  an  f ,  we  write  f (X)p − f (X) =
∏︁
a(f (X) − a) and note that gcd(g(X), f (X) − a) must be nontrivial for some a ∈ Fp, since 
gcd(g(X), ∏︁
a(f (X) − a)) = g(X), but for every a, g(X) does not divide f (X) − a.  Thus 
enumerating over all a ∈ Fp and computing gcd’s gives a non-trivial factorization of g. (This 
settles the problem when g has a non-trivial factorization into relatively prime elements g1
and g2, which is true in our case when we are only interested in finding all the roots and 
work  with  gcd(g(X), X q − X).)  This  leads  to  a  deterministic  algorithm  running  in  time 
poly(n, p, t).

Bivariate Root Finding
Given a bivariate polynomial R(X, Y ) ∈ Fq[X, Y ], we say that a polynomial P (X) is a root 
of  R(X, Y )  if  Y − P (X)  divides  R(X, Y ).  We  show  below  how  to  solve  the  root-finding 
problem for bivariate polynomials in polynomial time.

Theorem B.7.9. There exists a randomized algorithm that,  given a bivariate polynomial 
R(X, Y ) ∈ Fq[X, Y ] of degree at most D (say, as a list of coefficients), outputs a list of all its 
roots in expected time polynomial in D and log q.  If q = pt, there also exists a deterministic 
algorithm to output all roots in time polynomial in p, t and D.

Proof. 
The algorithm uses a simple reduction to the univariate case.  We find a monic 
irreducible polynomial of F (X) of degree N  where D < N ≤ O(D).  We then consider the 
field FQ = Fq[X] mod F (X) and view R(X, Y ) as a polynomial RX(Y ) ∈ FQ[Y ].  We find 
the roots of RX(Y ) (using the univariate root-finding algorithm from Lemma B.7.8 or the 
deterministic root-finder implied by Theorem B.7.2). Let α1, . . . , αs ∈ FQ be the roots of RX. 
Using FQ = Fq[X] mod F (X) we interpret α1, . . . , αs as polynomials A1(X), . . . , As(X) ∈
Fq[X].  We  report  all  Ai(X)  such  that  Y − Ai(X)  divides  R(X, Y ).  This  completes  the 
description of the algorithm and we argue correctness and run time below.

212

 


<!-- pdf-page: 225 -->
Since  the  algorithm  checks  if  Ai(X)  is  a  root  before  outputting  it,  it  is  clear  that  it 
outputs  a  subset  of  the  roots.  To  prove  correctness  we  only  need  to  show  every  root  is 
included in the output.  In particular we need to show that if Y − P (X) divides R(X, Y )
and  α = P (X) mod F (X)  represents  the  corresponding  element  of  FQ  then  Y − α  also 
divides RX(Y ).  Let h(X, Y ) ∈ Fq[X, Y ] be such that R(X, Y ) = h(X, Y )(Y − P (X)).  Let 
hX(Y ) = h(X, Y ) mod F (X) be  an  element of  FQ[Y ].  We now  have  hX(Y ) · (Y − α) =
R(X, Y ) mod F (X) = RX(Y ), as desired.  This proves correctness.

To argue the run time,  note that the algorithm F (X) can be found in expected time 
polynomial  in  N   and  log q,  or  deterministically  in  time  poly  in  N ,  p  and  t.  Once  F   is 
found  the  univariate  root-finding  takes  a  number  of  steps  that  is  polynomial  in  N   and 
log Q = N log q, where each step is a field operation in FQ which may take time polynomial 
in N log q. Using N = D +1, we get that the overall expected run time remains a polynomial 
in D and log q.  Similarly the determinstic run time is also polynomial in D, t and p, where 
we use the deterministic root-finder implied by Theorem B.7.2.

B.8  Exercises

Exercise B.1. Let R be a commutative ring.  Then prove the following:

1. If a is a unit in R, then b · a = 0 if and only if b = 0.

2. Using the previous part or otherwise, prove Proposition B.3.6.

Exercise B.2. Argue that every finite field F has a finite characteristic char(F).

Exercise B.3. Let F be a field with p elements for prime p.  Argue that the map 1F → 1 can 
be extended to an isomorphism between F and Zp.

Exercise B.4. Let G be an abelian group with identity 1 and let a ∈ G.

1. Argue that the map x → a · x for x ∈ G is a bijection.

2. Argue that

∏︂

x∈G

x = an ·

∏︂

x.

x∈G

3. Using the previous part or otherwise prove Proposition B.5.4 for abelian groups.

Exercise B.5. Let p be a prime and let 0 ≤ i ≤ p.  The show that

)︃

(︃p
i

mod p =

{︄
1
0

 if i = p or i = 0
 otherwise

.

213

 


<!-- pdf-page: 226 -->
Exercise  B.6.  In  this  exercise  we  will  argue  that  for  every  k  that  divides  n,  we  have 
N (Zn, k) = k, i.e.  show that the number of elements of Zn that have an order that divides k
is exactly k.  Consider the following:

1. Prove that

is a sub-group of Zn.

Sk =

{︂

a ·

n
k

|0 ≤ a < k

}︂

2. Argue that any b ∈ Zn that has an order that divides k satisfies, k · b mod n = 0.

3. Argue that any b ∈ Zn \ Sk it must be the case that k · b mod n ̸= 0.

4. Argue that any b ∈ Sk has an order that divides k.

5. Using the above parts or otherwise, argue that Sk contains all elements of Zn with an 

order that divides k.  Conclude that N (Zn, k) = k.

Exercise B.7. If k divides n, then show that X k − 1 divides X n − 1.

Exercise B.8. Let K (cid:3) F and let α be an F-generator of K.  Let p be the minimal polynomial 
in F[X] such that p(α) = 0.  Argue that have p is irreducible.

Exercise B.9. Let K (cid:3) F and let α be an F-generator of K.  Let p be the minimal polynomial 
in  F[X]  such  that  p(α) = 0.  Argue  that  there  is  an  isomorphism  between  K  and  F[x]/p
obtained by fixing F (cid:1) K and letting α ↦→ X, which can be extended to all other elements.

Exercise B.10. Using notation in proof of Theorem B.5.15, prove that the map α ↦→ β can 
be extended to an isomorphism between K and L.

Exercise B.11. Argue that for any β ∈ Fqn, the norm function satisfies N (β)q = N (β).

214


