<!-- generated-by: proofmatch Claude repair -->
<!-- source-pdf-sha256: 7251cb8e4bc5048cfd6ad113f14bc6d6d3c5a079e5dc33430b1cf36df5c21005 -->

<a id="pdf-7251cb8e4bc5-p001-b001"></a>
<!-- pdf-source: page=1; block=1; confidence=0.95 -->
# Essential Coding Theory

Textbook by Venkatesan Guruswami, Atri Rudra, and Madhu Sudan; dated April 19, 2026. Author affiliation: Dept. of Computer Science and Engineering, University at Buffalo, SUNY; work supported by NSF CAREER grant CCF-0844796. No mathematical content.

<a id="pdf-7251cb8e4bc5-p003-b001"></a>
<!-- pdf-source: page=3; block=1; confidence=0.95 -->
## Foreword

Book derived from coding-theory lecture notes taught by the three authors at various institutions. Version dated April 19, 2026; NSF CAREER grant CCF-0844796 support acknowledged; ©2019, licensed under Creative Commons BY-NC-ND 3.0. No mathematical content.

<a id="pdf-7251cb8e4bc5-p005-b001"></a>
<!-- pdf-source: page=5; block=1; confidence=0.97 -->
# Contents

<a id="pdf-7251cb8e4bc5-p005-b002"></a>
<!-- pdf-source: page=5; block=2; confidence=0.93 -->
**Part I. The Basics.** Table-of-contents listing. Ch. 1 *The Fundamental Question* (§1.1 Overview; §1.2 Some Definitions and Codes; §1.3 Error Correction; §1.4 Distance of a Code; §1.5 Hamming Code; §1.6 Hamming Bound; §1.7 Generalized Hamming Bound; §1.8 Family of codes; §1.9 Exercises; §1.10 Bibliographic Notes). Ch. 2 *Linear Codes* (§2.1 Groups and Finite Fields; §2.2 Vector Spaces and Linear Subspaces; §2.3 Linear Codes and Basic Properties; §2.4 Hamming Codes; §2.5 Efficient Decoding of Hamming codes; §2.6 Dual of a Linear Code; §2.7 Exercises; §2.8 Bibliographic Notes). Ch. 3 *Probability as Fancy Counting and the q-ary Entropy Function* (§3.1 A Crash Course on Probability; §3.2 The Probabilistic Method; §3.3 The q-ary Entropy Function; §3.4 Exercises; §3.5 Bibliographic Notes).

<a id="pdf-7251cb8e4bc5-p005-b003"></a>
<!-- pdf-source: page=5; block=3; confidence=0.90 -->
**Part II. The Combinatorics** (part heading only on this page).

<a id="pdf-7251cb8e4bc5-p006-b001"></a>
<!-- pdf-source: page=6; block=1; confidence=0.93 -->
**Part II. The Combinatorics.** Ch. 4 *What Can and Cannot Be Done–I* (§4.1 Asymptotic Version of the Hamming Bound; §4.2 Gilbert–Varshamov Bound; §4.3 Singleton Bound; §4.4 Plotkin Bound; §4.5 Exercises; §4.6 Bibliographic Notes). Ch. 5 *The Greatest Code of Them All: Reed–Solomon Codes* (§5.1 Polynomials and Finite Fields; §5.2 Reed–Solomon Codes; §5.3 Maximum Distance Separable Codes and Properties; §5.4 Exercises; §5.5 Bibliographic Notes).

<a id="pdf-7251cb8e4bc5-p006-b002"></a>
<!-- pdf-source: page=6; block=2; confidence=0.93 -->
**Part III. The Codes.** Ch. 6 *When Polynomials Save the Day: Polynomial Based Codes* (§6.1 The generic construction; §6.2 The low degree case; §6.3 The case of the binary field; §6.4 The general case; §6.5 Exercises; §6.6 Bibliographic Notes). Ch. 7 *From Large to Small Alphabets: Code Concatenation* (§7.1 Code Concatenation: The basic idea; §7.2 Zyablov Bound; §7.3 Advanced Concatenation and Strongly Explicit Constructions; §7.4 Summary of concatenation; §7.5 Exercises; §7.6 Bibliographic Notes).

<a id="pdf-7251cb8e4bc5-p006-b003"></a>
<!-- pdf-source: page=6; block=3; confidence=0.93 -->
**Part IV. The Algorithms.** Ch. 8 *Efficient Decoding of Reed–Solomon Codes* (§8.1 Unique decoding of Reed–Solomon codes; §8.2 List Decoding Reed–Solomon Codes; §8.3 Extensions; §8.4 Exercises; §8.5 Bibliographic Notes).

<a id="pdf-7251cb8e4bc5-p007-b001"></a>
<!-- pdf-source: page=7; block=1; confidence=0.95 -->
**Appendix A. Some Useful Facts** (p. 189). Subsections: A.1 Some Useful Inequalities (p. 189); A.2 Some Useful Identities and Bounds (p. 191).

<a id="pdf-7251cb8e4bc5-p007-b002"></a>
<!-- pdf-source: page=7; block=2; confidence=0.95 -->
**Appendix B. Basic Algebraic Algorithms** (p. 193). Subsections: B.1 Executive Summary (193); B.2 Groups, Rings, Fields (193); B.3 Polynomials (194); B.4 Vector Spaces (196); B.5 Finite Fields (199); B.6 Algorithmic aspects of Finite Fields (205); B.7 Algorithmic aspects of Polynomials (207); B.8 Exercises (213).

<a id="pdf-7251cb8e4bc5-p009-b001"></a>
<!-- pdf-source: page=9; block=1; confidence=0.95 -->
**List of Figures** (front matter, no mathematical content). Chapter 1: 1.1 decoding "Akash English" example; 1.2 coding process; 1.3 bad example for unique decoding; 1.4 illustration for the Hamming Bound proof (pp. 1, 7, 14, 18). Chapter 3: 3.1 the q-ary entropy function (p. 58). Chapter 4: 4.1 Hamming and Gilbert–Varshamov (GV) bounds for binary codes; 4.2 Gilbert's greedy algorithm (first five iterations); 4.3 new-code construction in the Singleton-bound proof; 4.4 Hamming, GV and Singleton bounds for binary codes; 4.5 R vs δ tradeoffs for binary codes (pp. 71, 72, 76, 77, 79). Chapter 7: 7.1 concatenated code C_out ∘ C_in (p. 133); 7.2 Zyablov bound for binary codes (p. 135). Chapter 8: 8.1 received word in 2-D space (148); 8.2 closest polynomial to a received word (149); 8.3 rate R vs correctable error fraction tradeoff for Algorithm 8.2.1 (158); 8.4 received word in 2-D space, second Reed–Solomon (160); 8.5 interpolating polynomial Q(X,Y) for Fig. 8.4 (161); 8.6 the two output polynomials shown in blue (161); 8.7 R vs correctable error fraction for Algorithms 8.2.1 and 8.2.2 (163); 8.8–8.10 multiplicity of 1, 2, 3 (164, 165, 165); 8.11 received word in 2-D space, third Reed–Solomon (166); 8.12 interpolating polynomial Q(X,Y) for Fig. 8.11 (166); 8.13 the five output polynomials shown in blue (167).

<a id="pdf-7251cb8e4bc5-p011-b001"></a>
<!-- pdf-source: page=11; block=1; confidence=0.95 -->
# Part I: The Basics

<a id="pdf-7251cb8e4bc5-p013-b001"></a>
<!-- pdf-source: page=13; block=1; confidence=0.98 -->
# Chapter 1 — The Fundamental Question

<a id="pdf-7251cb8e4bc5-p013-b002"></a>
<!-- pdf-source: page=13; block=2; confidence=0.98 -->
## 1.1 Overview

<a id="pdf-7251cb8e4bc5-p013-b003"></a>
<!-- pdf-source: page=13; block=3; confidence=0.90 -->
Motivational prose: natural languages such as English carry built-in redundancy, so communication tolerates small errors (accents, mispronunciations). Illustrated by a child's imperfect speech still being understood.

<a id="pdf-7251cb8e4bc5-p013-b004"></a>
<!-- pdf-source: page=13; block=4; confidence=0.85 -->
**Figure 1.1.** Caption: decoding "Akash English" yields "I need little little (trail)mix."

<a id="pdf-7251cb8e4bc5-p014-b001"></a>
<!-- pdf-source: page=14; block=1; confidence=0.90 -->
Prose: redundancy enables recovery despite corruption. Error-correcting codes ("codes") deliberately add redundancy so original data is recoverable when parts are corrupted. Examples of use: Internet packets use CRC checksums [58] (a weak code, but effective via error-detection plus retransmission); telephone, cell phones, deep-space and satellite communication where retransmission is impossible; and communication over time via storage — CDs/DVDs, RAID [13], error-correcting memory [12], and bar codes such as UPS MaxiCode [11].

<a id="pdf-7251cb8e4bc5-p015-b001"></a>
<!-- pdf-source: page=15; block=1; confidence=0.95 -->
Communication model: a sender has $k$ message symbols to send over a noisy channel. It **encodes** them into $n$ symbols (a *codeword*) and transmits; the receiver gets an $n$-symbol *received word* and **decodes** to recover the $k$ message symbols. Encoding adds redundancy; decoding removes errors.

<a id="pdf-7251cb8e4bc5-p015-b002"></a>
<!-- pdf-source: page=15; block=2; confidence=0.93 -->
**Note (assumption).** Sender and receiver communicate only via the channel: apart from shared setup information about the code, they exchange no other information, and no message is a priori more likely than another (no side-channel).

<a id="pdf-7251cb8e4bc5-p015-b003"></a>
<!-- pdf-source: page=15; block=3; confidence=0.95 -->
**Question 1.1.1 (Main Question).** How much redundancy is needed to correct a given amount of errors? Goal: correct as many errors as possible using as little redundancy as possible.

<a id="pdf-7251cb8e4bc5-p015-b004"></a>
<!-- pdf-source: page=15; block=4; confidence=0.92 -->
Maximizing error correction and minimizing redundancy are opposing goals (more redundancy tolerates more errors); a formalization comes later in the chapter. Beyond the optimal tradeoff, the book seeks codes with efficient encoding/decoding, where *efficient* primarily means polynomial-time.

<a id="pdf-7251cb8e4bc5-p015-b005"></a>
<!-- pdf-source: page=15; block=5; confidence=0.97 -->
## 1.2 Some Definitions and Codes

<a id="pdf-7251cb8e4bc5-p015-b006"></a>
<!-- pdf-source: page=15; block=6; confidence=0.96 -->
**Definition 1.2.1 (Code).** A code of *block length* $n$ over an alphabet $\Sigma$ is a subset of $\Sigma^n$. The *alphabet size* is denoted $q = |\Sigma|$ ($q$ may depend on $n$).

<a id="pdf-7251cb8e4bc5-p016-b001"></a>
<!-- pdf-source: page=16; block=1; confidence=0.97 -->
**Remark 1.2.2.** An element of Σⁿ may be viewed as a sequence, a vector tuple, or a function f : [n] → Σ with f(i) = vᵢ. Sequences are most generic; vectors suit structured Σ (e.g. a field); functional form suits structured coordinate sets. For now the representation is immaterial.

<a id="pdf-7251cb8e4bc5-p016-b002"></a>
<!-- pdf-source: page=16; block=2; confidence=0.98 -->
A code C ⊆ Σⁿ with |C| = M can equivalently be viewed as a mapping

$$C : [M] \to \Sigma^n \tag{1.1}$$

where for integer M ≥ 1, [M] denotes {1, 2, …, M}.

<a id="pdf-7251cb8e4bc5-p016-b003"></a>
<!-- pdf-source: page=16; block=3; confidence=0.98 -->
**Definition 1.2.3 (Dimension of a code).** For a code C ⊆ Σⁿ, its dimension is

$$k \overset{\text{def}}{=} \log_q |C|.$$

<a id="pdf-7251cb8e4bc5-p016-b004"></a>
<!-- pdf-source: page=16; block=4; confidence=0.97 -->
Two binary codes (Σ = {0,1}) with |C| = 2⁴ = 16, messages being 4-bit vectors, are introduced. The **parity code** C⊕ maps (x₁,x₂,x₃,x₄) ∈ {0,1}⁴ to

$$C_\oplus(x_1,x_2,x_3,x_4) = (x_1,x_2,x_3,x_4,\, x_1 \oplus x_2 \oplus x_3 \oplus x_4) \tag{1.2}$$

appending the XOR (parity) of the message bits.

<a id="pdf-7251cb8e4bc5-p016-b005"></a>
<!-- pdf-source: page=16; block=5; confidence=0.97 -->
The **repetition code** repeats each message bit a fixed number of times; C₃,rep repeats each of 4 bits 3 times:

$$C_{3,\mathrm{rep}}(x_1,x_2,x_3,x_4) = (x_1,x_1,x_1,\,x_2,x_2,x_2,\,x_3,x_3,x_3,\,x_4,x_4,x_4). \tag{1.3}$$

<a id="pdf-7251cb8e4bc5-p017-b001"></a>
<!-- pdf-source: page=17; block=1; confidence=0.90 -->
Absolute redundancy n − k fails to distinguish (k=100, n=102) from (k=2, n=4), which use very different redundancy per message bit; this motivates a relative measure.

<a id="pdf-7251cb8e4bc5-p017-b002"></a>
<!-- pdf-source: page=17; block=2; confidence=0.95 -->
**Definition 1.2.4 (Rate of a code).** A code with dimension k and block length n has rate

$$R \overset{\text{def}}{=} \frac{k}{n}.$$

Higher rate means less redundancy; since k ≤ n, R ≤ 1 (and with k > 0, n < ∞, R > 0). C⊕ has rate 4/5 and C₃,rep has rate 1/3.

<a id="pdf-7251cb8e4bc5-p017-b003"></a>
<!-- pdf-source: page=17; block=3; confidence=0.95 -->
**1.3 Error Correction.** Encoding is defined before error correction.

<a id="pdf-7251cb8e4bc5-p017-b004"></a>
<!-- pdf-source: page=17; block=4; confidence=0.98 -->
**Definition 1.3.1 (Encoding function).** For C ⊆ Σⁿ, an equivalent description of C is an injective mapping E : [|C|] → Σⁿ, the encoding function.

<a id="pdf-7251cb8e4bc5-p018-b001"></a>
<!-- pdf-source: page=18; block=1; confidence=0.98 -->
**Definition 1.3.2 (Decoding function).** For a code C ⊆ Σⁿ, a mapping D : Σⁿ → [|C|] is a decoding function for C.

<a id="pdf-7251cb8e4bc5-p018-b002"></a>
<!-- pdf-source: page=18; block=2; confidence=0.97 -->
**Definition 1.3.3 (Hamming distance).** For u, v ∈ Σⁿ, the Hamming distance Δ(u,v) is the number of positions where u and v differ. The relative Hamming distance is δ(u,v) = (1/n)·Δ(u,v), lying in [0,1]. It depends only on the number of differences, not their nature; e.g. u = 00000, v = 10001 gives Δ(u,v) = 2, and w = 01010 gives Δ(u,w) = 2.

<a id="pdf-7251cb8e4bc5-p018-b003"></a>
<!-- pdf-source: page=18; block=3; confidence=0.97 -->
**Definition 1.3.4 (t-Error Channel).** An n-symbol t-error channel over Σ is a function Ch : Σⁿ → Σⁿ with Δ(v, Ch(v)) ≤ t for every v ∈ Σⁿ. (If u is transmitted and v received, Δ(u,v) errors occurred.)

<a id="pdf-7251cb8e4bc5-p018-b004"></a>
<!-- pdf-source: page=18; block=4; confidence=0.96 -->
**Definition 1.3.5 (Error Correcting Code).** For C ⊆ Σⁿ and integer t ≥ 1, C is t-error-correcting if there exists a decoding function D such that for every message m ∈ [|C|] and every t-error channel Ch, D(Ch(C(m))) = m. Example: a 1-error-correcting binary code must decode (0,0,0,0) from any of (0,0,0,0), (1,0,0,0), (0,1,0,0), (0,0,1,0), (0,0,0,1). Error detection is mentioned as a weaker form of recovery.

<a id="pdf-7251cb8e4bc5-p019-b001"></a>
<!-- pdf-source: page=19; block=1; confidence=0.95 -->
Diagram of the coding process: encoding function maps message $m \mapsto C(m)$; transmission through channel $\mathrm{Ch}$; decoding function maps received $v = \mathrm{Ch}(C(m)) \mapsto m$.

<a id="pdf-7251cb8e4bc5-p019-b002"></a>
<!-- pdf-source: page=19; block=2; confidence=0.95 -->
**Definition 1.3.6 (t-error-detecting code).** Let $C \subseteq \Sigma^n$ be a code and $t \ge 1$ an integer. $C$ is *t-error-detecting* if there exists a detecting procedure $D$ such that for every message $m$ and every received $v \in \Sigma^n$ with $\Delta(C(m), v) \le t$, $D(v) = 1$ if $v = C(m)$ and $D(v) = 0$ otherwise. Remark: a $t$-error-correcting code is also $t$-error-detecting, but not necessarily conversely (Exercise 1.1).

<a id="pdf-7251cb8e4bc5-p019-b003"></a>
<!-- pdf-source: page=19; block=3; confidence=0.93 -->
Introduces the erasure error model: an erased symbol is explicitly replaced by a special symbol "?" $\notin \Sigma$ rather than by another alphabet symbol (e.g. $(0,0,0,0)$ with the second symbol erased is received as $(0,?,0,0)$).

<a id="pdf-7251cb8e4bc5-p019-b004"></a>
<!-- pdf-source: page=19; block=4; confidence=0.95 -->
**Definition 1.3.7 (t-Erasure Channel).** An $n$-symbol $t$-erasure channel over $\Sigma$ is a function $\mathrm{Ch} : \Sigma^n \to (\Sigma \cup \{?\})^n$ such that $\Delta(v, \mathrm{Ch}(v)) \le t$ for every $v \in \Sigma^n$ (both arguments viewed in $(\Sigma \cup \{?\})^n$), and for every $i \in [n]$ with $v_i \ne \mathrm{Ch}(v)_i$ we have $\mathrm{Ch}(v)_i = {?}$. A coordinate $i$ with $\mathrm{Ch}(v)_i = {?}$ is called an *erasure*.

<a id="pdf-7251cb8e4bc5-p019-b005"></a>
<!-- pdf-source: page=19; block=5; confidence=0.95 -->
**Definition 1.3.8 (Erasure Correcting Code).** Let $C \subseteq \Sigma^n$ be a code and $t \ge 1$ an integer. $C$ is *t-erasure-correcting* if there exists a decoding function $D$ such that for every message $m \in [|C|]$ and every $t$-erasure channel $\mathrm{Ch}$, $D(\mathrm{Ch}(C(m))) = m$.

<a id="pdf-7251cb8e4bc5-p020-b001"></a>
<!-- pdf-source: page=20; block=1; confidence=0.95 -->
**§1.3.1 Error-Correcting Capabilities of Parity and Repetition Codes.** Reference codes: $C_\oplus$ with $q=2, k=4, n=5, R=4/5$; and $C_{3,\mathrm{rep}}$ with $q=2, k=4, n=12, R=1/3$.

<a id="pdf-7251cb8e4bc5-p020-b002"></a>
<!-- pdf-source: page=20; block=2; confidence=0.93 -->
**Decoding for $C_{3,\mathrm{rep}}$.** A codeword has form $(x_1,x_1,x_1,x_2,x_2,x_2,x_3,x_3,x_3,x_4,x_4,x_4)$ for $(x_1,x_2,x_3,x_4)\in\{0,1\}^4$. Given received $y\in\{0,1\}^{12}$, split into four consecutive 3-bit blocks $(y_1,y_2,y_3,y_4)$; output the majority bit of each block as the message bit. This decoder corrects any pattern of at most 1 error (Exercise 1.2).

<a id="pdf-7251cb8e4bc5-p020-b003"></a>
<!-- pdf-source: page=20; block=3; confidence=0.97 -->
**Proposition 1.3.9.** $C_{3,\mathrm{rep}}$ is a 1-error correcting code.

<a id="pdf-7251cb8e4bc5-p020-b004"></a>
<!-- pdf-source: page=20; block=4; confidence=0.93 -->
$C_{3,\mathrm{rep}}$ cannot correct two errors: if both errors fall in the same block yielding received block $010$, the original block could be $111$ or $000$, so no decoder recovers the message (decoder has no side information). Thus $C_{3,\mathrm{rep}}$ corrects exactly one error, under the assumption that error positions are arbitrary.

<a id="pdf-7251cb8e4bc5-p020-b005"></a>
<!-- pdf-source: page=20; block=5; confidence=0.90 -->
**Digression: Channel Noise.** Hamming's *Adversarial Noise Model*: any error pattern may occur provided the total number of errors is bounded; location and nature of errors are arbitrary. The atomic unit of error is one alphabet symbol — e.g. pattern $(1,0,1,0,0,0)$ over $\{0,1\}$ has two errors.

<a id="pdf-7251cb8e4bc5-p021-b001"></a>
<!-- pdf-source: page=21; block=1; confidence=0.90 -->
The same pattern $(1,0,1,0,0,0)$ viewed over alphabet $\{0,1\}^3$ as $((1,0,1),(0,0,0))$ has only one error, since $(0,0,0)$ is the zero element. Thus enlarging the alphabet changes the adversarial noise model; error correction over a larger alphabet is generally easier.

<a id="pdf-7251cb8e4bc5-p021-b002"></a>
<!-- pdf-source: page=21; block=2; confidence=0.90 -->
Alternate model: at most 1 error per contiguous 3-bit block. Then a transmitted $C_{3,\mathrm{rep}}$ codeword suffers at most four errors, and the per-block majority decoder recovers it for any such pattern — whereas under worst-case noise it corrects at most one error. Illustrates that error-correcting capability depends on the noise model.

<a id="pdf-7251cb8e4bc5-p021-b003"></a>
<!-- pdf-source: page=21; block=3; confidence=0.93 -->
Stochastic model: the binary symmetric channel with crossover probability $0 \le p \le 1$, denoted $\mathrm{BSC}_p$ (Shannon). Each bit of a transmitted binary codeword flips independently with probability $p$.

<a id="pdf-7251cb8e4bc5-p021-b004"></a>
<!-- pdf-source: page=21; block=4; confidence=0.88 -->
Hamming's and Shannon's models are two extremes: Hamming assumes no channel knowledge beyond a bound on total errors; Shannon assumes complete knowledge of noise generation. The book considers only these two; it focuses on the worst-case (adversarial) model, noting that a code working over worst-case noise works over most other models with the same amount of noise.

<a id="pdf-7251cb8e4bc5-p021-b005"></a>
<!-- pdf-source: page=21; block=5; confidence=0.93 -->
$C_\oplus$ cannot correct even one error under worst-case noise: for received $y = 10000$, an error is known to have occurred but the flipped bit is undetermined, since codewords $u = 00000$ and $v = 10001$ each differ from $y$ in exactly one bit; with no side information no decoder can determine the transmitted codeword.

<a id="pdf-7251cb8e4bc5-p022-b001"></a>
<!-- pdf-source: page=22; block=1; confidence=0.95 -->
C⊕ cannot correct even one error, but it can *detect* one error, motivating the error-detector Algorithm 1.3.1.

<a id="pdf-7251cb8e4bc5-p022-b002"></a>
<!-- pdf-source: page=22; block=2; confidence=0.92 -->
**Algorithm 1.3.1 (Error Detector for Parity Code).** Input: received word $y=(y_1,y_2,y_3,y_4,y_5)$. Output: $1$ if $y\in C_\oplus$, else $0$.
1. $b \leftarrow y_1\oplus y_2\oplus y_3\oplus y_4\oplus y_5$.
2. return $1\oplus b$.

<a id="pdf-7251cb8e4bc5-p022-b003"></a>
<!-- pdf-source: page=22; block=3; confidence=0.93 -->
If no error occurs, $y_i=x_i$ ($1\le i\le 4$) and $y_5=x_1\oplus x_2\oplus x_3\oplus x_4$, so $b=0$ and the output is $1$. If a single error occurs (one flipped $y_i$, $i\le4$, or a flipped $y_5$), then $b=1$. The argument extends to the following result (Exercise 1.4).

<a id="pdf-7251cb8e4bc5-p022-b004"></a>
<!-- pdf-source: page=22; block=4; confidence=0.97 -->
**Proposition 1.3.10.** The parity code $C_\oplus$ can detect an odd number of errors.

<a id="pdf-7251cb8e4bc5-p022-b005"></a>
<!-- pdf-source: page=22; block=5; confidence=0.94 -->
Revisiting the codewords $u=00000$ (message $0000$) and $v=10001$ (message $1000$): if either is transmitted and one error yields received word $r=10000$, the decoder cannot determine which was sent. This ambiguity arises because $u,v$ differ in few positions, formalized next.

<a id="pdf-7251cb8e4bc5-p022-b006"></a>
<!-- pdf-source: page=22; block=6; confidence=0.98 -->
# 1.4 Distance of a Code

<a id="pdf-7251cb8e4bc5-p022-b007"></a>
<!-- pdf-source: page=22; block=7; confidence=0.92 -->
Introduces minimum distance, a parameter connected to error-correction and error-detection capacity and typically the first parameter studied for a new code.

<a id="pdf-7251cb8e4bc5-p022-b008"></a>
<!-- pdf-source: page=22; block=8; confidence=0.96 -->
**Definition 1.4.1 (Minimum distance).** For $C\subseteq\Sigma^n$, the minimum distance (or distance), denoted $\Delta(C)$, is $\displaystyle \Delta(C)=\min_{c_1\ne c_2\in C}\Delta(c_1,c_2)$.

<a id="pdf-7251cb8e4bc5-p023-b001"></a>
<!-- pdf-source: page=23; block=1; confidence=0.94 -->
**Definition (relative minimum distance).** The relative minimum distance of $C$ is $\displaystyle \delta(C)=\min_{c_1\ne c_2\in C}\delta(c_1,c_2)$.

<a id="pdf-7251cb8e4bc5-p023-b002"></a>
<!-- pdf-source: page=23; block=2; confidence=0.93 -->
$C_{3,\mathrm{rep}}$ has distance $3$: distinct messages differ in $\ge1$ message bit, which becomes a $3$-bit difference after encoding. Example: $C_{3,\mathrm{rep}}(0,0,0,0)=(0,0,0,0,0,0,0,0,0,0,0,0)$ and $C_{3,\mathrm{rep}}(1,0,0,0)=(1,1,1,0,0,0,0,0,0,0,0,0)$.

<a id="pdf-7251cb8e4bc5-p023-b003"></a>
<!-- pdf-source: page=23; block=3; confidence=0.92 -->
Claim: $\Delta(C_\oplus)=2$. If two messages differ in $\ge2$ places, then $\Delta(C_\oplus(m_1),C_\oplus(m_2))\ge2$ (ignoring parity bits); if they differ in exactly one place, the parity bits differ, giving Hamming distance $2$. Example: $C_\oplus(1,0,0,0)=(1,0,0,0,1)$ and $C_\oplus(1,0,0,1)=(1,0,0,1,0)$. Thus $C_\oplus$ has smaller distance than $C_{3,\mathrm{rep}}$; larger distance suggests greater error-correction, which minimum distance exactly captures (including erasures, Def. 1.3.8).

<a id="pdf-7251cb8e4bc5-p023-b004"></a>
<!-- pdf-source: page=23; block=4; confidence=0.95 -->
**Proposition 1.4.2.** Given a code $C$, the following are equivalent:
1. $C$ has minimum distance $d\ge2$;
2. if $d$ is odd, $C$ can correct $(d-1)/2$ errors;
3. $C$ can detect $d-1$ errors;
4. $C$ can correct $d-1$ erasures.

<a id="pdf-7251cb8e4bc5-p023-b005"></a>
<!-- pdf-source: page=23; block=5; confidence=0.94 -->
**Remark 1.4.3.** For even $d$, property (2) differs: one can correct up to $\tfrac{d}{2}-1$ errors but not $\tfrac{d}{2}$ errors (Exercise 1.6).

<a id="pdf-7251cb8e4bc5-p023-b006"></a>
<!-- pdf-source: page=23; block=6; confidence=0.95 -->
Applying Proposition 1.4.2 to $C_\oplus$ (distance $2$) and $C_{3,\mathrm{rep}}$ (distance $3$) recovers known facts: $C_{3,\mathrm{rep}}$ corrects $1$ error (Prop. 1.3.9); $C_\oplus$ detects $1$ error but cannot correct $1$ error (Prop. 1.3.10).

<a id="pdf-7251cb8e4bc5-p024-b001"></a>
<!-- pdf-source: page=24; block=1; confidence=0.95 -->
**Definition (Maximum Likelihood Decoding).** The MLD function $D_{MLD}:\Sigma^n\to C$ outputs the codeword closest to the received word in Hamming distance, ties broken arbitrarily: $\displaystyle D_{MLD}(y)=\arg\min_{c\in C}\Delta(c,y)$.

<a id="pdf-7251cb8e4bc5-p024-b002"></a>
<!-- pdf-source: page=24; block=2; confidence=0.93 -->
**Algorithm 1.4.1 (Naive Maximum Likelihood Decoder).** Input: $y\in\Sigma^n$. Output: $D_{MLD}(y)$.
1. Pick an arbitrary $c\in C$; set $z\leftarrow c$.
2. for every $c'\in C$ with $c\ne c'$: if $\Delta(c',y)<\Delta(z,y)$ then $z\leftarrow c'$.
3. return $z$.

<a id="pdf-7251cb8e4bc5-p024-b003"></a>
<!-- pdf-source: page=24; block=3; confidence=0.94 -->
**Proof of Proposition 1.4.2.** Two steps: (i) property 1 implies properties 2, 3, 4 (via implications 1⟹2, 1⟹3, 1⟹4); (ii) if property 1 fails, none of 2, 3, 4 hold (via the corresponding three implications).

<a id="pdf-7251cb8e4bc5-p024-b004"></a>
<!-- pdf-source: page=24; block=4; confidence=0.92 -->
**Proof (1 ⟹ 2).** Assume distance $d=2t+1$. Show the MLD function corrects all error patterns with $\le t$ errors. Suppose not: let $c_1$ be transmitted and $y$ received, so $\Delta(y,c_1)\le t$ (1.4). Since MLD supposedly fails, $D_{MLD}(y)=c_2\ne c_1$, and by definition of MLD, $\Delta(y,c_2)\le\Delta(y,c_1)$ (1.5).

<a id="pdf-7251cb8e4bc5-p024-b005"></a>
<!-- pdf-source: page=24; block=5; confidence=0.90 -->
Footnote: MLD outputs a codeword rather than a message (cf. Def. 1.3.2), but since only codes of distance $\ge1$ are considered, the codeword–message bijection makes this distinction immaterial.

<a id="pdf-7251cb8e4bc5-p025-b001"></a>
<!-- pdf-source: page=25; block=1; confidence=0.94 -->
**Proof (cont.).** Chain of inequalities completing a contradiction: Δ(c₁,c₂) ≤ Δ(c₂,y)+Δ(c₁,y) (1.6, triangle inequality) ≤ 2Δ(c₁,y) (1.7, from (1.5)) ≤ 2t (1.8, from (1.4)) = d−1 (1.9). Thus distance of C ≤ d−1, contradicting distance = d.

<a id="pdf-7251cb8e4bc5-p025-b002"></a>
<!-- pdf-source: page=25; block=2; confidence=0.94 -->
**Proof (1 ⇒ 3).** Error-detection algorithm: for received word y, exhaustively check whether y = c for some c ∈ C. If no error occurred, y = c₁ ∈ C and the algorithm accepts. If 1 ≤ Δ(y,c₁) ≤ d−1, then since C has distance d, y ∉ C, so the algorithm rejects.

<a id="pdf-7251cb8e4bc5-p025-b003"></a>
<!-- pdf-source: page=25; block=3; confidence=0.94 -->
**Proof (1 ⇒ 4).** For received y ∈ (Σ∪{?})ⁿ, claim a unique c=(c₁,…,cₙ) ∈ C agrees with y on unerased positions (yᵢ = cᵢ whenever yᵢ ≠ ?). Otherwise two distinct c₁,c₂ ∈ C agree with y on all i with yᵢ ≠ ?, giving Δ(c₁,c₂) ≤ |{i : yᵢ = ?}| ≤ d−1, contradicting distance d. Algorithm: scan all codewords of C and output the one agreeing with y.

<a id="pdf-7251cb8e4bc5-p025-b004"></a>
<!-- pdf-source: page=25; block=4; confidence=0.92 -->
**Proof (¬1 ⇒ ¬2).** Assume C has distance d−1. Then property 2 fails: choose c₁ ≠ c₂ ∈ C with Δ(c₁,c₂) = d−1, and a vector y with Δ(y,c₁) = Δ(y,c₂) = (d−1)/2 (exists since d is odd). Since y could arise from either c₁ or c₂, no decoding function can recover the sent codeword. (Footnote: generalizes the argument that C⊕ cannot correct 1 error.)

<a id="pdf-7251cb8e4bc5-p026-b001"></a>
<!-- pdf-source: page=26; block=1; confidence=0.85 -->
**Figure 1.3.** Bad example for unique decoding: codewords c₁, c₂ at distance d−1 with a received word y equidistant (distance (d−1)/2) from both.

<a id="pdf-7251cb8e4bc5-p026-b002"></a>
<!-- pdf-source: page=26; block=2; confidence=0.93 -->
**Proof (¬1 ⇒ ¬3).** Transmitted word c₁, with another codeword c₂ at Δ(c₂,c₁) = d−1; take y = c₂. The error-detecting algorithm then either detects no error, or declares an error when c₂ was sent with no transmission error — so property 3 fails.

<a id="pdf-7251cb8e4bc5-p026-b003"></a>
<!-- pdf-source: page=26; block=3; confidence=0.93 -->
**Proof (¬1 ⇒ ¬4).** Let y be received with erasures exactly on the positions where c₁ and c₂ differ. Then both c₁ and c₂ could have been transmitted, so no algorithm correcting up to d−1 erasures succeeds. ∎

<a id="pdf-7251cb8e4bc5-p026-b004"></a>
<!-- pdf-source: page=26; block=4; confidence=0.95 -->
**Question 1.4.4 (Main question, reframed).** By Proposition 1.4.2, Question 1.1.1 becomes: what is the largest rate R that a code with distance d can have?

<a id="pdf-7251cb8e4bc5-p026-b005"></a>
<!-- pdf-source: page=26; block=5; confidence=0.85 -->
**Question 1.4.5 (Special case of 1.4.4).** The repetition code C₃,rep has distance 3 and rate 1/3. Can a code have distance 3 and rate R > 1/3?

<a id="pdf-7251cb8e4bc5-p026-b006"></a>
<!-- pdf-source: page=26; block=6; confidence=0.90 -->
**1.5 Hamming Code.** Introduces the Hamming code C_H, aimed at the question of whether a distance-3 code can exceed rate 1/3.

<a id="pdf-7251cb8e4bc5-p027-b001"></a>
<!-- pdf-source: page=27; block=1; confidence=0.94 -->
**Hamming code C_H.** For a message (x₁,x₂,x₃,x₄) ∈ {0,1}⁴:
C_H(x₁,x₂,x₃,x₄) = (x₁, x₂, x₃, x₄, x₂⊕x₃⊕x₄, x₁⊕x₃⊕x₄, x₁⊕x₂⊕x₄).
Parameters: q = 2, k = 4, n = 7, R = 4/7. Its distance is 3 (proved next). The specific parities are conventional; alternate parity choices also give distance 3 (Exercise 1.9).

<a id="pdf-7251cb8e4bc5-p027-b002"></a>
<!-- pdf-source: page=27; block=2; confidence=0.96 -->
**Definition 1.5.1 (Hamming Weight).** For q ≥ 2 and v ∈ {0,1,…,q−1}ⁿ, the Hamming weight wt(v) is the number of nonzero symbols in v. Example: wt(01203400) = 4.

<a id="pdf-7251cb8e4bc5-p027-b003"></a>
<!-- pdf-source: page=27; block=3; confidence=0.97 -->
**Proposition 1.5.2.** C_H has distance 3.

<a id="pdf-7251cb8e4bc5-p027-b004"></a>
<!-- pdf-source: page=27; block=4; confidence=0.93 -->
**Proof.** Relies on two facts:
(1.10) min_{c∈C_H, c≠0} wt(c) = 3;
(1.11) min_{c∈C_H, c≠0} wt(c) = min_{c₁≠c₂∈C_H} Δ(c₁,c₂).
Proof of (1.10) by case analysis on wt(x), where x = (x₁,x₂,x₃,x₄):
- Case 0: wt(x)=0 ⇒ C_H(x)=0 (excluded).
- Case 1: wt(x)=1 ⇒ at least two of the parity bits (x₂⊕x₃⊕x₄, x₁⊕x₃⊕x₄, x₁⊕x₂⊕x₄) equal 1, so wt(C_H(x)) ≥ 3.
- Case 2: wt(x)=2 ⇒ at least one parity bit equals 1, so wt(C_H(x)) ≥ 3.
- Case 3: wt(x)≥3 ⇒ the message bits alone give wt(C_H(x)) ≥ 3.
Hence min wt(c) ≥ 3; and wt(C_H(1,0,0,0)) = 3 gives min wt(c) ≤ 3, proving (1.10).

<a id="pdf-7251cb8e4bc5-p028-b001"></a>
<!-- pdf-source: page=28; block=1; confidence=0.96 -->
**Proof (of (1.11), continued).** For distinct messages $x,y\in\{0,1\}^4$, associativity and commutativity of $\oplus$ give $CH(x)+CH(y)=CH(x+y)$, where $+$ is bitwise XOR. For $u,v\in\{0,1\}^n$, $\Delta(u,v)=\mathrm{wt}(u+v)$ (Exercise 1.12). Hence
$$\min_{x\neq y\in\{0,1\}^4}\Delta(CH(x),CH(y))=\min_{x\neq y}\mathrm{wt}(CH(x+y))=\min_{x\neq 0\in\{0,1\}^4}\mathrm{wt}(CH(x)),$$
the last equality using $\{x+y\mid x\neq y\in\{0,1\}^n\}=\{x\in\{0,1\}^n\mid x\neq 0\}$. Since $\mathrm{wt}(CH(x))=0$ iff $x=0$, this proves (1.11). Combining (1.10) and (1.11), $CH$ has distance $3$.

<a id="pdf-7251cb8e4bc5-p028-b002"></a>
<!-- pdf-source: page=28; block=2; confidence=0.95 -->
Alternative argument: the Hamming code equals $\{x\cdot G_H\mid x\in\{0,1\}^4\}$ (with $x$ a row vector), where
$$G_H=\begin{pmatrix}1&0&0&0&0&1&1\\0&1&0&0&1&0&1\\0&0&1&0&1&1&0\\0&0&0&1&1&1&1\end{pmatrix}.$$
Indeed $(x_1,x_2,x_3,x_4)\cdot G_H=(x_1,x_2,x_3,x_4,\ x_2\oplus x_3\oplus x_4,\ x_1\oplus x_3\oplus x_4,\ x_1\oplus x_2\oplus x_4)$; e.g. column 1 gives bit $x_1$ and column 5 gives $x_2\oplus x_3\oplus x_4$.

<a id="pdf-7251cb8e4bc5-p028-b003"></a>
<!-- pdf-source: page=28; block=3; confidence=0.95 -->
**Definition (binary linear code).** A binary code of dimension $k$ and block length $n$ generated by a $k\times n$ matrix $G$, i.e. $C=\{x\cdot G\mid x\in\{0,1\}^k\}$ (addition $=\oplus$, multiplication $=$ AND), is a binary linear code. Both $C_\oplus$ and $C_{3,\mathrm{rep}}$ are binary linear codes (Exercise 1.13).

<a id="pdf-7251cb8e4bc5-p028-b004"></a>
<!-- pdf-source: page=28; block=4; confidence=0.98 -->
**Lemma 1.5.3.** For any binary linear code $C$ and any two messages $x,y$: $C(x)+C(y)=C(x+y)$.

<a id="pdf-7251cb8e4bc5-p029-b001"></a>
<!-- pdf-source: page=29; block=1; confidence=0.97 -->
**Proof.** Let $G$ be the generator matrix of $C$. By distributivity and associativity of Boolean XOR and AND,
$$C(x)+C(y)=x\cdot G+y\cdot G=(x+y)\cdot G=C(x+y).\qquad\blacksquare$$

<a id="pdf-7251cb8e4bc5-p029-b002"></a>
<!-- pdf-source: page=29; block=2; confidence=0.95 -->
Remark: $x,y$ need not be distinct in Lemma 1.5.3. Since $b\oplus b=0$ for all $b\in\{0,1\}$, $x+x=0$, so the lemma gives $C(0)=0$ (also because $0\cdot G=0$ for any $G$).

<a id="pdf-7251cb8e4bc5-p029-b003"></a>
<!-- pdf-source: page=29; block=3; confidence=0.98 -->
**Proposition 1.5.4.** For any binary linear code, its minimum distance equals the minimum Hamming weight of any non-zero codeword.

<a id="pdf-7251cb8e4bc5-p029-b004"></a>
<!-- pdf-source: page=29; block=4; confidence=0.95 -->
$CH$ has distance $d=3$ and rate $R=\tfrac{4}{7}$; $C_{3,\mathrm{rep}}$ has $d=3$ and $R=\tfrac{1}{3}$, so the Hamming code beats the repetition code on the rate–distance tradeoff (answering Question 1.4.5 affirmatively).

**Question 1.5.5** (Codes better than $CH$). Can there be a distance-$3$ code with rate higher than that of $CH$?

<a id="pdf-7251cb8e4bc5-p029-b005"></a>
<!-- pdf-source: page=29; block=5; confidence=0.93 -->
# 1.6 Hamming Bound

Presents a first tradeoff between redundancy (code dimension) and error-correction capability (distance); proves a special case of the Hamming bound for distance $3$.

<a id="pdf-7251cb8e4bc5-p029-b006"></a>
<!-- pdf-source: page=29; block=6; confidence=0.97 -->
**Definition 1.6.1** (Hamming Ball). For $x\in[q]^n$,
$$B(x,e)=\{y\in[q]^n\mid\Delta(x,y)\le e\},$$
i.e. all vectors within Hamming distance $e$ of $x$.

<a id="pdf-7251cb8e4bc5-p030-b001"></a>
<!-- pdf-source: page=30; block=1; confidence=0.98 -->
**Theorem 1.6.2** (Hamming bound for $d=3$). Every binary code with block length $n$, dimension $k$, and distance $d=3$ satisfies
$$k\le n-\log_2(n+1).$$

<a id="pdf-7251cb8e4bc5-p030-b002"></a>
<!-- pdf-source: page=30; block=2; confidence=0.94 -->
**Proof.** For distinct codewords $c_1\neq c_2\in C$, since $C$ has distance $3$,
$$B(c_1,1)\cap B(c_2,1)=\emptyset.\tag{1.12}$$
(Otherwise $y$ in both balls gives $\Delta(y,c_1)\le1$, $\Delta(y,c_2)\le1$, so by the triangle inequality $\Delta(c_1,c_2)\le2<3$, a contradiction.) For all $x\in\{0,1\}^n$ (Exercise 1.16),
$$|B(x,1)|=n+1.\tag{1.13}$$
The union of the balls centered at codewords is a subset of $\{0,1\}^n$, so
$$\Big|\bigcup_{c\in C}B(c,1)\Big|\le 2^n.\tag{1.14}$$
[Proof continues beyond the supplied pages.]

<a id="pdf-7251cb8e4bc5-p031-b001"></a>
<!-- pdf-source: page=31; block=1; confidence=0.95 -->
**Proof (concl.).** Since the balls B(c,1) are pairwise disjoint (1.12), |⋃_{c∈C} B(c,1)| = ∑_{c∈C} |B(c,1)| = ∑_{c∈C}(n+1) = 2^k·(n+1); (1.15) uses (1.13) and (1.16) uses dim C = k. Combining (1.16) with (1.14) gives 2^k(n+1) ≤ 2^n, i.e. 2^k ≤ 2^n/(n+1), and taking log₂: k ≤ n − log₂(n+1). For n=7, n−log₂(n+1)=4, so the Hamming code C_H attains the largest dimension among binary codes of block length 7 and distance 3, answering Question 1.5.5 negatively for n=7.

<a id="pdf-7251cb8e4bc5-p031-b002"></a>
<!-- pdf-source: page=31; block=2; confidence=0.99 -->
**Section 1.7. Generalized Hamming Bound.**

<a id="pdf-7251cb8e4bc5-p031-b003"></a>
<!-- pdf-source: page=31; block=3; confidence=0.98 -->
**Definition 1.7.1.** A code C ⊆ Σⁿ with dimension k and distance d is called an (n,k,d)_Σ code, also written (n,k,d)_{|Σ|}.

<a id="pdf-7251cb8e4bc5-p031-b004"></a>
<!-- pdf-source: page=31; block=4; confidence=0.97 -->
**Theorem 1.7.2 (Hamming Bound for any d).** For every (n,k,d)_q code, k ≤ n − log_q( ∑_{i=0}^{⌊(d−1)/2⌋} C(n,i)(q−1)^i ).

<a id="pdf-7251cb8e4bc5-p032-b001"></a>
<!-- pdf-source: page=32; block=1; confidence=0.95 -->
**Proof.** Generalizes the proof of Theorem 1.6.2. Set e = ⌊(d−1)/2⌋. For distinct codewords c₁ ≠ c₂ ∈ C, the balls are disjoint: B(c₁,e) ∩ B(c₂,e) = ∅ (1.17). Claim (1.18): for all x ∈ [q]ⁿ, |B(x,e)| = ∑_{i=0}^{e} C(n,i)(q−1)^i, since a vector in B(x,e) differs from x in exactly i (0≤i≤e) positions, with C(n,i) choices of positions and (q−1) alternatives each. The union of balls around codewords lies in [q]ⁿ, so |⋃_{c∈C} B(c,e)| ≤ qⁿ (1.19). By disjointness, |⋃_{c∈C} B(c,e)| = ∑_{c∈C} |B(c,e)| = q^k ∑_{i=0}^{e} C(n,i)(q−1)^i (1.20), using (1.18) and dim C = k. Combining (1.19)–(1.20) and taking log_q yields k ≤ n − log_q( ∑_{i=0}^{e} C(n,i)(q−1)^i ). Consequently any distance-d code has rate R ≤ 1 − log_q(∑_{i=0}^{e} C(n,i)(q−1)^i)/n (partial answer to Question 1.4.4). Footnote: if y ∈ B(c₁,e)∩B(c₂,e) then Δ(y,c₁)≤e, Δ(y,c₂)≤e, so by triangle inequality Δ(c₁,c₂) ≤ 2e ≤ d−1, a contradiction.

<a id="pdf-7251cb8e4bc5-p033-b001"></a>
<!-- pdf-source: page=33; block=1; confidence=0.97 -->
**Definition 1.7.3.** Codes meeting the Hamming bound are called perfect codes: Hamming balls of radius ⌊(d−1)/2⌋ around all codewords cover the entire ambient space, so every vector lies in exactly one such ball.

<a id="pdf-7251cb8e4bc5-p033-b002"></a>
<!-- pdf-source: page=33; block=2; confidence=0.95 -->
The (7,4,3)₂ Hamming code (and the general Hamming code family) is perfect. **Question 1.7.4 (Perfect Codes).** Are there perfect binary codes other than the Hamming codes? (Answered in Section 2.4.)

<a id="pdf-7251cb8e4bc5-p033-b003"></a>
<!-- pdf-source: page=33; block=3; confidence=0.98 -->
**Section 1.8. Family of codes.** Motivates asymptotic study via families of codes rather than fixed codes.

<a id="pdf-7251cb8e4bc5-p033-b004"></a>
<!-- pdf-source: page=33; block=4; confidence=0.96 -->
**Definition 1.8.1 (Code families, Rate and Distance).** Given an increasing sequence of block lengths {n_i}_{i≥1} and sequences {k_i}, {d_i}, {q_i} such that for each i there is an (n_i,k_i,d_i)_{q_i} code C_i, the sequence C = {C_i}_{i≥1} is a family of codes. Its rate is R(C) = lim_{i→∞} k_i/n_i and its relative distance is δ(C) = lim_{i→∞} d_i/n_i (when the limits exist). If q_i = q for all i, C is a family of q-ary codes.

<a id="pdf-7251cb8e4bc5-p033-b005"></a>
<!-- pdf-source: page=33; block=5; confidence=0.93 -->
Example: the Hamming code extends to a family C_H = {C_i}_{i∈Z⁺} with C_i an (n_i,k_i,d_i)-code where n_i = 2^i − 1, k_i = 2^i − i − 1, d_i = 3; hence R(C_H) = lim_{i→∞} (1 − i/(2^i − 1)) = 1.

<a id="pdf-7251cb8e4bc5-p034-b001"></a>
<!-- pdf-source: page=34; block=1; confidence=0.95 -->
Concludes a computation: $\delta(C_H) = \lim_{i\to\infty} \frac{3}{2^i-1} = 0$.

<a id="pdf-7251cb8e4bc5-p034-b002"></a>
<!-- pdf-source: page=34; block=2; confidence=0.95 -->
Asymptotic analysis of algorithms on codes only makes sense for *families* of codes, not fixed codes (e.g. an $O(n^2)$-time decoder presumes a family with growing block length). Henceforth "code" implicitly means "family of codes."

<a id="pdf-7251cb8e4bc5-p034-b003"></a>
<!-- pdf-source: page=34; block=3; confidence=0.97 -->
**Note (Efficient algorithm).** An algorithm for a code of block length $n$ is *efficient* if it runs in time polynomial in $n$.

<a id="pdf-7251cb8e4bc5-p034-b004"></a>
<!-- pdf-source: page=34; block=4; confidence=0.93 -->
For the specific codes studied, families are "natural": all members are the same code with different parameters. Formally, consider families $\{C_i\}_{i\ge 1}$ where a sufficient description of $C_i$ can be computed efficiently from the index $i$ alone.

<a id="pdf-7251cb8e4bc5-p034-b005"></a>
<!-- pdf-source: page=34; block=5; confidence=0.96 -->
**Question 1.8.2 (Main Question — formal).** Given $q$, what is the optimal tradeoff between rate $R(C)$ and relative distance $\delta(C)$ achievable by some family $C$ of $q$-ary codes? (Refines Question 1.4.4 by comparing $R$ against $\delta$ rather than the integer distance $d$.)

<a id="pdf-7251cb8e4bc5-p034-b006"></a>
<!-- pdf-source: page=34; block=6; confidence=0.97 -->
**Question 1.8.3 (Asymptotically Good Codes).** Does there exist a constant $q$ and a $q$-ary family of codes $C$ with $R(C) > 0$ and $\delta(C) > 0$ simultaneously?

<a id="pdf-7251cb8e4bc5-p034-b007"></a>
<!-- pdf-source: page=34; block=7; confidence=0.94 -->
**Definition.** A code family with $R(C)>0$ and $\delta(C)>0$ simultaneously is called *asymptotically good*; such codes exist and are presented later.

<a id="pdf-7251cb8e4bc5-p034-b008"></a>
<!-- pdf-source: page=34; block=8; confidence=0.90 -->
Footnote 19: efficient constructibility of $\{C_i\}$ does not always hold — e.g. it fails for "random" codes.

<a id="pdf-7251cb8e4bc5-p035-b001"></a>
<!-- pdf-source: page=35; block=1; confidence=0.98 -->
## 1.9 Exercises

<a id="pdf-7251cb8e4bc5-p035-b002"></a>
<!-- pdf-source: page=35; block=2; confidence=0.96 -->
**Exercise 1.1.** Show every $t$-error correcting code is also $t$-error detecting, but not conversely.

<a id="pdf-7251cb8e4bc5-p035-b003"></a>
<!-- pdf-source: page=35; block=3; confidence=0.97 -->
**Exercise 1.2.** Prove Proposition 1.3.9.

<a id="pdf-7251cb8e4bc5-p035-b004"></a>
<!-- pdf-source: page=35; block=4; confidence=0.96 -->
**Exercise 1.3.** Show that for every integer $n$, no block-length-$n$ code can handle an arbitrary number of errors.

<a id="pdf-7251cb8e4bc5-p035-b005"></a>
<!-- pdf-source: page=35; block=5; confidence=0.97 -->
**Exercise 1.4.** Prove Proposition 1.3.10.

<a id="pdf-7251cb8e4bc5-p035-b006"></a>
<!-- pdf-source: page=35; block=6; confidence=0.96 -->
**Exercise 1.5.** A distance $d:\Sigma^n\times\Sigma^n\to\mathbb{R}$ is a *metric* if for all $x,y,z\in\Sigma^n$: (1) $d(x,y)\ge 0$; (2) $d(x,y)=0 \iff x=y$; (3) $d(x,y)=d(y,x)$; (4) $d(x,z)\le d(x,y)+d(y,z)$ (triangle inequality). Prove the Hamming distance is a metric.

<a id="pdf-7251cb8e4bc5-p035-b007"></a>
<!-- pdf-source: page=35; block=7; confidence=0.95 -->
**Exercise 1.6.** For a code $C$ with even distance $d$, argue $C$ corrects up to $d/2-1$ errors but not $d/2$ errors. Deduce that a $t$-error-correctable code has distance $2t+1$ or $2t+2$.

<a id="pdf-7251cb8e4bc5-p035-b008"></a>
<!-- pdf-source: page=35; block=8; confidence=0.95 -->
**Exercise 1.7.** Parameter conversions (work for all $n,k,d\ge1$, any $\Sigma$, using only the parameters): (1) from an $(n,k,d)_\Sigma$ code construct an $(n-1,k,d-1)_\Sigma$ code; (2) for odd $d$, from an $(n,k,d)_2$ code construct an $(n+1,k,d+1)_2$ code.

<a id="pdf-7251cb8e4bc5-p036-b001"></a>
<!-- pdf-source: page=36; block=1; confidence=0.95 -->
**Exercise 1.8.** Errors-and-erasures model for an $(n,k,d)_\Sigma$ code $C$: received $y\in(\Sigma\cup\{?\})^n$ has $s$ erasures and $e$ errors; decoding outputs $c\in C$ disagreeing with $y$ in at most $e$ of the $n-s$ non-erased positions. Assume $2e+s<d$ (1.21). (1) Argue the decoder output is unique under (1.21). (2) For binary (not necessarily linear) $C$ with a decoder $D$ correcting $<d/2$ errors in time $T(n)$, show decoding under (1.21) is possible in time $O(T(n))$.

<a id="pdf-7251cb8e4bc5-p036-b002"></a>
<!-- pdf-source: page=36; block=2; confidence=0.95 -->
**Exercise 1.9.** Define codes other than $C_H$ with $k=4$, $n=7$, $d=3$. (Hint: use the parity properties from the proof of Proposition 1.5.2.)

<a id="pdf-7251cb8e4bc5-p036-b003"></a>
<!-- pdf-source: page=36; block=3; confidence=0.95 -->
**Exercise 1.10.** Argue that if $\mathrm{wt}(x)=1$ then at least two parity check bits in $(x_2\oplus x_3\oplus x_4,\ x_1\oplus x_2\oplus x_4,\ x_1\oplus x_3\oplus x_4)$ are $1$.

<a id="pdf-7251cb8e4bc5-p036-b004"></a>
<!-- pdf-source: page=36; block=4; confidence=0.95 -->
**Exercise 1.11.** Argue that if $\mathrm{wt}(x)=2$ then at least one parity check bit in $(x_2\oplus x_3\oplus x_4,\ x_1\oplus x_2\oplus x_4,\ x_1\oplus x_3\oplus x_4)$ is $1$.

<a id="pdf-7251cb8e4bc5-p036-b005"></a>
<!-- pdf-source: page=36; block=5; confidence=0.96 -->
**Exercise 1.12.** Prove that for any $u,v\in\{0,1\}^n$, $\Delta(u,v)=\mathrm{wt}(u+v)$.

<a id="pdf-7251cb8e4bc5-p036-b006"></a>
<!-- pdf-source: page=36; block=6; confidence=0.94 -->
**Exercise 1.13.** Argue that $C_\oplus$ and $C_{3,\mathrm{rep}}$ are binary linear codes.

<a id="pdf-7251cb8e4bc5-p036-b007"></a>
<!-- pdf-source: page=36; block=7; confidence=0.95 -->
**Exercise 1.14.** Let $G$ be a generator matrix of an $(n,k,d)_2$ binary linear code. Show $G$ has at least $kd$ ones.

<a id="pdf-7251cb8e4bc5-p036-b008"></a>
<!-- pdf-source: page=36; block=8; confidence=0.95 -->
**Exercise 1.15.** Argue that in any binary linear code, either all codewords begin with $0$, or exactly half of the codewords begin with $0$.

<a id="pdf-7251cb8e4bc5-p036-b009"></a>
<!-- pdf-source: page=36; block=9; confidence=0.95 -->
**Exercise 1.16.** Prove (1.13).

<a id="pdf-7251cb8e4bc5-p036-b010"></a>
<!-- pdf-source: page=36; block=10; confidence=0.96 -->
**Exercise 1.17.** Show there is no binary code with block length $4$ achieving the Hamming bound.

<a id="pdf-7251cb8e4bc5-p036-b011"></a>
<!-- pdf-source: page=36; block=11; confidence=0.93 -->
**Exercise 1.18. ($\ast$)** $n$ people each receive an i.i.d. uniform black/white hat; each sees all others' hats but not their own. Each independently guesses their own color or abstains. They win collectively iff at least one person guesses and all non-abstainers guess correctly; they lose if all abstain or any guesser is wrong. Goal: devise a strategy achieving high win probability (warm-up stated).

<a id="pdf-7251cb8e4bc5-p037-b001"></a>
<!-- pdf-source: page=37; block=1; confidence=0.90 -->
**Exercise (part 1).** Show that the n people can win the hat game with probability at least 1/2.

<a id="pdf-7251cb8e4bc5-p037-b002"></a>
<!-- pdf-source: page=37; block=2; confidence=0.92 -->
**Exercise (part 2).** Define a directed graph G to be a subgraph of the n-dimensional hypercube if its vertex set is {0,1}^n and every edge u→v joins vertices u, v differing in at most one coordinate. Let K(G) be the number of vertices of G having in-degree ≥ 1 and out-degree 0. Show that the winning probability of the hat problem equals max_G K(G)/2^n, the maximum taken over all directed subgraphs G of the n-dimensional hypercube.

<a id="pdf-7251cb8e4bc5-p037-b003"></a>
<!-- pdf-source: page=37; block=3; confidence=0.92 -->
**Exercise (part 3).** Using that every vertex has out-degree at most n, show that K(G)/2^n ≤ n/(n+1) for any directed subgraph G of the n-dimensional hypercube.

<a id="pdf-7251cb8e4bc5-p037-b004"></a>
<!-- pdf-source: page=37; block=4; confidence=0.92 -->
**Exercise (part 4).** Show that if n = 2^r − 1, then there exists a directed subgraph G of the n-dimensional hypercube with K(G)/2^n = n/(n+1). Hint: use the Hamming code.

<a id="pdf-7251cb8e4bc5-p037-b005"></a>
<!-- pdf-source: page=37; block=5; confidence=0.97 -->
## 1.10 Bibliographic Notes

<a id="pdf-7251cb8e4bc5-p037-b006"></a>
<!-- pdf-source: page=37; block=6; confidence=0.90 -->
Coding theory originates in Shannon [65] and Hamming [35]. Shannon's paper defined the BSC_p channel and defined codes via encoding and decoding functions; Hamming's defined codes as in Definition 1.2.1 and the notion of Hamming distance. The Hamming bound and Hamming code are due to Hamming (the latter's definition used here also appears in Shannon's earlier paper, attributed to Hamming). Erasures were defined by Elias [23]. Most chapter exercises are based on [35]; the hat problem (Exercise 1.18) is from Ebert, Merkle and Vollmer [22].

<a id="pdf-7251cb8e4bc5-p039-b001"></a>
<!-- pdf-source: page=39; block=1; confidence=0.97 -->
# Chapter 2. A Look at Some Nicely Behaved Codes: Linear Codes

<a id="pdf-7251cb8e4bc5-p039-b002"></a>
<!-- pdf-source: page=39; block=2; confidence=0.90 -->
Motivation: how many bits are needed to describe a code C : [q]^k → [q]^n? A general code can be stored using n·q^k symbols from [q], i.e. n·q^k·log q bits — exponential (prohibitive even for k=100) at constant rate. Succinct representation requires extra structure; linear codes provide it. Recall (Section 1.5) that C ⊆ {0,1}^n is a binary linear code if c1+c2 ∈ C for all c1,c2 ∈ C, where + is bit-wise XOR. This chapter generalizes to linear codes, which give succinct representations and other nice properties. Defining general linear codes first requires finite fields and vector spaces over them.

<a id="pdf-7251cb8e4bc5-p039-b003"></a>
<!-- pdf-source: page=39; block=3; confidence=0.97 -->
## 2.1 Groups and Finite Fields

<a id="pdf-7251cb8e4bc5-p039-b004"></a>
<!-- pdf-source: page=39; block=4; confidence=0.90 -->
Linear subspaces are defined over (finite) fields, which endow finite symbols with arithmetic analogous to that of the reals. The section begins with the more elementary notion of a group before fields.

<a id="pdf-7251cb8e4bc5-p039-b005"></a>
<!-- pdf-source: page=39; block=5; confidence=0.90 -->
**Definition 2.1.1 (Group).** A group G is a pair (S, ∘) where S is a set of elements and ∘ : S × S → S is a function satisfying the following properties:
- **Closure:** for every a, b ∈ S, a ∘ b ∈ S.

(The list of further group properties continues beyond the supplied text.)

<a id="pdf-7251cb8e4bc5-p040-b001"></a>
<!-- pdf-source: page=40; block=1; confidence=0.95 -->
**Definition (Group, continued).** For $G=(S,\circ)$: (i) **Associativity:** $a\circ(b\circ c)=(a\circ b)\circ c$ for all $a,b,c\in S$. (ii) **Identity:** there exists $e\in S$ with $a\circ e=e\circ a=a$ for all $a\in S$. (iii) **Inverse:** every $a\in S$ has a unique $a^{-1}$ with $a\circ a^{-1}=a^{-1}\circ a=e$. If $G$ satisfies all properties except existence of inverses, it is a *monoid*. $G$ is *commutative* if $a\circ b=b\circ a$ for all $a,b\in S$. Same letter used for group and its element set.

<a id="pdf-7251cb8e4bc5-p040-b002"></a>
<!-- pdf-source: page=40; block=2; confidence=0.95 -->
**Definition 2.1.2 (Field).** A field $F=(S,+,\cdot)$ with $+,\cdot:S\times S\to S$ satisfies: (i) **Addition:** $(S,+)$ is a commutative group with identity $0\in S$; (ii) **Multiplication:** $(S\setminus\{0\},\cdot)$ is a commutative group with identity $1\in S\setminus\{0\}$ (0 excluded as it has no multiplicative inverse); (iii) **Distributivity:** $a\cdot(b+c)=a\cdot b+a\cdot c$ for all $a,b,c\in S$. Notation: $-a$ = additive inverse, $a^{-1}$ = multiplicative inverse for $a\in F\setminus\{0\}$.

<a id="pdf-7251cb8e4bc5-p040-b003"></a>
<!-- pdf-source: page=40; block=3; confidence=0.92 -->
The property $a\cdot 0=0=0\cdot a$ is not stated explicitly but is implied by Definition 2.1.2 (so $(S,\cdot)$ is a commutative monoid); see Exercise 2.1. $\mathbb{R}$ is a field; $\mathbb{Z}$ is not (division need not stay in $\mathbb{Z}$), though $\mathbb{Q}$ is (Exercise 2.2). The course focuses exclusively on finite fields; notation $|F|=|S|$.

<a id="pdf-7251cb8e4bc5-p040-b004"></a>
<!-- pdf-source: page=40; block=4; confidence=0.97 -->
**Theorem 2.1.3 (Size of Finite Fields).** Every finite field has size $p^s$ for some prime $p$ and integer $s\ge 1$. Conversely, for every prime $p$ and integer $s\ge 1$ there exists a field $F$ of size $p^s$.

<a id="pdf-7251cb8e4bc5-p041-b001"></a>
<!-- pdf-source: page=41; block=1; confidence=0.94 -->
Example $\mathbb{F}_2$ with $S=\{0,1\}$: addition is XOR, multiplication is AND; additive inverse of each element is itself, and $1^{-1}=1$. For prime $p$, integers mod $p$ form a field $\mathbb{F}_p$ (also $\mathbb{Z}_p$) with mod-$p$ arithmetic. In $\mathbb{F}_7=\{0,\dots,6\}$: $(4+3)\bmod 7=0$, $4\cdot 4\bmod 7=2$; additive inverse of $4$ is $3$, multiplicative inverse of $4$ is $2$ (since $4\cdot 2\bmod 7=1$).

<a id="pdf-7251cb8e4bc5-p041-b002"></a>
<!-- pdf-source: page=41; block=2; confidence=0.97 -->
**Lemma 2.1.4.** Let $p$ be prime. Then $\mathbb{F}_p=(\{0,1,\dots,p-1\},+_p,\cdot_p)$ is a field, where $+_p,\cdot_p$ are addition and multiplication modulo $p$.

<a id="pdf-7251cb8e4bc5-p041-b003"></a>
<!-- pdf-source: page=41; block=3; confidence=0.93 -->
**Proof.** Associativity, commutativity, distributivity, and identities are inherited from the integers. Closure holds since mod-$p$ arithmetic keeps results in $\{0,\dots,p-1\}$. It remains to show unique additive and multiplicative inverses.

*Additive inverse:* for $a\in\{0,\dots,p-1\}$, the inverse is $p-a\bmod p$ (since $a+(p-a)\equiv 0\bmod p$). Uniqueness: $a,a+1,\dots,a+p-1$ are $p$ consecutive integers, so exactly one is a multiple of $p$, occurring at $b=p-a\bmod p$.

*Multiplicative inverse:* fix $a\in\{1,\dots,p-1\}$ and let $T=\{a\cdot_p b\mid b\in\{1,\dots,p-1\}\}$. The elements of $T$ are distinct: if $a\cdot b_1\equiv a\cdot b_2\bmod p$ with $b_1\ne b_2$, then $a(b_1-b_2)\equiv 0\bmod p$, so $p\mid a(b_1-b_2)$; but $a$ and $|b_1-b_2|$ are both $\le p-1$, contradicting primality of $p$. Hence $|T|=p-1$ and $T=[p-1]$, so there is a unique $b$ with $a\cdot b\equiv 1\bmod p$, giving $a^{-1}=b$. $\square$

<a id="pdf-7251cb8e4bc5-p041-b004"></a>
<!-- pdf-source: page=41; block=4; confidence=0.95 -->
**Theorem 2.1.5.** For every prime power $q$ there is a unique finite field with $q$ elements (up to isomorphism), justifying the notation $\mathbb{F}_q$. (An isomorphism $\varphi:S\to S'$ between fields $(S,+,\cdot)$ and $(S',\oplus,\circ)$ is a bijection with $\varphi(a_1+a_2)=\varphi(a_1)\oplus\varphi(a_2)$ and $\varphi(a_1\cdot a_2)=\varphi(a_1)\circ\varphi(a_2)$.)

<a id="pdf-7251cb8e4bc5-p042-b001"></a>
<!-- pdf-source: page=42; block=1; confidence=0.99 -->
**2.2 Vector Spaces and Linear Subspaces**

<a id="pdf-7251cb8e4bc5-p042-b002"></a>
<!-- pdf-source: page=42; block=2; confidence=0.94 -->
**Definition 2.2.1 (Vector Space).** A vector space $V$ over a field $F$ is a triple $(T,+,\cdot)$ where $(T,+)$ is a commutative group and $\cdot$ (the scalar product) is a function $F\times T\to T$ such that for all $a,b\in F$ and $u,v\in T$: $(a+b)\cdot u=a\cdot u+b\cdot u$ and $a\cdot(u+v)=a\cdot u+a\cdot v$. The primary example is $F^n$ with coordinatewise addition and coordinatewise scaling.

<a id="pdf-7251cb8e4bc5-p042-b003"></a>
<!-- pdf-source: page=42; block=3; confidence=0.95 -->
**Definition 2.2.2 (Linear Subspace).** A non-empty $S\subseteq F^n$ is a linear subspace if: (1) for all $x,y\in S$, $x+y\in S$ (componentwise vector addition over $F$); (2) for all $a\in F$, $x\in S$, $a\cdot x\in S$ (componentwise scaling over $F$).

<a id="pdf-7251cb8e4bc5-p042-b004"></a>
<!-- pdf-source: page=42; block=4; confidence=0.90 -->
Example subspace of $\mathbb{F}_5^3$ (Eq. 2.1): $S_1=\{(0,0,0),(1,1,1),(2,2,2),(3,3,3),(4,4,4)\}$; e.g. $(1,1,1)+(3,3,3)=(4,4,4)\in S_1$ and $2\cdot(4,4,4)=(3,3,3)\in S_1$. Example subspace of $\mathbb{F}_3^3$ (Eq. 2.2): $S_2=\{(0,0,0),(1,0,1),(2,0,2),(0,1,1),(0,2,2),(1,1,2),(1,2,0),(2,1,0),(2,2,1)\}$; e.g. $(1,0,1)+(0,2,2)=(1,2,0)\in S_2$ and $2\cdot(2,0,2)=(1,0,1)\in S_2$.

<a id="pdf-7251cb8e4bc5-p042-b005"></a>
<!-- pdf-source: page=42; block=5; confidence=0.94 -->
**Remark 2.2.3.** Property (2) implies $0$ is contained in every linear subspace. Over $\mathbb{F}_2$, property (2) is redundant (Exercise 2.5).

<a id="pdf-7251cb8e4bc5-p042-b006"></a>
<!-- pdf-source: page=42; block=6; confidence=0.95 -->
**Definition 2.2.4 (Span).** Given $B=\{v_1,\dots,v_\ell\}$, the span of $B$ is $\left\{\sum_{i=1}^{\ell} a_i\cdot v_i \;\middle|\; a_i\in\mathbb{F}_q \text{ for every } i\in[\ell]\right\}$.

<a id="pdf-7251cb8e4bc5-p043-b001"></a>
<!-- pdf-source: page=43; block=1; confidence=0.98 -->
**Definition 2.2.5 (Linear (in)dependence).** Vectors $v_1,\dots,v_k$ are *linearly independent* if for every $1\le i\le k$ and every $(k-1)$-tuple $(a_1,\dots,a_{i-1},a_{i+1},\dots,a_k)\in\mathbb{F}_q^{k-1}$, $v_i \ne a_1v_1+\cdots+a_{i-1}v_{i-1}+a_{i+1}v_{i+1}+\cdots+a_kv_k$; equivalently, no $v_i$ lies in the span of the remaining vectors. They are *linearly dependent* otherwise.

<a id="pdf-7251cb8e4bc5-p043-b002"></a>
<!-- pdf-source: page=43; block=2; confidence=0.95 -->
Example: $(1,0,1),(1,1,1)\in S_2$ are linearly independent, since no scalar multiple of one equals the other over $\{0,1\}$.

<a id="pdf-7251cb8e4bc5-p043-b003"></a>
<!-- pdf-source: page=43; block=3; confidence=0.94 -->
**Definition 2.2.6 (Rank).** The rank of a matrix over $\mathbb{F}_q$ is the maximum number of linearly independent rows (equivalently columns). A matrix in $\mathbb{F}_q^{k\times n}$ of rank $\min(k,n)$ has *full rank*.

<a id="pdf-7251cb8e4bc5-p043-b004"></a>
<!-- pdf-source: page=43; block=4; confidence=0.95 -->
Row rank and column rank of a matrix are equal (standard theorem). Example: over $\mathbb{F}_3$, $G_2=\begin{pmatrix}1&0&1\\0&1&1\end{pmatrix}$ (eq. 2.3) has full rank (Exercise 2.6).

<a id="pdf-7251cb8e4bc5-p043-b005"></a>
<!-- pdf-source: page=43; block=5; confidence=0.97 -->
**Theorem 2.2.7.** If $S\subseteq\mathbb{F}_q^n$ is a linear subspace then:
1. $|S|=q^k$ for some $k\ge0$; $k$ is the *dimension* of $S$.
2. There is a set of linearly independent basis vectors $v_1,\dots,v_k\in S$ such that every $x\in S$ is $x=a_1v_1+\cdots+a_kv_k$ with $a_i\in\mathbb{F}_q$; equivalently a full-rank $k\times n$ *generator matrix* $G$ (rows $v_1,\dots,v_k$) with $x=(a_1,\dots,a_k)\cdot G$.
3. There is a full-rank $(n-k)\times n$ *parity check matrix* $H$ with $Hx^T=0$ for every $x\in S$.

<a id="pdf-7251cb8e4bc5-p044-b001"></a>
<!-- pdf-source: page=44; block=1; confidence=0.97 -->
**Theorem 2.2.7 (property 4).** $G$ and $H$ are orthogonal: $G\cdot H^T=0$.

<a id="pdf-7251cb8e4bc5-p044-b002"></a>
<!-- pdf-source: page=44; block=2; confidence=0.96 -->
**Proof Sketch.**
*Property 1:* Suppose for contradiction $q^k<|S|<q^{k+1}$. Greedily build a linearly independent $B\subseteq S$ with $|B|\ge k+1$: pick nonzero $v_1$ (exists since $|S|>q^k\ge1$); after step $t\le k$ with $|B|=t$, its span has size $q^t\le q^k<|S|$, so some $v_{t+1}\in S\setminus B$ is independent of $B$; continue until $|B|=k+1$. Then $\mathrm{span}(B)\subseteq S$ has size $\ge q^{k+1}>|S|$, a contradiction.
*Property 2:* Take $B=\{v_1,\dots,v_k\}$ any $k$ independent vectors; $\mathrm{span}(B)\subseteq S$ and $|\mathrm{span}(B)|=q^k=|S|$, so they coincide.
*Property 3:* $S$ has a null space $N\subseteq\mathbb{F}_q^n$ with $\langle x,y\rangle=0$ for all $x\in S,y\in N$; $N$ is a linear subspace of dimension $n-k$ (using $\langle x,y+z\rangle=\langle x,y\rangle+\langle x,z\rangle$ and $\langle x,ay\rangle=a\langle x,y\rangle$), and its generator matrix $H$ is the parity check matrix of $S$.
*Property 4:* Exercise 2.9.

<a id="pdf-7251cb8e4bc5-p044-b003"></a>
<!-- pdf-source: page=44; block=3; confidence=0.94 -->
Examples: $S_1$ (eq. 2.1) has generator $G_1=(1\ 1\ 1)$ and parity check $H_1=\begin{pmatrix}1&2&2\\2&2&1\end{pmatrix}$; $S_2$ (eq. 2.2) has generator $G_2$ and parity check $H_2=(1\ 1\ 2)$.

<a id="pdf-7251cb8e4bc5-p045-b001"></a>
<!-- pdf-source: page=45; block=1; confidence=0.98 -->
**Lemma 2.2.8.** If $G$ ($k\times n$) is a generator matrix of subspace $S_1$ and $H$ ($(n-k)\times n$) is a parity check matrix of subspace $S_2$ with $GH^T=0$, then $S_1=S_2$.

<a id="pdf-7251cb8e4bc5-p045-b002"></a>
<!-- pdf-source: page=45; block=2; confidence=0.97 -->
**Proof.** $S_1\subseteq S_2$: any $c\in S_1$ equals $xG$ for some $x\in\mathbb{F}_q^k$, so $H\cdot c^T=H(xG)^T=HG^Tx^T=(GH^T)^Tx^T=0$, giving $c\in S_2$. Since $H$ has full rank, its null space $S_2$ has dimension $n-(n-k)=k$ (rank–nullity); $G$ full rank gives $\dim S_1=k$. With $S_1\subseteq S_2$ and equal dimensions, $S_1=S_2$ (else $S_1\subset S_2$ forces $|S_2|\ge|S_1|+1$, impossible at equal dimension).

<a id="pdf-7251cb8e4bc5-p045-b003"></a>
<!-- pdf-source: page=45; block=3; confidence=0.99 -->
**2.3 Linear Codes and Basic Properties**

<a id="pdf-7251cb8e4bc5-p045-b004"></a>
<!-- pdf-source: page=45; block=4; confidence=0.98 -->
**Definition 2.3.1 (Linear Codes).** Let $q=p^s$ be a prime power. $C\subseteq\mathbb{F}_q^n$ is a *linear code* if it is a linear subspace of $\mathbb{F}_q^n$. If $C$ has dimension $k$ and distance $d$, it is an $[n,k,d]_q$ (or $[n,k]_q$) code.

<a id="pdf-7251cb8e4bc5-p045-b005"></a>
<!-- pdf-source: page=45; block=5; confidence=0.95 -->
By Theorem 2.2.7, an $[n,k]_q$ code $C$ is characterized either by a $k\times n$ generator matrix $G$ or by an $(n-k)\times n$ parity check matrix $H$.

<a id="pdf-7251cb8e4bc5-p045-b006"></a>
<!-- pdf-source: page=45; block=6; confidence=0.98 -->
**Definition 2.3.2 (Generator and Parity Check Matrices).** For an $[n,k]_q$ code $C$: there exists $G\in\mathbb{F}_q^{k\times n}$ of rank $k$ with $C=\{x\cdot G\mid x\in\mathbb{F}_q^k\}$ (generator matrix; $C$ = all linear combinations of rows of $G$), and there exists $H\in\mathbb{F}_q^{(n-k)\times n}$ of rank $n-k$ with $C=\{y\in\mathbb{F}_q^n\mid H\cdot y^T=0\}$ (parity check matrix).

<a id="pdf-7251cb8e4bc5-p046-b001"></a>
<!-- pdf-source: page=46; block=1; confidence=0.96 -->
Generator matrix G and parity-check matrix H are required to have full row rank. A non-full-row-rank matrix M ∈ F_q^{m×n} still generates a code C = {x·G : x ∈ F_q^m}, but C is then not an [n,m]_q code; the term "generator matrix" is reserved for full-rank matrices.

<a id="pdf-7251cb8e4bc5-p046-b002"></a>
<!-- pdf-source: page=46; block=2; confidence=0.97 -->
Generator and parity-check matrices are not unique for a code, but all generator matrices are k×n and all parity-check matrices are (n−k)×n. Examples follow for the [7,4,3]_2 Hamming code.

<a id="pdf-7251cb8e4bc5-p046-b003"></a>
<!-- pdf-source: page=46; block=3; confidence=0.95 -->
The $[7,4,3]_2$ Hamming code has generator matrix

$$G = \begin{pmatrix} 1&0&0&0&0&1&1 \\ 0&1&0&0&1&0&1 \\ 0&0&1&0&1&1&0 \\ 0&0&0&1&1&1&1 \end{pmatrix}.$$

<a id="pdf-7251cb8e4bc5-p046-b004"></a>
<!-- pdf-source: page=46; block=4; confidence=0.95 -->
A parity-check matrix of the $[7,4,3]_2$ Hamming code is

$$H = \begin{pmatrix} 0&0&0&1&1&1&1 \\ 0&1&1&0&0&1&1 \\ 1&0&1&0&1&0&1 \end{pmatrix}.$$

Since $G\cdot H^T = 0$, Lemma 2.2.8 confirms $H$ is a parity-check matrix of the code.

<a id="pdf-7251cb8e4bc5-p046-b005"></a>
<!-- pdf-source: page=46; block=5; confidence=0.94 -->
Both generator and parity-check matrices use O(n^2) symbols from F_q, far less than the exponential representation of a general code (cf. Exercise 2.11).

<a id="pdf-7251cb8e4bc5-p046-b006"></a>
<!-- pdf-source: page=46; block=6; confidence=0.97 -->
**Proposition 2.3.3.** Any [n,k]_q linear code can be represented with min(nk, n(n−k)) symbols from F_q.

<a id="pdf-7251cb8e4bc5-p046-b007"></a>
<!-- pdf-source: page=46; block=7; confidence=0.96 -->
Encoding maps a message m ∈ F_q^k to codeword C(m) = m·G in O(n^2), i.e. O(kn), time (Exercise 2.12). **Proposition 2.3.4.** For any [n,k]_q linear code, given its generator matrix, encoding can be done with O(nk) operations over F_q.

<a id="pdf-7251cb8e4bc5-p047-b001"></a>
<!-- pdf-source: page=47; block=1; confidence=0.96 -->
Error detection via the parity-check matrix runs in O(n^2), improving on brute-force exponential search over all codewords (Exercise 2.13). **Proposition 2.3.5.** For any [n,k]_q linear code, given its parity-check matrix, error detection can be performed in O(n(n−k)) operations over F_q.

<a id="pdf-7251cb8e4bc5-p047-b002"></a>
<!-- pdf-source: page=47; block=2; confidence=0.95 -->
**2.3.1 On the Distance of a Linear Code.** Minimum distance is characterized via Hamming weight of non-zero codewords (generalizing Proposition 1.5.4); wt(x) denotes the number of non-zero coordinates of x ∈ Σ^n.

<a id="pdf-7251cb8e4bc5-p047-b003"></a>
<!-- pdf-source: page=47; block=3; confidence=0.98 -->
**Proposition 2.3.6.** For every [n,k,d]_q code C, d = min_{c∈C, c≠0} wt(c).

<a id="pdf-7251cb8e4bc5-p047-b004"></a>
<!-- pdf-source: page=47; block=4; confidence=0.96 -->
**Proof.** Show d equals the minimum weight by two inequalities. (≤) Let c′ be the min-weight non-zero codeword; Δ(0,c′) = wt(c′), so d ≤ wt(c′). (≥) Pick c1 ≠ c2 ∈ C with Δ(c1,c2) = d. Then c1−c2 ∈ C (since −c2 = −1·c2 ∈ C and C is linear), and wt(c1−c2) = Δ(c1,c2) = d because non-zero symbols occur exactly where the codewords differ. As c1 ≠ c2, c1−c2 ≠ 0, so the minimum non-zero weight is ≤ d.

<a id="pdf-7251cb8e4bc5-p047-b005"></a>
<!-- pdf-source: page=47; block=5; confidence=0.97 -->
**Proposition 2.3.7.** For every [n,k,d]_q code C with parity-check matrix H, d equals the size of the smallest set of columns of H that are linearly dependent.

<a id="pdf-7251cb8e4bc5-p047-b006"></a>
<!-- pdf-source: page=47; block=6; confidence=0.90 -->
**Proof.** By Proposition 2.3.6 it suffices to show the minimum non-zero codeword weight equals t, the minimum number of linearly dependent columns of H; prove t ≤ d and t ≥ d. (continued on next page)

<a id="pdf-7251cb8e4bc5-p048-b001"></a>
<!-- pdf-source: page=48; block=1; confidence=0.94 -->
**Proof (continued).** (d ≥ t) Let c ≠ 0 ∈ C with wt(c) = d. Since H·c^T = 0, expanding gives ∑_{i=1}^n c_i H^i = 0 (H^i are columns of H). Dropping columns with c_i = 0, the columns with c_i ≠ 0 are linearly dependent, so d ≥ t. (d ≤ t) Take a minimal linearly dependent set of columns H^{i_1},…,H^{i_t}: there exist non-zero c′_{i_1},…,c′_{i_t} ∈ F_q with c′_{i_1}H^{i_1} + … + c′_{i_t}H^{i_t} = 0 (all coefficients non-zero by minimality). Extend to c′ with c′_j = 0 for j ∉ {i_1,…,i_t}; then H·(c′)^T = 0 so c′ ∈ C, giving d ≤ wt(c′) = t.

<a id="pdf-7251cb8e4bc5-p048-b002"></a>
<!-- pdf-source: page=48; block=2; confidence=0.95 -->
**2.4 Hamming Codes.** Introduces the general Hamming family: for any r ≥ 2 there is a [2^r−1, 2^r−r−1, 3]_2 Hamming code; the earlier [7,4,3]_2 code is the r = 3 case.

<a id="pdf-7251cb8e4bc5-p048-b003"></a>
<!-- pdf-source: page=48; block=3; confidence=0.96 -->
**Definition 2.4.1 (Binary Hamming Codes).** For a positive integer r, let H_r ∈ F_2^{r×(2^r−1)} be the matrix whose ith column H_r^i is the binary representation of i (a vector in {0,1}^r), for 1 ≤ i ≤ 2^r−1. The [2^r−1, 2^r−r−1]_2 Hamming code C_{H,r} is the code with parity-check matrix H_r, i.e. {c ∈ {0,1}^{2^r−1} : H_r·c^T = 0}.

<a id="pdf-7251cb8e4bc5-p048-b004"></a>
<!-- pdf-source: page=48; block=4; confidence=0.93 -->
For r = 3, H_3 is the 3×7 matrix with columns the binary representations of 1..7:

row1: 0 0 0 1 1 1 1
row2: 0 1 1 0 0 1 1
row3: 1 0 1 0 1 0 1

yielding a [7,4,3]_2 code. Next it is argued that the general Hamming code has distance 3 (shown for r = 3 in Proposition 1.5.2).

<a id="pdf-7251cb8e4bc5-p049-b001"></a>
<!-- pdf-source: page=49; block=1; confidence=0.98 -->
**Proposition 2.4.2.** The binary Hamming code $[2^r-1,\ 2^r-r-1,\ 3]_2$ has minimum distance 3.

<a id="pdf-7251cb8e4bc5-p049-b002"></a>
<!-- pdf-source: page=49; block=2; confidence=0.97 -->
**Proof.** No two columns of $H_r$ are linearly dependent: $H^i_r+H^j_r=0$ is impossible for $i\neq j$, since the columns are binary representations of distinct integers and differ in at least one bit. By Proposition 2.3.7 the distance is $\ge 3$. It is $\le 3$ because e.g. $H^1_r+H^2_r+H^3_r=0$. Hence the distance is exactly 3.

<a id="pdf-7251cb8e4bc5-p049-b003"></a>
<!-- pdf-source: page=49; block=3; confidence=0.95 -->
By the Hamming bound for $d=3$ (Theorem 1.6.2), $k\le n-\log_2(n+1)$; for $n=2^r-1$ this gives $k\le 2^r-r-1$, so the Hamming code meets the bound and is a perfect code (Definition 1.7.3). The only perfect binary codes are: the Hamming codes; the trivial $[n,1,n]_2$ codes for odd $n$ (codewords $0^n,1^n$; Exercise 2.24); and two Golay codes [28].

<a id="pdf-7251cb8e4bc5-p049-b004"></a>
<!-- pdf-source: page=49; block=4; confidence=0.98 -->
**2.5 Efficient Decoding of Hamming Codes**

<a id="pdf-7251cb8e4bc5-p049-b005"></a>
<!-- pdf-source: page=49; block=5; confidence=0.94 -->
Distance 3 gives one-error correction (Prop 1.4.2), but the only known MLD implementation (Algorithm 1.4.1) runs in $2^{\Theta(n)}$ time. A naive decoder (Algorithm 2.5.1): accept $y$ if $y\in C_{H,r}$, else flip each of the $n$ bits and test membership; fail if none works. It corrects up to 1 error. If each test costs $T(n)$, total time is $O(nT(n))$; since $C_{H,r}$ is linear with $k=n-O(\log n)$ (Prop 2.3.5), $T(n)=O(n\log n)$, giving $O(n^2\log n)$. This generalizes to any linear code $C$ of distance $2t+1$ (correcting $t$ errors) by iterating over all error vectors $z\in[q]^n$ with $\mathrm{wt}(z)\le t$ (Algorithm 2.5.2).

<a id="pdf-7251cb8e4bc5-p049-b006"></a>
<!-- pdf-source: page=49; block=6; confidence=0.90 -->
Footnote: a decoder should return the message $x$, but Algorithm 2.5.1 returns $C_{H,r}(x)$; by linearity $x$ is recoverable from $C_{H,r}(x)$ in $O(n^3)$ time (Exercise 2.25), and for $C_{H,r}$ in $O(n)$ time (Exercise 2.26).

<a id="pdf-7251cb8e4bc5-p050-b001"></a>
<!-- pdf-source: page=50; block=1; confidence=0.96 -->
**Algorithm 2.5.1 (Naive Decoder for Hamming Code).** Input: received word $y$; output: $c$ if $\Delta(y,c)\le 1$ else Fail. If $y\in C_{H,r}$, return $y$. Otherwise for $i=1,\dots,n$: set $y'\leftarrow y+e_i$ ($e_i$ the $i$th standard basis vector); if $y'\in C_{H,r}$, return $y'$. If no test succeeds, return Fail.

<a id="pdf-7251cb8e4bc5-p050-b002"></a>
<!-- pdf-source: page=50; block=2; confidence=0.95 -->
**Algorithm 2.5.2 (Decoder for Any Linear Code).** For an $[n,k,2t+1]_q$ code $C$. Input: received word $y$; output: $c\in C$ if $\Delta(y,c)\le t$ else Fail. For $i=0,\dots,t$: for each $S\subseteq[n]$ with $|S|=i$: for each $z\in\mathbb{F}_q^n$ with $\mathrm{wt}(z_S)=\mathrm{wt}(z)=i$: if $y-z\in C$, return $y-z$. Otherwise return Fail.

<a id="pdf-7251cb8e4bc5-p050-b003"></a>
<!-- pdf-source: page=50; block=3; confidence=0.95 -->
The number of error patterns considered is $\sum_{i=0}^{t}\binom{n}{i}(q-1)^i\le O((nq)^t)$. By Prop 2.3.5 the membership test (Step 4) uses $O(n^2)$ operations over $\mathbb{F}_q$, so Algorithm 2.5.2 runs in $O(n^{t+2}q^t)$ operations over $\mathbb{F}_q$, i.e. $n^{O(t)}$ for $q$ a small polynomial in $n$ — polynomial time for constant distance, though impractical for moderate $t$.

<a id="pdf-7251cb8e4bc5-p050-b004"></a>
<!-- pdf-source: page=50; block=4; confidence=0.95 -->
For Hamming codes an $O(n^2)$-time decoder exists via syndromes. If $y$ is error-free then $H_r\cdot y^T=0$. Otherwise $y=c+e_i$ with $c\in C$, and $H_r\cdot y^T = H_r c^T + H_r e_i^T = H_r e_i^T = H^i_r$ (the $i$th column of $H_r$), since $H_r c^T=0$ for $c\in C$. Thus $H_r\cdot y^T$ gives the error location, leading to Algorithm 2.5.3. Since $H_r$ is $r\times n$ with $n=2^r-1$, $r=\Theta(\log n)$, so the Step 1 matrix–vector product takes $O(n\log n)$.

<a id="pdf-7251cb8e4bc5-p051-b001"></a>
<!-- pdf-source: page=51; block=1; confidence=0.96 -->
**Algorithm 2.5.3 (Efficient Decoder for Hamming Code).** Input: received word $y$; output: $c$ if $\Delta(y,c)\le 1$ else Fail. (1) $b\leftarrow H_r\cdot y^T$; (2) let $i\in[n]$ be the integer whose binary representation is $b$; (3) if $y-e_i\in C_H$, return $y-e_i$; (5) return Fail.

<a id="pdf-7251cb8e4bc5-p051-b002"></a>
<!-- pdf-source: page=51; block=2; confidence=0.96 -->
Step 1 takes $O(n\log n)$; by a similar argument with Prop 2.3.5, Step 3 also takes $O(n\log n)$, so Algorithm 2.5.3 runs in $O(n\log n)$ time overall.

<a id="pdf-7251cb8e4bc5-p051-b003"></a>
<!-- pdf-source: page=51; block=3; confidence=0.98 -->
**Theorem 2.5.1.** The $[n=2^r-1,\ 2^r-r-1,\ 3]_2$ Hamming code is 1-error correctable, and decoding can be performed in $O(n\log n)$ time.

<a id="pdf-7251cb8e4bc5-p051-b004"></a>
<!-- pdf-source: page=51; block=4; confidence=0.98 -->
**2.6 Dual of a Linear Code**

<a id="pdf-7251cb8e4bc5-p051-b005"></a>
<!-- pdf-source: page=51; block=5; confidence=0.95 -->
Instead of using a parity check matrix to define a code via its null space, one may use it as a generator matrix, motivating the following definition.

<a id="pdf-7251cb8e4bc5-p051-b006"></a>
<!-- pdf-source: page=51; block=6; confidence=0.98 -->
**Definition 2.6.1 (Dual of a code).** If $H$ is a parity check matrix of a code $C$, the code generated by $H$ is called the dual of $C$, denoted $C^\perp$.

<a id="pdf-7251cb8e4bc5-p051-b007"></a>
<!-- pdf-source: page=51; block=7; confidence=0.97 -->
If $C$ is an $[n,k]_q$ code, then $C^\perp$ is an $[n,\ n-k]_q$ code.

<a id="pdf-7251cb8e4bc5-p051-b008"></a>
<!-- pdf-source: page=51; block=8; confidence=0.96 -->
**Definition 2.6.2 (Simplex and Hadamard Codes).** For a positive integer $r$, the Simplex code $C_{\mathrm{Sim},r}$ is generated by $H_r$ (equivalently $C_{\mathrm{Sim},r}=C_{H,r}^\perp$). The Hadamard code $C_{\mathrm{Had},r}$ is the $[2^r, r]_2$ code generated by the $r\times 2^r$ matrix $H'_r$ obtained by adding the all-zero column (in front of the columns) to $H_r$.

<a id="pdf-7251cb8e4bc5-p051-b009"></a>
<!-- pdf-source: page=51; block=9; confidence=0.96 -->
Claim: $C_{\mathrm{Sim},r}$ and $C_{\mathrm{Had},r}$ are $[2^r-1,\ r,\ 2^{r-1}]_2$ and $[2^r,\ r,\ 2^{r-1}]_2$ codes respectively. Block length and dimension follow from the definitions; the distance follows from Proposition 2.6.3.

<a id="pdf-7251cb8e4bc5-p051-b010"></a>
<!-- pdf-source: page=51; block=10; confidence=0.98 -->
**Proposition 2.6.3.** Both $C_{\mathrm{Sim},r}$ and $C_{\mathrm{Had},r}$ have distance $2^{r-1}$.

<a id="pdf-7251cb8e4bc5-p051-b011"></a>
<!-- pdf-source: page=51; block=11; confidence=0.95 -->
**Proof.** The result is shown first for $C_{\mathrm{Had},r}$, in fact a stronger claim: every nonzero codeword of $C_{\mathrm{Had},r}$ has weight exactly $2^{r-1}$ (the claimed distance). [The proof is truncated at the end of the supplied pages.]

<a id="pdf-7251cb8e4bc5-p052-b001"></a>
<!-- pdf-source: page=52; block=1; confidence=0.95 -->
**Proof (continued).** For nonzero message $x$ with $x_i=1$, the encoding is $c=(x_1,\dots,x_r)(H^0_r,H^1_r,\dots,H^{2^r-1}_r)$, where $H^j_r$ is the binary representation of $j$, $0\le j\le 2^r-1$, so the columns range over all of $\{0,1\}^r$ and the $j$th bit of $c$ is $\langle x,H^j_r\rangle$. Pair the generator columns as $(u,v)$ with $v=u+e_i$, giving $2^{r-1}$ disjoint pairs. Then $\langle x,v\rangle=\langle x,u+e_i\rangle=\langle x,u\rangle+x_i=\langle x,u\rangle+1$, so exactly one of $\langle x,u\rangle,\langle x,v\rangle$ equals $1$. Hence every nonzero $c\in C_{Had,r}$ has $\mathrm{wt}(c)=2^{r-1}$. Since $C_{Had,r}$ codewords are $C_{Sim,r}$ codewords with a leading $0$ padded, every nonzero $C_{Sim,r}$ codeword also has weight $2^{r-1}$, completing the proof.

<a id="pdf-7251cb8e4bc5-p052-b002"></a>
<!-- pdf-source: page=52; block=2; confidence=0.97 -->
Remark: the Hamming code family has rate $1$ and relative distance $0$; the Simplex/Hadamard families have rate $0$ and relative distance $1/2$. Neither resolves Question 1.8.3, so an asymptotically good code is not yet obtained.

<a id="pdf-7251cb8e4bc5-p052-b003"></a>
<!-- pdf-source: page=52; block=3; confidence=0.99 -->
## 2.7 Exercises

<a id="pdf-7251cb8e4bc5-p052-b004"></a>
<!-- pdf-source: page=52; block=4; confidence=0.98 -->
**Exercise 2.1.** For a field $(S,+,\cdot)$ (Definition 2.1.2), show $a\cdot 0=0\cdot a=0$ for every $a\in S$.

<a id="pdf-7251cb8e4bc5-p052-b005"></a>
<!-- pdf-source: page=52; block=5; confidence=0.98 -->
**Exercise 2.2.** Prove that $\mathbb{Q}$, the set of reals of the form $a/b$ with $a,b$ integers and $b\neq 0$, is a field.

<a id="pdf-7251cb8e4bc5-p052-b006"></a>
<!-- pdf-source: page=52; block=6; confidence=0.98 -->
**Exercise 2.3.** For a prime power $q$ and $x\in\mathbb{F}_q$ with $x\notin\{0,1\}$, prove that for any $n\le q-1$: $\sum_{i=0}^{n}x^i=\dfrac{x^{n+1}-1}{x-1}$.

<a id="pdf-7251cb8e4bc5-p053-b001"></a>
<!-- pdf-source: page=53; block=1; confidence=0.96 -->
**Exercise 2.4.** Goal: prove for any $\alpha\in\mathbb{F}_q$, $\alpha^q=\alpha$ (2.4). A group $G=(S,\circ)$ has $\circ:G\times G\to G$ commutative (abelian), closed, with identity $\iota\in S$ and every $a\in S$ having an inverse $b$ with $a\circ b=\iota$; $\mathbb{F}_q$ has an additive group (identity $0$) and a multiplicative group $\mathbb{F}_q^*$ (identity $1$). Let $G=(S,\cdot)$ with $|G|=m$; prove: (1) for $\beta\in G$, the order $o(\beta)$ = smallest $o$ with $\beta^o=1$ exists with $o\le m$, and $T=\{1,\beta,\dots,\beta^{o-1}\}$ is a subgroup; (2) the coset $gT=\{g\cdot\beta\mid\beta\in T\}$ satisfies $gT=hT$ if $h^{-1}g\in T$ and $gT\cap hT=\emptyset$ otherwise, and cosets partition $G$; (3) $|gT|=|T|$; (4) $\beta^m=1$ for all $\beta\in G$; (5) deduce (2.4).

<a id="pdf-7251cb8e4bc5-p053-b002"></a>
<!-- pdf-source: page=53; block=2; confidence=0.98 -->
**Exercise 2.5.** Prove that for $q=2$ the second condition in Definition 2.2.2 is implied by the first.

<a id="pdf-7251cb8e4bc5-p053-b003"></a>
<!-- pdf-source: page=53; block=3; confidence=0.98 -->
**Exercise 2.6.** Prove that $G_2$ from (2.3) has full rank.

<a id="pdf-7251cb8e4bc5-p053-b004"></a>
<!-- pdf-source: page=53; block=4; confidence=0.95 -->
**Exercise 2.7.** Solving a system of $m$ linear equations over $\mathbb{F}_q$ for unknowns $x_1,\dots,x_n$, with $a_{i,j},b_i\in\mathbb{F}_q$: $a_{i,1}x_1+a_{i,2}x_2+\cdots+a_{i,n}x_n=b_i$ for $1\le i\le m$ (first equation $a_{1,1}x_1+\cdots+a_{1,n}x_n=b_1$). (Continues on next page.)

<a id="pdf-7251cb8e4bc5-p054-b001"></a>
<!-- pdf-source: page=54; block=1; confidence=0.95 -->
**Exercise 2.7 (continued).** (1) State the system as $A\cdot x^T=b^T$ with $A$ an $m\times n$ matrix over $\mathbb{F}_q$, $x\in\mathbb{F}_q^n$, $b\in\mathbb{F}_q^m$. (2) For $n=m$ and $A$ upper triangular (all $a_{i,i}\neq0$, $a_{i,j}=0$ for $i>j$), give an $O(n^2)$ algorithm for $x$. (3) Gaussian elimination when $A$ has full rank $n$: (a) prove Gauss's procedure — permute columns so $a_{1,1}\neq0$, multiply each row $1<i\le n$ by $a_{1,1}/a_{i,1}$ then subtract $a_{1,j}$ from entry $(i,j)$, recurse on the $(n-1)\times(n-1)$ submatrix — yields an upper triangular matrix; (b) modify it to either upper-triangulate or report $A$ is not full rank; (c) call $A x^T=b^T$ consistent if a solution $x\in\mathbb{F}_q^n$ exists, and give an $O(n^3)$ algorithm finding it when consistent and $A$ full rank (else "fail"). (4) For $m<n$ with $A$ full rank $m$: the system is inconsistent or has $q^{n-m}$ solutions; give an $O(m^2n)$ algorithm outputting the solutions (with $n-m$ free and $m$ bound variables) or reporting inconsistency, noting solutions are represented as a linear system. (5) For $m>n$ with $A$ full rank $n$: the system is inconsistent or has a unique solution; give an $O(m^2n)$ algorithm to output it or report inconsistency. (Basic $\mathbb{F}_q$ operations take unit time.)

<a id="pdf-7251cb8e4bc5-p055-b001"></a>
<!-- pdf-source: page=55; block=1; confidence=0.90 -->
**Exercise (part 6, non-full-rank case).** Give an O(m²n) algorithm to solve a linear system with an m×n matrix A that need not have full rank; the algorithm either reports the system inconsistent or outputs the solution(s) x.

<a id="pdf-7251cb8e4bc5-p055-b002"></a>
<!-- pdf-source: page=55; block=2; confidence=0.98 -->
**Exercise 2.8.** Prove that the span of k linearly independent vectors over F_q has size exactly q^k.

<a id="pdf-7251cb8e4bc5-p055-b003"></a>
<!-- pdf-source: page=55; block=3; confidence=0.98 -->
**Exercise 2.9.** If G and H are a generator matrix and parity-check matrix of the same linear code of dimension k and block length n, then G·Hᵀ = 0.

<a id="pdf-7251cb8e4bc5-p055-b004"></a>
<!-- pdf-source: page=55; block=4; confidence=0.97 -->
**Exercise 2.10.** Let C be an [n,k]_q linear code with a generator matrix having no all-zero columns. Then for every position i∈[n] and every α∈F_q, the number of codewords c∈C with c_i = α is exactly q^{k−1}.

<a id="pdf-7251cb8e4bc5-p055-b005"></a>
<!-- pdf-source: page=55; block=5; confidence=0.95 -->
**Exercise 2.11.** Prove Proposition 2.3.3. **Exercise 2.12.** Prove Proposition 2.3.4. **Exercise 2.13.** Prove Proposition 2.3.5.

<a id="pdf-7251cb8e4bc5-p055-b006"></a>
<!-- pdf-source: page=55; block=6; confidence=0.96 -->
**Exercise 2.14.** Definition: S ⊆ F_q^n is *t-wise independent* if for every position set I with |I|=t, the projection of S onto I contains each vector of F_q^t the same number of times (equivalently, for a uniform random (X_1,…,X_n)∈S, the coordinates {X_i : i∈I} are uniform and independent over F_q). Prove: any linear code C whose dual C^⊥ has distance d^⊥ is (d^⊥ − 1)-wise independent.

<a id="pdf-7251cb8e4bc5-p055-b007"></a>
<!-- pdf-source: page=55; block=7; confidence=0.95 -->
**Exercise 2.15.** Definition: S ⊆ F_2^k is an *ε-biased sample space* if for X=(x_1,…,x_k) uniform from S and every I⊆[k], |Pr(∑_{i∈I} x_i = 0) − Pr(∑_{i∈I} x_i = 1)| ≤ ε. Prove:
1. If C is an [n,k]_2 code whose nonzero codewords all have Hamming weight in [((1−ε)/2)·n, ((1+ε)/2)·n], then there exists an ε-biased space of size n in F_2^k.
2. If C is an [n,k]_2 code whose nonzero codewords all have Hamming weight in [((1/2)−γ)·n, ((1/2)+γ)·n] for a constant 0<γ<1/2, then there exists an ε-biased space in F_2^k of size n^{O(γ^{−1}·log(1/ε))}.

<a id="pdf-7251cb8e4bc5-p056-b001"></a>
<!-- pdf-source: page=56; block=1; confidence=0.97 -->
**Exercise 2.16.** Let C be an [n,k,d]_q code and y=(y_1,…,y_n)∈(F_q∪{?})^n a received word with y_i=? in at most d−1 positions. Present an O(n³) algorithm that outputs a codeword c∈C agreeing with y on all un-erased positions (c_i=y_i whenever y_i≠?), or reports that no such c exists (such c, if it exists, is unique).

<a id="pdf-7251cb8e4bc5-p056-b002"></a>
<!-- pdf-source: page=56; block=2; confidence=0.95 -->
**Exercise 2.17.**
(a) Prove any k×n generator matrix G of an [n,k]_q code C can be converted to an equivalent generator matrix G′ = [I_k | A] with A a k×(n−k) matrix (equivalent meaning the code of G′ has a linear bijection to C); such codes, with the message as the first k codeword symbols, are systematic.
(b) Given a generator matrix [I_k | A], give a corresponding (n−k)×n parity-check matrix and justify correctness. (Hint: build it from a submatrix related to A and an identity submatrix, the identity not necessarily k×k.)
(c) Use (b) to give a generator matrix for the [2^r−1, 2^r−r−1, 3]_2 Hamming code.

<a id="pdf-7251cb8e4bc5-p056-b003"></a>
<!-- pdf-source: page=56; block=3; confidence=0.96 -->
**Exercise 2.18.** Notation: (n,k,d)_q denotes a general code with q^k codewords (k need not be an integer); [n,k,d]_q denotes a linear code of dimension k. Using only the stated parameters, prove:
1. An (n,k,d)_{2^m} code implies an (nm, km, d′≥d)_2 code.
2. An [n,k,d]_{2^m} code implies an [nm, km, d′≥d]_2 code.
3. An [n,k,d]_q code implies an [n−d, k−1, d′≥⌈d/q⌉]_q code.

<a id="pdf-7251cb8e4bc5-p057-b001"></a>
<!-- pdf-source: page=57; block=1; confidence=0.95 -->
**Exercise 2.18 (continued).**
4. An [n,k,δn]_q code implies, for every m≥1, an (nm, k/m, (1−(1−δ)^m)·nm)_{q^m} code.
5. An [n,k,δn]_2 code implies, for every odd m≥1, an [nm, k, ½·(1−(1−2δ)^m)·nm]_2 code.
Note: in all parts only the parameters given by the original code's definition may be assumed.

<a id="pdf-7251cb8e4bc5-p057-b002"></a>
<!-- pdf-source: page=57; block=2; confidence=0.94 -->
**Exercise 2.19.** For C_1 an [n,k_1,d_1]_q code and C_2 an [n,k_2,d_2]_q code, define C_1 ⊖ C_2 = {(c_1, c_1+c_2) : c_1∈C_1, c_2∈C_2}. Prove:
1. Given generator matrices G_i of C_i, give a generator matrix of C_1⊖C_2.
2. C_1⊖C_2 is a [2n, k_1+k_2, d]_q code with d := min(2d_1, d_2).
3. If A_1 decodes C_1 from e errors and s erasures whenever 2e+s<d_1, and A_2 decodes C_2 from ⌊(d_2−1)/2⌋ errors, then ⌊(d−1)/2⌋ errors can be corrected for C_1⊖C_2. (Hint: on received (y_1,y_2), apply A_2 to y_2−y_1, then form an intermediate received word for A_1.)
4. Recursive binary linear code C(r,m) for 0≤r≤m: C(r,r)=F_2^r; C(0,r) is the 2-codeword code {all-ones, all-zeros} in F_2^r; for 1<r<m, C(r,m)=C(r,m−1) ⊖ C(r−1,m−1). Determine the parameters of C(r,m).

<a id="pdf-7251cb8e4bc5-p057-b003"></a>
<!-- pdf-source: page=57; block=3; confidence=0.95 -->
**Exercise 2.20.** Let C_1 be an [n_1,k_1,d_1]_2 binary linear code and C_2 an [n_2,k_2,d_2] binary linear code. Let C ⊆ F_2^{n_1×n_2} be the set of n_2×n_1 matrices whose rows lie in C_1 and whose columns lie in C_2; this is the tensor C_1 ⊗ C_2. Prove C is an [n_1 n_2, k_1 k_2, d_1 d_2]_2 binary linear code. Further, given generator matrices G_1, G_2 of C_1, C_2, construct a generator matrix of C_1⊗C_2 and argue it is computable in polynomial time. (Hint: treat codewords and messages as vectors rather than matrices.)

<a id="pdf-7251cb8e4bc5-p058-b001"></a>
<!-- pdf-source: page=58; block=1; confidence=0.96 -->
**Exercise 2.21.** Generalized q-ary Hamming code, for q a prime power and integer r ≥ 1. Let H_{q,r} be the r × n matrix whose columns are exactly the nonzero vectors of F_q^r whose first nonzero entry is 1 (example given: H_{3,2} = [[0,1,1,1],[1,0,1,2]]). Define C_{H,r,q} to be the linear code with parity-check matrix H_{q,r}. Argue: (1) block length n = (q^r − 1)/(q − 1); (2) dimension n − r; (3) distance 3.

<a id="pdf-7251cb8e4bc5-p058-b002"></a>
<!-- pdf-source: page=58; block=2; confidence=0.95 -->
**Exercise 2.22.** Generalized q-ary Hadamard code, q a prime power, r ≥ 1. Let H_{q,r} be the r × q^r matrix whose columns are all vectors in F_q^r. Define C_{Had,r,q} to be the linear code with parity-check matrix H_{q,r}. Argue: (1) block length n = q^r; (2) dimension r; (3) distance (1 − 1/q)·n.

<a id="pdf-7251cb8e4bc5-p058-b003"></a>
<!-- pdf-source: page=58; block=3; confidence=0.97 -->
**Exercise 2.23.** Design the best possible 6-ary code family with distance 3. Hint: start from a 7-ary Hamming code.

<a id="pdf-7251cb8e4bc5-p058-b004"></a>
<!-- pdf-source: page=58; block=4; confidence=0.96 -->
**Exercise 2.24.** Prove that the [n, 1, n]_2 code for odd n — the code whose only two codewords are the all-zeros and all-ones vectors — attains the Hamming bound (Theorem 1.7.2).

<a id="pdf-7251cb8e4bc5-p058-b005"></a>
<!-- pdf-source: page=58; block=5; confidence=0.96 -->
**Exercise 2.25.** Let C be an [n, k]_q code with generator matrix G. Show that given a codeword c ∈ C, the corresponding message can be computed in time O(kn²).

<a id="pdf-7251cb8e4bc5-p058-b006"></a>
<!-- pdf-source: page=58; block=6; confidence=0.95 -->
**Exercise 2.26.** Show that given c ∈ C_{H,r}, the corresponding message can be computed in time O(n).

<a id="pdf-7251cb8e4bc5-p058-b007"></a>
<!-- pdf-source: page=58; block=7; confidence=0.90 -->
**Exercise 2.27.** Let C be an (n, k)_q code. Prove that if C can be decoded from e errors in time T(n), then it can be decoded from n + c errors in time O((nq)^c · T(n)).

<a id="pdf-7251cb8e4bc5-p058-b008"></a>
<!-- pdf-source: page=58; block=8; confidence=0.94 -->
**Exercise 2.28.** Show that the bound of kd on the number of ones in the generator matrix of any binary linear code (Exercise 1.14) cannot be improved for every code (i.e., it is tight).

<a id="pdf-7251cb8e4bc5-p059-b001"></a>
<!-- pdf-source: page=59; block=1; confidence=0.98 -->
**Exercise 2.29.** For a linear code C, prove that (C^⊥)^⊥ = C.

<a id="pdf-7251cb8e4bc5-p059-b002"></a>
<!-- pdf-source: page=59; block=2; confidence=0.96 -->
**Exercise 2.30.** For any linear code, 0 lies in both C and C^⊥. Show that there exists a linear code C that shares a nonzero codeword with C^⊥.

<a id="pdf-7251cb8e4bc5-p059-b003"></a>
<!-- pdf-source: page=59; block=3; confidence=0.95 -->
**Exercise 2.31.** (Contrast of finite vs. infinite fields.) Let S ⊆ R^n be a linear subspace over R with dual S^⊥. Prove that S ∩ S^⊥ = {0}. By contrast, subspaces over finite fields can intersect their duals nontrivially (cf. Exercise 2.30). [Footnote: a real linear subspace is as in Definition 2.2.2 with F_q replaced by R.]

<a id="pdf-7251cb8e4bc5-p059-b004"></a>
<!-- pdf-source: page=59; block=4; confidence=0.96 -->
**Exercise 2.32.** C is self-orthogonal if C ⊆ C^⊥. Show: (1) the binary repetition code with an even number of repetitions is self-orthogonal; (2) the Hadamard code C_{Had,r} is self-orthogonal.

<a id="pdf-7251cb8e4bc5-p059-b005"></a>
<!-- pdf-source: page=59; block=5; confidence=0.96 -->
**Exercise 2.33.** C is self-dual if C = C^⊥. Show: (1) any self-dual code has dimension n/2; (2) the code {(x, x) | x ∈ F_2^k} is self-dual.

<a id="pdf-7251cb8e4bc5-p059-b006"></a>
<!-- pdf-source: page=59; block=6; confidence=0.88 -->
**Exercise 2.34.** Puncturing: for C ⊆ Σ^n and punctured positions P ⊆ [n], the punctured code is {(c_i)_{i∉P} | (c_1,…,c_n) ∈ C}. Prove that any linear code with no repeated positions — i.e., no two positions i ≠ j such that c_i = c_i for every codeword c ∈ C — is a puncturing of the Hadamard code; hence the Hadamard code is the longest non-repeating linear code.

<a id="pdf-7251cb8e4bc5-p060-b001"></a>
<!-- pdf-source: page=60; block=1; confidence=0.85 -->
**Exercise 2.35.** Long code (functional view of the ambient space, Remark 1.2.2). A dimension-k long code is a binary code where the codeword for x ∈ F_2^k is the function f : {0,1}^{2^k} → {0,1} defined, for m ∈ {0,1}^{F_2^k}, by f((m_α)_{α∈F_2^k}) = m_x. Derive the parameters of the long code. Argue that it has the longest block length among codes whose codewords have no repeated coordinate (no i ≠ j with c_i = c_j for every codeword c), contrasting with the Hadamard code.

<a id="pdf-7251cb8e4bc5-p060-b002"></a>
<!-- pdf-source: page=60; block=2; confidence=0.90 -->
**Exercise 2.36.** For a linear code C ⊆ F_2^n, define its generating function as the 2n-variate polynomial in x = (x_1,…,x_n), y = (y_1,…,y_n): G_C(x, y) = ∑_{w∈C} P_w(x, y), where P_w(x, y) = (∏_{i: w_i=0} x_i)·(∏_{i: w_i=1} y_i). For w ∈ {0,…,n} let A_C^w be the number of weight-w codewords, and A_C(z) = ∑_{w=0}^n A_C^w z^w the weight-enumerator polynomial. Prove: (1) for every w ∈ F_2^n, P_w(x+y, x−y) = ∑_{v∈F_2^n} (−1)^{⟨v,w⟩} P_v(x, y); (2) G_{C^⊥}(x, y) = (1/|C|) · G_C(x+y, x−y); (3) A_C(z) = G_C(1,…,1, z,…,z); (4) A_{C^⊥}(z) = ((1+z)^n/|C|) · A_C((1−z)/(1+z)); (5) conclude A_w^{C^⊥} = (1/|C|) ∑_{u=0}^n A_u^C (∑_{i=0}^u (−1)^i C(u,i) C(n−u, w−i)) — so the primal weight distribution (A_0^C,…,A_n^C) completely determines the dual distribution (A_0^{C^⊥},…,A_n^{C^⊥}).

<a id="pdf-7251cb8e4bc5-p060-b003"></a>
<!-- pdf-source: page=60; block=3; confidence=0.97 -->
**Section 2.8 — Bibliographic Notes.**

<a id="pdf-7251cb8e4bc5-p060-b004"></a>
<!-- pdf-source: page=60; block=4; confidence=0.90 -->
Expository notes with references: algebra background (Artin [3]); finite fields (Lidl–Niederreiter [47]); linear codes originating with Hamming [35] and systematized by Slepian [69]; answer to Question 1.7.4 by van Lint [72] and Tietäväinen [71]; Hadamard codes (Definition 2.6.2) named for Jacques Hadamard and Hadamard matrices. Exercises 2.14–2.15 come from pseudorandomness (Chapter reference omitted); long codes (Exercise 2.35) introduced by Bellare–Goldreich–Sudan [5]; Exercise 2.36 based on the MacWilliams Identity [48].

<a id="pdf-7251cb8e4bc5-p061-b001"></a>
<!-- pdf-source: page=61; block=1; confidence=0.98 -->
# Chapter 3 — Probability as Fancy Counting and the q-ary Entropy Function

<a id="pdf-7251cb8e4bc5-p061-b002"></a>
<!-- pdf-source: page=61; block=2; confidence=0.95 -->
Chapter motivates existence questions of the form "given $n,k,d,q$, does an $(n,k,d)_q$ code exist?" and introduces the **probabilistic method** (existence via positive probability of a random object). §3.1 covers probability basics, §3.2 the probabilistic method, §3.3 the entropy function.

<a id="pdf-7251cb8e4bc5-p061-b003"></a>
<!-- pdf-source: page=61; block=3; confidence=0.95 -->
**Question 3.0.1.** Does there exist a $[2,2,1]_2$ code? Answer is trivially yes (take the $2\times2$ identity as generator matrix); the intended probabilistic proof is noted to generalize to later chapters.

<a id="pdf-7251cb8e4bc5-p061-b004"></a>
<!-- pdf-source: page=61; block=4; confidence=0.95 -->
## 3.1 A Crash Course on Probability

Reviews distributions, events, and random variables, restricted to finite spaces.

<a id="pdf-7251cb8e4bc5-p061-b005"></a>
<!-- pdf-source: page=61; block=5; confidence=0.96 -->
**Definition (probability distribution).** For a finite domain $D$, a probability distribution is a function $p : D \to [0,1]$ with $\sum_{x\in D} p(x) = 1$.

<a id="pdf-7251cb8e4bc5-p062-b001"></a>
<!-- pdf-source: page=62; block=1; confidence=0.92 -->
**Table 3.1.** Lists the uniform distribution over $\mathbb{F}_2^{2\times2}$ (each of 16 matrices $G$ with probability $\tfrac{1}{16}$) together with values of four random variables $V_{00},V_{01},V_{10},V_{11}$ and the value $U(G)$; notation for $G$ is defined by Eq. (3.1).

<a id="pdf-7251cb8e4bc5-p062-b002"></a>
<!-- pdf-source: page=62; block=2; confidence=0.94 -->
**Definition (event).** An event $E$ is a predicate over $D$, equivalently a subset of $D$ (the elements mapped to true). Logical and set notation are interchangeable: disjunction $E_1\vee E_2 = E_1\cup E_2$, conjunction $E_1\wedge E_2 = E_1\cap E_2$, negation $\neg E_1 = \overline{E_1}$.

<a id="pdf-7251cb8e4bc5-p062-b003"></a>
<!-- pdf-source: page=62; block=3; confidence=0.96 -->
**Definition 3.1.1 (Uniform Distribution).** The uniform distribution over $D$, denoted $U_D$, satisfies $\Pr_{U_D}(x) = \tfrac{1}{|D|}$ for every $x\in D$. Subscript dropped when $D$ is clear.

<a id="pdf-7251cb8e4bc5-p062-b004"></a>
<!-- pdf-source: page=62; block=4; confidence=0.85 -->
Example with $D=\mathbb{F}_2^{2\times2}$, the set of $2\times2$ matrices over $\mathbb{F}_2$ (each a generator matrix of some $[2,2]_2$ code). Matrix notation (Eq. (3.1)): $M_{b_{00},b_{10},b_{10},b_{11}} = \begin{pmatrix} b_{00} & b_{10} \\ b_{10} & b_{11}\end{pmatrix}$.

<a id="pdf-7251cb8e4bc5-p062-b005"></a>
<!-- pdf-source: page=62; block=5; confidence=0.95 -->
**Definition 3.1.2 (Random Variable).** For a finite domain $D$, a finite subset $I\subset\mathbb{R}$, and a distribution $p$ over $D$, a random variable is a function $V : D \to I$. (Footnotes: restricted to real-valued $V$ and finite $I$ for this book.)

<a id="pdf-7251cb8e4bc5-p063-b001"></a>
<!-- pdf-source: page=63; block=1; confidence=0.96 -->
**Definition (expectation).** $E[V] = \sum_{x\in D} p(x)\cdot V(x)$.

<a id="pdf-7251cb8e4bc5-p063-b002"></a>
<!-- pdf-source: page=63; block=2; confidence=0.90 -->
For $(i,j)\in\{0,1\}^2$, define $V_{ij}(G) = \mathrm{wt}((i,j)\cdot G)$ for $G\in\mathbb{F}_2^{2\times2}$; these four are tabulated in Table 3.1.

<a id="pdf-7251cb8e4bc5-p063-b003"></a>
<!-- pdf-source: page=63; block=3; confidence=0.88 -->
**Definition (indicator variable).** Binary random variables have $I=\{0,1\}$. For an event $E$ over $D$, its indicator $\mathbb{1}_E : D\to\{0,1\}$ is $\mathbb{1}_E(x)=1$ if $x\in E$ and $0$ otherwise. Example: $\mathbb{1}_{V_{01}=0}\big(\begin{smallmatrix}0&1\\0&0\end{smallmatrix}\big)=1$ and $\mathbb{1}_{V_{01}=0}\big(\begin{smallmatrix}0&1\\1&1\end{smallmatrix}\big)=0$. Notation abbreviated to $\mathbb{1}_E$ or $E$.

<a id="pdf-7251cb8e4bc5-p063-b004"></a>
<!-- pdf-source: page=63; block=4; confidence=0.90 -->
Computed expectations: $E[\mathbb{1}_{V_{00}=0}] = 16\cdot\tfrac{1}{16} = 1$; and $E[\mathbb{1}_{V_{01}=0}] = E[\mathbb{1}_{V_{10}=0}] = E[\mathbb{1}_{V_{11}=0}] = 4\cdot\tfrac{1}{16} = \tfrac14$ (Eqs. (3.2), (3.3), (3.4)).

<a id="pdf-7251cb8e4bc5-p063-b005"></a>
<!-- pdf-source: page=63; block=5; confidence=0.95 -->
### 3.1.1 Some Useful Results

<a id="pdf-7251cb8e4bc5-p063-b006"></a>
<!-- pdf-source: page=63; block=6; confidence=0.94 -->
**Lemma 3.1.3.** For any event $E$, $E[\mathbb{1}_E] = \Pr[E\text{ is true}]$. (Proof deferred to Exercise 3.1.) The text then announces a forthcoming property on the expectation of a sum of random variables.

<a id="pdf-7251cb8e4bc5-p064-b001"></a>
<!-- pdf-source: page=64; block=1; confidence=0.97 -->
**Proposition 3.1.4 (Linearity of Expectation).** For random variables $V_1,\dots,V_m$ over a common domain $D$ with the same distribution $p$, $E\!\left[\sum_{i=1}^m V_i\right]=\sum_{i=1}^m E[V_i]$.

<a id="pdf-7251cb8e4bc5-p064-b002"></a>
<!-- pdf-source: page=64; block=2; confidence=0.96 -->
**Proof.** Let $V=V_1+\cdots+V_m$. Then $E[V]=\sum_{x\in D}V(x)p(x)$ (3.5) $=\sum_{x\in D}\big(\sum_{i=1}^m V_i(x)\big)p(x)$ (3.6) $=\sum_{i=1}^m\sum_{x\in D}V_i(x)p(x)$ (3.7) $=\sum_{i=1}^m E[V_i]$ (3.8). (3.5),(3.8) use the definition of expectation; (3.6) the definition of $V$; (3.7) swaps the summation order.

<a id="pdf-7251cb8e4bc5-p064-b003"></a>
<!-- pdf-source: page=64; block=3; confidence=0.90 -->
Example: $E[\mathbb{1}_{V_{01}=0}+\mathbb{1}_{V_{10}=0}+\mathbb{1}_{V_{11}=0}]=\tfrac34$ (3.9).

<a id="pdf-7251cb8e4bc5-p064-b004"></a>
<!-- pdf-source: page=64; block=4; confidence=0.96 -->
Motivation: bounding the probability of a union of events. **Proposition 3.1.5 (Union Bound).** For binary random variables $A_1,\dots,A_m$, $\Pr\!\left[\big(\bigvee_{i=1}^m A_i\big)=1\right]\le\sum_{i=1}^m\Pr[A_i=1]$.

<a id="pdf-7251cb8e4bc5-p064-b005"></a>
<!-- pdf-source: page=64; block=5; confidence=0.95 -->
**Proof.** For each $i\in[m]$ define $S_i=\{x\in D\mid A_i(x)=1\}$. Then $\Pr\!\left[\big(\bigvee_{i=1}^m A_i\big)=1\right]=\sum_{x\in\cup_{i=1}^m S_i}p(x)$ (3.10) $\le\sum_{i=1}^m\sum_{x\in S_i}p(x)$ (3.11) $=\sum_{i=1}^m\Pr[A_i=1]$ (3.12).

<a id="pdf-7251cb8e4bc5-p065-b001"></a>
<!-- pdf-source: page=65; block=1; confidence=0.94 -->
**Proof (cont.).** (3.10),(3.12) follow from the definition of $S_i$; (3.11) because some $x\in\cup_i S_i$ are counted more than once. Remark: the bound is tight when the events are disjoint, i.e. $S_i\cap S_j=\emptyset$ for all $i\ne j$.

<a id="pdf-7251cb8e4bc5-p065-b002"></a>
<!-- pdf-source: page=65; block=2; confidence=0.90 -->
Example: with $A_1=\mathbb{1}_{V_{01}=0}$, $A_2=\mathbb{1}_{V_{10}=0}$, $A_3=\mathbb{1}_{V_{11}=0}$, the event $A_1\vee A_2\vee A_3$ equals the event that some nonzero $m\in\{0,1\}^2$ satisfies $\mathrm{wt}(mG)=0$. Under the uniform distribution over $\mathbb{F}_2^{2\times2}$, the union bound gives $\Pr[\exists\,m\in\{0,1\}^2\setminus\{(0,0)\}:\ \mathrm{wt}(mG)=0]\le\tfrac34$ (3.13).

<a id="pdf-7251cb8e4bc5-p065-b003"></a>
<!-- pdf-source: page=65; block=3; confidence=0.90 -->
Three bounds on a random variable deviating from its expectation follow; the first holds for any random variable.

<a id="pdf-7251cb8e4bc5-p065-b004"></a>
<!-- pdf-source: page=65; block=4; confidence=0.96 -->
**Lemma 3.1.6 (Markov Bound).** For a non-negative random variable $V$ and any $t>0$, $\Pr[V\ge t]\le E[V]/t$. In particular, for any $a\ge1$, $\Pr[V\ge a\,E[V]]\le 1/a$.

<a id="pdf-7251cb8e4bc5-p065-b005"></a>
<!-- pdf-source: page=65; block=5; confidence=0.92 -->
**Proof.** The second bound follows from the first by substituting $t=a\,E[V]$; it remains to prove the first. $E[V]=\sum_{i\in[0,t)}i\Pr[V=i]+\sum_{i\ge t}i\Pr[V=i]$ (3.14) $\ge\sum_{i\ge t}i\Pr[V=i]$ (3.15) $\ge t\sum_{i\ge t}\Pr[V=i]$ (3.16) $=t\,\Pr[V\ge t]$ (3.17). (3.14) uses the definition of expectation and non-negativity of $V$; (3.15) drops non-negative terms; (3.16) uses $i\ge t$ in the summands; (3.17) is the definition of $\Pr[V\ge t]$. Rearranging (3.17) yields the claim.

<a id="pdf-7251cb8e4bc5-p065-b006"></a>
<!-- pdf-source: page=65; block=6; confidence=0.92 -->
The second bound is stated in terms of variance, defined next.

<a id="pdf-7251cb8e4bc5-p066-b001"></a>
<!-- pdf-source: page=66; block=1; confidence=0.90 -->
**Definition 3.1.7 (Variance).** For a random variable $V$, $\mathrm{Var}[V]=E\!\left[(V^2-E[V])^2\right]$. The standard deviation is $\sigma[V]=\sqrt{\mathrm{Var}[V]}$.

<a id="pdf-7251cb8e4bc5-p066-b002"></a>
<!-- pdf-source: page=66; block=2; confidence=0.96 -->
**Lemma 3.1.8 (Chebyschev Bound).** For a random variable $V$ with $\mathrm{Var}[V]\ne0$ and any $t>0$, $\Pr[\,|V-E[V]|\ge t\,]\le\mathrm{Var}[V]/t^2$.

<a id="pdf-7251cb8e4bc5-p066-b003"></a>
<!-- pdf-source: page=66; block=3; confidence=0.95 -->
**Proof.** $\Pr[\,|V-E[V]|\ge t\,]=\Pr[(V-E[V])^2\ge t^2]\le E[(V-E[V])^2]/t^2=\mathrm{Var}[V]/t^2$. The inequality is Markov's inequality (Lemma 3.1.6); the last equality is the definition of variance.

<a id="pdf-7251cb8e4bc5-p066-b004"></a>
<!-- pdf-source: page=66; block=4; confidence=0.92 -->
The third bound applies only to sums of independent random variables, defined next.

<a id="pdf-7251cb8e4bc5-p066-b005"></a>
<!-- pdf-source: page=66; block=5; confidence=0.96 -->
**Definition 3.1.9 (Independence).** Two random variables $A,B$ are independent if for every $a,b$ in the ranges of $A,B$ respectively, $\Pr[A=a\wedge B=b]=\Pr[A=a]\cdot\Pr[B=b]$.

<a id="pdf-7251cb8e4bc5-p066-b006"></a>
<!-- pdf-source: page=66; block=6; confidence=0.90 -->
Example: under the uniform distribution of Table 3.1, the bits $G_{0,0}$ and $G_{0,1}$ are independent; in fact all four bits of $G$ are mutually independent.

<a id="pdf-7251cb8e4bc5-p066-b007"></a>
<!-- pdf-source: page=66; block=7; confidence=0.96 -->
**Definition 3.1.10 (Conditional Probability).** For events $A,B$ over the same domain and distribution, $\Pr[A\mid B]=\dfrac{\Pr[A\text{ and }B]}{\Pr[B]}$.

<a id="pdf-7251cb8e4bc5-p067-b001"></a>
<!-- pdf-source: page=67; block=1; confidence=0.85 -->
**Example.** Computes a conditional probability: $\Pr[\mathbb{1}_{V_{01}=1} \mid G_{0,0}=0] = \frac{4/16}{1/2} = \frac{1}{2}$. Notes the definition implies two events $A,B$ are independent iff $\Pr[A]=\Pr[A\mid B]$.

<a id="pdf-7251cb8e4bc5-p067-b002"></a>
<!-- pdf-source: page=67; block=2; confidence=0.97 -->
**Lemma 3.1.11.** For any two events A, B on the same domain and probability distribution: Pr[A] = Pr[A|B]·Pr[B] + Pr[A|¬B]·Pr[¬B]. (Cf. Exercise 3.2.)

<a id="pdf-7251cb8e4bc5-p067-b003"></a>
<!-- pdf-source: page=67; block=3; confidence=0.97 -->
**Theorem 3.1.12 (Chernoff Bound).** Let X_1,…,X_m be independent binary random variables and X = ∑ X_i. Multiplicative bound: for 0 < ε ≤ 1, Pr[|X − E(X)| > εE(X)] < 2e^{−ε²E(X)/3}. Additive bound: Pr[|X − E(X)| > εm] < 2e^{−ε²m/2}. Proof omitted (standard).

<a id="pdf-7251cb8e4bc5-p067-b004"></a>
<!-- pdf-source: page=67; block=4; confidence=0.95 -->
**Lemma 3.1.13.** For any m ≥ 1, the distribution U_{D1×D2×···×Dm} is identical to U_{D1} × U_{D2} × ··· × U_{Dm}. Here the product distribution p1×p2 over D1×D2 picks (x,y) by drawing x∼p1 and y∼p2 independently; two distributions on D are identical if p1(x)=p2(x) for all x∈D. (Cf. Exercise 3.4.)

<a id="pdf-7251cb8e4bc5-p068-b001"></a>
<!-- pdf-source: page=68; block=1; confidence=0.97 -->
**Lemma 3.1.14.** Given a non-zero vector m ∈ F_q^k and a uniformly random k×n matrix G over F_q, the vector m·G is uniformly distributed over F_q^n.

<a id="pdf-7251cb8e4bc5-p068-b002"></a>
<!-- pdf-source: page=68; block=2; confidence=0.95 -->
**Proof.** Denote the (j,i) entry of G by g_{ji} (1≤j≤k, 1≤i≤n); by Lemma 3.1.13 each g_{ji} is an independent uniform element of F_q. Let b_i be the i-th entry of m·G. With m = (m_1,…,m_k), b_i = ∑_{j=1}^k m_j g_{ji}. Since b_i and b_j (i≠j) depend on disjoint entries of G, they are independent, so it suffices to show each b_i is uniform on F_q. As m ≠ 0, WLOG m_1 ≠ 0; write b_i = m_1 g_{1i} + ∑_{j=2}^k m_j g_{ji}. For each of the q^{k−1} fixed assignments to g_{2i},…,g_{ki}, b_i takes a distinct value for each of the q choices of g_{1i} (using m_1 ≠ 0). Thus over all assignments b_i attains each value in F_q exactly q^{k−1} times, proving uniformity. Generalizes the argument of Proposition 2.6.3.

<a id="pdf-7251cb8e4bc5-p068-b003"></a>
<!-- pdf-source: page=68; block=3; confidence=0.94 -->
**3.2 The Probabilistic Method.** To prove existence of a code C with property P, define a distribution D over all possible codes and show, for C∼D, Pr[C has property P] > 0, equivalently Pr[C doesn't have property P] < 1 — which establishes existence.

<a id="pdf-7251cb8e4bc5-p068-b004"></a>
<!-- pdf-source: page=68; block=4; confidence=0.95 -->
**Example (Question 3.0.1).** All [2,2]_2 linear codes are covered by the 2×2 matrices over F_2; take D = uniform over F_2^{2×2}. By Proposition 2.3.6 and (3.13), Pr_{U(F_2^{2×2})}[there is no [2,2,1]_2 code] ≤ 3/4 < 1, answering Question 3.0.1 affirmatively.

<a id="pdf-7251cb8e4bc5-p068-b005"></a>
<!-- pdf-source: page=68; block=5; confidence=0.92 -->
**General approach.** Define sub-properties P_1,…,P_m with P = P_1 ∧ P_2 ∧ ··· ∧ P_m.

<a id="pdf-7251cb8e4bc5-p069-b001"></a>
<!-- pdf-source: page=69; block=1; confidence=0.94 -->
Show for every 1 ≤ i ≤ m that Pr[C doesn't have property P_i] = Pr[¬P_i] < 1/m. By the union bound this yields Pr[C doesn't have property P] < 1, as desired (note ¬P = ¬P_1 ∨ ··· ∨ ¬P_m).

<a id="pdf-7251cb8e4bc5-p069-b002"></a>
<!-- pdf-source: page=69; block=2; confidence=0.90 -->
**Example.** For Question 3.0.1 set P_1 = ⊮_{V01≥1}, P_2 = ⊮_{V10≥1}, P_3 = ⊮_{V11≥1} (seeking a [2,2]_2 code satisfying P_1∧P_2∧P_3). By (3.2),(3.3),(3.4), for i ∈ [3]: Pr[C doesn't have P_i] = Pr[¬P_i] = 1/4 < 1/3.

<a id="pdf-7251cb8e4bc5-p069-b003"></a>
<!-- pdf-source: page=69; block=3; confidence=0.94 -->
**Special case (Exercise 3.5).** If P is the property f(C) ≤ b, then E[f(C)] ≤ b implies Pr[C has property P] > 0, hence there exists a code C with f(C) ≤ b.

<a id="pdf-7251cb8e4bc5-p069-b004"></a>
<!-- pdf-source: page=69; block=4; confidence=0.93 -->
**3.3 The q-ary Entropy Function.** Introduces the entropy function, central to analyzing limits of codes: it captures an upper bound on the rate as a function of relative distance (Section 4.1) and a lower bound via the probabilistic method (Section 4.2).

<a id="pdf-7251cb8e4bc5-p069-b005"></a>
<!-- pdf-source: page=69; block=5; confidence=0.97 -->
**Definition 3.3.1 (q-ary Entropy Function).** For integer q ≥ 2 and real 0 ≤ x ≤ 1: H_q(x) = x·log_q(q−1) − x·log_q(x) − (1−x)·log_q(1−x). For q = 2 the subscript is dropped: H(x) = −x·log x − (1−x)·log(1−x), where log x = log_2(x) (convention for the rest of the book).

<a id="pdf-7251cb8e4bc5-p069-b006"></a>
<!-- pdf-source: page=69; block=6; confidence=0.90 -->
H(x) is the Shannon entropy of the distribution on {0,1} choosing 1 w.p. x and 0 w.p. 1−x; there is no analogous interpretation for general H_q(x). Its central role stems from its close relation to the volume of a Hamming ball, made precise in the next subsection.

<a id="pdf-7251cb8e4bc5-p070-b001"></a>
<!-- pdf-source: page=70; block=1; confidence=0.95 -->
Figure 3.1: plot of $H_q(x)$ for $q=2,3,4$; maximum value $1$ attained at $x=1-1/q$.

<a id="pdf-7251cb8e4bc5-p070-b002"></a>
<!-- pdf-source: page=70; block=2; confidence=0.97 -->
**Section 3.3.1 — Volume of Hamming Balls.** Motivates needing upper/lower bounds on the volume of a Hamming ball.

<a id="pdf-7251cb8e4bc5-p070-b003"></a>
<!-- pdf-source: page=70; block=3; confidence=0.95 -->
**Definition 3.3.2 (Volume of a Hamming Ball).** For integers $q\ge 2$ and $n\ge r\ge 1$, the volume of a Hamming ball of radius $r$ is
$$\mathrm{Vol}_q(r,n)=|B_q(\mathbf{0},r)|=\sum_{i=0}^{r}\binom{n}{i}(q-1)^i.$$
The volume is independent of the ball's center, so the center $\mathbf 0$ is chosen without loss of generality.

<a id="pdf-7251cb8e4bc5-p070-b004"></a>
<!-- pdf-source: page=70; block=4; confidence=0.96 -->
**Proposition 3.3.3.** Let $q\ge 2$ be an integer and $0\le p\le 1-\tfrac1q$ real. Then:
(i) $\mathrm{Vol}_q(pn,n)\le q^{H_q(p)n}$; and
(ii) for large enough $n$, $\mathrm{Vol}_q(pn,n)\ge q^{H_q(p)n-o(n)}$.

<a id="pdf-7251cb8e4bc5-p071-b001"></a>
<!-- pdf-source: page=71; block=1; confidence=0.95 -->
**Proof (part (i)).** Start from $1=(p+(1-p))^n=\sum_{i=0}^{n}\binom{n}{i}p^i(1-p)^{n-i}$ (3.18, binomial expansion). Drop the tail $\sum_{i=pn+1}^{n}$ to get $\ge\sum_{i=0}^{pn}\binom{n}{i}p^i(1-p)^{n-i}$ (3.19). Rewrite $p^i=(q-1)^i\big(\tfrac{p}{q-1}\big)^i$ and, using $\tfrac{p}{(q-1)(1-p)}\le 1$ (since $p\le 1-1/q$), bound each term to obtain (3.20)–(3.21) $\ge\big(\tfrac{p}{q-1}\big)^{pn}(1-p)^{(1-p)n}\sum_{i=0}^{pn}\binom{n}{i}(q-1)^i$. Since $q^{-H_q(p)n}=\big(\tfrac{p}{q-1}\big)^{pn}(1-p)^{(1-p)n}$, this gives $1\ge \mathrm{Vol}_q(pn,n)\,q^{-H_q(p)n}$ (3.22), equivalently $\mathrm{Vol}_q(pn,n)\le q^{H_q(p)n}$, proving (i).

<a id="pdf-7251cb8e4bc5-p071-b002"></a>
<!-- pdf-source: page=71; block=2; confidence=0.90 -->
Part (ii) will use Stirling's approximation for $n!$ (Lemma A.1.2). Footnote: $\tfrac{p}{(q-1)(1-p)}\le 1$ holds iff $\tfrac{p}{1-p}\le q-1$, which holds if $p\le \tfrac{q-1}{q}$ (Lemma A.2.1).

<a id="pdf-7251cb8e4bc5-p072-b001"></a>
<!-- pdf-source: page=72; block=1; confidence=0.85 -->
**Proof (part (ii), cont.).** By Stirling (Lemma A.1.2),
$$\binom{n}{pn}=\frac{n!}{(pn)!((1-p)n)!}>\frac{(n/e)^n}{(pn/e)^{pn}((1-p)n/e)^{(1-p)n}}\cdot\frac{e^{\lambda_1(n)-\lambda_2(pn)-\lambda_2((1-p)n)}}{\sqrt{2\pi p(1-p)n}}=\frac{1}{p^{pn}(1-p)^{(1-p)n}}\cdot\ell(n),$$
where $\ell(n)=\dfrac{e^{\lambda_1(n)-\lambda_2(pn)-\lambda_2((1-p)n)}}{\sqrt{2\pi p(1-p)n}}$. (Eq. 3.23)

<a id="pdf-7251cb8e4bc5-p072-b002"></a>
<!-- pdf-source: page=72; block=2; confidence=0.87 -->
Then $\mathrm{Vol}_q(pn,n)\ge\binom{n}{pn}(q-1)^{pn}$ (3.24, keeping only the last term of the defining sum) $>\dfrac{(q-1)^{pn}}{p^{pn}(1-p)^{(1-p)n}}\ell(n)$ (3.25, from 3.23) $\ge q^{H_q(p)n-o(n)}$ (3.26, by definition of $H_q(\cdot)$ and $\ell(n)=q^{-o(n)}$ for large $n$). This proves (ii). $\qquad\blacksquare$

<a id="pdf-7251cb8e4bc5-p072-b003"></a>
<!-- pdf-source: page=72; block=3; confidence=0.95 -->
**Section 3.3.2 — Other Properties of the $q$-ary Entropy function.** Examines behavior of $H_q$ over parameter ranges; uses asymptotic analysis (Appendix reference). Begins with large-$q$ behavior.

<a id="pdf-7251cb8e4bc5-p072-b004"></a>
<!-- pdf-source: page=72; block=4; confidence=0.96 -->
**Proposition 3.3.4.** For small enough $\varepsilon$, $1-H_q(\rho)\ge 1-\rho-\varepsilon$ for every $0<\rho\le 1-1/q$ if and only if $q$ is $2^{\Omega(1/\varepsilon)}$.

<a id="pdf-7251cb8e4bc5-p072-b005"></a>
<!-- pdf-source: page=72; block=5; confidence=0.90 -->
**Proof.** By definition of $H_q$ and binary $H$,
$$H_q(\rho)=\rho\log_q(q-1)-\rho\log_q\rho-(1-\rho)\log_q(1-\rho)=\rho\log_q(q-1)+H(\rho)/\log_2 q.$$
If $q\ge 2^{1/\varepsilon}$ then $H_q(\rho)\le\rho+\varepsilon$, since $\log_q(q-1)\le 1$ and $H(\rho)\le 1$. Hence for $q\ge 2^{1/\varepsilon}$, $1-H_q(\rho)\ge 1-\rho-\varepsilon$. (Proof continues beyond the supplied pages.)

<a id="pdf-7251cb8e4bc5-p073-b001"></a>
<!-- pdf-source: page=73; block=1; confidence=0.90 -->
**Proof (continued).** Case q = 2^{o(1/ε)}.

Claim: for small enough ε, if q ≥ 1/ε² then log_q(q−1) ≥ 1−ε. Reason: log_q(q−1) = 1 + (1/ln q)·ln(1−1/q) = 1 − O(1/(q ln q)) (using ln(1−x) = −O(x), Lemma A.2.2), which is ≥ 1−ε when q ≥ 1/ε².

If q = 2^{o(1/ε)} then for fixed ρ, H(ρ)/log q = ε·ω(1). Hence for q = 2^{o(1/ε)} with q ≥ 1/ε²:

ρ·log_q(q−1) + H(ρ)/log q ≥ ρ − ε + ε·ω(1) > ρ + ε,

which implies 1 − H_q(ρ) < 1 − ρ − ε. For q ≤ 1/ε², Lemma 3.3.5 gives 1 − H_q(ρ) ≤ 1 − H_{1/ε²}(ρ) < 1 − ρ − ε.

<a id="pdf-7251cb8e4bc5-p073-b002"></a>
<!-- pdf-source: page=73; block=2; confidence=0.95 -->
**Lemma 3.3.5.** Let q ≥ 2 be an integer and 0 ≤ ρ ≤ 1 − 1/q. For any real m ≥ 1 such that

q^{m−1} ≥ (1 + 1/(q−1))^{q−1}  (3.27),

we have H_q(ρ) ≥ H_{q^m}(ρ).

<a id="pdf-7251cb8e4bc5-p073-b003"></a>
<!-- pdf-source: page=73; block=3; confidence=0.90 -->
**Proof.** Since H_q(0) = H_{q^m}(0) = 0, assume ρ ∈ (0, 1−1/q]. Using H_q(ρ) = ρ·log(q−1)/log q + H(ρ)·(1/log q) (from the proof of Proposition 3.3.4):

H_q(ρ) − H_{q^m}(ρ) = ρ·(log(q−1)/log q − log(q^m−1)/(m log q)) + H(ρ)·(1/log q − 1/(m log q)).

This implies (1/ρ)·m log q·(H_q(ρ) − H_{q^m}(ρ)) = log((q−1)^m) − log(q^m−1) + (H(ρ)/ρ)·(m−1).

<a id="pdf-7251cb8e4bc5-p074-b001"></a>
<!-- pdf-source: page=74; block=1; confidence=0.95 -->
**Proof (continued, Lemma 3.3.5).** Since H(ρ)/ρ is decreasing in ρ (footnote 7) and ρ ≤ 1−1/q, the previous expression is

≥ log((q−1)^m) − log(q^m−1) + (H(1−1/q)/(1−1/q))·(m−1)  (3.28),

where H(1−1/q)/(1−1/q) = log(q/(q−1)) + (log q)/(q−1). Combining yields

= log( (q−1)·q^{(m−1)/(q−1)} · q^{m−1} / (q^m−1) ) ≥ 0  (3.29).

Step (3.29) uses the claim (q−1)·q^{(m−1)/(q−1)} ≥ q, which follows from (3.27). This completes the proof.

<a id="pdf-7251cb8e4bc5-p074-b002"></a>
<!-- pdf-source: page=74; block=2; confidence=0.90 -->
Since (1+1/x)^x ≤ e (Lemma A.2.5), (3.27) is satisfied for m ≥ 1 + 1/ln q, and is satisfied for every m ≥ 2 when q ≥ 3 (cf. Exercise 3.6), motivating Corollary 3.3.6.

<a id="pdf-7251cb8e4bc5-p074-b003"></a>
<!-- pdf-source: page=74; block=3; confidence=0.95 -->
**Corollary 3.3.6.** Let q ≥ 3 be an integer and 0 ≤ ρ ≤ 1 − 1/q. Then for any m ≥ 2, H_q(ρ) ≥ H_{q^m}(ρ).

<a id="pdf-7251cb8e4bc5-p074-b004"></a>
<!-- pdf-source: page=74; block=4; confidence=0.95 -->
**Proposition 3.3.7.** For small enough ε > 0, H_q(1 − 1/q − ε) ≤ 1 − c_q·ε², where c_q is a constant depending only on q.

<a id="pdf-7251cb8e4bc5-p074-b005"></a>
<!-- pdf-source: page=74; block=5; confidence=0.88 -->
**Proof.** Intuition: the derivative of H_q(x) is zero at x = 1 − 1/q, so the linear (ε) term vanishes in the Taylor expansion of H_q(1 − 1/q − ε). (Footnote 7: H(ρ)/ρ = log(1/ρ) − (1/ρ − 1)·log(1−ρ) is decreasing in ρ.)

<a id="pdf-7251cb8e4bc5-p075-b001"></a>
<!-- pdf-source: page=75; block=1; confidence=0.95 -->
**Proof (continued, Prop. 3.3.7).** Take q fixed and ε < 1/q. Expanding

H_q(1 − 1/q − ε) = −(1 − 1/q − ε)·log_q((1 − 1/q − ε)/(q−1)) − (1/q + ε)·log_q(1/q + ε)

via ln(1+x) = x − x²/2 + x³/3 − … (Lemma A.2.2), the linear-in-ε terms cancel; collecting ε³ and smaller terms into o(ε²) gives (steps (3.30)–(3.31)):

H_q(1 − 1/q − ε) = 1 − ε²q²/(2 ln q·(q−1)) + o(ε²) ≤ 1 − ε²q²/(4 ln q·(q−1))  (3.32),

for ε small enough. Hence one may take c_q = q²/(4 ln q·(q−1)).

<a id="pdf-7251cb8e4bc5-p075-b002"></a>
<!-- pdf-source: page=75; block=2; confidence=0.95 -->
**Proposition 3.3.8.** For small enough ε > 0, H_q(ε) = Θ( (1/log q)·ε·log(1/ε) ).

<a id="pdf-7251cb8e4bc5-p075-b003"></a>
<!-- pdf-source: page=75; block=3; confidence=0.90 -->
**Proof.** By definition,

H_q(ε) = ε·log_q(q−1) + ε·log_q(1/ε) + (1−ε)·log_q(1/(1−ε)).

Since all terms on the RHS are positive, H_q(ε) ≥ ε·log(1/ε)/log q  (3.33). (Proof continues beyond the supplied pages.)

<a id="pdf-7251cb8e4bc5-p076-b001"></a>
<!-- pdf-source: page=76; block=1; confidence=0.95 -->
**Proof (cont.).** By Lemma A.2.2, $(1-\varepsilon)\log_q(1/(1-\varepsilon)) \le 2\varepsilon/\ln q$ for small enough $\varepsilon$. Hence
$$H_q(\varepsilon) \le \frac{2+\ln(q-1)}{\ln q}\cdot\varepsilon + \frac{1}{\ln q}\cdot\varepsilon\ln\frac{1}{\varepsilon}. \tag{3.34}$$
Equations (3.33) and (3.34) together give the claimed bound.

<a id="pdf-7251cb8e4bc5-p076-b002"></a>
<!-- pdf-source: page=76; block=2; confidence=0.95 -->
**Definition.** On $[0,1-1/q]$, $H_q(\cdot)$ is a bijection onto $[0,1]$. Define $H_q^{-1}(y)=x$ to be the value $x$ with $H_q(x)=y$ and $0\le x\le 1-1/q$.

<a id="pdf-7251cb8e4bc5-p076-b003"></a>
<!-- pdf-source: page=76; block=3; confidence=0.96 -->
**Lemma 3.3.9.** For every $0<y\le 1-1/q$ and every small enough $\varepsilon>0$,
$$H_q^{-1}(y-\varepsilon^2/c'_q)\ \ge\ H_q^{-1}(y)-\varepsilon,$$
where $c'_q\ge 1$ is a constant depending only on $q$.

<a id="pdf-7251cb8e4bc5-p076-b004"></a>
<!-- pdf-source: page=76; block=4; confidence=0.85 -->
**Proof.** $H_q^{-1}(y)$ is strictly increasing and convex on $[0,1]$, so its derivative increases with $y$; in particular $(H_q^{-1})'(1)\ge (H_q^{-1})'(y)$ for all $0\le y\le 1$. Thus for every $0<y\le 1$ and small enough $\delta>0$,
$$\frac{H_q^{-1}(y)-H_q^{-1}(y-\delta)}{\delta}\ \le\ \frac{H_q^{-1}(1)-H_q^{-1}(1-\delta)}{\delta}.$$
Applying Proposition 3.3.7 together with $H_q^{-1}(1)=1-1/q$ and monotonicity of $H_q^{-1}$, and choosing $c'_q=\max(1,1/c_q)$ and $\delta=\varepsilon^2/c'_q$, completes the proof.

<a id="pdf-7251cb8e4bc5-p076-b005"></a>
<!-- pdf-source: page=76; block=5; confidence=0.99 -->
**3.4 Exercises**

<a id="pdf-7251cb8e4bc5-p076-b006"></a>
<!-- pdf-source: page=76; block=6; confidence=0.99 -->
**Exercise 3.1.** Prove Lemma 3.1.3.

<a id="pdf-7251cb8e4bc5-p076-b007"></a>
<!-- pdf-source: page=76; block=7; confidence=0.99 -->
**Exercise 3.2.** Prove Lemma 3.1.11.

<a id="pdf-7251cb8e4bc5-p076-b008"></a>
<!-- pdf-source: page=76; block=8; confidence=0.92 -->
**Exercise 3.3.** An unknown $x\in F$ is accessible via a randomized algorithm $A$ that on random input $r\in\{0,1\}^m$ outputs an estimate $A(r)$ with $\Pr_r[A(r)=x]\ge \tfrac12+\gamma$ for some $0<\gamma<\tfrac12$. Show that for any $t\ge 1$, using $O(t/\gamma^2)$ calls to $A$ one can determine $x$ with probability $\ge 1-e^{-t}$. Hint: call $A$ on independent random bits, take the majority answer, and apply the Chernoff bound (Theorem 3.1.12).

<a id="pdf-7251cb8e4bc5-p076-b009"></a>
<!-- pdf-source: page=76; block=9; confidence=0.99 -->
**Exercise 3.4.** Prove Lemma 3.1.13.

<a id="pdf-7251cb8e4bc5-p077-b001"></a>
<!-- pdf-source: page=77; block=1; confidence=0.95 -->
**Exercise 3.5.** Let $P$ be the property that a randomly chosen $C$ satisfies $f(C)\le b$. Show that $\mathbb{E}[f(C)]\le b$ implies $\Pr[C\text{ has property }P]>0$.

<a id="pdf-7251cb8e4bc5-p077-b002"></a>
<!-- pdf-source: page=77; block=2; confidence=0.97 -->
**Exercise 3.6.** Prove that for any $Q\ge q\ge 2$ and $\rho\le 1-1/q$, $H_Q(\rho)\le H_q(\rho)$.

<a id="pdf-7251cb8e4bc5-p077-b003"></a>
<!-- pdf-source: page=77; block=3; confidence=0.92 -->
**Exercise 3.7.** Prove that for $p<\tfrac12$, $H_2(p)\le O(p\log p)$.

<a id="pdf-7251cb8e4bc5-p077-b004"></a>
<!-- pdf-source: page=77; block=4; confidence=0.90 -->
**3.5 Bibliographic Notes.** Attributes the Chernoff bounds to Chernoff [14] (credited by him to Rubin [4]), noting their ubiquity in information theory/CS [15,54,53] and concentration-bound proofs in [17]; traces the probabilistic method to early-1940s work, Erdős [24], and Shannon [65], citing Alon–Spencer [2]; and attributes the entropy function to Shannon [65], with the two-parameter $H_q(p)$ a specialization of his more general definition.

<a id="pdf-7251cb8e4bc5-p079-b001"></a>
<!-- pdf-source: page=79; block=1; confidence=0.97 -->
# Part II — The Combinatorics

<a id="pdf-7251cb8e4bc5-p081-b001"></a>
<!-- pdf-source: page=81; block=1; confidence=0.97 -->
# Chapter 4. What Can and Cannot Be Done-I

<a id="pdf-7251cb8e4bc5-p081-b002"></a>
<!-- pdf-source: page=81; block=2; confidence=0.95 -->
Addresses the rate–distance trade-off (Question 1.8.2): for fixed relative distance δ, find the best achievable rate R. Upper bounds on R are negative results (non-existence); lower bounds are positive results. Chapter covers one positive result — the Gilbert–Varshamov bound (§4.2) — and upper bounds: asymptotic Hamming bound (§4.1), Singleton bound (§4.3, tight for large alphabets but not binary), and Plotkin bound (§4.4, stronger than Singleton for binary codes).

<a id="pdf-7251cb8e4bc5-p081-b003"></a>
<!-- pdf-source: page=81; block=3; confidence=0.97 -->
## 4.1 Asymptotic Version of the Hamming Bound

<a id="pdf-7251cb8e4bc5-p081-b004"></a>
<!-- pdf-source: page=81; block=4; confidence=0.94 -->
Converts the earlier Hamming bound (§1.7, stated as an upper bound on dimension k in terms of n, q, d) into a relation between rate R and relative distance δ. For any $(n,k,d)_q$ code with $R=k/n$ and $\delta=d/n$, Theorem 1.7.2 implies:

$$R = \frac{k}{n} \le 1 - \frac{\log_q \mathrm{Vol}_q\!\left(\left\lfloor \frac{d-1}{2} \right\rfloor,\, n\right)}{n}$$

<a id="pdf-7251cb8e4bc5-p082-b001"></a>
<!-- pdf-source: page=82; block=1; confidence=0.90 -->
Recalls Proposition 3.3.3: the Hamming-ball volume satisfies $V_q(\lfloor (d-1)/2 \rfloor, n) \ge q^{H_q(\delta/2)\,n - o(n)}$. Taking $\log_q$ of both sides and dividing by $n$ lower-bounds the corresponding term by $H_q(\delta/2) - o(1)$ (with $o(1)\to 0$ as $n\to\infty$). Applying Theorem 1.7.2, any $q$-ary code $C$ of rate $R$, relative distance $\delta$, block length $n$ satisfies
$$R \le 1 - H_q\!\left(\tfrac{\delta}{2}\right) + o(1). \tag{4.1}$$

<a id="pdf-7251cb8e4bc5-p082-b002"></a>
<!-- pdf-source: page=82; block=2; confidence=0.98 -->
**Proposition 4.1.1 (Asymptotic Hamming Bound).** For an infinite family $C$ of $q$-ary codes with rate $R = R(C)$ and relative distance $\delta = \delta(C)$, taking $n\to\infty$ in (4.1) gives
$$R \le 1 - H_q\!\left(\tfrac{\delta}{2}\right).$$

<a id="pdf-7251cb8e4bc5-p082-b003"></a>
<!-- pdf-source: page=82; block=3; confidence=0.95 -->
**Section 4.2 (Gilbert–Varshamov Bound).** Introduces the first non-trivial lower bound on $R$ in terms of $\delta$ (the only positive result on the $R$ vs $\delta$ tradeoff in the book).

<a id="pdf-7251cb8e4bc5-p082-b004"></a>
<!-- pdf-source: page=82; block=4; confidence=0.97 -->
**Theorem 4.2.1 (Gilbert–Varshamov Bound).** Let $q \ge 2$. For every $0 \le \delta < 1 - \tfrac{1}{q}$ there exists a family of $q$-ary codes $C$ with rate $R(C) \ge 1 - H_q(\delta)$ and relative distance $\delta(C) \ge \delta$. If $q$ is a prime power, such a family of *linear* codes exists. Furthermore, for every $0 \le \varepsilon \le 1 - H_q(\delta)$ and integer $n$, if a matrix $G$ is chosen uniformly from $\mathbb{F}_q^{k\times n}$ with $k = n(1 - H_q(\delta) - \varepsilon)$, then $G$ generates a code of rate $1 - H_q(\delta) - \varepsilon$ and relative distance at least $\delta$ with probability strictly greater than $1 - q^{-\varepsilon n}$.

<a id="pdf-7251cb8e4bc5-p082-b005"></a>
<!-- pdf-source: page=82; block=5; confidence=0.90 -->
The bound is called the GV bound. Proofs for general and linear codes appear in Sections 4.2.1 and 4.2.2. First a non-linear code of rate $1 - H_q(\delta)$ and relative distance $\ge \delta$ is shown to exist; then a linear code (with high probability when $\varepsilon > 0$), the linear existence following from the final part with $\varepsilon = 0$.

<a id="pdf-7251cb8e4bc5-p083-b001"></a>
<!-- pdf-source: page=83; block=1; confidence=0.90 -->
Figure 4.1 depicts the Hamming and GV bounds for binary codes: points below the GV bound are achievable, points above the Hamming bound are not. Goal: push the GV bound up and the Hamming bound down.

<a id="pdf-7251cb8e4bc5-p083-b002"></a>
<!-- pdf-source: page=83; block=2; confidence=0.92 -->
**Section 4.2.1 (Greedy Construction).** Proves Theorem 4.2.1 for general codes via a greedy construction: fix $n$, set $d = \delta n$, start with empty $C \subseteq [q]^n$, and repeatedly add strings at Hamming distance $\ge d$ from all existing codewords.

<a id="pdf-7251cb8e4bc5-p083-b003"></a>
<!-- pdf-source: page=83; block=3; confidence=0.95 -->
**Algorithm 4.2.1 (Gilbert's Greedy Code Construction).** Input: $n, q, d$. Output: a code $C \subseteq [q]^n$ of distance $d \ge 1$.
1. $C \leftarrow \emptyset$
2. **while** there exists $v \in [q]^n$ with $\Delta(v, c) \ge d$ for every $c \in C$ **do**
3.  add $v$ to $C$
4. **return** $C$

<a id="pdf-7251cb8e4bc5-p083-b004"></a>
<!-- pdf-source: page=83; block=4; confidence=0.90 -->
**Proof (correctness).** The output has distance $d$: Step 2 guarantees Step 3 never adds a vector reducing $C$'s distance below $d$. Termination: once a vector $v$ cannot be added (some $c$ has $\Delta(c,v) < d$), it can never be added later, since vectors are only added to $C$, so $\Delta(v,c) < d$ persists in all future iterations. (Continued on next page.)

<a id="pdf-7251cb8e4bc5-p084-b001"></a>
<!-- pdf-source: page=84; block=1; confidence=0.92 -->
Figure 4.2 illustrates the first five iterations of Gilbert's greedy algorithm.

<a id="pdf-7251cb8e4bc5-p084-b002"></a>
<!-- pdf-source: page=84; block=2; confidence=0.90 -->
**Proof step (running time).** The running time is $q^{O(n)}$. Step 2 may repeat for every vector in $[q]^n$ (at most $q^n$ times); a naive implementation cycles through all $v \in [q]^n$ and, for each, checks all $\le q^n$ codewords $c \in C$ for $\Delta(c,v) < d$, adding $v$ if none exists. Improvement: since a rejected $v$ stays rejected, fix an ordering of $[q]^n$ and test each $v$ once, giving time $O(nq^{2n})$, still $q^{O(n)}$.

<a id="pdf-7251cb8e4bc5-p084-b003"></a>
<!-- pdf-source: page=84; block=3; confidence=0.93 -->
**Proof step (covering).** After termination, $\bigcup_{c \in C} B(c, d-1) = [q]^n$: otherwise some $v \in [q]^n \setminus C$ has $\Delta(v,c) \ge d$ for all $c$ and could be added, contradicting termination. Hence
$$\left| \bigcup_{c \in C} B(c, d-1) \right| = q^n. \tag{4.2}$$

<a id="pdf-7251cb8e4bc5-p085-b001"></a>
<!-- pdf-source: page=85; block=1; confidence=0.95 -->
**Proof (continued).** Since $\sum_{c\in C}|B(c,d-1)|\ge\big|\bigcup_{c\in C}B(c,d-1)\big|$, equation (4.2) gives $\sum_{c\in C}|B(c,d-1)|\ge q^n$. By translation invariance of Hamming-ball volume, $\sum_{c\in C}\mathrm{Vol}_q(d-1,n)\ge q^n$. As $\sum_{c\in C}\mathrm{Vol}_q(d-1,n)=\mathrm{Vol}_q(d-1,n)\cdot|C|$, we get
$$|C|\ge \frac{q^n}{\mathrm{Vol}_q(d-1,n)}\ge \frac{q^n}{q^{nH_q(\delta)}}=q^{n(1-H_q(\delta))}.$$
Here the bound $\mathrm{Vol}_q(d-1,n)\le \mathrm{Vol}_q(\delta n,n)$ (4.3) $\le q^{nH_q(\delta)}$ (4.4) is used, the second inequality by the Hamming-ball volume upper bound (Proposition 3.3.3). Hence for every $q,n,\delta$ there is a code of rate $\ge 1-H_q(\delta)$.

<a id="pdf-7251cb8e4bc5-p085-b002"></a>
<!-- pdf-source: page=85; block=2; confidence=0.98 -->
**Lemma 4.2.2.** For every pair of positive integers $n,q$ and real $\delta\in[0,1]$ there exists an $(n,k,\delta n)_q$ code with $q^k\ge \dfrac{q^n}{\mathrm{Vol}_q(d-1,n)}$. In particular, for every positive integer $q$ and real $\delta\in[0,1-1/q]$ there is an infinite family of $q$-ary codes of rate $R$ and relative distance $\delta$ with $R\ge 1-H_q(\delta)$.

<a id="pdf-7251cb8e4bc5-p085-b003"></a>
<!-- pdf-source: page=85; block=3; confidence=0.95 -->
The greedy code (Algorithm 4.2.1) need not have special structure; even storing it may take exponential space, whereas linear codes have a succinct representation (Proposition 2.3.3).

**Question 4.2.3.** Do linear codes achieve the $R\ge 1-H_q(\delta)$ tradeoff of the greedy construction? (Answered affirmatively next.)

<a id="pdf-7251cb8e4bc5-p086-b001"></a>
<!-- pdf-source: page=86; block=1; confidence=0.97 -->
**4.2.2 Linear Code Construction** — a random linear code lies on the GV bound with high probability, via the probabilistic method (Section 3.2).

<a id="pdf-7251cb8e4bc5-p086-b002"></a>
<!-- pdf-source: page=86; block=2; confidence=0.94 -->
**Proof of Theorem 4.2.1.** By Proposition 2.3.6 it suffices to exhibit a full-rank $k\times n$ matrix $G$ (with $k=(1-H_q(\delta)-\varepsilon)n$) such that $\mathrm{wt}(mG)\ge d$ for every $m\in\mathbb{F}_q^k\setminus\{0\}$. Pick $G$ with its $kn$ entries chosen independently and uniformly from $\mathbb{F}_q$. Fix nonzero $m$; by Lemma 3.1.14, $mG$ is uniform in $\mathbb{F}_q^n$. Then
$$\Pr_G[\mathrm{wt}(mG)<d]=\frac{\mathrm{Vol}_q(d-1,n)}{q^n}\ (4.5)\ \le \frac{q^{nH_q(\delta)}}{q^n}\le q^{-k}\cdot q^{-\varepsilon n}\ (4.6),$$
where (4.5) uses that $\mathrm{wt}(mG)<d \iff mG\in B(0,d-1)$ with $mG$ uniform, the middle step uses (4.4), and (4.6) uses $k\le n(1-H_q(\delta)-\varepsilon)$. Applying the union bound (Lemma 3.1.5) over the $q^k-1$ nonzero $m$:
$$\Pr_G[\exists\, m\neq 0:\ \mathrm{wt}(mG)<d]\le (q^k-1)q^{-k}q^{-\varepsilon n}<q^{-\varepsilon n}.$$
Thus a random $G$ has $\mathrm{wt}(mG)\ge d$ for all nonzero $m$ with probability $>1-q^{-\varepsilon n}$, so by Proposition 2.3.6 the generated code has distance $\ge d$. For full rank: $G$ not full rank iff some nonzero $m$ has $mG=0$, giving $\mathrm{wt}(mG)=0<d$, a contradiction. Hence $G$ generates an $[n,k,d]_q$ code of rate $k/n=1-H_q(\delta)-\varepsilon$ and relative distance $\delta$.

<a id="pdf-7251cb8e4bc5-p087-b001"></a>
<!-- pdf-source: page=87; block=1; confidence=0.94 -->
The probabilistic-method proof gives a high-probability (not merely existence) result, and, as in Lemma 4.2.2, a non-asymptotic bound for every $n,k$ in the linear case too. A random linear code can alternatively be chosen via a random $(n-k)\times n$ parity-check matrix, yielding an alternate GV proof (Exercise 4.2). Theorem 4.2.1 requires $\delta<1-\tfrac1q$ only because the volume bound $\mathrm{Vol}_q(\delta n,n)\le q^{H_q(\delta)n}$ (Proposition 3.3.3) needs it.

**Question 4.2.4.** Does there exist a code with $R>0$ and $\delta>1-\tfrac1q$? (Revisited in Section 4.4.)

<a id="pdf-7251cb8e4bc5-p087-b002"></a>
<!-- pdf-source: page=87; block=2; confidence=0.97 -->
**4.3 Singleton Bound** — an upper bound on $R$ for fixed $\delta$.

<a id="pdf-7251cb8e4bc5-p087-b003"></a>
<!-- pdf-source: page=87; block=3; confidence=0.98 -->
**Theorem 4.3.1 (Singleton Bound).** For every $(n,k,d)_q$ code, $k\le n-d+1$. Consequently, if $\mathcal{C}$ is an infinite family of codes of rate $R$ and relative distance $\delta$, then $R\le 1-\delta$. The asymptotic bound holds for any family, even with alphabet growing with the code length.

<a id="pdf-7251cb8e4bc5-p087-b004"></a>
<!-- pdf-source: page=87; block=4; confidence=0.95 -->
**Proof.** (Non-asymptotic bound; asymptotic version shown at the end.) Let $c_1,\dots,c_M$ be the codewords of an $(n,k,d)_q$ code $C$; it suffices to show $M\le q^{n-d+1}$. For each $i\in[M]$ let $c'_i$ be the length-$(n-d+1)$ prefix of $c_i$ (Figure 4.3). Claim: for $i\neq j$, $c'_i\neq c'_j$. Otherwise $c'_i=c'_j$ means $c_i,c_j$ agree in the first $n-d+1$ positions, so $\Delta(c_i,c_j)\le d-1$, contradicting distance $d$. Hence $M$ equals the number of distinct length-$(n-d+1)$ prefixes, so $M\le q^{n-d+1}$.

<a id="pdf-7251cb8e4bc5-p088-b001"></a>
<!-- pdf-source: page=88; block=1; confidence=0.95 -->
*Figure 4.3.* Depicts the construction of a new code used in the proof of the Singleton bound.

<a id="pdf-7251cb8e4bc5-p088-b002"></a>
<!-- pdf-source: page=88; block=2; confidence=0.95 -->
**Proof (asymptotic Singleton bound).** Suppose an infinite family $C$ has rate $R = R(C) = 1 - \delta + \varepsilon$ for some $\varepsilon > 0$. Then there exist $n > 2/\varepsilon$ and a code $C_n \in C$ that is an $(n,k,d)_q$ code with $k \ge n(1-\delta+\varepsilon)$ and $d \ge \delta n$. The choice of $n$ gives $k \ge n - d + 2$, contradicting the non-asymptotic Singleton bound.

<a id="pdf-7251cb8e4bc5-p088-b003"></a>
<!-- pdf-source: page=88; block=3; confidence=0.93 -->
The Singleton bound is independent of alphabet size; it is worse than the Hamming bound for binary codes but better for larger alphabets. Reed–Solomon codes (Chapter 5) meet it, but their alphabet size grows with block length $n$.

<a id="pdf-7251cb8e4bc5-p088-b004"></a>
<!-- pdf-source: page=88; block=4; confidence=0.97 -->
**Question 4.3.2.** For a fixed $q \ge 2$, does there exist a $q$-ary code that meets the Singleton bound?

<a id="pdf-7251cb8e4bc5-p088-b005"></a>
<!-- pdf-source: page=88; block=5; confidence=0.96 -->
**4.4 Plotkin Bound.** Introduces the Plotkin bound, which answers Questions 4.2.4 and 4.3.2.

<a id="pdf-7251cb8e4bc5-p089-b001"></a>
<!-- pdf-source: page=89; block=1; confidence=0.95 -->
*Figure 4.4.* Plots the Hamming, GV, and Singleton bounds ($R$ vs. $\delta$) for binary codes.

<a id="pdf-7251cb8e4bc5-p089-b002"></a>
<!-- pdf-source: page=89; block=2; confidence=0.96 -->
**Theorem 4.4.1 (Plotkin bound).** For any code $C \subseteq [q]^n$ with distance at least $d$:
1. If $d = \left(1 - \tfrac{1}{q}\right)n$, then $|C| \le 2qn$.
2. If $d > \left(1 - \tfrac{1}{q}\right)n$, then $|C| \le \dfrac{qd}{qd - (q-1)n}$.

<a id="pdf-7251cb8e4bc5-p089-b003"></a>
<!-- pdf-source: page=89; block=3; confidence=0.93 -->
The bound implies any code with relative distance $\delta \ge 1 - \tfrac{1}{q}$ has $R = 0$, answering Question 4.2.4 negatively. The part-1 bound can be improved to $2(q-1)n$ for $q \ge 2$ (Exercise 4.13), is tight for $q=2$ (Exercise 4.14), and gives a trade-off only for relative distance $> 1 - 1/q$; Corollary 4.4.2 extends it to $0 \le \delta \le 1 - 1/q$.

<a id="pdf-7251cb8e4bc5-p089-b004"></a>
<!-- pdf-source: page=89; block=4; confidence=0.96 -->
**Corollary 4.4.2.** Let $C$ be an infinite family of $q$-ary codes with relative distance $0 \le \delta \le 1 - \tfrac{1}{q}$ and rate $R$. Then $R \le 1 - \left(\dfrac{q}{q-1}\right)\delta.$

<a id="pdf-7251cb8e4bc5-p089-b005"></a>
<!-- pdf-source: page=89; block=5; confidence=0.90 -->
**Proof.** Assume for contradiction $C$ is an infinite family of $q$-ary codes with rate $R = 1 - \left(\tfrac{q}{q-1}\right)\delta + \varepsilon$ for some $\varepsilon > 0$. Take $C \in C$ of block length $n \ge \tfrac{3}{\varepsilon}\log\!\left(\tfrac{1}{\varepsilon}\right)$ (continued on next page).

<a id="pdf-7251cb8e4bc5-p090-b001"></a>
<!-- pdf-source: page=90; block=1; confidence=0.95 -->
**Proof (continued).** The chosen $C$ has distance $d \le \delta n$ and message length $k \ge Rn$; a shortening of $C$ will contradict Theorem 4.4.1.

Partition the codewords of $C$ so that codewords in a partition agree on the first $n - n'$ symbols, where $n' = \left\lfloor \tfrac{qd}{q-1}\right\rfloor - 1$. For each $x \in [q]^{n-n'}$ define the prefix code $C_x = \{(c_{n-n'+1},\dots,c_n) \mid (c_1\dots c_n) \in C,\ (c_1\dots c_{n-n'}) = x\}$, i.e. the $n'$-length suffixes of codewords beginning with $x$.

Each $C_x$ is a $q$-ary code of block length $n' = \left\lfloor \tfrac{qd}{q-1}\right\rfloor - 1$ and has distance at least $d$: if $c_1 \ne c_2 \in C_x$ had $\Delta(c_1,c_2) < d$, then $(x,c_1)$ and $(x,c_2)$ would be codewords of $C$ at distance $< d$, contradicting $\Delta(C) \ge d$.

Since $n' < \tfrac{q}{q-1}d$, we have $d > \left(1 - \tfrac{1}{q}\right)n'$, so part 2 of Theorem 4.4.1 applies to $C_x$:
$$|C_x| \le \frac{qd}{qd - (q-1)n'} \le qd \le qn, \qquad (4.7)$$
where the second inequality holds because $qd - (q-1)n'$ is a positive integer and the third because $d \le n$.

Summing over $x$, $|C| = \sum_{x \in [q]^{n-n'}} |C_x|$, and by (4.7),
$$|C| \le \sum_{x \in [q]^{n-n'}} qn = q^{\,n - n' + 1 + \frac{\log n}{\log q}} \le q^{\,n - \frac{q}{q-1}d + 1 + \log n} \le q^{\,n\left(1 - \delta\cdot\frac{q}{q-1} + \varepsilon\right)},$$
using the definition of $n'$ and $n \ge \tfrac{3}{\varepsilon}\log\!\left(\tfrac{1}{\varepsilon}\right)$. Hence $R \le 1 - \left(\tfrac{q}{q-1}\right)\delta + \varepsilon$; since this holds for every $\varepsilon > 0$, the corollary follows. $\square$

<a id="pdf-7251cb8e4bc5-p090-b002"></a>
<!-- pdf-source: page=90; block=2; confidence=0.92 -->
Corollary 4.4.2 implies that any $q$-ary code (with $q$ constant in the block length) of rate $R$ and relative distance $\delta$ satisfies $R < 1 - \delta$, answering Question 4.3.2 negatively. Recaps the proved $R$-vs-$\delta$ bounds (Figure 4.5, $q=2$): the GV bound is the best known lower bound; the Elias–Bassalygo upper bound appears in a later section.

<a id="pdf-7251cb8e4bc5-p091-b001"></a>
<!-- pdf-source: page=91; block=1; confidence=0.90 -->
Figure 4.5 plots current bounds on rate $R$ vs. relative distance $\delta$ for binary codes: the GV bound is a lower bound on $R$; the Hamming, Singleton, and (a fourth) bounds are upper bounds on $R$.

<a id="pdf-7251cb8e4bc5-p091-b002"></a>
<!-- pdf-source: page=91; block=2; confidence=0.95 -->
Setup for the proof of Theorem 4.4.1 (needs two lemmas). Recap: for $v\in\mathbb{R}^n$, Euclidean norm $\lVert v\rVert=\sqrt{v_1^2+v_2^2+\cdots+v_n^2}$; $v$ is a unit vector iff $\lVert v\rVert=1$; inner product $\langle u,v\rangle=\sum_i u_i\cdot v_i$.

<a id="pdf-7251cb8e4bc5-p091-b003"></a>
<!-- pdf-source: page=91; block=3; confidence=0.97 -->
**Lemma 4.4.3 (Geometric Lemma).** Let $v_1,\dots,v_m\in\mathbb{R}^N$ be non-zero vectors.

1. If $\langle v_i,v_j\rangle\le 0$ for all $i\ne j$, then $m\le 2N$.
2. If additionally the $v_i$ are unit vectors ($1\le i\le m$) and $\langle v_i,v_j\rangle\le-\varepsilon<0$ for all $i\ne j$, then $m\le 1+\tfrac{1}{\varepsilon}$.

Both items are tight (Exercises 4.15, 4.16). Footnote: for unit vectors, $\langle v_i,v_j\rangle$ equals the cosine of the angle between them.

<a id="pdf-7251cb8e4bc5-p091-b004"></a>
<!-- pdf-source: page=91; block=4; confidence=0.97 -->
**Lemma 4.4.4 (Mapping Lemma).** For every $q$ and $n$ there exists a function $f:[q]^n\to\mathbb{R}^{nq}$ such that for every $c_1,c_2\in[q]^n$,
$$\langle f(c_1),f(c_2)\rangle=1-\left(\tfrac{q}{q-1}\right)\left(\tfrac{\Delta(c_1,c_2)}{n}\right).$$

<a id="pdf-7251cb8e4bc5-p092-b001"></a>
<!-- pdf-source: page=92; block=1; confidence=0.95 -->
Consequences of Lemma 4.4.4:

1. For every $c\in[q]^n$, $\lVert f(c)\rVert=1$.
2. If $\Delta(c_1,c_2)\ge d$ then $\langle f(c_1),f(c_2)\rangle\le 1-\left(\tfrac{q}{q-1}\right)\left(\tfrac{d}{n}\right)$.

Proofs of the Geometric and Mapping Lemmas are deferred to the end of the section.

<a id="pdf-7251cb8e4bc5-p092-b002"></a>
<!-- pdf-source: page=92; block=2; confidence=0.95 -->
**Proof of Theorem 4.4.1.** Let $C=\{c_1,\dots,c_m\}$ be a $q$-ary code of block length $n$ and distance $d$; let $f:[q]^n\to\mathbb{R}^{nq}$ be from Lemma 4.4.4. Each $f(c_i)$ is a unit vector in $\mathbb{R}^{nq}$, and for $i\ne j$, $\langle f(c_i),f(c_j)\rangle\le 1-\left(\tfrac{q}{q-1}\right)\tfrac{d}{n}$. Apply Lemma 4.4.3.

**Part 1:** if $d=\left(1-\tfrac1q\right)n=\tfrac{(q-1)n}{q}$, then $\langle f(c_i),f(c_j)\rangle\le 0$ for $i\ne j$, so by Lemma 4.4.3(1), $m\le 2nq$.

**Part 2:** if $d>\tfrac{(q-1)}{q}n$, then $\langle f(c_i),f(c_j)\rangle\le 1-\left(\tfrac{q}{q-1}\right)\tfrac{d}{n}=-\tfrac{qd-(q-1)n}{(q-1)n}$. Set $\varepsilon:=\tfrac{qd-(q-1)n}{(q-1)n}>0$ and apply Lemma 4.4.3(2) to get $m\le 1+\tfrac{(q-1)n}{qd-(q-1)n}=\tfrac{qd}{qd-(q-1)n}$. $\square$

<a id="pdf-7251cb8e4bc5-p092-b003"></a>
<!-- pdf-source: page=92; block=3; confidence=0.97 -->
**4.4.1 Proof of Geometric and Mapping Lemmas.**

<a id="pdf-7251cb8e4bc5-p092-b004"></a>
<!-- pdf-source: page=92; block=4; confidence=0.94 -->
**Proof of Lemma 4.4.3.** Both parts by linear algebra over $\mathbb{R}$.

Part 1: Choose a generic $u\in\mathbb{R}^N$ with $\langle u,v_i\rangle\ne 0$ for every $i$. Such $u$ exists because each set $\{u:\langle u,v_i\rangle=0\}$ is a dimension-$(N{-}1)$ subspace (as $v_i\ne 0$), and a union of $N$ such subspaces cannot cover $\mathbb{R}^N$.

<a id="pdf-7251cb8e4bc5-p093-b001"></a>
<!-- pdf-source: page=93; block=1; confidence=0.95 -->
**Proof of Lemma 4.4.3 (continued).** WLOG at least half the $v_i$ have $\langle u,v_i\rangle>0$ (else use $-u$); renumber so these are $v_1,\dots,v_\ell$ with $\ell\ge m/2$. Show $v_1,\dots,v_\ell$ are linearly independent, giving $\ell\le N$ and $m\le 2\ell\le 2N$.

Suppose a dependency $\sum_{i\in[\ell]}\alpha_i v_i=0$ with some $\alpha_i\ne 0$; WLOG some $\alpha_i>0$ (negate if needed), and renumber so $\alpha_1,\dots,\alpha_k>0$ and $\alpha_{k+1},\dots,\alpha_\ell\le 0$. Let $w=\sum_{i=1}^k\alpha_i v_i=-\sum_{j=k+1}^\ell\alpha_j v_j$. Then $\langle u,w\rangle=\sum_{i=1}^k\alpha_i\langle u,v_i\rangle\ge\alpha_1\langle u,v_1\rangle>0$, so $w\ne 0$. But
$$0<\langle w,w\rangle=\Big\langle\sum_{i=1}^k\alpha_i v_i,\,-\sum_{j=k+1}^\ell\alpha_j v_j\Big\rangle=-\sum_{i=1,\,j=k+1}^{k,\ell}\alpha_i\alpha_j\langle v_i,v_j\rangle\le 0,$$
since each term has $\alpha_i\ge 0$, $\alpha_j\le 0$, $\langle v_i,v_j\rangle\le 0$. Contradiction, so the $v_i$ are independent; part 1 follows.

Part 2: Let $z=v_1+\cdots+v_m$. Then
$$\lVert z\rVert^2=\sum_{i=1}^m\lVert v_i\rVert^2+2\sum_{i<j}\langle v_i,v_j\rangle\le m+2\binom{m}{2}(-\varepsilon)=m(1-\varepsilon m+\varepsilon),$$
using unit vectors and $\langle v_i,v_j\rangle\le-\varepsilon$. Since $\lVert z\rVert^2\ge 0$, $m(1-\varepsilon m+\varepsilon)\ge 0$; as $m\ge 1$, $1-\varepsilon m+\varepsilon\ge 0$, i.e. $\varepsilon m\le 1+\varepsilon$, so $m\le 1+\tfrac{1}{\varepsilon}$. $\square$

<a id="pdf-7251cb8e4bc5-p094-b001"></a>
<!-- pdf-source: page=94; block=1; confidence=0.90 -->
**Alternate proof (first part), by induction on N.** Base case N=0: m=0, satisfying m ≤ 2N. Inductive step: given m ≥ 1 nonzero vectors v₁,…,v_m ∈ ℝ^N with ⟨v_i,v_j⟩ ≤ 0 for all i≠j (4.8). Since rotation and scaling preserve the sign of inner products, WLOG the distinguished vector equals ⟨1,0,…,0⟩. Write v_i = ⟨α_i, y_i⟩ with α_i ∈ ℝ, y_i ∈ ℝ^{N−1}. Its inner product with v_i equals α_i, so by (4.8) α_i ≤ 0 (4.9).

Claim: at most one of y₁,…,y_{m−1} is the zero vector. If y₁=y₂=0, then ⟨v₁,v₂⟩ = α₁α₂ + ⟨y₁,y₂⟩ = α₁α₂ > 0, since v₁,v₂ nonzero forces α₁,α₂ ≠ 0 and (4.9) forces α₁,α₂ < 0; this contradicts (4.8).

Hence WLOG y₁,…,y_{m−2} are all nonzero. For i≠j ∈ [m−2], ⟨y_i,y_j⟩ = ⟨v_i,v_j⟩ − α_iα_j ≤ ⟨v_i,v_j⟩ ≤ 0. This reduces m vectors in dimension N to m−2 vectors in dimension N−1. By induction m−2 ≤ 2(N−1), giving m ≤ 2N. ∎

<a id="pdf-7251cb8e4bc5-p094-b002"></a>
<!-- pdf-source: page=94; block=2; confidence=0.95 -->
Announces the proof of the Mapping Lemma (Lemma 4.4.4).

<a id="pdf-7251cb8e4bc5-p094-b003"></a>
<!-- pdf-source: page=94; block=3; confidence=0.90 -->
**Proof of Lemma 4.4.4.** Strategy: define a map φ : [q] → ℝ^q handling the n=1 case (up to a normalization constant), then apply φ coordinatewise to build f : [q]^n → ℝ^{nq} with the claimed properties.

Definitions: e_i is the i-th standard unit vector in ℝ^q. Let e = (1/q)∑_{i∈[q]} e_i = ⟨1/q,…,1/q⟩. Then ⟨e_i,e_j⟩ = 1 if i=j and 0 otherwise, and ⟨e,e_i⟩ = ⟨e,e⟩ = 1/q for every i.

<a id="pdf-7251cb8e4bc5-p095-b001"></a>
<!-- pdf-source: page=95; block=1; confidence=0.95 -->
**Proof of Lemma 4.4.4 (cont.).** Define φ : [q] → ℝ^q by φ(i) = e_i − e. For all i,j: ⟨φ(i),φ(j)⟩ = ⟨e_i−e, e_j−e⟩ = ⟨e_i,e_j⟩ − ⟨e_i,e⟩ − ⟨e,e_j⟩ + ⟨e,e⟩ = ⟨e_i,e_j⟩ − 1/q.

Consequences: ‖φ(i)‖² = ⟨e_i,e_i⟩ − 1/q = (q−1)/q (4.10); and for i≠j, ⟨φ(i),φ(j)⟩ = −1/q (4.11).

<a id="pdf-7251cb8e4bc5-p095-b002"></a>
<!-- pdf-source: page=95; block=2; confidence=0.94 -->
**Proof of Lemma 4.4.4 (cont.).** Define f : [q]^n → ℝ^{nq} by, for c = (c₁,…,c_n) ∈ [q]^n,

f(c) = √(q / (n(q−1))) · (φ(c₁), φ(c₂),…, φ(c_n)).

The factor √(q/(n(q−1))) makes f(c) a unit vector.

Condition 1: ‖f(c)‖² = (q/((q−1)n)) · ∑_{i=1}^{n} ‖φ(i)‖² = 1, using the definition of f and (4.10).

<a id="pdf-7251cb8e4bc5-p095-b003"></a>
<!-- pdf-source: page=95; block=3; confidence=0.90 -->
**Proof of Lemma 4.4.4 (cont.).** Second condition: write c₁ = (x₁,…,x_n), c₂ = (y₁,…,y_n). Then

⟨f(c₁),f(c₂)⟩ = (q/(n(q−1))) · ∑_{ℓ=1}^{n} ⟨φ(x_ℓ),φ(y_ℓ)⟩
= (q/(n(q−1))) · [ ∑_{ℓ:x_ℓ≠y_ℓ} (−1/q) + ∑_{ℓ:x_ℓ=y_ℓ} ((q−1)/q) ]   (4.12)
= (q/(n(q−1))) · [ Δ(c₁,c₂)(−1/q) + (n − Δ(c₁,c₂))((q−1)/q) ]   (4.13)
= 1 − (q/(q−1)) · (Δ(c₁,c₂)/n),

as desired. Here (4.12) uses (4.11) and (4.10), and (4.13) uses the definition of Hamming distance Δ. ∎

<a id="pdf-7251cb8e4bc5-p096-b001"></a>
<!-- pdf-source: page=96; block=1; confidence=0.98 -->
# 4.5 Exercises

<a id="pdf-7251cb8e4bc5-p096-b002"></a>
<!-- pdf-source: page=96; block=2; confidence=0.90 -->
**Exercise 4.1.** Given an infinite family of q-ary codes 𝒞 of relative distance δ and ε > 0, prove there exists n₀ such that for all n ≥ n₀, if C_n ∈ 𝒞 is an [n,k]_q code then k/n < 1 − H_q(δ/2) + ε. Use this to conclude Proposition 4.1.1.

<a id="pdf-7251cb8e4bc5-p096-b003"></a>
<!-- pdf-source: page=96; block=3; confidence=0.95 -->
**Exercise 4.2.** Pick an (n−k)×n matrix H over F_q at random. Show that with high probability the code with parity check matrix H achieves the GV bound.

<a id="pdf-7251cb8e4bc5-p096-b004"></a>
<!-- pdf-source: page=96; block=4; confidence=0.95 -->
**Exercise 4.3.** Using the definition of an ε-biased space (Exercise 2.15), show there exists an ε-biased space of size O(k/ε²). Hint: use part 1 of Exercise 2.15.

<a id="pdf-7251cb8e4bc5-p096-b005"></a>
<!-- pdf-source: page=96; block=5; confidence=0.95 -->
**Exercise 4.4.** Argue that a random linear code and its dual both lie on the corresponding GV bound.

<a id="pdf-7251cb8e4bc5-p096-b006"></a>
<!-- pdf-source: page=96; block=6; confidence=0.90 -->
**Exercise 4.5.** For general random (n,k)_q codes (each of the q^k messages independently assigned a uniform random vector in [q]^n): (1) Prove a random q-ary code of rate R > 0 has, w.h.p., relative distance δ ≥ H_q^{−1}(1 − 2R − ε) — worse than the random-linear bound of Theorem 4.2.1. (2) Prove that w.h.p. the relative distance of a random q-ary code of rate R is at most H_q^{−1}(1 − 2R) + ε, i.e. general random codes have worse distance than random linear codes. Hint: use Chebyshev's inequality (Lemma 3.1.8).

<a id="pdf-7251cb8e4bc5-p096-b007"></a>
<!-- pdf-source: page=96; block=7; confidence=0.95 -->
**Exercise 4.6.** Algorithm 4.2.1 computes an (n,k)_q code on the GV bound in time q^{O(n)}; the goal is a deterministic q^{O(n)} construction of a linear [n,k]_q code meeting the GV bound. (1) Argue Theorem 4.2.1 gives a q^{O(kn)}-time algorithm constructing an [n,k]_q code on the GV bound (goal: shave a factor of k off the exponent). (2) A k×n Toeplitz matrix A = {A_{i,j}} satisfies A_{i,j} = A_{i−1,j−1} (constant along each diagonal); example is a 4×6 [matrix, cut off].

<a id="pdf-7251cb8e4bc5-p097-b001"></a>
<!-- pdf-source: page=97; block=1; confidence=0.95 -->
**Definition (Random Toeplitz matrix).** A Toeplitz matrix has constant descending diagonals (illustrated by a 4×6 example with first row `1 2 3 4 5 6` and first column `1,7,8,9`). A random k×n Toeplitz matrix T ∈ F_q^{k×n} is obtained by choosing the entries of its first row and first column independently and uniformly at random from F_q; all remaining entries are fixed by the Toeplitz constraint.

<a id="pdf-7251cb8e4bc5-p097-b002"></a>
<!-- pdf-source: page=97; block=2; confidence=0.90 -->
**Exercise 4.6 (part 2).** Prove: for any nonzero m ∈ F_q^k, the vector m·T is uniformly distributed over F_q^n, i.e. for every y ∈ F_q^n, Pr[m·T = y] = q^{−n}.

<a id="pdf-7251cb8e4bc5-p097-b003"></a>
<!-- pdf-source: page=97; block=3; confidence=0.90 -->
**Hint (part 2).** Express each of the n entries of m·T as a combination of the first-row/first-column variables of T, treating those as variables. Partition them (depending on m) into sets S and S̄, and show: for every fixed y ∈ F_q^n and every fixed assignment to S, there is a unique assignment to S̄ giving m·T = y.

<a id="pdf-7251cb8e4bc5-p097-b004"></a>
<!-- pdf-source: page=97; block=4; confidence=0.95 -->
**Exercise 4.6 (part 3).** Briefly argue that part 2 implies a random code whose generator matrix is a random Toeplitz matrix lies on the GV bound with high probability.

<a id="pdf-7251cb8e4bc5-p097-b005"></a>
<!-- pdf-source: page=97; block=5; confidence=0.95 -->
**Exercise 4.6 (part 4).** Conclude that an [n,k]_q code on the GV bound can be constructed in time q^{O(k+n)}.

<a id="pdf-7251cb8e4bc5-p097-b006"></a>
<!-- pdf-source: page=97; block=6; confidence=0.95 -->
**Exercise 4.7.** Show that the parity-check matrix of an [n,k]_q code lying on the GV bound can be constructed in time q^{O(n)}.

<a id="pdf-7251cb8e4bc5-p097-b007"></a>
<!-- pdf-source: page=97; block=7; confidence=0.93 -->
**Exercise 4.8 (setup).** Seeks a faster GV-bound construction for k = o(n). Fix target distance d = δn. For m ∈ F_q^k and an [n,k]_q code C, define the indicator W_m(C) = 1 if wt(C(m)) < d and 0 otherwise, and D(C) = Σ_{m ∈ F_q^k \ {0}} W_m(C). Write D(G), W_m(G) for the code generated by G. For a k×n matrix M, M_i denotes its ith column and M_{≤i} the submatrix of its first i columns.

<a id="pdf-7251cb8e4bc5-p098-b001"></a>
<!-- pdf-source: page=98; block=1; confidence=0.93 -->
**Exercise 4.8 (continued).** Let G be a uniformly random k×n generator matrix and G a fixed instantiation; assume k < (1 − H_q(δ))n for large enough n. **(1)** Argue C has distance d iff D(C) < 1. **(2)** Argue E[D(G)] < 1.

<a id="pdf-7251cb8e4bc5-p098-b002"></a>
<!-- pdf-source: page=98; block=2; confidence=0.90 -->
**Exercise 4.8 (part 3).** For any 1 ≤ i < n and fixed k×n matrix G, prove:

min_{v ∈ F_q^k} E[ D(G) | G_{≤i} = G_{≤i}, G_{i+1} = v ] ≤ E[ D(G) | G_{≤i} = G_{≤i} ].

<a id="pdf-7251cb8e4bc5-p098-b003"></a>
<!-- pdf-source: page=98; block=3; confidence=0.93 -->
**Exercise 4.8 (part 4).** Prove that Algorithm 4.5.1 outputs a matrix G whose generated linear code is an [n,k,δn]_q code, and conclude that this code lies on the GV bound.

<a id="pdf-7251cb8e4bc5-p098-b004"></a>
<!-- pdf-source: page=98; block=4; confidence=0.92 -->
**Exercise 4.8 (part 5).** Analyze the running time: argue Step 2 can be implemented in poly(n, q^k) time, and conclude Algorithm 4.5.1 runs in poly(n, q^k) time. Hint: maintain a data structure tracking one number for each nonzero m ∈ F_q^k throughout the run.

<a id="pdf-7251cb8e4bc5-p098-b005"></a>
<!-- pdf-source: page=98; block=5; confidence=0.85 -->
**Algorithm 4.5.1** ($q^{O(k)}$-time construction of a code on the GV bound). Input: integer parameters $1 \le k \ne n$ such that $k < (1 - H_q(\delta)n)$. Output: a $k\times n$ generator matrix $G$ for a code of distance $\delta n$.
1. Initialize $G$ to the all-0s matrix (this initialization is arbitrary).
2. For every $1 \le i \le n$: $G^i \leftarrow \arg\min_{v \in \mathbb{F}_q^k} E\big[D(\mathcal{G}) \mid \mathcal{G}^{\le i} = G^{\le i},\, \mathcal{G}^{i+1} = v\big]$.
3. Return $G$.

<a id="pdf-7251cb8e4bc5-p098-b006"></a>
<!-- pdf-source: page=98; block=6; confidence=0.93 -->
**Exercise 4.9.** Derive the GV bound via a graph-theoretic proof (equivalent to the greedy proof of Section 4.2.1). For integers 1 ≤ d ≤ n and q ≥ 1, define the graph G_{n,d,q} = (V,E) with vertex set V = [q]^n and, for u ≠ v ∈ [q]^n, edge (u,v) ∈ E iff Δ(u,v) < d. An independent set I ⊆ V has no edge between any two distinct members. **(1)** Argue any independent set C of G_{n,d,q} is a q-ary code of distance d.

<a id="pdf-7251cb8e4bc5-p099-b001"></a>
<!-- pdf-source: page=99; block=1; confidence=0.94 -->
**Exercise 4.9 (parts 2–3).** **(2)** With Δ the maximum vertex degree of G = (V,E), argue G has an independent set of size at least |V|/(Δ+1). **(3)** Using parts 1 and 2, argue the GV bound.

<a id="pdf-7251cb8e4bc5-p099-b002"></a>
<!-- pdf-source: page=99; block=2; confidence=0.93 -->
**Exercise 4.10.** Improve slightly on the GV bound via a triangle-counting graph argument. Let G_{n,d,q}, N, Δ be as in Exercise 4.9. A triangle is a set {u,v,w} ⊂ V with all three pairwise edges present. Focus on q = 2, d = n/5, and the limit n → ∞. **(1)** Prove a graph on N vertices of maximum degree Δ has at most O(NΔ²) triangles.

<a id="pdf-7251cb8e4bc5-p099-b003"></a>
<!-- pdf-source: page=99; block=3; confidence=0.92 -->
**Exercise 4.10 (part 2).** Prove the number of triangles in G_{n,d,2} is at most 2^n · Σ_{0 ≤ e ≤ 3d/2} C(n,e) · 3^e. Hint: fix u and let e count the coordinates where at least one of v, w disagrees with u; prove e ≤ 3d/2.

<a id="pdf-7251cb8e4bc5-p099-b004"></a>
<!-- pdf-source: page=99; block=4; confidence=0.93 -->
**Exercise 4.10 (part 3).** For d = n/5, simplify the expression to show the number of triangles in G_{n,n/5,2} is O(N · Δ^{2−η}) for some η > 0.

<a id="pdf-7251cb8e4bc5-p099-b005"></a>
<!-- pdf-source: page=99; block=5; confidence=0.95 -->
**Exercise 4.10 (part 4).** Using the (unproved) probabilistic-method result that a graph on N vertices with maximum degree Δ and at most O(N · Δ^{2−η}) triangles has an independent set of size Ω((N/Δ) log Δ), conclude there is a binary code of block length n and distance n/5 of size Ω(n · 2^n / C(n, n/5)) — an Ω(n)-factor improvement over the GV bound.

<a id="pdf-7251cb8e4bc5-p099-b006"></a>
<!-- pdf-source: page=99; block=6; confidence=0.95 -->
**Exercise 4.11.** Use part 1 of Exercise 1.7 to prove the Singleton bound.

<a id="pdf-7251cb8e4bc5-p099-b007"></a>
<!-- pdf-source: page=99; block=7; confidence=0.95 -->
**Exercise 4.12.** For an (n,k,d)_q code C, prove that fixing any n − d + 1 positions uniquely determines the corresponding codeword.

<a id="pdf-7251cb8e4bc5-p099-b008"></a>
<!-- pdf-source: page=99; block=8; confidence=0.90 -->
**Exercise 4.13.** Improve the bound in part 1 of Theorem 4.4.1. **(1)** Prove that for every k ≥ 1 there exist k+1 vectors v_1^k, …, v_{k+1}^k ∈ R^k such that (1) ‖v_i^k‖₂² = 1 for every i ∈ [k+1], and (2) ⟨v_i^k, v_j^k⟩ = −1/k for every i ≠ j ∈ [k+1].

<a id="pdf-7251cb8e4bc5-p100-b001"></a>
<!-- pdf-source: page=100; block=1; confidence=0.95 -->
**Exercise (part 2).** Using the previous part or otherwise, show: if C is a q-ary code of block length n and distance n(1 − 1/q), then |C| ≤ 2(q − 1)n. Remark: this improves part 1 of Theorem 4.4.1 by a factor q/(q − 1).

<a id="pdf-7251cb8e4bc5-p100-b002"></a>
<!-- pdf-source: page=100; block=2; confidence=0.95 -->
**Exercise 4.14.** Show the bound of Exercise 4.13 is tight for q = 2: there exist binary codes C of block length n and distance n/2 with |C| = 2n.

<a id="pdf-7251cb8e4bc5-p100-b003"></a>
<!-- pdf-source: page=100; block=3; confidence=0.97 -->
**Exercise 4.15.** Prove that part 1 of Lemma 4.4.3 is tight.

<a id="pdf-7251cb8e4bc5-p100-b004"></a>
<!-- pdf-source: page=100; block=4; confidence=0.97 -->
**Exercise 4.16.** Prove that part 2 of Lemma 4.4.3 is tight.

<a id="pdf-7251cb8e4bc5-p100-b005"></a>
<!-- pdf-source: page=100; block=5; confidence=0.95 -->
**Exercise 4.17.** Combinatorial proof of the Plotkin bound (part 2 of Theorem 4.4.1). Given an (n, k, d)_q code C with d > n(1 − 1/q), define S = ∑_{c1 ≠ c2 ∈ C} Δ(c1, c2). Regard C as an |C| × n matrix whose rows are codewords.

1. Via each column's contribution, show S ≤ (1 − 1/q)·n·|C|².
2. Via the rows' contribution, show S ≥ |C|(|C| − 1)·d.
3. Conclude part 2 of Theorem 4.4.1.

<a id="pdf-7251cb8e4bc5-p100-b006"></a>
<!-- pdf-source: page=100; block=6; confidence=0.97 -->
**Exercise 4.18.** Prove the Griesmer Bound: for any [n, k, d]_q code, n ≥ ∑_{i=0}^{k−1} ⌈d / q^i⌉. Hint: use Exercise 2.18.

<a id="pdf-7251cb8e4bc5-p100-b007"></a>
<!-- pdf-source: page=100; block=7; confidence=0.97 -->
**Exercise 4.19.** Use Exercise 4.18 to prove part 2 of Theorem 4.4.1 for linear codes.

<a id="pdf-7251cb8e4bc5-p100-b008"></a>
<!-- pdf-source: page=100; block=8; confidence=0.97 -->
**Exercise 4.20.** Use Exercise 4.18 to prove Theorem 4.3.1 for linear codes.

<a id="pdf-7251cb8e4bc5-p101-b001"></a>
<!-- pdf-source: page=101; block=1; confidence=0.98 -->
# 4.6 Bibliographic Notes

<a id="pdf-7251cb8e4bc5-p101-b002"></a>
<!-- pdf-source: page=101; block=2; confidence=0.90 -->
Attributions: the GV bound (Theorem 4.2.1) was proved for general codes by Gilbert [27] and for linear codes by Varshamov [73]. The Singleton bound (Theorem 4.3.1) is due to Singleton [68], with an earlier q = 2 version by Joshi [39]. For prime powers q ≥ 49, algebraic geometric (AG) codes give linear codes beating the q-ary GV bound; AG codes are outside the book's scope (see the survey by Høholdt, van Lint, Pellikaan [37]). Exercise 4.10 is from Jiang and Vardy [38].

Footnote: AG codes are defined only for q a square or a prime and achieve rate R ≥ 1 − δ − 1/(√q − 1); q = 49 is the smallest prime square for which this bound improves on the q-ary GV bound.

<a id="pdf-7251cb8e4bc5-p103-b001"></a>
<!-- pdf-source: page=103; block=1; confidence=0.99 -->
# Chapter 5. The Greatest Code of Them All: Reed-Solomon Codes

<a id="pdf-7251cb8e4bc5-p103-b002"></a>
<!-- pdf-source: page=103; block=2; confidence=0.95 -->
Reed-Solomon codes are optimal, exactly meeting the Singleton bound (Theorem 4.3.1): for every $k \le n$ there is a Reed-Solomon code of dimension $k$, block length $n$, and distance $n - k + 1$. They are fully explicit and have applications beyond coding theory. They are defined via univariate polynomials over a finite field $\mathbb{F}_q$; polynomials over $\mathbb{F}_p$ ($p$ prime) also help describe extension fields $\mathbb{F}_{p^s}$ for $s > 1$.

<a id="pdf-7251cb8e4bc5-p103-b003"></a>
<!-- pdf-source: page=103; block=3; confidence=0.97 -->
## 5.1 Polynomials and Finite Fields

Reviews univariate polynomials over a field: degree, evaluation, root, and the "degree mantra" relating degree to number of roots.

<a id="pdf-7251cb8e4bc5-p103-b004"></a>
<!-- pdf-source: page=103; block=4; confidence=0.98 -->
**Definition 5.1.1.** A polynomial over a variable $X$ and a finite field $\mathbb{F}_q$ is a finite sequence $(f_0, f_1, \dots, f_d)$ with $f_i \in \mathbb{F}_q$, denoted $F(X) = \sum_{i=0}^{d} f_i X^i$. The degree $\deg(F)$ is the largest index $i$ such that $f_i \ne 0$.

<a id="pdf-7251cb8e4bc5-p104-b001"></a>
<!-- pdf-source: page=104; block=1; confidence=0.94 -->
Leading zeroes are ignored (e.g. $2X^3 + X^2 + 5X + 6$ over $\mathbb{F}_7$ has degree 3). $\mathbb{F}_q[X]$ denotes the set of polynomials with coefficients in $\mathbb{F}_q$, with operations:

- **Addition:** $F(X) + G(X) = \sum_{i=0}^{\max(\deg F, \deg G)} (f_i + g_i) X^i$, coefficient addition over $\mathbb{F}_q$.
- **Multiplication:** $F(X) \cdot G(X) = \sum_{i=0}^{\deg F + \deg G} \left( \sum_{j=0}^{\min(i, \deg F)} f_j \cdot g_{i-j} \right) X^i$, operations over $\mathbb{F}_q$.

Examples over $\mathbb{F}_2$: $X + (1+X) = 1$; $X(1+X) = X + X^2$; $(1+X)^2 = 1 + X^2$ (since $2 \equiv 0 \bmod 2$).

<a id="pdf-7251cb8e4bc5-p104-b002"></a>
<!-- pdf-source: page=104; block=2; confidence=0.96 -->
**Definition 5.1.2.** For $F(X) \in \mathbb{F}_q[X]$ and $\alpha \in \mathbb{F}_q$, the evaluation of $F$ at $\alpha$ is $F(\alpha) = \sum_{i=0}^{\deg F} f_i \alpha^i \in \mathbb{F}_q$. The definition extends naturally when $\alpha$ or $F$'s coefficients lie in an extension field $\mathbb{F}_Q \supseteq \mathbb{F}_q$, giving $F(\alpha) \in \mathbb{F}_Q$.

<a id="pdf-7251cb8e4bc5-p104-b003"></a>
<!-- pdf-source: page=104; block=3; confidence=0.93 -->
Polynomials lack multiplicative inverses, but one polynomial can be divided by another to yield a quotient and remainder, formalized next.

<a id="pdf-7251cb8e4bc5-p105-b001"></a>
<!-- pdf-source: page=105; block=1; confidence=0.98 -->
**Proposition 5.1.3 (Polynomial Division).** For $f(X), g(X) \in \mathbb{F}_q[X]$ there exist unique polynomials $q(X)$ (quotient) and $r(X)$ (remainder) with $\deg(r) < \deg(g)$ such that $f(X) = q(X)g(X) + r(X)$. If $g(X) = X - \alpha$ for $\alpha \in \mathbb{F}_q$, then $r(X)$ is the degree-0 polynomial $f(\alpha)$.

<a id="pdf-7251cb8e4bc5-p105-b002"></a>
<!-- pdf-source: page=105; block=2; confidence=0.98 -->
**Definition 5.1.4.** $\alpha \in \mathbb{F}_q$ is a root of $F(X)$ if $F(\alpha) = 0$. Example: $1$ is a root of $1 + X^2$ over $\mathbb{F}_2$.

<a id="pdf-7251cb8e4bc5-p105-b003"></a>
<!-- pdf-source: page=105; block=3; confidence=0.90 -->
Introduces the "Degree Mantra" (bounding roots by degree) and irreducible polynomials, whose existence relates to that of prime-power finite fields.

<a id="pdf-7251cb8e4bc5-p105-b004"></a>
<!-- pdf-source: page=105; block=4; confidence=0.98 -->
**Proposition 5.1.5 ("Degree Mantra").** A nonzero polynomial $f(X)$ of degree $t$ over a field $\mathbb{F}_q$ has at most $t$ distinct roots in $\mathbb{F}_q$.

<a id="pdf-7251cb8e4bc5-p105-b005"></a>
<!-- pdf-source: page=105; block=5; confidence=0.85 -->
**Proof.** By induction on $t$. Base case $t = 0$: done. For $t > 0$: if $f$ has no roots, done; otherwise let $\alpha \in \mathbb{F}_q$ be a root and $g(X) = X - \alpha$. By Proposition 5.1.3, $f(X) = (X - \alpha)q(X) + f(\alpha) = (X - \alpha)q(X)$, so $\deg(f) = 1 + \deg(q)$, giving $\deg(q) = t - 1$. If $\beta \ne \alpha$ is a root of $f$, then $q(\alpha) = f(\beta)\cdot(\beta - \alpha)^{-1}$, and so $\beta$ is also a root of $q$. By induction $q$ has at most $t - 1$ roots, hence $f$ has at most $t$ distinct roots (the $\le t-1$ roots of $q$ plus $\alpha$). $\square$

<a id="pdf-7251cb8e4bc5-p105-b006"></a>
<!-- pdf-source: page=105; block=6; confidence=0.96 -->
### 5.1.1 Irreducibility and Field Extensions

Irreducible polynomials are analogous to prime numbers.

<a id="pdf-7251cb8e4bc5-p105-b007"></a>
<!-- pdf-source: page=105; block=7; confidence=0.98 -->
**Definition 5.1.6.** A polynomial $F(X)$ is irreducible if for every factorization $F(X) = G_1(X)G_2(X)$, $\min(\deg(G_1), \deg(G_2)) = 0$.

<a id="pdf-7251cb8e4bc5-p105-b008"></a>
<!-- pdf-source: page=105; block=8; confidence=0.95 -->
Over $\mathbb{F}_2$: $1 + X^2$ is not irreducible since $(1+X)(1+X) = 1 + X^2$. In contrast, $1 + X + X^2$ is irreducible, since its only possible nontrivial factors are $X$ and $X+1$, and neither divides it. (Text continues past the supplied pages.)

<a id="pdf-7251cb8e4bc5-p106-b001"></a>
<!-- pdf-source: page=106; block=1; confidence=0.95 -->
$1+X+X^2$ is the only irreducible degree-2 polynomial over $\mathbb{F}_2$ (Exercise 5.4). Caution: a polynomial $E(X)\in\mathbb{F}_q[X]$ with no root in $\mathbb{F}_q$ need not be irreducible; e.g. $(1+X+X^2)^2$ over $\mathbb{F}_2$ has no root but is reducible.

<a id="pdf-7251cb8e4bc5-p106-b002"></a>
<!-- pdf-source: page=106; block=2; confidence=0.95 -->
Irreducible polynomials yield non-prime fields: as integers mod a prime form a field, polynomials mod an irreducible polynomial form a field of non-prime size.

<a id="pdf-7251cb8e4bc5-p106-b003"></a>
<!-- pdf-source: page=106; block=3; confidence=0.98 -->
**Theorem 5.1.7.** Let $E(X)$ be an irreducible polynomial of degree $s\ge 2$ over $\mathbb{F}_p$, $p$ prime. Then the set of polynomials in $\mathbb{F}_p[X]$ modulo $E(X)$, denoted $\mathbb{F}_p[X]/E(X)$, is a field.

<a id="pdf-7251cb8e4bc5-p106-b004"></a>
<!-- pdf-source: page=106; block=4; confidence=0.95 -->
**Proof (sketch, analogous to Lemma 2.1.4).** The tenets of $\mathbb{F}_p[X]/E(X)$:
- Elements: polynomials in $\mathbb{F}_p[X]$ of degree $\le s-1$; there are $p^s$ of them.
- Addition: $(F(X)+G(X))\bmod E(X)=F(X)+G(X)$ (plain polynomial addition, since degrees $\le s-1$).
- Multiplication: $(F(X)\cdot G(X))\bmod E(X)$ is the unique $R(X)$ of degree $\le s-1$ with $R(X)+A(X)E(X)=F(X)\cdot G(X)$ for some $A(X)$.
- Additive identity: the zero polynomial; additive inverse of $F(X)$ is $-F(X)$.
- Multiplicative identity: constant $1$; every $F(X)$ has a unique inverse $(F(X))^{-1}$.

<a id="pdf-7251cb8e4bc5-p106-b005"></a>
<!-- pdf-source: page=106; block=5; confidence=0.96 -->
For $p=2$, $E(X)=1+X+X^2$: $\mathbb{F}_2[X]/(1+X+X^2)$ has elements $\{0,1,X,1+X\}$. Each element is its own additive inverse. Multiplicative inverses of $1,\,X,\,1+X$ are $1,\,1+X,\,X$ respectively.

<a id="pdf-7251cb8e4bc5-p107-b001"></a>
<!-- pdf-source: page=107; block=1; confidence=0.98 -->
**Lemma 5.1.8.** Let $E(x)\in\mathbb{F}_q[x]$ be irreducible of degree $s$. Then $\mathbb{F}_q[x]/E(x)$ is a field of size $q^s$.

<a id="pdf-7251cb8e4bc5-p107-b002"></a>
<!-- pdf-source: page=107; block=2; confidence=0.96 -->
**Proof.** Elements of $\mathbb{F}_q[x]/E(x)$ correspond one-to-one with remainders of polynomials in $\mathbb{F}_q[X]$ divided by $E(X)$, i.e. all polynomials of degree $<s$. There are $q^s$ such polynomials ($q$ choices for each coefficient of $X^i$, $0\le i<s$).

<a id="pdf-7251cb8e4bc5-p107-b003"></a>
<!-- pdf-source: page=107; block=3; confidence=0.95 -->
**Theorem 5.1.9.** For all $s\ge 2$ and $\mathbb{F}_p$, there exists an irreducible polynomial of degree $s$ over $\mathbb{F}_p$. The number of such monic irreducible polynomials is $\Theta\!\left(\frac{p^s}{s}\right)$. (A proof is in Appendix B.) The result holds for general $\mathbb{F}_q$; stated over prime fields for simplicity.

<a id="pdf-7251cb8e4bc5-p107-b004"></a>
<!-- pdf-source: page=107; block=4; confidence=0.96 -->
**Corollary 5.1.10.** Combining Theorem 2.1.5 (unique field $\mathbb{F}_{p^s}$ for every prime power) with Theorem 5.1.7, Lemma 5.1.8, and Theorem 5.1.9: the field $\mathbb{F}_{p^s}$ is $\mathbb{F}_p[X]/E(X)$, where $E(X)$ is an irreducible polynomial of degree $s$.

<a id="pdf-7251cb8e4bc5-p107-b005"></a>
<!-- pdf-source: page=107; block=5; confidence=0.90 -->
**5.1.2 Finding Irreducible Polynomials.** To make working with fields fully algorithmic, one needs to find an irreducible polynomial of degree $s$ over $\mathbb{F}_p$ quickly.

<a id="pdf-7251cb8e4bc5-p107-b006"></a>
<!-- pdf-source: page=107; block=6; confidence=0.93 -->
A monic polynomial $E(X)$ of degree $s$ is irreducible iff both hold:
- $\gcd(E(X),\, X^{q^s}-X)=E(X)$, and
- for every $t\notin\{1,s\}$ dividing $s$, $\gcd(E(X),\, X^{q^t}-X)=1$.

(Here $\gcd$ denotes the greatest common factor of two polynomials.)

<a id="pdf-7251cb8e4bc5-p107-b007"></a>
<!-- pdf-source: page=107; block=7; confidence=0.92 -->
Monic means the leading coefficient is $1$. If $E(X)=e_sX^s+e_{s-1}X^{s-1}+\cdots+1$ is irreducible, then $e_s^{-1}\cdot E(X)$ is also irreducible.

<a id="pdf-7251cb8e4bc5-p108-b001"></a>
<!-- pdf-source: page=108; block=1; confidence=0.93 -->
The test is valid because every irreducible polynomial in $\mathbb{F}_q[X]$ of degree exactly $s$ divides $X^{q^s}-X$ (Proposition B.5.14). Euclid's algorithm computes $\gcd(F,G)$ in time polynomial in $\min(\deg F,\deg G)$ and $\log q$ (Section B.7.2), so checking irreducibility of a degree-$s$ polynomial over $\mathbb{F}_q$ takes $\mathrm{poly}(s,\log q)$ time (improvable slightly, Exercise 5.5).

<a id="pdf-7251cb8e4bc5-p108-b002"></a>
<!-- pdf-source: page=108; block=2; confidence=0.92 -->
Brute force enumerates all monic degree-$s$ polynomials over $\mathbb{F}_q$ and tests each, in $\mathrm{poly}(q^s)$ time. Using randomness and Theorem 5.1.9 gives a Las Vegas algorithm: repeatedly generate random polynomials until an irreducible one is found; by Theorem 5.1.9 it tests $O(p^s)$ polynomials in expectation.

<a id="pdf-7251cb8e4bc5-p108-b003"></a>
<!-- pdf-source: page=108; block=3; confidence=0.95 -->
**Algorithm 5.1.1 (Generating Irreducible Polynomial).** Input: prime power $q$, integer $s>1$. Output: a monic irreducible polynomial of degree $s$ over $\mathbb{F}_q$.
1. $b\leftarrow 0$.
2. while $b=0$:
3. $\quad F(X)\leftarrow X^s+\sum_{i=0}^{s-1} f_iX^i$, each $f_i$ uniform random in $\mathbb{F}_q$.
4. $\quad$ if $\gcd(F(X),X^{q^s}-X)=F(X)$:
5. $\qquad b\leftarrow 1$.
6. $\qquad$ for all $t\notin\{1,s\}$ dividing $s$:
7. $\qquad\quad$ if $\gcd(F(X),X^{q^t}-X)\neq 1$: $b\leftarrow 0$.
8. return $F(X)$.

<a id="pdf-7251cb8e4bc5-p108-b004"></a>
<!-- pdf-source: page=108; block=4; confidence=0.97 -->
**Corollary 5.1.11.** There is a Las Vegas algorithm to generate an irreducible polynomial of degree $s$ over any $\mathbb{F}_q$ in expected time $\mathrm{poly}(s,\log q)$.

<a id="pdf-7251cb8e4bc5-p108-b005"></a>
<!-- pdf-source: page=108; block=5; confidence=0.90 -->
Hence a finite field $\mathbb{F}_q$ can be 'constructed' in randomized $\mathrm{poly}(\log q)$ time (Exercise 5.6). Footnote 4: a Las Vegas algorithm always succeeds, with time complexity taken as its expected worst-case run time. This ends the discussion of polynomials; the text next turns to building codes.

<a id="pdf-7251cb8e4bc5-p109-b001"></a>
<!-- pdf-source: page=109; block=1; confidence=0.99 -->
## 5.2 Reed-Solomon Codes

<a id="pdf-7251cb8e4bc5-p109-b002"></a>
<!-- pdf-source: page=109; block=2; confidence=0.97 -->
Recalls the Singleton bound (Theorem 4.3.1): every $(n,k,d)_q$ code has $k \le n-d+1$. Reed-Solomon codes meet this bound ($k = n-d+1$) but require $q \ge n$, showing the Singleton bound is tight at least for $q \ge n$.

<a id="pdf-7251cb8e4bc5-p109-b003"></a>
<!-- pdf-source: page=109; block=3; confidence=0.95 -->
**Definition 5.2.1 (Reed-Solomon code).** For a finite field $\mathbb{F}_q$ and integers $k \le n \le q$, fix a sequence $\alpha = (\alpha_1,\dots,\alpha_n)$ of $n$ distinct evaluation points from $\mathbb{F}_q$. The encoding function $\mathrm{RS}_q[\alpha,k]:\mathbb{F}_q^k \to \mathbb{F}_q^n$ maps a message $m=(m_0,\dots,m_{k-1})$, $m_i \in \mathbb{F}_q$, to the polynomial
$$f_m(X) = \sum_{i=0}^{k-1} m_i X^i \tag{5.1}$$
of degree at most $k-1$, and outputs its evaluations $\mathrm{RS}_q[\alpha,k](m) = (f_m(\alpha_1),\dots,f_m(\alpha_n))$. The Reed-Solomon (RS) code is the image $\{\mathrm{RS}[m] \mid m \in \mathbb{F}_q^k\}$; when $q,\alpha,k$ are clear the map is written $\mathrm{RS}$. A common special case is $n=q-1$ with evaluation points $\mathbb{F}^* \overset{\text{def}}{=} \mathbb{F}\setminus\{0\}$.

<a id="pdf-7251cb8e4bc5-p109-b004"></a>
<!-- pdf-source: page=109; block=4; confidence=0.90 -->
Example: the nine codewords of the $[3,2]_3$ RS code with evaluation points $\mathbb{F}_3$, listed by messages in $\mathbb{F}_3^2$ in lexicographic order (with corresponding polynomials $f_m(X)$).

<a id="pdf-7251cb8e4bc5-p109-b005"></a>
<!-- pdf-source: page=109; block=5; confidence=0.96 -->
Since $\{\alpha_1,\dots,\alpha_n\}$ are distinct, necessarily $n \le q$. For simplicity $k,n,q,\alpha_1,\dots,\alpha_n$ with $k \le n \le q$ are fixed and the code is written $\mathrm{RS}$; results hold for every such choice.

<a id="pdf-7251cb8e4bc5-p109-b006"></a>
<!-- pdf-source: page=109; block=6; confidence=0.99 -->
**Claim 5.2.2.** RS codes are linear codes.

<a id="pdf-7251cb8e4bc5-p110-b001"></a>
<!-- pdf-source: page=110; block=1; confidence=0.96 -->
**Proof.** For $a \in \mathbb{F}_q$ and $f,g \in \mathbb{F}_q[X]$ of degree $\le k-1$, both $af$ and $f+g$ have degree $\le k-1$. By the map (5.1), $f_{m_1}(X)+f_{m_2}(X)=f_{m_1+m_2}(X)$ and $a f_{m_1}(X)=f_{a m_1}(X)$. Hence $\mathrm{RS}(m_1)+\mathrm{RS}(m_2)=\mathrm{RS}(m_1+m_2)$ and $a\,\mathrm{RS}(m_1)=\mathrm{RS}(a m_1)$, so $\mathrm{RS}$ is an $[n,k]_q$ linear code. $\qquad\blacksquare$

<a id="pdf-7251cb8e4bc5-p110-b002"></a>
<!-- pdf-source: page=110; block=2; confidence=0.99 -->
**Claim 5.2.3.** The minimum distance of RS is $n-k+1$.

<a id="pdf-7251cb8e4bc5-p110-b003"></a>
<!-- pdf-source: page=110; block=3; confidence=0.95 -->
The distance bound uses Proposition 5.1.5 (a nonzero degree-$(k-1)$ polynomial over $\mathbb{F}_q$ has at most $k-1$ roots) for the lower bound; the upper bound comes from the Singleton bound (Theorem 4.3.1).

<a id="pdf-7251cb8e4bc5-p110-b004"></a>
<!-- pdf-source: page=110; block=4; confidence=0.95 -->
**Proof of Claim 5.2.3.** Fix $m_1 \ne m_2 \in \mathbb{F}_q^k$. Then $f_{m_1},f_{m_2} \in \mathbb{F}_q[X]$ are distinct of degree $\le k-1$, so $f_{m_1}-f_{m_2} \ne 0$ has degree $\le k-1$. Since $\mathrm{wt}(\mathrm{RS}(m_2)-\mathrm{RS}(m_1)) = \Delta(\mathrm{RS}(m_1),\mathrm{RS}(m_2))$ equals $n$ minus the number of roots of $f_{m_1}-f_{m_2}$ among $\{\alpha_1,\dots,\alpha_n\}$:
$$\Delta(\mathrm{RS}(m_1),\mathrm{RS}(m_2)) = n - |\{\alpha_i \mid f_{m_1}(\alpha_i)=f_{m_2}(\alpha_i)\}|.$$
By Proposition 5.1.5 there are at most $k-1$ roots, so the weight is at least $n-(k-1)=n-k+1$, giving $d \ge n-k+1$. With the Singleton bound $d \le n-k+1$, hence $d = n-k+1$. Distinct polynomials map to distinct codewords (distance $\ge n-k+1 \ge 1$ since $k \le n$), so the code has $q^k$ codewords and dimension $k$; linearity is Claim 5.2.2. An alternate direct argument is in Exercise 5.2. $\qquad\blacksquare$

<a id="pdf-7251cb8e4bc5-p111-b001"></a>
<!-- pdf-source: page=111; block=1; confidence=0.95 -->
Summarizes the exact dimension and distance of RS codes and notes they match the Singleton bound. By the Plotkin bound (Corollary 4.4.2), matching the Singleton bound requires non-constant alphabet size, so growth of $q$ with $n$ is unavoidable; RS achieves it with $q \ge n$.

<a id="pdf-7251cb8e4bc5-p111-b002"></a>
<!-- pdf-source: page=111; block=2; confidence=0.98 -->
**Theorem 5.2.4.** RS is an $[n,k,n-k+1]_q$ code; that is, RS codes match the Singleton bound.

<a id="pdf-7251cb8e4bc5-p111-b003"></a>
<!-- pdf-source: page=111; block=3; confidence=0.94 -->
An explicit generator matrix arises from the monomial basis $1,X,\dots,X^{k-1}$: its $i$th row (rows numbered $0$ to $k-1$) is $(\alpha_1^i,\alpha_2^i,\dots,\alpha_n^i)$. This $k \times n$ matrix is the Vandermonde matrix, with entry in row $i$, column $j$ equal to $\alpha_j^i$.

<a id="pdf-7251cb8e4bc5-p111-b004"></a>
<!-- pdf-source: page=111; block=4; confidence=0.99 -->
## 5.3 Maximum Distance Separable Codes and Properties

<a id="pdf-7251cb8e4bc5-p111-b005"></a>
<!-- pdf-source: page=111; block=5; confidence=0.97 -->
**Definition 5.3.1 (MDS codes).** An $(n,k,d)_q$ code is Maximum Distance Separable (MDS) if $d = n-k+1$. Consequently Reed-Solomon codes are MDS codes.

<a id="pdf-7251cb8e4bc5-p111-b006"></a>
<!-- pdf-source: page=111; block=6; confidence=0.96 -->
**Definition 5.3.2.** For a code $C \subseteq \Sigma^n$ and a subset $S \subseteq [n]$ with $|S| = k$, $C_S$ denotes the set of all codewords of $C$ projected onto the indices in $S$.

<a id="pdf-7251cb8e4bc5-p112-b001"></a>
<!-- pdf-source: page=112; block=1; confidence=0.95 -->
Notes that MDS codes have a projection property, proved first for Reed–Solomon codes and then in general.

<a id="pdf-7251cb8e4bc5-p112-b002"></a>
<!-- pdf-source: page=112; block=2; confidence=0.96 -->
**Proposition 5.3.3.** Let $C \subseteq \Sigma^n$ be an MDS code of (integral) dimension $k$. Then for every $S \subseteq [n]$ with $|S| = k$, the projection satisfies $|C_S| = \Sigma^k$ (i.e. $C_S = \Sigma^k$, the full space of size $|\Sigma|^k$).

<a id="pdf-7251cb8e4bc5-p112-b003"></a>
<!-- pdf-source: page=112; block=3; confidence=0.95 -->
**Proof (Reed–Solomon case).** Fix $S \subseteq [n]$, $|S| = k$, and an arbitrary $v = (v_1,\dots,v_k) \in \mathbb{F}_q^k$; the RS code evaluates polynomials of degree $\le k-1$ at $\alpha_1,\dots,\alpha_n \subseteq \mathbb{F}_q$. Must find a codeword $c$ with $c_S = v$, i.e. a polynomial $F(X) = \sum_{i=0}^{k-1} f_i X^i$ with $F(\alpha_i) = v_i$ for all $i \in S$. Taking $S = [k]$ and treating the $f_i$ as unknowns, the relations $F(\alpha_i) = v_i$ form a linear system whose coefficient matrix is a $k \times k$ Vandermonde matrix in $\alpha_1,\dots,\alpha_k$. This matrix has full rank (Exercise 5.3), so by Exercise 2.7 there is a unique solution $(p_0,\dots,p_{k-1})$, proving the claim for RS codes.

<a id="pdf-7251cb8e4bc5-p112-b004"></a>
<!-- pdf-source: page=112; block=4; confidence=0.93 -->
**Proof of Proposition 5.3.3.** Form the $|C| \times n$ matrix whose rows are the codewords of $C$, so there are $|C| = |\Sigma|^k$ rows and $n$ columns. Since $C$ is MDS, its distance is $d = n - k + 1$. Fix $S \subseteq [n]$ with $|S| = k$. For any two distinct codewords $c_i \ne c_j \in C$, their projections $c_i^S, c_j^S \in C_S$ differ, since otherwise $\triangle(c_i, c_j) \le d - 1$, contradicting minimum distance $d$. Hence distinct codewords map to distinct projections, so $|C_S| = |C| = |\Sigma|^k$. As $C_S \subseteq \Sigma^k$, this forces $C_S = \Sigma^k$. $\square$

<a id="pdf-7251cb8e4bc5-p112-b005"></a>
<!-- pdf-source: page=112; block=5; confidence=0.95 -->
Remarks that Proposition 5.3.3 yields a property relevant to pseudorandomness; see Exercise 5.14.

<a id="pdf-7251cb8e4bc5-p113-b001"></a>
<!-- pdf-source: page=113; block=1; confidence=0.99 -->
# 5.4 Exercises

<a id="pdf-7251cb8e4bc5-p113-b002"></a>
<!-- pdf-source: page=113; block=2; confidence=0.97 -->
**Exercise 5.1.** Prove every function $f : \mathbb{F}_q \to \mathbb{F}_q$ equals a polynomial $P(X) \in \mathbb{F}_q[X]$ of degree $\le q-1$, i.e. $f(\alpha) = P(\alpha)$ for all $\alpha \in \mathbb{F}_q$, and prove such $P$ is unique.

<a id="pdf-7251cb8e4bc5-p113-b003"></a>
<!-- pdf-source: page=113; block=3; confidence=0.97 -->
**Exercise 5.2.** For every $[n,k]_q$ Reed–Solomon code $RS_q[\alpha, k]$ (any $k \le n \le q$, any $\alpha = (\alpha_1,\dots,\alpha_n)$), exhibit two codewords at Hamming distance exactly $n - k + 1$.

<a id="pdf-7251cb8e4bc5-p113-b004"></a>
<!-- pdf-source: page=113; block=4; confidence=0.97 -->
**Exercise 5.3.** For distinct $\alpha_1,\dots,\alpha_k$ in a field $F$, the $k \times k$ Vandermonde matrix $V(\alpha_1,\dots,\alpha_k)$ with $(i,j)$ entry $\alpha_i^{j-1}$ has full rank. Use this to show a dimension-$k$ Reed–Solomon code efficiently corrects $n - k$ erasures.

<a id="pdf-7251cb8e4bc5-p113-b005"></a>
<!-- pdf-source: page=113; block=5; confidence=0.98 -->
**Exercise 5.4.** Prove $X^2 + X + 1$ is the unique irreducible degree-two polynomial over $\mathbb{F}_2$.

<a id="pdf-7251cb8e4bc5-p113-b006"></a>
<!-- pdf-source: page=113; block=6; confidence=0.90 -->
**Exercise 5.5.** Let $s \ge 1$, $r$ the number of prime divisors of $s$, and $\tau(s)$ the number of divisors of $s$; count gcd operations needed to test irreducibility of a degree-$s$ polynomial. (1) Show $\tau(s) - 1$ gcd calls suffice (hint: used in Algorithm 5.1.1). (2) With prime divisors $p_1,\dots,p_r$, a degree-$s$ polynomial $E(X)$ is irreducible iff $\gcd(E(X), X^{q^s} - X) = E(X)$ and for every $i \in [r]$, $\gcd\!\big(E(X), X^{q^{s/p_i}} - X\big) = 1$. (3) Conclude $r + 1$ gcd calls suffice, exponentially fewer than part (1) (hint: prove and use $\tau(s) \ge 2^r$).

<a id="pdf-7251cb8e4bc5-p113-b007"></a>
<!-- pdf-source: page=113; block=7; confidence=0.88 -->
**Exercise 5.6.** On what it means to 'construct' a finite field. Assume $q = p^s$, $s \ge 1$. A representation of $\mathbb{F}_q$ is a triple $(S, \theta, f)$ where $S \subset \{0,1\}^*$ with $|S| = p^s$ is a set of element representations, $\theta$ an auxiliary representation, and $f : \mathbb{F}_{p^s} \to S$ a bijection giving each $\alpha$ its representation $f(\alpha)$. (Continues on next page.)

<a id="pdf-7251cb8e4bc5-p114-b001"></a>
<!-- pdf-source: page=114; block=1; confidence=0.95 -->
**Exercise 5.6 (cont.).** The representation must support $f(\alpha)+f(\beta)$, $-f(\alpha)$, $f(\alpha)\cdot f(\beta)$, identify additive/multiplicative identities in $S$, and compute $f(\alpha)^{-1}$ for nonzero $\alpha$; $\theta$ may aid these. A representation is *efficient* if all operations run in $\mathrm{poly}(\log q)$ time. (1) Given an irreducible $E(X)$ of degree $s$, prove $\mathbb{F}_p[X]/E(X)$ (with $\theta = E(X)$, $f(u) = f_u(X)$ per (5.1), identities the $0$ and $1$ polynomials) is efficient (hint: $\alpha^{q-2} = \alpha^{-1}$ for $\alpha \in \mathbb{F}_q^*$). (2) Deduce that for every prime $p$ and $s \ge 1$, an efficient representation of $\mathbb{F}_{p^s}$ is computable in randomized $\mathrm{poly}(s \log p)$ time.

<a id="pdf-7251cb8e4bc5-p114-b002"></a>
<!-- pdf-source: page=114; block=2; confidence=0.95 -->
**Exercise 5.7.** Give an explicit systematic Reed–Solomon encoding. Given evaluation points $\alpha_1,\dots,\alpha_n$, design an explicit map $f$ from $\mathbb{F}_q^k$ to polynomials of degree $\le k-1$ so that for each message $m \in \mathbb{F}_q^k$ with polynomial $f_m(X)$, the codeword $(f_m(\alpha_i))_{i \in [n]}$ contains $m$ in its first $k$ positions. Prove the map yields an $[n, k, n-k+1]_q$ code.

<a id="pdf-7251cb8e4bc5-p114-b003"></a>
<!-- pdf-source: page=114; block=3; confidence=0.95 -->
**Exercise 5.8.** Let $\alpha \subseteq \mathbb{F}_q^q$ enumerate all elements of $\mathbb{F}_q$. Prove $(RS_q[\alpha, k])^\perp = RS_q[\alpha, q-k]$, i.e. the dual of a Reed–Solomon code is itself Reed–Solomon. Conclude the class of RS codes contains self-dual codes (Exercise 2.33 for the definition).

<a id="pdf-7251cb8e4bc5-p114-b004"></a>
<!-- pdf-source: page=114; block=4; confidence=0.93 -->
**Exercise 5.9.** Show equivalence of the evaluation and prescribed-roots (coefficient) definitions of Reed–Solomon codes. Let $\mathbb{F}_q$ be a field, $\mathbb{F}_q^*$ its nonzero multiplicative group, $n = q - 1$, and $\alpha$ a generator so $\alpha = (1, \alpha, \dots, \alpha^{n-1})$ has distinct entries with $\alpha^n = 1$. Consider $RS_q[\alpha, k] = \{(p(1), p(\alpha), \dots, p(\alpha^{n-1})) \mid p(X) \in F[X],\ \deg p \le k-1\}$.

<a id="pdf-7251cb8e4bc5-p115-b001"></a>
<!-- pdf-source: page=115; block=1; confidence=0.95 -->
**Exercise 5.9 (continued).** Prove the parity-check characterization
$$RS_q[\alpha,k]=\{(c_0,\dots,c_{n-1})\in F^n \mid C(\alpha^\ell)=0\text{ for }1\le\ell\le n-k\},$$
where $C(X)=c_0+c_1X+\cdots+c_{n-1}X^{n-1}$ (eq. 5.2). Hint: Exercise 2.3.

<a id="pdf-7251cb8e4bc5-p115-b002"></a>
<!-- pdf-source: page=115; block=2; confidence=0.93 -->
**Exercise 5.10 (Generalized Reed–Solomon codes).** For a field $F$ with $|F|\ge n$, distinct $\alpha=(\alpha_1,\dots,\alpha_n)$, and nonzero $v=(v_1,\dots,v_n)\in(F^*)^n$, define
$$GRS_F[\alpha,k,v]=\{(v_1p(\alpha_1),\dots,v_np(\alpha_n))\mid p\in F[X],\ \deg p<k\}\quad(5.3).$$
Note $RS_q[\alpha,k]=GRS_{F_q}[\alpha,k,(1,\dots,1)]$.
1. Prove $GRS_F[\alpha,k,v]$ is an $[n,k,n-k+1]_F$ linear code.
2. Prove the dual is $GRS_F[\alpha,k,v]^\perp=GRS_F[\alpha,n-k,u]$ with $u_i=\dfrac{1}{v_i\prod_{j\ne i}(\alpha_i-\alpha_j)}$. Hint: reduce to showing $\sum_{i=1}^n u_iv_ip(\alpha_i)q(\alpha_i)=0$ for $\deg p<k$, $\deg q<n-k$; expand $h=p\cdot q$ (degree $<n$) in Lagrange polynomials $L_i$ ($L_i(\alpha_j)=\delta_{ij}$) and use that the coefficient of $x^{n-1}$ in $h$ is $0$.
3. Prove the dual of $RS[\alpha,k]$, when $\alpha$ enumerates all of $F_q^*$, is the RS variant mapping a message polynomial $m(X)$ ($\deg<n-k$) to evaluations of $X\cdot m(X)$ on $\alpha$.
4. Derive Exercise 5.8 as a corollary of Part 2.

<a id="pdf-7251cb8e4bc5-p115-b003"></a>
<!-- pdf-source: page=115; block=3; confidence=0.95 -->
**Exercise 5.11 (BCH codes).** Fix integer $m$; let $q=2^m$, $n=q-1$. Let the nonzero elements of $\mathbb F_{2^m}$ be $\{\eta_1,\dots,\eta_n\}$ and $\alpha=(\eta_1,\dots,\eta_n)$. For $0\le k\le n$, the binary BCH code is $C_{BCH}=C_{BCH}(m,k):=RS_{2^m}[\alpha,k]\cap\mathbb F_2^n$, i.e. the RS codewords all of whose coordinates lie in $\mathbb F_2\subseteq\mathbb F_{2^m}$. (BCH = Bose–Chaudhuri–Hocquenghem.)

<a id="pdf-7251cb8e4bc5-p116-b001"></a>
<!-- pdf-source: page=116; block=1; confidence=0.88 -->
**Exercise 5.11 (continued).**
1. With $d=n-k+1$, prove $C_{BCH}$ is a binary linear code of distance $\ge d$ and dimension $\ge n-(d-1)\log_2(n+1)$. Hint: use characterization (5.2).
2. Prove the better dimension bound $n-\left\lceil\frac{d-1}{2}\right\rceil\log_2(n+1)$. Hint: there are redundant checks among the parity checks (5.2) because the coefficients lie in $\mathbb F_2$.
3. For $d=3$, identify $C_{BCH}$ with a previously seen code.
4. Define the subcode of $C_{BCH}$ with a global parity check $c_1+c_2+\cdots+c_n=0$ (over $\mathbb F_2$). For even $d$, use the BCH code with a global parity check to construct a binary linear code of distance $\ge d$ and dimension $\ge n-(d/2-1)\log_2(n+1)-1$.
5. Conclude that for all $n=2^m-1$ and integers $d$ with $2\le d<n/\log_2 n$ [source garbled], one can construct an $[n,k',d']_2$ code with $d'\ge d$ and $k'\ge n-\left\lfloor\frac{d-1}{2}\right\rfloor\log_2(n+1)-1$.
6. Prove the $\left\lfloor\frac{d-1}{2}\right\rfloor$ factor cannot be any smaller. Hint: Hamming bound.

<a id="pdf-7251cb8e4bc5-p116-b002"></a>
<!-- pdf-source: page=116; block=2; confidence=0.95 -->
**Exercise 5.12 (binary intersection of GRS codes).** Let $C_{GRS}=GRS_F[\alpha,k,v]$ (eq. 5.3) of dimension $k$, block length $n$, over $F=\mathbb F_{2^m}$. Define the binary intersection $C^*:=C_{GRS}\cap\mathbb F_2^n$.
1. Prove $C^*$ has distance $\ge d:=n-k+1$.
2. Prove $C^*$ is a binary linear code of rate $\ge 1-\frac{(n-k)m}{n}$. Hint: count parity checks.
3. For nonzero $c\in\mathbb F_2^n$, prove that for every choice of evaluation points $\alpha$ there are at most $(2^m-1)^k$ choices of $v$ with $c\in C_{GRS}$.
4. Prove that if integer $D$ satisfies $\mathrm{Vol}_2(n,D-1)<(2^m-1)^{n-k}$, where $\mathrm{Vol}_2(n,D-1)=\sum_{i=0}^{D-1}\binom{n}{i}$, then there exists $v\in(F^*)^n$ such that the minimum distance of $C^*$ is at least $D$.
5. Using parts 2 and 4, prove the family $GRS_F[\alpha,k,v]\cap\mathbb F_2^n$ contains binary linear codes meeting the Gilbert–Varshamov bound.

<a id="pdf-7251cb8e4bc5-p117-b001"></a>
<!-- pdf-source: page=117; block=1; confidence=0.95 -->
**Exercise 5.13 (polynomial view of Hadamard codes).** Recall the $[2^r,r,2^{r-1}]_2$ Hadamard code generated by the $r\times 2^r$ matrix whose $i$-th column ($0\le i\le 2^r-1$) is the binary representation of $i$. Prove that the Hadamard codeword for message $(m_1,\dots,m_r)\in\{0,1\}^r$ is the evaluation of the multivariate polynomial $m_1X_1+m_2X_2+\cdots+m_rX_r$ over all assignments $(X_1,\dots,X_r)\in\{0,1\}^r$. Using this, reprove that the code has distance $2^{r-1}$.

<a id="pdf-7251cb8e4bc5-p117-b002"></a>
<!-- pdf-source: page=117; block=2; confidence=0.90 -->
**Exercise 5.14 ($t$-wise independence).** Recall (Exercise 2.14): $S\subseteq\mathbb F_q^n$ is a $t$-wise independent source ($1\le t\le n$) if for every $I\subseteq[n]$ with $|I|=t$, a uniform sample $(X_1,\dots,X_n)$ from $S$ has $\{X_i:i\in I\}$ uniform and independent over $\mathbb F_q$ (samplable with $\log_2|S|$ bits).
1. Let $C$ be a linear code with no coordinate identically $0$; prove $C$ is a 1-wise independent source.
2. Prove every $[n,k]_q$ MDS code is a $k$-wise independent source but not a $(k+1)$-wise independent source.
3. Using Part 2 or otherwise, prove there exists a $k$-wise independent source $S\subseteq\mathbb F_q^m$ of size $\le q^k$ for $q\ge m$. Show how to pick $q$ so $S$ is viewable as a $k$-wise independent source in $\mathbb F_2^{m\log_2 q}$ of size $\le(2m)^k$. Setting $m,q$ as functions of $n,k$, show that $k\cdot(\log_2 n-\log_2\log_2 n+O(1))$ random bits suffice to sample from a $k$-wise independent source over $\mathbb F_2^n$.
4. For $0<p\le 1/2$, call binary $X_1,\dots,X_n$ $p$-biased and $t$-wise independent if any $t$ are independent and $\Pr[X_i=1]=p$ for all $i$. For $p$ a power of $1/2$: show any $t\log_2(1/p)$-wise independent variables can be converted into $t$-wise independent $p$-biased ones. Conclude such sources can be built with $t\log_2(1/p)(1+\log_2(n\log_2(1/p)))$ uniform bits; then improve to $t(1+\max(\log_2(1/p),\log_2 n))$ uniform bits.

<a id="pdf-7251cb8e4bc5-p117-b003"></a>
<!-- pdf-source: page=117; block=3; confidence=0.90 -->
**Exercise 5.15.** Improving the randomness of Exercise 5.14 Part 3 by nearly a factor of 2: using Exercises 2.14 and 5.11 part 5, prove that for all integers $1\le k\le n$, at most $\lfloor\frac{k}{2}\rfloor\log_2(2n)$ random bits suffice to compute $n$ bits that are $k$-wise independent.

<a id="pdf-7251cb8e4bc5-p117-b004"></a>
<!-- pdf-source: page=117; block=4; confidence=0.90 -->
**Exercise 5.16 (burst errors).** Motivation only: errors often occur in contiguous bursts (e.g. a scratch on a DVD/disk); the exercise develops using Reed–Solomon codes to correct bursty errors.

<a id="pdf-7251cb8e4bc5-p118-b001"></a>
<!-- pdf-source: page=118; block=1; confidence=0.90 -->
**Definition (burst error patterns).** For e ∈ {0,1}^n: e is a *t-single burst error pattern* if all its nonzero bits lie in some range [i, i+t−1] with 1 ≤ i ≤ n−t+1. e is an *(s,t)-burst error pattern* if it is a union of at most s such t-single bursts (nonzero bits contained in at most s contiguous ranges in [n]).

<a id="pdf-7251cb8e4bc5-p118-b002"></a>
<!-- pdf-source: page=118; block=2; confidence=0.95 -->
**Definition ((s,t)-burst error correcting).** A binary code C ⊆ {0,1}^n is *(s,t)-burst error correcting* if every (s,t)-burst error pattern is uniquely decodable: for any (s,t)-burst pattern e and codeword c ∈ C, the only c′ ∈ C with (c+e)−c′ an (s,t)-burst pattern is c′ = c.

<a id="pdf-7251cb8e4bc5-p118-b003"></a>
<!-- pdf-source: page=118; block=3; confidence=0.85 -->
**Exercise (2 parts).** (1) Show that if C is (st)-error correcting (Definition 1.3.5) then it is (s,t)-burst error correcting; conclude that for every ε>0 there is a code of rate Ω(ε²) and block length n that is (s,t)-burst correcting whenever s·t ≤ (1/4 − ε)·n. (2) Show that for every rate R>0 and large enough n there exist (s,t)-burst correcting codes as long as s·t ≤ ((1−R−ε)/2)·n and t ≥ Ω(log n / ε); in particular one can correct from a (1/2 − ε) fraction of burst-errors (each burst long enough) with rate Ω(ε). Hint: use Reed-Solomon codes.

<a id="pdf-7251cb8e4bc5-p118-b004"></a>
<!-- pdf-source: page=118; block=4; confidence=0.90 -->
**Exercise 5.17 (Chinese Remainder code).** Let 1 ≤ k < n, and p₁ < p₂ < ⋯ < pₙ distinct primes. Set K = ∏_{i=1}^{k} pᵢ and N = ∏_{i=1}^{n} pᵢ; Z_M = {0,…,M−1}. Encoding E : Z_K → Z_{p₁} × ⋯ × Z_{pₙ}, E(m) = (m mod p₁, …, m mod pₙ) (symbols lie in different alphabets, but distance is well-defined). Task: for m₁ ≠ m₂, define indicator bᵢ = 1 iff E(m₁)ᵢ ≠ E(m₂)ᵢ; prove ∏_{i=1}^{n} pᵢ^{bᵢ} > N/K, and deduce that E(m₁) and E(m₂) differ in at least n − k + 1 locations.

<a id="pdf-7251cb8e4bc5-p118-b005"></a>
<!-- pdf-source: page=118; block=5; confidence=0.95 -->
**Exercise 5.18 (derivatives over F_q).** For f(X) = ∑_{i=0}^{t} fᵢ Xⁱ over F_q, define the derivative f′(X) = ∑_{i=0}^{t−1} (i+1)·f_{i+1}·Xⁱ. Write f^{(i)}(X) for the i-fold derivative. The exercise records facts about these derivatives (stated in the following items).

<a id="pdf-7251cb8e4bc5-p119-b001"></a>
<!-- pdf-source: page=119; block=1; confidence=0.95 -->
**Exercise 5.18 (items).** (1) Define R(X,Z) = f(X+Z) = ∑_{i=0}^{t} rᵢ(X)·Zⁱ; then for every j ≥ 1, f^{(j)}(X) = j!·r_j(X). (2) For every j ≥ char(F_q), f^{(j)}(X) ≡ 0. (3) For j < char(F_q), if f^{(i)}(α) = 0 for every 0 ≤ i < j (some α ∈ F_q), then (X−α)^j divides f(X). (4) Generalized degree mantra (extending Prop. 5.1.5): if f ≠ 0 has degree t and m ≤ char(F_q), then there are at most ⌊t/m⌋ distinct α ∈ F_q with f^{(j)}(α) = 0 for every 0 ≤ j < m.

<a id="pdf-7251cb8e4bc5-p119-b002"></a>
<!-- pdf-source: page=119; block=2; confidence=0.92 -->
**Exercise 5.19 (derivative code).** Integer m ≥ 1, parameters k < char(F_q) and n with m < k < nm. For message m ∈ F_q^k let f_m(X) be the Reed-Solomon message polynomial; let α₁,…,αₙ ∈ F_q be distinct. The (n,k,m) derivative codeword is the m×n matrix whose (j+1)-th row (j = 0,…,m−1) is (f_m^{(j)}(α₁), f_m^{(j)}(α₂), …, f_m^{(j)}(αₙ)).

<a id="pdf-7251cb8e4bc5-p119-b003"></a>
<!-- pdf-source: page=119; block=3; confidence=0.95 -->
**Exercise 5.19 (items).** (1) Prove the code is F_q-linear: if c₁, c₂ ∈ (F_q^m)^n are codewords then αc₁ + βc₂ is a codeword for all α,β ∈ F_q (αv scales each coordinate of v ∈ F_q^m by α, applied componentwise). (2) Prove the code has rate k/(nm) and distance at least n − ⌊(k−1)/m⌋.

<a id="pdf-7251cb8e4bc5-p119-b004"></a>
<!-- pdf-source: page=119; block=4; confidence=0.92 -->
**Exercise 5.20 (Folded Reed-Solomon).** Integer m ≥ 1; distinct α₁,…,αₙ ∈ F_q and γ ∈ F_q* such that the sets {αᵢ, αᵢγ, αᵢγ², …, αᵢγ^{m−1}} (Eq. 5.4) are pairwise disjoint across i ∈ [n]. Footnote: char(F_q) = p when q = p^s (p prime); any natural i in F_q equals i mod char(F_q).

<a id="pdf-7251cb8e4bc5-p120-b001"></a>
<!-- pdf-source: page=120; block=1; confidence=0.92 -->
**Exercise 5.20 (codeword).** With parameters (m,k,n,γ,α₁,…,αₙ) and RS message polynomial f_m(X), the codeword for message m ∈ F_q^k is the m×n matrix with (j+1)-th row (j = 0,…,m−1) equal to (f_m(α₁·γʲ), f_m(α₂·γʲ), …, f_m(αₙ·γʲ)). **Task:** prove the code has rate k/(nm) and distance at least n − ⌊(k−1)/m⌋.

<a id="pdf-7251cb8e4bc5-p120-b002"></a>
<!-- pdf-source: page=120; block=2; confidence=0.93 -->
**Exercise 5.21 (general polynomial codes).** Integer m ≥ 1 with m < k ≤ n. Let E₁(X),…,Eₙ(X) be n polynomials over F_q, each of degree m, pairwise coprime (deg gcd(Eᵢ,Eⱼ) = 0 for i ≠ j). For message m ∈ F_q^k with RS message polynomial f_m(X), the codeword is (f_m(X) mod E₁(X), …, f_m(X) mod Eₙ(X)), each residue (degree ≤ m−1) identified with an element of F_{q^m} via a fixed bijection.

<a id="pdf-7251cb8e4bc5-p120-b003"></a>
<!-- pdf-source: page=120; block=3; confidence=0.94 -->
**Exercise 5.21 (items).** (1) Prove the code has rate k/(nm) and distance at least n − ⌊(k−1)/m⌋ (i.e. it is MDS). (2) With distinct α₁,…,αₙ and Eᵢ(X) = X − αᵢ, show the m=1 case is the Reed-Solomon code. (3) With Eᵢ(X) = (X − αᵢ)^m, show it is the derivative code (Ex. 5.19), under an appropriate per-i mapping from degree-≤(m−1) polynomials to F_q^m depending on Eᵢ. (4) With γ ∈ F_q* satisfying (5.4) and Eᵢ(X) = ∏_{j=0}^{m−1}(X − αᵢ·γʲ), show it is the folded Reed-Solomon code (Ex. 5.20), under a similar per-i mapping.

<a id="pdf-7251cb8e4bc5-p121-b001"></a>
<!-- pdf-source: page=121; block=1; confidence=0.95 -->
**Exercise 5.22 (Eisenstein's criterion).** Work in the ring `Fq(Y)[X]` of polynomials in `X` whose coefficients lie in `Fq(Y)`, the ring of polynomials in `Y` over `Fq`. Let `F(X,Y) = X^t + f_{t-1}(Y)·X^{t-1} + ... + f_0(Y)` with each `f_i(Y) ∈ Fq(Y)`. Let `P(Y)` be a prime of `Fq(Y)` (degree ≥ 1 and `P | A·B ⇒ P | A` or `P | B`). If (i) `P(Y) | f_i(Y)` for every `0 ≤ i < t`, and (ii) `P(Y)^2 ∤ f_0(Y)`, then `F(X,Y)` has no non-trivial factors over `Fq(Y)[X]` (every factor has degree `t` or `0` in `X`).

<a id="pdf-7251cb8e4bc5-p121-b002"></a>
<!-- pdf-source: page=121; block=2; confidence=0.80 -->
**Proof (guided steps).**
1. For contradiction suppose `F = G·H` with `G(X,Y) = Σ_{i=0}^{t1} g_i(Y)·X^i` and `H(X,Y) = Σ_{i=0}^{t2} h_i(Y)·X^i`, `0 < t1, t2 < t`. Show `P(Y)` does not divide both `g_0(Y)` and `h_0(Y)`; WLOG `P(Y) | g_0(Y)` and `P(Y) ∤ h_0(Y)`.
2. Show there exists `i*` with `P(Y) | g_i(Y)` for all `0 ≤ i < i*` but `P(Y) ∤ g_{i*}(Y)` (set `g_t(Y) = 1`).
3. Show `P(Y)` does not divide `f_i(Y)`, and conclude `F(X,Y)` has no non-trivial factors.

<a id="pdf-7251cb8e4bc5-p121-b003"></a>
<!-- pdf-source: page=121; block=3; confidence=0.95 -->
**Exercise 5.23.** Construct an algebraic-geometric (AG) code and establish its rate vs. distance trade-off. Let `p` be prime and `q = p^2`. Consider over `Fq` the equation

`Y^p + Y = X^{p+1}`  (5.5)

<a id="pdf-7251cb8e4bc5-p122-b001"></a>
<!-- pdf-source: page=122; block=1; confidence=0.90 -->
**Exercise 5.23 (parts).**
1. Show (5.5) has exactly `p^3` solutions in `Fq × Fq`; i.e. `S = {(α,β) ∈ F_q^2 | β^p + β = α^{p+1}}` has `|S| = p^3`.
2. Show `F(X,Y) = Y^p + Y − X^{p+1}` is irreducible over `Fq` (hint: Exercise 5.22).
3. Let `n = p^3` and define `ev : Fq[X,Y] → Fq^n` by `ev(f) = (f(α,β) : (α,β) ∈ S)`. Show that if `f ≠ 0` and `f` is not divisible by `Y^p + Y − X^{p+1}`, then `ev(f)` has Hamming weight ≥ `n − deg(f)(p+1)`, where `deg(f)` is total degree. Hint — Bézout: nonzero `f, g ∈ Fq[X,Y]` with no common factor have at most `deg(f)·deg(g)` common zeroes.
4. For integer `ℓ ≥ 1`, let `F^ℓ = {f ∈ Fq[X,Y] | deg(f) ≤ ℓ, deg_X(f) ≤ p}`. Show `F^ℓ` is an `Fq`-linear space of dimension `(ℓ+1)(p+1) − p(p+1)/2`.
5. Let `C = {ev(f) | f ∈ F^ℓ} ⊆ Fq^n`, `n = p^3`. Show `C` is a linear code with minimum distance ≥ `n − ℓ(p+1)`.
6. Deduce an `[n,k]_q` code with distance `d ≥ n − k + 1 − p(p−1)/2` (off from the Singleton bound by `p(p−1)/2`, block length `n = q^{3/2}`, deficiency `o(n)`).

<a id="pdf-7251cb8e4bc5-p122-b002"></a>
<!-- pdf-source: page=122; block=2; confidence=0.90 -->
**Exercise 5.24.** Goal: a more efficient error-detection algorithm for Reed–Solomon codes using data-streaming algorithms (a single sequential pass, poly-logarithmic time per input location and poly-logarithmic space). Plan: first define an unrelated problem solvable by a randomized data-stream algorithm, then solve RS error detection in the streaming setting using that as a black box.

<a id="pdf-7251cb8e4bc5-p123-b001"></a>
<!-- pdf-source: page=123; block=1; confidence=0.90 -->
**Exercise 5.24 (parts).**
1. For `σ = ((i_1,α_1), ..., (i_n,α_n)) ∈ ([m] × Fq)^n`, define `y = y(σ) ∈ Fq^m` by `y_ℓ = Σ_{ {j∈[n] | i_j = ℓ} } α_j` for `ℓ ∈ [m]`. Give a randomized data-stream algorithm that outputs 0 iff `y = 0` with probability ≥ 2/3, using ≤ `polylog(q(m+n))` time per input position and ≤ `O(log q(m+n))` space; assume oracle access to an irreducible polynomial of degree `t` over `Fq`. Hint: instead of storing `y`, compute a single coordinate `E(y)_j` of an ECC encoding `E : Fq^ℓ → Fq^L` with `j ∈ [L]` uniformly random, using a Reed–Solomon code for fast evaluation.
2. Given a `[q,k]_q` Reed–Solomon code `C` (evaluation points `Fq`), give a data-stream error-detection algorithm using `O(log q)` space and `polylog q` time per received-word position, correct with probability ≥ 2/3, assuming access to `k` and `q`. Hint: Part 1 and Exercise 5.8.

<a id="pdf-7251cb8e4bc5-p123-b002"></a>
<!-- pdf-source: page=123; block=2; confidence=0.92 -->
**§5.5 Bibliographic Notes.** RS codes invented by Reed and Solomon [61] as polynomial evaluations; Gorenstein and Zierler [29] showed that for specific `α` an RS code is a BCH code (cf. Exercise 5.9). BCH codes due to Bose and Ray-Chaudhuri [9] and Hocquenghem [36], originally via polynomial coefficients; the subcode-of-RS definition (Exercise 5.11) uses [29]. Chinese Remainder Codes (Exercise 5.17) due to Mandelbaum [49]. Derivative Codes (Exercise 5.19) due to Rosenbloom and Tsfasman [63], a subclass of Multiplicity Codes of Kopparty, Saraf and Yekhanin [44]. Folded RS codes (Exercise 5.20) introduced by Krachovsky [45], highlighted by Guruswami and Rudra [32]. Exercise 5.21 based on Guruswami and Kopparty [30].

<a id="pdf-7251cb8e4bc5-p125-b001"></a>
<!-- pdf-source: page=125; block=1; confidence=0.95 -->
**Part III.** The Codes

<a id="pdf-7251cb8e4bc5-p127-b001"></a>
<!-- pdf-source: page=127; block=1; confidence=0.98 -->
# Chapter 6 — When Polynomials Save the Day: Polynomial Based Codes

<a id="pdf-7251cb8e4bc5-p127-b002"></a>
<!-- pdf-source: page=127; block=2; confidence=0.90 -->
Reed-Solomon codes achieve the optimal dimension-distance tradeoff, meeting the Singleton bound (Theorem 4.3.1) with $k = n - d + 1$, but only over large alphabets $q \ge n$. No explicit asymptotically good code over small alphabets has yet been seen.

<a id="pdf-7251cb8e4bc5-p127-b003"></a>
<!-- pdf-source: page=127; block=3; confidence=0.95 -->
**Question 6.0.1.** Do there exist explicit asymptotically good codes for small alphabets $q \ll n$?

<a id="pdf-7251cb8e4bc5-p127-b004"></a>
<!-- pdf-source: page=127; block=4; confidence=0.90 -->
Introduces (generalized) Reed-Muller codes, an extension of Reed-Solomon codes to multivariate functions of total degree at most $r$, giving codes over smaller alphabets at a cost in the dimension-distance tradeoff. Bivariate functions give block length $n = q^2$; more variables increase length further at fixed $q$. Distance is analyzed via polynomial-distance lemmas (Lemmas 6.2.2, 6.3.1, 6.4.1).

<a id="pdf-7251cb8e4bc5-p127-b005"></a>
<!-- pdf-source: page=127; block=5; confidence=0.95 -->
## 6.1 The generic construction

For a monomial $X^d = X_1^{d_1} X_2^{d_2} \cdots X_m^{d_m}$, its total degree is $d_1 + d_2 + \cdots + d_m$. This is next extended to the degree of a polynomial.

<a id="pdf-7251cb8e4bc5-p128-b001"></a>
<!-- pdf-source: page=128; block=1; confidence=0.95 -->
**Definition 6.1.1.** The total degree of a polynomial $P(X) = \sum_d c_d X^d$ over $\mathbb{F}_q$ (each $c_d \in \mathbb{F}_q$) is the maximum, over $d$ with $c_d \ne 0$, of the total degree of $X^d$; denoted $\deg(P)$. Example: $\deg(3X^3Y^4 + X^5 + Y^6) = 7$.

<a id="pdf-7251cb8e4bc5-p128-b002"></a>
<!-- pdf-source: page=128; block=2; confidence=0.90 -->
For $f : \mathbb{F}_q^m \to \mathbb{F}_q$, $\deg(f)$ is the minimal degree of a polynomial $P \in \mathbb{F}_q[X_1,\ldots,X_m]$ with $f(\alpha) = P(\alpha)$ for all $\alpha \in \mathbb{F}_q^m$. Since $a^q - a = 0$ for every $a \in \mathbb{F}_q$ (Exercise 2.4), a minimal-degree polynomial has individual degree at most $q-1$ in each variable.

<a id="pdf-7251cb8e4bc5-p128-b003"></a>
<!-- pdf-source: page=128; block=3; confidence=0.93 -->
**Definition 6.1.2.** $\deg_{X_i}(p)$ denotes the degree of polynomial $p$ in variable $X_i$, and $\deg_{X_i}(f)$ the degree in $X_i$ of the minimal polynomial for a function $f$. Examples: $\deg_X(3X^3Y^4 + X^5 + Y^6) = 5$, $\deg_Y(\cdot) = 6$. For every $f : \mathbb{F}_q^m \to \mathbb{F}_q$, $\deg_{X_i}(f) \le q-1$ for all $i \in [m]$.

<a id="pdf-7251cb8e4bc5-p128-b004"></a>
<!-- pdf-source: page=128; block=4; confidence=0.95 -->
**Definition 6.1.3 (Reed-Muller Codes).** For prime power $q$ and positive integers $m, r$, the Reed-Muller code $\mathrm{RM}(q,m,r)$ is the set of evaluations, over all points in $\mathbb{F}_q^m$, of all $m$-variate polynomials in $\mathbb{F}_q[X_1,\ldots,X_m]$ of total degree at most $r$ and individual degree at most $q-1$. Formally, $\mathrm{RM}(q,m,r) \overset{\text{def}}{=} \{ f : \mathbb{F}_q^m \to \mathbb{F}_q \mid \deg(f) \le r \}$.

<a id="pdf-7251cb8e4bc5-p128-b005"></a>
<!-- pdf-source: page=128; block=5; confidence=0.92 -->
For $m = q = 2$, $r = 1$: the bivariate polynomials over $\mathbb{F}_2$ of degree $\le 1$ are $0, 1, X_1, X_2, 1+X_1, 1+X_2, X_1+X_2, 1+X_1+X_2$. Ordering evaluation points $(X_1,X_2)$ as $(0,0),(0,1),(1,0),(1,1)$: $\mathrm{RM}(2,2,1) = \{(0,0,0,0),(1,1,1,1),(0,0,1,1),(0,1,0,1),(1,1,0,0),(1,0,1,0),(0,1,1,0),(1,0,0,1)\}$. Note $\mathrm{RM}(q,m,1)$ is almost the Hadamard code (Exercise 5.9).

<a id="pdf-7251cb8e4bc5-p128-b006"></a>
<!-- pdf-source: page=128; block=6; confidence=0.93 -->
$\mathrm{RM}(q,m,r)$ has alphabet $\mathbb{F}_q$, block length $n = q^m$, and is a linear code (Exercise 6.1).

<a id="pdf-7251cb8e4bc5-p128-b007"></a>
<!-- pdf-source: page=128; block=7; confidence=0.95 -->
**Question 6.1.4.** What are the dimension and distance of an $\mathrm{RM}(q,m,r)$ code?

<a id="pdf-7251cb8e4bc5-p128-b008"></a>
<!-- pdf-source: page=128; block=8; confidence=0.90 -->
The dimension equals the number of $m$-variate monomials of total degree at most $r$ with individual degree at most $q-1$. No simple closed form is known for all $q,m,r$; only special cases are described.

<a id="pdf-7251cb8e4bc5-p129-b001"></a>
<!-- pdf-source: page=129; block=1; confidence=0.95 -->
## 6.2 The low degree case

Considers $\mathrm{RM}(q,m,r)$ with $r < q$ (degree smaller than field size), the "low-degree" setting.

<a id="pdf-7251cb8e4bc5-p129-b002"></a>
<!-- pdf-source: page=129; block=2; confidence=0.90 -->
In the low-degree case the individual-degree constraint $\le q-1$ is automatically implied by $r \le q-1$, giving a closed-form dimension.

<a id="pdf-7251cb8e4bc5-p129-b003"></a>
<!-- pdf-source: page=129; block=3; confidence=0.95 -->
**Proposition 6.2.1.** The dimension of $\mathrm{RM}(q,m,r)$ equals $\binom{m+r}{r}$ when $r < q$.

<a id="pdf-7251cb8e4bc5-p129-b004"></a>
<!-- pdf-source: page=129; block=4; confidence=0.92 -->
**Proof.** The dimension equals $|D|$ where
$$D = \Big\{ (d_1,\ldots,d_m) \in \mathbb{Z}^m \mid d_i \ge 0 \ \forall i \in [m],\ \sum_{i=1}^m d_i \le r \Big\}, \quad (6.1)$$
since each $(d_1,\ldots,d_m) \in D$ gives a monomial $X_1^{d_1}\cdots X_m^{d_m}$ of degree at most $r$, and these are all such monomials. The closed form $\binom{m+r}{r}$ follows by a counting argument (Exercise 6.2). $\square$

<a id="pdf-7251cb8e4bc5-p129-b005"></a>
<!-- pdf-source: page=129; block=5; confidence=0.90 -->
Distance is analyzed via a bound on the number of zeroes of a multivariate polynomial; three versions appear in the chapter, the third subsuming the first (Lemma 6.2.2) and second (Lemma 6.3.1).

<a id="pdf-7251cb8e4bc5-p129-b006"></a>
<!-- pdf-source: page=129; block=6; confidence=0.95 -->
**Lemma 6.2.2 (Polynomial Distance Lemma, low-degree case).** Let $f \in \mathbb{F}_q[X_1,\ldots,X_m]$ be a non-zero polynomial with $\deg(f) \le r$. Then the fraction of zeroes of $f$ is at most $r/q$:
$$\frac{|\{a \in \mathbb{F}_q^m \mid f(a) = 0\}|}{q^m} \le \frac{r}{q}.$$

<a id="pdf-7251cb8e4bc5-p129-b007"></a>
<!-- pdf-source: page=129; block=7; confidence=0.92 -->
For $m=1$ this is the degree mantra (Proposition 5.1.5). For every $m \ge 1$ the lemma is tight (Exercise 6.3), though some polynomials do not attain it (Exercise 6.4).

<a id="pdf-7251cb8e4bc5-p129-b008"></a>
<!-- pdf-source: page=129; block=8; confidence=0.95 -->
**Proof of Lemma 6.2.2.** Equivalently, the probability that $f(a) = 0$ is at most $\deg(f)/q$ when $a = (a_1,\ldots,a_m)$ is chosen uniformly at random from $\mathbb{F}_q^m$. Proceed by induction on $m \ge 1$: the base case is the degree mantra (Proposition 5.1.5); the case $m > 1$ follows [continues on next page].

<a id="pdf-7251cb8e4bc5-p130-b001"></a>
<!-- pdf-source: page=130; block=1; confidence=0.95 -->
**Proof (continued).** Inductive step (assuming the lemma for $m-1$). Write $f$ as a polynomial in $X_m$ with coefficients in $\mathbb{F}_q[X_1,\dots,X_{m-1}]$:
$$f = f_0 X_m^0 + f_1 X_m^1 + \cdots + f_t X_m^t,$$
where $\deg(f_i) \le r - i$ and $t$ is the largest index with $f_t \ne 0$. Choose $a\in\mathbb{F}_q^m$ in two steps: pick $(a_1,\dots,a_{m-1})$ uniform from $\mathbb{F}_q^{m-1}$, then $a_m$ uniform from $\mathbb{F}_q$. Set
$$f^{(a_1,\dots,a_{m-1})}(X_m) = f_0(a_1,\dots,a_{m-1})X_m^0 + \cdots + f_t(a_1,\dots,a_{m-1})X_m^t.$$
Define events
$$E_1 = \{(a_1,\dots,a_m)\mid f_t(a_1,\dots,a_{m-1}) = 0\},$$
$$E_2 = \{(a_1,\dots,a_m)\mid f_t(a_1,\dots,a_{m-1}) \ne 0 \text{ and } f^{(a_1,\dots,a_{m-1})}(a_m) = 0\}.$$
By the inductive hypothesis, since $\deg(f_t)\le r-t$ and $f_t\ne 0$,
$$\Pr[E_1] \le \frac{r-t}{q}. \tag{6.2}$$
For each $(a_1,\dots,a_{m-1})$ with $f_t \ne 0$, the univariate $f^{(a_1,\dots,a_{m-1})}(X_m)$ is nonzero of degree $\le t$, so by the degree mantra it has at most $t$ roots; hence the probability over $a_m$ that it vanishes is $\le t/q$, giving
$$\Pr[E_2] \le \frac{t}{q}. \tag{6.3}$$
If neither $E_1$ nor $E_2$ occurs then $f(a)\ne 0$ (if $f(a)=0$ then either $f_t=0$, i.e. $E_1$, or $f_t\ne 0$ and $f^{(a_1,\dots,a_{m-1})}(a_m)=0$, i.e. $E_2$). Therefore, using the union bound (Proposition 3.1.5) and (6.2),(6.3),
$$\Pr_a[f(a)=0] \le \Pr[E_1\cup E_2] \le \Pr[E_1]+\Pr[E_2] \le \frac{r}{q}. \qquad\square$$

<a id="pdf-7251cb8e4bc5-p131-b001"></a>
<!-- pdf-source: page=131; block=1; confidence=0.97 -->
**Comparison with other codes.** Prose comparing the asymptotics of Reed–Muller codes with other code families.

<a id="pdf-7251cb8e4bc5-p131-b002"></a>
<!-- pdf-source: page=131; block=2; confidence=0.95 -->
Special cases: $m=1$, $r=k-1$ gives Reed–Solomon codes evaluated on all of $\mathbb{F}_q$ (Chapter 5); $m=k-1$, $r=1$, $q=2$ gives extended Hadamard codes (Exercise 5.9). Thus RM codes generalize known codes over both large and small alphabets. Taking $m$ constant keeps the alphabet small relative to block length $n$: for $m=2$, length $n$ over alphabet of size $\sqrt{n}$ with rate $\ge (1-\delta)^2/2$ for relative distance $\delta$; for general $m$, alphabet size $n^{1/m}$ and rate $\ge (1-\delta)^m/m!$ (Exercise 6.5). Hence for small $m$ and fixed $\delta<1$ there is $R>0$ giving codes of unbounded length $n$, alphabet $n^{1/m}$, rate $R$, distance $\delta$ — answering Question 6.0.1 affirmatively. Later (Chapter 7) alphabet size $q$ independent of $n$ with $R>0$, $\delta>0$ is achieved.

<a id="pdf-7251cb8e4bc5-p131-b003"></a>
<!-- pdf-source: page=131; block=3; confidence=0.97 -->
**6.3 The case of the binary field.** Fix alphabet size $q=2$ and vary $m$ and $r$.

<a id="pdf-7251cb8e4bc5-p131-b004"></a>
<!-- pdf-source: page=131; block=4; confidence=0.96 -->
**Lemma 6.3.1 (Polynomial distance, binary case).** Let $f$ be a nonzero polynomial in $\mathbb{F}_2[X_1,\dots,X_m]$ with $\deg_{X_i}(f)\le 1$ for every $i\in[m]$. Then
$$|\{a\in\mathbb{F}_2^m \mid f(a)\ne 0\}| \ge 2^{m-\deg(f)}.$$
(Proof deferred to Exercise 6.6; bound is tight, Exercise 6.7.)

<a id="pdf-7251cb8e4bc5-p131-b005"></a>
<!-- pdf-source: page=131; block=5; confidence=0.96 -->
**Proposition 6.3.2.** For any $r\le m$, the dimension of the Reed–Muller code $\mathrm{RM}(2,m,r)$ equals the number of subsets of $[m]$ of size at most $r$:
$$\sum_{i=0}^{r}\binom{m}{i}.$$

<a id="pdf-7251cb8e4bc5-p132-b001"></a>
<!-- pdf-source: page=132; block=1; confidence=0.97 -->
**Theorem 6.3.3.** For every $r\le m$, the Reed–Muller code $\mathrm{RM}(2,m,r)$ has block length $2^m$, dimension $\sum_{i=0}^{r}\binom{m}{i}$, and distance $2^{m-r}$. (Follows from Lemma 6.3.1 and Proposition 6.3.2.)

<a id="pdf-7251cb8e4bc5-p132-b002"></a>
<!-- pdf-source: page=132; block=2; confidence=0.95 -->
Fixing $\tau>0$, setting $r=\tau\cdot m$ and letting $m\to\infty$ yields codes of block length $n$ (infinitely many $n$) with rate roughly $n^{H(\tau)-1}$ and distance $n^{-\tau}$ (Exercise 6.8). Both rate and distance tend to zero as small polynomials in $n$, but the alphabet is constant-sized.

<a id="pdf-7251cb8e4bc5-p132-b003"></a>
<!-- pdf-source: page=132; block=3; confidence=0.95 -->
**6.4 The general case.** General $q$ with $r$ possibly larger than $q-1$; analyze dimension and distance. Distance has a clean expression (given first); dimension has no simple exact expression, so lower bounds (often asymptotically tight) are given. **6.4.1 The general case: Distance.**

<a id="pdf-7251cb8e4bc5-p132-b004"></a>
<!-- pdf-source: page=132; block=4; confidence=0.96 -->
**Lemma 6.4.1 (Polynomial distance, general case).** Let $f$ be a nonzero polynomial in $\mathbb{F}_q[X_1,\dots,X_m]$ with $\deg_{X_i}(f)\le q-1$ for every $i\in[m]$ and $\deg(f)\le r$. Let $s,t$ be the unique nonnegative integers with $t\le q-2$ and
$$s(q-1)+t = r.$$
Then
$$|\{a\in\mathbb{F}_q^m \mid f(a)\ne 0\}| \ge (q-t)\cdot q^{m-s-1} \ge q^{m-\frac{r}{q-1}}.$$
Hence $\mathrm{RM}(q,m,r)$ has distance at least $q^{m-\frac{r}{q-1}}$.

<a id="pdf-7251cb8e4bc5-p132-b005"></a>
<!-- pdf-source: page=132; block=5; confidence=0.90 -->
Lemma 6.4.1 generalizes Lemma 6.2.2 (case $s=0$) and Lemma 6.3.1 (case $q=2$, $s=r-1$, $t=1$). The second lower bound shows that the probability $f$ is nonzero at a uniform point of $\mathbb{F}_q^m$ is at least $q^{-r/(q-1)}$. The lemma is tight for all parameter settings (Exercise 6.9).

<a id="pdf-7251cb8e4bc5-p132-b006"></a>
<!-- pdf-source: page=132; block=6; confidence=0.93 -->
**Proof of Lemma 6.4.1.** Similar to the proof of Lemma 6.2.2, additionally exploiting that the degree in each single variable is at most $q-1$, and requiring some simple inequalities. As before, it is shown that for a random $a=(a_1,\dots,a_m)\in\mathbb{F}_q^m$, the probability that $f(a)\ne 0$ is at least
$$(q-t)\cdot q^{-(s+1)}. \tag{6.4}$$
(Proof continues beyond the supplied pages.)

<a id="pdf-7251cb8e4bc5-p133-b001"></a>
<!-- pdf-source: page=133; block=1; confidence=0.92 -->
**Proof (continued).** Strategy: track the good event (polynomial nonzero) rather than the bad event. Induction on m.

_Base case m=1._ By the degree mantra (Proposition 5.1.5), $\Pr[f(a_1)\neq 0]\ge \frac{q-r}{q}$. If $r<q-1$ then $s=0$, $t=r$, and (6.4) gives $(q-t)\cdot q^{-1}=\frac{q-r}{q}\le \Pr[f(a_1)\neq0]$. If $r=q-1$ then $s=1$, $t=0$, and (6.4) equals $q\cdot q^{-2}=\frac{q-(q-1)}{q}\le\Pr[f(a_1)\neq0]$.

_Inductive step._ Assume the hypothesis for $(m-1)$-variate polynomials. Write $f=\sum_{i=0}^{b} f_i X_m^{i}$ with $f_i\in\mathbb{F}_q[X_1,\dots,X_{m-1}]$, $f_b\neq0$, $0\le b\le q-1$, $\deg(f_b)\le r-b$. Let $E=\{(a_1,\dots,a_m)\mid f(a_1,\dots,a_m)\neq0\}$ and $E^1=\{(a_1,\dots,a_{m-1})\mid f_b(a_1,\dots,a_{m-1})\neq0\}$.

Bound on $\Pr[E\mid E^1]$: fix $a_1,\dots,a_{m-1}$ with $f_b\neq0$ and set $P(Z)=\sum_{i=0}^{b} f_i(a_1,\dots,a_{m-1})Z^{i}$, a nonzero polynomial of degree $b$. Then $\Pr_{a_m}[P(a_m)\neq0]\ge\frac{q-b}{q}$ (degree mantra: $\le b$ roots), giving $\Pr[E\mid E^1]\ge 1-\frac{b}{q}$.

Then $\Pr[E]\ge\Pr[E\text{ and }E^1]=\Pr[E^1]\cdot\Pr[E\mid E^1]$, reducing the task to bounding $\Pr[E^1]$.

<a id="pdf-7251cb8e4bc5-p134-b001"></a>
<!-- pdf-source: page=134; block=1; confidence=0.92 -->
**Proof (continued).** With $\deg(f_b)\le r-b$, write $r-b=s'(q-1)+t'$, $s',t'\ge0$, $t'\le q-2$. By induction, $\Pr[E^1]=\Pr[f_b(a_1,\dots,a_{m-1})\neq0]\ge (q-t')\cdot q^{-(s'+1)}$.

Combining, $\Pr[E]\ge\Pr[E\mid E^1]\cdot\Pr[E^1]\ge \frac{q-b}{q}\cdot(q-t')\cdot q^{-(s'+1)}$.

It remains to show this is $\ge (q-t)\cdot q^{-(s+1)}$, done in Claim 6.4.2 using $t,t'\le q-2$, $b\le q-1$, $r=s(q-1)+t$, $r-b=s'(q-1)+t'$. Claim 6.4.3 then gives $(q-t)\cdot q^{-(s+1)}\ge q^{-r/(q-1)}$, completing the lemma.

<a id="pdf-7251cb8e4bc5-p134-b002"></a>
<!-- pdf-source: page=134; block=2; confidence=0.97 -->
**Claim 6.4.2.** If $q,r,s,t,s',t',b$ are non-negative integers with $r=s(q-1)+t$, $r-b=s'(q-1)+t'$, $t,t'\le q-2$ and $b\le q-1$, then
$$\frac{q-b}{q}\cdot(q-t')\cdot q^{-(s'+1)}\ge (q-t)\cdot q^{-(s+1)}.$$

<a id="pdf-7251cb8e4bc5-p134-b003"></a>
<!-- pdf-source: page=134; block=3; confidence=0.96 -->
**Proof.** $s,s'$ are the quotients of $r$ and $r-b$ divided by $q-1$; since $0\le b\le q-1$, either $s'=s$ or $s'=s-1$.

_Case $s=s'$:_ then $t=t'+b$, and it suffices to show $\frac{q-b}{q}(q-t')\ge q-(t'+b)$, i.e. $(q-b)(q-t')\ge q(q-(t'+b))$. This holds because $(q-b)(q-t')=q^2-(b+t')q+bt'=q(q-(b+t'))+bt'\ge q(q-(b+t'))$ since $bt'\ge0$.

_Case $s=s'+1$:_ then $t+q-1=t'+b$, and it suffices to show $\frac{q-b}{q}(q-t')\,q\ge (q-t)=2q-(t'+b+1)$. Put $\alpha=q-b$, $\beta=q-t'$; the left side is $\alpha\beta$, the right is $\alpha+\beta-1$. Since $b,t'\le q-1$, $\alpha,\beta\ge1$, and $\alpha\beta=\alpha+\alpha(\beta-1)\ge\alpha+\beta-1$ because $\alpha(\beta-1)\ge\beta-1$. Both cases give the claim.

<a id="pdf-7251cb8e4bc5-p135-b001"></a>
<!-- pdf-source: page=135; block=1; confidence=0.97 -->
**Claim 6.4.3.** Let $q,r,s,t$ be non-negative reals with $q\ge2$, $r=s(q-1)+t$ and $t\le q-2$. Then
$$(q-t)\cdot q^{-(s+1)}\ge q^{-r/(q-1)}.$$
(Remark: the proof is included only for completeness and may be skipped.)

<a id="pdf-7251cb8e4bc5-p135-b002"></a>
<!-- pdf-source: page=135; block=2; confidence=0.95 -->
**Proof of Claim 6.4.3.** Substitute $r=s(q-1)+t$: suffices to prove $(q-t)\cdot q^{-(s+1)}\ge q^{-(s(q-1)+t)/(q-1)}=q^{-s}\cdot q^{-t/(q-1)}$. Cancel $q^{-s}$: suffices $\frac{q-t}{q}\ge q^{-t/(q-1)}$.

Let $f_q(t)=\frac{t}{q}+q^{-t/(q-1)}-1$; the goal is $f_q(t)\le0$ for $0\le t\le q-2$. Derivatives: $f_q'(t)=\frac1q-\frac{\ln q}{q-1}q^{-t/(q-1)}$ and $f_q''(t)=\left(\frac{\ln q}{q-1}\right)^2 q^{-t/(q-1)}>0$, so $f_q$ is convex and maximized at an endpoint of $[0,q-2]$. Since $f_q(0)=0\le0$, it suffices to show $f_q(q-2)=q^{-(q-2)/(q-1)}-\frac{2}{q}\le0$.

Multiplying by $q$, suffices $q^{1/(q-1)}\le2$, equivalently $q\le2^{q-1}$ for $q\ge2$. This follows from Bernoulli's inequality (Lemma A.1.4) $1+kx\le(1+x)^k$ ($x\ge-1$, $k\ge1$) with $x=1$, $k=q-1$.

<a id="pdf-7251cb8e4bc5-p135-b003"></a>
<!-- pdf-source: page=135; block=3; confidence=0.98 -->
## 6.4.2 The general case: Dimension

<a id="pdf-7251cb8e4bc5-p135-b004"></a>
<!-- pdf-source: page=135; block=4; confidence=0.97 -->
**Definition.** For integers $q,m,r$,
$$S_{q,m,r}=\Big\{\,d=(d_1,\dots,d_m)\in\mathbb{Z}^m \;\Big|\; 0\le d_i\le q-1 \text{ for all } i\in[m],\ \sum_{i=1}^{m} d_i\le r\,\Big\} \tag{6.5}$$
and $K_{q,m,r}=|S_{q,m,r}|$. An almost tautological proposition about these quantities follows.

<a id="pdf-7251cb8e4bc5-p136-b001"></a>
<!-- pdf-source: page=136; block=1; confidence=0.97 -->
**Proposition 6.4.4.** For every prime power $q$ and integers $m \ge 1$, $r \ge 0$, the dimension of $\mathrm{RM}(q,m,r)$ equals $K_{q,m,r}$.

<a id="pdf-7251cb8e4bc5-p136-b002"></a>
<!-- pdf-source: page=136; block=2; confidence=0.95 -->
**Proof.** For each $d=(d_1,\dots,d_m)\in S_{q,m,r}$ the monomial $X^d=X_1^{d_1}\cdots X_m^{d_m}$ has total degree $\le r$ and individual degree $\le q-1$; their evaluations form a basis of $\mathrm{RM}(q,m,r)$. (Exercise 6.10.) $\square$

<a id="pdf-7251cb8e4bc5-p136-b003"></a>
<!-- pdf-source: page=136; block=3; confidence=0.90 -->
Bridge: the definition of $K_{q,m,r}$ gives no direct sense of its growth, so the next proposition supplies a lower bound $K^-_{q,m,r}$ and upper bound $K^+_{q,m,r}$ given by simple expressions and within polynomial factors of each other for all $q,m,r$.

<a id="pdf-7251cb8e4bc5-p136-b004"></a>
<!-- pdf-source: page=136; block=4; confidence=0.90 -->
**Proposition 6.4.5.** For integers $q\ge 2$, $m\ge 1$, $r\ge 0$, define
$$K^+_{q,m,r}\triangleq\min\left\{q^m,\ \binom{m+r}{r}\right\},$$
$$K^-_{q,m,r}\triangleq\begin{cases}\max\left\{\tfrac{q^m}{2},\ q^m-K^+_{q,m,(q-1)m-r}\right\}&\text{if } r\ge (q-1)m/2,\\[4pt]\max\left\{\binom{m}{r},\ \tfrac{1}{2}\left(\left\lfloor\tfrac{2r+m}{m}\right\rfloor\right)^m\right\}&\text{if } r< (q-1)m/2.\end{cases}$$
Then there are universal constants $c_1,c_2$ ($c_1<3.1$ and $c_2<8.2$ suffice) such that
$$K^-_{q,m,r}\le K_{q,m,r}\le K^+_{q,m,r}\le c_1\cdot (K^-_{q,m,r})^{c_2}.$$
(The proof establishes $c_2=1+\log_2(3e/2)<3.1$ and $c_1=2^{c_2}<8.2$.)

<a id="pdf-7251cb8e4bc5-p136-b005"></a>
<!-- pdf-source: page=136; block=5; confidence=0.86 -->
**Proof.** Inequalities proved in order of increasing difficulty; uses that $K_{q,m,r}$ is monotone non-decreasing in $q$ and $r$ (Exercise 6.11).

Upper bound $K_{q,m,r}\le K^+_{q,m,r}$: ignoring the total-degree restriction, $K_{q,m,r}\le K_{q,m,(q-1)m}=q^m$; ignoring the individual-degree restriction, $K_{q,m,r}\le K_{r,m,r}=\binom{m+r}{r}$.

Lower bound $K^-_{q,m,r}\le K_{q,m,r}$, case $r\ge (q-1)m/2$ (symmetry): the map $d=(d_1,\dots,d_m)\mapsto (q-1-d_1,\dots,q-1-d_m)$ on $\{0,\dots,q-1\}^m$ is a bijection sending vectors with $\sum_i d_i>r$ to vectors with $\sum_i d_i<(q-1)m-r$; hence every $d$ lies in $S_{q,m,r}$ or $S_{q,m,(q-1)m-r}$, giving $K_{q,m,r}=q^m-K_{q,m,(q-1)m-r}$.

<a id="pdf-7251cb8e4bc5-p137-b001"></a>
<!-- pdf-source: page=137; block=1; confidence=0.85 -->
Since $r\ge (q-1)m/2$, $(q-1)m-r\le r$, so $K_{q,m,r}\ge K_{q,m,(q-1)m-r}$, hence $K_{q,m,r}\ge q^m/2$; this gives $K_{q,m,r}\ge K^-_{q,m,r}$ when $r\ge (q-1)m/2$.

Case $r<(q-1)m/2$: set $q'=\lfloor(2r+m)/m\rfloor$; since $r\ge (q'-1)m/2$, $K_{q,m,r}\ge K_{q',m,r}\ge (q')^m/2=\tfrac12\left(\lfloor(2r+m)/m\rfloor\right)^m$. Also $K_{q,m,r}\ge K_{2,m,r}=\sum_{i=0}^r\binom{m}{i}\ge\binom{m}{r}$, establishing $K_{q,m,r}\ge K^-_{q,m,r}$ here.

Upper vs lower, $K^+\le c_1(K^-)^{c_2}$: if $r\ge (q-1)m/2$ then $q^m/2\le K^-\le K^+\le q^m$, so $K^+\le 2K^-$. Case $r<m/2$: $K^-\ge\binom{m}{r}\ge (m/r)^r\ge 2^r$; and $\binom{m+r}{r}\le\left(\tfrac{e(m+r)}{r}\right)^r\le\left(\tfrac{e\cdot(3/2)m}{r}\right)^r=\left(\tfrac{3e}{2}\right)^r(m/r)^r$. From $2^r\le K^-$, $(3e/2)^r\le (K^-)^{\log_2(3e/2)}$; combined with $(m/r)^r\le K^-$, $K^+\le (K^-)^{1+\log_2(3e/2)}$. Case $m/2\le r<(q-1)m/2$: $\lfloor(2r+m)/m\rfloor=1+\lfloor 2r/m\rfloor\ge 1+r/m=(m+r)/m$.

<a id="pdf-7251cb8e4bc5-p138-b001"></a>
<!-- pdf-source: page=138; block=1; confidence=0.88 -->
Thus $K^-_{q,m,r}\ge\tfrac12\left(\lfloor(2r+m)/m\rfloor\right)^m\ge\tfrac12\left(\tfrac{m+r}{m}\right)^m\ge\tfrac12\left(\tfrac32\right)^m$. On the other hand $K^+_{q,m,r}\le\binom{m+r}{m}\le\left(\tfrac{e(m+r)}{m}\right)^m=e^m\left(\tfrac{m+r}{m}\right)^m$. Again $\left(\tfrac{m+r}{m}\right)^m\le 2K^-_{q,m,r}$ and $e^m\le (2K^-_{q,m,r})^{\log_2(3e/2)}$, so $K^+_{q,m,r}\le (2K^-_{q,m,r})^{1+\log_2(3e/2)}$. In all cases $K^+_{q,m,r}\le c_1(K^-_{q,m,r})^{c_2}$ with $c_2=1+\log_2(3e/2)<3.1$ and $c_1=2^{c_2}<8.2$. $\square$

<a id="pdf-7251cb8e4bc5-p138-b002"></a>
<!-- pdf-source: page=138; block=2; confidence=0.92 -->
**Example 6.4.6** (constant alphabet size and relative distance). Fix $q$ and $r<q-1$, let $m\to\infty$. Then $\mathrm{RM}(q,m,r)$ are $[N,K,D]_q$ codes with $N=q^m$, $D=\delta N$ for $\delta=1-r/q$, and $K\ge\binom{m}{r}\ge (m/r)^r=(\log_q N/r)^r$ — dimension growing as an arbitrary polynomial in $\log N$.

<a id="pdf-7251cb8e4bc5-p138-b003"></a>
<!-- pdf-source: page=138; block=3; confidence=0.92 -->
**Example 6.4.7** (binary RM codes, rate near 1, constant absolute distance). Fix $q=2$ and $d$, let $m\to\infty$. Then $\mathrm{RM}(2,m,m-d)$ are $[N,K,D]_2$ codes with $N=2^m$, $D=2^d$, and $K\ge N-\binom{\log_2 N+d}{d}\ge N-(\log_2 N)^d$; rate $\to 1$ as $N\to\infty$. (Exercise 6.12.)

<a id="pdf-7251cb8e4bc5-p138-b004"></a>
<!-- pdf-source: page=138; block=4; confidence=0.95 -->
**Example 6.4.8** (constant rate and relative distance over polynomially small alphabets). Given $\varepsilon>0$, set $m=\lceil 1/\varepsilon\rceil$ and let $q\to\infty$ with $r=q/2$. Then $\mathrm{RM}(q,m,r)$ are $[N,K,D]_q$ codes with $N=q^m$, $D=N/2$, and $K\ge\tfrac12\left(\tfrac{q+m}{m}\right)^m\ge\tfrac{1}{2m^m}N$. In terms of $N,\varepsilon$: length $N$, dimension $\Omega(\varepsilon^{1/\varepsilon})\cdot N$, relative distance $1/2$, alphabet size $N^\varepsilon$.

<a id="pdf-7251cb8e4bc5-p139-b001"></a>
<!-- pdf-source: page=139; block=1; confidence=0.90 -->
Notes two further RM-code parameter regimes: constant rate 1/2 (cf. Exercise 6.13), and a regime useful in theoretical CS where the alphabet size grows very slowly with N while the code keeps fixed relative distance and dimension polynomially related to block length.

<a id="pdf-7251cb8e4bc5-p139-b002"></a>
<!-- pdf-source: page=139; block=2; confidence=0.95 -->
**Example 6.4.9** (RM codes over polylogarithmic alphabets with polynomial dimension). Given $0<\varepsilon<1$, let $q\to\infty$, $r=q/2$, $m=q^{\varepsilon}$. Then $\mathrm{RM}(q,m,r)$ is an $[N,K,D]_q$ code with $N=q^m$, $D=N/2$, and
$$K\ge \tfrac12\left(\tfrac{q+m}{m}\right)^{m}\ge \tfrac12\left(q^{1-\varepsilon}\right)^{m}=\tfrac12\cdot N^{1-\varepsilon}.$$
In terms of $N$ and $\varepsilon$: length $N$, dimension $\Omega(N^{1-\varepsilon})$, relative distance $1/2$, alphabet size $(\log N)^{1/\varepsilon}$ (bound on $q$: Exercise 6.14).

<a id="pdf-7251cb8e4bc5-p139-b003"></a>
<!-- pdf-source: page=139; block=3; confidence=0.99 -->
## 6.5 Exercises

<a id="pdf-7251cb8e4bc5-p139-b004"></a>
<!-- pdf-source: page=139; block=4; confidence=0.98 -->
**Exercise 6.1.** Prove that any $\mathrm{RM}(q,m,r)$ is a linear code.

<a id="pdf-7251cb8e4bc5-p139-b005"></a>
<!-- pdf-source: page=139; block=5; confidence=0.97 -->
**Exercise 6.2.** Prove that for $D$ defined in (6.1), $|D|=\binom{m+r}{r}$.

<a id="pdf-7251cb8e4bc5-p139-b006"></a>
<!-- pdf-source: page=139; block=6; confidence=0.97 -->
**Exercise 6.3.** Show Lemma 6.2.2 is tight: for every prime power $q$ and integers $m\ge1$, $1\le r\le q-1$, there exists a polynomial with exactly $r\cdot q^{m-1}$ roots.

<a id="pdf-7251cb8e4bc5-p139-b007"></a>
<!-- pdf-source: page=139; block=7; confidence=0.96 -->
**Exercise 6.4.** Show Lemma 6.2.2 is not tight for most polynomials: for every prime power $q$ and integers $m\ge1$, $1\le r\le q-1$, a random polynomial in $\mathbb{F}_q[X_1,\dots,X_m]$ of degree $r$ has $q^{m-1}$ expected number of roots.

<a id="pdf-7251cb8e4bc5-p139-b008"></a>
<!-- pdf-source: page=139; block=8; confidence=0.95 -->
**Exercise 6.5.** Show the Reed–Muller codes of Section 6.2 give codes of relative distance $\delta$ (any $0<\delta<1$) and block length $n$ with alphabet size $\sqrt[m]{n}$ and rate at least $\dfrac{(1-\delta)^m}{m!}$.

<a id="pdf-7251cb8e4bc5-p139-b009"></a>
<!-- pdf-source: page=139; block=9; confidence=0.98 -->
**Exercise 6.6.** Prove Lemma 6.3.1.

<a id="pdf-7251cb8e4bc5-p139-b010"></a>
<!-- pdf-source: page=139; block=10; confidence=0.98 -->
**Exercise 6.7.** Prove that the lower bound in Lemma 6.3.1 is tight.

<a id="pdf-7251cb8e4bc5-p139-b011"></a>
<!-- pdf-source: page=139; block=11; confidence=0.95 -->
**Exercise 6.8.** Show there exists a binary RM code with block length $n$, rate $n^{H(\tau)-1}$, and relative distance $n^{-\tau}$ for any $0<\tau<1/2$.

<a id="pdf-7251cb8e4bc5-p140-b001"></a>
<!-- pdf-source: page=140; block=1; confidence=0.97 -->
**Exercise 6.9.** Prove the (first) lower bound in Lemma 6.4.1 is tight for all settings of the parameters.

<a id="pdf-7251cb8e4bc5-p140-b002"></a>
<!-- pdf-source: page=140; block=2; confidence=0.95 -->
**Exercise 6.10.** Prove that the evaluations of $X^d$ for every $d\in S_{q,m,r}$ (as in (6.5)) form a basis for $\mathrm{RM}(q,m,r)$.

<a id="pdf-7251cb8e4bc5-p140-b003"></a>
<!-- pdf-source: page=140; block=3; confidence=0.96 -->
**Exercise 6.11.** Prove that $K_{q,m,r}$ is monotone non-decreasing in $q$ as well as in $r$ (other parameters fixed).

<a id="pdf-7251cb8e4bc5-p140-b004"></a>
<!-- pdf-source: page=140; block=4; confidence=0.97 -->
**Exercise 6.12.** Prove the claimed bound on $K$ in Example 6.4.7.

<a id="pdf-7251cb8e4bc5-p140-b005"></a>
<!-- pdf-source: page=140; block=5; confidence=0.96 -->
**Exercise 6.13.** Determine the smallest alphabet $q$ for which an RM code has (absolute) distance that goes to infinity with the block length; determine an asymptotically tight bound on the distance as a function of the block length.

<a id="pdf-7251cb8e4bc5-p140-b006"></a>
<!-- pdf-source: page=140; block=6; confidence=0.97 -->
**Exercise 6.14.** Prove the claimed bound on $q$ in Example 6.4.9.

<a id="pdf-7251cb8e4bc5-p140-b007"></a>
<!-- pdf-source: page=140; block=7; confidence=0.85 -->
**Exercise 6.15.** Show the dual of Reed–Muller codes are themselves Reed–Muller codes (different degree), in sub-problems:
1. For $1\le j\le q-1$: $\sum_{\alpha\in\mathbb{F}_q}\alpha^{j}\ne 0$ iff $j=q-1$ (Hint: Exercise 2.3).
2. For $m\ge1$ and $1\le j_1,\dots,j_m\le q-1$: $\sum_{(c_1,\dots,c_m)\in\mathbb{F}_q^m}\prod_{i=1}^m c_i^{j_i}=0$ iff $j_1=\cdots=j_m=q-1$ (condition direction uncertain — see ambiguities).
3. Using the above, for $0\le r<(q-1)-s$: $\mathrm{RM}(q,m,r)^{\perp}=\mathrm{RM}(q,m,\,m(q-1)-r-1)$.

<a id="pdf-7251cb8e4bc5-p141-b001"></a>
<!-- pdf-source: page=141; block=1; confidence=0.99 -->
## 6.6 Bibliographic Notes

<a id="pdf-7251cb8e4bc5-p141-b002"></a>
<!-- pdf-source: page=141; block=2; confidence=0.95 -->
The name comes from the first two papers: the binary version was invented by Muller [55], and Reed [60] gave a non-trivially fast decoder — the first polynomial-time decoder correcting errors up to half the distance where brute-force decoders take super-polynomial time. The polynomial distance lemmas (Lemmas 6.3.1, 6.2.2, 6.4.1) date back at least to Ore [56], with versions in Muller [55], Schwartz [64], Zippel [76], and DeMillo–Lipton [16].

<a id="pdf-7251cb8e4bc5-p143-b001"></a>
<!-- pdf-source: page=143; block=1; confidence=0.98 -->
# Chapter 7 — From Large to Small Alphabets: Code Concatenation

<a id="pdf-7251cb8e4bc5-p143-b002"></a>
<!-- pdf-source: page=143; block=2; confidence=0.90 -->
Motivation: build an explicit asymptotically good binary code (rate $R>0$, relative distance $\delta>0$). Two explicitness levels are used: a linear code is *explicit* if its generator matrix is constructible in polynomial time, and *strongly explicit* if each generator-matrix entry is computable in poly-logarithmic time. The chapter seeks asymptotically good binary codes for both, via a new tool, *code concatenation*.

<a id="pdf-7251cb8e4bc5-p143-b003"></a>
<!-- pdf-source: page=143; block=3; confidence=0.92 -->
Summary of prior explicit binary codes (block length $n$):

- **Hamming:** $R = 1 - O(\log n / n)$, $\delta = O(1/n)$.
- **Hadamard:** $R = O(\log n / n)$, $\delta = 1/2$.

Each optimizes one parameter at the expense of the other. **Binary-RS:** from an $[n,k,n-k+1]_q$ Reed–Solomon code, write each $\mathbb{F}_q$ element as a $\lceil \log q\rceil$-bit string, mapping $\mathbb{F}_q^k \to \{0,1\}^{n\lceil\log q\rceil}$ with distance $\ge n-k+1$. When $q = n = 2^s$ this becomes an $\mathbb{F}_2$-linear $[n\log n,\ k\log n,\ n-k+1]_2$ code. Taking $k=n/2$ gives rate $1/2$ and relative distance $\Omega(1/\log n)$ — closer to asymptotically good but still short.

<a id="pdf-7251cb8e4bc5-p143-b004"></a>
<!-- pdf-source: page=143; block=4; confidence=0.93 -->
Footnote 1: one way to state that a rate-$R$, distance-$\delta$ code is asymptotically good is $R\delta = \Omega(1)$. Values: Hamming $R\delta = \Theta(1/n)$; Hadamard $R\delta = \Theta(\log n / n)$; binary-RS $R\delta = \Theta(1/\log n)$ (best of the three).

<a id="pdf-7251cb8e4bc5-p144-b001"></a>
<!-- pdf-source: page=144; block=1; confidence=0.85 -->
**Table 7.1** (strongly explicit binary codes seen so far):

| Code | $R$ | $\delta$ | $R\cdot\delta$ |
|------|-----|----------|----------------|
| Hamming | $1 - O(\tfrac{\log n}{n})$ | $O(\tfrac{1}{n})$ | $O(\tfrac{1}{n})$ |
| Hadamard | $O(\tfrac{\log n}{n})$ | $\tfrac12$ | $O(\tfrac{\log n}{n})$ |
| Binary-RS | $\tfrac12$ | $O(\tfrac{1}{\log n})$ | $O(\tfrac{1}{\log n})$ |

<a id="pdf-7251cb8e4bc5-p144-b002"></a>
<!-- pdf-source: page=144; block=2; confidence=0.85 -->
The weak distance of binary-RS arises because bit representations of two distinct $\mathbb{F}_{2^s}$ symbols may differ in only one bit; hence $x,y \in \mathbb{F}_{q^s}$ (with $q=2^s$) differing in $d$ positions can have binary images in $\mathbb{F}_2^{ns}$ differing in only $d$ positions.

<a id="pdf-7251cb8e4bc5-p144-b003"></a>
<!-- pdf-source: page=144; block=3; confidence=0.87 -->
Ideal fix: represent each element of $\mathbb{F}_{2^s}$ by $O(s)$ bits so that distinct elements' representations differ in $\Omega(s)$ coordinates — exactly an asymptotically good binary code. Key observation of progress: the *inner code* representing $\mathbb{F}_{2^s}$ elements need not be efficiently explicit. The *outer code* has length $2^s$ with $\mathrm{poly}(2^s)$ construction time; the inner code has messages of length $s$, also affording $\mathrm{poly}(2^s)$ time to build its generator matrix — a much weaker requirement (allowing e.g. brute-force search), which is what enables the constructions of this chapter.

<a id="pdf-7251cb8e4bc5-p144-b004"></a>
<!-- pdf-source: page=144; block=4; confidence=0.97 -->
## 7.1 Code Concatenation: The basic idea

<a id="pdf-7251cb8e4bc5-p144-b005"></a>
<!-- pdf-source: page=144; block=5; confidence=0.90 -->
**Definition (basic concatenated code).** Built from an outer code $C_{\mathrm{out}}$ and an inner code $C_{\mathrm{in}}$: first encode the message with $C_{\mathrm{out}}$ to obtain a codeword $(c_0,\dots,c_{N-1})$, then encode each symbol $c_i$ with $C_{\mathrm{in}}$. (Illustrated in Figure 7.1.)

<a id="pdf-7251cb8e4bc5-p144-b006"></a>
<!-- pdf-source: page=144; block=6; confidence=0.90 -->
Footnote 2: unlike string concatenation, code concatenation does not join codewords as strings; it is a recursive construction where the outer code reduces the block length required from the inner code.

<a id="pdf-7251cb8e4bc5-p145-b001"></a>
<!-- pdf-source: page=145; block=1; confidence=0.90 -->
Figure 7.1: illustration of the concatenated code $C_{out} \circ C_{in}$.

<a id="pdf-7251cb8e4bc5-p145-b002"></a>
<!-- pdf-source: page=145; block=2; confidence=0.95 -->
**Definition (concatenated code).** For $q \ge 2$, $k \ge 1$, and $Q = q^k$, take an outer code $C_{out}:[Q]^K \to [Q]^N$ and inner code $C_{in}:[q]^k \to [q]^n$. The alphabet size of $C_{out}$ equals the number of messages of $C_{in}$, giving a bijection $[Q=q^k] \leftrightarrow [q]^k$, so $C_{in}$ can encode each symbol of a $C_{out}$ codeword. For $m=(m_1,\dots,m_K)\in[Q]^K$, define $C_{out}\circ C_{in}:[q]^{kK}\to[q]^{nN}$ by $C_{out}\circ C_{in}(m) = (C_{in}(C_{out}(m)_1),\dots,C_{in}(C_{out}(m)_N))$, where $C_{out}(m)=(C_{out}(m)_1,\dots,C_{out}(m)_N)$.

<a id="pdf-7251cb8e4bc5-p145-b003"></a>
<!-- pdf-source: page=145; block=3; confidence=0.97 -->
**Theorem 7.1.1.** If $C_{out}$ is an $(N,K,D)_{q^k}$ code and $C_{in}$ is an $(n,k,d)_q$ code, then $C_{out}\circ C_{in}$ is an $(nN,kK,dD)_q$ code. In particular, if $C_{out}$ has rate $R$ and relative distance $\delta_{out}$, and $C_{in}$ has rate $r$ and relative distance $\delta_{in}$, then $C_{out}\circ C_{in}$ has rate $Rr$ and relative distance $\delta_{out}\cdot\delta_{in}$.

<a id="pdf-7251cb8e4bc5-p145-b004"></a>
<!-- pdf-source: page=145; block=4; confidence=0.93 -->
**Proof.** The first claim implies the second (rate and relative distance). Block length, dimension, and alphabet follow from the definition. To show distance $\ge dD$: take arbitrary $m_1 \ne m_2 \in [Q]^K$; since $C_{out}$ has distance $D$, $\Delta(C_{out}(m_1),C_{out}(m_2)) \ge D$. (Footnote: the dimension $kK$ requires distinct codewords, which follows from distance $dD \ge 1$ for $d,D \ge 1$.)

<a id="pdf-7251cb8e4bc5-p146-b001"></a>
<!-- pdf-source: page=146; block=1; confidence=0.95 -->
**Proof (cont.).** Define $S = \{i\in[N] \mid C_{out}(m_1)_i \ne C_{out}(m_2)_i\}$; the distance bound gives $|S| \ge D$ (7.1). For each $i\in S$, since $C_{in}$ has distance $d$, $\Delta(C_{in}(C_{out}(m_1)_i), C_{in}(C_{out}(m_2)_i)) \ge d$ (7.2). With at least $D$ such positions, $\Delta(C_{out}\circ C_{in}(m_1), C_{out}\circ C_{in}(m_2)) \ge dD$. Since $m_1,m_2$ were arbitrary, the proof is complete. $\square$

<a id="pdf-7251cb8e4bc5-p146-b002"></a>
<!-- pdf-source: page=146; block=2; confidence=0.90 -->
If $C_{in}$ and $C_{out}$ are linear, then so is $C_{out}\circ C_{in}$ (provable by constructing a generator matrix from those of $C_{in}$ and $C_{out}$); left as an exercise.

<a id="pdf-7251cb8e4bc5-p146-b003"></a>
<!-- pdf-source: page=146; block=3; confidence=0.95 -->
**7.2 Zyablov Bound** — instantiate outer and inner codes in Theorem 7.1.1 to get a rate lower bound given relative distance.

<a id="pdf-7251cb8e4bc5-p146-b004"></a>
<!-- pdf-source: page=146; block=4; confidence=0.95 -->
Instantiate $C_{out}$ as a Reed–Solomon code (Ch. 5), optimal since it meets the Singleton bound 4.3.1; assume $C_{out}$ has rate $R$ so $\delta_{out} \ge 1-R$. For $C_{out}\circ C_{in}$ to be asymptotically good, $C_{in}$ needs $r>0$ and $\delta_{in}>0$. Fix $\varepsilon>0$; suppose $C_{in}$ meets the GV bound (Theorem 4.2.1) with rate $r$, so $\delta_{in} \ge H_q^{-1}(1-r) - \varepsilon$. By Theorem 7.1.1, $C_{out}\circ C_{in}$ has rate $rR$ and relative distance $\delta = (1-R)\,(H_q^{-1}(1-r) - \varepsilon)$. Solving for $R$: $R = 1 - \dfrac{\delta}{H_q^{-1}(1-r) - \varepsilon}$.

<a id="pdf-7251cb8e4bc5-p147-b001"></a>
<!-- pdf-source: page=147; block=1; confidence=0.90 -->
Figure 7.2: plot of the Zyablov bound for binary codes, with the GV bound shown for comparison.

<a id="pdf-7251cb8e4bc5-p147-b002"></a>
<!-- pdf-source: page=147; block=2; confidence=0.95 -->
**Zyablov bound.** Optimizing over $r$, the concatenated code rate satisfies $$R \ge \lim_{\varepsilon\to 0} \max_{0<r<1-H_q(\delta+\varepsilon)} \left( r\left(1 - \frac{\delta}{H_q^{-1}(1-r) - \varepsilon}\right)\right),$$ where the constraint $r < 1 - H_q(\delta+\varepsilon)$ ensures $R>0$.

<a id="pdf-7251cb8e4bc5-p147-b003"></a>
<!-- pdf-source: page=147; block=3; confidence=0.90 -->
For $\delta = \tfrac12 - \gamma$ with $\gamma\to 0$, the Zyablov bound gives $R \ge \Omega(\gamma^3)$ (vs. $\Omega(\gamma^2)$ for the GV bound); proof left as Exercise 7.3. The bound implies that for every $\delta>0$ there is a concatenated code with $R>0$ (existence already known via GV bound, Theorem 4.2.1). **Question 7.2.1.** Does there exist an explicit code on the Zyablov bound?

<a id="pdf-7251cb8e4bc5-p147-b004"></a>
<!-- pdf-source: page=147; block=4; confidence=0.90 -->
Restrict to linear codes (polynomial-size representation). Let $C_{out}$ be an $[N,K]_Q$ Reed–Solomon code with $N = Q-1$ (evaluation points $\mathbb{F}_Q^*$, $Q=q^k$), which gives $k = \Theta(\log N)$. An efficient construction of an inner code on the GV bound is still needed.

<a id="pdf-7251cb8e4bc5-p148-b001"></a>
<!-- pdf-source: page=148; block=1; confidence=0.90 -->
Constructing $C_{in}$ in $\mathrm{poly}(k)$ time is not expected (would resolve an open question). Since $k=O(\log N)$, an algorithm running in time exponential in $k$ is still polynomial in $N$.

<a id="pdf-7251cb8e4bc5-p148-b002"></a>
<!-- pdf-source: page=148; block=2; confidence=0.85 -->
Two ways to build the inner code $C_{in}$ in time exponential in $k$:

1. Exhaustive search over all generator matrices for one on the GV bound (exists by the Varshamov bound, Theorem 4.2.1); takes $q^{O(kn)}$ time. With $k=rn$ (so $n=O(k)$), $q^{O(kn)}=q^{O(k^2)}=N^{O(\log N)}$, bounded by $(nN)^{O(\log(nN))}$ (quasi-polynomial).
2. Construct $C_{in}$ in $q^{O(n)}$ time, giving $(nN)^{O(1)}$ overall (cf. Exercise 4.6).

The latter yields an explicit family of codes on the Zyablov bound.

<a id="pdf-7251cb8e4bc5-p148-b003"></a>
<!-- pdf-source: page=148; block=3; confidence=0.95 -->
**Theorem 7.2.2.** For every prime power $q$ there is an explicit $q$-ary code achieving the Zyablov bound: for every $\varepsilon>0$ there is an algorithm that, given $\delta\in[0,\,1-\tfrac1q]$ and $n$, outputs in time $\mathrm{poly}(n)$ the generator matrix of a code of block length $n$ and rate
$$R \ge \max_{0<r<1-H_q(\delta+\varepsilon)} r\left(1 - \frac{\delta}{H_q^{-1}(1-r) - \varepsilon}\right).$$
This answers Question 7.2.1 affirmatively.

<a id="pdf-7251cb8e4bc5-p148-b004"></a>
<!-- pdf-source: page=148; block=4; confidence=0.90 -->
The construction of Theorem 7.2.2 relies on a brute-force search for a suitable inner code (acceptable for polynomial construction time).

**Question 7.2.3.** Does there exist a strongly explicit asymptotically good code?

<a id="pdf-7251cb8e4bc5-p148-b005"></a>
<!-- pdf-source: page=148; block=5; confidence=0.95 -->
## 7.3 Advanced Concatenation and Strongly Explicit Constructions

<a id="pdf-7251cb8e4bc5-p148-b006"></a>
<!-- pdf-source: page=148; block=6; confidence=0.90 -->
Strongly explicit codes via concatenation with extra twists, due to Justesen (the *Justesen codes*). The Zyablov-bound argument generalizes while preserving parameters by:

1. Picking $N$ different inner codes, one for each of the $N$ coordinates of the outer codeword.

<a id="pdf-7251cb8e4bc5-p149-b001"></a>
<!-- pdf-source: page=149; block=1; confidence=0.90 -->
2. It suffices that *most* (not all) inner codes lie on the GV bound.

Ensembles where most codes are good are constructible; e.g. the ensemble of all linear codes (Varshamov). The difficulty is only in selecting a single good one. Catch: the required ensemble must contain exactly $N$ codes, each with $N$ codewords of length $O(\log N)$ — far fewer than the number of linear codes of length $O(\log N)$, which is $2^{\Theta(\log^2 N)}$ (super-polynomial in $N$).

<a id="pdf-7251cb8e4bc5-p149-b002"></a>
<!-- pdf-source: page=149; block=2; confidence=0.90 -->
**Definition (Justesen concatenation).** Given an $(N,K,D)_{q^k}$ outer code $C_{out}$ and $N$ inner codes $(C^i_{in}:1\le i\le N)$, the concatenation $C_{out}\circ(C^1_{in},\dots,C^N_{in})$ is defined by: for a message $m\in[q^k]^K$ with outer codeword $(c_1,\dots,c_N)\stackrel{\text{def}}{=}C_{out}(m)$,
$$C_{out}\circ(C^1_{in},\dots,C^N_{in})(m) = (C^1_{in}(c_1),\,C^2_{in}(c_2),\dots,C^N_{in}(c_N)).$$

<a id="pdf-7251cb8e4bc5-p149-b003"></a>
<!-- pdf-source: page=149; block=3; confidence=0.88 -->
**Theorem 7.3.1.** Let $\varepsilon>0$. There is an ensemble of inner codes $C^1_{in},\dots,C^N_{in}$ of rate $\tfrac12$, with $N=q^k-1$, such that for at least $(1-\varepsilon)N$ values of $i$, $C^i_{in}$ has relative distance $\ge H_q^{-1}(\tfrac12-\varepsilon)$.

The ensemble (the *Wozencraft ensemble*): for $\alpha\in\mathbb{F}_{q^k}^*$, define $C^\alpha_{in}:\mathbb{F}_q^k\to\mathbb{F}_q^{2k}$ by $C^\alpha_{in}(x)=(x,\alpha x)$. Each $C^\alpha_{in}$ is linear and strongly explicit (proof left as exercise).

<a id="pdf-7251cb8e4bc5-p149-b004"></a>
<!-- pdf-source: page=149; block=4; confidence=0.95 -->
### 7.3.1 Justesen code

<a id="pdf-7251cb8e4bc5-p149-b005"></a>
<!-- pdf-source: page=149; block=5; confidence=0.90 -->
**Definition (Justesen code).** The outer code $C_{out}$ is a Reed–Solomon code evaluated over $\mathbb{F}_{q^k}^*$ of rate $R$ ($0<R<1$), with relative distance $\delta_{out}=1-R$ and block length $N=q^k-1$. The inner codes are the Wozencraft ensemble $\{C^\alpha_{in}\}_{\alpha\in\mathbb{F}_{q^k}^*}$ from Theorem 7.3.1. The Justesen code is $C^*\stackrel{\text{def}}{=}C_{out}\circ(C^1_{in},\dots,C^N_{in})$ with rate $R/2$.

<a id="pdf-7251cb8e4bc5-p149-b006"></a>
<!-- pdf-source: page=149; block=6; confidence=0.90 -->
**Proposition 7.3.2.** Let $\varepsilon>0$. $C^*$ has relative distance at least $(1-R-\varepsilon)\cdot H_q^{-1}(\tfrac12-\varepsilon)$.

<a id="pdf-7251cb8e4bc5-p149-b007"></a>
<!-- pdf-source: page=149; block=7; confidence=0.90 -->
**Proof.** Take $m_1\ne m_2\in(\mathbb{F}_{q^k})^K$. By the outer code's distance, $|S|\ge(1-R)N$ where $S=\{i\mid C_{out}(m_1)_i\ne C_{out}(m_2)_i\}$.

<a id="pdf-7251cb8e4bc5-p150-b001"></a>
<!-- pdf-source: page=150; block=1; confidence=0.85 -->
Call the $i$th inner code *good* if $C^i_{in}$ has distance $\ge d\stackrel{\text{def}}{=}H_q^{-1}(\tfrac12-\varepsilon)\cdot 2^k$, else *bad*. By Theorem 7.3.1 there are at most $\varepsilon N$ bad inner codes. Let $S_g$ (resp. $S_b$) be the good (resp. bad) inner codes in $S$. Since $|S_b|\le\varepsilon N$,
$$|S_g|=|S|-|S_b|\ge(1-R-\varepsilon)N. \tag{7.3}$$
For each good $i\in S$, $\Delta\big(C^i_{in}(C_{out}(m_1)_i),\,C^i_{in}(C_{out}(m_2)_i)\big)\ge d. \tag{7.4}$
From (7.3),(7.4), the distance of $C^*$ is at least
$$(1-R-\varepsilon)Nd=(1-R-\varepsilon)H_q^{-1}\!\left(\tfrac12-\varepsilon\right)N\cdot 2^k. \qquad\blacksquare$$

<a id="pdf-7251cb8e4bc5-p150-b002"></a>
<!-- pdf-source: page=150; block=2; confidence=0.92 -->
Since Reed–Solomon codes and the Wozencraft ensemble are strongly explicit (Exercise 7.4):

**Corollary 7.3.3.** The concatenated code $C^*$ of Proposition 7.3.2 is asymptotically good and strongly explicit.

This answers Question 7.2.3 modulo Theorem 7.3.1, proved next.

<a id="pdf-7251cb8e4bc5-p150-b003"></a>
<!-- pdf-source: page=150; block=3; confidence=0.85 -->
**Proof of Theorem 7.3.1.** Fix $y=(y_1,y_2)\in\mathbb{F}_q^{2k}\setminus\{0\}$ (so not both $y_1,y_2$ zero). Claim: $y\in C^\alpha_{in}$ for at most one $\alpha\in\mathbb{F}_{2^k}^*$. If $y\in C^\alpha_{in}$ then $y_2=\alpha\cdot y_1$. Case analysis:

- **Case 1:** $y_1\ne0,\ y_2\ne0$: $y\in C^\alpha_{in}$ with $\alpha=y_2/y_1$.
- **Case 2:** $y_1\ne0,\ y_2=0$: $y\notin C^\alpha_{in}$ for all $\alpha\in\mathbb{F}_{2^k}^*$ (since $\alpha y_1\ne0$).
- **Case 3:** $y_1=0,\ y_2\ne0$: $y\notin C^\alpha_{in}$ for all $\alpha\in\mathbb{F}_{2^k}^*$ (since $\alpha y_1=0$).

Assume $\mathrm{wt}(y)<H_q^{-1}(\tfrac12-\varepsilon)\cdot 2k$; such a $y$ makes $C^\alpha_{in}$ *bad* and lies in at most one $C^\alpha_{in}$, so the number of bad codes is at most
$$\Big|\big\{y:\mathrm{wt}(y)<H_q^{-1}(\tfrac12-\varepsilon)\cdot 2k\big\}\Big|\le \mathrm{Vol}_q\!\big(H_q^{-1}(\tfrac12-\varepsilon)\cdot 2k,\,2k\big)\le q^{H_q(H_q^{-1}(\tfrac12-\varepsilon))\cdot 2k}. \tag{7.5}$$

<a id="pdf-7251cb8e4bc5-p151-b001"></a>
<!-- pdf-source: page=151; block=1; confidence=0.95 -->
**Proof (conclusion).** The count equals $q^{(1/2-\varepsilon)\cdot 2k} = q^k/q^{2\varepsilon k} < \varepsilon(q^k-1) = \varepsilon N$ (eqs. (7.6)-(7.7)). Step (7.5) uses the upper bound on the volume of a Hamming ball (Proposition 3.3.3); (7.6) holds for large enough $k$. Hence for at least $(1-\varepsilon)N$ values of $\alpha$, the inner code $C_\alpha^{in}$ has relative distance at least $H_q^{-1}(1/2-\varepsilon)$. $\blacksquare$

<a id="pdf-7251cb8e4bc5-p151-b002"></a>
<!-- pdf-source: page=151; block=2; confidence=0.98 -->
## 7.4 Summary of concatenation

<a id="pdf-7251cb8e4bc5-p151-b003"></a>
<!-- pdf-source: page=151; block=3; confidence=0.90 -->
**Summary.** Concatenating an outer code of distance $D$ with an inner code of distance $d$ yields distance $\ge Dd$ (Theorem 7.1.1); $Dd$ is the *designed distance*. Combinatorial performance is the Zyablov bound (Theorem 7.2.2, Figure 7.2). Extremes: at binary relative distance $1/2-\varepsilon$ ($\varepsilon\to 0$), GV gives rate $\Omega(\varepsilon^2)$ while Zyablov gives $\approx\Omega(\varepsilon^3)$ (up to $\mathrm{polylog}(1/\varepsilon)$; Exercise 7.3); at distance $\delta\to 0$, GV gives rate $1-O(\delta\log(1/\delta))$ while Zyablov gives $\approx 1-O(\sqrt{\delta})$ (up to $\mathrm{polylog}(1/\delta)$; Exercise 7.12(4)). Zyablov is not known to be improvable via concatenation variants in the high-distance regime, but the Blokh-Zyablov variation improves the low-rate regime, approaching the GV bound up to polylog factors in $\delta$ (Exercise 7.12). Algorithmically, asymptotically good codes have polynomial-time construction (Theorem 7.2.2, making them 'explicit'), strongly explicit construction with generator-matrix entries computable in polynomial time (Corollary 7.3.3), and polynomial-time encoding by linearity.

<a id="pdf-7251cb8e4bc5-p151-b004"></a>
<!-- pdf-source: page=151; block=4; confidence=0.95 -->
**Question 7.4.1.** Can concatenated codes be decoded up to half their designed distance in polynomial time? (Deferred to a later chapter.)

<a id="pdf-7251cb8e4bc5-p152-b001"></a>
<!-- pdf-source: page=152; block=1; confidence=0.98 -->
## 7.5 Exercises

<a id="pdf-7251cb8e4bc5-p152-b002"></a>
<!-- pdf-source: page=152; block=2; confidence=0.90 -->
**Exercise 7.1.** Call $C\subseteq \mathbb{F}_2^n$ a *binary RS code* if there exist $q=2^t$, $n'$, a Reed-Solomon code $C'\subseteq \mathbb{F}_q^{n'}$, and a bijection $\varphi:\mathbb{F}_q\to\mathbb{F}_2^t$ with $C=\{(\varphi(x_1),\dots,\varphi(x_{n'})) : (x_1,\dots,x_{n'})\in C'\}$. Prove that for every $0\le R\le 1$ and integer $t$ there exist linear binary RS codes of block length $n=t2^t$, rate $R$, and relative distance at least $\frac{1-R}{\log n}$.

<a id="pdf-7251cb8e4bc5-p152-b003"></a>
<!-- pdf-source: page=152; block=3; confidence=0.92 -->
**Exercise 7.2.** Prove the concatenation of two linear codes is linear: for $C_{out}\subseteq \mathbb{F}_{q^k}^N$ an $\mathbb{F}_{q^k}$-linear code and $C_{in}\subseteq \mathbb{F}_q^n$ an $\mathbb{F}_q$-linear code of dimension $k$, prove $C_{out}\circ C_{in}$ is $\mathbb{F}_q$-linear, and describe its generator matrix.

<a id="pdf-7251cb8e4bc5-p152-b004"></a>
<!-- pdf-source: page=152; block=4; confidence=0.95 -->
**Exercise 7.3.** Prove Theorem 7.2.2 yields explicit binary codes of distance $\delta=1/2-\gamma$ and rate $R=\Omega(\gamma^3)$ for every $\gamma>0$: show there is a constant $\eta>0$ such that for all $\gamma>0$ there is an explicit family of binary codes of relative distance at least $1/2-\gamma$ and rate at least $\eta\cdot\gamma^3$.

<a id="pdf-7251cb8e4bc5-p152-b005"></a>
<!-- pdf-source: page=152; block=5; confidence=0.95 -->
**Exercise 7.4.** For an $\mathbb{F}_2$-linear bijection $\varphi:\mathbb{F}_{2^t}\to\mathbb{F}_2^t$, the Wozencraft ensemble is $\{C_\alpha\subseteq \mathbb{F}_2^{2t} : \alpha\in\mathbb{F}_{2^t}^*\}$, where $C_\alpha$ has encoding $E_\alpha:\beta\mapsto \varphi(\beta)\circ\varphi(\alpha\beta)$. The rate-$1/4$ Justesen code has encoding $E_{Justesen}:\mathbb{F}_2^{tk}\to\mathbb{F}_2^{2t\cdot 2^t}$ with $k=2^{t-1}$, sending $(\varphi(c_0),\dots,\varphi(c_{k-1}))\mapsto (E_\alpha(P(\alpha)))_{\alpha\in\mathbb{F}_{2^t}}$ where $P(x)=\sum_{i=0}^{k-1} c_i x^i$. Prove: (1) each $C_\alpha$ ($\alpha\in\mathbb{F}_{2^t}^*$) is linear; (2) the Justesen code is linear; (3) the Justesen code is strongly explicit — give a generator matrix $G\in\mathbb{F}_2^{kt\times 2t\cdot 2^t}$ generating it, with a $\mathrm{poly}(t)$-time algorithm computing its $(i,j)$th entry for $(i,j)\in[kt]\times[2t\cdot 2^t]$.

<a id="pdf-7251cb8e4bc5-p152-b006"></a>
<!-- pdf-source: page=152; block=6; confidence=0.90 -->
**Exercise 7.5.** Prove a random code in the Wozencraft ensemble achieves capacity on $\mathrm{BSC}_p$ for every $p<H^{-1}(1/2)$. Specifically, given $\varepsilon>0$ and $p=H^{-1}(1/2)-\varepsilon$, prove there is $\gamma>0$ such that for every $t$ there exist $\alpha\in\mathbb{F}_2^t$ and a decoding map $D:\mathbb{F}_2^{2t}\to\mathbb{F}_2^t$ with, for every $m\in\mathbb{F}_2^t$, $\Pr_{e\sim\mathrm{BSC}(p)}[D(E_\alpha(m)+e)\ne m]\le 2^{-\gamma t}$.

<a id="pdf-7251cb8e4bc5-p152-b007"></a>
<!-- pdf-source: page=152; block=7; confidence=0.93 -->
**Exercise 7.6.** Say linear codes $C_1,\dots,C_M\subseteq \mathbb{F}_2^n$ form a *packing* in $\mathbb{F}_2^n$ if (i) all have the same size ($|C_i|=|C_j|$ for all $i,j\in[M]$) and (ii) they have minimal possible intersection $C_i\cap C_j=\{0^n\}$ for all $i\ne j$. [Parts (1)-(3) continue on p. 153.]

<a id="pdf-7251cb8e4bc5-p153-b001"></a>
<!-- pdf-source: page=153; block=1; confidence=0.92 -->
**Exercise 7.6 (continued).** (1) If $C_1,\dots,C_M$ form a packing and $d$ satisfies $\sum_{i=1}^{d-1}\binom{n}{i}<M$, then there exists $i\in[M]$ with $\Delta(C_i)\ge d$. (2) Extend the Wozencraft ensemble to codes of rate $1/\ell$ and distance approaching $H^{-1}(1-1/\ell)$ for every positive integer $\ell$. (3) Extend the notion of 'packing' to 'uniform cover' to build codes of rate $1-1/\ell$ and distance $H^{-1}(1/\ell)$.

<a id="pdf-7251cb8e4bc5-p153-b002"></a>
<!-- pdf-source: page=153; block=2; confidence=0.95 -->
**Exercise 7.7.** Let $C_{RS}\subseteq \mathbb{F}_{2^t}^{2^t}$ be a Reed-Solomon code of rate $\varepsilon$ and $C_{Had,t}\subseteq \mathbb{F}_2^{2^t}$ the Hadamard code of dimension $t$ and block length $2^t$ (Definition 2.6.2). Prove their concatenation yields an $[n=4^t,\ k=t2^t]_2$ linear code in which every non-zero codeword has Hamming weight in $[(1-\varepsilon)\tfrac{n}{2},\ (1+\varepsilon)\tfrac{n}{2}]$. Conclude there is an explicit $\varepsilon$-biased space in $\mathbb{F}_2^k$ of size $O\!\left(\frac{k^2}{\varepsilon^2\log^2 k}\right)$.

<a id="pdf-7251cb8e4bc5-p153-b003"></a>
<!-- pdf-source: page=153; block=3; confidence=0.90 -->
**Exercise 7.8.** (Generalized concatenated codes with logarithmic-length inner code achieve the asymptotic GV bound.) Let $C_{RS}$ be an $[N,K,N-K+1]_N$ code with $N=2^t$, and let $C^1,\dots,C^N\subseteq \mathbb{F}_2^t$ be independent random linear codes of rate $1$ (each a uniformly and independently chosen random linear map $\mathbb{F}_N\to\mathbb{F}_2^t$, possibly with nontrivial kernel). Prove the concatenated code $C=C_{RS}\circ(C^1,\dots,C^N)$ has, with high probability, rate $R=K/N$ and relative distance approaching $H^{-1}(1-R)$.

<a id="pdf-7251cb8e4bc5-p153-b004"></a>
<!-- pdf-source: page=153; block=4; confidence=0.93 -->
**Exercise 7.9.** (Dual distance of concatenated codes.) For $C=C_{out}\circ C_{in}$ a linear concatenated code: (1) if $C_{in}$ is an $[n,k]_q$ code with $k<n$, prove the minimum distance of $C^\perp$ is at most $k+1$; (2) if $C_{in}$ is an $[n,n]_q$ code, prove the relative minimum distance of $C^\perp$ is at least $\delta(C_{out}^\perp)/n$.

<a id="pdf-7251cb8e4bc5-p153-b005"></a>
<!-- pdf-source: page=153; block=5; confidence=0.85 -->
**Exercise 7.10.** For a prime power $q$ and integer $r\le q^2$, the Hermitian code $H_{q,r}$ is an explicit $[n,k,d]_{q^2}$ code with $n=q^3$, $k=\binom{r+1}{2}$, $d=n-rq$. Given $\varepsilon>0$ and $K_0$, choose parameters $q,r,t$ so that the concatenation of $H_{q,r}$ with the Hadamard code $C_{Had,t}$ yields an $[N,K]_2$ binary code with $K\ge K_0$, $N=O\!\left(\max\{K^{5/2},(\sqrt{K}/\varepsilon)^{5/2}\}\right)$, and every non-zero codeword of weight in $[(1-\varepsilon)\tfrac{N}{2},(1+\varepsilon)\tfrac{N}{2}]$. Conclude there is an explicit $\varepsilon$-biased space in $\mathbb{F}_2^K$ of size $O\!\left(\max\{K^{5/2},(\sqrt{K}/\varepsilon)^{5/2}\}\right)$. (For $\varepsilon=1/K$ this improves on the RS+Hadamard construction of Exercise 7.7, achieving $N=O(K^{15/4})$ instead of $N=O(K^4)$.)

<a id="pdf-7251cb8e4bc5-p154-b001"></a>
<!-- pdf-source: page=154; block=1; confidence=0.95 -->
**Exercise 7.11.** Show that a fully explicit asymptotically good code arises from a two-stage concatenation with two outer Reed–Solomon layers and an inner code drawn from an exponentially large ensemble: exhibit Reed–Solomon codes C₁, C₂ and a code C₃ from a Wozencraft ensemble such that C₁ ◦ C₂ ◦ C₃ is fully explicit and asymptotically good.

<a id="pdf-7251cb8e4bc5-p154-b002"></a>
<!-- pdf-source: page=154; block=2; confidence=0.90 -->
**Exercise 7.12 (multilevel concatenation).** For c and t₁,…,t_c with Σᵢtᵢ = t, a c-level concatenation of type (t₁,…,t_c) is given by c outer F_q-linear codes C^i_out : F_q^{k_i} → (F_q^{t_i})^n (i∈[c]) and one inner code C_in : F_q^t → F_q^T, with k = k₁+···+k_c. For a message m=(m₁,…,m_c), mᵢ∈F_q^{k_i}, set x^i = (x^i_1,…,x^i_n) = C^i_out(mᵢ) ∈ (F_q^{t_i})^n and y_j = C_in(x^1_j,…,x^c_j); then C(m) = (y_j)_{j∈[n]}. The concatenated code is denoted C = (C^1_out × ··· × C^c_out) ◦ C_in and maps F_q^k → F_q^{nT}. The exercise's aim: show multilevel concatenation improves on the Zyablov bound in the high-rate regime.

<a id="pdf-7251cb8e4bc5-p154-b003"></a>
<!-- pdf-source: page=154; block=3; confidence=0.90 -->
**Definition (type distance).** C_in has (t₁,…,t_c)-type distance (δ₁,…,δ_c) if for every i∈[c] the subcode C^i_in := { C_in(0^{t₁+···+t_{i-1}} mᵢ) : mᵢ ∈ F_q^{t_i+···+t_c} } has distance δ(C^i_in) ≥ δᵢ. Thus the type distance measures not just the distance of C_in but of the subcodes obtained by zeroing message prefixes. Any C_in of distance δ has type distance (δ,…,δ), but for most codes the later values δ₂, δ₃,… can be taken larger, which lets C^2_out, C^3_out,… have higher rate than a plain Zyablov-bound use would permit, raising the final rate.

<a id="pdf-7251cb8e4bc5-p154-b004"></a>
<!-- pdf-source: page=154; block=4; confidence=0.95 -->
**Exercise 7.12, Part 1.** Let Rᵢ = kᵢ/(tᵢ·n) be the rate of C^i_out, τᵢ = tᵢ/t, and R̄ := 1 − R the redundancy of rate R. Verify that C has rate R = (t/T)·Σᵢ τᵢ Rᵢ and redundancy R̄ ≤ (1 − t/T) + Σ_{i=1}^c τᵢ R̄ᵢ, and that C is F_q-linear.

<a id="pdf-7251cb8e4bc5-p154-b005"></a>
<!-- pdf-source: page=154; block=5; confidence=0.90 -->
**Exercise 7.12, Part 2.** Fix ε > 0. Prove there exists δ > 0 such that a random linear inner code C_in has (t₁,…,t_c)-type distance (δ₁,…,δ_c) with δᵢ = H_q^{-1}(1 − rᵢ) − ε and rᵢ = (tᵢ + ··· + t_c)/T, with probability at least 1 − exp(−δT).

<a id="pdf-7251cb8e4bc5-p154-b006"></a>
<!-- pdf-source: page=154; block=6; confidence=0.85 -->
**Exercise 7.12, Part 3.** Prove the minimum distance of C equals minᵢ { δᵢ · δ(C^i_out) }. Hint: for m=(m₁,…,m_c) take the smallest i with mᵢ ≠ 0 and show C(m) has weight at least δᵢ · δ(C^i_out) · nT.

<a id="pdf-7251cb8e4bc5-p154-b007"></a>
<!-- pdf-source: page=154; block=7; confidence=0.90 -->
**Exercise 7.12, Part 4.** Fix ε > 0 and take q large enough that H_q^{-1}(1 − R) ≥ 1 − R − ε for every R ∈ [0,1]. Prove the Zyablov bound (Theorem 7.2.2) rate R_Z for codes of minimum distance δ satisfies 1 − 2√δ − ε ≤ R_Z ≤ 1 − √δ.

<a id="pdf-7251cb8e4bc5-p154-b008"></a>
<!-- pdf-source: page=154; block=8; confidence=0.85 -->
**Exercise 7.12, Part 5.** For all δ, ε > 0 and sufficiently large q: for every sufficiently large N there exists a q-ary two-level concatenated code C = (C^1_out × C^2_out) ◦ C_in of length N with distance δ − O(ε) and rate 1 − δ^{2/3} − O(ε). Hint: with γ = t₁/(t₁+t₂) and ρ = δ(C_in), ignoring ε and assuming all codes (including C^2_in) meet the Singleton bound, bound the redundancy of C by ρ + γδ/ρ + δ/γ, then optimize over δ and γ.

<a id="pdf-7251cb8e4bc5-p155-b001"></a>
<!-- pdf-source: page=155; block=1; confidence=0.90 -->
**Exercise 7.12, Part 6.** Extend the Part 5 argument so that for every δ > 0, positive integer c, and ε > 0 one obtains concatenated codes of distance δ − ε and rate at least 1 − O_c(δ^{1−1/c}) − ε.

<a id="pdf-7251cb8e4bc5-p155-b002"></a>
<!-- pdf-source: page=155; block=2; confidence=0.90 -->
**Remark 7.5.1.** The same exercise carried out with q = 2 yields codes of distance δ and rate 1 − O_c(H₂(δ)^{1−1/c}) − ε, at the cost of somewhat more complex expressions.

<a id="pdf-7251cb8e4bc5-p155-b003"></a>
<!-- pdf-source: page=155; block=3; confidence=0.98 -->
## 7.6 Bibliographic Notes

<a id="pdf-7251cb8e4bc5-p155-b004"></a>
<!-- pdf-source: page=155; block=4; confidence=0.92 -->
**Bibliographic notes (§7.6).** Code concatenation, plus decoding algorithms achieving Shannon capacity in polynomial time (covered in a later chapter), are due to Forney [25]. The rate–distance tradeoff and the Zyablov bound (Theorem 7.2.2) are from Zyablov [77]. Justesen codes: Justesen [41]. Wozencraft ensembles: first reported by Massey [51], attributed to Wozencraft; the low-rate variant (Exercise 7.6, Part 2) is due to Weldon [40]. Multilevel concatenation (Exercise 7.12) is due to Blokh and Zyablov [8], who also give a closed-form optimized version, the Blokh–Zyablov bound (exact expression complex, involving integrals, omitted); see Dumer's survey [19] for details.

<a id="pdf-7251cb8e4bc5-p157-b001"></a>
<!-- pdf-source: page=157; block=1; confidence=0.98 -->
# Part IV: The Algorithms

<a id="pdf-7251cb8e4bc5-p159-b001"></a>
<!-- pdf-source: page=159; block=1; confidence=0.98 -->
# Chapter 8: Efficient Decoding of Reed-Solomon Codes

<a id="pdf-7251cb8e4bc5-p159-b002"></a>
<!-- pdf-source: page=159; block=2; confidence=0.95 -->
Overview: when the number of errors is below half the minimum distance, the received word uniquely determines the codeword. The chapter first gives an efficient unique-decoding algorithm recovering the codeword from a corrupted received word, then generalizes it to a list-decoding algorithm achieving the Johnson bound (Theorem ??): given a received word within the Johnson radius of the transmitted codeword, it efficiently outputs a small list of words containing the transmitted word.

<a id="pdf-7251cb8e4bc5-p159-b003"></a>
<!-- pdf-source: page=159; block=3; confidence=0.97 -->
## 8.1 Unique decoding of Reed-Solomon codes

<a id="pdf-7251cb8e4bc5-p159-b004"></a>
<!-- pdf-source: page=159; block=4; confidence=0.95 -->
Setup for the $[n,k,d=n-k+1]_q$ Reed-Solomon code with evaluation points $(\alpha_1,\dots,\alpha_n)$ (cf. Definition 5.2.1). The message is a polynomial $P(X)=\sum_{i=0}^{k-1} c_i X^i$, equivalently its coefficient vector $(c_0,\dots,c_{k-1})\in \mathbb{F}_q^k$. Its encoding is $(P(\alpha_1),\dots,P(\alpha_n))\in\mathbb{F}_q^n$. Transmission produces a received vector $y=(y_1,\dots,y_n)\in\mathbb{F}_q^n$ with error count $e=|\{i\in[n] \mid y_i\neq P(\alpha_i)\}|$. Unique decoding aims to recover $P$ from $y$ whenever $e < \tfrac{n-k+1}{2}$ (less than half the minimum distance).

<a id="pdf-7251cb8e4bc5-p159-b005"></a>
<!-- pdf-source: page=159; block=5; confidence=0.96 -->
**Problem 8.1.1 (Reed-Solomon Unique Decoding).**
- Input: code parameters $\mathbb{F}_q$, $(\alpha_1,\dots,\alpha_n)\in\mathbb{F}_q^n$, $k$; received word $y\in\mathbb{F}_q^n$.
- Output: a polynomial $P(X)\in\mathbb{F}_q[X]$ of degree less than $k$ such that $e:=|\{i\in[n]\mid y_i\neq P(\alpha_i)\}| < \tfrac{n-k+1}{2}$ if such a polynomial exists, and fail otherwise.

<a id="pdf-7251cb8e4bc5-p160-b001"></a>
<!-- pdf-source: page=160; block=1; confidence=0.94 -->
**Section 8.1.1 (Motivating the decoding algorithm).** Introduces a geometric view of the received word: treat y as the set of ordered pairs {(α₁,y₁),…,(αₙ,yₙ)}, i.e. points in 2-D space, switching between this and the usual vector view.

<a id="pdf-7251cb8e4bc5-p160-b002"></a>
<!-- pdf-source: page=160; block=2; confidence=0.90 -->
Figure 8.1: received word for a [14,2] Reed-Solomon code, with F_q embedded in {−7,…,7}. Evaluation points (−7,−5,−4,−3,−2,−1,0,1,2,3,4,5,6,7); received word (−7,5,−4,−3,2,−4,0,1,−2,3,4,−5,−2,7).

<a id="pdf-7251cb8e4bc5-p160-b003"></a>
<!-- pdf-source: page=160; block=3; confidence=0.95 -->
Assume there exists a polynomial P(X) of degree ≤ k−1 with Δ(y,(P(αᵢ))ⁿᵢ₌₁) ≤ e; equivalently P(αᵢ)=yᵢ for at least n−e locations i∈[n] (such P is unique if it exists). The design strategy is reverse engineering: assume P(X) known, derive identities on its coefficients, then solve for P(X). Also assume access to a polynomial E(X) (the error-locator, defined next).

<a id="pdf-7251cb8e4bc5-p160-b004"></a>
<!-- pdf-source: page=160; block=4; confidence=0.97 -->
**Definition 8.1.2 (Error-Locator Polynomial).** A non-zero polynomial E(X) is an error-locator polynomial if for all i∈[n]: E(αᵢ)=0 whenever yᵢ ≠ P(αᵢ).

<a id="pdf-7251cb8e4bc5-p161-b001"></a>
<!-- pdf-source: page=161; block=1; confidence=0.90 -->
Figure 8.2: closest codeword P(X)=X for the received word of Figure 8.1; degree-1 polynomials are lines.

<a id="pdf-7251cb8e4bc5-p161-b002"></a>
<!-- pdf-source: page=161; block=2; confidence=0.93 -->
The roots of E(X) include all error locations (where P and y disagree). Such an E of degree ≤ e exists, e.g. E(X) = ∏_{i: yᵢ≠P(αᵢ)} (X − αᵢ).

<a id="pdf-7251cb8e4bc5-p161-b003"></a>
<!-- pdf-source: page=161; block=3; confidence=0.96 -->
**Claim.** For every 1 ≤ i ≤ n: yᵢE(αᵢ) = P(αᵢ)E(αᵢ). (8.1)

<a id="pdf-7251cb8e4bc5-p161-b004"></a>
<!-- pdf-source: page=161; block=4; confidence=0.96 -->
**Proof.** Two cases. (1) If yᵢ ≠ P(αᵢ), then E(αᵢ)=0, so both sides are 0. (2) If yᵢ = P(αᵢ), then multiplying the equality by E(αᵢ) preserves it, so (8.1) holds. ∎

<a id="pdf-7251cb8e4bc5-p161-b005"></a>
<!-- pdf-source: page=161; block=5; confidence=0.90 -->
Both E(X) and P(X) are unknown, and finding P(X) is the decoder's task (given E(X), P(X) is easily computed from y — left as exercise). Treating the k coefficients of P(X) and the e+1 coefficients of E(X) as variables gives n equations from (8.1) in e+k+1 variables; the bound on e yields more equations than variables.

<a id="pdf-7251cb8e4bc5-p162-b001"></a>
<!-- pdf-source: page=162; block=1; confidence=0.90 -->
The n equations from (8.1) are quadratic (generally NP-hard to solve), but here e+k−1 ≪ n. Apply linearization: define N(X) := P(X)·E(X), a polynomial of degree ≤ e+k−1; then P(X)=N(X)/E(X), so finding N(X) and E(X) suffices. Requiring N to be a multiple of E retains the hardness. Welch-Berlekamp's idea: drop the constraint that E divides N, keeping only: deg N ≤ k+e−1, deg E ≤ e, and N(αᵢ)=yᵢ·E(αᵢ) for every i. This linearizes the search but may change the problem; correctness must be argued.

<a id="pdf-7251cb8e4bc5-p162-b002"></a>
<!-- pdf-source: page=162; block=2; confidence=0.92 -->
**Section 8.1.2 (Welch-Berlekamp Algorithm).** Finds two low-degree polynomials N(X), E(X) with N(αᵢ)=yᵢ·E(αᵢ) for all i, and outputs N(X)/E(X) provided this ratio is a polynomial of the correct degree with few errors. Formal statement in Algorithm 8.1.1.

<a id="pdf-7251cb8e4bc5-p162-b003"></a>
<!-- pdf-source: page=162; block=3; confidence=0.92 -->
**Section 8.1.3 (Analysis).** All steps except Step 1 are clearly efficiently implementable; Step 1 is too (proof deferred). Assuming Step 1 is solved efficiently, the analysis turns to correctness of Algorithm 8.1.1.

<a id="pdf-7251cb8e4bc5-p163-b001"></a>
<!-- pdf-source: page=163; block=1; confidence=0.95 -->
**Algorithm 8.1.1 (Welch-Berlekamp).** Input: integers n ≥ k ≥ 1, error bound 0 < e < (n−k+1)/2, and n pairs {(αᵢ, yᵢ)}ⁿᵢ₌₁ with the αᵢ distinct. Output: a polynomial P(X) of degree ≤ k−1, or fail.

1. Compute a nonzero E(X) of degree exactly e and N(X) of degree ≤ e+k−1 with yᵢE(αᵢ) = N(αᵢ) for 1 ≤ i ≤ n (Eq. 8.2).
2. If no such E(X), N(X) exist, or E(X) ∤ N(X), return fail.
4. Set P(X) ← N(X)/E(X).
5. If Δ(y, (P(αᵢ))ⁿᵢ₌₁) > e, return fail.
8. Otherwise return P(X).

<a id="pdf-7251cb8e4bc5-p163-b002"></a>
<!-- pdf-source: page=163; block=2; confidence=0.95 -->
If the algorithm does not output fail, its output is correct; so correctness reduces to Theorem 8.1.3 below.

<a id="pdf-7251cb8e4bc5-p163-b003"></a>
<!-- pdf-source: page=163; block=3; confidence=0.96 -->
**Theorem 8.1.3.** If (P(αᵢ))ⁿᵢ₌₁ is transmitted, where deg P(X) ≤ k−1, and at most e < (n−k+1)/2 errors occur (i.e. Δ(y, (P(αᵢ))ⁿᵢ₌₁) ≤ e), then the Welch-Berlekamp algorithm outputs P(X). Consequently the algorithm corrects RS codes of rate R up to a (1−R)/2 fraction of errors.

<a id="pdf-7251cb8e4bc5-p163-b004"></a>
<!-- pdf-source: page=163; block=4; confidence=0.96 -->
**Claim 8.1.4.** There exists a pair E*(X), N*(X) satisfying Step 1 with N*(X)/E*(X) = P(X).

<a id="pdf-7251cb8e4bc5-p163-b005"></a>
<!-- pdf-source: page=163; block=5; confidence=0.93 -->
**Proof.** Take E*(X) an error-locating polynomial for P(X) and set N*(X) = P(X)E*(X), so deg N* ≤ deg P + deg E* ≤ e+k−1. Define E*(X) of degree exactly e by

E*(X) = X^{e − Δ(y,(P(αᵢ))ⁿᵢ₌₁)} · ∏_{1≤i≤n : yᵢ ≠ P(αᵢ)} (X − αᵢ)   (Eq. 8.3).

Then E*(X) is nonzero of degree exactly e and satisfies: E*(αᵢ) ≠ 0 ⟹ yᵢ = P(αᵢ). (The prefactor X^{e−Δ} forces the degree to be exactly e.)

<a id="pdf-7251cb8e4bc5-p164-b001"></a>
<!-- pdf-source: page=164; block=1; confidence=0.93 -->
**Proof (cont.).** E* and N* satisfy Eq. 8.2: if E*(αᵢ) = 0 then N*(αᵢ) = P(αᵢ)E*(αᵢ) = yᵢE*(αᵢ) = 0; if E*(αᵢ) ≠ 0 then yᵢ = P(αᵢ), so P(αᵢ)E*(αᵢ) = yᵢE*(αᵢ). Hence a Step-1 solution exists, so fail can only occur if some solution (E′, N′) has N′/E′ ≠ P. Claim 8.1.5 rules this out; combined with Claim 8.1.4 it gives N′/E′ = P for every Step-1 solution.

<a id="pdf-7251cb8e4bc5-p164-b002"></a>
<!-- pdf-source: page=164; block=2; confidence=0.96 -->
**Claim 8.1.5.** If two distinct solutions (E₁(X), N₁(X)) ≠ (E₂(X), N₂(X)) both satisfy Step 1, then N₁(X)/E₁(X) = N₂(X)/E₂(X).

<a id="pdf-7251cb8e4bc5-p164-b003"></a>
<!-- pdf-source: page=164; block=3; confidence=0.92 -->
**Proof.** Define R(X) = N₁(X)E₂(X) − N₂(X)E₁(X) (Eq. 8.4), of degree ≤ 2e+k−1 (each product has degree ≤ 2e+k−1). From Step 1, for every i ∈ [n]: N₁(αᵢ) = yᵢE₁(αᵢ) and N₂(αᵢ) = yᵢE₂(αᵢ) (Eq. 8.5). Then

R(αᵢ) = N₁(αᵢ)E₂(αᵢ) − N₂(αᵢ)E₁(αᵢ) = yᵢE₁(αᵢ)E₂(αᵢ) − yᵢE₂(αᵢ)E₁(αᵢ) = 0   (Eq. 8.6).

So R has n zeros but degree ≤ 2e+k−1. Since e < (n−k+1)/2, we have 2e+k−1 < n, so R ≡ 0 by the degree mantra (Proposition 5.1.5). Thus N₁E₂ ≡ N₂E₁, and since E₁, E₂ ≠ 0, N₁/E₁ = N₂/E₂.

<a id="pdf-7251cb8e4bc5-p164-b004"></a>
<!-- pdf-source: page=164; block=4; confidence=0.95 -->
**Proof of Theorem 8.1.3.** By Claim 8.1.4 there is a pair (N₁, E₁) satisfying Eq. 8.2 with N₁(X)/E₁(X) = P(X); hence Step 1 produces some (N₂, E₂) satisfying Eq. 8.2. By Claim 8.1.5, N₂/E₂ = N₁/E₁ = P(X). Therefore the algorithm outputs P(X) at Step 8.

<a id="pdf-7251cb8e4bc5-p165-b001"></a>
<!-- pdf-source: page=165; block=1; confidence=0.92 -->
**Runtime.** The algorithm runs in O(n³) field-operation steps. All steps except 1, 2, 4 are O(n) bookkeeping. Steps 2 and 4 divide N(X) by E(X) by long division in O(n²). For Step 1, write E(X) = Σ_{j=0}^{e} EⱼXʲ and N(X) = Σ_{j=0}^{e+k−1} NⱼXʲ; the unknowns are E₀…E_e, N₀…N_{e+k−1}, totaling 2e+k+1 ≤ n+1 variables (using the bound on e). Each constraint yᵢE(αᵢ) = N(αᵢ) is linear. The nonlinear requirement E_e ≠ 0 (deg E = e) is replaced by E_e = 1, giving a linear system of n+1 equations in ≤ n+1 variables, solvable in O(n³). Every solution of this system solves Step 1 (E_e = 1 forces degree e); conversely, any Step-1 solution with E_e ≠ 0 yields the scaled solution E′(X) = E_e⁻¹·E(X), N′(X) = E_e⁻¹·N(X) with leading coefficient 1. Hence Step 1, and the whole algorithm, run in O(n³).

<a id="pdf-7251cb8e4bc5-p165-b002"></a>
<!-- pdf-source: page=165; block=2; confidence=0.97 -->
**Theorem 8.1.6.** Reed-Solomon Unique Decoding can be solved in O(n³) time.

<a id="pdf-7251cb8e4bc5-p165-b003"></a>
<!-- pdf-source: page=165; block=3; confidence=0.95 -->
This restates the error-decoding part of an earlier theorem and completes the missing piece in the proofs of the results on decoding concatenated codes up to half their design distance and on efficiently achieving BSCp capacity.

<a id="pdf-7251cb8e4bc5-p165-b004"></a>
<!-- pdf-source: page=165; block=4; confidence=0.88 -->
**Section 8.2 — List Decoding Reed-Solomon Codes.** Motivates the question of whether an efficient list-decoding algorithm exists for a rate-R code correcting up to a 1 − √R fraction of errors (the Johnson bound).

<a id="pdf-7251cb8e4bc5-p166-b001"></a>
<!-- pdf-source: page=166; block=1; confidence=0.85 -->
Reed-Solomon codes of rate R can be efficiently list-decoded up to a 1−√R fraction of errors, yielding an explicit code meeting the stated target. A sequence of RS (list-)decoding algorithms is presented, each handling an increasing fraction of errors.

<a id="pdf-7251cb8e4bc5-p166-b002"></a>
<!-- pdf-source: page=166; block=2; confidence=0.95 -->
**Problem 8.2.1 (Reed-Solomon List Decoding).** Input: field F_q, evaluation points (α₁,…,αₙ) ∈ F_qⁿ, integers k and e, and received word y = (y₁,…,yₙ) ∈ F_qⁿ. Output: the list (set) of all polynomials P(X) ∈ F_q[X] with deg P < k such that t := |{ i ∈ [n] : yᵢ = P(αᵢ) }| ≥ n − e.

<a id="pdf-7251cb8e4bc5-p166-b003"></a>
<!-- pdf-source: page=166; block=3; confidence=0.90 -->
Goal: make t as small (e as large) as possible. The Johnson bound here permits t as small as √(nk); unique decoding corresponds to t > (n+k)/2. By AM-GM, √(nk) ≤ (n+k)/2.

<a id="pdf-7251cb8e4bc5-p166-b004"></a>
<!-- pdf-source: page=166; block=4; confidence=0.97 -->
**Section 8.2.1. Structure of the (list-)decoding algorithms.**

<a id="pdf-7251cb8e4bc5-p166-b005"></a>
<!-- pdf-source: page=166; block=5; confidence=0.92 -->
**Welch-Berlekamp (restated).** Step 1: find N(X) of degree k+e−1 and E(X) of degree e with N(αᵢ) = yᵢ E(αᵢ) for every 1 ≤ i ≤ n. Step 2: if Y − P(X) divides Q(X,Y) := Y·E(X) − N(X), output P(X) (assuming Δ(y, (P(αᵢ))ⁿᵢ₌₁) ≤ e). Y − P(X) divides Q iff P(X) = N(X)/E(X); indeed Q(X,Y) = E(X)·(Y − N(X)/E(X)), so Y − N(X)/E(X) is the unique linear-in-Y factor.

<a id="pdf-7251cb8e4bc5-p166-b006"></a>
<!-- pdf-source: page=166; block=6; confidence=0.90 -->
The algorithm is reinterpreted as an interpolation step plus a root-finding step. Step 1 (Interpolation Step): find a non-zero Q(X,Y) such that Q(αᵢ, yᵢ) = 0 for 1 ≤ i ≤ n.

<a id="pdf-7251cb8e4bc5-p167-b001"></a>
<!-- pdf-source: page=167; block=1; confidence=0.90 -->
Step 2 (Root Finding Step): if Y − P(X) is a factor of Q(X,Y), output P(X) (when close enough to the received word). In Welch-Berlekamp, Q(X,Y) = Y·E(X) − N(X), so Q(αᵢ, yᵢ) = 0 ⇔ N(αᵢ) = yᵢ E(αᵢ). Viewing Q as Q_X(Y) ∈ (F_q[X])[Y], a root is P(X) ∈ F_q[X] with Q_X(P(X)) = 0, equivalently Y − P(X) divides Q(X,Y).

<a id="pdf-7251cb8e4bc5-p167-b002"></a>
<!-- pdf-source: page=167; block=2; confidence=0.90 -->
Interpolation reduces to solving a linear system; root-finding is easy when Q is linear in Y, i.e. Q(X,Y) = E(X)Y − N(X), whose only root is N(X)/E(X). All list-decoders in the chapter share this two-step structure, differing only in how Step 1's linear system is set up. Step 2 is handled by bivariate polynomial factorization (retaining linear factors Y − P(X)), which is polynomial-time; the required bivariate root-finding is Theorem B.7.9.

<a id="pdf-7251cb8e4bc5-p167-b003"></a>
<!-- pdf-source: page=167; block=3; confidence=0.92 -->
For an $[n,k]$ RS code with rate $R = k/n$, three list-decoder instantiations are compared:

| | Basic LD | Weighted-Degree LD | Multiplicity LD |
|---|---|---|---|
| Fraction of errors | $1 - 2\sqrt{R}$ | $1 - \sqrt{2R}$ | $1 - \sqrt{R}$ |
| Agreement $t$ | $2\sqrt{nk}$ | $\sqrt{2nk}$ | $\sqrt{nk}$ |

The chapter proceeds starting with the Basic List-Decoder.

<a id="pdf-7251cb8e4bc5-p167-b004"></a>
<!-- pdf-source: page=167; block=4; confidence=0.97 -->
**Section 8.2.2. Basic List-Decoder.**

<a id="pdf-7251cb8e4bc5-p167-b005"></a>
<!-- pdf-source: page=167; block=5; confidence=0.90 -->
Allowing the degree of Q(X,Y) to be large makes its existence (Step 1) easy to guarantee, but too high a degree makes Q useless. The degree is controlled so the existence proof goes through while Q remains useful for Step 2; degree restrictions plus the degree mantra (Proposition 5.1.5) show Step 2 recovers all polynomials agreeing with y often.

<a id="pdf-7251cb8e4bc5-p168-b001"></a>
<!-- pdf-source: page=168; block=1; confidence=0.95 -->
**Definition 8.2.2.** deg_X(Q) is the maximum degree of X in any monomial of Q(X,Y); deg_Y(Q) is the maximum degree of Y in any monomial of Q(X,Y). Example: for Q(X,Y) = X²Y³ + X⁴Y², deg_X(Q) = 4 and deg_Y(Q) = 3.

<a id="pdf-7251cb8e4bc5-p168-b002"></a>
<!-- pdf-source: page=168; block=2; confidence=0.90 -->
Given deg_X(Q) = a and deg_Y(Q) = b, write Q(X,Y) = Σ_{0≤i≤a, 0≤j≤b} c_{ij} X^i Y^j with c_{ij} ∈ F_q; the number of coefficients is (a+1)(b+1). The algorithm bounds deg_X(Q) and deg_Y(Q) in Step 1 so there are enough variables to guarantee a suitable Q exists, then uses the degree mantra (Proposition 5.1.5) for Step 2. Its performance is incomparable to Welch-Berlekamp (each recovers P in cases the other does not).

<a id="pdf-7251cb8e4bc5-p168-b003"></a>
<!-- pdf-source: page=168; block=3; confidence=0.95 -->
**Algorithm 8.2.1 (The Basic List-Decoder for Reed-Solomon Codes).** Input: n ≥ k ≥ 1, ℓ ≥ 1, e = n − t, and n pairs {(αᵢ, yᵢ)}ⁿᵢ₌₁. Output: (possibly empty) list of polynomials P(X) of degree ≤ k−1. Step 1: find a non-zero Q(X,Y) with deg_X(Q) ≤ ℓ and deg_Y(Q) ≤ n/ℓ such that Q(αᵢ, yᵢ) = 0 for 1 ≤ i ≤ n (eq. 8.7). Step 2: factor Q(X,Y) into irreducible factors Q₁(X,Y),…,Q_m(X,Y). Set L ← ∅; for every factor Q_j(X,Y) = Y − P_j(X), if Δ(y, (P_j(αᵢ))ⁿᵢ₌₁) ≤ e and deg(P_j) ≤ k−1, add P_j(X) to L. Return L.

<a id="pdf-7251cb8e4bc5-p168-b004"></a>
<!-- pdf-source: page=168; block=4; confidence=0.90 -->
Steps 1 and 2 are the main steps; the remaining steps are simple post-processing to prune the output list. The runtime and correctness are analyzed next.

<a id="pdf-7251cb8e4bc5-p169-b001"></a>
<!-- pdf-source: page=169; block=1; confidence=0.96 -->
**Run time analysis.** The algorithm runs in polynomial time given Steps 1 and 2 are polynomial. Step 1 finds coefficients $\{Q_{ij}\}_{i\in\{0,\dots,n/\ell\},\,j\in\{0,\dots,\ell\}}$ in $\mathbb{F}_q$, not all zero, satisfying (8.7); each constraint of (8.7) is homogeneous linear, so this is finding a nontrivial solution to a homogeneous linear system, solvable in polynomial time via Gaussian elimination. Step 2 finds a root of a bivariate polynomial in polynomial time by Theorem B.7.9. Hence the Basic List-Decoder is polynomial-time.

<a id="pdf-7251cb8e4bc5-p169-b002"></a>
<!-- pdf-source: page=169; block=2; confidence=0.95 -->
**Correctness of Algorithm 8.2.1.** Claim: Step 1 always returns a non-zero $Q$ satisfying (8.7); this holds iff such a polynomial exists, argued below.

<a id="pdf-7251cb8e4bc5-p169-b003"></a>
<!-- pdf-source: page=169; block=3; confidence=0.97 -->
**Lemma 8.2.3.** For every input sequence $\{(\alpha_i, y_i)\}_{i=1}^{n}$, there exists a non-zero $Q(X,Y)$ satisfying (8.7).

<a id="pdf-7251cb8e4bc5-p169-b004"></a>
<!-- pdf-source: page=169; block=4; confidence=0.94 -->
**Proof.** It suffices that the number of coefficients of $Q(X,Y)$, namely $(\ell+1)(n/\ell+1)$, exceeds the number of constraints in (8.7), namely $n$. Indeed, $(\ell+1)\left(\tfrac{n}{\ell}+1\right) > \ell\cdot\tfrac{n}{\ell} = n$. $\square$

<a id="pdf-7251cb8e4bc5-p169-b005"></a>
<!-- pdf-source: page=169; block=5; confidence=0.93 -->
Remaining goal: show the final list $L$ in Step 6 contains all polynomials $P(X)$ to be output.

<a id="pdf-7251cb8e4bc5-p169-b006"></a>
<!-- pdf-source: page=169; block=6; confidence=0.97 -->
**Lemma 8.2.4.** If $P(X)$ of degree $\le k-1$ agrees with $Y$ in at least $t$ positions, then $Y-P(X)$ divides $Q(X,Y)$.

<a id="pdf-7251cb8e4bc5-p169-b007"></a>
<!-- pdf-source: page=169; block=7; confidence=0.95 -->
**Proof.** Define $R(X) \overset{\text{def}}{=} Q(X, P(X))$. Then $Y-P(X)$ divides $Q(X,Y)$ iff $R(X)\equiv 0$, so it suffices to show $R\equiv 0$. Suppose for contradiction $R\not\equiv 0$. Then
$$\deg(R) \le \deg_X(Q) + \deg(P)\cdot\deg_Y(Q) \le \ell + \frac{n(k-1)}{\ell},$$
the first inequality from the definition of $R$, the second from the assumed bounds on $\deg_X(Q)$ and $\deg_Y(Q)$. Also, whenever $P(\alpha_i)=y_i$, (8.7) gives $Q(\alpha_i,y_i)=Q(\alpha_i,P(\alpha_i))=0$.

<a id="pdf-7251cb8e4bc5-p170-b001"></a>
<!-- pdf-source: page=170; block=1; confidence=0.95 -->
**Proof (cont.).** Each such $\alpha_i$ is a root of $R(X)$, so $R$ has at least $t$ roots. By the degree mantra (Proposition 5.1.5), this contradicts $R\not\equiv 0$ provided $t > \deg(R)$, i.e. if $t > \ell + \frac{n(k-1)}{\ell}$. Choosing $\ell = \sqrt{n(k-1)}$ gives the condition $t > 2\sqrt{n(k-1)}$. $\square$

<a id="pdf-7251cb8e4bc5-p170-b002"></a>
<!-- pdf-source: page=170; block=2; confidence=0.96 -->
**Theorem 8.2.5.** Algorithm 8.2.1 can list decode Reed–Solomon codes of rate $R$ from a $1-2\sqrt{R}$ fraction of errors, and can be implemented in polynomial time.

<a id="pdf-7251cb8e4bc5-p170-b003"></a>
<!-- pdf-source: page=170; block=3; confidence=0.93 -->
Efficiency: Step 1 uses Gaussian elimination; for Step 3, all factors of $Q(X,Y)$ (in particular linear factors $Y-P(X)$) are computed via the algorithm of [43]. The bound $1-2\sqrt{R}$ beats the unique-decoding bound $\frac{1-R}{2}$ for $R<0.07$, but is still below the $1-\sqrt{R}$ fraction guaranteed by the Johnson bound (cf. Figure 8.2.2).

<a id="pdf-7251cb8e4bc5-p170-b004"></a>
<!-- pdf-source: page=170; block=4; confidence=0.90 -->
**Figure 8.3.** Tradeoff between rate $R$ and the fraction of errors correctable by Algorithm 8.2.1.

<a id="pdf-7251cb8e4bc5-p171-b001"></a>
<!-- pdf-source: page=171; block=1; confidence=0.97 -->
## 8.2.3 Algorithm 2

<a id="pdf-7251cb8e4bc5-p171-b002"></a>
<!-- pdf-source: page=171; block=2; confidence=0.94 -->
Recall in Algorithm 8.2.1 the analysis used $R(X)\overset{\text{def}}{=}Q(X,P(X))$ with $\deg(R)\le \deg_X(Q)+(k-1)\deg_Y(Q)$, requiring $t>\deg_X(Q)+(k-1)\deg_Y(Q)$. Shortcoming: the maximum $X$- and $Y$-degrees need not occur in the same term (e.g. $X^2Y^3+X^4Y^2$). The new algorithm uses a more balanced degree notion.

<a id="pdf-7251cb8e4bc5-p171-b003"></a>
<!-- pdf-source: page=171; block=3; confidence=0.97 -->
**Definition 8.2.6.** The $(1,w)$ weighted degree of the monomial $X^i Y^j$ is $i+wj$. The $(1,w)$-weighted degree (or $(1,w)$ degree) of $Q(X,Y)$ is the maximum $(1,w)$ weighted degree over its monomials.

<a id="pdf-7251cb8e4bc5-p171-b004"></a>
<!-- pdf-source: page=171; block=4; confidence=0.95 -->
Example: the $(1,2)$-degree of $XY^3+X^4Y$ is $\max(1+3\cdot2,\,4+2\cdot1)=7$. The $(1,1)$-degree of $Q(X,Y)$ equals its total degree.

<a id="pdf-7251cb8e4bc5-p171-b005"></a>
<!-- pdf-source: page=171; block=5; confidence=0.96 -->
**Lemma 8.2.7.** Let $Q(X,Y)$ have $(1,w)$ degree $D$, and let $P(X)$ satisfy $\deg(P)\le w$. Then $\deg\big(Q(X,P(X))\big)\le D$. (Proof left as an exercise.)

<a id="pdf-7251cb8e4bc5-p171-b006"></a>
<!-- pdf-source: page=171; block=6; confidence=0.90 -->
A polynomial of $(1,w)$ degree $\le D$ can be written $Q(X,Y)\overset{\text{def}}{=}\sum_{\substack{i+wj\le D\\ i,j\ge0}} c_{i,j}X^iY^j$ with $c_{i,j}\in\mathbb{F}_q$. The new algorithm equals Algorithm 8.2.1 except the interpolation step computes a bivariate $Q$ of bounded $(1,k-1)$ degree; illustrated by example (Figures 8.4–8.6, showing interpolation of a $(1,1)$-degree-$4$ $Q$ through the received word and factoring $Y-X$, $Y+X$).

<a id="pdf-7251cb8e4bc5-p171-b007"></a>
<!-- pdf-source: page=171; block=7; confidence=0.96 -->
Algorithm 8.2.2 uses the condition $Q(\alpha_i, y_i)=0,\ 1\le i\le n.$ (8.8)

<a id="pdf-7251cb8e4bc5-p172-b001"></a>
<!-- pdf-source: page=172; block=1; confidence=0.90 -->
**Figure 8.4.** Received word for the [14, 2] Reed–Solomon code (field F_q embedded in {−7, …, 7}) with e = 9 errors, exceeding what Algorithm 8.1.1 handles. Goal: find lines through at least 5 points. Unique decoding would require t ≥ (n+k)/2 = (14+2)/2 = 8, higher than the target agreement of 5 achievable by list decoding.

<a id="pdf-7251cb8e4bc5-p172-b002"></a>
<!-- pdf-source: page=172; block=2; confidence=0.90 -->
**Proof of Correctness of Algorithm 8.2.2.** Two requirements, as for Algorithm 8.2.1:

- **Interpolation Step:** the number of coefficients of Q(X, Y) is strictly greater than n.
- **Root Finding Step:** with R(X) := Q(X, P(X)), if P(α_i) ≥ y_i for at least t values of i, then R(X) ≡ 0.

Root finding: since Q(X, Y) has (1, k−1)-degree at most D, Lemma 8.2.7 gives deg(R) ≤ D. By the same argument as the root-finding step of Algorithm 8.2.1, R(X) ≡ 0 is guaranteed by choosing t > D. Hence D should be as small as possible, while Step 1 requires D large enough that the number of variables exceeds the number of constraints.

<a id="pdf-7251cb8e4bc5-p173-b001"></a>
<!-- pdf-source: page=173; block=1; confidence=0.95 -->
**Figure 8.5.** An interpolating polynomial Q(X, Y) for the received word of Figure 8.4.

<a id="pdf-7251cb8e4bc5-p173-b002"></a>
<!-- pdf-source: page=173; block=2; confidence=0.95 -->
**Figure 8.6.** The two polynomials to be output, shown in blue.

<a id="pdf-7251cb8e4bc5-p174-b001"></a>
<!-- pdf-source: page=174; block=1; confidence=0.95 -->
**Algorithm 8.2.2 (Second List Decoding Algorithm for Reed–Solomon Codes).**

- Input: n ≥ k ≥ 1, D ≥ 1, e = n − t, and n pairs {(α_i, y_i)}_{i=1}^{n}.
- Output: possibly empty list of polynomials P(X) of degree ≤ k − 1.

Steps:
1. Find a non-zero Q(X, Y) with (1, k−1)-degree at most D satisfying (8.8).
2. L ← ∅.
3. For every factor Y − P(X) of Q(X, Y):
4.   if Δ(y, (P(α_i))_{i=1}^{n}) ≤ e and deg(P) ≤ k − 1, then
5.     add P(X) to L.
6. Return L.

<a id="pdf-7251cb8e4bc5-p174-b002"></a>
<!-- pdf-source: page=174; block=2; confidence=0.95 -->
**Proof (continued, interpolation step).** Let N = |{(i, j) : i + (k−1)j ≤ D, i, j ∈ Z⁺}| be the number of coefficients of Q(X, Y). Since j ≤ ⌊D/(k−1)⌋, define L = ⌊D/(k−1)⌋ (the algorithm's list size). Then

N = Σ_{j=0}^{L} Σ_{i=0}^{D−(k−1)j} 1 = Σ_{j=0}^{L} (D − (k−1)j + 1) = (D+1)(L+1) − (k−1)·Σ_{j=0}^{L} j = (D+1)(L+1) − (k−1)L(L+1)/2 = ((L+1)/2)(2D + 2 − (k−1)L) ≥ ((L+1)/2)(D+2)   (8.9) ≥ D(D+2)/(2(k−1)).   (8.10)

Here (8.9) uses L ≤ D/(k−1), and (8.10) uses D/(k−1) − 1 ≤ L. Thus the interpolation step succeeds (a non-zero Q exists) if

D(D+2)/(2(k−1)) > n.

The choice D = ⌈√(2(k−1)n)⌉ [is made].

<a id="pdf-7251cb8e4bc5-p175-b001"></a>
<!-- pdf-source: page=175; block=1; confidence=0.90 -->
**Argument (continued).** The chain $\frac{D(D+2)}{2(k-1)} > \frac{D^2}{2(k-1)} \ge \frac{2(k-1)n}{2(k-1)} = n$ shows the required bound. Hence for the root-finding step to work one needs $t > \lceil\sqrt{2(k-1)n}\rceil$, which yields the following result.

<a id="pdf-7251cb8e4bc5-p175-b002"></a>
<!-- pdf-source: page=175; block=2; confidence=0.97 -->
**Theorem 8.2.8.** Algorithm 2 list decodes Reed–Solomon codes of rate $R$ from up to $1-\sqrt{2R}$ fraction of errors, runs in polynomial time, and outputs a list of size at most $O(1/\sqrt{R})$.

<a id="pdf-7251cb8e4bc5-p175-b003"></a>
<!-- pdf-source: page=175; block=3; confidence=0.90 -->
Polynomial time: Step 1 via Gaussian elimination (number of coefficients is $O(n)$); root finding via any polynomial-time bivariate factorization. The bound $1-\sqrt{2R}$ beats the unique-decoding bound $(1-R)/2$ for $R < 1/3$ (Figure 8.7).

<a id="pdf-7251cb8e4bc5-p175-b004"></a>
<!-- pdf-source: page=175; block=4; confidence=0.97 -->
**8.2.4 Algorithm 3.**

<a id="pdf-7251cb8e4bc5-p176-b001"></a>
<!-- pdf-source: page=176; block=1; confidence=0.92 -->
Algorithm 3 list decodes Reed–Solomon codes correcting up to $1-\sqrt{R}$ fraction of errors. Added to the $(1,k-1)$-degree $\le D$ constraint on $Q(X,Y)$: for an integer parameter $r \ge 1$, require $Q(X,Y)$ to have $r$ roots at each $(\alpha_i, y_i)$, $1 \le i \le n$.

<a id="pdf-7251cb8e4bc5-p176-b002"></a>
<!-- pdf-source: page=176; block=2; confidence=0.90 -->
1. The number of equations on $Q$'s coefficients grows while the number of coefficients stays fixed, increasing $D$ (and hence $t$). 2. It also increases the number of roots of $R(X)$, and this gain more than compensates for the increase in $D$.

<a id="pdf-7251cb8e4bc5-p176-b003"></a>
<!-- pdf-source: page=176; block=3; confidence=0.90 -->
Examples motivating multiplicity: $Q=Y-X$ passes through the origin once and has no degree-0 term (Fig. 8.8); $Q=(Y-X)(Y+X)$ passes through the origin twice, no term of degree $\le 1$ (Fig. 8.9); $Q=(Y-X)(Y+X)(Y-2X)$ thrice, no term of degree $\le 2$ (Fig. 8.10). Generally, the product of $r$ lines through the origin has no term of degree $\le r-1$.

<a id="pdf-7251cb8e4bc5-p177-b001"></a>
<!-- pdf-source: page=177; block=1; confidence=0.96 -->
**Definition 8.2.9.** $Q(X,Y)$ has $r$ roots at $(0,0)$ if $Q(X,Y)$ has no monomial of degree at most $r-1$.

<a id="pdf-7251cb8e4bc5-p177-b002"></a>
<!-- pdf-source: page=177; block=2; confidence=0.96 -->
**Definition 8.2.10.** $Q(X,Y)$ has $r$ roots at $(\alpha,\beta)$ if $Q_{\alpha,\beta}(X,Y) \stackrel{\text{def}}{=} Q(x+\alpha, y+\beta)$ has $r$ roots at $(0,0)$.

<a id="pdf-7251cb8e4bc5-p178-b001"></a>
<!-- pdf-source: page=178; block=1; confidence=0.90 -->
Worked example preceding the formal algorithm. Figure 8.11 shows a received word for the [10, 2] Reed-Solomon code, with $\mathbb{F}_q$ embedded in $\{-9,\dots,11\}$, and $e = 6$ errors — more than Algorithm 8.2.2 can decode. Goal: find lines passing through at least 4 points.

<a id="pdf-7251cb8e4bc5-p178-b002"></a>
<!-- pdf-source: page=178; block=2; confidence=0.90 -->
Interpolate a bivariate $Q(X,Y)$ of $(1,1)$-degree $5$ that passes "twice" through all 2-D points of the received word (Figure 8.12), then factor out the linear factors $Y - P(X)$ of $Q(X,Y)$.

<a id="pdf-7251cb8e4bc5-p179-b001"></a>
<!-- pdf-source: page=179; block=1; confidence=0.90 -->
$Q(X,Y)$ from Figure 8.12 has five degree-one factors (Figure 8.13); in fact it decomposes exactly into the five lines.

<a id="pdf-7251cb8e4bc5-p179-b002"></a>
<!-- pdf-source: page=179; block=2; confidence=0.97 -->
**Condition (8.11).** $Q(\alpha_i, y_i) = 0$ with multiplicity $r$ for every $1 \le i \le n$.

<a id="pdf-7251cb8e4bc5-p179-b003"></a>
<!-- pdf-source: page=179; block=3; confidence=0.95 -->
**Algorithm 8.2.3 (Third List Decoding Algorithm for Reed-Solomon Codes).**

Input: $n \ge k \ge 1$, $D \ge 1$, $r \ge 1$, $e = n - t$, and $n$ pairs $\{(\alpha_i, y_i)\}_{i=1}^n$.

Output: (possibly empty) list of polynomials $P(X)$ of degree $\le k-1$.

1. Find a non-zero $Q(X,Y)$ of $(1, k-1)$-degree $\le D$ satisfying (8.11).
2. $L \leftarrow \emptyset$.
3. For every factor $Y - P(X)$ of $Q(X,Y)$:
4-5. if $\Delta(y, (P(\alpha_i))_{i=1}^n) \le e$ and $\deg(P) \le k-1$ then add $P(X)$ to $L$.
6. Return $L$.

<a id="pdf-7251cb8e4bc5-p179-b004"></a>
<!-- pdf-source: page=179; block=4; confidence=0.95 -->
Correctness of Algorithm 8.2.3 relies on the two lemmas below; their proofs are deferred to Section 8.2.4.

<a id="pdf-7251cb8e4bc5-p179-b005"></a>
<!-- pdf-source: page=179; block=5; confidence=0.95 -->
**Lemma 8.2.11.** The constraints in (8.11) impose $\binom{r+1}{2}$ constraints, for each $i$, on the coefficients of $Q(X,Y)$.

<a id="pdf-7251cb8e4bc5-p179-b006"></a>
<!-- pdf-source: page=179; block=6; confidence=0.96 -->
**Lemma 8.2.12.** $R(X) \overset{\text{def}}{=} Q(X, P(X))$ has $r$ roots for every $i$ with $P(\alpha_i) = y_i$; equivalently, $(X - \alpha_i)^r$ divides $R(X)$.

<a id="pdf-7251cb8e4bc5-p180-b001"></a>
<!-- pdf-source: page=180; block=1; confidence=0.94 -->
**Proof (interpolation step).** By arguments as for Algorithm 8.2.2, it suffices that
$$\frac{D(D+2)}{2(k-1)} > n\binom{r+1}{2},$$
where the LHS upper-bounds the number of coefficients of $Q(X,Y)$ (from (8.10)) and the RHS comes from Lemma 8.2.11. This is equivalent to $\frac{D(D+2)}{k-1} > n(r+1)r$, i.e. $D^2 + 2D > n(k-1)(r+1)r$. The choice $D = \left\lceil \sqrt{(k-1)\,n\,r(r+1)} \right\rceil$ works, establishing correctness of Step 1.

<a id="pdf-7251cb8e4bc5-p180-b002"></a>
<!-- pdf-source: page=180; block=2; confidence=0.93 -->
**Proof (root-finding step).** Need the number of roots of $R(X)$ (at least $rt$ by Lemma 8.2.12) to strictly exceed $\deg R(X) = D$ (Lemma 8.2.7). Thus require $tr > D$, i.e. $t > D/r$, which holds if $t = \left\lceil \sqrt{(k-1)n\left(1 + \tfrac{1}{r}\right)} \right\rceil$. Choosing $r = 2(k-1)n$ gives the requirement $t > \left\lceil \sqrt{(k-1)n + \tfrac{1}{2}} \right\rceil$, which is satisfied by $t \ge \sqrt{kn}$ since $-n + 1/2 < 0$ for all $n \ge 1$.

<a id="pdf-7251cb8e4bc5-p180-b003"></a>
<!-- pdf-source: page=180; block=3; confidence=0.96 -->
**Theorem 8.2.13.** Algorithm 8.2.3 list decodes Reed-Solomon codes of rate $R$ from up to a $1 - \sqrt{R}$ fraction of errors, and runs in polynomial time.

<a id="pdf-7251cb8e4bc5-p181-b001"></a>
<!-- pdf-source: page=181; block=1; confidence=0.95 -->
Runtime bound follows by the same argument as for the polynomial running time of Algorithm 8.2.2. **Theorem 8.2.13** thus establishes that Reed–Solomon codes can be efficiently decoded up to the Johnson bound; Figure 8.2.3 illustrates the error fractions correctable by the three list-decoding algorithms.

<a id="pdf-7251cb8e4bc5-p181-b002"></a>
<!-- pdf-source: page=181; block=2; confidence=0.97 -->
**Open Question 8.2.14.** Whether a rate-$R$ Reed–Solomon code can be efficiently list decoded beyond a $1-\sqrt{R}$ fraction of errors; the answer is unknown.

<a id="pdf-7251cb8e4bc5-p181-b003"></a>
<!-- pdf-source: page=181; block=3; confidence=0.97 -->
To complete the proof of Theorem 8.2.13, Lemmas 8.2.11 and 8.2.12 remain to be proved.

<a id="pdf-7251cb8e4bc5-p181-b004"></a>
<!-- pdf-source: page=181; block=4; confidence=0.98 -->
## Proof of key lemmas

<a id="pdf-7251cb8e4bc5-p181-b005"></a>
<!-- pdf-source: page=181; block=5; confidence=0.95 -->
**Proof of Lemma 8.2.11.** Let $Q(X,Y)=\sum_{i,j:\,i+(k-1)j\le D} c_{i,j}X^iY^j$ and $Q_{\alpha,\beta}(X,Y)=Q(X+\alpha,Y+\beta)=\sum_{i,j} c^{\alpha,\beta}_{i,j}X^iY^j$ (8.12)–(8.13). It suffices to show: (i) each $c^{\alpha,\beta}_{i,j}$ is a homogeneous linear combination of the $c_{i,j}$; (ii) if $Q_{\alpha,\beta}$ has no monomial of degree $<r$, this imposes $\binom{r+1}{2}$ constraints on the $c^{\alpha,\beta}_{i,j}$. Together (i) and (ii) prove the lemma. For (i), comparing coefficients of $X^iY^j$ in (8.12)/(8.13) gives $c^{\alpha,\beta}_{i,j}=\sum_{i'>i,\,j'>j} c_{i',j'}\binom{i'}{i}\binom{j'}{j}\alpha^{i'-i}\beta^{j'-j}$, which proves (i).

<a id="pdf-7251cb8e4bc5-p182-b001"></a>
<!-- pdf-source: page=182; block=1; confidence=0.95 -->
**Proof (continued).** For (ii): $Q_{\alpha,\beta}$ having no monomial of degree $<r$ means $c^{\alpha,\beta}_{i,j}=0$ whenever $i+j\le r-1$. The count of such constraints is $|\{(i,j)\in\mathbb{Z}_{\ge0}^2 : i+j\le r-1\}|=\binom{r+1}{2}$, since for each fixed $0\le j\le r-1$ there are $r-j$ choices of $i$, giving $\sum_{j=0}^{r-1}(r-j)=\sum_{\ell=1}^{r}\ell=\binom{r+1}{2}$. $\square$

<a id="pdf-7251cb8e4bc5-p182-b002"></a>
<!-- pdf-source: page=182; block=2; confidence=0.96 -->
**Lemma 8.2.15** (precise restatement of Lemma 8.2.12). Let $Q(X,Y)$ be computed by Step 1 of Algorithm 8.2.3, and let $P(X)$ have degree $\le k-1$ with $P(\alpha_i)=y_i$ for at least $t>\tfrac{D}{r}$ values of $i$. Then $Y-P(X)$ divides $Q(X,Y)$.

<a id="pdf-7251cb8e4bc5-p182-b003"></a>
<!-- pdf-source: page=182; block=3; confidence=0.95 -->
**Proof.** Define $R(X)\stackrel{\text{def}}{=}Q(X,P(X))$; it suffices to show $R(X)\equiv 0$.

<a id="pdf-7251cb8e4bc5-p182-b004"></a>
<!-- pdf-source: page=182; block=4; confidence=0.96 -->
**Claim 8.2.16.** If $P(\alpha_i)=y_i$, then $(X-\alpha_i)^r$ divides $R(X)$, i.e. $\alpha_i$ is a root of $R(X)$ of multiplicity $r$.

<a id="pdf-7251cb8e4bc5-p182-b005"></a>
<!-- pdf-source: page=182; block=5; confidence=0.92 -->
By definition of $Q$ and $P$, $\deg R\le D$. Granting Claim 8.2.16, $R$ has at least $t\cdot r$ roots, so by the degree mantra (Proposition 5.1.5) $R\equiv 0$ since $t\cdot r>D$. To prove the claim, define $P_{\alpha_i,y_i}(X)\stackrel{\text{def}}{=}P(X+\alpha_i)-y_i$ and $R_{\alpha_i,y_i}(X)\stackrel{\text{def}}{=}R(X+\alpha_i)=Q(X+\alpha_i,P(X+\alpha_i))=Q(X+\alpha_i,P_{\alpha_i,y_i}(X)+y_i)=Q_{\alpha_i,y_i}(X,P_{\alpha_i,y_i}(X))$, equations (8.14)–(8.18).

<a id="pdf-7251cb8e4bc5-p183-b001"></a>
<!-- pdf-source: page=183; block=1; confidence=0.93 -->
By (8.15), $R_{\alpha_i,y_i}(0)=0\Rightarrow R(\alpha_i)=0$, so $X\mid R_{\alpha_i,y_i}(X)\Rightarrow (X-\alpha_i)\mid R(X)$, and likewise $X^r\mid R_{\alpha_i,y_i}(X)\Rightarrow (X-\alpha_i)^r\mid R(X)$. So it suffices to show $X^r\mid R_{\alpha_i,y_i}(X)$. Since $P(\alpha_i)=y_i$, $P_{\alpha_i,y_i}(0)=0$, hence $P_{\alpha_i,y_i}(X)=X\cdot g(X)$ with $\deg g\le k-1$. Then $R_{\alpha_i,y_i}(X)=\sum_{i',j'}c^{\alpha_i,y_i}_{i',j'}X^{i'}(P_{\alpha_i,y_i}(X))^{j'}=\sum_{i',j'}c^{\alpha_i,y_i}_{i',j'}X^{i'}(Xg(X))^{j'}$. Every term with $c^{\alpha_i,y_i}_{i',j'}\ne0$ has $i'+j'\ge r$ (as $Q_{\alpha_i,y_i}$ has no monomial of degree $<r$), so $X^r\mid R_{\alpha_i,y_i}(X)$. $\square$

<a id="pdf-7251cb8e4bc5-p183-b002"></a>
<!-- pdf-source: page=183; block=2; confidence=0.98 -->
## 8.3 Extensions

<a id="pdf-7251cb8e4bc5-p183-b003"></a>
<!-- pdf-source: page=183; block=3; confidence=0.95 -->
Algorithm 8.2.3 is general enough to solve problems beyond list decoding; this section overviews such extensions.

<a id="pdf-7251cb8e4bc5-p183-b004"></a>
<!-- pdf-source: page=183; block=4; confidence=0.93 -->
Constraint (8.11) requires $Q(X,Y)$ to have $r\ge0$ roots at each $(\alpha_i,y_i)$, $1\le i\le n$, but the analysis never used that the multiplicity is uniform. Given nonzero integer multiplicities $w_i\ge0$, Algorithm 8.2.3 generalizes to output all $P(X)$ of degree $\le k-1$ with $\sum_{i:P(\alpha_i)=y_i} w_i > \sqrt{2(k-1)\sum_{i=1}^{n}\binom{w_i+1}{2}}$ (8.19); the previously treated case is $w_i=r$ for all $i$. (Proof left as an exercise.)

<a id="pdf-7251cb8e4bc5-p183-b005"></a>
<!-- pdf-source: page=183; block=5; confidence=0.94 -->
**Theorem 8.3.1.** Also allowing non-distinct $\alpha_i$: there is an algorithm that, given positive integer weights $w_{i,\alpha}$ for every $1\le i\le n$ and $\alpha\in\mathbb{F}$, runs in time polynomial in $n$ and $\sum_{i,\alpha}w_{i,\alpha}$, and outputs all polynomials $P(X)$ of degree $\le k-1$ such that $\sum_i w_{i,P(\alpha_i)} > \sqrt{(k-1)\sum_{i=1}^{n}\sum_{\alpha\in\mathbb{F}} w_{i,\alpha}^2}$. (Proof left as an exercise.)

<a id="pdf-7251cb8e4bc5-p184-b001"></a>
<!-- pdf-source: page=184; block=1; confidence=0.90 -->
Proof of the preceding theorem left to Exercise 8.13 (which also relaxes the integer-weight assumption at a cost in the agreement parameter). Introduces *soft decoding* as a generalization of list decoding.

<a id="pdf-7251cb8e4bc5-p184-b002"></a>
<!-- pdf-source: page=184; block=2; confidence=0.95 -->
**Definition 8.3.2 (Soft decoding).** Input: nonnegative weights $w_{i,\alpha}$ ($1 \le i \le n$, $\alpha \in \mathbb{F}_q$) and threshold $W \ge 0$. Output: all codewords $(c_1,\dots,c_n)$ of the $q$-ary code of block length $n$ satisfying $\sum_{i=1}^{n} w_{i,c_i} \ge W$.

<a id="pdf-7251cb8e4bc5-p184-b003"></a>
<!-- pdf-source: page=184; block=3; confidence=0.85 -->
**Note.** Theorem 8.3.1 solves the soft decoding problem with $W = \sqrt{(1+\varepsilon)(k-1)\sum_{i=1}^{n}\sum_{\alpha\in\mathbb{F}} w_{i,\alpha}^2}$ for every $\varepsilon > 0$.

<a id="pdf-7251cb8e4bc5-p184-b004"></a>
<!-- pdf-source: page=184; block=4; confidence=0.90 -->
List decoding is the special case $w_{i,y_i}=1$, $w_{i,\alpha}=0$ for $\alpha\neq y_i$, with received word $(y_1,\dots,y_n)$. Soft decoding models analog channels via confidence weights. List recovery is a further special case, used for decoding concatenated codes.

<a id="pdf-7251cb8e4bc5-p184-b005"></a>
<!-- pdf-source: page=184; block=5; confidence=0.95 -->
**Definition 8.3.3 (List Recovery).** Let $C \subseteq \mathbb{F}_q^n$. For $\varepsilon \in [0,1]$ and integers $0 \le \ell \le q$ and $L$, $C$ is $(\varepsilon,\ell,L)$-list recoverable if for every sequence of sets $S_1,\dots,S_n$ with $|S_i| \le \ell$, at most $L$ codewords $c=(c_1,\dots,c_n)\in C$ satisfy $|\{i\in[n] : c_i \in S_i\}| \ge t := (1-\varepsilon)n$. It is $(\varepsilon,\ell,L)$-efficiently-list recoverable if a polynomial-time algorithm finds all such codewords.

<a id="pdf-7251cb8e4bc5-p184-b006"></a>
<!-- pdf-source: page=184; block=6; confidence=0.92 -->
**Theorem 8.3.4.** For every $k \le n \le q$, the $[n,k]_q$ Reed-Solomon code is $\big(1-\sqrt{(k-1)\ell/n},\ \ell,\ \mathrm{poly}(n)\big)$-efficiently list recoverable. (Proof left as an exercise; that list recovery is a special case of soft decoding is also left as an exercise.)

<a id="pdf-7251cb8e4bc5-p185-b001"></a>
<!-- pdf-source: page=185; block=1; confidence=0.99 -->
**8.4 Exercises**

<a id="pdf-7251cb8e4bc5-p185-b002"></a>
<!-- pdf-source: page=185; block=2; confidence=0.95 -->
**Exercise 8.1 (Peterson's algorithm).** Let $G(X)\in\mathbb{F}_q[X]$ have degree $n-k$ with roots $\alpha,\alpha^2,\dots,\alpha^\ell$, where $\alpha\in\mathbb{F}_{q^s}$ has order $\ge n$. Code $C=\{(c_0,\dots,c_{n-1}) : \exists\, M(X)\in\mathbb{F}_q^{<k}[X],\ \sum_{i=0}^{n-1} c_i X^i = M(X)G(X)\}$. Transmitted codeword $C(X)=\sum_{i=0}^{n-1} c_i X^i$; received $y_i=c_i+z_i$; error locations $T=\{i : z_i\neq 0\}$. Define:
- Error-Locator: $E(X)=\prod_{i\in T}(1-\alpha^i X)$.
- Error-Descriptor: $\Gamma(X)=\sum_{i\in T} z_i\alpha^i \prod_{j\in T\setminus\{i\}}(1-\alpha^j X)$.
- Syndrome: $S(X)=\sum_{s=1}^{\ell} Z(\alpha^s)X^{s-1}$, where $Z(X)=\sum_{i=0}^{n-1} z_i X^i$.

<a id="pdf-7251cb8e4bc5-p185-b003"></a>
<!-- pdf-source: page=185; block=3; confidence=0.85 -->
1. Using $G(\alpha^j)=0$ for $1\le j\le\ell$, prove $Z(\alpha^j)=Y(\alpha^j)$ with $Y(X)=\sum_{i=0}^{n-1} y_i X^i$; conclude $S(X)$ is poly-time computable from the received word.
2. Key Equation: $E(X)S(X)\equiv\Gamma(X)\pmod{X^\ell}$.
3. Using $\mathrm{ord}(\alpha)\ge n$, prove $\gcd(E(X),\Gamma(X))=1$.
4. Prove $E(X)$ is invertible modulo $X^\ell$.
5. If $E_1(X)S(X)=\Gamma_1(X)\pmod{X^\ell}$ and $\max\{\deg(E_1)+\deg(\Gamma),\ \deg(E)+\deg(\Gamma_1)\}<\ell$, then $E\mid E_1$.
6. Give a poly-time algorithm correcting up to $(\ell-1)/2$ errors. *Hint:* compute $E_1$ of degree $\le\ell/2$ and $\Gamma_1$ of degree $\le(\ell-1)/2$ with $E_1 S=\Gamma_1\pmod{X^s}$; use roots of $E_1$ to locate a superset of errors, erase them, and apply erasure decoding.

<a id="pdf-7251cb8e4bc5-p186-b001"></a>
<!-- pdf-source: page=186; block=1; confidence=0.85 -->
**Exercise 8.2.** Generalizes the previous decoding to recovering a sparse univariate polynomial from its values. $Z(X)=\sum_{i=0}^{n-1} z_i X^i \in\mathbb{F}_q[X]$ is *$t$-sparse* if at most $t$ coefficients are nonzero.

<a id="pdf-7251cb8e4bc5-p186-b002"></a>
<!-- pdf-source: page=186; block=2; confidence=0.90 -->
1. If $\ell\ge 2t$ and $\alpha\in\mathbb{F}_q$ has order $\ge n$, prove that for every $\beta_1,\dots,\beta_\ell$ there is at most one $t$-sparse polynomial $Z$ of degree $<n$ with $Z(\alpha^i)=\beta_i$ for all $i$.
2. Recover the terms (exponents and coefficients) of $Z$ in time $\mathrm{poly}(t)$. Define $S(X)=\sum_{i=1}^{\ell} Z(\alpha^i)X^{i-1}$.
   (a) $t=1$, $Z(X)=c\,X^d$: prove $S(X)\equiv \dfrac{c\alpha^d}{1-\alpha^d X}\pmod{X^\ell}$.
   (b) General $t$, $Z(X)=\sum_{i=1}^t c_i X^{d_i}$: prove $S(X)\equiv \sum_{i=1}^t \dfrac{c_i\alpha^{d_i}}{1-\alpha^{d_i}X}\pmod{X^\ell}$.
   (c) Using $\mathrm{ord}(\alpha)\ge n$, conclude there exist relatively prime $\Gamma(X),E(X)$ of degree $\le t-1$ and $\le t$, with $E$ invertible mod $X^\ell$, such that $S(X)\equiv \Gamma(X)/E(X)\pmod{X^\ell}$.
   (d) If $\Gamma_1,E_1$ of degree $\le t-1$ and $\le t$ satisfy $S\equiv\Gamma_1/E_1\pmod{X^\ell}$, then $E\mid E_1$.
   (e) Compute such $\Gamma_1,E_1$ with $E_1(0)=1$, and recover the coefficients $c_1,\dots,c_t$ and exponents $d_1,\dots,d_t$ of $Z$.
Conclude: for degree bound $n$, sparsity $t$, $n<q$, there exist $2t$ points $\alpha_1,\dots,\alpha_{2t}\in\mathbb{F}_q$ whose evaluations uniquely specify and efficiently recover any $t$-sparse degree-$n$ polynomial $Z$.

<a id="pdf-7251cb8e4bc5-p186-b003"></a>
<!-- pdf-source: page=186; block=3; confidence=0.90 -->
**Exercise 8.3.** For $\mathbb{F}_{q^m}$, the Trace map is $\mathrm{Tr}(x)=x+x^q+x^{q^2}+\cdots+x^{q^{m-1}}$ for $x\in\mathbb{F}_{q^m}$. (Properties in Appendix B.5.5.)

<a id="pdf-7251cb8e4bc5-p187-b001"></a>
<!-- pdf-source: page=187; block=1; confidence=0.95 -->
**Exercise (part 1).** For a linear code C ⊆ F_{q^m}^n with dual C^⊥, define the subfield subcode C|_{F_q} = C ∩ F_q^n. Prove (C|_{F_q})^⊥ = Tr(C^⊥), where Tr(C^⊥) = {Tr(c) | c ∈ C^⊥}. Hint: prove both inclusions; the easy one is Tr(C^⊥) ⊆ (C|_{F_q})^⊥; for the harder direction use that A ⊆ B follows from ⟨a,b⟩ = 0 for all a ∈ A, b ∈ B^⊥.

<a id="pdf-7251cb8e4bc5-p187-b002"></a>
<!-- pdf-source: page=187; block=2; confidence=0.92 -->
**Exercise (part 2).** Show dim(C) ≤ dim(Tr(C)) ≤ m·dim(C), and dim(C) − (m−1)(n − dim(C)) ≤ dim(C|_{F_q}) ≤ dim(C), where dim(X) is the dimension of a linear space X ⊆ F^n as an F-vector space.

<a id="pdf-7251cb8e4bc5-p187-b003"></a>
<!-- pdf-source: page=187; block=3; confidence=0.88 -->
**Exercise 8.4.** Prove that RS Bounded Distance Decoding (Decision) is NP-hard over exponentially large fields. Problem: input F_q, (α_1,…,α_n) ∈ F_q^n, k, received word y ∈ F_q^n, error parameter t; output Yes iff there exists P(X) ∈ F_q[X] of degree < k with e := |{i ∈ [n] : y_i ≠ P(α_i)}| ≤ t, else No. May assume Finite Field Subset Sum is NP-hard: given S = {γ_1,…,γ_n} ⊆ F_{2^m}, β ∈ F_{2^m}, integer 1 ≤ k < n, decide whether there is a nonempty T ⊆ {1,…,n} with |T| = k+1 and ∑_{i∈T} γ_i = β. Hint: take q = 2^m, α_i = γ_i, t = n−k−1, and y_i = α_i^{k+1} − β·α_i^k for i = 1,…,n.

<a id="pdf-7251cb8e4bc5-p187-b004"></a>
<!-- pdf-source: page=187; block=4; confidence=0.90 -->
**Exercise 8.5.** Using Exercise 8.4, prove that the Minimum Distance (Decision) Problem is NP-hard over exponentially large fields. (Problem statement continues on the next page.)

<a id="pdf-7251cb8e4bc5-p188-b001"></a>
<!-- pdf-source: page=188; block=1; confidence=0.90 -->
**Exercise 8.5 (cont.).** Minimum Distance (Decision) Problem: input F_q, G ∈ F_q^{k×n}, d ∈ Z^+; output Yes iff there is a nonzero codeword of weight ≤ d in the code generated by G (i.e. x ∈ F_q^k with 0 < wt(xG) ≤ d), else No. Hint: use the code generated by the RS code from Exercise 8.4 together with the vector y; prove the new code has distance n−k−1 iff y is within distance n−k−1 of the RS code.

<a id="pdf-7251cb8e4bc5-p188-b002"></a>
<!-- pdf-source: page=188; block=2; confidence=0.90 -->
**Exercise 8.6.** List Recovery Problem (RS codes): input F_q, (α_1,…,α_n) ∈ F_q^n, k, error parameters e, ℓ, received lists S_1,…,S_n with S_i ⊆ F_q, |S_i| ≤ ℓ; output all P(X) ∈ F_q[X] of degree < k with |{i ∈ [n] : P(α_i) ∉ S_i}| ≤ e. Adapt Algorithm 8.2.3 (the RS list-decoder up to the Johnson bound) to solve it in polynomial time provided e < n − √(nℓk). In particular, for e = 0 conclude list-recovery is efficient when ℓ < n/k.

<a id="pdf-7251cb8e4bc5-p188-b003"></a>
<!-- pdf-source: page=188; block=3; confidence=0.95 -->
**Exercise 8.7.** Show the e = 0 list-recovery guarantee is tight: when ℓ = ⌈n/k⌉ there can be super-polynomially many (n^{ω(1)}) output polynomials. Let r be a fixed prime power, n = q = r^m, k = (r^m − 1)/(r − 1). Prove there are at least r^{2^m} polynomials f ∈ F_q[X]_{≤k} with f(a) ∈ F_r for every a ∈ F_q, and deduce the algorithm cannot be improved to ℓ = ⌈n/k⌉ in general. Hint: for x ∈ F_{r^m}, x^{(r^m−1)/(r−1)} ∈ F_r, so f_β(X) := (X+β)^{(r^m−1)/(r−1)} takes values in F_r on evaluation points in F_{r^m}; show {f_β}_{β∈{α^0,…,α^{k−1}}} contains 2^m F_r-linearly independent polynomials; by Lucas's theorem there are 2^m indices ℓ ∈ {0,…,k−1} with C(k,ℓ) nonzero in F_r. Remark: these families are F_r-subfield subcodes of RS codes (BCH codes, cf. Exercise 5.11), so this lower-bounds BCH dimension in a regime where the Exercise 5.11 bound is trivial.

<a id="pdf-7251cb8e4bc5-p188-b004"></a>
<!-- pdf-source: page=188; block=4; confidence=0.90 -->
**Exercise 8.8.** Prove there exist bad configurations for list-decoding RS codes when errors exceed half the minimum distance. Fix an [n,k,d]_q code C.

<a id="pdf-7251cb8e4bc5-p189-b001"></a>
<!-- pdf-source: page=189; block=1; confidence=0.95 -->
**Exercise 8.8 (parts 1–2).** (1) For every integer e, prove the expected number of codewords of C in a uniformly chosen ball of radius e is at least C(n,e)·(q−1)^e·q^{k−n}. (2) Prove that if k = n − n^ε and C is an [n,k,d]_n Reed-Solomon code, then there is a ball of radius d/(2(1−ε)) containing exp(n^ε) codewords; conclude that for high-rate RS codes, list-decoding from strictly more than half the minimum distance requires exponential-size lists.

<a id="pdf-7251cb8e4bc5-p189-b002"></a>
<!-- pdf-source: page=189; block=2; confidence=0.92 -->
**Exercise 8.9 / Definition.** Explore bad list-decoding configurations for RS codes near the Johnson radius via linearized/subspace polynomials. Let q = p^s be a prime power (p need not be prime). A set P ⊆ F_q[X] of polynomials is a **(k,b,t)-nice-family** if there exists a set S with |S| ≤ b such that every P ∈ P is (1) supported on the monomials {x^0,…,x^{k−1}} ∪ {x^i | i ∈ S}, and (2) has at least t zeroes in F_q.

<a id="pdf-7251cb8e4bc5-p189-b003"></a>
<!-- pdf-source: page=189; block=3; confidence=0.90 -->
**Exercise 8.9 (part 1).** Prove that if P is a (k,b,t)-nice-family, then there exists a Hamming ball of radius n−t in F_q^q containing at least |P|/q^b codewords of RS_q[F_q, k], the Reed-Solomon code of dimension k over F_q obtained by evaluating degree-(k−1) polynomials at all of F_q.

<a id="pdf-7251cb8e4bc5-p189-b004"></a>
<!-- pdf-source: page=189; block=4; confidence=0.88 -->
**Exercise 8.9 (parts 2–6).** For S ⊆ F_q let Z_S(X) = ∏_{α∈S}(X−α). V ⊆ F_q is an F_p-subspace if for all α ∈ F_p, β,γ ∈ V: αβ, β+γ ∈ V. Show that for an F_p-subspace V, Z_V is linearized: (2) for every α ∈ V, β ∈ F_q, Z_V(α+β) = Z_V(β); (3) with Q_V(X,Y) := Z_V(X+Y) − Z_V(X) − Z_V(Y), prove Q_V(α,β) = Q_V(β,α) = 0 for α ∈ V, β ∈ F_q; (4) prove deg Q_V(X,Y) < |V| and conclude Z_V(X+Y) = Z_V(X) + Z_V(Y); (5) for every α ∈ F_p, Z_V(αX) = α·Z_V(X); (6) conclude Z_V(X) is linearized, i.e. of the form ∑_{i=0}^{log_p|V|} c_i X^{p^i}.

<a id="pdf-7251cb8e4bc5-p189-b005"></a>
<!-- pdf-source: page=189; block=5; confidence=0.90 -->
**Exercise 8.9 (parts 7–8).** (7) Prove the number of F_p-subspaces of F_q of dimension v is at least p^{v(s−v)}. (8) Let P = {Z_V(X) | V an F_p-subspace of F_q with dim(V) = v}. Prove that for every integer a with 0 ≤ a ≤ v, P is a (p^a, v−a, p^v)-nice-family.

<a id="pdf-7251cb8e4bc5-p190-b001"></a>
<!-- pdf-source: page=190; block=1; confidence=0.90 -->
**Exercise (part 9).** Choose parameters to show: for every $\delta>0$ and $c<\infty$ there exist $R>0$ and infinitely many $N$ such that some ball of radius $N - R^{1/2+\delta}N$ contains $\Omega(N^c)$ codewords of an $[N, RN]_N$ Reed–Solomon code. Conclude that for every $\delta>0$ there is no polynomial-time algorithm to decode a $1 - R^{1/2+\delta}$ fraction of errors from every rate-$R$ Reed–Solomon code.

<a id="pdf-7251cb8e4bc5-p190-b002"></a>
<!-- pdf-source: page=190; block=2; confidence=0.95 -->
**Exercise 8.10.** Definition: $K \subseteq \mathbb{F}_q^n$ is a *Kakeya set* if for every direction $y \in \mathbb{F}_q^n$ there is a point $x \in \mathbb{F}_q^n$ with the line $\{x + a\cdot y \mid a \in \mathbb{F}_q\} \subseteq K$. Goal: prove $|K| \ge \binom{q+n-2}{n-1}$.

1. If $|K| < \binom{d+n-1}{n-1}$, there is a nonzero homogeneous degree-$d$ polynomial $P$ vanishing on all $a \in K$.
2. For $x\in\mathbb{F}_q^n$, $y\in\mathbb{F}_q^n\setminus\{0\}$, on the line $\ell = \ell_{x,y} := \{x + t\cdot y \mid t\in\mathbb{F}_q\}$ the restriction of a homogeneous degree-$d$ polynomial $P$ is $P_\ell(t) = P(y)\cdot t^d + g_{x,y}(t)$ with $\deg(g_{x,y}) < d$.
3. If $K$ contains a line $\ell_{x,y}$ and $P$ is homogeneous of degree $d < q$ and vanishes on $K$, then $P(y)=0$.
4. Conclude: if $|K| < \binom{q+n-2}{n-1}$ then $K$ cannot be a Kakeya set.

<a id="pdf-7251cb8e4bc5-p190-b003"></a>
<!-- pdf-source: page=190; block=3; confidence=0.95 -->
**Exercise 8.11.** Chinese Remainder codes as a number-theoretic analog of RS codes. Let $1 \le k < n$, distinct primes $p_1 < p_2 < \cdots < p_n$, $K = \prod_{i=1}^{k} p_i$, $N = \prod_{i=1}^{n} p_i$, and $\mathbb{Z}_M = \{0,1,\dots,M-1\}$. Encoding $E:\mathbb{Z}_K \to \mathbb{Z}_{p_1}\times\cdots\times\mathbb{Z}_{p_n}$, $E(m) = (m \bmod p_1, \dots, m \bmod p_n)$ (symbols lie in different alphabets, but distance is still defined).

1. For $m_1 \ne m_2$, set indicator $b_i = 1$ if $E(m_1)_i \ne E(m_2)_i$ else $0$. Prove $\prod_{i=1}^{n} p_i^{b_i} > N/K$, and deduce $E(m_1)$, $E(m_2)$ differ in at least $n-k+1$ locations.
2. (Welch–Berlekamp-style decoder.) Received word $r=(r_1,\dots,r_n)$, $r_i\in\mathbb{Z}_{p_i}$. By part 1, there is at most one $m\in\mathbb{Z}_K$ satisfying condition (8.20) [stated on next page].

<a id="pdf-7251cb8e4bc5-p191-b001"></a>
<!-- pdf-source: page=191; block=1; confidence=0.92 -->
**Exercise 8.11 (continued).** Condition (8.20): $\prod_{i:\,E(m)_i \ne r_i} p_i \le \sqrt{N/K}$; at most one $m$ satisfies it. Let $r$ be the unique integer in $\mathbb{Z}_N$ with $r \bmod p_i = r_i$ for all $i$ (guaranteed by CRT).

(a) Assuming such $m$ exists, prove there are integers $y,z$ with $0 \le y < \sqrt{NK}$ and $1 \le z \le \sqrt{N/K}$ such that $y \equiv rz \pmod{N}$.
(b) Prove that any $y,z$ meeting these conditions give $m = y/z$.
Remark: such $(y,z)$ is found via an integer linear program in variables $y,z,t$ with constraints $0 < z \le \sqrt{N/K}$ and $0 \le z\cdot r - t\cdot N < \sqrt{NK}$ — fixed dimension, solvable in polynomial time.

3. To instead decode under the Hamming condition $|\{i : E(m)_i \ne r_i\}| \le \tfrac{n-k}{2}$, use GMD-style ideas: call the above decoder repeatedly, erasing the last $i$ symbols for each $1 \le i \le n$.

<a id="pdf-7251cb8e4bc5-p191-b002"></a>
<!-- pdf-source: page=191; block=2; confidence=0.88 -->
**Exercise 8.12.** Abstract view of RS decoding extending to RS-like codes (algebraic-geometric, CRT). Definitions over a field $F$: for $u,v\in F^n$, componentwise product $u * v = (u_1 v_1, \dots, u_n v_n) \in F^n$; for $U,V\subseteq F^n$, $U * V = \{u*v \mid u\in U, v\in V\}$. Idea: to decode a code $C$ correcting $e$ errors (i.e. $\mathrm{dist}(C) > 2e$), build an error-locator code $E$ so that $E * C$ lies in a linear code $N$ of large distance. Required properties:
- $\dim(E) > e$;
- $E * C \subseteq N$;
- $\mathrm{dist}(N) > e$;
- $\mathrm{dist}(C) > n - \mathrm{dist}(E)$ [last item on next page].

<a id="pdf-7251cb8e4bc5-p192-b001"></a>
<!-- pdf-source: page=192; block=1; confidence=0.90 -->
**Exercise 8.12 (continued).** Fourth requirement: $\mathrm{dist}(C) > n - \mathrm{dist}(E)$. Decoding algorithm for $C$: input $r\in F^n$ with $\Delta(r,c)\le e$ for some (unique) $c\in C$.
- Step 1: Find $a\in E$, $b\in N$, $a\ne 0$, with $a * r = b$.
- Step 2: For each $i$, if $a_i=0$ set $s_i={?}$, else $s_i=r_i$; run erasure decoding of $C$ on $s$ to get $c\in C$ with $c_i=s_i$ wherever $s_i\ne{?}$. Output $c$.

Parts: (1) prove $a,b$ in Step 1 exist; (2) prove poly-time implementation given generator matrices of $C,N,E$; (3) prove every $(a,b)$ satisfying Step 1 gives $a * c = b$; (4) prove if $a * c' = b$ for some $c'\in C$ then $c'=c$; (5) conclude correctness; (6) for $C$ an $[n, n-2e]$ RS code, identify the $E$ and $N$ corresponding to the Welch–Berlekamp algorithm.

<a id="pdf-7251cb8e4bc5-p192-b002"></a>
<!-- pdf-source: page=192; block=2; confidence=0.90 -->
**Exercise 8.13.** Prove Theorem 8.3.1.
1. Give an algorithm taking positive integer weights $w_{i,\alpha}$ for $1\le i\le n$, $\alpha\in F$, running in time polynomial in $n$ and $\sum_{i,\alpha} w_{i,\alpha}$, that outputs all polynomials $P(X)$ of degree $\le k-1$ with
$$\sum_i w_{i,P(\alpha_i)} > \sqrt{(k-1)\sum_{i=0}^{n}\sum_{\alpha\in F} w_{i,\alpha}^2}.$$
Hint: scale the weights by a large enough polynomial in $n$ and $\sum_{i,\alpha} w_{i,\alpha}$ so that the bound in Eq. (8.19) implies the bound above.

<a id="pdf-7251cb8e4bc5-p193-b001"></a>
<!-- pdf-source: page=193; block=1; confidence=0.95 -->
**Exercise (Part 2).** Give an algorithm taking as input $\varepsilon > 0$ and positive real weights $w_{i,\alpha}$ for every $1 \le i \le n$ and $\alpha \in \mathbb{F}$, running in time polynomial in $n$ and $1/\varepsilon$, that outputs all polynomials $P(X)$ of degree at most $k-1$ such that
$$\sum_i w_{i,P(\alpha_i)} > (1+\varepsilon)\cdot \sqrt{(k-1)\sum_{i=0}^{n}\sum_{\alpha\in\mathbb{F}} w_{i,\alpha}^2}.$$

<a id="pdf-7251cb8e4bc5-p193-b002"></a>
<!-- pdf-source: page=193; block=2; confidence=0.95 -->
**Hint.** Scale the weights, round them down to integers bounded by $\mathrm{poly}(n/\varepsilon)$, then apply Part (1).

<a id="pdf-7251cb8e4bc5-p193-b003"></a>
<!-- pdf-source: page=193; block=3; confidence=0.99 -->
## 8.5 Bibliographic Notes

<a id="pdf-7251cb8e4bc5-p193-b004"></a>
<!-- pdf-source: page=193; block=4; confidence=0.97 -->
Attribution summary (expository):
- First polynomial-time decoder for certain Reed–Solomon families: Peterson [59] (1960, presented for binary cyclic BCH codes).
- Extended to cyclic BCH codes over general fields, including Reed–Solomon classes, by Gorenstein and Zierler [29]; leads to Exercise 8.1.
- Faster implementation: Berlekamp [7] and Massey [52]; these work for the polynomial-multiplication view of RS codes (Exercise 5.9).
- Algorithm of Section 8.1 (all RS codes): Welch and Berlekamp [75], exposition following Gemmell and Sudan [26].
- Algorithm 8.2.2 (RS list-decoding, Section 8.2): Sudan [70].
- Algorithm 8.2.3 (Section 8.2.4): Guruswami and Sudan [33].
- Exercise 8.2: Ben-Or and Tiwari (formulation from Kumar [46]).
- Exercises 8.4, 8.5: Guruswami and Vardy [34].
- Exercise 8.7: Guruswami and Rudra [31].
- Exercise 8.8: Justesen and Høholdt [42]; Dumer, Micciancio and Sudan [18].
- Exercise 8.9: Ben-Sasson, Kopparty and Radhakrishnan [6].
- Exercise 8.10: Dvir [21].
- Exercise 8.11: Mandelbaum [50].
- Exercise 8.12: Duursma and Kötter [20]; Pellikaan [57].

<a id="pdf-7251cb8e4bc5-p195-b001"></a>
<!-- pdf-source: page=195; block=1; confidence=0.99 -->
# Bibliography

<a id="pdf-7251cb8e4bc5-p195-b002"></a>
<!-- pdf-source: page=195; block=2; confidence=0.96 -->
Reference list (non-mathematical; entries condensed):
- [1] Agrawal, Kayal, Saxena, "PRIMES Is in P," Ann. Math. 160(2):781–793, 2004.
- [2] Alon, Spencer, *The Probabilistic Method*, Wiley, 1992.
- [3] Artin, *Algebra*, Prentice-Hall of India, 1996.
- [4] Bather, "A conversation with Herman Chernoff," Statistical Science 11(4):335–350, 1996.
- [5] Bellare, Goldreich, Sudan, "Free bits, PCPs, and nonapproximability—towards tight results," SIAM J. Comput. 27(3):804–915, 1998.
- [6] Ben-Sasson, Kopparty, Radhakrishnan, "Subspace polynomials and limits to list decoding of Reed–Solomon codes," IEEE Trans. Inf. Theory 56(1):113–120, 2010.
- [7] Berlekamp, *Algebraic Coding Theory*, McGraw-Hill, 1968.
- [8] Blokh, Zyablov, "Coding of generalized concatenated codes," Probl. Peredachi Inf. 10(3):45–50, 1974 (Engl. transl. Probl. Inf. Transm. 10:3:218–222, 1974).
- [9] Bose, Ray-Chaudhuri, "On a class of error correcting binary group codes," Information and Control 3:68–79, 1960.
- [10] Bullen, *Handbook of Means and Their Inequalities*, Springer Netherlands, 2010.
- [11] Chandler, Batterman, Shah, "Hexagonal information encoding article, process and system," US Patent 4,874,936, Oct. 1989.
- [12] Chen, Hsiao, "Error-correcting codes for semiconductor memory applications: a state-of-the-art review," IBM J. Res. Dev. 28(2):124–134, 1984.

<a id="pdf-7251cb8e4bc5-p196-b001"></a>
<!-- pdf-source: page=196; block=1; confidence=0.95 -->
Bibliography (references [13]–[27]), condensed to author + topic:

- [13] Chen, Lee, Gibson, Katz, Patterson — RAID reliable secondary storage.
- [14] Chernoff — asymptotic efficiency of hypothesis tests from sums of observations.
- [15] Cover & Thomas — *Elements of Information Theory* (2nd ed.).
- [16] DeMillo & Lipton — probabilistic remark on algebraic program testing.
- [17] Dubhashi & Panconesi — *Concentration of Measure* for randomized algorithms.
- [18] Dumer, Micciancio, Sudan — hardness of approximating minimum distance of a linear code.
- [19] Dumer — concatenated codes and multilevel generalizations.
- [20] Duursma & Kötter — error-locating pairs for cyclic codes.
- [21] Dvir — size of Kakeya sets in finite fields.
- [22] Ebert, Merkle, Vollmer — autoreducibility of random sequences.
- [23] Elias — coding for two noisy channels.
- [24] Erdős — remarks on graph theory.
- [25] Forney — *Concatenated Codes*.
- [26] Gemmell & Sudan — resilient correctors for multivariate polynomials.
- [27] Gilbert — comparison of signalling alphabets.

<a id="pdf-7251cb8e4bc5-p197-b001"></a>
<!-- pdf-source: page=197; block=1; confidence=0.97 -->
Bibliography (references [28]–[43]), condensed to author + topic:

- [28] Golay — notes on digital coding.
- [29] Gorenstein & Zierler — error-correcting codes in p^m symbols.
- [30] Guruswami & Kopparty — explicit subspace designs.
- [31] Guruswami & Rudra — limits to list decoding Reed–Solomon codes.
- [32] Guruswami & Rudra — explicit codes achieving list-decoding capacity with optimal redundancy.
- [33] Guruswami & Sudan — improved decoding of Reed–Solomon and algebraic-geometry codes.
- [34] Guruswami & Vardy — maximum-likelihood decoding of Reed–Solomon codes is NP-hard.
- [35] Hamming — error detecting and correcting codes.
- [36] Hocquenghem — error-correcting codes.
- [37] Høholdt, van Lint, Pellikaan — algebraic geometry codes.
- [38] Jiang & Vardy — asymptotic improvement of the Gilbert–Varshamov bound for binary codes.
- [39] Joshi — upper bounds for minimum distance codes.
- [40] Weldon Jr. — Justesen's construction, low-rate case.
- [41] Justesen — constructive asymptotically good algebraic codes.
- [42] Justesen & Høholdt — bounds on list decoding of MDS codes.
- [43] Kaltofen — reductions from multivariate to bi-/univariate integral polynomial factorization.

<a id="pdf-7251cb8e4bc5-p198-b001"></a>
<!-- pdf-source: page=198; block=1; confidence=0.97 -->
Bibliography (references [44]–[59]), condensed to author + topic:

- [44] Kopparty, Saraf, Yekhanin — high-rate codes with sublinear-time decoding.
- [45] Krachkovsky — Reed–Solomon codes for phased error bursts.
- [46] Kumar — personal communication (May 2024).
- [47] Lidl & Niederreiter — *Introduction to Finite Fields and Their Applications*.
- [48] MacWilliams — distribution of weights in a systematic code.
- [49] Mandelbaum — error correction in residue arithmetic.
- [50] Mandelbaum — class of arithmetic codes and a decoding algorithm.
- [51] Massey — *Threshold Decoding*.
- [52] Massey — shift-register synthesis and BCH decoding.
- [53] Mitzenmacher & Upfal — *Probability and Computing*.
- [54] Motwani & Raghavan — *Randomized Algorithms*.
- [55] Muller — Boolean algebra for switching circuits and error detection.
- [56] Ore — higher congruences (German), cited for Theorem 6.13.
- [57] Pellikaan — decoding by error location and dependent sets of error positions.
- [58] Peterson & Davis — *Computer Networks: A Systems Approach*.
- [59] Peterson — encoding/error-correction procedures for Bose–Chaudhuri codes.

<a id="pdf-7251cb8e4bc5-p199-b001"></a>
<!-- pdf-source: page=199; block=1; confidence=0.95 -->
Reference list (coding theory / algebra): [60] Reed, multiple-error-correcting codes, IRE Trans. IT 1954; [61] Reed & Solomon, polynomial codes over finite fields, SIAM J. Appl. Math. 1960; [62] Robbins, remark on Stirling's formula, Amer. Math. Monthly 1955; [63] Rosenbloom & Tsfasman, codes for the m-metric, 1997; [64] Schwartz, fast probabilistic polynomial-identity verification, J. ACM 1980; [65] Shannon, mathematical theory of communication, Bell STJ 1948; [66] Shoup, finding irreducible polynomials over finite fields, Math. Comp. 1990; [67] Shoup, computational intro to number theory and algebra, 2006; [68] Singleton, maximum distance q-nary codes, IEEE IT 1964; [69] Slepian, binary signaling alphabets, Bell STJ 1956; [70] Sudan, decoding Reed–Solomon beyond error-correction bound, J. Complexity 1997; [71] Tietäväinen, nonexistence of perfect codes, SIAM J. Appl. Math. 1973; [72] van Lint, nonexistence theorems for perfect codes, 1970; [73] Varshamov, number of signals in error-correcting codes, 1957; [74] von zur Gathen & Gerhard, Modern Computer Algebra, 3rd ed. 2013; [75] Welch & Berlekamp, error correction of algebraic block codes, US Patent 4,633,470, 1986.

<a id="pdf-7251cb8e4bc5-p200-b001"></a>
<!-- pdf-source: page=200; block=1; confidence=0.95 -->
Reference list (continued): [76] Zippel, probabilistic algorithms for sparse polynomials, EUROSAM, LNCS 72, Springer 1979; [77] Zyablov, complexity of constructing binary linear cascade codes, Probl. Peredachi Inf. 1971 (English transl. Problems of Information Transmission 7).

<a id="pdf-7251cb8e4bc5-p201-b001"></a>
<!-- pdf-source: page=201; block=1; confidence=0.98 -->
**Appendix A. Some Useful Facts** — Section A.1: Some Useful Inequalities.

<a id="pdf-7251cb8e4bc5-p201-b002"></a>
<!-- pdf-source: page=201; block=2; confidence=0.97 -->
**Definition.** For integers $a \le b$, the binomial coefficient is $\binom{b}{a} = \dfrac{b!}{a!\,(b-a)!}$.

<a id="pdf-7251cb8e4bc5-p201-b003"></a>
<!-- pdf-source: page=201; block=3; confidence=0.98 -->
**Lemma A.1.1.** For all integers $1 \le a \le b$, $\binom{b}{a} \ge \left(\dfrac{b}{a}\right)^{a}$.

<a id="pdf-7251cb8e4bc5-p201-b004"></a>
<!-- pdf-source: page=201; block=4; confidence=0.97 -->
**Proof.** $\binom{b}{a} = \prod_{i=0}^{a-1} \dfrac{b-i}{a-i} \ge \prod_{i=0}^{a-1} \dfrac{b}{a} = \left(\dfrac{b}{a}\right)^{a}$; the first equality is by definition, and the inequality holds because $b \ge a$ and $i \ge 0$ imply $\tfrac{b-i}{a-i} \ge \tfrac{b}{a}$. $\square$

<a id="pdf-7251cb8e4bc5-p201-b005"></a>
<!-- pdf-source: page=201; block=5; confidence=0.97 -->
**Lemma A.1.2 (Stirling's Approximation).** For every integer $n \ge 1$, $\sqrt{2\pi n}\left(\dfrac{n}{e}\right)^{n} e^{\lambda_1(n)} < n! < \sqrt{2\pi n}\left(\dfrac{n}{e}\right)^{n} e^{\lambda_2(n)}$, where $\lambda_1(n) = \dfrac{1}{12n+1}$ and $\lambda_2(n) = \dfrac{1}{12n}$. Stated without proof (see [62]).

<a id="pdf-7251cb8e4bc5-p202-b001"></a>
<!-- pdf-source: page=202; block=1; confidence=0.90 -->
Sets up another inequality on binomial coefficients.

<a id="pdf-7251cb8e4bc5-p202-b002"></a>
<!-- pdf-source: page=202; block=2; confidence=0.97 -->
**Lemma A.1.3.** For all integers $1 \le a \le b$, $\binom{b}{a} \le \left(\frac{eb}{a}\right)^a$.

<a id="pdf-7251cb8e4bc5-p202-b003"></a>
<!-- pdf-source: page=202; block=3; confidence=0.96 -->
**Proof.** $\binom{b}{a} = \frac{b(b-1)\cdots(b-a+1)}{a!} \le \frac{b^a}{a!}$. The bound follows from $a! > (a/e)^a$, itself following from $\frac{a^a}{a!} < \sum_{i=0}^{\infty} \frac{a^i}{i!} = e^a$.

<a id="pdf-7251cb8e4bc5-p202-b004"></a>
<!-- pdf-source: page=202; block=4; confidence=0.98 -->
**Lemma A.1.4 (Bernoulli's Inequality).** For all reals $k \ge 1$ and $x \ge -1$, $(1+x)^k \ge 1 + kx$.

<a id="pdf-7251cb8e4bc5-p202-b005"></a>
<!-- pdf-source: page=202; block=5; confidence=0.96 -->
**Proof Sketch.** Shown only for integer $k$ (full proof cited to [10]). Base case $k=1$ trivial. Inductive step: $(1+x)^{k+1} = (1+x)(1+x)^k \ge (1+x)(1+kx) = 1+(k+1)x+kx^2 \ge 1+(k+1)x$; first inequality uses the inductive hypothesis, second uses $k \ge 1$.

<a id="pdf-7251cb8e4bc5-p202-b006"></a>
<!-- pdf-source: page=202; block=6; confidence=0.95 -->
**Lemma A.1.5.** For $|x| \le 1$, $\sqrt{1+x} \le 1 + \frac{x}{2} - \frac{x^2}{16}$.

<a id="pdf-7251cb8e4bc5-p203-b001"></a>
<!-- pdf-source: page=203; block=1; confidence=0.95 -->
**Proof.** Squaring the RHS: $\left(1+\frac{x}{2}-\frac{x^2}{16}\right)^2 = 1 + \frac{x^2}{4} + \frac{x^4}{256} + x - \frac{x^2}{16} - \frac{x^3}{32} = 1 + x + \frac{3x^2}{16} - \frac{x^3}{32} + \frac{x^4}{256} \ge 1+x$.

<a id="pdf-7251cb8e4bc5-p203-b002"></a>
<!-- pdf-source: page=203; block=2; confidence=0.95 -->
**Lemma A.1.6 (Cauchy–Schwarz).** For vectors $x,y \in \mathbb{R}^n$, $|\langle x,z\rangle| \le \|x\|_2 \cdot \|z\|_2$.

<a id="pdf-7251cb8e4bc5-p203-b003"></a>
<!-- pdf-source: page=203; block=3; confidence=0.97 -->
# A.2 Some Useful Identities and Bounds

<a id="pdf-7251cb8e4bc5-p203-b004"></a>
<!-- pdf-source: page=203; block=4; confidence=0.96 -->
**Lemma A.2.1.** For $a,b,c,d > 0$: $\frac{a}{b} \le \frac{c}{d}$ if and only if $\frac{a}{a+b} \le \frac{c}{c+d}$.

<a id="pdf-7251cb8e4bc5-p203-b005"></a>
<!-- pdf-source: page=203; block=5; confidence=0.96 -->
**Proof.** $\frac{a}{b} \le \frac{c}{d}$ iff $\frac{b}{a} \ge \frac{d}{c}$ iff $\frac{b}{a}+1 \ge \frac{d}{c}+1$, which is equivalent to $\frac{a}{a+b} \le \frac{c}{c+d}$.

<a id="pdf-7251cb8e4bc5-p203-b006"></a>
<!-- pdf-source: page=203; block=6; confidence=0.95 -->
**Lemma A.2.2.** For $|x| < 1$, $\ln(1+x) = x - \frac{x^2}{2!} + \frac{x^3}{3!} - \cdots$ (as written in source; proof omitted as standard).

<a id="pdf-7251cb8e4bc5-p203-b007"></a>
<!-- pdf-source: page=203; block=7; confidence=0.95 -->
**Lemma A.2.3.** For $0 \le x < 1$: $x - x^2/2 \le \ln(1+x) \le x$. For $0 \le x \le 1/2$: $-x - x^2 \le \ln(1-x) \le -x$. (Proof omitted.)

<a id="pdf-7251cb8e4bc5-p204-b001"></a>
<!-- pdf-source: page=204; block=1; confidence=0.94 -->
**Lemma A.2.4.** For $x \le 1/4$, $1 - 5x^2 \le H(1/2 - x) \le 1 - x^2$, where $H$ is the binary entropy function.

<a id="pdf-7251cb8e4bc5-p204-b002"></a>
<!-- pdf-source: page=204; block=2; confidence=0.95 -->
**Proof.** Uses the identity $H(1/2 - x) = 1 - \tfrac{1}{2}\log(1-4x^2) + x\log\frac{1-2x}{1+2x}$ and the $\ln(1\pm\cdot)$ bounds of Lemma A.2.3. Upper bound: combining the bounds gives $H(1/2-x) \le 1 - \frac{x^2}{\ln 2} \le 1 - x^2$, where the last step (A.1) uses $x \le 1/4$. Lower bound: $H(1/2-x) \ge 1 - \frac{3x^2}{\ln 2} \ge 1 - 5x^2$, again using $x \le 1/4$.

<a id="pdf-7251cb8e4bc5-p204-b003"></a>
<!-- pdf-source: page=204; block=3; confidence=0.96 -->
**Lemma A.2.5.** For every real $x > 0$, $\left(1 + \frac{1}{x}\right)^x \le e$. Follows from $\lim_{x\to\infty}(1+1/x)^x = e$.

<a id="pdf-7251cb8e4bc5-p205-b001"></a>
<!-- pdf-source: page=205; block=1; confidence=0.98 -->
# Appendix B. Basic Algebraic Algorithms

<a id="pdf-7251cb8e4bc5-p205-b002"></a>
<!-- pdf-source: page=205; block=2; confidence=0.95 -->
**B.1 Executive Summary.** Background algebra used in the book, emphasizing finiteness (fields and vector spaces are usually finite) and efficient computation over these structures. Some material overlaps Sections 2.1, 2.2, 5.1; further references: Lidl–Niederreiter [47] (finite fields) and Shoup [67] (algebraic algorithms).

<a id="pdf-7251cb8e4bc5-p205-b003"></a>
<!-- pdf-source: page=205; block=3; confidence=0.93 -->
**B.2 Groups, Rings, Fields — terminology.** A binary operator on set $X$ is a function $\circ : X\times X\to X$, written $a\circ b$. It is *associative* if $a\circ(b\circ c)=(a\circ b)\circ c$ for all $a,b,c\in X$; *commutative* if $a\circ b=b\circ a$. An element $e\in X$ is an *identity* if $a\circ e=e\circ a=a$ for all $a$; identities are unique (if $e_1,e_2$ both identities, $e_1=e_1\circ e_2=e_2$). Given identity $e$, element $a$ is *invertible* if there exists $a^{-1}\in X$ with $a\circ a^{-1}=a^{-1}\circ a=e$ (completed on p.206).

<a id="pdf-7251cb8e4bc5-p206-b001"></a>
<!-- pdf-source: page=206; block=1; confidence=0.97 -->
**Definition B.2.1 (Group).** $(G,\circ)$ is a *group* if $\circ$ is associative, has an identity, and every element of $G$ is invertible. It is an *abelian group* if $\circ$ is also commutative. (Examples: integers under $+$; nonzero rationals under $\times$; permutations of a finite set under composition.)

<a id="pdf-7251cb8e4bc5-p206-b002"></a>
<!-- pdf-source: page=206; block=2; confidence=0.96 -->
**Definition B.2.2 (Ring).** A finite set $R$ with operations $+$ and $\cdot$ is a *ring* if (1) $(R,+)$ is an abelian group, (2) $\cdot$ is associative with an identity, and (3) $\cdot$ distributes over $+$: $a\cdot(b+c)=a\cdot b+a\cdot c$ and $(b+c)\cdot a=b\cdot a+c\cdot a$. It is a *commutative ring* if $\cdot$ is commutative. (Examples: integers, a commutative ring; $k\times k$ integer matrices under matrix $+,\cdot$, non-commutative for $k\ge 2$.)

<a id="pdf-7251cb8e4bc5-p206-b003"></a>
<!-- pdf-source: page=206; block=3; confidence=0.97 -->
**Definition B.2.3 (Field).** A set $F$ with $+,\cdot$ is a *field* if $(F,+,\cdot)$ is a commutative ring and $(F\setminus\{0\},\cdot)$ is a group, where $0$ is the additive identity. (Examples: rationals, reals, complexes; integers mod a prime $p$, cf. Lemma 2.1.4.)

<a id="pdf-7251cb8e4bc5-p206-b004"></a>
<!-- pdf-source: page=206; block=4; confidence=0.96 -->
Notation: $0$ = additive identity, $1$ = multiplicative identity, $-a$ = additive inverse, $a^{-1}$ = multiplicative inverse; $a+(-b)$ abbreviated $a-b$.

<a id="pdf-7251cb8e4bc5-p206-b005"></a>
<!-- pdf-source: page=206; block=5; confidence=0.94 -->
## B.3 Polynomials

Introduces polynomial rings, unique factorization, the remainder algorithm, the evaluation map, and the polynomial distance property (restating the degree mantra, Proposition 5.1.5).

<a id="pdf-7251cb8e4bc5-p206-b006"></a>
<!-- pdf-source: page=206; block=6; confidence=0.95 -->
**Definition B.3.1 (Formal Polynomials).** For a commutative ring $(R,+,\cdot)$ with identity, the ring of formal polynomials over $R$ in indeterminate $X$ is $R[X]=\{\sum_{i=0}^d f_i X^i \mid f_0,\dots,f_d\in R,\ d\in\mathbb{Z}_{\ge 0}\}$, under the equivalence $\sum_{i=0}^d f_i X^i = \sum_{i=0}^{d-1} f_i X^i$ whenever $f_d=0$. "Formal" means the $X^i$ are symbols without operational meaning; equivalently, polynomials are finite sequences over $R$ under $(f_0,\dots,f_d,0)\cong(f_0,\dots,f_d)$.

<a id="pdf-7251cb8e4bc5-p207-b001"></a>
<!-- pdf-source: page=207; block=1; confidence=0.85 -->
**Terminology.** For $f=\sum_{i=0}^d f_i X^i$: the $f_i$ are *coefficients*, the $X^i$ are *monomials*, the $f_i X^i$ are *terms*. The *degree* $\deg_X(f)=\deg(f)$ is the largest $e$ with $f_e\ne 0$.

**Addition.** For $f=\sum_{i=0}^d f_i X^i$, $g=\sum_{i=0}^d g_i X^i$ (pad with zeros to equal length), $f+g=\sum_{i=0}^d (f_i+g_i)X^i$.

**Multiplication.** For $f=\sum_{i=0}^d f_i X^i$, $g=\sum_{i=0}^e g_i X^i$, $f\cdot g=\sum_{i=0}^{d+e}\left(\sum_{j=0}^{e} f_{i-j}\cdot g_j\right)X^i$.

<a id="pdf-7251cb8e4bc5-p207-b002"></a>
<!-- pdf-source: page=207; block=2; confidence=0.97 -->
**Proposition B.3.2.** For every commutative ring $R$, $R[X]$ is a commutative ring under polynomial sum and product.

<a id="pdf-7251cb8e4bc5-p207-b003"></a>
<!-- pdf-source: page=207; block=3; confidence=0.93 -->
**Definition B.3.3 (UFD).** Let $R$ be a commutative ring. $u\in R$ is a *unit* if it has a multiplicative inverse. $a,b$ are *associates* if $a=b\cdot u$ for some unit $u$ (an equivalence relation). $a$ is *irreducible* if $a=b\cdot c$ implies $b$ or $c$ is a unit. A *factorization* of $a$ is $b_1,\dots,b_k$ with $a=b_1\cdots b_k$ and no $b_i$ a unit. $R$ is a *factorization domain* if every nonzero non-unit $a$ has a bound $k_a$ on the number of factors in any factorization. It is a *unique factorization domain (UFD)* if every nonzero non-unit has a unique irreducible factorization up to associates: if $a=b_1\cdots b_k=c_1\cdots c_\ell$ with all $b_i,c_j$ irreducible, then $k=\ell$ and there is a bijection $\pi:[k]\to[\ell]$ with $b_i$ and $c_{\pi(i)}$ associates for all $i$.

<a id="pdf-7251cb8e4bc5-p207-b004"></a>
<!-- pdf-source: page=207; block=4; confidence=0.97 -->
**Proposition B.3.4.** Every field is a UFD (since every nonzero element of a field is a unit).

<a id="pdf-7251cb8e4bc5-p207-b005"></a>
<!-- pdf-source: page=207; block=5; confidence=0.90 -->
**Lemma B.3.5 (Gauss).** If $R$ is a UFD, then $R[X]$ is a UFD. (Proof omitted.) Consequence: from a field $F$, $F[X]$, $(F[X])[Y]$, and $(F[Y])[X]$ are all UFDs; if $X,Y$ commute ($XY=YX$) then $(F[X])[Y]\cong(F[Y])[X]$.

<a id="pdf-7251cb8e4bc5-p208-b001"></a>
<!-- pdf-source: page=208; block=1; confidence=0.95 -->
The bivariate polynomial ring over F is written F[X, Y]; univariate and multivariate polynomial rings are central to algebraic coding theory.

<a id="pdf-7251cb8e4bc5-p208-b002"></a>
<!-- pdf-source: page=208; block=2; confidence=0.97 -->
**Definition (monic).** For f ∈ R[X] with f = ∑_{i=0}^{d} f_i X^i and f_d ≠ 0, f is *monic* if the leading coefficient f_d is a unit in R.

<a id="pdf-7251cb8e4bc5-p208-b003"></a>
<!-- pdf-source: page=208; block=3; confidence=0.97 -->
**Proposition B.3.6.** For a monic polynomial f and any polynomial p, there is a unique pair (q, r) of polynomials with p = q · f + r and deg(r) < deg(f). (Proof deferred to Exercise B.1.)

<a id="pdf-7251cb8e4bc5-p208-b004"></a>
<!-- pdf-source: page=208; block=4; confidence=0.90 -->
The map p ↦ (q, r) is the division algorithm. In the special case f = X − α with α ∈ R, the remainder has degree ≤ 0 and is identified with an element p(α) ∈ R, giving the evaluation map R[X] × R → R.

<a id="pdf-7251cb8e4bc5-p208-b005"></a>
<!-- pdf-source: page=208; block=5; confidence=0.96 -->
**Proposition B.3.7.** For p = ∑_{i=0}^{d} p_i X^i ∈ R[X] and α ∈ R, set p(α) = ∑_{i=0}^{d} p_i α^i. Then there is a unique q ∈ R[X] with p = q · (X − α) + p(α). Consequently p(α) = 0 iff (X − α) divides p(X).

<a id="pdf-7251cb8e4bc5-p208-b006"></a>
<!-- pdf-source: page=208; block=6; confidence=0.97 -->
**Lemma B.3.8 (Polynomial Distance Lemma).** For distinct f, g ∈ F[X] of degree at most d, there are at most d elements α ∈ F with f(α) = g(α).

<a id="pdf-7251cb8e4bc5-p208-b007"></a>
<!-- pdf-source: page=208; block=7; confidence=0.96 -->
**Proof.** Let h = f − g, which is nonzero of degree ≤ d. Let S = {α | f(α) = g(α)}. For each α ∈ S, (X − α) divides h. By unique factorization (F[X] is a UFD), h̃ = ∏_{α∈S}(X − α) divides h. Hence deg(h̃) ≤ deg(h) and deg(h̃) = |S|, so |S| ≤ d.

<a id="pdf-7251cb8e4bc5-p208-b008"></a>
<!-- pdf-source: page=208; block=8; confidence=0.93 -->
**B.4 Vector Spaces.** Introduces vector spaces over fields and two representations of a finite-dimensional space: via generators (generator matrix) and via constraints (parity check matrix), preceded by matrix notation.

<a id="pdf-7251cb8e4bc5-p209-b001"></a>
<!-- pdf-source: page=209; block=1; confidence=0.95 -->
**B.4.1 Matrices and Vectors.**

<a id="pdf-7251cb8e4bc5-p209-b002"></a>
<!-- pdf-source: page=209; block=2; confidence=0.92 -->
**Definition (vector, inner product).** A vector of length n over F is a row vector x ∈ F^n. For u, v ∈ F^n, the inner product is ⟨u, v⟩ = ∑_{i=1}^{n} u_i · v_i, with arithmetic over F.

<a id="pdf-7251cb8e4bc5-p209-b003"></a>
<!-- pdf-source: page=209; block=3; confidence=0.95 -->
**Definition (matrix operations).** A matrix M ∈ F^{k×n} has entry M_{i,j} for (i,j) ∈ [k]×[n]; M_{i,·} is the i-th row and M_{·,j} the j-th column. The transpose M^T ∈ F^{n×k} satisfies M^T_{j,i} = M_{i,j} for (j,i) ∈ [n]×[k] (so a row vector's transpose is a column vector). The product of A ∈ F^{k×n} and B ∈ F^{n×m} is C ∈ F^{k×m} with C_{i,j} = ⟨A_{i,·}, B_{·,j}⟩ for (i,j) ∈ [k]×[m].

<a id="pdf-7251cb8e4bc5-p209-b004"></a>
<!-- pdf-source: page=209; block=4; confidence=0.94 -->
**B.4.2 Definition and Properties of Vector Spaces.** (Repeats material from Section 2.2.)

<a id="pdf-7251cb8e4bc5-p209-b005"></a>
<!-- pdf-source: page=209; block=5; confidence=0.96 -->
**Definition B.4.1 (Vector Space).** Over a field F, a vector space is a triple (V, +, ·) where (V, +) is a commutative group and · : F × V → V distributes over addition: α · (u + v) = α · u + α · v for all α ∈ F and u, v ∈ V. The group identity is written 0 and V is called an F-vector space.

<a id="pdf-7251cb8e4bc5-p210-b001"></a>
<!-- pdf-source: page=210; block=1; confidence=0.93 -->
The basic F-vector space is F^n with coordinate-wise operations: for u = (u_1,…,u_n), v = (v_1,…,v_n), α ∈ F, u + v = (u_1+v_1,…,u_n+v_n) and α·u = (α·u_1,…,α·u_n). These are essentially the only vector spaces, but the representation of vectors matters.

<a id="pdf-7251cb8e4bc5-p210-b002"></a>
<!-- pdf-source: page=210; block=2; confidence=0.96 -->
**Definition B.4.2 (Dimension).** Vectors v_1,…,v_k ∈ V are linearly independent if ∑_{i=1}^{k} β_i · v_i = 0 forces β_1 = ··· = β_k = 0, and linearly dependent otherwise. V is finite dimensional of dimension k if every sequence of k+1 vectors from V is linearly dependent while some sequence of length k is linearly independent. A linearly independent set v_1,…,v_k forms a basis of V when V has dimension k.

<a id="pdf-7251cb8e4bc5-p210-b003"></a>
<!-- pdf-source: page=210; block=3; confidence=0.90 -->
**Proposition B.4.3.** If v_1,…,v_k form a basis of an F-vector space V, then V = {∑_{i=1}^{k} β_i · v_i | β_1,…,β_k ∈ F}, and the map (β_1,…,β_k) ↦ ∑_{i=1}^{k} β_i · v_i is an isomorphism from F^k to V.

<a id="pdf-7251cb8e4bc5-p210-b004"></a>
<!-- pdf-source: page=210; block=4; confidence=0.92 -->
Although all k-dimensional F-vector spaces are isomorphic, isomorphisms do not preserve error-correction properties, so different spaces yield different codes. The focus is on k-dimensional subspaces of F^n and their succinct matrix representations.

<a id="pdf-7251cb8e4bc5-p210-b005"></a>
<!-- pdf-source: page=210; block=5; confidence=0.95 -->
**Definition B.4.4 (Generator Matrix, Parity Check Matrix).** For V ⊆ F^n: G ∈ F^{k×n} is a generator matrix of V if its rows are linearly independent and V = {x · G | x ∈ F^k} (the rows form a basis). H ∈ F^{(n−k)×n} is a parity check matrix of V if its rows are linearly independent and V = {y ∈ F^n | H · y^T = 0}. The dual space V^⊥ is the space generated by H: V^⊥ = {x · H | x ∈ F^{n−k}}.

<a id="pdf-7251cb8e4bc5-p210-b006"></a>
<!-- pdf-source: page=210; block=6; confidence=0.88 -->
**Proof sketch.** Every V has a generator matrix: take a basis v_1,…,v_k as rows of G. For a parity check matrix, define a row operation as a k×k matrix R that either (i) has R_{ii}=1 with R_{ij}=0 except for one pair i≠j, or (ii) is a permutation matrix swapping two rows. Write G ⇝ G̃ when G̃ = R_m · R_{m−1} ··· R_1 · G; then G̃ is also a generator matrix of V. Gaussian elimination simplifies G so that, after permuting columns, G̃ has the form [I_k | A] with I_k the k×k identity. (Text continues beyond the supplied pages.)

<a id="pdf-7251cb8e4bc5-p211-b001"></a>
<!-- pdf-source: page=211; block=1; confidence=0.95 -->
Given $\tilde G = [I_k \mid A]$, set $H = [-A^T \mid I_{n-k}]$. Then $\tilde G \cdot H^T = 0$, hence $G \cdot H^T = 0$; the rows of $H$ are linearly independent, so $H$ is a parity check matrix of $V$.

<a id="pdf-7251cb8e4bc5-p211-b002"></a>
<!-- pdf-source: page=211; block=2; confidence=0.98 -->
**Proposition B.4.5.** If $V \subseteq \mathbb{F}^n$ is a $k$-dimensional vector space, then it has a generator matrix $G \in \mathbb{F}^{k\times n}$ and a parity check matrix $H \in \mathbb{F}^{(n-k)\times n}$. Its dual $V^\perp$ is generated by $H$, has dimension $n-k$, and has $G$ as its parity check matrix. Finally $(V^\perp)^\perp = V$.

<a id="pdf-7251cb8e4bc5-p211-b003"></a>
<!-- pdf-source: page=211; block=3; confidence=0.95 -->
Unlike orthogonality of real vectors, over finite fields there can be nonzero vectors in $V \cap V^\perp$, and even $V = V^\perp$ is possible.

<a id="pdf-7251cb8e4bc5-p211-b004"></a>
<!-- pdf-source: page=211; block=4; confidence=0.95 -->
## B.5 Finite Fields

Covers existence and uniqueness of finite fields and the basic maps between prime fields and their extensions.

<a id="pdf-7251cb8e4bc5-p211-b005"></a>
<!-- pdf-source: page=211; block=5; confidence=0.97 -->
### B.5.1 Prime Fields

<a id="pdf-7251cb8e4bc5-p211-b006"></a>
<!-- pdf-source: page=211; block=6; confidence=0.93 -->
**Definition.** For prime $p$, let $\mathbb{Z}_p = \{0,\dots,p-1\}$. For integer $a$ and positive integer $b$, $a \bmod b$ is the unique $c \in \mathbb{Z}_p$ with $b \mid (a-c)$. Define $+_p : (a,b) \mapsto (a+b) \bmod p$ and $\cdot_p : (a,b) \mapsto (ab) \bmod p$.

<a id="pdf-7251cb8e4bc5-p211-b007"></a>
<!-- pdf-source: page=211; block=7; confidence=0.98 -->
**Proposition B.5.1.** $(\mathbb{Z}_p, +_p, \cdot_p)$ forms a field of cardinality $p$.

<a id="pdf-7251cb8e4bc5-p211-b008"></a>
<!-- pdf-source: page=211; block=8; confidence=0.96 -->
**Definition.** For a finite field $\mathbb{F}$, its characteristic $\mathrm{char}(\mathbb{F})$ is the smallest positive integer $p$ with $p \cdot 1 = \underbrace{1+1+\cdots+1}_{p} = 0$.

<a id="pdf-7251cb8e4bc5-p211-b009"></a>
<!-- pdf-source: page=211; block=9; confidence=0.97 -->
**Proposition B.5.2.** For every finite field $\mathbb{F}$, $\mathrm{char}(\mathbb{F})$ is prime. Moreover $\mathbb{F}$ is a $\mathbb{Z}_p$-vector space with $p = \mathrm{char}(\mathbb{F})$, so $|\mathbb{F}| = p^n$ for prime $p$ and integer $n$.

<a id="pdf-7251cb8e4bc5-p211-b010"></a>
<!-- pdf-source: page=211; block=10; confidence=0.93 -->
**Proof.** Let $p = \mathrm{char}(\mathbb{F})$. Then $p$ is the smallest integer with $p \cdot a = 0$ for every nonzero $a \in \mathbb{F}$: indeed $p \cdot a = p \cdot 1 \cdot a = 0$, and if $p \cdot a = 0$ then $p \cdot a \cdot a^{-1} = p \cdot 1 = 0$. If $p = qr$, then $w = q \cdot 1 \in \mathbb{F}$ satisfies $w \cdot r = 0$, contradicting minimality of $p$; hence $p$ is prime. Finally $(\mathbb{F}, +, \circ)$ with $i \circ a = a + \cdots + a$ ($i$ times) for $i \in \mathbb{Z}_p$, $a \in \mathbb{F}$ is a $\mathbb{Z}_p$-vector space, so $|\mathbb{F}| = p^n$ where $n = \dim(\mathbb{F}, +, \circ)$.

<a id="pdf-7251cb8e4bc5-p212-b001"></a>
<!-- pdf-source: page=212; block=1; confidence=0.98 -->
**Proposition B.5.3.** For any prime $p$, there is a unique field of cardinality $p$ up to isomorphism.

<a id="pdf-7251cb8e4bc5-p212-b002"></a>
<!-- pdf-source: page=212; block=2; confidence=0.94 -->
**Proof.** Let $\mathbb{F}$ be a field of cardinality $p$. By Proposition B.5.2, $\mathrm{char}(\mathbb{F}) = p$. The map $1_{\mathbb{F}} \mapsto 1$ extends to an isomorphism (Exercise B.3).

<a id="pdf-7251cb8e4bc5-p212-b003"></a>
<!-- pdf-source: page=212; block=3; confidence=0.96 -->
Uniqueness justifies denoting the field of cardinality $p$ by $\mathbb{F}_p$.

<a id="pdf-7251cb8e4bc5-p212-b004"></a>
<!-- pdf-source: page=212; block=4; confidence=0.93 -->
### B.5.2 Extension fields and subfields

Non-prime fields exist exactly for cardinalities $p^n$ ($p$ prime, $n \ge 1$); proving existence requires structural facts about fields, developed next.

<a id="pdf-7251cb8e4bc5-p212-b005"></a>
<!-- pdf-source: page=212; block=5; confidence=0.97 -->
**Proposition B.5.4.** If $(G, \cdot)$ is a finite group with identity $1$, then $a^{|G|} = 1$ for every $a \in G$.

<a id="pdf-7251cb8e4bc5-p212-b006"></a>
<!-- pdf-source: page=212; block=6; confidence=0.97 -->
**Proposition B.5.5.** Let $\mathbb{F}$ be a field of cardinality $q$. Every $\alpha \in \mathbb{F}$ is a root of $X^q - X$, and $X^q - X = \prod_{\alpha \in \mathbb{F}} (X - \alpha)$.

<a id="pdf-7251cb8e4bc5-p212-b007"></a>
<!-- pdf-source: page=212; block=7; confidence=0.96 -->
**Proof.** If $\alpha = 0$, it is trivially a root of $X^q - X$. If $\alpha \neq 0$, then $\alpha \in (\mathbb{F}\setminus\{0\}, \cdot)$, so by Proposition B.5.4, $\alpha^{|\mathbb{F}\setminus\{0\}|} = 1$, i.e. $\alpha^{q-1} = 1$, hence $\alpha^q = \alpha$.

<a id="pdf-7251cb8e4bc5-p212-b008"></a>
<!-- pdf-source: page=212; block=8; confidence=0.90 -->
**Definition.** Let $K$ be a field and $F \subseteq K$ closed under addition and multiplication. Then $F$ is itself a field, written $F \trianglelefteq K$ (subfield), and $K \trianglerighteq F$ ($K$ extends $F$).

<a id="pdf-7251cb8e4bc5-p212-b009"></a>
<!-- pdf-source: page=212; block=9; confidence=0.95 -->
**Proposition B.5.6.** If $K \trianglerighteq F$, then $K$ is an $F$-vector space, so $|K| = |F|^n$ where $n = \dim_F K$. Furthermore there is a unique copy of $F$ in $K$.

<a id="pdf-7251cb8e4bc5-p212-b010"></a>
<!-- pdf-source: page=212; block=10; confidence=0.94 -->
**Proof.** $K$ being an $F$-vector space follows from the definitions, giving the cardinality claim. Uniqueness of the copy of $F$ follows since elements of $F$ satisfy $X^q - X = 0$ with $q = |F|$, and this polynomial has at most $q$ roots.

<a id="pdf-7251cb8e4bc5-p213-b001"></a>
<!-- pdf-source: page=213; block=1; confidence=0.94 -->
### B.5.3 Existence of Finite Fields

Notation for modular reduction of polynomials: for a field $\mathbb{F}$ and $f,g \in \mathbb{F}[X]$, $f \bmod g$ is the remainder on dividing $f$ by $g$, so $\deg(f \bmod g) < \deg(g)$ and $g \mid (f - (f \bmod g))$. Set $f +_g h = (f+h) \bmod g$ and $f \cdot_g h = (fh) \bmod g$. An irreducible polynomial in $\mathbb{F}_q[X]$ has no nontrivial factor (Definition 5.1.6).

<a id="pdf-7251cb8e4bc5-p213-b002"></a>
<!-- pdf-source: page=213; block=2; confidence=0.97 -->
**Proposition B.5.7.** Let $\mathbb{F}$ be a finite field of cardinality $q$ and $g \in \mathbb{F}[X]$ irreducible of degree $n$. Then $(\mathbb{F}[X]/g, +_g, \cdot_g)$ is a field of cardinality $q^n$.

<a id="pdf-7251cb8e4bc5-p213-b003"></a>
<!-- pdf-source: page=213; block=3; confidence=0.90 -->
**Proof (sketch).** Every $f \in \mathbb{F}[X]$ splits completely (into linear factors) over some extension $K$ of $\mathbb{F}$. Working one irreducible factor at a time: if $g$ is an irreducible factor of $f$, form $L = \mathbb{F}[Z]/g(Z)$; then $Z$ is a root of $g$ (since $g(Z) \equiv 0$ in $L$), hence of $f$, so $f$ splits further in $L$. Repeat until $f$ splits completely in some field $K$. (Uses Theorem 5.1.7.)

<a id="pdf-7251cb8e4bc5-p213-b004"></a>
<!-- pdf-source: page=213; block=4; confidence=0.92 -->
**Proof (cont.).** Take $f(X) = X^{p^n} - X$ in $\mathbb{F}_p[X]$ and let $K$ be a field in which it splits completely. Let $S = \{\alpha \in K \mid f(\alpha) = 0\}$. $S$ is closed under multiplication: $f(\alpha) = 0 \iff \alpha^{p^n} = \alpha$, so if $\alpha^{p^n} = \alpha$ and $\beta^{p^n} = \beta$ then $(\alpha\beta)^{p^n} = \alpha^{p^n}\beta^{p^n} = \alpha\beta$, giving $\alpha\beta \in S$.

<a id="pdf-7251cb8e4bc5-p213-b005"></a>
<!-- pdf-source: page=213; block=5; confidence=0.95 -->
**Proposition B.5.8.** Let $K$ be a field of characteristic $p$ and $A, B \in K[X,Y]$. Then for all positive integers $n$, $(A+B)^{p^n} = A^{p^n} + B^{p^n}$. (Proof: $\binom{p}{i} \equiv 0 \pmod p$ unless $p \mid i$; Exercise B.5. Needed only for $A,B \in K$.)

<a id="pdf-7251cb8e4bc5-p213-b006"></a>
<!-- pdf-source: page=213; block=6; confidence=0.95 -->
**Proof (cont.).** Applying Proposition B.5.8 to $\alpha,\beta \in S$: $(\alpha+\beta)^{p^n} = \alpha^{p^n} + \beta^{p^n} = \alpha + \beta$, so $S$ is closed under addition. Thus $S$, being closed under addition and multiplication and contained in $K$, is a field once shown to have exactly $p^n$ elements. Note $S$ contains all roots of $f$, and $f$ has no multiple roots — proved generally via derivatives, but here [proof continues beyond page].

<a id="pdf-7251cb8e4bc5-p214-b001"></a>
<!-- pdf-source: page=214; block=1; confidence=0.90 -->
**Proof (continued).** To show $(X-\alpha)^2 \nmid X^{p^n}-X$, substitute $Z=X-\alpha$: equivalently $Z^2 \nmid (Z+\alpha)^{p^n}-(Z+\alpha)=Z^{p^n}-Z+\alpha^{p^n}-\alpha$, which fails since the coefficient of $Z$ is $-1\neq 0$. Hence $X^{p^n}-X$ has $p^n$ distinct roots. Since $S$ contains all of them, $|S|\ge p^n$; and since every element of $S$ is a root and the polynomial has at most $p^n$ roots, $|S|=p^n$. Thus a field of cardinality $p^n$ exists.

<a id="pdf-7251cb8e4bc5-p214-b002"></a>
<!-- pdf-source: page=214; block=2; confidence=0.95 -->
**Theorem B.5.9.** Every finite field $F$ has characteristic $p$ for some prime $p$ and cardinality $p^n$ for some positive integer $n$. Conversely, for every prime $p$ and positive integer $n$ there is a field of cardinality $p^n$. (First part from Proposition B.5.2, second from Proposition B.5.7.)

<a id="pdf-7251cb8e4bc5-p214-b003"></a>
<!-- pdf-source: page=214; block=3; confidence=0.97 -->
**B.5.4 Uniqueness of finite fields**

<a id="pdf-7251cb8e4bc5-p214-b004"></a>
<!-- pdf-source: page=214; block=4; confidence=0.90 -->
**Definitions (cyclic groups).** The cyclic group of order $n$ is $\mathbb{Z}_n=\{0,\dots,n-1\}$ under addition mod $n$; it has an element of order $n$ (namely $1$). For a group $G$, let $N^=(G,m)$ be the number of elements of order exactly $m$ and $N(G,m)$ the number of elements of order dividing $m$. Then $N(G,m)=\sum_{k\mid m}N^=(G,k)$. For $\mathbb{Z}_n$ and every $k\mid n$: $N(\mathbb{Z}_n,k)=k$ and $N^=(\mathbb{Z}_n,k)\ge 0$ (Exercise B.6).

<a id="pdf-7251cb8e4bc5-p214-b005"></a>
<!-- pdf-source: page=214; block=5; confidence=0.95 -->
**Lemma B.5.10.** Let $q=|F|$ and $n=q-1$. For every $k$ dividing $n$, $N(F^*,k)=N(\mathbb{Z}_n,k)$ and $N^=(F^*,k)=N^=(\mathbb{Z}_n,k)$.

<a id="pdf-7251cb8e4bc5-p214-b006"></a>
<!-- pdf-source: page=214; block=6; confidence=0.90 -->
**Proof.** For $N(F^*,k)$: every $\alpha\in F^*$ is a root of $X^n-1$, and $X^k-1\mid X^n-1$, so $k$ elements of $F^*$ are roots of $X^k-1$; thus $N(F^*,k)=k=N(\mathbb{Z}_n,k)$. For $N^=$: by the inductive formula $\sum_{\ell\mid k}N^=(F^*,\ell)=N(F^*,k)=k=N(\mathbb{Z}_n,k)=\sum_{\ell\mid k}N^=(\mathbb{Z}_n,\ell)$; by induction $N^=(F^*,\ell)=N^=(\mathbb{Z}_n,\ell)$ for $\ell<k$, so the remaining terms match: $N^=(F^*,k)=N^=(\mathbb{Z}_n,k)$.

<a id="pdf-7251cb8e4bc5-p214-b007"></a>
<!-- pdf-source: page=214; block=7; confidence=0.88 -->
**Definition (primitive element).** $\omega\in F$ is primitive if $\omega^i\neq 1$ for $i<|F|-1$ and $\omega^{|F|-1}=1$. Since $N^=(F^*,n)$ counts primitive elements, Lemma B.5.10 gives at least one. With $p$ the smallest prime divisor of $n$: if $p<n/p$, $N^=(F^*,n)=N(F^*,n)-N(F^*,n/p)-N(F^*,p)=n-n/p-p>0$; if $n=p^2$, $N^=(F^*,n)=n-p>0$; if $n$ is prime, $N^=(F^*,n)=n>0$.

<a id="pdf-7251cb8e4bc5-p215-b001"></a>
<!-- pdf-source: page=215; block=1; confidence=0.95 -->
**Proposition B.5.11.** Every finite field $F$ has a primitive element; consequently its multiplicative group is cyclic.

<a id="pdf-7251cb8e4bc5-p215-b002"></a>
<!-- pdf-source: page=215; block=2; confidence=0.93 -->
**Definition (F-generator).** For $K$ extending $F$, an element $\alpha\in K$ is an $F$-generator of $K$ if every $\beta\in K$ equals $p(\alpha)$ for some polynomial $p\in F[X]$.

<a id="pdf-7251cb8e4bc5-p215-b003"></a>
<!-- pdf-source: page=215; block=3; confidence=0.92 -->
**Proposition B.5.12.** Let $K$ be a finite field and $\omega$ a primitive element of $K$. Then for every subfield $F\subseteq K$, $\omega$ is an $F$-generator of $K$. Consequently, for every extension $K\supseteq F$ there is an $F$-generator in $K$.

<a id="pdf-7251cb8e4bc5-p215-b004"></a>
<!-- pdf-source: page=215; block=4; confidence=0.88 -->
**Proof.** Let $p\in F[X]$ be the lowest-degree polynomial with $p(\omega)=0$, and $|F|=q$, $|K|=q^n$. Claim $\deg p=n$. If $\deg p>n$, then $1,\omega,\dots,\omega^n$ are $F$-linearly independent, forcing $|K|>q^n$. If $\deg p<n$, then $X,X^2,\dots,X^{q^n-1}$ mod $p$ take only $q^{\deg p}$ residues, so two coincide: $X^i=X^j+p\cdot f$ with $i\neq j$, $f\in F[X]$; substituting $\omega$ gives $\omega^i=\omega^j$, contradicting primitivity. Finally, every nonzero $\beta\in K$ is $X^j\bmod p$ evaluated at $\omega$ for some $0\le j<q^n$.

<a id="pdf-7251cb8e4bc5-p215-b005"></a>
<!-- pdf-source: page=215; block=5; confidence=0.90 -->
**Remark.** Generators show that field extensions can only be constructed via irreducible polynomials.

<a id="pdf-7251cb8e4bc5-p215-b006"></a>
<!-- pdf-source: page=215; block=6; confidence=0.94 -->
**Proposition B.5.13.** Let $K\supseteq F$ and let $\alpha$ be an $F$-generator of $K$. If $p\in F[X]$ is the minimal polynomial with $p(\alpha)=0$, then $p$ is irreducible and $K\cong F[X]/p$.

<a id="pdf-7251cb8e4bc5-p215-b007"></a>
<!-- pdf-source: page=215; block=7; confidence=0.90 -->
**Proof.** Irreducibility of $p$ follows from its minimality (Exercise B.8). The isomorphism is obtained by fixing $F\subseteq K$ and sending $\alpha\mapsto X$; this extends uniquely to an isomorphism (Exercise B.9).

<a id="pdf-7251cb8e4bc5-p215-b008"></a>
<!-- pdf-source: page=215; block=8; confidence=0.95 -->
**Proposition B.5.14.** If $f\in\mathbb{F}_p[X]$ is irreducible of degree $n$, then $f\mid X^{p^n}-X$.

<a id="pdf-7251cb8e4bc5-p215-b009"></a>
<!-- pdf-source: page=215; block=9; confidence=0.93 -->
**Proof.** $K=\mathbb{F}_p[X]/(f)$ is a field of cardinality $p^n$, so every $\alpha\in K$ satisfies $\alpha^{p^n}=\alpha$. In particular $X\in K$ satisfies it, so $X^{p^n}-X\equiv 0\pmod f$, i.e. $f\mid X^{p^n}-X$.

<a id="pdf-7251cb8e4bc5-p215-b010"></a>
<!-- pdf-source: page=215; block=10; confidence=0.96 -->
**Theorem B.5.15.** For every prime $p$ and integer $n$, there is a unique field of cardinality $p^n$ up to isomorphism.

<a id="pdf-7251cb8e4bc5-p216-b001"></a>
<!-- pdf-source: page=216; block=1; confidence=0.90 -->
**Proof.** Let $K,L$ both have cardinality $p^n$. Both contain a unique copy of $\mathbb{F}_p$; mapping $1_K\mapsto 1_L$ and extending additively gives a partial isomorphism of these copies. Take an $\mathbb{F}_p$-generator $\alpha\in K$ with minimal polynomial $f\in\mathbb{F}_p[X]$, irreducible of degree $n$, so $f\mid X^{p^n}-X$ (Proposition B.5.14). Since $X^{p^n}-X=\prod_{\beta\in L}(X-\beta)$, $L$ contains a root $\beta$ of $f$; the map $\alpha\mapsto\beta$ extends to an isomorphism $K\to L$ (Exercise B.10).

<a id="pdf-7251cb8e4bc5-p216-b002"></a>
<!-- pdf-source: page=216; block=2; confidence=0.97 -->
**B.5.5 The Trace and Norm maps**

<a id="pdf-7251cb8e4bc5-p216-b003"></a>
<!-- pdf-source: page=216; block=3; confidence=0.94 -->
**Definition B.5.16.** For $F=\mathbb{F}_q$ and $K=\mathbb{F}_{q^n}$, the Trace $\mathrm{Tr}=\mathrm{Tr}_{K\to F}$ is evaluation of $\mathrm{Tr}(X)=X+X^q+X^{q^2}+\cdots+X^{q^{n-1}}$, and the Norm is evaluation of $N(X)=X^{1+q+q^2+\cdots+q^{n-1}}$.

<a id="pdf-7251cb8e4bc5-p216-b004"></a>
<!-- pdf-source: page=216; block=4; confidence=0.92 -->
**Remark.** Trace and Norm map elements of $K$ into the subfield $F$ in a uniform way.

<a id="pdf-7251cb8e4bc5-p216-b005"></a>
<!-- pdf-source: page=216; block=5; confidence=0.94 -->
**Proposition B.5.17.** (1) Trace is $F$-linear: $\mathrm{Tr}(\alpha\cdot\beta+\gamma)=\alpha\cdot\mathrm{Tr}(\beta)+\mathrm{Tr}(\gamma)$ for $\alpha\in F$, $\beta,\gamma\in K$. (2) Norm is multiplicative: $N(\beta\cdot\gamma)=N(\beta)N(\gamma)$. (3) Trace is a $q^{n-1}$-to-one map from $K$ to $F$. (4) Norm is a $(q^n-1)/(q-1)$-to-one map from $K^*$ to $F^*$.

<a id="pdf-7251cb8e4bc5-p216-b006"></a>
<!-- pdf-source: page=216; block=6; confidence=0.90 -->
**Proof.** (1) From $(\alpha\beta+\gamma)^{q^i}=\alpha^{q^i}\beta^{q^i}+\gamma^{q^i}$ and $\alpha^{q^i}=\alpha$. (2) Immediate from the definition. (3) $\mathrm{Tr}(\beta)^q=\beta^q+\cdots+\beta^{q^n}=\mathrm{Tr}(\beta)$ (using $\beta^{q^n}=\beta$), so the range is $F$; as a degree-$q^{n-1}$ polynomial it attains each value at most $q^{n-1}$ times, and with domain of size $q^n$ and range of size $q$ it attains each exactly $q^{n-1}$ times. (4) Similarly $N(\beta)^q=N(\beta)$ (Exercise B.11) and $N(\beta)\neq 0$ iff $\beta\neq 0$; the degree of $N$ and counting show it is regular on nonzero values.

<a id="pdf-7251cb8e4bc5-p217-b001"></a>
<!-- pdf-source: page=217; block=1; confidence=0.95 -->
The Trace map $K\to F$ is significant because it represents every $F$-linear map $K\to F$, as formalized next.

<a id="pdf-7251cb8e4bc5-p217-b002"></a>
<!-- pdf-source: page=217; block=2; confidence=0.98 -->
**Proposition B.5.18.** A function $L:K\to F$ is $F$-linear if and only if there exists $\lambda\in K$ with $L(\beta)=\mathrm{Tr}(\lambda\beta)$ for every $\beta\in K$.

<a id="pdf-7251cb8e4bc5-p217-b003"></a>
<!-- pdf-source: page=217; block=3; confidence=0.95 -->
**Proof.** ($\Leftarrow$) $f(\beta)=\mathrm{Tr}(\lambda\beta)$ is $F$-linear: for $\alpha\in F$, $\beta,\gamma\in K$, $f(\alpha\beta+\gamma)=\mathrm{Tr}(\lambda(\alpha\beta+\gamma))=\mathrm{Tr}(\lambda\alpha\beta)+\mathrm{Tr}(\lambda\gamma)=\alpha\,\mathrm{Tr}(\lambda\beta)+\mathrm{Tr}(\lambda\gamma)=\alpha f(\beta)+f(\gamma)$, using Proposition B.5.17.

($\Rightarrow$) Counting argument. If $\lambda\neq0$, then $f_\lambda(\beta)=\mathrm{Tr}(\lambda\beta)$ is not identically zero: as a polynomial in $Z$ it has degree $|K|/|F|$ and the coefficient of $Z$ is nonzero. By linearity $f_\lambda-f_\tau=f_{\lambda-\tau}\neq0$ for $\lambda\neq\tau$, so (including $\lambda=0$) there are at least $|K|$ distinct functions $f_\lambda$. There are also at most $|K|$: take an $F$-linearly independent basis $\beta_1,\dots,\beta_n$ of $K$ (with $n=[K:F]$), i.e. $\sum_{i=1}^n\alpha_i\beta_i\neq0$ for $(\alpha_1,\dots,\alpha_n)\in F^n\setminus\{0\}$; every $\beta=\sum_i\alpha_i\beta_i$. Any linear $L$ is determined by $L(\beta_1),\dots,L(\beta_n)$ since $L(\beta)=\sum_i\alpha_i L(\beta_i)$, so the count is $\le|F|^n=|K|$. Hence there are exactly $|K|$ $F$-linear maps $K\to F$, and they are exactly the Trace functions $f_\lambda$. $\square$

<a id="pdf-7251cb8e4bc5-p217-b004"></a>
<!-- pdf-source: page=217; block=4; confidence=0.97 -->
**B.6 Algorithmic aspects of Finite Fields.** How to represent finite fields and compute field operations efficiently.

<a id="pdf-7251cb8e4bc5-p217-b005"></a>
<!-- pdf-source: page=217; block=5; confidence=0.95 -->
Let $q=p^t$ ($p$ prime, $t\ge1$); goal is to work with $F_q$. If $O(q^2)$ space is acceptable, four lookup tables (addition, multiplication, additive and multiplicative inverses) make each operation a single lookup. The following sections give more succinct representations with operations still polynomial in $\log q$.

<a id="pdf-7251cb8e4bc5-p218-b001"></a>
<!-- pdf-source: page=218; block=1; confidence=0.95 -->
**B.6.1 Prime Fields.** For $t=1$, represent the field by the prime $p$, using $\log_2 p+1=\log q+1$ bits. Addition and multiplication reduce to computing the remainder mod $p$, costing $O((\log p)^2)$ naively, improvable to $O((\log p)(\log\log p)^2)$.

<a id="pdf-7251cb8e4bc5-p218-b002"></a>
<!-- pdf-source: page=218; block=2; confidence=0.93 -->
**B.6.2 General fields as vectors.** Use the isomorphism $F_{p^t}\cong F_p^t$, representing elements as vectors ($O(\log q)$ bits); addition is coordinatewise $F_p$-addition. Multiplication needs extra data: store $t^2$ vectors $w_{ij}\in F_p^t$ with $w_{ij}=e_i\cdot e_j$ (unit vectors $e_i$). Then $u\cdot v=\sum_{i=1}^t\sum_{j=1}^t u_i v_j w_{ij}$. This gives $O(t^3(\log p)^2)=O((\log q)^3)$ multiplication time and $O(t^3\log p)$ bits of storage.

<a id="pdf-7251cb8e4bc5-p218-b003"></a>
<!-- pdf-source: page=218; block=3; confidence=0.93 -->
**B.6.3 General fields as polynomial rings.** Use $F_{p^t}\cong F_p[X]/(g)$ for any irreducible $g$ of degree $t$. An element is a polynomial in $F_p[X]$ of degree $<t$, stored as its coefficient vector. Addition is coordinatewise, $O(t(\log p)^2)$; multiplication is polynomial multiplication then remainder mod $g$, naively $O(t^2(\log p)^2)$. Only $p$ and $g$ need storing, $O(t\log p)$ bits. This outperforms the vector-space representation in nearly all respects.

<a id="pdf-7251cb8e4bc5-p218-b004"></a>
<!-- pdf-source: page=218; block=4; confidence=0.92 -->
**B.6.4 Finding primes and irreducible polynomials.** Given a field specified by its cardinality $q=p^t$, one enumerates candidate $(p,t)$ pairs: there are $\log q$ possible values of $t$.

<a id="pdf-7251cb8e4bc5-p219-b001"></a>
<!-- pdf-source: page=219; block=1; confidence=0.93 -->
Only the pair with the largest $t$ can have prime $p$. Primality can be tested efficiently by randomization, and deterministically in time $\mathrm{poly}(\log q)$ by a recent result [1]. For $t=1$ nothing more is needed; for $t>1$ one must find an irreducible polynomial $g$ of degree $t$, addressed by several approaches.

<a id="pdf-7251cb8e4bc5-p219-b002"></a>
<!-- pdf-source: page=219; block=2; confidence=0.94 -->
**Randomized.** A random $g\in F_p[X]$ of degree $t$ is irreducible with probability $\ge 1/t$; irreducibility is testable in $\mathrm{poly}(\log q)$ time. Sampling until success takes expected $\mathrm{poly}(\log q)$ time (Algorithm 5.1.1).

<a id="pdf-7251cb8e4bc5-p219-b003"></a>
<!-- pdf-source: page=219; block=3; confidence=0.94 -->
**Deterministic.** Shoup [66] deterministically finds an irreducible degree-$t$ polynomial in $F_p[X]$ in time $\mathrm{poly}(t,p)$; the $p$-dependence is worse than ideal but fine when $p$ is small (e.g. $p<t$).

<a id="pdf-7251cb8e4bc5-p219-b004"></a>
<!-- pdf-source: page=219; block=4; confidence=0.90 -->
**Explicit.** For rare $(p,t)$ choices, explicit irreducible polynomials are known and usable when the field size fits; one family follows.

<a id="pdf-7251cb8e4bc5-p219-b005"></a>
<!-- pdf-source: page=219; block=5; confidence=0.97 -->
**Proposition B.6.1** ([47])**.** Let $p=2$ and $t=2\cdot 3^\ell$ for any non-negative integer $\ell$. Then $X^t+X^{t/2}+1$ is irreducible in $F_2[X]$.

<a id="pdf-7251cb8e4bc5-p219-b006"></a>
<!-- pdf-source: page=219; block=6; confidence=0.95 -->
**B.7 Algorithmic aspects of Polynomials.** Basic algorithmic tasks on polynomials, progressing to factoring and root-finding.

<a id="pdf-7251cb8e4bc5-p219-b007"></a>
<!-- pdf-source: page=219; block=7; confidence=0.95 -->
**B.7.1 Adding, Multiplying, Dividing.** For $f,g\in F_q[X]$ of degree $\le n$: addition costs $O(n)$ operations in $F_q$; multiplication costs $O(n^2)$ by long multiplication; the quotient and remainder of $f$ divided by $g$ cost $O(n^2)$ by long division. More efficient methods achieve $O(n(\log n)^c)$ field operations for some constant $c$ (see [74]).

<a id="pdf-7251cb8e4bc5-p220-b001"></a>
<!-- pdf-source: page=220; block=1; confidence=0.98 -->
## B.7.2 Greatest Common Divisor

<a id="pdf-7251cb8e4bc5-p220-b002"></a>
<!-- pdf-source: page=220; block=2; confidence=0.97 -->
**Definition B.7.1 (Greatest Common Divisor).** For polynomials $f, g \in F[X]$, their greatest common divisor $\gcd(f,g)$ is the maximal-degree monic polynomial $h(X)$ (leading coefficient $1$) such that $h$ divides both $f$ and $g$.

<a id="pdf-7251cb8e4bc5-p220-b003"></a>
<!-- pdf-source: page=220; block=3; confidence=0.92 -->
The factor-and-intersect approach reduces $\gcd$ to factoring, which is the wrong direction. Instead Euclid's algorithm uses the reduction: if $\deg(g) < \deg(f)$ and $g \nmid f$, then $\gcd(f,g) = \gcd(g,r)$, where $f = q\cdot g + r$ with $\deg(r) < \deg(g)$ from the division algorithm. Each division step reduces the total degree, giving a polynomial-time algorithm; a clever implementation runs in $O(n(\log n)^c)$ time.

<a id="pdf-7251cb8e4bc5-p220-b004"></a>
<!-- pdf-source: page=220; block=4; confidence=0.98 -->
## B.7.3 Factoring and Root-Finding

<a id="pdf-7251cb8e4bc5-p220-b005"></a>
<!-- pdf-source: page=220; block=5; confidence=0.90 -->
**Theorem B.7.2.** There exists a constant $c$ and a randomized algorithm running in expected time $O((n \log q)^c)$ that factors degree-$n$ polynomials in $F_q[X]$. Furthermore, if $q = p^t$ for prime $t$, there is a deterministic algorithm with running time $O((npt)^c)$ for factoring.

<a id="pdf-7251cb8e4bc5-p220-b006"></a>
<!-- pdf-source: page=220; block=6; confidence=0.97 -->
**Definition B.7.3 (Root-Finding Problem).** Input: a polynomial $f \in F_q[X]$ of degree at most $n$, given as coefficients $f_0,\dots,f_n \in F_q$. Task: output the set of all roots $\{\alpha \in F_q \mid f(\alpha) = 0\}$.

<a id="pdf-7251cb8e4bc5-p221-b001"></a>
<!-- pdf-source: page=221; block=1; confidence=0.95 -->
The root-finding algorithm relies on the GCD algorithm plus two facts. First it uses the identity $X^q - X = \prod_{\alpha \in F_q}(X - \alpha)$.

<a id="pdf-7251cb8e4bc5-p221-b002"></a>
<!-- pdf-source: page=221; block=2; confidence=0.97 -->
**Lemma B.7.4.** A polynomial $f \in F_q[X]$ has a root in $F_q$ if and only if $\gcd(f, X^q - X) \neq 1$.

<a id="pdf-7251cb8e4bc5-p221-b003"></a>
<!-- pdf-source: page=221; block=3; confidence=0.94 -->
**Proof.** If $f$ has a root $\alpha$, then $X - \alpha$ divides $\gcd(f, X^q - X)$, so the gcd is nontrivial. Conversely, any factor of $X^q - X$ has the form $\prod_{\alpha \in S}(X - \alpha)$ for some $S \subseteq F_q$, so $\gcd(f, X^q - X)$ has this form; if it is nontrivial then $S \neq \emptyset$, and for every $\alpha \in S$, $X - \alpha \mid f$, so $f$ has a root in $S \subseteq F_q$. $\square$

<a id="pdf-7251cb8e4bc5-p221-b004"></a>
<!-- pdf-source: page=221; block=4; confidence=0.90 -->
Assuming $\gcd(f, X^q - X)$ is computable in time polynomial in $\deg(f)$ and $\log q$: set $g = \gcd(f, X^q - X)$. If $g \neq 1$, output $S_1 \cup S_2$ where $S_1$ = roots of $g$ and $S_2$ = roots of $f/g$; $S_2$ is found recursively (smaller degree). Computing $S_1$, where $g$ splits into distinct linear factors over $F_q$, needs new ideas exploiting that $X^q - X$ splits into high-degree sparse factors.

<a id="pdf-7251cb8e4bc5-p221-b005"></a>
<!-- pdf-source: page=221; block=5; confidence=0.97 -->
### Sparse high degree polynomials

<a id="pdf-7251cb8e4bc5-p221-b006"></a>
<!-- pdf-source: page=221; block=6; confidence=0.95 -->
A polynomial $h \in F[X]$ is **$t$-sparse** if at most $t$ of its coefficients are nonzero. Every $h$ is $(\deg(h)+1)$-sparse; e.g. $X^q - X$ is $2$-sparse.

<a id="pdf-7251cb8e4bc5-p221-b007"></a>
<!-- pdf-source: page=221; block=7; confidence=0.96 -->
**Lemma B.7.5.** Let $f \in F[X]$ have degree $n$ and let $h \in F[X]$ be a $t$-sparse polynomial of degree $D$. Then $h \bmod f$ and $\gcd(f,h)$ can be computed in time $\mathrm{poly}(n, t, \log D)$.

<a id="pdf-7251cb8e4bc5-p221-b008"></a>
<!-- pdf-source: page=221; block=8; confidence=0.90 -->
**Proof.** It suffices to compute $h \bmod f$ in time $\mathrm{poly}(n,t,\log D)$; then Euclid's algorithm gives $\gcd(f,h) = \gcd(f, h \bmod f)$ in time $\mathrm{poly}(n)$. Writing $h = \sum_{i=1}^{t} h_i X^{d_i}$, if each $h_i X^{d_i} \bmod f$ is computable in time $\mathrm{poly}(n, \log d_i)$, the $t$ results are summed in time $\mathrm{poly}(n,t)$. Each $X^d \bmod f$ is computed by repeated squaring: write $d = \sum_{j=0}^{\log_2 d} d_j 2^j$; compute $g_j = X^{2^j} \bmod f = g_{j-1}^2 \bmod f$ by successive squaring, then $X^d \bmod f = \prod_{j=0}^{\log_2 d} (g_j)^{d_j}$ using $\log d$ further multiplications. $\square$

<a id="pdf-7251cb8e4bc5-p222-b001"></a>
<!-- pdf-source: page=222; block=1; confidence=0.95 -->
**Proposition B.7.6.**
1. Let $F_q$ have odd characteristic (so $q$ is odd). Then $X^q - X = X \cdot (X^{(q-1)/2} - 1) \cdot (X^{(q-1)/2} + 1)$; i.e. $X^q - X$ factors into three $2$-sparse polynomials of degree at most $q/2$.
2. Let $q = 2^t$ for integer $t \ge 2$. Then $X^q - X = \mathrm{Tr}(X)\cdot(\mathrm{Tr}(X) - 1)$, where $\mathrm{Tr}(X) = \mathrm{Tr}_{F_q \to F_2}(X) = X + X^2 + X^4 + \cdots + X^{2^{r-1}}$ is the trace map from $F_q$ to $F_2$; i.e. $X^q - X$ factors into two $(2 + \log_2 q)$-sparse polynomials of degree $q/2$.

<a id="pdf-7251cb8e4bc5-p222-b002"></a>
<!-- pdf-source: page=222; block=2; confidence=0.92 -->
**Proof.** For odd $q$ the factorization is obvious by inspection; the only point to stress is that $(q-1)/2$ is an integer. For even $q$: the trace is a map $F_q \to F_2$, so every $\alpha \in F_q$ satisfies $\mathrm{Tr}(\alpha) \in \{0,1\}$, whence $X - \alpha \mid \mathrm{Tr}(X)\cdot(\mathrm{Tr}(X)-1)$ for every $\alpha$, so $X^q - X \mid \mathrm{Tr}(X)\cdot(\mathrm{Tr}(X)-1)$. Equality $X^q - X = \mathrm{Tr}(X)\cdot(\mathrm{Tr}(X)-1)$ follows since both sides have the same degree and leading coefficient $1$. $\square$

<a id="pdf-7251cb8e4bc5-p222-b003"></a>
<!-- pdf-source: page=222; block=3; confidence=0.97 -->
### Univariate Root finding algorithm

<a id="pdf-7251cb8e4bc5-p222-b004"></a>
<!-- pdf-source: page=222; block=4; confidence=0.88 -->
After reducing (via $g = \gcd(f, X^q - X)$) to $g$ splitting into distinct linear factors over $F_q$, take odd $q$ (using only that $X^q - X$ splits into sparse factors of degree $\le q/2$). If some root $\alpha$ of $g$ has $X - \alpha \mid (X^{(q-1)/2} - 1)$ while another root $\beta$ does not, then $g_1 = \gcd(g, X^{(q-1)/2} - 1)$ is a nontrivial factor and one recurses on $g_1$ and $g_2 = g/g_1$. To force this "lucky" split, apply a random affine change of variables: fix $a \in F_q^{*}$, $b \in F_q$ and set $g_{a,b}(X) = g((X - b)/a)$.

<a id="pdf-7251cb8e4bc5-p222-b005"></a>
<!-- pdf-source: page=222; block=5; confidence=0.95 -->
**Proposition B.7.7.** Let $g \in F_q[X]$ have distinct roots $\alpha \neq \beta$. Then:
1. The coefficients of $g_{a,b}$ can be computed efficiently from $a$, $b$, and the coefficients of $g$.
2. $g_{a,b}$ has $a\alpha + b$ and $a\beta + b$ as its roots.

<a id="pdf-7251cb8e4bc5-p223-b001"></a>
<!-- pdf-source: page=223; block=1; confidence=0.90 -->
**Proposition B.7.7 (3).** For $a\in\mathbb{F}_q^*$ and $b\in\mathbb{F}_q$ chosen uniformly at random and independently, the probability that exactly one of $a\alpha+b$ and $a\beta+b$ is a root of $X^{(q-1)/2}-1$ is at least $1/2$.

<a id="pdf-7251cb8e4bc5-p223-b002"></a>
<!-- pdf-source: page=223; block=2; confidence=0.90 -->
**Proof.** Parts (1) and (2) are straightforward. For (3): for any distinct $\gamma,\delta\in\mathbb{F}_q$ there is exactly one pair $a\in\mathbb{F}_q^*,\,b\in\mathbb{F}_q$ with $a\alpha+b=\gamma$ and $a\beta+b=\delta$. The fraction of distinct pairs $\gamma,\delta$ for which exactly one lies in the size-$(q-1)/2$ root set of $X^{(q-1)/2}-1$ is at least $1/2$ (exactly $1/2+1/(2q)$), giving the claimed bound.

<a id="pdf-7251cb8e4bc5-p223-b003"></a>
<!-- pdf-source: page=223; block=3; confidence=0.95 -->
**Algorithm B.7.1 (Root-Find$(\mathbb{F}_q,f)$).** Input: $\mathbb{F}_q$, $f(X)\in\mathbb{F}_q[X]$; output: the $\mathbb{F}_q$-roots of $f$.
1: $g\leftarrow\gcd(f,\,X^q-X)$.
2-3: if $g=1$ return $\varnothing$.
4: return Linear-Root-Find$(\mathbb{F}_q,g)\cup$ Root-Find$(\mathbb{F}_q,\,f/g)$.

<a id="pdf-7251cb8e4bc5-p223-b004"></a>
<!-- pdf-source: page=223; block=4; confidence=0.90 -->
**Algorithm B.7.2 (Linear-Root-Find$(\mathbb{F}_q,g)$).** Input: $\mathbb{F}_q$, $g(X)$; output: the $\mathbb{F}_q$-roots of $g$ when $g\mid X^q-X$.
1-2: if $\deg(g)=1$ return $\{\alpha\}$ where $g=X-\alpha$.
3-8: repeat — pick $a\in\mathbb{F}_q^*,\,b\in\mathbb{F}_q$ uniform and independent; $g_{a,b}\leftarrow g((X-b)/a)$; $h_1\leftarrow\gcd(g_{a,b},\,X^{(q-1)/2}-1)$; $g_1\leftarrow h_1(aX+b)$ — until $0<\deg(g_1)<\deg(g)$.
9: return Linear-Root-Find$(\mathbb{F}_q,g_1)\cup$ Linear-Root-Find$(\mathbb{F}_q,\,g/g_1)$.

<a id="pdf-7251cb8e4bc5-p223-b005"></a>
<!-- pdf-source: page=223; block=5; confidence=0.97 -->
**Lemma B.7.8.** Root-Find$(\mathbb{F}_q,f)$ outputs the multiset of roots of $f$ in expected time $\mathrm{poly}(n,\log q)$.

<a id="pdf-7251cb8e4bc5-p223-b006"></a>
<!-- pdf-source: page=223; block=6; confidence=0.92 -->
**Proof.** Let $n=\deg(f)$. Root-Find makes at most $n$ calls to Linear-Root-Find (a weak bound, chosen for simplicity).

<a id="pdf-7251cb8e4bc5-p224-b001"></a>
<!-- pdf-source: page=224; block=1; confidence=0.93 -->
**Proof (continued).** By Proposition B.7.7(3) the loop in Linear-Root-Find runs an expected constant number of iterations before a nontrivial split. The two recursive calls have degrees summing to $\deg(g)$, giving a recursion tree of size at most $n$ with each node doing $\mathrm{poly}(n,\log q)$ work (gcds and change of variable). Hence the overall expected running time is $\mathrm{poly}(n,\log q)$. $\square$

<a id="pdf-7251cb8e4bc5-p224-b002"></a>
<!-- pdf-source: page=224; block=2; confidence=0.90 -->
**Remark (deterministic variant, $q=p^t$).** Runs in time $\mathrm{poly}(n,p,t)$. Given $g(X)$, first find $f(X)$ with $0<\deg(f)<\deg(g)$ and $f(X)^p-f(X)\equiv 0\pmod{g(X)}$; this is a linear system over $\mathbb{F}_p$. Existence: if $g=g_1g_2$ with $g_1,g_2$ coprime, take $f\equiv a\pmod{g_1}$, $f\equiv b\pmod{g_2}$ for distinct $a,b\in\mathbb{F}_p$; by CRT such $f$ exists with degree $<\deg(g_1g_2)$. Then $f^p-f=\prod_{a\in\mathbb{F}_p}(f-a)$, and since $\gcd(g,\prod_a(f-a))=g$ but $g\nmid(f-a)$ for each $a$, some $\gcd(g,f-a)$ is nontrivial; enumerating $a\in\mathbb{F}_p$ yields a nontrivial factorization of $g$. This handles $g$ with a coprime factorization, which holds for root-finding via $\gcd(g,X^q-X)$. Deterministic time $\mathrm{poly}(n,p,t)$.

<a id="pdf-7251cb8e4bc5-p224-b003"></a>
<!-- pdf-source: page=224; block=3; confidence=0.95 -->
**Bivariate Root Finding.** $P(X)$ is a *root* of $R(X,Y)\in\mathbb{F}_q[X,Y]$ if $Y-P(X)$ divides $R(X,Y)$. The bivariate root-finding problem is solved in polynomial time below.

<a id="pdf-7251cb8e4bc5-p224-b004"></a>
<!-- pdf-source: page=224; block=4; confidence=0.96 -->
**Theorem B.7.9.** There is a randomized algorithm that, given $R(X,Y)\in\mathbb{F}_q[X,Y]$ of degree at most $D$ (as a coefficient list), outputs all its roots in expected time polynomial in $D$ and $\log q$. If $q=p^t$, there is also a deterministic algorithm outputting all roots in time polynomial in $p,t,D$.

<a id="pdf-7251cb8e4bc5-p224-b005"></a>
<!-- pdf-source: page=224; block=5; confidence=0.92 -->
**Proof.** Reduce to the univariate case. Find a monic irreducible $F(X)$ of degree $N$ with $D<N\le O(D)$. Set $\mathbb{F}_Q=\mathbb{F}_q[X]\bmod F(X)$ and view $R(X,Y)$ as $R_X(Y)\in\mathbb{F}_Q[Y]$. Find the roots $\alpha_1,\dots,\alpha_s\in\mathbb{F}_Q$ of $R_X$ (via Lemma B.7.8 or the deterministic root-finder of Theorem B.7.2). Interpret each $\alpha_i$ as $A_i(X)\in\mathbb{F}_q[X]$, and report all $A_i$ with $Y-A_i(X)$ dividing $R(X,Y)$. Correctness and run time are argued next.

<a id="pdf-7251cb8e4bc5-p225-b001"></a>
<!-- pdf-source: page=225; block=1; confidence=0.93 -->
**Proof (continued).** The output is a subset of the roots since membership is checked before output. Conversely every root is reported: if $Y-P(X)\mid R(X,Y)$ and $\alpha=P(X)\bmod F(X)$, then $Y-\alpha\mid R_X(Y)$. Indeed, writing $R(X,Y)=h(X,Y)(Y-P(X))$ and $h_X(Y)=h(X,Y)\bmod F(X)$ gives $h_X(Y)\cdot(Y-\alpha)=R(X,Y)\bmod F(X)=R_X(Y)$; hence correctness. Run time: $F(X)$ is found in expected time $\mathrm{poly}(N,\log q)$ (deterministically $\mathrm{poly}(N,p,t)$); univariate root-finding takes $\mathrm{poly}(N,\log Q)$ steps with $\log Q=N\log q$, each step a field operation in $\mathbb{F}_Q$ costing $\mathrm{poly}(N\log q)$. Taking $N=D+1$ gives expected time $\mathrm{poly}(D,\log q)$, and deterministic time $\mathrm{poly}(D,t,p)$ using the root-finder of Theorem B.7.2. $\square$

<a id="pdf-7251cb8e4bc5-p225-b002"></a>
<!-- pdf-source: page=225; block=2; confidence=0.98 -->
**B.8 Exercises.**

<a id="pdf-7251cb8e4bc5-p225-b003"></a>
<!-- pdf-source: page=225; block=3; confidence=0.95 -->
**Exercise B.1.** Let $R$ be a commutative ring. Prove: (1) if $a$ is a unit in $R$, then $b\cdot a=0$ iff $b=0$; (2) using (1) or otherwise, prove Proposition B.3.6.

<a id="pdf-7251cb8e4bc5-p225-b004"></a>
<!-- pdf-source: page=225; block=4; confidence=0.97 -->
**Exercise B.2.** Argue that every finite field $F$ has a finite characteristic $\mathrm{char}(F)$.

<a id="pdf-7251cb8e4bc5-p225-b005"></a>
<!-- pdf-source: page=225; block=5; confidence=0.96 -->
**Exercise B.3.** Let $F$ be a field with $p$ elements, $p$ prime. Argue that the map $1_F\mapsto 1$ extends to an isomorphism between $F$ and $\mathbb{Z}_p$.

<a id="pdf-7251cb8e4bc5-p225-b006"></a>
<!-- pdf-source: page=225; block=6; confidence=0.90 -->
**Exercise B.4.** Let $G$ be an abelian group with identity $1$ and $a\in G$. (1) The map $x\mapsto a\cdot x$ on $G$ is a bijection. (2) $\prod_{x\in G}x=a^{n}\cdot\prod_{x\in G}x$ (with $n=|G|$). (3) Use (2) or otherwise to prove Proposition B.5.4 for abelian groups.

<a id="pdf-7251cb8e4bc5-p225-b007"></a>
<!-- pdf-source: page=225; block=7; confidence=0.95 -->
**Exercise B.5.** For a prime $p$ and $0\le i\le p$, show that $\binom{p}{i}\bmod p=1$ if $i=0$ or $i=p$, and $0$ otherwise.

<a id="pdf-7251cb8e4bc5-p226-b001"></a>
<!-- pdf-source: page=226; block=1; confidence=0.95 -->
**Exercise B.6.** For every $k \mid n$, show $N(\mathbb{Z}_n, k) = k$, i.e. the number of elements of $\mathbb{Z}_n$ whose order divides $k$ is exactly $k$. Steps:
1. Prove $S_k = \{\,a\cdot \tfrac{n}{k} \mid 0 \le a < k\,\}$ is a subgroup of $\mathbb{Z}_n$.
2. Any $b \in \mathbb{Z}_n$ whose order divides $k$ satisfies $k\cdot b \bmod n = 0$.
3. Any $b \in \mathbb{Z}_n \setminus S_k$ satisfies $k\cdot b \bmod n \ne 0$.
4. Any $b \in S_k$ has order dividing $k$.
5. Conclude $S_k$ contains all elements of $\mathbb{Z}_n$ with order dividing $k$, hence $N(\mathbb{Z}_n, k) = k$.

<a id="pdf-7251cb8e4bc5-p226-b002"></a>
<!-- pdf-source: page=226; block=2; confidence=0.99 -->
**Exercise B.7.** If $k \mid n$, show that $X^k - 1$ divides $X^n - 1$.

<a id="pdf-7251cb8e4bc5-p226-b003"></a>
<!-- pdf-source: page=226; block=3; confidence=0.95 -->
**Exercise B.8.** Let $K$ be an extension of $F$ and let $\alpha$ be an $F$-generator of $K$. Let $p$ be the minimal polynomial in $F[X]$ with $p(\alpha) = 0$. Argue that $p$ is irreducible.

<a id="pdf-7251cb8e4bc5-p226-b004"></a>
<!-- pdf-source: page=226; block=4; confidence=0.95 -->
**Exercise B.9.** Same setup: $K$ extends $F$, $\alpha$ an $F$-generator of $K$, $p$ the minimal polynomial in $F[X]$ with $p(\alpha)=0$. Argue there is an isomorphism between $K$ and $F[X]/p$ obtained by fixing $F \subseteq K$ and sending $\alpha \mapsto X$, extended to all other elements.

<a id="pdf-7251cb8e4bc5-p226-b005"></a>
<!-- pdf-source: page=226; block=5; confidence=0.97 -->
**Exercise B.10.** Using the notation in the proof of Theorem B.5.15, prove that the map $\alpha \mapsto \beta$ can be extended to an isomorphism between $K$ and $L$.

<a id="pdf-7251cb8e4bc5-p226-b006"></a>
<!-- pdf-source: page=226; block=6; confidence=0.97 -->
**Exercise B.11.** Argue that for any $\beta \in \mathbb{F}_{q^n}$, the norm function satisfies $N(\beta)^q = N(\beta)$.
