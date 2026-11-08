<!-- generated-by: proofmatch local extraction -->
<!-- source-pdf-sha256: ffbe9c7b3306c5d5cf14b26b0e17943c1ca5d4a3c2fa7e215e985e16441e915d -->
<!-- extractor: pdfminer.six v20260107 -->

<!-- pdf-page: 1 -->
ANALYSIS OF BOOLEAN FUNCTIONS

Ryan O’Donnell

May 2021 arXiv Edition.

Copyright © Ryan O’Donnell, 2014, 2015, 2016, 2017, 2018, 2019, 2020, 2021.

Originally published April 2014 by Cambridge University Press.

Cover illustration by A. A. Williams.

Single paper or electronic copies for noncommercial personal use may be made without explicit permission from the

author or publisher. All other rights reserved.



<!-- pdf-page: 2 -->


<!-- pdf-page: 3 -->
To Zeynep,

for her unending support and encouragement.



<!-- pdf-page: 4 -->


<!-- pdf-page: 5 -->
Contents

Prefaces

List of Notation

Chapter 1. Boolean functions and the Fourier expansion

§1.1. On analysis of Boolean functions

ix

xiii

19

19

§1.2. The “Fourier expansion”: functions as multilinear polynomials 20

§1.3. The orthonormal basis of parity functions

§1.4. Basic Fourier formulas

§1.5. Probability densities and convolution

§1.6. Highlight: Almost linear functions and the BLR Test

§1.7. Exercises and notes

Chapter 2. Basic concepts and social choice

§2.1. Social choice functions

§2.2.

Inuences and derivatives

§2.3. Total inuence

§2.4. Noise stability

§2.5. Highlight: Arrow’s Theorem

§2.6. Exercises and notes

Chapter 3. Spectral structure and learning

§3.1. Low-degree spectral concentration

§3.2. Subspaces and decision trees

§3.3. Restrictions

Copyright © Ryan O’Donnell, 2014, 2015, 2016, 2017, 2018, 2019, 2020, 2021.

23

25

28

31

33

43

43

46

49

53

57

61

69

69

71

74

v



<!-- pdf-page: 6 -->
vi

Contents

§3.4. Learning theory

§3.5. Highlight: the Goldreich–Levin Algorithm

§3.6. Exercises and notes

Chapter 4. DNF formulas and small-depth circuits

§4.1. DNF formulas

§4.2. Tribes

§4.3. Random restrictions

§4.4. Håstad’s Switching Lemma and the spectrum of DNFs

§4.5. Highlight: LMN’s work on constant-depth circuits

§4.6. Exercises and notes

Chapter 5. Majority and threshold functions

78

82

85

93

93

96

98

100

103

107

113

§5.1. Linear threshold functions and polynomial threshold functions 113

§5.2. Majority, and the Central Limit Theorem

§5.3. The Fourier coefcients of Majority

§5.4. Degree-1 weight

§5.5. Highlight: Peres’s Theorem and uniform noise stability

§5.6. Exercises and notes

Chapter 6. Pseudorandomness and 2-polynomials

§6.1. Notions of pseudorandomness

§6.2.

2-polynomials

§6.3. Constructions of various pseudorandom functions

§6.4. Applications in learning and testing

§6.5. Highlight: Fooling

2-polynomials

§6.6. Exercises and notes

Chapter 7. Property testing, PCPPs, and CSPs

§7.1. Dictator testing

§7.2. Probabilistically Checkable Proofs of Proximity

§7.3. CSPs and computational complexity

§7.4. Highlight: Håstad’s hardness theorems

§7.5. Exercises and notes

Chapter 8. Generalized domains

§8.1. Fourier bases for product spaces

§8.2. Generalized Fourier formulas

Copyright © Ryan O’Donnell, 2014, 2015, 2016, 2017, 2018, 2019, 2020, 2021.

118

121

124

130

134

143

143

148

151

155

160

163

173

173

178

183

190

195

207

207

211



<!-- pdf-page: 7 -->
Contents

§8.3. Orthogonal decomposition

§8.4. p-biased analysis

§8.5. Abelian groups

§8.6. Highlight: Randomized decision tree complexity

§8.7. Exercises and notes

Chapter 9. Basics of hypercontractivity

§9.1. Low-degree polynomials are reasonable

§9.2. Small subsets of the hypercube are noise-sensitive

§9.3.

(2, q)- and (p, 2)-hypercontractivity for a single bit

§9.4. Two-function hypercontractivity and induction

§9.5. Applications of hypercontractivity

§9.6. Highlight: The Kahn–Kalai–Linial Theorem

§9.7. Exercises and notes

Chapter 10. Advanced hypercontractivity

§10.1. The Hypercontractivity Theorem for uniformly random bits

§10.2. Hypercontractivity of general random variables

§10.3. Applications of general hypercontractivity

§10.4. More on randomization/symmetrization

§10.5. Highlight: General sharp threshold theorems

§10.6. Exercises and notes

Chapter 11. Gaussian space and Invariance Principles

§11.1. Gaussian space and the Gaussian noise operator

§11.2. Hermite polynomials

§11.3. Borell’s Isoperimetric Theorem

§11.4. Gaussian surface area and Bobkov’s Inequality

§11.5. The Berry–Esseen Theorem

§11.6. The Invariance Principle

§11.7. Highlight: Majority Is Stablest Theorem

§11.8. Exercises and notes

Some tips

Bibliography

Index

vii

216

220

227

229

235

247

248

252

256

259

262

264

270

283

283

287

292

297

304

312

327

328

336

340

343

350

357

364

370

389

391

413

Copyright © Ryan O’Donnell, 2014, 2015, 2016, 2017, 2018, 2019, 2020, 2021.



<!-- pdf-page: 8 -->


<!-- pdf-page: 9 -->
Prefaces

Preface to the arXiv edition

The purpose of this May 2021 revision is to x 100+ small typos and er-
rors present in the rst edition, and to make the result available on arXiv.
The numbering of all theorems, denitions, exercises, etc. is unchanged; there
are only slight pagination differences. Essentially no new mathematical con-
tent has been added, despite plenty of progress in the eld; the book can be
considered a “snapshot” of analysis of Boolean functions circa 2014.

Preface to the rst edition

The subject of this textbook is the analysis of Boolean functions. Roughly
speaking, this refers to studying Boolean functions f : {0, 1}n → {0, 1} via their
Fourier expansion and other analytic means. Boolean functions are perhaps
the most basic object of study in theoretical computer science, and Fourier
analysis has become an indispensable tool in the eld. The topic has also
played a key role in several other areas of mathematics, from combinatorics,
random graph theory, and statistical physics, to Gaussian geometry, met-
ric/Banach spaces, and social choice theory.

The intent of this book is both to develop the foundations of the eld and
to give a wide (though far from exhaustive) overview of its applications. Each
chapter ends with a “highlight” showing the power of analysis of Boolean
functions in different subject areas: property testing, social choice, cryptog-
raphy, circuit complexity, learning theory, pseudorandomness, hardness of
approximation, concrete complexity, and random graph theory.

Copyright © Ryan O’Donnell, 2014, 2015, 2016, 2017, 2018, 2019, 2020, 2021.

ix



<!-- pdf-page: 10 -->
x

Prefaces

The book can be used as a reference for working researchers or as the basis
of a one-semester graduate-level course. The author has twice taught such a
course at Carnegie Mellon University, attended mainly by graduate students
in computer science and mathematics but also by advanced undergraduates,
postdocs, and researchers in adjacent elds. In both years most of Chapters 1–
5 and 7 were covered, along with parts of Chapters 6, 8, 9, and 11, and
some additional material on additive combinatorics. Nearly 500 exercises are
provided at the ends of the book’s chapters.

Acknowledgments

My foremost acknowledgment is to all of the people who have taught me
analysis of Boolean functions, especially Guy Kindler and Elchanan Mossel.
I also learned a tremendous amount from my advisor Madhu Sudan, and my
coauthors and colleagues Per Austrin, Eric Blais, Nader Bshouty, Ilias Di-
akonikolas, Irit Dinur, Uri Feige, Ehud Friedgut, Parikshit Gopalan, Venkat
Guruswami, Johan Håstad, Gil Kalai, Daniel Kane, Subhash Khot, Adam
Klivans, James Lee, Assaf Naor, Joe Neeman, Krzysztof Oleszkiewicz, Yuval
Peres, Oded Regev, Mike Saks, Oded Schramm, Rocco Servedio, Amir Shpilka,
Jeff Steif, Benny Sudakov, Li-Yang Tan, Avi Wigderson, Karl Wimmer, John
Wright, Yi Wu, Yuan Zhou, and many others. Ideas from all of them have
strongly informed this book.

Many thanks to my PhD students who suffered from my inattention dur-
ing the completion of this book: Eric Blais, Yuan Zhou, John Wright, and
David Witmer. I’d also like to thank the students who took my 2007 and 2012
courses on analysis of Boolean functions; special thanks to Deepak Bal, Carol
Wang, and Patrick Xia for their very helpful course writing projects.

Thanks to my editor Lauren Cowles for her patience and encouragement,
to the copyediting team of David Anderson and Rishi Gupta, and to Cam-
bridge University Press for welcoming the free online publication of this book.
Thanks also to Amanda Williams for the use of the cover image.

I’m very grateful to everyone who pointed out errors in earlier drafts of
this work: Amirali Abdullah, Stefan Alders, anon, Arda Antikacıo ˘glu, Albert
Atserias, Per Austrin, Deepak Bal, Paul Beame, Tim Black, Ravi Boppana,
Clément Canonne, Yongzhi Cao, Sankardeep Chakraborty, Bireswar Das, An-
drew Drucker, Kirill Elagin, John Engbers, Diodato Ferraioli, Magnus Find,
Michael Forbes, Malin Forsström, Matt Franklin, David Gajser, David García
Soriano, Dmitry Gavinsky, Daniele Gewurz, Mrinalkanti Ghosh, Sivakanth
Gopi, Tom Gur, Zachary Hamaker, Sean Harrap, Prahladh Harsha, Justin
Hilyard, Dmitry Itsykson, Hamidreza Jahanjou, Mitchell Johnston, Gautam

Copyright © Ryan O’Donnell, 2014, 2015, 2016, 2017, 2018, 2019, 2020, 2021.



<!-- pdf-page: 11 -->
Prefaces

xi

Kamath, Shiva Kaul, Brian Kell, Ohad Klein, Pravesh Kothari, Chin Ho
Lee, Euiwoong Lee, Holden Lee, Jerry Li, Noam Lifshitz, Chengyu Lin, Yang
Liu, Tengyu Ma, Mladen Mikša, Alexey Milovanov, Sidhanth Mohanty, Ash-
ley Montanaro, Tobias Müller, Aleksandar Nikolov, Krzysztof Oleszkiewicz,
Pavithra KS, David Pritchard, Juspreet Sandhu, Swagato Sanyal, Pranav
Senthilnathan, Igor Shinkar, Lior Silberman, Marla Slusky, Dmitry Sokolov,
Aravind Srinivasan, Jeffrey Steif, Avishay Tal, Li-Yang Tan, Roei Tell, Suresh
Venkatasubramanian, Marc Vinyals, Emanuele Viola, Poorvi Vora, Amos Wa-
terland, Jake Wellens, Ryan Williams, Karl Wimmer, Chung Hoi Wong, Xi
Wu, Yi Wu, Mingji Xia, Yuichi Yoshida, Shengyu Zhang, Yu Zhao, and Art-
sem Zhuk. Special thanks in this group to Matt Franklin and Li-Yang Tan;
extra-special thanks in this group to Noam Lifshitz and Jeff Steif.

I’m grateful to Denis Thérien for inviting me to lecture at the Barbados
Complexity Workshop, to Cynthia Dwork and the STOC 2008 PC for inviting
me to give a tutorial, and to the Simons Foundation who arranged for me
to co-organize a symposium together with Elchanan Mossel and Krzysztof
Oleskiewicz, all on the topic of analysis of Boolean functions. These opportu-
nities greatly helped me to crystallize my thoughts on the topic.

I worked on this book while visiting the Institute for Advanced Study in
2010–2011 (supported by the Von Neumann Fellowship and in part by NSF
grants DMS-0835373 and CCF-0832797); I’m very grateful to them for having
me and for the wonderful working environment they provided. The remain-
der of the work on this book was done at Carnegie Mellon; I’m of course very
thankful to my colleagues there and to the Department of Computer Science.
“Reasonable” random variables were named after the department’s “Reason-
able Person Principle”. I was also supported in this book-writing endeavor
by the National Science Foundation, specically grants CCF-0747250 and
CCF-1116594. As usual: “This material is based upon work supported by the
National Science Foundation under grant numbers listed above. Any opinions,
ndings and conclusions or recommendations expressed in this material are
those of the author and do not necessarily reect the views of the National
Science Foundation (NSF).”

Finally, I’d like to thank all of my colleagues, friends, and relatives who

encouraged me to write and to nish the book, Zeynep most of all.

– Ryan O’Donnell
Pittsburgh
October 2013

Copyright © Ryan O’Donnell, 2014, 2015, 2016, 2017, 2018, 2019, 2020, 2021.



<!-- pdf-page: 12 -->


<!-- pdf-page: 13 -->
List of Notation

◦

∇

¬

3

⊕
ˆ‖ f ˆ‖p
4

∨

∧

entry-wise multiplication of vectors

the gradient: ∇ f (x) = (D1 f (x), . . . , Dn f (x))
logical NOT

S 3 i is equivalent to i ∈ S

logical XOR (exclusive-or)

| f (γ)|p)1/p

(

γ∈ n
2

symmetric difference of sets;

i.e., S4T = {i : i is in exactly one of S, T}

logical OR

logical AND

∗
[zk]F(z)

the convolution operator
coefcient on zk in the power series F(z)

1A
1B
2A

#α

|α|

ANDn

A⊥

Aut( f )

0-1 indicator function for A

0-1 indicator random variable for event B

the set of all subsets of A

if α is a multi-index, denotes the number of nonzero com-
ponents of α

if α is a multi-index, denotes



i αi

the logical AND function on n bits: False unless all inputs
are True

{γ : γ · x = 0 for all x ∈ A}

the group of automorphisms of Boolean function f

Copyright © Ryan O’Donnell, 2014, 2015, 2016, 2017, 2018, 2019, 2020, 2021.

xiii



<!-- pdf-page: 14 -->
xiv

List of Notation

BitsToGaussiansd

M on input the bit matrix x ∈ {−1, 1}d×M, has output z ∈ d
equal to 1p
times the column-wise sum of x; if d is omitted
M
it’s taken to be 1

χ(b)

χS(x)

codim H

Cov[ f , g]

Di
dχ2(ϕ, 1)

deg( f )

deg

( f )

2

∆(x, y)
∆(π)( f )

δ(π)( f )

∆(π)(T )

δ(π)
i

(T )

∆y f

dist(g, h)

DNFsize( f )
DNFwidth( f )
DT( f )

DTsize( f )
dTV(ϕ, ψ)

2 , denotes (−1)b ∈

the complex numbers
when b ∈ n
when x ∈ n, denotes
denotes (−1)
for a subspace H ≤ n, denotes n − dim H

i∈S xi





i∈S xi, where S ⊆ [n]; when x ∈ n
2 ,

the covariance of f and g, Cov[ f ] = E[ f g] − E[ f ] E[g]
the ith discrete derivative: Di f (x) = f (x(i7→1))− f (x(i7→−1))
chi-squared distance of the distribution with density ϕ from
the uniform distribution

2

the degree of f ; the least k such that f is a real linear
combination of k-juntas

for Boolean-valued f , the degree of its
resentation

2-polynomial rep-

the Hamming distance, #{i : xi 6= yi}
the expected number of queries made by the best decision
tree computing f when the input bits are chosen from the
distribution π
the revealment of f ; i.e., min{maxi δ(π)
i
the expected number of queries made by randomized deci-
sion tree T when the input bits are chosen from the distri-
bution π

(T ) : T computes f }

the probability randomized decision tree T queries coor-
dinate i when the input bits are chosen from the distribu-
tion π

for f :
f (x + y) − f (x)

n

2 → 2, the function n

2 → 2 dened by ∆y f (x) =

the relative Hamming distance; i.e., the fraction of inputs
on which g and h disagree

least possible size of a DNF formula computing f

least possible width of a DNF formula computing f

least possible depth of a decision tree computing f

least possible size of a decision tree computing f

total variation distance between the distributions with den-
sities ϕ, ψ

Copyright © Ryan O’Donnell, 2014, 2015, 2016, 2017, 2018, 2019, 2020, 2021.



<!-- pdf-page: 15 -->
List of Notation

xv

Ei

EI

Ent[ f ]

[·]

Eπp
f ⊕ g

f ⊗ g

f ⊗d

f ∗n

f †

f +z

f +z
H

2
n
2

f even

〈 f , g〉

f H
f (i)
f ⊆J

f|z

f J|z

f =k

f ≤k

f odd

the ith expectation operator:

Ei f (x) = Exi

[ f (x1, . . . , xi−1, xi, xi+1, . . . , xn))]

the expectation over coordinates I operator

for a nonnegative function on a probability space, denotes
E[ f ln f ] − E[ f ] ln E[ f ]

[·]

an abbreviation for Ex∼π⊗n
if f : {−1, 1}m → {−1, 1} and g : {−1, 1}n → {−1, 1}, denotes
the function h : {−1, 1}m+n → {−1, 1} dened by h(x, y) =
f (x)g(y)

p

if f : {−1, 1}m → {−1, 1} and g : {−1, 1}n → {−1, 1}, denotes the
function h : {−1, 1}mn → {−1, 1} dened by h(x(1), . . . , x(m)) =
f (g(x(1)), . . . , g(x(m)))
if f : {−1, 1}n → {−1, 1}, then f ⊗d : {−1, 1}nd → {−1, 1} is de-
ned inductively by f ⊗1 = f , f ⊗(d+1) = f ⊗ f ⊗d

the n-fold convolution, f ∗ f ∗ · · · ∗ f

the Boolean dual dened by f †(x) = − f (−x)

2 , denotes the function f +z(x) = f (x + z)

n

2 → , z ∈ n

if f :
denotes ( f +z)H
the nite eld of size 2

the group (vector space) indexing the Fourier characters of
functions f :

n
2 →
the even part of f , ( f (x) + f (−x))/2

Ex[ f (x)g(x)]
n

2 → , H ≤ n
if f :
shorthand for f ({i}) when i ∈

2 , denotes the restriction of f to H

the function (depending only on the J coordinates) dened
f (S)χS
by f ⊆J(x) = Ex′
when f : {−1, 1}n →

)]; in particular, it’s

[ f (xJ, x′
J

S⊆J



J

if f : Ωn → , J ⊆ [n], and z ∈ ΩJ, denotes the restriction of
f given by xing the coordinates in J to z

if f : Ωn → , J ⊆ [n], and z ∈ ΩJ, denotes the restriction
of f given by xing the coordinates in J to z




|S|=k

|S|≤k

f (S) χS
f (S) χS

the odd part of f , ( f (x) − f (−x))/2

Copyright © Ryan O’Donnell, 2014, 2015, 2016, 2017, 2018, 2019, 2020, 2021.



<!-- pdf-page: 16 -->
xvi

p`

f (S)

F

S|J
f

f (z)

γ+(∂A)

G (v, p)

h j

hα

H j

Infi[ f ]
Inf(ρ)
[ f ]
i
˜InfJ[ f ]

˜Inf

b
J[ f ]

J
L2({−1, 1}n)

L2(G n)

L2(Ω, π)

Λρ(α, β)

Λρ(α)
L f

Li
ln x

log x

Majn

List of Notation

for p prime and ` ∈ +, denotes the nite eld of p` ele-
ments

the Fourier coefcient of f on character χS
for S ⊆ J ⊆ [n], denotes ̂f J|z(S)
the randomization/symmetrization of f , dened by f (r, x) =


S rS f =S(x)

the Gaussian Minkowski content of ∂A

the Erd˝os–Rényi random graph distribution, π
the jth (normalized) Hermite polynomial, h j = 1p

⊗(v
2)
p

H j

j!

n

n a multi-index, the n-variate (normalized) Her-
(z j)

for α ∈
j=1 hα j
mite polynomial hα(z) =
the jth probabilists’ Hermite polynomial, dened by exp(tz−
1
j! H j(z)t j
2 t2) =
the inuence of coordinate i on f

∞
j=0

1

the ρ-stable inuence, Stabρ[Di f ]
the coalitional inuence of J ⊆ [n] on f : {−1, 1}n → {−1, 1},
namely Pr

z∼{−1,1}J [ f J|z is not constant]

for b ∈ {−1, 1}, equals Pr

z∼{−1,1}J [ f J|z 6≡ −b] − Pr[ f = b]

if J ⊆ [n], denotes [n] \ J
denotes L2({−1, 1}n, π⊗n
1/2

)

if G is a nite abelian group, denotes the complex inner
product space of functions G n → with inner product 〈 f , g〉 =
Ex∼G n [ f (x)g(x)]
the inner product space of (square-integrable) functions
Ω → with inner product 〈 f , g〉 = Ex∼π[ f (x)g(x)]
Pr[z1 ≤ t, z2 ≤ t′], where z1, z2 are standard Gaussians
with correlation E[z1 z2] = ρ, and t = Φ−1(α), t′ = Φ−1(β)
denotes Λρ(α, α)
the Laplacian operator applied to the Boolean function f ,
dened by L f =
i=1 Li f (or, the Ornstein–Uhlenbeck oper-
ator if f is a function on Gaussian space)

n

the ith coordinate Laplacian operator: Li f = f − Ei f
loge x
log2 x
the majority function on n bits

Copyright © Ryan O’Donnell, 2014, 2015, 2016, 2017, 2018, 2019, 2020, 2021.



<!-- pdf-page: 17 -->
List of Notation

MaxInf[ f ]

[n]

+

<m
Nρ(x)

Nρ(z)

NSδ[ f ]
N(0, 1)
N(0, 1)d

N(µ, Σ)

ORn

φ

Φ

Φ

ϕA

φα

π⊗n

π1/2
πp
Prπp

[·]

≥0

RDT( f )

RSA(δ)

xvii

maxi{Infi[ f ]}
{1, 2, 3, . . . , n}

{0, 1, 2, 3, . . . }

{1, 2, 3, . . . }

{0, 1, . . . , m − 1}
when x ∈ {−1, 1}n, denotes the probability distribution gen-
erating a string ρ-correlated to x
when z ∈ n, denotes the probability distribution of ρz +


1 − ρ2 g where g ∼ N(0, 1)n

the noise sensitivity of f at δ; i.e., 1

2 − 1

2 Stab1−2δ[ f ]

the standard Gaussian distribution

the distribution of d independent standard Gaussians; i.e.,
N(0, I d×d)
for µ ∈ d and Σ ∈ d×d positive semidenite, the d-variate
Gaussian distribution with mean µ and covariance ma-
trix Σ

e−z2/2

the logical OR function on n bits: True unless all inputs are
False
the standard Gaussian pdf, φ(z) = 1p
2π
t
−∞ φ(z) dz

the standard Gaussian cdf, Φ(t) =

the standard Gaussian complementary cdf, Φ(t) =

∞
t φ(z) dz
the density function for the uniform probability distribu-
tion on A; i.e., 1A/ E[1A]
given functions φ0, . . . , φm−1 and a multi-index α, denotes
n

i=1 φαi

if π is a probability distribution on Ω, denotes the associ-
ated product probability distribution on Ωn

the uniform distribution on {−1, 1}

the “p-biased” distribution on bits: πp(−1) = p, πp(1) = 1− p
an abbreviation for Prx∼π⊗n
[·]
the real numbers

p

the nonnegative real numbers

the zero-error randomized decision tree complexity of f
the rotation sensitivity of A at δ; i.e., Pr[1A(z) 6= 1A(z′)] for
a cos δ-correlated pair (z, z′)

sens f (x)

the number of pivotal coordinates for f at x

Copyright © Ryan O’Donnell, 2014, 2015, 2016, 2017, 2018, 2019, 2020, 2021.



<!-- pdf-page: 18 -->
xviii

sgn(t)

Sn
sparsity( f )
sparsity( f )

Stabρ[ f ]

supp(α)

supp( f )

Tρ
Ti
ρ
Tr
U

Uρ
Var[ f ]

Vari

volγ(A)
Wk[ f ]
W>k[ f ]
x(i7→b)
x⊕i

x ∼ ϕ

xS

x ∼ A
x ∼ {−1, 1}n

(y, z)

̂n
m

List of Notation

+1 if t ≥ 0, −1 if t < 0

the symmetric group on [n]

Prx[ f (x) 6= 0]
|supp( f )|

the noise stability of f at ρ: E[ f (x) f (y)] where x, y are a
ρ-correlated pair

if α is a multi-index, denotes {i : αi 6= 0}
if f is a function, denotes the set of inputs where f is
nonzero
the noise operator: Tρ f (x) = E y∼Nρ(x)[ f (y)]
the operator dened by Ti

ρ f (x) = ρ f + (1 − ρ)Ei f

for r ∈ n, denotes the operator dened by T1
T2
r2
r1
the Gaussian isoperimetric function, U = φ ◦ Φ−1
the Gaussian noise operator: Uρ f (z) = Ez′∼Nρ(z)[ f (z′)]
the variance of f , Var[ f ] = E[ f 2] − E[ f ]2

· · · Tn
r n

the operator dened by
Vari f (x) = Varxi

[ f (x1, . . . , xi−1, xi, xi+1, . . . , xn))]

Prz∼N(0,1)n [z ∈ A], the Gaussian volume of A
the Fourier weight of f at degree k

the Fourier weight of f at degrees above k

the string (x1, . . . , xi−1, b, xi+1, . . . , xn)
(x1, . . . , xi−1, −xi, xi+1, . . . , xn)
the random variable x is chosen from the probability distri-
bution with density ϕ


i∈S xi, with the convention x; = 1

the random variable x is chosen uniformly from the set A
the random variable x is chosen uniformly from {−1, 1}n

if J ⊆ [n], y ∈ {−1, 1}J, z ∈ {−1, 1}J, denotes the natural com-
posite string in {−1, 1}n

the additive group of integers modulo m

the group indexing the Fourier characters of functions f :

n
m →

Copyright © Ryan O’Donnell, 2014, 2015, 2016, 2017, 2018, 2019, 2020, 2021.



<!-- pdf-page: 19 -->
Chapter 1

Boolean functions and
the Fourier expansion

In this chapter we describe the basics of analysis of Boolean functions. We
emphasize viewing the Fourier expansion of a Boolean function as its repre-
sentation as a real multilinear polynomial. The viewpoint based on harmonic
n
2 is mostly deferred to Chapter 3. We illustrate the use of basic
analysis over
Fourier formulas through the analysis of the Blum–Luby–Rubinfeld linearity
test.

1.1. On analysis of Boolean functions

This is a book about Boolean functions,

f : {0, 1}n → {0, 1}.

Here f maps each length-n binary vector, or string, into a single binary value,
or bit. Boolean functions arise in many areas of computer science and mathe-
matics. Here are some examples:

• In circuit design, a Boolean function may represent the desired behavior

of a circuit with n inputs and one output.

• In graph theory, one can identify v-vertex graphs G with length-

v
2
strings indicating which edges are present. Then f may represent a
property of such graphs; e.g., f (G) = 1 if and only if G is connected.



• In extremal combinatorics, a Boolean function f can be identied with
a “set system” F on [n] = {1, 2, . . . , n}, where sets X ⊆ [n] are identied
with their 0-1 indicators and X ∈ F if and only if f (X ) = 1.

Copyright © Ryan O’Donnell, 2014, 2015, 2016, 2017, 2018, 2019, 2020, 2021.

19



<!-- pdf-page: 20 -->
20

1. Boolean functions and the Fourier expansion

• In coding theory, a Boolean function might be the indicator function for

the set of messages in a binary error-correcting code of length n.

• In learning theory, a Boolean function may represent a “concept” with n

binary attributes.

• In social choice theory, a Boolean function can be identied with a “vot-

ing rule” for an election with two candidates named 0 and 1.

We will be quite exible about how bits are represented. Sometimes we
will use True and False; sometimes we will use −1 and 1, thought of as real
numbers. Other times we will use 0 and 1, and these might be thought of as
real numbers, as elements of the eld 2 of size 2, or just as symbols. Most
frequently we will use −1 and 1, so a Boolean function will look like

f : {−1, 1}n → {−1, 1}.

But we won’t be dogmatic about the issue.

We refer to the domain of a Boolean function, {−1, 1}n, as the Hamming
cube (or hypercube, n-cube, Boolean cube, or discrete cube). The name “Ham-
ming cube” emphasizes that we are often interested in the Hamming distance
between strings x, y ∈ {−1, 1}n, dened by

∆(x, y) = #{i : xi 6= yi}.

Here we’ve used notation that will arise constantly: x denotes a bit string,
and xi denotes its ith coordinate.

Suppose you have a problem involving Boolean functions with the follow-

ing two characteristics:

• the Hamming distance is relevant;

• you are counting strings, or the uniform probability distribution on

{−1, 1}n is involved.

These are the hallmarks of a problem for which analysis of Boolean functions
may help. Roughly speaking, this means deriving information about Boolean
functions by analyzing their Fourier expansion.

1.2. The “Fourier expansion”: functions as multilinear

polynomials

The Fourier expansion of a Boolean function f : {−1, 1}n → {−1, 1} is simply
its representation as a real, multilinear polynomial. (Multilinear means that
no variable xi appears squared, cubed, etc.) For example, suppose n = 2 and

Copyright © Ryan O’Donnell, 2014, 2015, 2016, 2017, 2018, 2019, 2020, 2021.



<!-- pdf-page: 21 -->
1.2. The “Fourier expansion”: functions as multilinear polynomials

21

f = max2, the “maximum” function on 2 bits:

max2(+1, +1) = +1,
max2(−1, +1) = +1,
max2(+1, −1) = +1,
max2(−1, −1) = −1.

Then max2 can be expressed as a multilinear polynomial,
max2(x1, x2) = 1

2 + 1
this is the “Fourier expansion” of max2. As another example, consider the
majority function on 3 bits, Maj3 : {−1, 1}3 → {−1, 1}, which outputs the ±1 bit
occurring more frequently in its input. Then it’s easy to verify the Fourier
expansion

2 x1 + 1

2 x2 − 1

2 x1x2;

(1.1)

2 x3 − 1

2 x2 + 1

2 x1x2x3.

Maj3(x1, x2, x3) = 1

2 x1 + 1
The functions max2 and Maj3 will serve as running examples in this chapter.
Let’s see how to obtain such multilinear polynomial representations in
general. Given an arbitrary Boolean function f : {−1, 1}n → {−1, 1} there is a
familiar method for nding a polynomial that interpolates the 2n values that
f assigns to the points {−1, 1}n ⊂ n. For each point a = (a1, . . . , an) ∈ {−1, 1}n
the indicator polynomial

(1.2)

1{a}(x) =

 



1+a1 x1
2

1+a2 x2
2





· · ·

1+an xn
2



takes value 1 when x = a and value 0 when x ∈ {−1, 1}n \ {a}. Thus f has the
polynomial representation

∑

f (x) =

a∈{−1,1}n

f (a)1{a}(x).

Illustrating with the f = max2 example again, we have

max2(x) = (+1)

+ (+1)

+ (+1)

+ (−1)











 

 

 

 

1+x2
2
1+x2
2
1−x2
2
1−x2
2

1+x1
2
1−x1
2
1+x1
2
1−x1
2







(1.3)

= 1

2 + 1

2 x1 + 1

2 x2 − 1

2 x1x2.

Let us make two remarks about this interpolation procedure. First, it works
equally well in the more general case of real-valued Boolean functions, f :
{−1, 1}n → . Second, since the indicator polynomials are multilinear when
expanded out, the interpolation always produces a multilinear polynomial.
Indeed, it makes sense that we can represent functions f : {−1, 1}n → with
multilinear polynomials: since we only care about inputs x where xi = ±1, any
factor of x2
i

can be replaced by 1.

Copyright © Ryan O’Donnell, 2014, 2015, 2016, 2017, 2018, 2019, 2020, 2021.



<!-- pdf-page: 22 -->
22

1. Boolean functions and the Fourier expansion

We have illustrated that every f : {−1, 1}n → can be represented by a
real multilinear polynomial; as we will see in Section 1.3, this representation
is unique. The multilinear polynomial for f may have up to 2n terms, corre-
sponding to the subsets S ⊆ [n]. We write the monomial corresponding to S
as

∏

xS =

xi

(with x; = 1 by convention),

and we use the following notation for its coefcient:

i∈S

f (S) = coefcient on monomial xS in the multilinear representation of f .

This discussion is summarized by the Fourier expansion theorem:

Theorem 1.1. Every function f : {−1, 1}n → can be uniquely expressed as a
multilinear polynomial,

∑

f (x) =

f (S) xS.

(1.4)

S⊆[n]
This expression is called the Fourier expansion of f , and the real number f (S)
is called the Fourier coefcient of f on S. Collectively, the coefcients are
called the Fourier spectrum of f .

As examples, from (1.1) and (1.2) we obtain:
2 , Émax2({1}) = 1
ÅMaj3({1}), ÅMaj3({2}), ÅMaj3({3}) = 1

2 , Émax2({2}) = 1
2 , ÅMaj3({1, 2, 3}) = − 1

Émax2(;) = 1

2 , ÅMaj3(S) = 0 else.
We nish this section with some notation. It is convenient to think of the

2 , Émax2({1, 2}) = − 1
2 ;

monomial xS as a function on x = (x1, . . . , xn) ∈ n; we write it as

χS(x) =

xi.

∏

i∈S

Thus we sometimes write the Fourier expansion of f : {−1, 1}n → as

∑

f (x) =

f (S) χS(x).

S⊆[n]

So far our notation makes sense only when representing the Hamming cube
by {−1, 1}n ⊆ n. The other frequent representation we will use for the cube
n
is
2 → by
“encoding” input bits 0, 1 ∈ 2 by the real numbers −1, 1 ∈ . We choose the
encoding χ :

n
2 . We can dene the Fourier expansion for functions f :

2 → dened by

χ(0

2

) = +1, χ(1

) = −1.

2

This encoding is not so natural from the perspective of Boolean logic; e.g., it
means the function max2 we have discussed represents logical AND. But it’s
mathematically natural because for b ∈ 2 we have the formula χ(b) = (−1)b.
We now extend the χS notation:

Copyright © Ryan O’Donnell, 2014, 2015, 2016, 2017, 2018, 2019, 2020, 2021.



<!-- pdf-page: 23 -->
1.3. The orthonormal basis of parity functions

23

Denition 1.2. For S ⊆ [n] we dene χS :

∏

χS(x) =

χ(xi) = (−1)

n
2 → by

i∈S xi ,

which satises

i∈S

χS(x + y) = χS(x)χS(y).

(1.5)

In this way, given any function f :

n
2 → it makes sense to write its

Fourier expansion as

f (x) =

∑

S⊆[n]

f (S) χS(x).

In fact, if we are really thinking of

2, it makes sense to identify subsets S ⊆ [n] with vectors γ ∈ n

n
2 the n-dimensional vector space over
2 . This will

be discussed in Chapter 3.2.

1.3. The orthonormal basis of parity functions

For x ∈ {−1, 1}n, the number χS(x) =
i∈S xi is in {−1, 1}. Thus χS : {−1, 1}n →
{−1, 1} is a Boolean function; it computes the logical parity, or exclusive-or
(XOR), of the bits (xi)i∈S. The parity functions play a special role in the
analysis of Boolean functions: the Fourier expansion



∑

f =

f (S) χS

(1.6)

shows that any f can be represented as a linear combination of parity func-
tions (over the reals).

S⊆[n]

It’s useful to explore this idea further from the perspective of linear alge-
bra. The set of all functions f : {−1, 1}n → forms a vector space V , since we
can add two functions (pointwise) and we can multiply a function by a real
scalar. The vector space V is 2n-dimensional: if we like we can think of the
functions in this vector space as vectors in 2n , where we stack the 2n values
f (x) into a tall column vector (in some xed order). Here we illustrate the
Fourier expansion (1.1) of the max2 function from this perspective:




















max2 =











= (1/2)











+ (1/2)











+ (1/2)











+ (−1/2)











.

(1.7)

+1
+1
+1
+1

+1
−1
+1
−1

+1
+1
−1
−1

+1
+1
+1
−1

+1
−1
−1
+1

More generally, the Fourier expansion (1.6) shows that every function
f : {−1, 1}n → in V is a linear combination of the parity functions; i.e., the
parity functions are a spanning set for V . Since the number of parity functions
is 2n = dim V , we can deduce that they are in fact a linearly independent basis
for V . In particular this justies the uniqueness of the Fourier expansion
stated in Theorem 1.1.

Copyright © Ryan O’Donnell, 2014, 2015, 2016, 2017, 2018, 2019, 2020, 2021.



<!-- pdf-page: 24 -->
24

1. Boolean functions and the Fourier expansion

in V . The usual inner product on 2n would correspond to

We can also introduce an inner product on pairs of function f , g : {−1, 1}n →
x∈{−1,1}n f (x)g(x),
but it’s more convenient to scale this by a factor of 2−n, making it an average
rather than a sum. In this way, a Boolean function f : {−1, 1}n → {−1, 1} will
have 〈 f , f 〉 = 1, i.e., be a “unit vector”.



Denition 1.3. We dene an inner product 〈·, ·〉 on pairs of function f , g :
{−1, 1}n → by

〈 f , g〉 = 2−n

∑

f (x)g(x) =

E
x∼{−1,1}n

[ f (x)g(x)] .

(1.8)

We also use the notation ‖ f ‖2 =

x∈{−1,1}n


〈 f , f 〉, and more generally,

‖ f ‖p = E[| f (x)|p]1/p.

Here we have introduced probabilistic notation that will be used heavily

throughout the book:

Notation 1.4. We write x ∼ {−1, 1}n to denote that x is a uniformly chosen ran-
dom string from {−1, 1}n. Equivalently, the n coordinates xi are independently
chosen to be +1 with probability 1/2 and −1 with probability 1/2. We always
write random variables in boldface. Probabilities Pr and expectations E will
always be with respect to a uniformly random x ∼ {−1, 1}n unless otherwise
specied. Thus we might write the expectation in (1.8) as Ex[ f (x)g(x)] or
E[ f (x)g(x)] or even E[ f g].

Returning to the basis of parity functions for V , the crucial fact underlying

all analysis of Boolean functions is that this is an orthonormal basis.

Theorem 1.5. The 2n parity functions χS : {−1, 1}n → {−1, 1} form an orthonor-
mal basis for the vector space V of functions {−1, 1}n → ; i.e.,

〈χS, χT 〉 =



1 if S = T,

0 if S 6= T.

Recalling the denition 〈χS, χT 〉 = E[χS(x)χT (x)], Theorem 1.5 follows imme-
diately from two facts:

Fact 1.6. For x ∈ {−1, 1}n it holds that χS(x)χT (x) = χS4T (x), where S4T
denotes symmetric difference.

Proof. χS(x)χT (x) =

∏

∏

xi

xi =

∏

xi

∏

i∈S

i∈T

i∈S4T

i∈S∩T

x2
i =

∏

i∈S4T

xi = χS4T (x).



Fact 1.7. E[χS(x)] = E



∏



xi

=

i∈S

1 if S = ;,

0 if S 6= ;.

Copyright © Ryan O’Donnell, 2014, 2015, 2016, 2017, 2018, 2019, 2020, 2021.



<!-- pdf-page: 25 -->
1.4. Basic Fourier formulas

25

Proof. If S = ; then E[χS(x)] = E[1] = 1. Otherwise,

∏



∏

E

xi

=

E[xi]

because the random bits x1, . . . , xn are independent. But each of the factors

E[xi] in the above (nonempty) product is (1/2)(+1) + (1/2)(−1) = 0.

i∈S

i∈S

1.4. Basic Fourier formulas

As we have seen, the Fourier expansion of f : {−1, 1}n → can be thought
of as the representation of f over the orthonormal basis of parity functions
(χS)S⊆[n]. In this basis, f has 2n “coordinates”, and these are precisely the
Fourier coefcients of f . The “coordinate” of f in the χS “direction” is 〈 f , χS〉;
i.e., we have the following formula for Fourier coefcients:

Proposition 1.8. For f : {−1, 1}n → and S ⊆ [n], the Fourier coefcient of f
on S is given by

f (S) = 〈 f , χS〉 =

E
x∼{−1,1}n

[ f (x)χS(x)].

We can verify this formula explicitly:



〈 f , χS〉 =

f (T) χT , χS

=



∑

T⊆[n]

∑

T⊆[n]

f (T)〈χT , χS〉 = f (S),

(1.9)

where we used the Fourier expansion of f , the linearity of 〈·, ·〉, and nally
Theorem 1.5. This formula is the simplest way to calculate the Fourier coef-
cients of a given function; it can also be viewed as a streamlined version of
the interpolation method illustrated in (1.3). Alternatively, this formula can
be taken as the denition of Fourier coefcients.

The orthonormal basis of parities also lets us measure the squared “length”
(2-norm) of f : {−1, 1}n → efciently: it’s just the sum of the squares of f ’s
“coordinates” – i.e., Fourier coefcients. This simple but crucial fact is called
Parseval’s Theorem.

Parseval’s Theorem. For any f : {−1, 1}n → ,
∑

〈 f , f 〉 =

E
x∼{−1,1}n

[ f (x)2] =

f (S)2.

S⊆[n]

In particular, if f : {−1, 1}n → {−1, 1} is Boolean-valued then

∑

f (S)2 = 1.

As examples we can recall the Fourier expansions of max2 and Maj3:

S⊆[n]

max2(x) = 1

2 + 1

2 x1 + 1

2 x2 − 1

2 x1x2,

Maj3(x) = 1

2 x1 + 1

2 x2 + 1

2 x3 − 1

2 x1x2x3.

In both cases the sum of squares of Fourier coefcients is 4 × (1/4) = 1.

Copyright © Ryan O’Donnell, 2014, 2015, 2016, 2017, 2018, 2019, 2020, 2021.



<!-- pdf-page: 26 -->
26

1. Boolean functions and the Fourier expansion

More generally, given two functions f , g : {−1, 1}n → , we can compute
〈 f , g〉 by taking the “dot product” of their coordinates in the orthonormal basis
of parities. The resulting formula is called Plancherel’s Theorem.

Plancherel’s Theorem. For any f , g : {−1, 1}n → ,

〈 f , g〉 =

E
x∼{−1,1}n

[ f (x)g(x)] =

∑

S⊆[n]

f (S) g(S).

We can verify this formula explicitly as we did in (1.9):

〈 f , g〉 =

〈 ∑

∑

f (S) χS,

〉

g(T) χT

=

∑

f (S) g(T)〈χS, χT 〉 =

S⊆[n]

T⊆[n]

S,T⊆[n]

∑

S⊆[n]

f (S) g(S).

Now is a good time to remark that for Boolean-valued functions f , g :
{−1, 1}n → {−1, 1}, the inner product 〈 f , g〉 can be interpreted as a kind of “cor-
relation” between f and g, measuring how similar they are. Since f (x)g(x) = 1
if f (x) = g(x) and f (x)g(x) = −1 if f (x) 6= g(x), we have:

Proposition 1.9. If f , g : {−1, 1}n → {−1, 1},

〈 f , g〉 = Pr[ f (x) = g(x)] − Pr[ f (x) 6= g(x)] = 1 − 2dist( f , g).

Here we are using the following denition:

Denition 1.10. Given f , g : {−1, 1}n → {−1, 1}, we dene their (relative Ham-
ming) distance to be

the fraction of inputs on which they disagree.

dist( f , g) = Pr
x

[ f (x) 6= g(x)],

With a number of Fourier formulas now in hand we can begin to illustrate
a basic theme in the analysis of Boolean functions: interesting combinatorial
properties of a Boolean function f can be “read off ” from its Fourier coef-
cients. Let’s start by looking at one way to measure the “bias” of f :

Denition 1.11. The mean of f : {−1, 1}n → is E[ f ]. When f has mean 0 we
say that it is unbiased, or balanced. In the particular case that f : {−1, 1}n →
{−1, 1} is Boolean-valued, its mean is

E[ f ] = Pr[ f = 1] − Pr[ f = −1];

thus f is unbiased if and only if it takes value 1 on exactly half of the points
of the Hamming cube.
Fact 1.12. If f : {−1, 1}n → then E[ f ] = f (;).

This formula holds simply because E[ f ] = 〈 f , 1〉 = f (;) (taking S = ; in
Proposition 1.8). In particular, a Boolean function is unbiased if and only if
its empty-set Fourier coefcient is 0.

Next we obtain a formula for the variance of a real-valued Boolean func-

tion (thinking of f (x) as a real-valued random variable):

Copyright © Ryan O’Donnell, 2014, 2015, 2016, 2017, 2018, 2019, 2020, 2021.



<!-- pdf-page: 27 -->
1.4. Basic Fourier formulas

27

Proposition 1.13. The variance of f : {−1, 1}n → is

Var[ f ] = 〈 f − E[ f ], f − E[ f ]〉 = E[ f 2] − E[ f ]2 =

∑

S6=;

f (S)2.

The above Fourier formula follows immediately from Parseval’s Theorem and
Fact 1.12. We also have:

Fact 1.14. For f : {−1, 1}n → {−1, 1},

Var[ f ] = 1 − E[ f ]2 = 4 Pr[ f (x) = 1] Pr[ f (x) = −1] ∈ [0, 1].

In particular, a Boolean-valued function f has variance 1 if it’s unbiased
and variance 0 if it’s constant. More generally, the variance of a Boolean-
valued function is proportional to its “distance from being constant”.

Proposition 1.15. Let f : {−1, 1}n → {−1, 1}. Then 2≤ ≤ Var[ f ] ≤ 4≤, where

≤ = min{dist( f , 1), dist( f , −1)}.

The proof of Proposition 1.15 is an exercise. See also Exercise 1.17.

By using Plancherel in place of Parseval, we get a generalization of Propo-

sition 1.13 for covariance:

Proposition 1.16. The covariance of f , g : {−1, 1}n → is

Cov[ f , g] = 〈 f − E[ f ], g − E[g]〉 = E[ f g] − E[ f ] E[g] =

∑

S6=;

f (S) g(S).

We end this section by discussing the Fourier weight distribution of Boolean

functions.

Denition 1.17. The (Fourier) weight of f : {−1, 1}n → on set S is dened
to be the squared Fourier coefcient, f (S)2.

Although we lose some information about the Fourier coefcients when
we square them, many Fourier formulas only depend on the weights of f .
For example, Proposition 1.13 says that the variance of f equals its Fourier
weight on nonempty sets. Studying Fourier weights is particularly pleasant
for Boolean-valued functions f : {−1, 1}n → {−1, 1} since Parseval’s Theorem
says that they always have total weight 1. In particular, they dene a proba-
bility distribution on subsets of [n].

Denition 1.18. Given f : {−1, 1}n → {−1, 1}, the spectral sample for f , de-
noted S f , is the probability distribution on subsets of [n] in which the set S
has probability f (S)2. We write S ∼ S f for a draw from this distribution.

For example, the spectral sample for the max2 function is the uniform
distribution on all four subsets of [2]; the spectral sample for Maj3 is the
uniform distribution on the four subsets of [3] with odd cardinality.

Copyright © Ryan O’Donnell, 2014, 2015, 2016, 2017, 2018, 2019, 2020, 2021.



<!-- pdf-page: 28 -->
28

1. Boolean functions and the Fourier expansion

Given a Boolean function it can be helpful to try to keep a mental picture
of its weight distribution on the subsets of [n], partially ordered by inclu-
sion. Figure 1.1 is an example for the Maj3 function, with the white circles
indicating weight 0 and the shaded circles indicating weight 1/4.

[3]

{1,3}

{2}

{1,2}

{1}

{2,3}

{3}

Figure 1.1. Fourier weight distribution of the Maj3 function

Finally, as suggested by the diagram we often stratify the subsets S ⊆ [n]
according to their cardinality (also called “height” or “level”). Equivalently,
this is the degree of the associated monomial xS.

Denition 1.19. For f : {−1, 1}n → and 0 ≤ k ≤ n, the (Fourier) weight of f
at degree k is

∑

Wk[ f ] =

f (S)2.

If f : {−1, 1}n → {−1, 1} is Boolean-valued, an equivalent denition is

S⊆[n]
|S|=k

Wk[ f ] = Pr
S∼S f

[|S| = k].

By Parseval’s Theorem, Wk[ f ] = ‖ f =k‖2
∑

2 where
f (S) χS

f =k =

is called the degree k part of f . We will also sometimes use notation like
W>k[ f ] =

f (S)2 and f ≤k =





f (S) χS.

|S|>k

|S|≤k

|S|=k

1.5. Probability densities and convolution

n
2 rather
For variety’s sake, in this section we write the Hamming cube as
than {−1, 1}n. In developing the Fourier expansion, we have generalized from
n
Boolean-valued Boolean functions f :
2 → {−1, 1} to real-valued Boolean func-
n
tions f :
2 → . Boolean-valued functions arise more often in combinatorial
problems, but there are important classes of real-valued Boolean functions.
One example is probability densities.

Copyright © Ryan O’Donnell, 2014, 2015, 2016, 2017, 2018, 2019, 2020, 2021.



<!-- pdf-page: 29 -->
1.5. Probability densities and convolution

Denition 1.20. A (probability) density function on the Hamming cube
is any nonnegative function ϕ :

n

2 → ≥0 satisfying
E
x∼ n
2

[ϕ(x)] = 1.

29

n
2

We write y ∼ ϕ to denote that y is a random string drawn from the associated
probability distribution, dened by

[y = y] = ϕ(y)

Pr
y∼ϕ

1
2n

∀y ∈ n
2 .

Here you should think of ϕ(y) as being the relative density of y with

respect to the uniform distribution on n

2 . For example, we have:

Fact 1.21. If ϕ is a density function and g :

E
y∼ϕ

[g(y)] = 〈ϕ, g〉 = E

x∼ n
2

n
2 → , then

[ϕ(x)g(x)].

The simplest example of a probability density is just the constant func-
tion 1, which corresponds to the uniform probability distribution on n
2 . The
most common case arises from the uniform distribution over some subset
A ⊆ n
2 .

Denition 1.22. If A ⊆ n
function of A; i.e.,

2 we write 1A :

n
2 → {0, 1} for the 0-1 indicator

1A(x) =



1 if x ∈ A,

0 if x ∉ A.

Assuming A 6= ; we write ϕA for the density function associated to the uni-
form distribution on A; i.e.,

E[1A] 1A.
We typically write y ∼ A rather than y ∼ ϕA.

ϕA = 1

A simple but useful example is when A is the singleton set A = {0}. (Here 0
2 .) In this case the function ϕ{0} takes
2 . In Exercise 1.1 you will

is denoting the vector (0, 0, . . . , 0) ∈ n
value 2n on input 0 ∈ n
verify the Fourier expansion of ϕ{0}:

2 and is zero elsewhere on n

Fact 1.23. Every Fourier coefcient of ϕ{0} is 1; i.e., its Fourier expansion is

ϕ{0}(y) =

∑

S⊆[n]

χS(y).

We now introduce an operation on functions that interacts particularly

nicely with density functions, namely, convolution.

Copyright © Ryan O’Donnell, 2014, 2015, 2016, 2017, 2018, 2019, 2020, 2021.



<!-- pdf-page: 30 -->
30

1. Boolean functions and the Fourier expansion

Denition 1.24. Let f , g :

n
2 → dened by

n
2 → . Their convolution is the function f ∗ g :

( f ∗ g)(x) = E

y∼ n
2

[ f (y)g(x − y)] = E

y∼ n
2

[ f (x − y)g(y)].

Since subtraction is equivalent to addition in n

( f ∗ g)(x) = E

y∼ n
2

[ f (y)g(x + y)] = E

y∼ n
2

2 we may also write
[ f (x + y)g(y)].

If we were representing the Hamming cube by {−1, 1}n rather than n
would replace x + y with x ◦ y, where ◦ denotes entry-wise multiplication.

2 we

Exercise 1.25 asks you to verify that convolution is associative and com-

mutative:

f ∗ (g ∗ h) = ( f ∗ g) ∗ h,

f ∗ g = g ∗ f .

Using Fact 1.21 we can deduce the following two simple results:

Proposition 1.25. If ϕ is a density function on n

ϕ ∗ g(x) = E
y∼ϕ

[g(x − y)] = E
y∼ϕ

In particular, E y∼ϕ[g(y)] = ϕ ∗ g(0).

2 and g :
[g(x + y)].

n
2 → then

Proposition 1.26. If g = ψ is itself a probability density function then so is
ϕ ∗ ψ; it represents the distribution on x ∈ n
2 given by choosing y ∼ ϕ and
z ∼ ψ independently and setting x = y + z.

The most important theorem about convolution is that it corresponds to

multiplication of Fourier coefcients:

Theorem 1.27. Let f , g :

n
2 → . Then for all S ⊆ [n],

Åf ∗ g(S) = f (S) g(S).

Proof. We have

Åf ∗ g(S) = E
x∼ n
2

[( f ∗ g)(x)χS(x)]
[

]

= E

x∼ n
2

E
y∼ n
2

[ f (y)g(x − y)]χS(x)

(the Fourier formula)

(by denition)

=

E
y,z∼ n
2
independently

[ f (y)g(z)χS(y + z)]

(as x − y is uniform on n

2 ∀x)

= E

[ f (y)χS(y)g(z)χS(z)]

y,z∼ n
2
= f (S) g(S)

as claimed.

(by identity (1.5))

(Fourier formula, independence),



Copyright © Ryan O’Donnell, 2014, 2015, 2016, 2017, 2018, 2019, 2020, 2021.



<!-- pdf-page: 31 -->
1.6. Highlight: Almost linear functions and the BLR Test

31

1.6. Highlight: Almost linear functions and the BLR Test

In linear algebra there are two equivalent denitions of what it means for a
function to be linear:

Denition 1.28. A function f :
equivalent conditions hold:

n
2 → 2 is linear if either of the following

(1) f (x + y) = f (x) + f (y) for all x, y ∈ n
2 ;
2 ; i.e., f (x) =

(2) f (x) = a · x for some a ∈ n



i∈S xi for some S ⊆ [n].

Exercise 1.26 asks you to verify that the conditions are indeed equivalent.
If we encode the output of f by ±1 ∈
in the usual way then the “linear”
functions f :

2 → {−1, 1} are precisely the 2n parity functions (χS)S⊆[n].

n

Let’s think of what it might mean for a function f :
imately linear. Denition 1.28 suggests two possibilities:

n
2 → 2 to be approx-

(1′) f (x + y) = f (x) + f (y) for almost all pairs x, y ∈ n
2 ;

(2′) there is some S ⊆ [n] such that f (x) =



i∈S xi for almost all x ∈ n
2 .

Are these equivalent? The proof of (2) =⇒ (1) in Denition 1.28 is “robust”: it
easily extends to show (2′) =⇒ (1′) (see Exercise 1.26). But the natural proof
of (1) =⇒ (2) in Denition 1.28 does not have this robustness property. The
goal of this section is to show that (1′) =⇒ (2′) nevertheless holds.

Motivation for this problem comes from an area of theoretical computer
science called property testing, which we will discuss in more detail in Chap-
n
ter 7. Imagine that you have “black-box” access to a function f :
2 → 2,
meaning that the function f is unknown to you but you can “query” its value
on inputs x ∈ n
2 of your choosing. The function f is “supposed” to be a linear
function, and you would like to try to verify this.

The only way you can be certain f is indeed a linear function is to query
its value on all 2n inputs; unfortunately, this is very expensive. The idea
behind “property testing” is to try to verify that f has a certain property – in
this case, linearity – by querying its value on just a few random inputs. In
exchange for efciency, we need to be willing to only approximately verify the
property.

Denition 1.29. If f and g are Boolean-valued functions we say they are
≤-close if dist( f , g) ≤ ≤; otherwise we say they are ≤-far. If P is a (nonempty)
property of n-bit Boolean functions we dene dist( f , P ) = ming∈P {dist( f , g)}.
We say that f is ≤-close to P if dist( f , P ) ≤ ≤; i.e., f is ≤-close to some g
satisfying P .

Copyright © Ryan O’Donnell, 2014, 2015, 2016, 2017, 2018, 2019, 2020, 2021.



<!-- pdf-page: 32 -->
32

1. Boolean functions and the Fourier expansion

In particular, in property testing we take property (2′) above to be the no-
tion of “approximately linear”: we say f is ≤-close to being linear if dist( f , g) ≤ ≤
for some truly linear g(x) =



i∈S xi.

In 1990 Blum, Luby, and Rubinfeld [BLR90] showed that indeed (1′) =⇒
(2′) holds, giving the following “test” for the property of linearity that makes
just 3 queries:

BLR Test. Given query access to f :

• Choose x ∼ n

2 and y ∼ n
• Query f at x, y, and x + y.

n
2 → 2:
2 independently.

• “Accept” if f (x) + f (y) = f (x + y).

We now show that if the BLR Test accepts f with high probability then
f is close to being linear. The proof works by directly relating the acceptance
probability to the quantity

f (S)3; see equation (1.10) below.



S

Theorem 1.30. Suppose the BLR Test accepts f :
1 − ≤. Then f is ≤-close to being linear.

n
2 → 2 with probability

Proof. In order to use the Fourier transform we encode f ’s output by ±1 ∈ ;
thus the acceptance condition of the BLR Test becomes f (x) f (y) = f (x + y).
Since

1

2 + 1

2 f (x) f (y) f (x + y) =



1 if f (x) f (y) = f (x + y),

0 if f (x) f (y) 6= f (x + y),

we conclude

1 − ≤ = Pr[BLR accepts f ] = E
x,y

2 + 1
[ 1

2 f (x) f (y) f (x + y)]

[ f (y) f (x + y)]]

= 1

2 + 1
2 + 1
2 + 1

2

= 1

= 1

[ f (x) · E
y

2 E
x
[ f (x) · ( f ∗ f )(x)]
2 E
x
∑

f (S)Åf ∗ f (S)

= 1

2 + 1

2

S⊆[n]
∑

S⊆[n]

f (S)3

(by denition)

(Plancherel)

(Theorem 1.27).

(1.10)

(Parseval).

We rearrange this equality and then continue:

1 − 2≤ =

∑

f (S)3

S⊆[n]

≤ max
S⊆[n]

{ f (S)} ·

∑

S⊆[n]

f (S)2

= max
S⊆[n]

{ f (S)}

Copyright © Ryan O’Donnell, 2014, 2015, 2016, 2017, 2018, 2019, 2020, 2021.



<!-- pdf-page: 33 -->
1.7. Exercises and notes

33

But f (S) = 〈 f , χS〉 = 1 − 2dist( f , χS) (Proposition 1.9). Hence there exists some
S∗ ⊆ [n] such that 1−2≤ ≤ 1−2dist( f , χS∗); i.e., f is ≤-close to the linear function

χS∗.

In fact, for small ≤ one can show that f is more like (≤/3)-close to linear,

and this is sharp. See Exercise 1.28.

The BLR Test shows that given black-box access to f :

n
2 → {−1, 1}, we can
“test” whether f is close to some linear function χS using just 3 queries. The
test does not reveal which linear function χS is close to (indeed, determining
this takes at least n queries; see Exercise 1.27). Nevertheless, we can still
determine the value of χS(x) with high probability for every x ∈ n
2 of our
choosing using just 2 queries. This property is called local correctability of
linear functions.

Proposition 1.31. Suppose f :
Then for every x ∈ n
at least 1 − 2≤:

n
2 → {−1, 1} is ≤-close to the linear function χS.
2 , the following algorithm outputs χS(x) with probability

• Choose y ∼ n
2 .

• Query f at y and x + y.

• Output f (y) f (x + y).

We emphasize the order of quantiers here: if we just output f (x) then this
will equal χS(x) for most x; however, the above “local correcting” algorithm
determines χS(x) (with high probability) for every x.

Proof. Since y and x + y are both uniformly distributed on n
2 (though not
independently) we have Pr[ f (y) 6= χS(y)] ≤ ≤ and Pr[ f (x + y) 6= χS(x + y)] ≤ ≤
by assumption. By the union bound, the probability of either event occurring
is at most 2≤; when neither occurs,

f (y) f (x + y) = χS(y)χS(x + y) = χS(x)

as desired.

1.7. Exercises and notes



1.1 Compute the Fourier expansions of the following functions:

(a) min2 : {−1, 1}2 → {−1, 1}, the minimum function on 2 bits (also known

as the logical OR function);

(b) min3 : {−1, 1}3 → {−1, 1} and max3 : {−1, 1}3 → {−1, 1};
2 → {0, 1}, where a ∈ n
(c) the indicator function 1{a} :
2 ;
2 → ≥0, where a ∈ n
(d) the density function ϕ{a} :
2 ;
(e) the density function ϕ{a,a+e i} :

2 → ≥0, where a ∈

n

n

n

(0, . . . , 0, 1, 0, . . . , 0) with the 1 in the ith coordinate;

n
2 and e i =

Copyright © Ryan O’Donnell, 2014, 2015, 2016, 2017, 2018, 2019, 2020, 2021.



<!-- pdf-page: 34 -->
34

1. Boolean functions and the Fourier expansion

(f ) the density function corresponding to the product probability distri-
bution on {−1, 1}n in which each coordinate has mean ρ ∈ [−1, 1];

(g) the inner product mod 2 function, IP2n :

IP2n(x1, . . . , xn, y1, . . . , yn) = (−1)x·y;

2n
2 → {−1, 1} dened by

(h) the equality function Equn : {−1, 1}n → {0, 1}, dened by Equn(x) = 1 if

and only if x1 = x2 = · · · = xn;

(i) the not-all-equal function NAEn : {−1, 1}n → {0, 1}, dened by NAEn(x) =

1 if and only if the bits x1, . . . , xn are not all equal;

(j) the selection function, Sel : {−1, 1}3 → {−1, 1}, which outputs x2 if x1 =

−1 and outputs x3 if x1 = 1;

(k) mod3 :

3
2 → {0, 1}, which is 1 if and only if the number of 1’s in the

input is divisible by 3;

(l) OXR :

3
2 → {0, 1} dened by OXR(x1, x2, x3) = x1 ∨ (x2 ⊕ x3). Here ∨ de-

notes logical OR, ⊕ denotes logical XOR;

(m) the sortedness function Sort4 : {−1, 1}4 → {−1, 1}, dened by Sort4(x) =

−1 if and only if x1 ≤ x2 ≤ x3 ≤ x4 or x1 ≥ x2 ≥ x3 ≥ x4;

(n) the hemi-icosahedron function HI : {−1, 1}6 → {−1, 1} (also known as
the Kushilevitz function), dened to be the number of facets labeled
(+1, +1, +1) in Figure 1.2, minus the number of facets labeled (−1, −1, −1),
modulo 3.

Figure 1.2. The hemi-icosahedron

(Hint: First compute the real multilinear interpolation of the ana-
logue HI : {0, 1}6 → {0, 1}.)

(o) the majority functions Maj5 : {−1, 1}5 → {−1, 1} and Maj7 : {−1, 1}7 →

{−1, 1};



(p) the complete quadratic function CQn :

n
2 → {−1, 1} dened by CQn(x) =
χ(
1≤i< j≤n xi x j). (Hint: Determine CQn(x) as a function of the num-
ber of 1’s in the input modulo 4. You’ll want to distinguish whether n
is even or odd.)

Copyright © Ryan O’Donnell, 2014, 2015, 2016, 2017, 2018, 2019, 2020, 2021.



<!-- pdf-page: 35 -->
1.7. Exercises and notes

35

1.2 How many Boolean functions f : {−1, 1}n → {−1, 1} have exactly 1 nonzero

Fourier coefcient?

1.3 Let f :

n
2 → {0, 1}, n > 1, and suppose #{x : f (x) = 1} is odd. Prove that all

of f ’s Fourier coefcients are nonzero.

1.4 Let f : {−1, 1}n → have Fourier expansion f (x) =



n → be the extension of f which is also dened by F(x) =

S⊆[n]

f (S) xS. Let F :

f (S) xS.

S⊆[n]

Show that if µ = (µ1, . . . , µn) ∈ [−1, 1]n then

F(µ) = E
y

[ f (y)],

where y is the random string in {−1, 1}n dened by having E[yi] = µi
independently for all i ∈ [n].

1.5 Prove that any f : {−1, 1}n → {−1, 1} has at most one Fourier coefcient
with magnitude exceeding 1/2. Is this also true for any f : {−1, 1}n →
with ‖ f ‖2 = 1?

1.6 Use Parseval’s Theorem to prove uniqueness of the Fourier expansion.
1.7 Let f : {−1, 1}n → {−1, 1} be a random function (i.e., each f (x) is ±1 with
probability 1/2, independently for all x ∈ {−1, 1}n). Show that for each
S ⊆ [n], the random variable f (S) has mean 0 and variance 2−n. (Hint:
Parseval.)

1.8 The (Boolean) dual of f : {−1, 1}n → is the function f † dened by f †(x) =
− f (−x). The function f is said to be odd if it equals its dual; equivalently,
if f (−x) = − f (x) for all x. The function f is said to be even if f (−x) = f (x)
for all x. Given any function f : {−1, 1}n → , its odd part is the function
f odd : {−1, 1}n → dened by f odd(x) = ( f (x) − f (−x))/2, and its even part
is the function f even : {−1, 1}n → dened by f even(x) = ( f (x) + f (−x))/2.
(a) Express f †(S) in terms of f (S).
(b) Verify that f = f odd + f even and that f is odd (respectively, even) if and

only if f = f odd (respectively, f = f even).

(c) Show that

f odd =

∑

S⊆[n]
|S| odd

f (S) χS,

f even =

∑

S⊆[n]
|S| even

f (S) χS.

1.9 In this problem we consider representing False,True as 0, 1 ∈ .

(a) Using the interpolation method from Section 1.2, show that every f :
{False,True}n → {False,True} can be represented as a real multilinear
polynomial

∑

∏

q(x) =

cS

xi,

(1.11)

“over {0, 1}”, meaning mapping {0, 1}n → {0, 1}.

S⊆[n]

i∈S

Copyright © Ryan O’Donnell, 2014, 2015, 2016, 2017, 2018, 2019, 2020, 2021.



<!-- pdf-page: 36 -->
36

1. Boolean functions and the Fourier expansion

(b) Show that this representation is unique. (Hint: If q as in (1.11) has
at least one nonzero coefcient, consider q(a) where a ∈ {0, 1}n is the
indicator vector of a minimal S with cS 6= 0.)

(c) Show that all coefcients cS in the representation (1.11) will be inte-

gers in the range [−2n, 2n].

(d) Let f : {False,True}n → {False,True}. Let p(x) be f ’s multilinear rep-
resentation when False,True are 1, −1 ∈
(i.e., p is the Fourier ex-
pansion of f ) and let q(x) be f ’s multilinear representation when
False,True are 0, 1 ∈ . Show that q(x) = 1

2 p(1 − 2x1, . . . , 1 − 2xn).

2 − 1

1.10 Let f : {−1, 1}n → be not identically 0. The (real) degree of f , denoted
deg( f ), is dened to be the degree of its multilinear (Fourier) expansion;
i.e., max{|S| : f (S) 6= 0}.
(a) Show that deg( f ) = deg(a + b f ) for any a, b ∈

(assuming b 6= 0, a +

b f 6= 0).

(b) Show that deg( f ) ≤ k if and only if f is a real linear combination of
functions g1, . . . , gs, each of which depends on at most k input coordi-
nates.

(c) Which functions in Exercise 1.1 have “nontrivial” degree? (Here f :

{−1, 1}n → has “nontrivial” degree if deg( f ) < n.)

1.11 Suppose that f : {−1, 1}n → {−1, 1} has deg( f ) = k ≥ 1.

(a) Show that f ’s real multilinear representation over {0, 1} (see Exer-

cise 1.9), call it q(x), also has deg(q) = k.

(b) Using Exercise 1.9(c),(d), deduce that f ’s Fourier spectrum is “21−k-

granular”, meaning each f (S) is an integer multiple of 21−k.

(c) Show that

S⊆[n] | f (S)| ≤ 2k−1.



1.12 A Hadamard Matrix is any N × N real matrix with ±1 entries and orthog-
onal rows. Particular examples are the Walsh–Hadamard Matrices HN ,
]
inductively dened for N = 2n as follows: H1 =
(a) Let’s index the rows and columns of H2n by the integers {0, 1, 2, . . . , 2n−
1} rather than [2n]. Further, let’s identify such an integer i with its
binary expansion (i0, i1, . . . , i n−1) ∈ n
2 , where i0 is the least signicant
bit and i n−1 the most. For example, if n = 3, we identify the index
i = 6 with (0, 1, 1). Now show that the (γ, x) entry of H2n is (−1)γ·x.

H2n H2n
H2n −H2n

, H2n+1 =

1

[





.

(b) Show that if f :

n

2 → is represented as a column vector in 2n (ac-
cording to the indexing scheme from part (a)) then 2−nH2n f = f . Here
we think of f as also being a function n
2 → , identifying subsets
S ⊆ {0, 1, . . . , n − 1} with their indicator vectors.

(c) Show how to compute H2n f using just n2n additions and subtractions
(rather than 22n additions and subtractions as the usual matrix-vector
multiplication algorithm would require). This computation is called

Copyright © Ryan O’Donnell, 2014, 2015, 2016, 2017, 2018, 2019, 2020, 2021.



<!-- pdf-page: 37 -->
1.7. Exercises and notes

37

the Fast Walsh–Hadamard Transform and is the method of choice
for computing the Fourier expansion of a generic function f :
when n is large.

n
2 →

(d) Show that taking the Fourier transform is essentially an “involution”:

f = 2−n f (using the notations from part (b)).

1.13 Let f : {−1, 1}n → and let 0 < p ≤ q < ∞. Show that ‖ f ‖p ≤ ‖ f ‖q. (Hint:
Use Jensen’s inequality with the convex function t 7→ tq/p.) Extend the in-
equality to the case q = ∞, where ‖ f ‖∞ is dened to be maxx∈{−1,1}n {| f (x)|}.

1.14 Compute the mean and variance of each function from Exercise 1.1.
1.15 Let f : {−1, 1}n → . Let K ⊆ [n] and let z ∈ {−1, 1}K . Suppose g : {−1, 1}[n]\K →

is the subfunction of f gotten by restricting the K-coordinates to be z.

Show that E[g] =



f (T) zT .

T⊆K

1.16 If f : {−1, 1}n → {−1, 1}, show that Var[ f ] = 4·dist( f , 1)·dist( f , −1). Deduce

Proposition 1.15.

1.17 Extend Fact 1.14 by proving the following: If F is a {−1, 1}-valued random

variable with mean µ then

Var[F] = E[(F − µ)2] = 1

2 E[(F − F′)2] = 2 Pr[F 6= F′] = E[|F − µ|],

where F′ is an independent copy of F. (The rst two equalities do not
require F to be {−1, 1}-valued.)
1.18 For any f : {−1, 1}n → , show that

〈 f =k, f =`〉 =



Wk[ f ]

if k = `,

0

if k 6= `.

1.19 Let f : {−1, 1}n → {−1, 1}.

(a) Suppose W1[ f ] = 1. Show that f (x) = ±χS for some |S| = 1.
(b) Suppose W≤1[ f ] = 1. Show that f depends on at most 1 input coordi-

nate.

(c) Suppose W≤2[ f ] = 1. Must f depend on at most 2 input coordinates?

At most 3 input coordinates? What if we assume W2[ f ] = 1?

f (i)2 f ( j)2.
1.20 Let f : {−1, 1}n → satisfy f = f =1. Show that Var[ f 2] = 2
1.21 Prove that there are no functions f : {−1, 1}n → {−1, 1} with exactly 2
nonzero Fourier coefcients. What about exactly 3 nonzero Fourier coef-
cients?

i6= j



1.22 Verify Propositions 1.25 and 1.26.

1.23 In this exercise you will prove some basic facts about “distances” between
probability distributions. Let ϕ and ψ be probability densities on n
2 .
(a) Show that the total variation distance between ϕ and ψ, dened by

dTV(ϕ, ψ) = max
A⊆ n
2

[y ∈ A] − Pr
y∼ψ

[y ∈ A]

∣
∣
∣ Pr
y∼ϕ



∣
∣
∣

,

Copyright © Ryan O’Donnell, 2014, 2015, 2016, 2017, 2018, 2019, 2020, 2021.



<!-- pdf-page: 38 -->
38

1. Boolean functions and the Fourier expansion

is equal to 1

2 ‖ϕ − ψ‖1.

(b) Show that the collision probability of ϕ, dened to be

[y = y′],

Pr
y,y′∼ϕ
independently

is equal to ‖ϕ‖2

2/2n.

(c) The χ2-distance of ϕ from ψ is dened by

dχ2(ϕ, ψ) = E
y∼ψ

 ϕ(y)
ψ(y)

2

,

− 1

assuming ψ has full support. Show that the χ2-distance of ϕ from
uniform is equal to Var[ϕ].

(d) Show that the total variation distance of ϕ from uniform is at most



1
2

Var[ϕ].

1.24 Let A ⊆ {−1, 1}n have “volume” δ, meaning E[1A] = δ. Suppose ϕ is a
probability density supported on A, meaning ϕ(x) = 0 when x ∉ A. Show
that ‖ϕ‖2
2 ≥ 1/δ with equality if ϕ = ϕA, the uniform density on A.

1.25 Show directly from the denition that the convolution operator is associa-

tive and commutative.

1.26 Verify that (1) ⇐⇒ (2) in Denition 1.28.

1.27 Suppose an algorithm is given query access to a linear function f :

n
2 →
2 and its task is to determine which linear function f is. Show that

querying f on n inputs is necessary and sufcient.

1.28 (a) Generalize Exercise 1.5 as follows: Let f :

n
2 → {−1, 1} and suppose
that dist( f , χS∗) = δ. Show that | f (S)| ≤ 2δ for all S 6= S∗. (Hint: Use
the union bound.)

(b) Deduce that the BLR Test rejects f with probability at least 3δ −

10δ2 + 8δ3.

(c) Show that this lower bound cannot be improved to cδ − O(δ2) for any

c > 3.

1.29 (a) We call f :

n

(b) Let f :

2 → 2 an afne function if f (x) = a · x + b for some a ∈ n
2 ,
b ∈ 2. Show that f is afne if and only if f (x)+ f (y)+ f (z) = f (x+ y+ z)
for all x, y, z, ∈ n
2
n

2 → . Suppose we choose x, y, z ∼ n
uniformly. Show that E[ f (x) f (y) f (z) f (x + y + z)] =

2 independently and
f (S)4.

(c) Give a 4-query test for a function f :

S
n
2 → 2 with the following prop-
erty: if the test accepts with probability 1 − ≤ then f is ≤-close to being
afne. All four query inputs should have the uniform distribution
on n

2 (but of course need not be independent).



(d) Give an alternate 4-query test for being afne in which three of the
query inputs are uniformly distributed and the fourth is not random.

Copyright © Ryan O’Donnell, 2014, 2015, 2016, 2017, 2018, 2019, 2020, 2021.



<!-- pdf-page: 39 -->
1.7. Exercises and notes

39

(Hint: Show that f is afne if and only if f (x) + f (y) + f (0) = f (x + y)
for all x, y ∈ n
2 .)

1.30 Permutations π ∈ Sn act on strings x ∈ {−1, 1}n in the natural way: (xπ)i =
xπ(i). They also act on functions f : {−1, 1}n → via f π(x) = f (xπ) for all x ∈
{−1, 1}n. We say that functions g, h : {−1, 1}n → {−1, 1} are (permutation-
)isomorphic if g = hπ for some π ∈ Sn. We call Aut( f ) = {π ∈ Sn : f π = f }
the (permutation-)automorphism group of f .
(a) Show that f π(S) = f (π−1(S)) for all S ⊆ [n].

For future reference, when we write ( f (S))|S|=k, we mean the sequence
of degree-k Fourier coefcients of f , listed in lexicographic order of the
k-sets S.

Given complete truth tables of some g and h we might wish to deter-
mine whether they are isomorphic. One way to do this would be to dene
a canonical form can( f ) : {−1, 1}n → {−1, 1} for each f : {−1, 1}n → {−1, 1},
meaning that: (i) can( f ) is isomorphic to f ; (ii) if g is isomorphic to h then
can(g) = can(h). Then we can determine whether g is isomorphic to h by
checking whether can(g) = can(h). Here is one possible way to dene a
canonical form for f :
1. Set P0 = Sn.
2. For each k = 1, 2, 3, . . . , n,
3.

Dene Pk to be the set of all π ∈ Pk−1 that make the sequence
(f π(S))|S|=k maximal in lexicographic order on (n
k).

4. Let can( f ) = f π for (any) π ∈ Pn.

(b) Show that this is well-dened, meaning that can( f ) is the same func-

tion for any choice of π ∈ Pn.

(c) Show that can( f ) is indeed a canonical form; i.e., it satises (i) and (ii)

above.

(d) Show that if f ({1}), . . . , f ({n}) are distinct numbers then can( f ) can be

computed in O(2n) time.

(e) We could more generally consider g, h : {−1, 1}n → {−1, 1} to be isomor-
phic if g(x) = h(±xπ(1), . . . , ±xπ(n)) for some permutation π on [n] and
some choice of signs. Extend the results of this exercise to handle this
denition.

Notes. The Fourier expansion for real-valued Boolean functions dates back
to Walsh [Wal23] who introduced a complete orthonormal basis for L2([0, 1])
consisting of ±1-valued functions, constant on dyadic intervals. Using the or-
dering introduced by Paley [Pal32], the nth Walsh basis function wn : [0, 1] →
i=0 ni2i and r i(x) (the
{−1, 1} is dened by wn(x) =
∞
i=0 xi2−(i+1)
“ith Rademacher function at x”) is dened to be (−1)xi , with x =
for non-dyadic x ∈ [0, 1]. Walsh’s interest was in comparing and contrasting

i=0 r i(x)n i , where n =

∞

∞

Copyright © Ryan O’Donnell, 2014, 2015, 2016, 2017, 2018, 2019, 2020, 2021.



<!-- pdf-page: 40 -->
40

1. Boolean functions and the Fourier expansion

the properties of this basis with the usual basis of trigonometric polynomials
and also Haar’s basis [Haa10].

The rst major study of the Walsh functions came in the remarkable paper
of Paley [Pal32], which included strong results on the L p-norms of truncations
of Walsh series. Sadly, Paley died in an avalanche one year later (at age 26)
while skiing near Banff. The next major development in the study of Walsh
series was conceptual, with Vilenkin [Vil47] and Fine [Fin49] independently
suggesting the more natural viewpoint of the Walsh functions as characters
of the discrete group n
2 . There was signicant subsequent work in the 1950s
and 1960s, but it’s somewhat unnatural from our point of view because it
relies fundamentally on ordering the Rademacher and Walsh functions ac-
cording to binary expansions. Bonami [Bon68] and Kiener [Kie69] seem to
have been the rst authors to take our viewpoint, treating bits x1, x2, x3, . . .
symmetrically and ordering Fourier characters χS according to |S| rather
than max(S). Bonami also obtained the rst hypercontractivity result for the
Boolean cube. This proved to be a crucial tool for analysis of Boolean func-
tions; see Chapter 9. For an early survey on Walsh series, see Balashov and
Rubinshtein [BR73].

Turning to Boolean functions and computer science, the idea of using
Boolean logic to study “switching functions” (as engineers originally called
Boolean functions) dates to the late 1930s and is usually credited to Naka-
shima [Nak35], Shannon [Sha37], and Shestakov [She38]. Muller [Mul54b]
seems to be the rst to have used Fourier coefcients in the study of Boolean
functions; he mentions computing them while classifying all functions f :
{0, 1}4 → {0, 1} up to certain equivalences. The rst publication devoted to
Boolean Fourier coefcients was by Ninomiya [Nin58], who expanded on
Muller’s use of Fourier coefcients for the classication of Boolean functions
up to various isomorphisms. Golomb [Gol59] independently pursued the
same project (his work is the content of Exercise 1.30); he was also the rst to
recognize the connection to Walsh series. The use of “Fourier–Walsh analysis”
in the study of Boolean functions quickly became well known in the early
1960s. Several symposia on applications of Walsh functions took place in the
early 1970s, with Lechner’s 1971 monograph [Lec71] and Karpovsky’s 1976
book [Kar76] becoming the standard references. However, the use of Boolean
analysis in theoretical computer science seemed to wane until 1988, when the
outstanding work of Kahn, Kalai, and Linial [KKL88] ushered in a new area
of sophistication.

The original analysis by Blum, Luby, and Rubinfeld [BLR90] for their
linearity test was combinatorial; our proof of Theorem 1.30 is the elegant an-
alytic one due to Bellare, Coppersmith, Håstad, Kiwi, and Sudan [BCH+96].
In fact, the essence of this analysis appears already in the 1953 work of

Copyright © Ryan O’Donnell, 2014, 2015, 2016, 2017, 2018, 2019, 2020, 2021.



<!-- pdf-page: 41 -->
1.7. Exercises and notes

41

Roth [Rot53] (in the context of the cyclic group N rather than n
2 ). The
work of Bellare et al. also gives additional analysis improving the results of
Theorem 1.30 and Exercise 1.28. See also the work of Kaufman, Litsyn, and
Xie [KLX10] for further slight improvement.

In Exercise 1.1, the sortedness function was introduced by Ambainis [Amb03,

LLS06]; the hemi-icosahedron function was introduced by Kushilevitz [NW95].
The fast algorithm for computing the Fourier transform mentioned in Exer-
cise 1.12 is due to Lechner [Lec63].

Copyright © Ryan O’Donnell, 2014, 2015, 2016, 2017, 2018, 2019, 2020, 2021.



<!-- pdf-page: 42 -->


<!-- pdf-page: 43 -->
Chapter 2

Basic concepts and
social choice

In this chapter we introduce a number of important basic concepts including
inuences and noise stability. Many of these concepts are nicely motivated
using the language of social choice. The chapter is concluded with Kalai’s
Fourier-based proof of Arrow’s Theorem.

2.1. Social choice functions

In this section we describe some rudiments of the mathematics of social choice,
a topic studied by economists, political scientists, mathematicians, and com-
puter scientists. The fundamental question in this area is how best to ag-
gregate the opinions of many agents. Examples where this problem arises
include citizens voting in an election, committees deciding on alternatives,
and independent computational agents making collective decisions. Social
choice theory also provides very appealing interpretations for a number of
important functions and concepts in the analysis of Boolean functions.

A Boolean function f : {−1, 1}n → {−1, 1} can be thought of as a voting rule
or social choice function for an election with 2 candidates and n voters; it
maps the votes of the voters to the winner of the election. Perhaps the most
familiar voting rule is the majority function:

Denition 2.1. For n odd, the majority function Majn : {−1, 1}n → {−1, 1} is
dened by Majn(x) = sgn(x1 + x2 + · · · + xn). (Occasionally, for n even we say
that f is a majority function if f (x) equals the sign of x1 + · · · + xn whenever
this number is nonzero.)

Copyright © Ryan O’Donnell, 2014, 2015, 2016, 2017, 2018, 2019, 2020, 2021.

43



<!-- pdf-page: 44 -->
44

2. Basic concepts and social choice

The Boolean AND and OR functions correspond to voting rules in which
a certain candidate is always elected unless all voters are unanimously op-
posed. Recalling our somewhat nonintuitive convention that −1 represents
True and +1 represents False:

Denition 2.2. The function ANDn : {−1, 1}n → {−1, 1} is dened by ANDn(x) =
+1 unless x = (−1, −1, . . . , −1). The function ORn : {−1, 1}n → {−1, 1} is dened
by ORn(x) = −1 unless x = (+1, +1, . . . , +1).

Another voting rule commonly encountered in practice:

Denition 2.3. The ith dictator function χi : {−1, 1}n → {−1, 1} is dened by
χi(x) = xi.

Here we are simplifying notation for the singleton monomial from χ{i} to
χi. Even though they are extremely simple functions, the dictators play a very
important role in analysis of Boolean functions; to highlight this we prefer
the colorful terminology “dictator functions” to the more mathematically staid
“projection functions”. Generalizing:

Denition 2.4. A function f : {−1, 1}n → {−1, 1} is called a k-junta for k ∈
if it depends on at most k of its input coordinates; i.e., f (x) = g(xi1
) for
some g : {−1, 1}k → {−1, 1} and i1, . . . , i k ∈ [n]. Informally, we say that f is a
“junta” if it depends on only a “constant” number of coordinates.

, . . . , xi k

For example, the number of functions f : {−1, 1}n → {−1, 1} which are 1-juntas
is precisely 2n+2: the n dictators, the n negated-dictators, and the 2 constant
functions ±1.

The European Union’s Council of Ministers adopts decisions based on a

weighted majority voting rule:

Denition 2.5. A function f : {−1, 1}n → {−1, 1} is called a weighted majority
or (linear) threshold function if it is expressible as f (x) = sgn(a0 + a1x1 + · · · +
an xn) for some a0, a1, . . . , an ∈ .

Exercise 2.2 has you verify that majority, AND, OR, dictators, and constants
are all linear threshold functions.

The leader of the United States (and many other countries) is elected via
a kind of “two-level majority”. We make a natural denition along these lines:

Denition 2.6. The depth-d recursive majority of n function, denoted Maj⊗d
n ,
is the Boolean function of nd bits dened inductively as follows: Maj⊗1
n =
Majn, and Maj⊗(d+1)
n (x(n))) for x(i) ∈
{−1, 1}nd .

(x(1), . . . , x(n)) = Majn(Maj⊗d

n (x(1)), . . . , Maj⊗d

n

Copyright © Ryan O’Donnell, 2014, 2015, 2016, 2017, 2018, 2019, 2020, 2021.



<!-- pdf-page: 45 -->
2.1. Social choice functions

45

In our last example of a 2-candidate voting rule, the voters are divided into
“tribes” of equal size and the outcome is True if and only if at least one tribe is
unanimously in favor of True. This rule is only somewhat plausible in practice,
but it plays a very important role in the analysis of Boolean functions:

Denition 2.7. The tribes function of width w and size s, Tribesw,s : {−1, 1}sw →
{−1, 1}, is dened by Tribesw,s(x(1), . . . , x(s)) = ORs(ANDw(x(1)), . . . , ANDw(x(s))),
where x(i) ∈ {−1, 1}w.

Here are some natural properties of 2-candidate social choice functions

which may be considered desirable:

Denition 2.8. We say that a function f : {−1, 1}n → {−1, 1} is:

• monotone if f (x) ≤ f (y) whenever x ≤ y coordinate-wise;

• odd if f (−x) = − f (x);

• unanimous if f (1, . . . , 1) = 1 and f (−1, . . . , −1) = −1;
• symmetric if f (xπ) = f (x) for all permutations π ∈ Sn (using the notation
from Exercise 1.30); i.e., f (x) only depends on the number of 1’s in x.

The denitions of monotone, odd, and symmetric are also natural for f :
{−1, 1}n → .

Example 2.9. The majority function (for n odd) has all four properties in
Denition 2.8; indeed, May’s Theorem (Exercise 2.3) states that it is the only
monotone, odd, symmetric function. The dictator functions have the rst
three properties above, as do recursive majority functions. The AND and OR
functions are monotone, unanimous, and symmetric, but not odd. The tribes
functions are monotone and unanimous; although they are not symmetric
they have an important weaker property:

Denition 2.10. A function f : {−1, 1}n → {−1, 1} is transitive-symmetric if for
all i, i′ ∈ [n] there exists a permutation π ∈ Sn taking i to i′ such f (xπ) = f (x)
for all x ∈ {−1, 1}n.

Intuitively, a function is transitive-symmetric if any two coordinates i, j ∈ [n]
are “equivalent”.

One more natural desirable property of a 2-candidate voting rule is that
it be unbiased as dened in Chapter 1.4, i.e., “equally likely” to elect ±1. Of
course, this presupposes the uniform probability distribution on votes.

Denition 2.11. The impartial culture assumption is that the n voters’ pref-
erences are independent and uniformly random.

Although this assumption might seem somewhat unrealistic, it gives a
good basis for comparing voting rules in the absence of other information.

Copyright © Ryan O’Donnell, 2014, 2015, 2016, 2017, 2018, 2019, 2020, 2021.



<!-- pdf-page: 46 -->
46

2. Basic concepts and social choice

One might also consider it as a model for the votes of just the “undecided” or
“party-independent” voters.

2.2. Inuences and derivatives

Given a voting rule f : {−1, 1}n → {−1, 1} it’s natural to try to measure the
“inuence” or “power” of the ith voter. One can dene this to be the “probability
that the ith vote affects the outcome”.

Denition 2.12. We say that coordinate i ∈ [n] is pivotal for f : {−1, 1}n →
{−1, 1} on input x if f (x) 6= f (x⊕i). Here we have used the notation x⊕i for the
string (x1, . . . , xi−1, −xi, xi+1, . . . , xn).

Denition 2.13. The inuence of coordinate i on f : {−1, 1}n → {−1, 1} is de-
ned to be the probability that i is pivotal for a random input:

Infi[ f ] = Pr

x∼{−1,1}n

[ f (x) 6= f (x⊕i)].

Inuences can be equivalently dened in terms of “geometry” of the Ham-

ming cube:

Fact 2.14. For f : {−1, 1}n → {−1, 1}, the inuence Infi[ f ] equals the fraction
of dimension-i edges in the Hamming cube which are boundary edges. Here
(x, y) is a dimension-i edge if y = x⊕i; it is a boundary edge if f (x) 6= f (y).

Figure 2.1. Boundary edges of the Maj3 function

Example 2.15. For the ith dictator function χi we have that coordinate i
is pivotal for every input x; hence Infi[χi] = 1. On the other hand, if j 6= i
then coordinate j is never pivotal; hence Inf j[χi] = 0 for j 6= i. Note that
the same two statements are true about the negated-dictator functions. For
the constant functions ±1, all inuences are 0. For the ORn function, coordi-
nate 1 is pivotal for exactly two inputs, (−1, 1, 1, . . . , 1) and (1, 1, 1, . . . , 1); hence
Inf1[ORn] = 21−n. Similarly, Infi[ORn] = Infi[ANDn] = 21−n for all i ∈ [n].
The Maj3 is depicted in Figure 2.1; the points where it’s +1 are colored gray
and the points where it’s −1 are colored white. Its boundary edges are high-
lighted in black; there are 2 of them in each of the 3 dimensions. Since there

Copyright © Ryan O’Donnell, 2014, 2015, 2016, 2017, 2018, 2019, 2020, 2021.



<!-- pdf-page: 47 -->
2.2. Inuences and derivatives

47

are 4 total edges in each dimension, we conclude Infi[Maj3] = 2/4 = 1/2 for all
i ∈ [3]. For majority in higher dimensions, Infi[Majn] equals the probability
p
2/πp
that among n − 1 random bits, exactly half of them are 1. This is roughly
n
for large n; see Exercise 2.22 or Chapter 5.2.

Inuences can also be dened more “analytically” by introducing the de-

rivative operators.

Denition 2.16. The ith (discrete) derivative operator Di maps the function
f : {−1, 1}n → to the function Di f : {−1, 1}n → dened by

Di f (x) =

f (x(i7→1)) − f (x(i7→−1))
2

.

Here we have used the notation x(i7→b) = (x1, . . . , xi−1, b, xi+1, . . . , xn). Notice
that Di f (x) does not actually depend on xi. The operator Di is a linear opera-
tor: i.e., Di( f + g) = Di f + Di g.

If f : {−1, 1}n → {−1, 1} is Boolean-valued then



Di f (x) =

0

if coordinate i is not pivotal for x,

±1 if coordinate i is pivotal for x.

(2.1)

Thus Di f (x)2 is the 0-1 indicator for whether i is pivotal for x and we con-
clude that Infi[ f ] = E[Di f (x)2]. We take this formula as a denition for the
inuences of real-valued Boolean functions.

Denition 2.17. We generalize Denition 2.13 to functions f : {−1, 1}n →
by dening the inuence of coordinate i on f to be

Infi[ f ] =

E
x∼{−1,1}n

[Di f (x)2] = ‖Di f ‖2
2.

Denition 2.18. We say that coordinate i ∈ [n] is relevant for f : {−1, 1}n →
if and only if Infi[ f ] > 0; i.e., f (x(i7→1)) 6= f (x(i7→−1)) for at least one x ∈ {−1, 1}n.

The discrete derivative operators are quite analogous to the usual partial
derivatives. For example, f : {−1, 1}n → is monotone if and only if Di f (x) ≥ 0
for all i and x. Further, Di acts like formal differentiation on Fourier expan-
sions:

Proposition 2.19. Let f : {−1, 1}n → have the multilinear expansion f (x) =


f (S) xS. Then

S⊆[n]

Di f (x) =

∑

S⊆[n]
S3i

f (S) xS\{i}.

(2.2)

Proof. Since Di is a linear operator, the claim follows immediately from the
observation that



Di xS =

xS\{i}

if i ∈ S,

0

if i 6∈ S.



Copyright © Ryan O’Donnell, 2014, 2015, 2016, 2017, 2018, 2019, 2020, 2021.



<!-- pdf-page: 48 -->
48

2. Basic concepts and social choice

By applying Parseval’s Theorem to the Fourier expansion (2.2), we obtain

a Fourier formula for inuences:

Theorem 2.20. For f : {−1, 1}n → and i ∈ [n],
f (S)2.

Infi[ f ] =

∑

S3i

In other words, the inuence of coordinate i on f equals the sum of f ’s
Fourier weights on sets containing i. This is another good example of being
able to “read off ” an interesting combinatorial property of a Boolean function
from its Fourier expansion. In the special case that f : {−1, 1}n → {−1, 1} is
monotone there is a much simpler way to read off its inuences: they are the
degree-1 Fourier coefcients. In what follows, we write f (i) in place of f ({i}).
Proposition 2.21. If f : {−1, 1}n → {−1, 1} is monotone, then Infi[ f ] = f (i).

Proof. By monotonicity, the ±1 in (2.1) is always 1; i.e., Di f (x) is the 0-1
indicator that i is pivotal for x. Hence Infi[ f ] = E[Di f ] = ̂Di f (;) = f (i), where

the third equality used Proposition 2.19.

This formula allows us a neat proof that for any 2-candidate voting rule
that is monotone and transitive-symmetric, all of the voters have small inu-
ence:

Proposition 2.22. Let f : {−1, 1}n → {−1, 1} be transitive-symmetric and mono-
tone. Then Infi[ f ] ≤ 1/

n for all i ∈ [n].

p

Proof. Transitive-symmetry of f implies that f (i) = f (i′) for all i, i′ ∈ [n]
(using Exercise 1.30(a)); thus by monotonicity, Infi[ f ] = f (i) = f (1) for all
f (i)2 = n f (1)2; hence f (1) ≤
f (S)2 ≥
i ∈ [n]. But by Parseval, 1 =

1/

n

i=1

n.

p



S

This bound is slightly improved in Proposition 2.58 and Exercise 2.24.

The derivative operators are very convenient for functions dened on
{−1, 1}n. However they are less natural if we think of the Hamming cube
as {True,False}n; for the more general domains we’ll look at in Chapter 8
they don’t even make sense. We end this section by introducing some useful
denitions that will generalize better later.

Denition 2.23. The ith expectation operator Ei is the linear operator on
functions f : {−1, 1}n → dened by

Ei f (x) = E
xi

[ f (x1, . . . , xi−1, xi, xi+1, . . . , xn)].

Whereas Di f isolates the part of f depending on the ith coordinate, Ei f
isolates the part not depending on the ith coordinate. Exercise 2.15 asks you
to verify the following:

Copyright © Ryan O’Donnell, 2014, 2015, 2016, 2017, 2018, 2019, 2020, 2021.



<!-- pdf-page: 49 -->
2.3. Total inuence

49

Proposition 2.24. For f : {−1, 1}n → ,

• Ei f (x) =

• Ei f (x) =

f (x(i7→1)) + f (x(i7→−1))
2
f (S) xS,

∑

,

S63i
• f (x) = xiDi f (x) + Ei f (x).

Note that in the decomposition f = xiDi f + Ei f , neither Di f nor Ei f de-
pends on xi. This decomposition is very useful for proving facts about Boolean
functions by induction on n.

Finally, we will also dene an operator very similar to Di called the ith

Laplacian:

Denition 2.25. The ith coordinate Laplacian operator Li is dened by

Li f = f − Ei f .

Notational warning: Elsewhere you might see the negated denition, Ei f − f .

Exercise 2.16 asks you to verify the following:

Proposition 2.26. For f : {−1, 1}n → ,

• Li f (x) =

f (x) − f (x⊕i)
2

,
∑

• Li f (x) = xiDi f (x) =

f (S) xS,

• 〈 f , Li f 〉 = 〈Li f , Li f 〉 = Infi[ f ].

S3i

2.3. Total inuence

A very important quantity in the analysis of a Boolean function is the sum of
its inuences.

Denition 2.27. The total inuence of f : {−1, 1}n → is dened to be

I[ f ] =

n∑

i=1

Infi[ f ].

For Boolean-valued functions f : {−1, 1}n → {−1, 1} the total inuence has
several additional interpretations. First, it is often referred to as the average
sensitivity of f because of the following proposition:

Proposition 2.28. For f : {−1, 1}n → {−1, 1}

I[ f ] = E
x

[sens f (x)],

where sens f (x) is the sensitivity of f at x, dened to be the number of pivotal
coordinates for f on input x.

Copyright © Ryan O’Donnell, 2014, 2015, 2016, 2017, 2018, 2019, 2020, 2021.



<!-- pdf-page: 50 -->
50

2. Basic concepts and social choice

Proof.

I[ f ] =

n∑

i=1

n∑

Infi[ f ] =

[ f (x) 6= f (x⊕i)]

Pr
x

i=1
n∑

i=1

=

[1 f (x)6= f (x⊕i)] = E
x



n∑

i=1



1 f (x)6= f (x⊕i)

= E
x

[sens f (x)]. 

E
x

The total inuence of f : {−1, 1}n → {−1, 1} is also closely related to the size

of its edge boundary; from Fact 2.14 we deduce:

Fact 2.29. The fraction of edges in the Hamming cube {−1, 1}n which are
boundary edges for f : {−1, 1}n → {−1, 1} is equal to 1

n I[ f ].

Example 2.30. (Recall Example 2.15.) For Boolean-valued functions f :
{−1, 1}n → {−1, 1} the total inuence ranges between 0 and n. It is minimized
by the constant functions ±1 which have total inuence 0. It is maximized by
the parity function χ[n] and its negation which have total inuence n; every
coordinate is pivotal on every input for these functions. The dictator functions
(and their negations) have total inuence 1. The total inuence of ORn and
ANDn is very small: n21−n. On the other hand, the total inuence of Majn is
fairly large: roughly

n for large n.

2/π

p

p

By virtue of Proposition 2.21 we have another interpretation for the total

inuence of monotone functions:

Proposition 2.31. If f : {−1, 1}n → {−1, 1} is monotone, then

I[ f ] =

n∑

i=1

f (i).

This sum of the degree-1 Fourier coefcients has a natural interpretation

in social choice:

Proposition 2.32. Let f : {−1, 1}n → {−1, 1} be a voting rule for a 2-candidate
election. Given votes x = (x1, . . . , xn), let w be the number of votes that agree
with the outcome of the election, f (x). Then
n∑

E[w] =

+

n
2

1
2

f (i).

i=1

Proof. By the formula for Fourier coefcients,
n∑

n∑

f (i) =

i=1

i=1

E
x

[ f (x)xi] = E
x

[ f (x)(x1 + x2 + · · · + xn)].

(2.3)

Now x1 + · · · + xn equals the difference between the number of votes for can-
didate 1 and the number of votes for candidate −1. Hence f (x)(x1 + · · · + xn)
equals the difference between the number of votes for the winner and the
number of votes for the loser; i.e., w − (n − w) = 2w − n. The result follows. 

Copyright © Ryan O’Donnell, 2014, 2015, 2016, 2017, 2018, 2019, 2020, 2021.



<!-- pdf-page: 51 -->
2.3. Total inuence

51

Rousseau [Rou62] suggested that the ideal voting rule is one which max-
imizes the number of votes that agree with the outcome. Here we show that
the majority rule has this property (at least when n is odd):

Theorem 2.33. The unique maximizers of
{−1, 1} are the majority functions. In particular, I[ f ] ≤ I[Majn] =
O(n−1/2) for all monotone f .

f (i) among all f : {−1, 1}n →
n +

2/π

i=1

p

p

n

Proof. From (2.3),

n∑

i=1

f (i) = E
x

[ f (x)(x1 + x2 + · · · + xn)] ≤ E
x

[|x1 + x2 + · · · + xn|],

since f (x) ∈ {−1, 1} always. Equality holds if and only if f (x) = sgn(x1 + · · · + xn)
whenever x1 + · · · + xn 6= 0. The second statement of the theorem follows from

Proposition 2.31 and Exercise 2.22.

Let’s now take a look at more analytic expressions for the total inuence.

By denition, if f : {−1, 1}n → , then

I[ f ] =

n∑

i=1

Infi[ f ] =

n∑

i=1

E
x

[Di f (x)2] = E
x

This motivates the following denition:



Di f (x)2

.

(2.4)



n∑

i=1

Denition 2.34. The (discrete) gradient operator ∇ maps the function f :
{−1, 1}n → to the function ∇ f : {−1, 1}n → n dened by

∇ f (x) = (D1 f (x), D2 f (x), . . . , Dn f (x)).

Note that for f : {−1, 1}n → {−1, 1} we have ‖∇ f (x)‖2

2 = sens f (x), where ‖·‖2

is the usual Euclidean norm in n. In general, from (2.4) we deduce:

Proposition 2.35. For f : {−1, 1}n → ,

I[ f ] = E
x

[‖∇ f (x)‖2

2].

An alternative analytic denition involves introducing the Laplacian:

Denition 2.36. The Laplacian operator L is the linear operator on functions
f : {−1, 1}n → dened by L =

n

i=1 Li.

Exercise 2.17 asks you to verify the following:

Proposition 2.37. For f : {−1, 1}n → ,




• L f (x) = (n/2)

f (x) − avg
i∈[n]

{ f (x⊕i)}

,

• L f (x) = f (x) · sens f (x)
|S| f (S) χS,
• L f =

∑

S⊆[n]

if f : {−1, 1}n → {−1, 1},

Copyright © Ryan O’Donnell, 2014, 2015, 2016, 2017, 2018, 2019, 2020, 2021.



<!-- pdf-page: 52 -->
52

2. Basic concepts and social choice

• 〈 f , L f 〉 = I[ f ].

We can obtain a Fourier formula for the total inuence of a function using
Theorem 2.20; when we sum that theorem over all i ∈ [n] the Fourier weight
f (S)2 is counted exactly |S| times. Hence:
Theorem 2.38. For f : {−1, 1}n → ,

I[ f ] =

∑

S⊆[n]

|S| f (S)2 =

n∑

k=0

k · Wk[ f ].

(2.5)

For f : {−1, 1}n → {−1, 1} we can express this using the spectral sample:

I[ f ] = E
S∼S f

[|S|].

Thus the total inuence of f : {−1, 1}n → {−1, 1} also measures the average

“height” or degree of its Fourier weights.

Finally, from Proposition 1.13 we have Var[ f ] =

k>0 Wk[ f ]; comparing
this with (2.5) we immediately deduce a simple but important fact called the
Poincaré Inequality.



Poincaré Inequality. For any f : {−1, 1}n → , Var[ f ] ≤ I[ f ].

Equality holds in the Poincaré Inequality if and only if all of f ’s Fourier
weight is at degrees 0 and 1; i.e., W≤1[ f ] = E[ f 2]. For Boolean-valued f :
{−1, 1}n → {−1, 1}, Exercise 1.19 tells us this can only occur if f = ±1 or f = ±χi
for some i.

For Boolean-valued f : {−1, 1}n → , the Poincaré Inequality can be viewed
as an (edge-)isoperimetric inequality, or (edge-)expansion bound, for the Ham-
ming cube. If we think of f as the indicator function for a set A ⊆ {−1, 1}n
of “measure” α = |A|/2n, then Var[ f ] = 4α(1 − α) (Fact 1.14) whereas I[ f ] is n
times the (fractional) size of A’s edge boundary. In particular, the Poincaré
Inequality says that subsets A ⊆ {−1, 1}n of measure α = 1/2 must have edge
boundary at least as large as those of the dictator sets.

For α ∉ {0, 1/2, 1} the Poincaré Inequality is not sharp as an edge-isoperimetric

inequality for the Hamming cube; for small α even the asymptotic depen-
dence is not optimal. Precisely optimal edge-isoperimetric results (and also
vertex-isoperimetric results) are known for the Hamming cube. The following
simplied theorem is optimal for α of the form 2−i:

Theorem 2.39. For f : {−1, 1}n → {−1, 1} with α = min{Pr[ f = 1], Pr[ f = −1]},

2α log(1/α) ≤ I[ f ].

This result illustrates an important recurring concept in the analysis of
Boolean functions: The Hamming cube is a “small-set expander”. Roughly
speaking, this is the idea that “small” subsets A ⊆ {−1, 1}n have unusually
large “boundary size”.

Copyright © Ryan O’Donnell, 2014, 2015, 2016, 2017, 2018, 2019, 2020, 2021.



<!-- pdf-page: 53 -->
2.4. Noise stability

53

2.4. Noise stability

Suppose f : {−1, 1}n → {−1, 1} is a voting rule for a 2-candidate election. Mak-
ing the impartial culture assumption, the n voters independently and uni-
formly randomly choose their votes x = (x1, . . . , xn). Now imagine that when
each voter goes to the ballot box there is some chance that their vote is mis-
recorded. Specically, say that each vote is correctly recorded with probability
ρ ∈ [0, 1] and is garbled – i.e., changed to a random bit – with probability
1 − ρ. Writing y = (y1, . . . , yn) for the votes that are nally recorded, we may
ask about the probability that f (x) = f (y), i.e., whether the misrecorded votes
affected the outcome of the election. This has to do with the noise stability
of f .

Denition 2.40. Let ρ ∈ [0, 1]. For xed x ∈ {−1, 1}n we write y ∼ Nρ(x) to
denote that the random string y is drawn as follows: for each i ∈ [n] indepen-
dently,



yi =

xi
uniformly random with probability 1 − ρ.

with probability ρ,

We extend the notation to all ρ ∈ [−1, 1] as follows:


yi =

with probability 1
xi
−xi with probability 1

2 + 1
2 − 1

2 ρ,
2 ρ.

We say that y is ρ-correlated to x.

Denition 2.41. If x ∼ {−1, 1}n is drawn uniformly at random and then
y ∼ Nρ(x), we say that (x, y) is a ρ-correlated pair of random strings. This def-
inition is symmetric in x and y; it is equivalent to saying that independently
for each i ∈ [n], the pair of random bits (xi, yi) satises E[xi] = E[yi] = 0 and
E[xi yi] = ρ.

With these denitions in hand we can now dene the important concept
of noise stability, which measures the correlation between f (x) and f (y) when
(x, y) is a ρ-correlated pair.

Denition 2.42. For f : {−1, 1}n → and ρ ∈ [−1, 1], the noise stability of f at
ρ is

Stabρ[ f ] =

[ f (x) f (y)].

E
(x,y)
ρ-correlated

If f : {−1, 1}n → {−1, 1} we have

Stabρ[ f ] =

Pr
(x,y)
ρ-correlated

[ f (x) = f (y)] −

[ f (x) 6= f (y)]

Pr
(x,y)
ρ-correlated

= 2

Pr
(x,y)
ρ-correlated

[ f (x) = f (y)] − 1.

Copyright © Ryan O’Donnell, 2014, 2015, 2016, 2017, 2018, 2019, 2020, 2021.



<!-- pdf-page: 54 -->
54

2. Basic concepts and social choice

In the voting scenario described above, the probability that the misrecord-

ing of votes doesn’t affect the election outcome is 1

2 + 1

2 Stabρ[ f ].

When ρ is close to 1 (i.e., the “noise” is small) it’s sometimes more natu-
ral to ask about the probability that reversing a small fraction of the votes
reverses the outcome of the election.

Denition 2.43. For f : {−1, 1}n → {−1, 1} and δ ∈ [0, 1] we write NSδ[ f ] for
noise sensitivity of f at δ, dened to be the probability that f (x) 6= f (y) when
x ∼ {−1, 1}n is uniformly random and y is formed from x by reversing each bit
independently with probability δ. In other words,

NSδ[ f ] =

1
2

−

1
2

Stab1−2δ[ f ].

Example 2.44. The constant functions ±1 have noise stability 1 for ev-
ery ρ. The dictator functions χi satisfy Stabρ[χi] = ρ for all ρ (equivalently,
NSδ[χi] = δ for all δ). More generally,

Stabρ[χS] =

[xS yS] = E

E
(x,y)
ρ-correlated



(xi yi)

=



∏

i∈S

∏

i∈S

E[xi yi] =

∏

i∈S

ρ = ρ|S|,

where we used the fact that the bit pairs (xi, yi) are independent across i to
convert the expectation of a product to a product of an expectation.

There is no convenient expression for the noise stability of the major-
ity function Stabρ[Majn]. However, for a xed noise rate, the noise stabil-
ity/sensitivity tends to a nice limit as n → ∞:

Theorem 2.45. For any ρ ∈ [−1, 1],

Stabρ[Majn] = 2
π

arcsin ρ = 1 − 2
π

arccos ρ.

lim
n→∞
n odd

Equivalently, for δ ∈ [0, 1],

NSδ[Majn] = 1
π

arccos(1 − 2δ).

lim
n→∞
n odd

Using cos(z) = 1 − 1

2 z2 + O(z4), hence arccos(1 − 2δ) = 2

p

δ + O(δ3/2), we deduce

NSδ[Majn] = 2
π

lim
n→∞
n odd

p

δ + O(δ3/2).

Copyright © Ryan O’Donnell, 2014, 2015, 2016, 2017, 2018, 2019, 2020, 2021.



<!-- pdf-page: 55 -->
2.4. Noise stability

55

Figure 2.2. Plot of 2

π arcsin ρ as a function of ρ

We prove Theorem 2.45 in Chapter 5.2.

There is a simple Fourier formula for the noise stability of a Boolean
function; it’s one of the most powerful links between the combinatorics of
Boolean functions and their Fourier spectra. To determine it, we begin by
introducing the most important operator in analysis of Boolean functions: the
noise operator, denoted Tρ for historical reasons.

Denition 2.46. For ρ ∈ [−1, 1], the noise operator with parameter ρ is the
linear operator Tρ on functions f : {−1, 1}n → dened by

Tρ f (x) = E

y∼Nρ(x)

[ f (y)].

Proposition 2.47. For f : {−1, 1}n → , the Fourier expansion of Tρ f is given
by

∑

n∑

Tρ f =

ρ|S| f (S) χS =

ρk f =k.

S⊆[n]

k=0

Proof. Since Tρ is a linear operator, it sufces to verify that TρχS = ρ|S|χS:

TρχS(x) = E

y∼Nρ(x)

[yS] =

E
y∼Nρ(x)

[yi] =

(ρxi) = ρ|S|χS(x).

∏

i∈S

∏

i∈S

Here we used the fact that for y ∼ Nρ(x) the bits yi are independent and

satisfy E[yi] = ρxi.

Exercise 2.25 gives an alternate way of looking at this proof. Yet another proof
using probability densities and convolution is outlined in Exercise 2.30.

The connection between Tρ and noise stability is that

[

]

Stabρ[ f ] =

E
x∼{−1,1}n
y∼Nρ(x)

[ f (x) f (y)] = E
x

f (x) E

y∼Nρ(x)

[ f (y)]

;

Copyright © Ryan O’Donnell, 2014, 2015, 2016, 2017, 2018, 2019, 2020, 2021.



<!-- pdf-page: 56 -->
56

hence:

2. Basic concepts and social choice

Fact 2.48. Stabρ[ f ] = 〈 f , Tρ f 〉.

From Plancherel’s Theorem and Proposition 2.47 we deduce the Fourier

formula for noise stability:

Theorem 2.49. For f : {−1, 1}n → ,

Stabρ[ f ] =

∑

S⊆[n]

ρ|S| f (S)2 =

n∑

k=0

ρk · Wk[ f ].

Hence for f : {−1, 1}n → {−1, 1} we have

Stabρ[ f ] = E
S∼S f

[ρ|S|],

NSδ[ f ] = 1
2

n∑

k=0

(1 − (1 − 2δ)k) · Wk[ f ].

(2.6)

(2.7)

Thus the noise stability of f at ρ is equal to the sum of its Fourier weights,
attenuated by a factor which decreases exponentially with degree. A simple
but important corollary is that dictators (and their negations) maximize noise
stability:

Proposition 2.50. Let ρ ∈ (0, 1). If f : {−1, 1}n → {−1, 1} is unbiased, then
Stabρ[ f ] ≤ ρ, with equality if and only if f = ±χi for some i ∈ [n].


k≥1 ρkWk[ f ].
Proof. For unbiased f we have W0[ f ] = 0 and hence Stabρ[ f ] =
Since ρk < ρ for all k > 1, noise stability is maximized if all of f ’s Fourier
weight is on degree 1. This occurs if and only if f = ±χi, by Exercise 1.19(a).


For a xed function f , it’s often interesting to see how Stabρ[ f ] varies
as a function of ρ. From Theorem 2.49 we see that Stabρ[ f ] is a (univari-
ate) polynomial with nonnegative coefcients; in particular, it’s an increasing
function of ρ on [0, 1]. The derivatives of this polynomial at 0 and 1 have nice
interpretations, as can be immediately deduced from Theorem 2.49:

Proposition 2.51. For f : {−1, 1}n → ,
∣
∣
∣

Stabρ[ f ]

d
dρ
d
dρ

= W1[ f ],

ρ=0

Stabρ[ f ]

∣
∣
∣

ρ=1

= I[ f ].

For f : {−1, 1}n → {−1, 1} we have that NSδ[ f ] is an increasing function of δ on
[0, 1/2], and the second identity is equivalent to

d
dδ

NSδ[ f ]

∣
∣
∣

δ=0

= I[ f ].

Copyright © Ryan O’Donnell, 2014, 2015, 2016, 2017, 2018, 2019, 2020, 2021.



<!-- pdf-page: 57 -->
2.5. Highlight: Arrow’s Theorem

57

We conclude this section by introducing a version of inuences that also

incorporates noise.

Denition 2.52. For f : {−1, 1}n → , ρ ∈ [0, 1] and i ∈ [n], the ρ-stable inu-
ence of i on f is

Inf(ρ)
i

[ f ] = Stabρ[Di f ] =

∑

S3i

ρ|S|−1 f (S)2,

with 00 interpreted as 1. We also dene I(ρ)[ f ] =

n

i=1 Inf(ρ)

i

[ f ].

Exercise 2.40 asks you to verify the following:

Fact 2.53. I(ρ)[ f ] = d
dρ

Stabρ[ f ] =

n

k=1

kρk−1 · Wk[ f ].

i

The ρ-stable inuence Inf(ρ)

[ f ] increases from f (i)2 up to Infi[ f ] as ρ
increases from 0 to 1. For 0 < ρ < 1 there isn’t an especially natural combi-
natorial interpretation for Inf(ρ)
[ f ] beyond Stabρ[Di f ]; however, we will see
later that the stable inuences are technically very useful. One reason for
this is that every function f : {−1, 1}n → {−1, 1} has at most “constantly” many
“stably-inuential” coordinates:

i

Proposition 2.54. Suppose f : {−1, 1}n → has Var[ f ] ≤ 1. Given 0 < δ, ≤ ≤ 1,
let J = {i ∈ [n] : Inf(1−δ)

[ f ] ≥ ≤}. Then |J| ≤ 1
δ≤

.

i

Proof. Certainly |J| ≤ I(1−δ)[ f ]/≤ so it remains to verify I(1−δ)[ f ] ≤ 1/δ. Com-
k6=0 Wk[ f ] term by term, it sufces to show
paring Fact 2.53 with Var[ f ] =
that (1 − δ)k−1k ≤ 1/δ for all k ≥ 1. This is the easy Exercise 2.45.




It’s good to think of the set J in this proposition as the “notable” coor-
dinates for function f . Had we used the usual inuences in place of stable
inuences, we would not have been guaranteed a bounded number of “notable”
coordinates (since, e.g., the parity function χ[n] has all n of its inuences equal
to 1).

2.5. Highlight: Arrow’s Theorem

When there are just 2 candidates, the majority function possesses all of the
mathematical properties that seem desirable in a voting rule (e.g., May’s
Theorem and Theorem 2.33). Unfortunately, as soon as there are 3 (or more)
candidates the problem of social choice becomes much more difcult. For
example, suppose we have candidates a, b, and c, and each of n voters has
a ranking of them. How should we aggregate these preferences to produce a
winning candidate?

Copyright © Ryan O’Donnell, 2014, 2015, 2016, 2017, 2018, 2019, 2020, 2021.



<!-- pdf-page: 58 -->
58

2. Basic concepts and social choice

In his 1785 Essay on the Application of Analysis to the Probability of Ma-
jority Decisions [dC85], Condorcet suggested using the voters’ preferences to
conduct the three possible pairwise elections, a vs. b, b vs. c, and c vs. a. This
calls for the use of a 2-candidate voting rule f : {−1, 1}n → {−1, 1}; Condorcet
suggested f = Majn but we might consider any such rule. Thus a “3-candidate
Condorcet election” using f is conducted as follows:

Voters’ Preferences

#1

#2

#3 · · ·

a (+1) vs. b (−1) +1 +1 −1 · · · = x
b (+1) vs. c (−1) +1 −1 +1 · · · = y
c (+1) vs. a (−1) −1 −1 +1 · · · = z

Societal Aggregation
f (x)
f (y)
f (z)

In the above example, voter #1 ranked the candidates a > b > c, voter #2
ranked them a > c > b, voter #3 ranked them b > c > a, etc. Note that the ith
voter has one of 3! = 6 possible rankings, and these translate into a triple of
bits (xi, yi, zi) from the following set:




(+1, +1, −1), (+1, −1, −1), (−1, +1, −1), (−1, +1, +1), (+1, −1, +1), (−1, −1, +1)

.

These are precisely the triples satisfying the not-all-equal predicate NAE3
(see Exercise 1.1(i)).

In the example above, if n = 3 and f = Maj3 then the societal outcome
would be (+1, +1, −1), meaning that society elects a over b, b over c, and
a over c. In this case it is only natural to declare a the overall winner.

Denition 2.55. In an election employing Condorcet’s method with voting
rule f : {−1, 1}n → {−1, 1}, we say that a candidate is a Condorcet winner if it
wins all of the pairwise elections in which it participates.

Unfortunately, as Condorcet himself noted, there may not be a Condorcet
winner. In the example above, if voter #2’s ranking was instead c > a > b
(corresponding to (+1, −1, +1)), we would obtain the “paradoxical” outcome
(+1, +1, +1): society prefers a over b, b over c, and c over a! This lack of a
Condorcet winner is termed Condorcet’s Paradox; it occurs when the outcome
( f (x), f (y), f (z)) is one of the two “all-equal” triples {(−1, −1, −1), (+1, +1, +1)}.

One might wonder if the Condorcet Paradox can be avoided by using a
voting rule f : {−1, 1}n → {−1, 1} other than majority. However, in 1950 Ar-
row [Arr50] famously showed that the only means of avoidance is an unap-
pealing one:

Arrow’s Theorem. Suppose f : {−1, 1}n → {−1, 1} is a unanimous voting rule
used in a 3-candidate Condorcet election. If there is always a Condorcet winner,
then f must be a dictatorship.

Copyright © Ryan O’Donnell, 2014, 2015, 2016, 2017, 2018, 2019, 2020, 2021.



<!-- pdf-page: 59 -->
2.5. Highlight: Arrow’s Theorem

59

(In fact, Arrow’s Theorem is slightly stronger than this; see Exercise 2.51.)

In 2002 Kalai gave a new proof of Arrow’s Theorem; it takes its cue from
the title of Condorcet’s work and computes the probability of a Condorcet
winner. This is done under the “impartial culture assumption” for 3-candidate
elections: each voter independently chooses one of the 6 possible rankings
uniformly at random.

Theorem 2.56. Consider a 3-candidate Condorcet election using f : {−1, 1}n →
{−1, 1}. Under the impartial culture assumption, the probability of a Condorcet
winner is precisely 3

4 − 3

4 Stab−1/3[ f ].

Proof. Let x, y, z ∈ {−1, 1}n be the votes for the elections a vs. b, b vs. c, and
c vs. a, respectively. Under impartial culture, the bit triples (xi, yi, zi) are
independent and each is drawn uniformly from the 6 triples satisfying the
not-all-equal predicate NAE3 : {−1, 1}3 → {0, 1}. There is a Condorcet winner if
and only if NAE3( f (x), f (y), f (z)) = 1. Hence

Pr[∃ Condorcet winner] = E[NAE3( f (x), f (y), f (z))].

(2.8)

The multilinear (Fourier) expansion of NAE3 is
4 w1w2 − 1
NAE3(w1, w2, w3) = 3

4 − 1

4 w1w3 − 1

4 w2w3;

thus

(2.8) = 3

4 − 1

4 E[ f (x) f (y)] − 1

4 E[ f (x) f (z)] − 1

4 E[ f (y) f (z)].

In the joint distribution of x, y the n bit pairs (xi, yi) are independent. Further,
by inspection we see that E[xi] = E[yi] = 0 and that E[xi yi] = (2/6)(+1) +
(4/6)(−1) = −1/3. Hence E[ f (x) f (y)] is precisely Stab−1/3[ f ]. Similarly we

have E[ f (x) f (z)] = E[ f (y) f (z)] = Stab−1/3[ f ] and the proof is complete.

Arrow’s Theorem is now an easy corollary:

Proof of Arrow’s Theorem. By assumption, the probability of a Condorcet
winner is 1; hence

1 = 3

4 − 3

4 Stab−1/3[ f ] =

3
4

−

3
4

n∑

k=0

(−1/3)kWk[ f ].

Since (−1/3)k ≥ −1/3 for all k, the equality above can only occur if all of f ’s
Fourier weight is on degree 1; i.e., W1[ f ] = 1. By Exercise 1.19(a) this implies
that f is either a dictator or a negated-dictator. Since f is unanimous, it must

in fact be a dictator.

An advantage of Kalai’s analytic proof of Arrow’s Theorem is that we can
deduce several more interesting results about the probability of a Condorcet
winner. For example, combining Theorem 2.56 with Theorem 2.45 we get
Guilbaud’s Formula:

Copyright © Ryan O’Donnell, 2014, 2015, 2016, 2017, 2018, 2019, 2020, 2021.



<!-- pdf-page: 60 -->
60

2. Basic concepts and social choice

Guilbaud’s Formula. In a 3-candidate Condorcet election using Majn, the
probability of a Condorcet winner tends to

as n → ∞.

3
2π

arccos(−1/3) ≈ 91.2%.

This is already a fairly high probability. Unfortunately, if we want to
improve on it while still using a reasonably fair election scheme, we can only
set our hopes higher by a sliver:

Theorem 2.57. In a 3-candidate Condorcet election using an f : {−1, 1}n →
{−1, 1} with all f (i) equal, the probability of a Condorcet winner is at most
9 + 4
7

+ on(1) ≈ 91.9%.

9π

The condition in Theorem 2.57 seems like it would be satised by most
reasonably fair voting rules f : {−1, 1}n → {−1, 1} (e.g., it is satised if f is
transitive-symmetric or is monotone with all inuences equal). In fact, we will
show that Theorem 2.57’s hypothesis can be relaxed in Chapter 5.4; we will
9 + 4
further show in Chapter 11.7 that 7
can be improved to the tight value
9π
3
arccos(−1/3) of majority. To return to Theorem 2.57, it is an immediate
2π
consequence of the following two results, the rst being Exercise 2.24 and the
second being an easy corollary of Theorem 2.56.

Proposition 2.58. Suppose f : {−1, 1}n → {−1, 1} has all f (i) equal. Then
W1[ f ] ≤ 2/π + on(1).
Corollary 2.59. In a 3-candidate Condorcet election using f : {−1, 1}n →
{−1, 1}, the probability of a Condorcet winner is at most 7

9 + 2

9 W1[ f ].

Proof. From Theorem 2.56, the probability is

3

4 − 3

4 Stab−1/3[ f ] = 3
≤ 3

27 W3[ f ] + · · · )

4 − 3
4 + 1
4 + 1
4 + 1

4 (W0[ f ] − 1
4 W1[ f ] + 1
4 W1[ f ] + 1
4 W1[ f ] + 1

3 W1[ f ] + 1
9 W2[ f ] − 1
324 W5[ f ] + · · ·
36 W3[ f ] + 1
36 (W3[ f ] + W5[ f ] + · · · )
36 (1 − W1[ f ]) = 7

9 + 2

≤ 3

≤ 3

9 W1[ f ].



Finally, using Corollary 2.59 we can prove a “robust” version of Arrow’s
Theorem, showing that a Condorcet election is almost paradox-free only if it
is almost a dictatorship (possibly negated).

Corollary 2.60. Suppose that in a 3-candidate Condorcet election using f :
{−1, 1}n → {−1, 1}, the probability of a Condorcet winner is 1 − ≤. Then f is
O(≤)-close to ±χi for some i ∈ [n].

Proof. From Corollary 2.59 we obtain that W1[ f ] ≥ 1 − 9
now follows from the FKN Theorem.

2 ≤. The conclusion


Copyright © Ryan O’Donnell, 2014, 2015, 2016, 2017, 2018, 2019, 2020, 2021.



<!-- pdf-page: 61 -->
2.6. Exercises and notes

61

Friedgut–Kalai–Naor (FKN) Theorem. Suppose f : {−1, 1}n → {−1, 1} has
W1[ f ] ≥ 1 − δ. Then f is O(δ)-close to ±χi for some i ∈ [n].

We will see the proof of the FKN Theorem in Chapter 9.1. We’ll also show
in Chapter 5.4 that the O(δ) closeness can be improved to δ/4 + O(δ2 log(2/δ)).

2.6. Exercises and notes

2.1 For each function in Exercise 1.1, determine if it is odd, transitive-symmetric,

and/or symmetric.

2.2 Show that the n-bit functions majority, AND, OR, ±χi, and ±1 are all

linear threshold functions.

2.3 Prove May’s Theorem:

(a) Show that f : {−1, 1}n → {−1, 1} is symmetric and monotone if and only
if it can be expressed as a weighted majority with a1 = a2 = · · · = an =
1.

(b) Suppose f : {−1, 1}n → {−1, 1} is symmetric, monotone, and odd. Show

that n must be odd, and that f = Majn.

2.4 Subset A ⊆ {−1, 1}n is called a Hamming ball if A = {x : ∆(x, z) < r} for some
z ∈ {−1, 1}n and real r. Show that f : {−1, 1}n → {−1, 1} is the indicator of a
Hamming ball if and only if it’s expressible as a linear threshold function
f (x) = sgn(a0 + a1x1 + · · · + an xn) with |a1| = |a2| = · · · = |an|.

2.5 Let f : {−1, 1}n → {−1, 1} and i ∈ [n]. We say that f is unate in the ith direc-
tion if either f (x(i7→−1)) ≤ f (x(i7→1)) for all x (monotone in the ith direction)
or f (x(i7→−1)) ≥ f (x(i7→1)) for all x (antimonotone in the ith direction). We
say that f is unate if it is unate in all n directions.
(a) Show that | f (i)| ≤ Infi[ f ] with equality if and only if f is unate in the

ith direction.

(b) Show that the second statement of Theorem 2.33 holds even for all

unate f .

2.6 Show that linear threshold functions are unate.

2.7 For each function f in Exercise 1.1, compute Inf1[ f ].
2.8 Let f : {−1, 1}n → {−1, 1}. Without using Fourier formulas, show that
(Hint: Show Infi[ f ] ≤ 2 min{Pr[ f =

Infi[ f ] ≤ Var[ f ] for each i ∈ [n].
−1], Pr[ f = 1]}.)

2.9 Let f : {0, 1}6 → {−1, 1} be given by the weighted majority f (x) = sgn(−58 +
31x1 + 31x2 + 28x3 + 21x4 + 2x5 + 2x6). Compute Infi[ f ] for all i ∈ [6].
2.10 Given b ∈ {−1, 1}, say that coordinate i is b-pivotal for f : {−1, 1}n → {−1, 1}
on input x if f (x) = b and f (x⊕i) 6= b. Show that Prx[i is b-pivotal on x] =
1
2 Infi[ f ]. Deduce that I[ f ] = 2 Ex[# b-pivotal coordinates on x].

Copyright © Ryan O’Donnell, 2014, 2015, 2016, 2017, 2018, 2019, 2020, 2021.



<!-- pdf-page: 62 -->
62

2. Basic concepts and social choice

2.11 Let f : {−1, 1}n → {−1, 1} and suppose f (S) 6= 0. Show that each coordinate

i ∈ S is relevant for f .

2.12 Let f : {−1, 1}n → {−1, 1} be a random function (as in Exercise 1.7). Com-

pute E[Inf1[ f ]] and E[I[ f ]].

2.13 Let w ∈ , n = w2w, and write f for Tribesw,2w : {−1, 1}n → {−1, 1}.

(a) Compute E[ f ] and Var[ f ], and estimate them asymptotically in terms

of n.

(b) Describe the function D1 f .
(c) Compute Inf1[ f ] and I[ f ] and estimate them asymptotically.

2.14 Let f : {−1, 1}n → , and write g = | f |. Show that |Di g| ≤ |Di f | pointwise.

Deduce that Infi[g] ≤ Infi[ f ] and I[g] ≤ I[ f ].

2.15 Prove Proposition 2.24.

2.16 Prove Proposition 2.26.

2.17 Prove Proposition 2.37.
2.18 Let f : {−1, 1}n → . Show that

d
dρ

∣
∣
∣

d
dt

∣
∣
∣

L f (x) =

Tρ f (x)

= −

Te−t f (x)

.

ρ=1
2.19 Suppose f , g : {−1, 1}n → have the property that f does not depend on
the ith coordinate and g does not depend on the jth coordinate (i 6= j).
Show that E[xi x j f (x)g(x)] = E[D j f (x)Di g(x)].

t=0

2.20 For f : {−1, 1}n → {−1, 1} we have that E[sens f (x)] = ES∼S f

[|S|]. Show that
also E[sens f (x)2] = E[|S|2]. (Hint: Use Proposition 2.37.) Is it true that
E[sens f (x)3] = E[|S|3]?
2.21 Let f : {−1, 1}n → and i ∈ [n].

(a) Dene Vari f : {−1, 1}n → by

Vari f (x) = Var

xi

[ f (x1, . . . , xi−1, xi, xi+1, . . . , xn)].

Show that Infi[ f ] = Ex[Vari f (x)].

(b) Show that

Infi[ f ] = 1
2

E
xi,x′
i∼{−1,1}
independent

[∥
∥
∥ f|xi

]

,

∥
∥
∥

2

2

− f|x′

i

where f|b denotes the function of n − 1 variables gotten by xing the
ith input of f to bit b.

2.22 (a) Show that Infi[Majn] =

21−n for all i ∈ [n].

n−1



n−1
2

(b) Show that Inf1[Majn] is a decreasing function of (odd) n.
(c) Use Stirling’s Formula m! = (m/e)m(
p
2/πp
n

Inf1[Majn] =

+ O(n−3/2). (Here the O(·) terms are nonnegative.)

2πm + O(m−1/2)) to deduce that

p

(d) Deduce that 2/π ≤ W1[Majn] ≤ 2/π + O(n−1).

Copyright © Ryan O’Donnell, 2014, 2015, 2016, 2017, 2018, 2019, 2020, 2021.



<!-- pdf-page: 63 -->
2.6. Exercises and notes

63

p

p

p

p

(e) Deduce that
(f ) Suppose n is even and f : {−1, 1}n → {−1, 1} is a majority function.
2/π

Show that I[ f ] = I[Majn−1] =

n ≤ I[Majn] ≤

n + O(n−1/2).

n + O(n−1/2).

2/π

2/π

p

p

2.23 Using only Cauchy–Schwarz and Parseval, give a very simple proof of the
following weakening of Theorem 2.33: If f : {−1, 1}n → {−1, 1} is monotone
then I[ f ] ≤

n. Extend also to the case of f unate (see Exercise 2.5).

p

2.24 Prove Proposition 2.58 with O(n−1) in place of on(1). (Hint: Show f (i) ≤

p
2/πp
n

+ O(n−3/2) using Theorem 2.33.)



S ρ|S| f (S) xS using Exercise 1.4.
2.25 Deduce Tρ f (x) =
2.26 For each function f in Exercise 1.1, compute I[ f ].
2.27 Which functions f : {−1, 1}n → {−1, 1} with #{x : f (x) = 1} = 3 maximize I[ f ]?
2.28 Suppose f : {−1, 1}n → is an even function (recall Exercise 1.8). Show

the improved Poincaré Inequality Var[ f ] ≤ 1

2 I[ f ].

2.29 Let f : {−1, 1}n → {−1, 1} be unbiased, E[ f ] = 0, and let MaxInf[ f ] denote

maxi∈[n]{Infi[ f ]}.
(a) Use the Poincaré Inequality to show MaxInf[ f ] ≥ 1/n.
(b) Prove that I[ f ] ≥ 2 − nMaxInf[ f ]2. (Hint: Prove I[ f ] ≥ W1[ f ] + 2(1 −

W1[ f ]) and use Exercise 2.5.) Deduce that MaxInf[ f ] ≥ 2

2.30 Use Exercises 1.1(e),(f ) to deduce the formulas Ei f =



Tρ f =

S ρ|S| f (S) χS.

2.31 Show that Tρ is positivity-preserving for ρ ∈ [−1, 1]; i.e., f ≥ 0 =⇒ Tρ f ≥ 0.
Show that Tρ is positivity-improving for ρ ∈ (−1, 1); i.e., f ≥ 0, f 6= 0 =⇒
Tρ f > 0.

2.32 Show that Tρ satises the semigroup property: Tρ1
2.33 For ρ ∈ [−1, 1], show that Tρ is a contraction on L p({−1, 1}n) for all p ≥ 1;

= Tρ1ρ2

Tρ2

.

i.e., ‖Tρ f ‖p ≤ ‖ f ‖p for all f : {−1, 1}n → .

2.34 Show that |Tρ f | ≤ Tρ| f | pointwise for any f : {−1, 1}n → . Further show
that for −1 < ρ < 1, equality occurs if and only if f is everywhere nonneg-
ative or everywhere nonpositive.

2.35 For i ∈ [n] and ρ ∈ , let Ti

ρ be the operator on functions f : {−1, 1}n →

dened by

Ti

ρ f = ρ f + (1 − ρ)Ei f = Ei f + ρLi f .

(a) Show that for ρ ∈ [−1, 1] we have

Ti

ρ f (x) =

E
yi∼Nρ(xi)

[ f (x1, . . . , xi−1, yi, xi+1, . . . , xn)].

(b) Show that Ti
Ti
= Ti
ρ1
ρ2
ρ1ρ2
ρ and T j
ρ′ commute.

tors Ti

(cf. Exercise 2.32) and that any two opera-

Copyright © Ryan O’Donnell, 2014, 2015, 2016, 2017, 2018, 2019, 2020, 2021.

n − 4
n2 .
f (S) χS and



S63i



<!-- pdf-page: 64 -->
64

2. Basic concepts and social choice

(c) For (ρ1, . . . , ρn) ∈

. Show that
T(ρ,...,ρ) is simply Tρ and that T(1,...,1,ρ,1,...,1) (with the ρ in the ith
position) is Ti
ρ.

n we dene T(ρ1,...,ρn) = T1
ρ1

· · · Tn
ρn

T2
ρ2

(d) For ρ1, . . . , ρn ∈ [−1, 1], show that T(ρ1,...,ρn) is a contraction on L p({−1, 1}n)

for all p ≥ 1 (cf. Exercise 2.33).

2.36 Show that Stab−ρ[ f ] = −Stabρ[ f ] if f is odd and Stab−ρ[ f ] = Stabρ[ f ] if

f is even.

2.37 For each function f in Exercise 1.1, compute Stabρ[ f ].
2.38 Compute Stabρ[Tribesw,s].
2.39 Suppose f : {−1, 1}n → {−1, 1} has min(Pr[ f = 1], Pr[ f = −1]) = α. Show

that NSδ[ f ] ≤ 2α for all δ ∈ [0, 1].

2.40 Verify Fact 2.53.
2.41 Fix f : {−1, 1}n → . Show that Stabρ[ f ] is a convex function of ρ on [0, 1].
2.42 Let f : {−1, 1}n → {−1, 1}. Show that NSδ[ f ] ≤ δI[ f ] for all δ ∈ [0, 1].
2.43 (a) Dene the average inuence of f : {−1, 1}n → to be EEE [ f ] = 1

n I[ f ]. Now

for f : {−1, 1}n → {−1, 1}, show

EEE [ f ] = Pr

x∼{−1,1}n
i∼[n]

[ f (x) 6= f (x⊕i)] and 1−e−2

2 EEE [ f ] ≤ NS1/n[ f ] ≤ EEE [ f ].

(b) Given f : {−1, 1}n → {−1, 1} and integer k ≥ 2, dene

Ak =

1
k

(W≥1[ f ] + W≥2[ f ] + · · · + W≥k[ f ]),

the “average of the rst k tail weights”. Generalizing the second
statement in part (a), show that 1−e−2

2 Ak ≤ NS1/k[ f ] ≤ Ak.

2.44 Suppose f1, . . . , f s : {−1, 1}n → {−1, 1} satisfy NSδ[ f i] ≤ ≤i. Let g : {−1, 1}s →
{−1, 1} and dene h : {−1, 1}n → {−1, 1} by h = g( f1, . . . , f s). Show that
NSδ[h] ≤

s

i=1 ≤i.

2.45 Complete the proof of Proposition 2.54 by showing that (1 − δ)k−1k ≤ 1/δ
for all 0 < δ ≤ 1 and k ∈ +. (Hint: Compare both sides with 1 + (1 − δ) +
(1 − δ)2 + · · · + (1 − δ)k−1.)

2.46 Fixing f : {−1, 1}n → , show the following Lipschitz bound for Stabρ[ f ]

when 0 ≤ ρ − ≤ ≤ ρ < 1:

∣
∣Stabρ[ f ] − Stabρ−≤[ f ]

∣
∣ ≤ ≤ ·

1
1 − ρ

· Var[ f ].

(Hint: Use the Mean Value Theorem and Exercise 2.45.)

2.47 Let f : {−1, 1}n → {−1, 1} be a transitive-symmetric function; in the nota-
tion of Exercise 1.30, this means the group Aut( f ) acts transitively on [n].
Show that Prπ∼Aut( f )[π(i) = j] = 1/n for all i, j ∈ [n].

Copyright © Ryan O’Donnell, 2014, 2015, 2016, 2017, 2018, 2019, 2020, 2021.



<!-- pdf-page: 65 -->
2.6. Exercises and notes

65



2.48 Suppose that F is a functional on functions f : {−1, 1}n → expressible
f (S)2 where cS ≥ 0 for all S ⊆ [n]. (Examples include Var,
, and Stabρ for ρ ≥ 0.) Show that F is convex, meaning

as F[ f ] =
Wk, Infi, I, Inf(1−δ)
F[λ f + (1 − λ)g] ≤ λ F[ f ] + (1 − λ) F[g] for all f , g, and λ ∈ [0, 1].

S cS

i

2.49 Extend the FKN Theorem as follows: Suppose f : {−1, 1}n → {−1, 1} has
W≤1[ f ] ≥ 1 − δ. Show that f is O(δ)-close to a 1-junta. (Hint: Consider
g(x0, x) = x0 f (x0x).)

2.50 Compute the precise probability of a Condorcet winner (under impartial

culture) in a 3-candidate, 3-voter election using f = Maj3.

2.51 (a) Arrow’s Theorem for 3 candidates is slightly more general than what
we stated: it allows for three different unanimous functions f , g, h :
{−1, 1}n → {−1, 1} to be used in the three pairwise elections. But show
that if using f , g, h always gives rise to a Condorcet winner then
f = g = h. (Hint: First show g(x) = − f (−x) for all x by using the fact
that x, y = −x, and z = ( f (x), . . . , f (x)) is always a valid possibility for
the votes.)

(b) Extend Arrow’s Theorem to the case of Condorcet elections with more

than 3 candidates.

2.52 The polarizations of f : {−1, 1}n → (also known as compressions, down-
shifts, or two-point rearrangements) are dened as follows. For i ∈ [n],
the i-polarization of f is the function f σi : {−1, 1}n → dened by



f σi (x) =

max{ f (x(i7→+1)), f (x(i7→−1))}
min { f (x(i7→+1)), f (x(i7→−1))}

if xi = +1,
if xi = −1.

(a) Show that E[ f σi ] = E[ f ] and ‖ f σi ‖p = ‖ f ‖p for all p.
(b) Show that Inf j[ f σi ] ≤ Inf j[ f ] for all j ∈ [n].
(c) Show that Stabρ[ f σi ] ≥ Stabρ[ f ] for all 0 ≤ ρ ≤ 1.
(d) Show that f σi is monotone in the ith direction (recall Exercise 2.5).
Further, show that if f is monotone in the jth direction for some
j ∈ [n] then f σi is still monotone in the jth direction.

(e) Let f ∗ = f σ1σ2···σn . Show that f ∗ is monotone, E[ f ∗] = E[ f ], Inf j[ f ∗] ≤
Inf j[ f ] for all j ∈ [n], and Stabρ[ f ∗] ≥ Stabρ[ f ] for all 0 ≤ ρ ≤ 1.

2.53 The Hamming distance ∆(x, y) = #{i : xi 6= yi} on the discrete cube {−1, 1}n
is an example of an `1 metric space. For D ≥ 1, we say that the discrete
cube can be embedded into `2 with distortion D if there is a mapping
F : {−1, 1}n → m for some m ∈

such that:

‖F(x) − F(y)‖2 ≥ ∆(x, y) for all x, y;
‖F(x) − F(y)‖2 ≤ D · ∆(x, y) for all x, y.

(“no contraction”)

(“expansion at most D”)

In this exercise you will show that the least distortion possible is D =

p

n.

Copyright © Ryan O’Donnell, 2014, 2015, 2016, 2017, 2018, 2019, 2020, 2021.



<!-- pdf-page: 66 -->
66

2. Basic concepts and social choice

(a) Recalling the denition of f odd from Exercise 1.8, show that for any

f : {−1, 1}n → we have ‖ f odd‖2

2 ≤ I[ f ] and hence

[( f (x) − f (−x))2] ≤

E
x

f (x) − f (x⊕i)



2

.



n∑

i=1

E
x

(b) Suppose F : {−1, 1}n → m, and write F(x) = ( f1(x), f2(x), . . . , f m(x)) for
functions f i : {−1, 1}n → . By summing the above inequality over
i ∈ [m], show that any F with no contraction must have expansion at
least

n.

p

(c) Show that there is an embedding F achieving distortion

n.

p

2.54 Give a Fourier-free proof of the Poincaré Inequality by induction on n.

2.55 Let V be a vector space with norm ‖ · ‖ and x w1, . . . , wn ∈ V . Dene
i=1 xiwi‖.

g : {−1, 1}n → by g(x) = ‖
(a) Show that Lg ≤ g pointwise. (Hint: Triangle inequality.)
(b) Deduce 2 Var[g] ≤ E[g2] and thus the following Khintchine–Kahane

n

Inequality:

[∥
∥
∥
∥

n

i=1

E
x

]

∥
∥
∥
∥

≥

1
p

2

· E
x

[∥
∥
∥
∥

n

i=1

2]1/2

∥
∥
∥
∥

.

xiwi

xiwi

(Hint: Exercise 2.28.)
(c) Show that the constant 1p
2

above is optimal, even if V = .

2.56 In the correlation distillation problem, a source chooses x ∼ {−1, 1}n uni-
formly at random and broadcasts it to q parties. We assume that the
transmissions suffer from some kind of noise, and therefore the players
receive imperfect copies y(1), . . . , y(q) of x. The parties are not allowed to
communicate, and despite having imperfectly correlated information they
wish to agree on a single random bit. In other words, the jth party will
output a bit f j(y( j)) ∈ {−1, 1}, and the goal is to nd functions f1, . . . , f q that
maximize the probability that f1(y(1)) = f2(y(2)) = · · · = f q(y(q)). To avoid
trivial deterministic solutions, we insist that E[ f j(y( j))] be 0 for all j ∈ [q].
(a) Suppose q = 2, ρ ∈ (0, 1), and y( j) ∼ Nρ(x) independently for each j.
Show that the optimal solution is f1 = f2 = ±χi for some i ∈ [n]. (Hint:
You’ll need Cauchy–Schwarz.)

(b) Show the same result for q = 3.
(c) Let q = 2 and ρ ∈ ( 1

2 , 1). Suppose that y(1) = x exactly, but y(2) ∈
{−1, 0, 1}n has erasures: it’s formed from x by setting y(2)
= xi with
probability ρ and y(2)
= 0 with probability 1 − ρ, independently for
all i ∈ [n]. Show that the optimal success probability is 1
2 ρ and
there is an optimal solution in which f1 = ±χi for any i ∈ [n]. (Hint:
Eliminate the source, and introduce a ctitious party 1′. . . )

2 + 1

i

i

Copyright © Ryan O’Donnell, 2014, 2015, 2016, 2017, 2018, 2019, 2020, 2021.



<!-- pdf-page: 67 -->
n (assuming δ ≤ 1/4). Deduce W1[g] ≤

2.6. Exercises and notes

67

(d) Consider the previous scenario but with ρ ∈ (0, 1

2 ). Show that if n is

sufciently large, then the optimal solution does not have f1 = ±χi.

2.57 (a) Let g : {−1, 1}n → ≥0 have E[g] = δ. Show that for any ρ ∈ [0, 1],

ρ

n∑

j=1

| g( j)| ≤ δ +

n∑

k=2

ρk‖g=k‖∞.

(Hint: Exercise 2.31.)

(b) Assume further that g : {−1, 1}n → {0, 1}. Show that ‖g=k‖∞ ≤

2.) Deduce ρ

j=1 | g( j)| ≤ δ + 2ρ2

δn, assum-

n

p

δ

n



k

.

p

(Hint: First bound ‖g=k‖2
ing ρ ≤ 1
p
2

.
n
n
(c) Show that
2 · δ7/4p
p

p

2

W2[ f ] ≤

2 · δ3/4 · I[ f ] ·

n.

p

p

j=1 | g( j)| ≤ 2

2δ3/4p
n. (Hint: show | g( j)| ≤ δ for all j.)

(d) Suppose f : {−1, 1}n → {−1, 1} is monotone and MaxInf[ f ] ≤ δ. Show

(e) Suppose further that f is unbiased. Show that MaxInf[ f ] ≤ o(n−2/3)
implies I[ f ] ≥ 3− o(1); conclude MaxInf[ f ] ≥ 3
n − o(1/n). (Hint: Extend
Exercise 2.29.) Use Exercise 2.52 to remove the assumption that f is
monotone for these statements.

2.58 Let V be a vector space (over

) with norm ‖ · ‖V . If f : {−1, 1}n → V we
can dene its Fourier coefcients f (S) ∈ V by the usual formula f (S) =
Ex∈{−1,1}n [ f (x)xS]. We may also dene ‖ f ‖p = Ex∈{−1,1}n [‖ f (x)‖p
]1/p. Fi-
V
nally, if the norm ‖ · ‖V arises from an inner product 〈·, ·〉V on V we
can dene an inner product on functions f , g : {−1, 1}n → V by 〈 f , g〉 =
Ex∈{−1,1}n [〈 f (x), g(x)〉V ]. The material developed so far in this book has
used V = with 〈·, ·〉V being multiplication. Explore the extent to which
this material extends to the more general setting.

Notes. The mathematical study of social choice began in earnest in the late
1940s; see Riker [Rik61] for an early survey or the compilation [BGR09]
for some modern results. Arrow’s Theorem was the eld’s rst major re-
sult; Arrow proved it in 1950 [Arr50] under the extra assumption of mono-
tonicity (and with a minor error [Bla57]), with the rened version appearing
in 1963 [Arr63]. He was awarded the Nobel Prize for this work in 1972.
May’s Theorem is from 1952 [May52]. Guilbaud’s Formula is also from
1952 [Gui52], though Guilbaud only stated it in a footnote and wrote that it is
computed “by the usual means in combinatorial analysis”. The rst published
proof appears to be due to Garman and Kamien [GK68]; they also introduced
the impartial culture assumption. The term “junta” appears to have been
introduced by Parnas, Ron, and Samorodnitsky [PRS01].

The notion of inuence Infi[ f ] was originally introduced by the geneticist
. It was rediscovered

Penrose [Pen46], who observed that Infi[Majn] ∼

p
2/πp
n

Copyright © Ryan O’Donnell, 2014, 2015, 2016, 2017, 2018, 2019, 2020, 2021.



<!-- pdf-page: 68 -->
68

2. Basic concepts and social choice

by the lawyer Banzhaf in 1965 [Ban65]; he sued the Nassau County (NY)
Board after proving that the voting system it used (the one in Exercise 2.9)
gave some towns zero inuence. Inuence is sometimes referred to as the
Banzhaf, Penrose–Banzhaf, or Banzhaf–Coleman index (Coleman being an-
other rediscoverer [Col71]). Inuences were rst studied in the computer
science literature by Ben-Or and Linial [BL85]; they introduced also intro-
duced “tribes” as an example of a function with constant variance yet small
inuences. The Fourier formulas for inuence may have rst appeared in the
work of Chor and Geréb-Graus [CGG87].

Total inuence of Boolean functions has long been studied in combina-
torics, since it is equivalent to edge-boundary size for subsets of the Ham-
ming cube. For example, the edge-isoperimetric inequality was rst proved
by Harper in 1964 [Har64]. In the context of Boolean functions, Karpovsky
[Kar76] proposed I[ f ] as a measure of the computational complexity of f ,
S |S| f (S)2.
and Hurst, Miller, and Muzio [HMM82] gave the Fourier formula
The terminology “Poincaré Inequality” comes from the theory of functional
inequalities and Markov chains; the inequality is equivalent to the spectral
gap for the discrete cube graph.



The noise stability of Boolean functions was rst studied explicitly by
Benjamini, Kalai, and Schramm in 1999 [BKS99], though it plays an impor-
tant role in the earlier work of Håstad [Hås97]. See O’Donnell [O’D03] for a
survey. The noise operator was introduced by Bonami [Bon70] and indepen-
dently by Beckner [Bec75], who used the notation Tρ which was standardized
by Kahn, Kalai, and Linial [KKL88]. For nonnegative noise rates it’s often
natural to use the alternate parameterization Te−t for t ∈ [0, ∞].

The Fourier approach to Arrow’s Theorem is due to Kalai [Kal02]; he
also proved Theorem 2.57 and Corollary 2.60. The FKN Theorem is due to
Friedgut, Kalai, and Naor [FKN02]; the observation from Exercise 2.49 is
due to Kindler.

The polarizations from Exercise 2.52 originate in Kleitman [Kle66]. Exer-
cise 2.53 is a theorem of Eno from 1970 [Enf70]. Exercise 2.55 is a theorem
of Latała and Oleszkiewicz [LO94]. In Exercise 2.56, part (b) is due to Mos-
sel and O’Donnell [MO05]; part (c) was conjectured by Yang [Yan04] and
proved by O’Donnell and Wright [OW12]. Exercise 2.57 is a polishing of the
1987 work by Chor and Geréb-Graus [CGG87, CGG88], a precursor of the
KKL Theorem. The weaker Exercise 2.29 is also due to them and Noga Alon
independently.

Copyright © Ryan O’Donnell, 2014, 2015, 2016, 2017, 2018, 2019, 2020, 2021.



<!-- pdf-page: 69 -->
Chapter 3

Spectral structure and
learning

One reasonable way to assess the “complexity” of a Boolean function is in
terms how complex its Fourier spectrum is. For example, functions with
sufciently simple Fourier spectra can be efciently learned from examples.
This chapter will be concerned with understanding the location, magnitude,
and structure of a Boolean function’s Fourier spectrum.

3.1. Low-degree spectral concentration

One way a Boolean function’s Fourier spectrum can be “simple” is for it to be
mostly concentrated at small degree.

Denition 3.1. We say that the Fourier spectrum of f : {−1, 1}n → is ≤-
concentrated on degree up to k if

W>k[ f ] =

f (S)2 ≤ ≤.

∑

S⊆[n]
|S|>k

For f : {−1, 1}n → {−1, 1} we can express this condition using the spectral
sample: PrS∼S f

[|S| > k] ≤ ≤.

It’s possible to show such a concentration result combinatorially by show-

ing that a function has small total inuence:

Proposition 3.2. For any f : {−1, 1}n → and ≤ > 0, the Fourier spectrum of
f is ≤-concentrated on degree up to I[ f ]/≤.

Copyright © Ryan O’Donnell, 2014, 2015, 2016, 2017, 2018, 2019, 2020, 2021.

69



<!-- pdf-page: 70 -->
70

3. Spectral structure and learning

k · Wk[ f ].
Proof. This follows immediately from Theorem 2.38, I[ f ] =
For f : {−1, 1}n → {−1, 1}, this is Markov’s inequality applied to the cardinality

of the spectral sample.

k=0

n

For example, in Exercise 2.13 you showed that I[Tribesw,2w ] ≤ O(log n),
where n = w2w; thus this function’s spectrum is .01-concentrated on degree
up to O(log n), a rather low level. Proving this by explicitly calculating Fourier
coefcients would be quite painful.

Another means of showing low-degree spectral concentration is through

noise stability/sensitivity:

Proposition 3.3. For any f : {−1, 1}n → {−1, 1} and δ ∈ (0, 1/2], the Fourier
spectrum of f is ≤-concentrated on degree up to 1/δ for

≤ = 2

1−e−2 NSδ[ f ] ≤ 3NSδ[ f ].

Proof. Using the Fourier formula from Theorem 2.49,

2NSδ[ f ] = E
S∼S f

[1 − (1 − 2δ)|S|]

≥ (1 − (1 − 2δ)1/δ) · Pr
S∼S f

[|S| ≥ 1/δ]

≥ (1 − e−2) · Pr
S∼S f

[|S| ≥ 1/δ],

where the rst inequality used that 1−(1−2δ)k is a nonnegative nondecreasing

function of k. The claim follows.

p

As an example, Theorem 2.45 tells us that for δ > 0 sufciently small and n
δ. Hence the Fourier
sufciently large (as a function of δ), NSδ[Majn] ≤
δ-concentrated on degree up to 1/δ; equivalently, it
spectrum of Majn is 3
is ≤-concentrated on degree up to 9/≤2.
(We will give sharp constants for
majority’s spectral concentration in Chapter 5.3.) This example also shows
there is no simple converse to Proposition 3.2; although Majn has its spectrum
.01-concentrated on degree up to O(1), its total inuence is Θ(

n).

p

p

Finally, suppose a function f : {−1, 1}n → {−1, 1} has its Fourier spectrum
0-concentrated up to degree k; in other words, f has real degree deg( f ) ≤ k. In
this case f must be somewhat simple; indeed, if k is a constant, then f is a
junta:

Theorem 3.4. Suppose f : {−1, 1}n → {−1, 1} has deg( f ) ≤ k. Then f is a k2k−1-
junta.

The bound k2k−1 cannot be signicantly improved; see Exercise 3.24. The
key to proving Theorem 3.4 is the following lemma, the proof of which is
outlined in Exercise 3.4:

Copyright © Ryan O’Donnell, 2014, 2015, 2016, 2017, 2018, 2019, 2020, 2021.



<!-- pdf-page: 71 -->
3.2. Subspaces and decision trees

71

Lemma 3.5. Suppose deg( f ) ≤ k, where f : {−1, 1}n → is not identically 0.
Then Pr[ f (x) 6= 0] ≥ 2−k.

Since deg(Di f ) ≤ k − 1 when deg( f ) ≤ k (by the “differentiation” formula)
and since Infi[ f ] = Pr[Di f (x) 6= 0] for Boolean-valued f , we immediately infer:

Proposition 3.6. If f : {−1, 1}n → {−1, 1} has deg( f ) ≤ k then Infi[ f ] is either 0
or at least 21−k for all i ∈ [n].

We can now give the proof of Theorem 3.4. From Proposition 3.6 the
number of coordinates which have nonzero inuence on f is at most I[ f ]/21−k,
and this in turn is at most k2k−1 by the following fact:

Fact 3.7. For f : {−1, 1}n → {−1, 1}, I[ f ] ≤ deg( f ).

Fact 3.7 is immediate from the Fourier formula for total inuence.

We remark that the FKN Theorem (stated in Chapter 2.5) is a “robust”
version of Theorem 3.4 for k = 1. In Chapter 9.6 we will see Friedgut’s Junta
Theorem, a related robust result showing that if I[ f ] ≤ k then f is ≤-close to a
2O(k/≤)-junta.

3.2. Subspaces and decision trees

n
2 , an n-
In this section we will treat the domain of a Boolean function as
dimensional vector space over the eld 2. As mentioned in Chapter 1.2, it
n
can be natural to index the Fourier characters χS :
2 → {−1, 1} not by subsets
S ⊆ [n] but by their 0-1 indicator vectors γ ∈ n

2 ; thus

χγ(x) = (−1)γ·x,

with the dot product γ·x being carried out in n
we’d write χ0 for the constantly 1 function and χe i
now becomes

2 . For example, in this notation
for the ith dictator. Fact 1.6

χβχγ = χβ+γ ∀β, γ.

(3.1)

Thus the characters form a group under multiplication, which is isomorphic
n
2 under addition. To distinguish this group from the input
to the group
domain we write it as n
2 ; we also tend to identify the character with its index.
Thus the Fourier expansion of f :

n
2 → can be written as
∑

f (x) =

f (γ)χγ(x).

γ∈ n
2

The Fourier transform of f can be thought of as a function f : n

2 → . We

can measure its complexity with various norms.

Copyright © Ryan O’Donnell, 2014, 2015, 2016, 2017, 2018, 2019, 2020, 2021.



<!-- pdf-page: 72 -->
72

3. Spectral structure and learning

Denition 3.8. The Fourier (or spectral) p-norm of f : {−1, 1}n → is




1/p

| f (γ)|p



.

ˆ‖ f ˆ‖p =



∑

γ∈ n
2

Note that we use the “counting measure” on n

2 , and hence we have a nice
rephrasing of Parseval’s Theorem: ‖ f ‖2 = ˆ‖ f ˆ‖2. We make two more denitions
relating to the simplicity of f :

Denition 3.9. The Fourier (or spectral) sparsity of f : {−1, 1}n → is

sparsity( f ) = |supp( f )| = #



γ ∈ n

2 : f (γ) 6= 0



.

Denition 3.10. We say that f is ≤-granular if f (γ) is an integer multiple
of ≤ for all γ ∈ n
2 .

To gain some practice with this notation, let’s look at the Fourier trans-
n
2 → {0, 1} and probability density
2 is a subspace. Then one

forms of some indicator functions 1A :
functions ϕA, where A ⊆ n
way to characterize A is by its perpendicular subspace A⊥:

2 . First, suppose A ≤ n

A⊥ = {γ ∈ n

2 : γ · x = 0 for all x ∈ A}.

It holds that dim A⊥ = n − dim A (this is called the codimension of A) and that
A = (A⊥)⊥.

Proposition 3.11. If A ≤ n
2 has codim A = dim A⊥ = k, then
∑

∑

1A =

2−kχγ,

ϕA =

χγ.

γ∈A⊥

γ∈A⊥

Proof. Let γ1, . . . , γk form a basis of A⊥. Since A = (A⊥)⊥ it follows that x ∈ A
if and only if χγi

(x) = 1 for all i ∈ [k]. We therefore have

1A(x) =



k∏

i=1

1

2 + 1

2 χγi



(x)

= 2−k

∑

χγ(x)

γ∈span{γ1,...,γk}

as claimed, where the last equality used (3.1). The Fourier expansion of ϕA
follows because E[1A] = 2−k.


More generally, suppose A is afne subspace (or coset) of

for some H ≤ n

2 and a ∈ n

2 , or equivalently

n
2 ; i.e., A = H +a

A = {x ∈ n

2 : γ · x = γ · a for all γ ∈ H⊥}.

Then it is easy (Exercise 3.11) to extend Proposition 3.11 to:

Copyright © Ryan O’Donnell, 2014, 2015, 2016, 2017, 2018, 2019, 2020, 2021.



<!-- pdf-page: 73 -->
3.2. Subspaces and decision trees

73

Proposition 3.12. If A = H + a is an afne subspace of codimension k, then



1A(γ) =

χγ(a)2−k
0

if γ ∈ H⊥

else;



γ∈H⊥ χγ(a)χγ. We have sparsity( 1A) = 2k, 1A is 2−k-granular,

hence ϕA =
ˆ‖1A

ˆ‖∞ = 2−k, and ˆ‖1A

ˆ‖1 = 1.

In computer science terminology, any f :

n
2 → {0, 1} that is a conjunction
of parity conditions is the indicator of an afne subspace (or the zero function).
In the simple case that the parity conditions are all of the form “xi = ai”, the
function is a logical AND of literals, and we call the afne subspace a subcube.

Another class of Boolean functions with simple Fourier spectra are the

ones computable by simple decision trees:

Denition 3.13. A decision tree T is a representation of a Boolean function
n
f :
2 → . It consists of a rooted binary tree in which the internal nodes are
labeled by coordinates i ∈ [n], the outgoing edges of each internal node are
labeled 0 and 1, and the leaves are labeled by real numbers. We insist that no
coordinate i ∈ [n] appears more than once on any root-to-leaf path.

On input x ∈ n

2 , the tree T constructs a computation path from the root
node to a leaf. Specically, when the computation path reaches an internal
node labeled by coordinate i ∈ [n] we say that T queries xi; the computation
path then follows the outgoing edge labeled by xi. The output of T (and
hence f ) on input x is the label of the leaf reached by the computation path.
We often identify a tree with the function it computes.

For decision trees, a picture is worth a thousand words; see Figure 3.1.

Figure 3.1. Decision tree computing Sort3

(It’s traditional to write xi rather than i for the internal node labels.) For
example, the computation path of the above tree on input x = (0, 1, 0) ∈ 3
2
starts at the root, queries x1, proceeds left, queries x3, proceeds left, queries

Copyright © Ryan O’Donnell, 2014, 2015, 2016, 2017, 2018, 2019, 2020, 2021.



<!-- pdf-page: 74 -->
74

3. Spectral structure and learning

x2, proceeds right, and reaches a leaf labeled 0. In fact, this tree computes the
function Sort3 dened by Sort3(x) = 1 if and only if x1 ≤ x2 ≤ x3 or x1 ≥ x2 ≥ x3.

Denition 3.14. The size s of a decision tree T is the total number of leaves.
The depth k of T is the maximum length of any root-to-leaf path. For decision
n
trees over
2 → we write DT( f )
(respectively, DTsize( f )) for the least depth (respectively, size) of a decision
tree computing f . (Note that these are not necessarily achieved by the same
tree.)

2 we have k ≤ n and s ≤ 2k. Given f :

n

The example decision tree above has size 6 and depth 3.

Let T be a decision tree computing f :

n
2 → and let P be one of its
root-to-leaf paths. The set of inputs x that follow computation path P in T is
n
precisely a subcube of
2 , call it CP . The function f is constant on CP ; we
will call its value there f (P). Further, since every input x follows a unique
n
2 . These
path in T, the subcubes {CP : P a path in T} form a partition of
observations yield the following “spectral simplicity” results for decision trees:

Fact 3.15. Let f :

n
2 → be computed by a decision tree T. Then

∑

f =

f (P) · 1CP

.

Proposition 3.16. Let f :
and depth k. Then:

n
2 → be computed by a decision tree T of size s

paths P of T

• deg( f ) ≤ k;
• sparsity( f ) ≤ s2k ≤ 4k;
• ˆ‖ f ˆ‖1 ≤ ‖ f ‖∞ · s ≤ ‖ f ‖∞ · 2k;
• f is 2−k-granular assuming f :

n
2 → .

n
Proposition 3.17. Let f :
2 → {−1, 1} be computable by a decision tree of
size s and let ≤ ∈ (0, 1]. Then the spectrum of f is ≤-concentrated on degree up
to log(s/≤).

You are asked to prove these propositions in Exercises 3.21 and 3.22. Sim-
ilar spectral simplicity results hold for some generalizations of the decision
tree representation (“subcube partitions”, “parity decision trees”); see Exer-
cise 3.26.

3.3. Restrictions

A common operation on Boolean functions f : {−1, 1}n → is restriction to
subcubes. Suppose [n] is partitioned into two sets, J and J = [n] \ J. If the
inputs bits in J are xed to constants, the result is a function {−1, 1}J → .
For example, if we take the function Maj5 : {−1, 1}5 → {−1, 1} and restrict the

Copyright © Ryan O’Donnell, 2014, 2015, 2016, 2017, 2018, 2019, 2020, 2021.



<!-- pdf-page: 75 -->
3.3. Restrictions

75

4th and 5th coordinates to be 1 and −1 respectively, we obtain the function
Maj3 : {−1, 1}3 → {−1, 1}. If we further restrict the 3rd coordinate to be −1, we
obtain the two-bit function which is 1 if and only if both input bits are 1.

We introduce following notation:

Denition 3.18. Let f : {−1, 1}n → and let (J, J) be a partition of [n]. Let
z ∈ {−1, 1}J. Then we write f J|z : {−1, 1}J → (pronounced “the restriction
of f to J using z”) for the subfunction of f given by xing the coordinates
in J to the bit values z. When the partition (J, J) is understood we may
write simply f|z. If y ∈ {−1, 1}J and z ∈ {−1, 1}J we will sometimes write (y, z)
for the composite string in {−1, 1}n, even though y and z are not literally
concatenated; with this notation, f J|z(y) = f (y, z).

Let’s examine how restrictions affect the Fourier transform by considering

an example.

Example 3.19. Let f : {−1, 1}4 → {−1, 1} be the function dened by

f (x) = 1 ⇐⇒ x3 = x4 = −1 or x1 ≥ x2 ≥ x3 ≥ x4 or x1 ≤ x2 ≤ x3 ≤ x4.

You can check that f has the Fourier expansion

f (x) = + 1

8 − 1
8 x1 + 1
8 x1x2 + 1
8 x1x2x3 + 1

+ 3

+ 1

8 x2 − 1
8 x1x3 − 3

8 x3 − 1
8 x4
8 x1x4 + 3

8 x1x2x4 − 1

8 x2x3 − 1
8 x1x3x4 + 1

8 x2x4 + 5
8 x2x3x4 − 1

8 x3x4
8 x1x2x3x4.

(3.2)

(3.3)

Consider the restriction x3 = 1, x4 = −1, and let f ′ = f{1,2}|(1,−1) be the restricted
function of x1 and x2. From the original denition (3.2) of f we see that
f ′(x1, x2) is 1 if and only if x1 = x2 = 1. This is the min2 function of x1 and x2,
which we know has Fourier expansion

f ′(x1, x2) = min2(x1, x2) = − 1

2 + 1

2 x1 + 1

2 x2 + 1

2 x1x2.

(3.4)

We can of course obtain this expansion simply by plugging x3 = 1, x4 = −1
into (3.3). Now suppose we only wanted to know the coefcient on x1 in the
Fourier expansion of f ′. We can nd it as follows: Consider all monomials
in (3.3) that contain x1 and possibly also x3, x4; substitute x3 = 1, x4 = −1 into
the associated terms; and sum the results. The relevant terms in (3.3) are
− 1
8 x1x3x4, and substituting in x3 = 1, x4 = −1 gives us
− 1

8 x1x4, − 1
2 , as expected from (3.4).

8 x1x3, − 3
8 = 1
8 + 1

8 x1, + 1
8 + 3
8 + 1

Now we work out these ideas more generally. In the setting of Deni-
tion 3.18 the restricted function f J|z has {−1, 1}J as its domain. Thus its
Fourier coefcients are indexed by subsets of J. Let’s introduce notation for
the Fourier coefcients of a restricted function:

Copyright © Ryan O’Donnell, 2014, 2015, 2016, 2017, 2018, 2019, 2020, 2021.



<!-- pdf-page: 76 -->
76

3. Spectral structure and learning

Denition 3.20. Let f : {−1, 1}n → and let (J, J) be a partition of [n]. Let
S ⊆ J. Then we write F

f : {−1, 1}J → for the function ̂f J|•(S); i.e.,

S|J

F

S|J

f (z) = ̂f J|z(S).

When the partition (J, J) is understood we may write simply FS| f .

In Example 3.19 we considered J = {3, 4}, S = {1}, and z = (1, −1). See

Figure 3.2 for an illustration of a typical restriction scenario.

Figure 3.2. Notation for a typical restriction scenario. Note that J and J
need not be literally contiguous.

In general, for a xed partition (J, J) of [n] and a xed S ⊆ J, we may wish
to know what ̂f J|z(S) is as a function of z ∈ {−1, 1}J. This is precisely asking for
f has domain {−1, 1}J,
the Fourier transform of F

f . Since the function F

S|J

S|J

its Fourier transform has coefcients indexed by subsets of J. The formula
for this Fourier transform generalizes the computation we used at the end of
Example 3.19:

Proposition 3.21. In the setting of Denition 3.20 we have the Fourier expan-
sion

F

S|J

f (z) =

∑

f (S ∪ T)zT ;

i.e.,

T⊆J

ÉF
S|J

f (T) = f (S ∪ T).

Proof. (The S = ; case here is Exercise 1.15.) Every U ⊆ [n] indexing f ’s
Fourier coefcients can be written as a disjoint union U = S ∪ T, where S ⊆ J
and T ⊆ J. We can also decompose any x ∈ {−1, 1}n into two substrings y ∈
{−1, 1}J and z ∈ {−1, 1}J. We have xU = yS zT and so
∑

 ∑

∑

∑



f (x) =

f (U) xU =

f (S ∪ T) yS zT =

f (S ∪ T) zT

yS.

U⊆[n]

S⊆J
T⊆J

S⊆J

T⊆J

Thus when z is xed, the resulting function of y indeed has
as its Fourier coefcient on the monomial yS.



T⊆J

f (S ∪ T) zT


Copyright © Ryan O’Donnell, 2014, 2015, 2016, 2017, 2018, 2019, 2020, 2021.



<!-- pdf-page: 77 -->
3.3. Restrictions

77

Corollary 3.22. Let f : {−1, 1}n → , let (J, J) be a partition of [n], and x
S ⊆ J. Suppose z ∼ {−1, 1}J is chosen uniformly at random. Then

[ ̂f J|z(S)] = f (S),

E
z
[ ̂f J|z(S)2] =

E
z

∑

T⊆J

f (S ∪ T)2.

Proof. The rst statement is immediate from Proposition 3.21, taking T = ;
and unraveling the denition. As for the second statement,

E
z

[ ̂f J|z(S)2] = E
[F
z
∑

=

=

T⊆J
∑

T⊆J

f (z)2]

S|J
ÉF
S|J

f (T)2

(by denition)

(Parseval)

f (S ∪ T)2

(Proposition 3.21) 

We move on to discussing a more general kind of restriction; namely,
n
restricting a function f :
2 → to an afne subspace H + z. This generalizes
restriction to subcubes as we’ve seen so far, by considering H = span{e i : i ∈ J}
for a given subset J ⊆ [n]. For restrictions to a subspace H ≤ n
2 we have a
natural denition:

Denition 3.23. If f :
for the restriction of f to H.

n

2 → and H ≤ n

2 is a subspace, we write f H : H →

For restrictions to afne subspaces, we run into difculties if we try to
extend our notation for restrictions to subcubes. Unlike in the subcube case
of H = span{e i : i ∈ J}, we don’t in general have a canonical isomorphism
between H and a coset H + z. Thus it’s not natural to introduce notation
such as f H|z : H → for the function h 7→ f (h + z), because such a denition
depends on the choice of representative for H + z. As an example consider
H = {(0, 0), (1, 1)} ≤ 2
2, a 1-dimensional subspace (which satises H⊥ = H).
Here the nontrivial coset is H + (1, 0) = H + (0, 1) = {(1, 0), (0, 1)}, which has no
canonical representative.

To get around this difculty we can view restriction to a coset H + z as
consisting of two steps: rst, translation of the domain by a xed representa-
tive z, and then restriction to the subspace H. Let’s introduce some notation
for the rst operation:

Denition 3.24. Let f :
f +z :

2 → by f +z(x) = f (x + z).

n

n

2 → and let z ∈ n

2 . We dene the function

By substituting x = x + z into the Fourier expansion of f , we deduce:

Copyright © Ryan O’Donnell, 2014, 2015, 2016, 2017, 2018, 2019, 2020, 2021.



<!-- pdf-page: 78 -->
78

3. Spectral structure and learning

Fact 3.25. The Fourier coefcients of f +z are given by ̂f +z(γ) = (−1)γ·z f (γ); i.e.,

f +z(x) =

∑

γ∈ n
2

χγ(z) f (γ) χγ(x).

(This fact also follows by noting that f +z = ϕ{z} ∗ f ; see Exercise 3.31.)

We can now give notation for the restriction of a function to an afne

subspace:

Denition 3.26. Let f :
for the function ( f +z)H; namely, the restriction of f to coset H + z with the
representative z made explicit.

2 . We write f +z

2 → , z ∈ n

2 , H ≤ n

: H →

H

n

. These can be indexed by the cosets of H⊥ in n

Finally, we would like to consider Fourier coefcients of restricted func-
tions f +z
2 . However, we again
H
have a notational difculty since the only coset with a canonical representa-
tive is H⊥ itself, with representative 0. There is no need to introduce extra
notation for ̂f +z
H

(0), the average value of f on coset H + z, since it is just

[ f (h + z)] = 〈ϕH, f +z〉.

E
h∼H

Applying Plancherel on the right-hand side, as well as Proposition 3.11 and
Fact 3.25, we deduce the following classical fact:

Poisson Summation Formula. Let f :

∑

n

2 → , H ≤ n
χγ(z) f (γ).

2 , z ∈ n

2 . Then

[ f (h + z)] =

E
h∼H

γ∈H⊥

3.4. Learning theory

Computational learning theory is an area of algorithms research devoted to
the following task: Given a source of “examples” (x, f (x)) from an unknown
function f , compute a “hypothesis” function h that is good at predicting f (y)
on future inputs y. In this book we will focus on just one possible formulation
of the task:

Denition 3.27. In the model of PAC (“Probably Approximately Correct”)
learning under the uniform distribution on {−1, 1}n, a learning problem is
identied with a concept class C , which is just a collection of functions f :
{−1, 1}n → {−1, 1}. A learning algorithm A for C is a randomized algorithm
which has limited access to an unknown target function f ∈ C . The two access
models, in increasing order of strength, are:

• random examples, meaning A can draw pairs (x, f (x)) where x ∈ {−1, 1}n

is uniformly random;

Copyright © Ryan O’Donnell, 2014, 2015, 2016, 2017, 2018, 2019, 2020, 2021.



<!-- pdf-page: 79 -->
3.4. Learning theory

79

• queries, meaning A can request the value f (x) for any x ∈ {−1, 1}n of its

choice.

In addition, A is given as input an accuracy parameter ≤ ∈ [0, 1/2]. The output
of A is required to be (the circuit representation of) a hypothesis function
h : {−1, 1}n → {−1, 1}. We say that A learns C with error ≤ if for any f ∈ C ,
with high probability A outputs an h which is ≤-close to f :
i.e., satises
dist( f , h) ≤ ≤.

In the above denition, the phrase “with high probability” can be xed
to mean, say, “except with probability at most 1/10”.
(As is common with
randomized algorithms, the choice of constant 1/10 is unimportant; see Exer-
cise 3.40.)

For us, the main desideratum of a learning algorithm is efcient running
time. One can easily learn any function f to error 0 in time O(2n) (see Exer-
cise 3.33); however, this is not very efcient. If the concept class C contains
very complex functions, then such exponential running time is necessary;
however, if C contains only relatively “simple” functions, then more efcient
learning may be possible. For example, the results of Section 3.5 show that
the concept class

C = { f :

n
2 → {−1, 1} | DTsize( f ) ≤ s}

can be learned with queries to error ≤ by an algorithm whose running time is
poly(s, n, 1/≤).

A common way of trying to learn an unknown target f : {−1, 1}n → {−1, 1}
is by discovering “most of ” its Fourier spectrum. To formalize this, let’s gener-
alize Denition 3.1:

Denition 3.28. Let F be a collection of subsets S ⊆ [n]. We say that the
Fourier spectrum of f : {−1, 1}n → is ≤-concentrated on F if

∑

f (S)2 ≤ ≤.

S⊆[n]
S∉F

For f : {−1, 1}n → {−1, 1} we can express this condition using the spectral
sample: PrS∼S f

[S ∉ F ] ≤ ≤.

Most functions don’t have their Fourier spectrum concentrated on a small
collection (see Exercise 3.35). But for those that do, we may hope to discover
“most of ” their Fourier coefcients. The main result of this section is a kind of
“meta-algorithm” for learning an unknown target f . It reduces the problem of
learning f to the problem of identifying a collection of characters on which f ’s
Fourier spectrum is concentrated.

Theorem 3.29. Assume learning algorithm A has (at least) random example
access to target f : {−1, 1}n → {−1, 1}. Suppose that A can – somehow – identify a

Copyright © Ryan O’Donnell, 2014, 2015, 2016, 2017, 2018, 2019, 2020, 2021.



<!-- pdf-page: 80 -->
80

3. Spectral structure and learning

collection F of subsets on which f ’s Fourier spectrum is ≤/2-concentrated. Then
using poly(|F |, n, 1/≤) additional time, A can with high probability output a
hypothesis h that is ≤-close to f .

The idea of the theorem is that A will estimate all of f ’s Fourier coef-
cients in F , obtaining a good approximation to f ’s Fourier expansion. Then
A’s hypothesis will be the sign of this approximate Fourier expansion.

The rst tool we need to prove Theorem 3.29 is the ability to accurately

estimate any xed Fourier coefcient:

Proposition 3.30. Given access to random examples from f : {−1, 1}n →
{−1, 1}, there is a randomized algorithm which takes as input S ⊆ [n], 0 <
δ, ≤ ≤ 1/2, and outputs an estimate f (S) for f (S) that satises

| f (S) − f (S)| ≤ ≤

except with probability at most δ. The running time is poly(n, 1/≤) · log(1/δ).

Proof. We have f (S) = Ex[ f (x)χS(x)]. Given random examples (x, f (x)), the
algorithm can compute f (x)χS(x) ∈ {−1, 1} and therefore empirically estimate
Ex[ f (x)χS(x)]. A standard application of the Chernoff bound implies that
O(log(1/δ)/≤2) examples are sufcient to obtain an estimate within ±≤ with

probability at least 1 − δ.

The second observation we need to prove Theorem 3.29 is the following:

Proposition 3.31. Suppose that f : {−1, 1}n → {−1, 1} and g : {−1, 1}n →
satisfy ‖ f − g‖2
with sgn(0) chosen arbitrarily from {−1, 1}. Then dist( f , h) ≤ ≤.

2 ≤ ≤. Let h : {−1, 1}n → {−1, 1} be dened by h(x) = sgn(g(x)),

Proof. Since | f (x) − g(x)|2 ≥ 1 whenever f (x) 6= sgn(g(x)), we conclude

dist( f , h) = Pr
x

[ f (x) 6= h(x)] = E
x

[1 f (x)6=sgn(g(x))] ≤ E
x

[| f (x)− g(x)|2] = ‖ f − g‖2

2. 

(See Exercise 3.34 for an improvement to this argument.)

We can now prove Theorem 3.29:

Proof of Theorem 3.29. For each S ∈ F the algorithm uses Proposition 3.30
to produce an estimate f (S) for f (S) which satises | f (S)− f (S)| ≤
|F |)
except with probability at most 1/(10|F |). Overall this requires poly(|F |, n, 1/≤)
time, and by the union bound, except with probability at most 1/10 all |F |
estimates have the desired accuracy. Finally, A forms the real-valued function
f (S)χS and outputs hypothesis h = sgn(g). By Proposition 3.31, it
g =

≤/(2

p

p



S∈F

Copyright © Ryan O’Donnell, 2014, 2015, 2016, 2017, 2018, 2019, 2020, 2021.



<!-- pdf-page: 81 -->
3.4. Learning theory

81

Åf − g(S)2

(Parseval)

sufces to show that ‖ f − g‖2

2 ≤ ≤. And indeed,

∑

‖ f − g‖2

2 =

=

≤

S⊆[n]
∑

( f (S) − f (S))2 +

∑

S∉F

f (S)2

S∈F

∑

S∈F

 p
p

)2

≤

2

|F |

+ ≤/2

(estimates, concentration assumption)

= ≤/4 + ≤/2 ≤ ≤,

as desired.



As we described, Theorem 3.29 reduces the algorithmic task of learning f
to the algorithmic task of identifying a collection F on which f ’s Fourier
spectrum is concentrated. In Section 3.5 we will describe the Goldreich–Levin
algorithm, a sophisticated way to nd such an F assuming query access to f .
For now, though, we observe that for several interesting concept classes we
don’t need to do any algorithmic searching for F ; we can just take F to be
all sets of small cardinality. This works whenever all functions in C have
low-degree spectral concentration.

The “Low-Degree Algorithm”. Let k ≥ 1 and let C be a concept class for
which every function f : {−1, 1}n → {−1, 1} in C is ≤/2-concentrated up to de-
gree k. Then C can be learned from random examples only with error ≤ in time
poly(nk, 1/≤).

Proof. Apply Theorem 3.29 with F = {S ⊆ [n] : |S| ≤ k}. We have |F | =
k


≤ O(nk).



n
j

j=0

The Low-Degree Algorithm reduces the algorithmic problem of learning C
from random examples to the analytic task of showing low-degree spectral
concentration for the functions in C . Using the results of Section 3.1 we can
quickly obtain some learning-theoretic results. For example:

Corollary 3.32. For t ≥ 1, let C = { f : {−1, 1}n → {−1, 1} | I[ f ] ≤ t}. Then C is
learnable from random examples with error ≤ in time nO(t/≤).

Proof. Use the Low-Degree Algorithm with k = 2t/≤; the result follows from

Proposition 3.2.

Corollary 3.33. Let C = { f : {−1, 1}n → {−1, 1} | f is monotone}. Then C is
learnable from random examples with error ≤ in time nO(

n/≤).

p

Proof. Follows from the previous corollary and Theorem 2.33.



Copyright © Ryan O’Donnell, 2014, 2015, 2016, 2017, 2018, 2019, 2020, 2021.



<!-- pdf-page: 82 -->
82

3. Spectral structure and learning

You might be concerned that a running time such as nO(

n) does not
seem very efcient. Still, it’s much better than the trivial running time of
O(2n). Further, as we will see in the next section, learning algorithms are
sometimes used in attacks on cryptographic schemes, and in this context even
subexponential-time algorithms are considered dangerous.

p

Continuing with applications of the Low-Degree Algorithm:

Corollary 3.34. For δ ∈ (0, 1/2], let C = { f : {−1, 1}n → {−1, 1} | NSδ[ f ] ≤ ≤/6}.
Then C is learnable from random examples with error ≤ in time poly(n1/δ, 1/≤).

Proof. Follows from Proposition 3.3.



Corollary 3.35. Let C = { f : {−1, 1}n → {−1, 1} | DTsize( f ) ≤ s}. Then C is
learnable from random examples with error ≤ in time nO(log(s/≤)).

Proof. Follows from Proposition 3.17.



With a slight extra twist one can also exactly learn the class of degree-k

functions in time poly(nk); see Exercise 3.36:

Theorem 3.36. Let k ≥ 1 and let C = { f : {−1, 1}n → {−1, 1} | deg( f ) ≤ k} (e.g., C
contains all depth-k decision trees). Then C is learnable from random exam-
ples with error 0 in time nk · poly(n, 2k).

3.5. Highlight: the Goldreich–Levin Algorithm

We close this chapter by briey describing a topic which is in some sense the
“opposite” of learning theory: cryptography. At the highest level, cryptography
is concerned with constructing functions which are computationally easy to
compute but computationally difcult to invert. Intuitively, think about the
task of encrypting secret messages: You would like a scheme where it’s easy
to take any message x and produce an encrypted version e(x), but where it’s
hard for an adversary to compute x given e(x). Indeed, even with examples
e(x(1)), . . . , e(x(m)) of several encryptions, it should be hard for an adversary
to learn anything about the encrypted messages, or to predict (“forge”) the
encryption of future messages.

A basic task in cryptography is building stronger cryptographic functions
from weaker ones. Often the rst example in “Cryptography 101” is the
Goldreich–Levin Theorem, which is used to build a “pseudorandom generator”
from a “one-way permutation”. We sketch the meaning of these terms and
the analysis of the construction in Exercise 3.45; for now, sufce it to say that
the key to the analysis of Goldreich and Levin’s construction is a learning
algorithm. Specically, the Goldreich–Levin learning algorithm solves the
n
2 → 2, nd
following problem: Given query access to a target function f :

Copyright © Ryan O’Donnell, 2014, 2015, 2016, 2017, 2018, 2019, 2020, 2021.



<!-- pdf-page: 83 -->
3.5. Highlight: the Goldreich–Levin Algorithm

83

all of the linear functions (in the sense of Chapter 1.6) with which f is at
least slightly correlated. Equivalently, nd all of the noticeably large Fourier
coefcients of f .

Goldreich–Levin Theorem. Given query access to a target f : {−1, 1}n →
{−1, 1} as well as input 0 < τ ≤ 1, there is a poly(n, 1/τ)-time algorithm that
with high probability outputs a list L = {U1, . . . ,U`} of subsets of [n] such that:

• | f (U)| ≥ τ =⇒ U ∈ L;
• U ∈ L =⇒ | f (U)| ≥ τ/2.

(By Parseval’s Theorem, the second guarantee implies that |L| ≤ 4/τ2.)

Although the Goldreich–Levin Theorem was originally developed for cryp-
tography, it was soon put to use for learning theory. Recall that the “meta-
algorithm” of Theorem 3.29 reduces learning an unknown target f : {−1, 1}n →
{−1, 1} to identifying a collection F of sets on which f ’s Fourier spectrum is
≤/2-concentrated. Using the Goldreich–Levin Algorithm, a learner with query
access to f can “collect up” its largest Fourier coefcients until only ≤/2 Fourier
weight remains unfound. This strategy straightforwardly yields the following
result (see Exercise 3.39):

Theorem 3.37. Let C be a concept class such that every f : {−1, 1}n → {−1, 1}
in C has its Fourier spectrum ≤/4-concentrated on a collection of at most M
sets. Then C can be learned using queries with error ≤ in time poly(M, n, 1/≤).

The algorithm of Theorem 3.37 is often called the Kushilevitz–Mansour Al-
gorithm. Much like the Low-Degree Algorithm, it reduces the computational
problem of learning C (using queries) to the analytic problem of proving that
the functions in C have concentrated Fourier spectra. The advantage of the
Kushilevitz–Mansour Algorithm is that it works so long as the Fourier spec-
trum of f is concentrated on some small collection of sets; the Low-Degree
Algorithm requires that the concentration specically be on the low-degree
characters. The disadvantage of the Kushilevitz–Mansour Algorithm is that
it requires query access to f , rather than just random examples. An example
concept class for which the Kushilevitz–Mansour Algorithm works well is the
set of all f for which ˆ‖ f ˆ‖1 is not too large:

Theorem 3.38. Let C = { f : {−1, 1}n → {−1, 1} | ˆ‖ f ˆ‖1 ≤ s} (e.g., C contains
any f computable by a decision tree of size at most s). Then C is learnable
from queries with error ≤ in time poly(n, s, 1/≤).

This is proved in Exercise 3.38.

Copyright © Ryan O’Donnell, 2014, 2015, 2016, 2017, 2018, 2019, 2020, 2021.



<!-- pdf-page: 84 -->
84

3. Spectral structure and learning

Let’s now return to the Goldreich–Levin Algorithm itself, which seeks
the Fourier coefcients f (U) with magnitude at least τ. Given any candi-
date U ⊆ [n], Proposition 3.30 lets us easily distinguish whether the associ-
ated coefcient is large, | f (U)| ≥ τ, or small, | f (U)| ≤ τ/2. The trouble is that
there are 2n potential candidates. The Goldreich–Levin Algorithm overcomes
this difculty using a divide-and-conquer strategy that measures the Fourier
weight of f on various collections of sets. Let’s make a denition:

Denition 3.39. Let f : {−1, 1}n → and S ⊆ J ⊆ [n]. We write

WS|J[ f ] =

∑

T⊆J

f (S ∪ T)2

for the Fourier weight of f on sets whose restriction to J is S.

The crucial tool for the Goldreich–Levin Algorithm is Corollary 3.22,

which says that

WS|J[ f ] =

E
z∼{−1,1}J
This identity lets a learning algorithm with query access to f efciently esti-
mate any WS|J[ f ] of its choosing. Intuitively, query access to f allows query
access to f J|z for any z ∈ {−1, 1}J; with this one can estimate any ̂f J|z(S) and
hence (3.5). More precisely:

(3.5)

[ ̂f J|z(S)2].

Proposition 3.40. For any S ⊆ J ⊆ [n] an algorithm with query access to
f : {−1, 1}n → {−1, 1} can compute an estimate of WS|J[ f ] that is accurate to
within ±≤ (except with probability at most δ) in time poly(n, 1/≤) · log(1/δ).

Proof. From (3.5),





WS|J[ f ] =

E
z∼{−1,1}J

[ ̂f J|z(S)2] =

E
z∼{−1,1}J

E
y∼{−1,1}J

[ f (y, z)χS(y)]2

=

E
z∼{−1,1}J

E
y,y′∼{−1,1}J

[ f (y, z)χS(y) · f (y′, z)χS(y′)],

where y, y′ are independent. As in Proposition 3.30, f (y, z)χS(y)· f (y′, z)χS(y′)
is a ±1-valued random variable that the algorithm can sample from using
queries to f . A Chernoff bound implies that O(log(1/δ)/≤2) samples are suf-

cient to estimate its mean with accuracy ≤ and condence 1 − δ.

We’re now ready to prove the Goldreich–Levin Theorem.

Proof of the Goldreich–Levin Theorem. We begin with an overview of
how the algorithm works. Initially, all 2n sets U are (implicitly) put in a
single “bucket”. The algorithm then repeats the following loop:

• Select any bucket B containing 2m sets, m ≥ 1.

Copyright © Ryan O’Donnell, 2014, 2015, 2016, 2017, 2018, 2019, 2020, 2021.



<!-- pdf-page: 85 -->
3.6. Exercises and notes

85

• Split it into two buckets B1, B2 of 2m−1 sets each.
• “Weigh” each Bi, i = 1, 2; i.e., estimate
• Discard B1 or B2 if its weight estimate is at most τ2/2.

f (U)2.

U∈Bi



The algorithm stops once all buckets contain just 1 set; it then outputs the
list of these sets.

We now ll in the details. First we argue the correctness of the algorithm,
assuming all weight estimates are accurate (this assumption is removed later).
On one hand, any set U with | f (U)| ≥ τ will never be discarded, since it
always contributes weight at least τ2 ≥ τ2/2 to the bucket it’s in. On the other
hand, no set U with | f (U)| ≤ τ/2 can end up in a singleton bucket because
such a bucket, when created, would have weight only τ2/4 ≤ τ2/2 and thus
be discarded. Notice that this correctness proof does not rely on the weight
estimates being exact; it sufces for them to be accurate to within ±τ2/4.

The next detail concerns running time. Note that any “active” (undis-
carded) bucket has weight at least τ2/4, even assuming the weight estimates
are only accurate to within ±τ2/4. Therefore Parseval tells us there can only
ever be at most 4/τ2 active buckets. Since a bucket can be split only n times, it
follows that the algorithm repeats its main loop at most 4n/τ2 times. Thus as
long as the buckets can be maintained and accurately weighed in poly(n, 1/τ)
time, the overall running time will be poly(n, 1/τ) as claimed.

Finally, we describe the bucketing system. The buckets are indexed (and
thus maintained implicitly) by an integer 0 ≤ k ≤ n and a subset S ⊆ [k]. The
bucket Bk,S is dened by





Bk,S =

S ∪ T : T ⊆ {k + 1, k + 2, . . . , n}

.

Note that |Bk,S| = 2n−k. The initial bucket is B0,;. The algorithm always
splits a bucket Bk,S into the two buckets Bk+1,S and Bk+1,S∪{k+1}. The
nal singleton buckets are of the form Bn,S = {S}. Finally, the weight of
bucket Bk,S is precisely WS|{k+1,...,n}[ f ]. Thus it can be estimated to accuracy
±τ2/4 with condence 1 − δ in time poly(n, 1/τ) · log(1/δ) using Proposition 3.40.
Since the main loop is executed at most 4n/τ2 times, the algorithm overall
needs to make at most 8n/τ2 weighings; by setting δ = τ2/(80n) we ensure that
all weighings are accurate with high probability (at least 9/10). The overall

running time is therefore indeed poly(n, 1/τ).

3.6. Exercises and notes

3.1 Let M :

let f ◦ M :

n

2 → n

2 be an invertible linear transformation. Given f :

n
2 → ,
2 → be dened by f ◦ M(x) = f (M x). Show that Éf ◦ M(γ) =

n

Copyright © Ryan O’Donnell, 2014, 2015, 2016, 2017, 2018, 2019, 2020, 2021.



<!-- pdf-page: 86 -->
86

3. Spectral structure and learning

f (M−γ). What if M is an invertible afne transformation? What if M is
not invertible?

3.2 Show that

2

1−e−2 is smallest constant (not depending on δ or n) that can

be taken in Proposition 3.3.

3.3 Generalize Proposition 3.3 by showing that any f : {−1, 1}n → is ≤-
concentrated on degree up to 1/δ for ≤ = (E[ f 2] − Stab1−δ[ f ])/(1 − 1/e).
3.4 Prove Lemma 3.5 by induction on n. (Hint: If one of the subfunctions
f (x1, . . . , xn, ±1) is identically 0, show that the other has degree at most k−
1.)

3.5 Verify for all p ∈ [1, ∞] that ˆ‖· ˆ‖p is a norm on the vector space of functions

f :

n
2 → .

3.6 Show that ˆ‖ f g ˆ‖1 ≤ ˆ‖ f ˆ‖1
3.7 Let f : {−1, 1}n → and let J ⊆ [n], z ∈ {−1, 1}J.

ˆ‖g ˆ‖1 for all f , g :

n
2 → .

(a) Show that restriction reduces spectral 1-norm: ˆ‖ f J|z
(b) Show that it also reduces Fourier sparsity: sparsity( ̂f J|z) ≤ sparsity( f ).
3.8 Let f : {−1, 1}n → and let 0 < p ≤ q ≤ ∞. Show that ˆ‖ f ˆ‖p ≥ ˆ‖ f ˆ‖q. (Cf. Ex-

ˆ‖1 ≤ ˆ‖ f ˆ‖1.

ercise 1.13.)

3.9 Let f : {−1, 1}n → . Show that ˆ‖ f ˆ‖∞ ≤ ‖ f ‖1 and ‖ f ‖∞ ≤ ˆ‖ f ˆ‖1. (These are

easy special cases of the Hausdorff–Young Inequality.)

3.10 Suppose f : {−1, 1}n → {−1, 1} is monotone. Show that | f (S)| ≤ f (i) when-
ever i ∈ S ⊆ [n]. Deduce that ˆ‖ f ˆ‖∞ = maxS{| f (S)|} is achieved by an S of
cardinality 0 or 1. (Hint: Apply the previous exercise to f ’s derivatives.)

3.11 Prove Proposition 3.12.

3.12 Verify Parseval’s Theorem for the Fourier expansion of subspaces given

in Proposition 3.11.

3.13 Let f :

n

2 → {0, 1} be the indicator of A ⊆ n

2 . We know that ˆ‖ f ˆ‖1 = 1 if A

is an afne subspace. So assume that A is not an afne subspace.
(a) Show that there exists an afne subspace B of dimension 2 on which f

takes the value 1 exactly 3 times.

(b) Let b be the point in B where f is 0 and let ψ = ϕB − (1/2)ϕb. Show

that ˆ‖ψˆ‖∞ = 1/2.

(c) Show that 〈ψ, f 〉 = 3/4 and deduce ˆ‖ f ˆ‖1 ≥ 3/2.

3.14 Suppose f : {−1, 1}n → satises E[ f 2] ≤ 1. Show that ˆ‖ f ˆ‖1 ≤ 2n/2, and
show that for any even n the upper bound can be achieved by a function
f : {−1, 1}n → {−1, 1}.

3.15 Given f :

n
2 → , dene its (fractional) sparsity to be

sparsity( f ) = |supp( f )|/2n = Pr
x∈ n
2

[ f (x) 6= 0].

Copyright © Ryan O’Donnell, 2014, 2015, 2016, 2017, 2018, 2019, 2020, 2021.



<!-- pdf-page: 87 -->
3.6. Exercises and notes

87

In this exercise you will prove the uncertainty principle: If f is nonzero,
then sparsity( f ) · sparsity( f ) ≥ 1.
(a) Show that we may assume ‖ f ‖1 = 1.
(b) Suppose F = {γ : f (γ) 6= 0}. Show that ˆ‖ f ˆ‖2
(c) Suppose G = {x : f (x) 6= 0}. Show that ‖ f ‖2

2 ≤ |F |.
2 ≥ 2n/|G |, and deduce the

uncertainty principle.

(d) Identify all cases of equality.

collection F ⊆ 2[n] with |F | ≤ ˆ‖ f ˆ‖2

3.16 Let f : {−1, 1}n → and let ≤ > 0. Show that f is ≤-concentrated on a
1/≤.
3.17 Suppose the Fourier spectrum of f : {−1, 1}n → is ≤1-concentrated on F
2 ≤ ≤2. Show that the Fourier

and that g : {−1, 1}n → satises ‖ f − g‖2
spectrum of g is 2(≤1 + ≤2)-concentrated on F .

3.18 Show that every function f :

n
2 → is computed by a decision tree with

depth at most n and size at most 2n.

3.19 Let f :

n
2 → be computable by a decision tree of size s and depth k
Show that − f and the Boolean dual f † are also computable by decision
trees of size s and depth k.

3.20 For each function in Exercise 1.1 with 4 or fewer inputs, give a decision
tree computing it. Try primarily to use the least possible depth, and
secondarily to use the least possible size.

3.21 Prove Proposition 3.16.

3.22 Let f :

n
2 → {−1, 1} be computed by a decision tree T of size s and let ≤ ∈
(0, 1]. Suppose each path in T is truncated (if necessary) so that its length
does not exceed log(s/≤); new leaves with labels −1 and 1 may be created
in an arbitrary way as necessary. Show that the resulting decisions tree
T′ computes a function that is ≤-close to f . Deduce Proposition 3.17.

3.23 A decision list is a decision tree in which every internal node has an
outgoing edge to at least one leaf. Show that any function computable by
a decision list is a linear threshold function.

3.24 A read-once decision tree is one in which every internal node queries a
distinct variable. Bearing this in mind, show that the bound k2k−1 in
Theorem 3.4 cannot be reduced below 2k − 1.

3.25 Suppose that f is computed by a read-once decision tree in which every
root-to-leaf path has length k and every internal node at the deepest level
has one child (leaf) labeled −1 and one child labeled 1. Compute the
inuence of each coordinate on f , and compute I[ f ].

3.26 The following are generalizations of decision trees:

Subcube partition: This is dened by a collection C1, . . . , Cs of sub-
. It

n
2 , along with values b1, . . . , bs ∈

cubes that form a partition of

Copyright © Ryan O’Donnell, 2014, 2015, 2016, 2017, 2018, 2019, 2020, 2021.



<!-- pdf-page: 88 -->
88

3. Spectral structure and learning

n
2 → which has value bi on all inputs in Ci.
computes the function f :
The subcube partition’s size is s and its “codimension” k (analogous to
depth) is the maximum codimension of the cubes Ci.

Parity decision tree: This is similar to a decision tree except that
the internal nodes are labeled by vectors γ ∈ n
2 . At such a node the
computation path on input x follows the edge labeled γ · x. We insist that
for each root-to-leaf path, the vectors appearing in its internal nodes are
linearly independent. Size s and depth k are dened as with normal
decision trees.

Afne subspace partition: This is similar to a subcube partition except

the subcubes Ci may be arbitrary afne subspaces.
(a) Show that subcube partition size/codimension and parity decision
tree size/depth generalize normal decision tree size/depth, and are
generalized by afne subspace partition size/codimension.

(b) Show that Proposition 3.16 holds also for the generalizations, except
that the statement about degree need not hold for parity decision
trees and afne subspace partitions.

(c) Show that the class of functions with afne subspace partition size at
most s is learnable from queries with error ≤ in time poly(n, s, 1/≤).

3.27 Dene Equ3 : {−1, 1}3 → {−1, 1} by Equ3(x) = −1 if and only if x1 = x2 = x3.

(a) Show that deg(Equ3) = 2.
(b) Show that DT(Equ3) = 3.
(c) Show that Equ3 is computable by a parity decision tree of codimen-

sion 2.

(d) For d ∈ , dene f {−1, 1}3d → {−1, 1} by f = Equ⊗d
3

(using the notation

from Denition 2.6). Show that deg( f ) = 2d but DT( f ) = 3d.

3.28 Let f : {−1, 1}n → and J ⊆ [n]. Dene f ⊆J : {−1, 1}n → by f (x) =
y∼{−1,1}J [ f (xJ, y)], where xJ ∈ {−1, 1}J is the projection of x to coordi-

E
nates J. Verify the Fourier expansion

f ⊆J =

∑

S⊆J

f (S) χS.

3.29 Let ϕ :

n

2 → ≥0 be a probability density function corresponding to prob-

ability distribution φ on n
(a) Consider the marginal probability distribution of φ on coordinates J.
2 → ≥0) in

What is its probability density function (a function
terms of ϕ?

2 . Let J ⊆ [n].

J

(b) Consider the probability distribution of φ conditioned on a substring
2 . Assuming it’s well dened, what is its probability density

z ∈ J
function in terms of ϕ?

Copyright © Ryan O’Donnell, 2014, 2015, 2016, 2017, 2018, 2019, 2020, 2021.



<!-- pdf-page: 89 -->
3.6. Exercises and notes

89

3.30 Suppose f : {−1, 1}n → is computable by a decision tree that has a leaf
(Hint: You may nd

at depth k labeled b. Show that ˆ‖ f ˆ‖∞ ≥ |b|/2k.
Exercise 3.28 helpful.)

3.31 Prove Fact 3.25 by using Theorem 1.27 and Exercise 1.1(d).

3.32 (a) Suppose f :

n

2 → has sparsity( f ) < 2n. Show that for any γ ∈
2 such that fβ⊥ has f (γ) as a Fourier

supp( f ) there exists nonzero β ∈ n
coefcient.

(b) Prove by induction on n that if f :

2 → {−1, 1} has sparsity( f ) = s > 1
then f is 21−blog sc-granular. (Hint: Distinguish the cases s = 2n and
s < 2n. In the latter case use part (a).)

n

(c) Prove that there are no functions f : {−1, 1}n → {−1, 1} with sparsity( f ) ∈

{2, 3, 5, 6, 7, 9}.

3.33 Show that one can learn any target f : {−1, 1}n → {−1, 1} with error 0 from

random examples only in time O(2n).

3.34 Improve Proposition 3.31 as follows. Suppose f : {−1, 1}n → {−1, 1} and
g : {−1, 1}n → satisfy ‖ f − g‖1 ≤ ≤. Pick θ ∈ [−1, 1] uniformly at ran-
dom and dene h : {−1, 1}n → {−1, 1} by h(x) = sgn(g(x) − θ). Show that
E[dist( f , h)] ≤ ≤/2.

3.35 (a) For n even, nd a function f : {−1, 1}n → {−1, 1} such that f is not 1/2-

concentrated on any F ⊆ 2[n] with |F | < 2n−1. (Hint: Exercise 1.1.)
(b) Let f : {−1, 1}n → {−1, 1} be a random function as in Exercise 1.7. Show
that with probability at least 1/2, f is not 1/4-concentrated on degree
up to bn/2c.

3.36 Prove Theorem 3.36. (Hint: In light of Exercise 1.11 you may round off

certain estimates with condence.)

3.37 Show that each of the following classes C (ordered by inclusion) can be
learned exactly (i.e., with error 0) using queries in time poly(n, 2k):
(a) C = { f : {−1, 1}n → {−1, 1} | f is a k-junta}. (Hint: Estimate inuences.)
(b) C = { f : {−1, 1}n → {−1, 1} | DT( f ) ≤ k}.
(c) C = { f : {−1, 1}n → {−1, 1} | sparsity( f ) ≤ 2O(k)}. (Hint: Exercise 3.32.)

3.38 Prove Theorem 3.38. (Hint: Exercise 3.16.)

3.39 Deduce Theorem 3.37 from the Goldreich–Levin Algorithm.

3.40 Suppose A learns C from random examples with error ≤/2 in time T –

with probability at least 9/10.
(a) After producing hypothesis h on target f : {−1, 1}n → {−1, 1}, show that
A can “check” whether h is a good hypothesis in time poly(n, T, 1/≤) ·
log(1/δ). Specically, except with probability at most δ, A should out-
put ‘YES’ if dist( f , h) ≤ ≤/2 and ‘NO’ if dist( f , h) > ≤. (Hint: Time poly(T)
may be required for A to evaluate h(x).)

Copyright © Ryan O’Donnell, 2014, 2015, 2016, 2017, 2018, 2019, 2020, 2021.



<!-- pdf-page: 90 -->
90

3. Spectral structure and learning

(b) Show that for any δ ∈ (0, 1/2], there is a learning algorithm that learns
C with error ≤ in time poly(n, T, ≤) · log(1/δ) – with probability at least
1 − δ.

3.41 (a) Our description of the Low-Degree Algorithm with degree k and er-
ror ≤ involved using a new batch of random examples to estimate each
low-degree Fourier coefcient. Show that one can instead simply draw
a single batch E of poly(nk, 1/≤) examples and use E to estimate each
of the low-degree coefcients.

(b) Show that when using the above form of the Low-Degree Algorithm,

the nal hypothesis h : {−1, 1}n → {−1, 1} is of the form

h(y) = sgn

w(∆(y, x)) · f (x)

,



(

∑

(x, f (x))∈E

for some function w : {0, 1, . . . , n} → . In other words, the hypothe-
sis on a given y is equal to a weighted vote over all examples seen,
where an example’s weight depends only on its Hamming distance
to y. Simplify your expression for w as much as you can.

3.42 Extend the Goldreich–Levin Algorithm so that it works also for functions
f : {−1, 1}n → [−1, 1]. (The learning model for targets f : {−1, 1}n → [−1, 1]
assumes that f (x) is always a rational number expressible by poly(n)
bits.)

3.43 (a) Assume γ, γ′ ∈ n
(b) Fix γ ∈ n

2 are distinct. Show that Prx[γ · x = γ′ · x] = 1/2.

2 and suppose x(1), . . . , x(m) ∼ n

2 are drawn uniformly and
independently. Show that if m = Cn for C a sufciently large constant
then with high probability, the only γ′ ∈ n
2 satisfying γ′ · x(i) = γ · x(i)
for all i ∈ [m] is γ′ = γ.

(c) Essentially improve on Exercise 1.27 by showing that the concept
n
2 → 2 can be learned from random
class of all linear functions
is such
examples only, with error 0, in time poly(n). (Remark: If ω ∈
that n × n matrix multiplication can be done in O(nω) time, then the
learning algorithm also requires only O(nω) time.)

3.44 Let τ ≥ 1/2 + ≤ for some constant ≤ > 0. Give an algorithm simpler than
Goldreich and Levin’s that solves the following problem with high proba-
bility: Given query access to f : {−1, 1}n → {−1, 1}, in time poly(n, 1/≤) nd
the unique U ⊆ [n] such that | f (U)| ≥ τ, assuming it exists. (Hint: Use
Proposition 1.31 and Exercise 1.27.)

3.45 Informally: a “one-way permutation” is a bijective function f :

2 → n
2
that is easy to compute on all inputs but hard to invert on more than a
negligible fraction of inputs; a “pseudorandom generator” is a function g :
2 for m > k whose output on a random input “looks unpredictable”
to any efcient algorithm. Goldreich and Levin proposed the following

2 → m

n

k

Copyright © Ryan O’Donnell, 2014, 2015, 2016, 2017, 2018, 2019, 2020, 2021.



<!-- pdf-page: 91 -->
3.6. Exercises and notes

91

construction of the latter from the former: for k = 2n, m = 2n + 1, dene

g(r, s) = (r, f (s), r · s),

where r, s ∈ n
2 . When g’s input (r, s) is uniformly random, then so is the
rst 2n bits of its output (using the fact that f is a bijection). The key to
the analysis is showing that the nal bit, r · s, is highly unpredictable to
efcient algorithms even given the rst 2n bits (r, f (s)). This is proved by
contradiction.
(a) Suppose that an adversary has a deterministic, efcient algorithm A

good at predicting the bit r · s:

Pr
r,s∼ n
2

[A(r, f (s)) = r · s] ≥

+ γ.

1
2
2 with |B|/2n ≥ 1
2 γ such that
1
2

1
2

+

γ

[A(r, f (s)) = r · s] ≥

Show there exists B ⊆ n

Pr
r∼ n
2

for all s ∈ B.

(b) Switching to ±1 notation in the output, deduce ÉA| f (s)(s) ≥ γ for all

s ∈ B.

(c) Show that the adversary can efciently compute s given f (s) (with
high probability) for any s ∈ B. If γ is nonnegligible, this contradicts
the assumption that f is “one-way”. (Hint: Use the Goldreich–Levin
Algorithm.)

(d) Deduce the same conclusion even if A is a randomized algorithm.

n
2 → {−1, 1} form a group
Notes. The fact that the Fourier characters χγ :
n
2 is not a coincidence; the analogous result holds for any nite
isomorphic to
abelian group and is a special case of the theory of Pontryagin duality in
harmonic analysis. We will see further examples of this in Chapter 8.

Regarding spectral structure, Karpovsky [Kar76] proposed sparsity( f )
as a measure of complexity for the function f . Brandman’s thesis [Bra87]
(see also [BOH90]) is an early work connecting decision tree and subcube
partition complexity to Fourier analysis. The notation introduced for restric-
tions in Section 3.3 is not standard; unfortunately there is no standard nota-
tion. The uncertainty principle from Exercise 3.15 dates back to Matolcsi and
Szücs [MS73]. The result of Exercise 3.13 is due to Green and Sanders [GS08],
with inspiration from Saeki [Sae68]. The main result of Green and Sanders
2 → {0, 1} with ˆ‖ f ˆ‖1 ≤ s can be
is the sophisticated theorem that any f :

i=1 ±1Hi

expressed as

, where L ≤ 22poly(s) and each Hi ≤ n
2 .
Theorem 3.4 is due to Nisan and Szegedy [NS94]. That work also showed
a nontrivial kind of converse to the rst statement in Proposition 3.16: Any f :
{−1, 1}n → {−1, 1} is computable by a decision tree of depth at most poly(deg( f )).

L

n

Copyright © Ryan O’Donnell, 2014, 2015, 2016, 2017, 2018, 2019, 2020, 2021.



<!-- pdf-page: 92 -->
92

3. Spectral structure and learning

The best upper bound currently known is deg( f )3 due to Midrij ¯anis [Mid04].
Nisan and Szegedy also gave the example in Exercise 3.27 showing the depen-
dence cannot be linear.

The eld of computational learning theory was introduced by Valiant
in 1984 [Val84]; for a good survey with focus on learning under the uni-
form distribution, see the thesis by Jackson [Jac95]. Linial, Mansour, and
Nisan [LMN93] pioneered the Fourier approach to learning, developing the
Low-Degree Algorithm. We present their strong results on constant-depth
circuits in Chapter 4. The noise sensitivity approach to the Low-Degree Al-
gorithm is from Klivans, O’Donnell, and Servedio [KOS04]. Corollary 3.33
is due to Bshouty and Tamon [BT96] who also gave certain matching lower
bounds. Goldreich and Levin’s work dates from 1989 [GL89]. Besides its
applications to cryptography and learning, it is important in coding theory
and complexity as a local list-decoding algorithm for the Hadamard code. The
Kushilevitz–Mansour algorithm is from their 1993 paper [KM93]; they also
are responsible for the results of Exercise 3.37(b) and 3.38. The results of
Exercise 3.32 and 3.37(c) are from Gopalan et al. [GOS+11].

Copyright © Ryan O’Donnell, 2014, 2015, 2016, 2017, 2018, 2019, 2020, 2021.



<!-- pdf-page: 93 -->
Chapter 4

DNF formulas and
small-depth circuits

In this chapter we investigate Boolean functions representable by small DNF
formulas and constant-depth circuits; these are signicant generalizations
of decision trees. Besides being natural from a computational point of view,
these representation classes are close to the limit of what complexity theorists
can “understand” (e.g., prove explicit lower bounds for). One reason for this is
that functions in these classes have strong Fourier concentration properties.

4.1. DNF formulas

One of the commonest ways of representing a Boolean function f : {0, 1}n →
{0, 1} is by a DNF formula:

Denition 4.1. A DNF (disjunctive normal form) formula over Boolean vari-
ables x1, . . . , xn is dened to be a logical OR of terms, each of which is a logi-
cal AND of literals. A literal is either a variable xi or its logical negation xi.
We insist that no term contains both a variable and its negation. The number
of literals in a term is called its width. We often identify a DNF formula with
the Boolean function f : {0, 1}n → {0, 1} it computes.

Example 4.2. Recall the function Sort3, dened by Sort3(x1, x2, x3) = 1 if and
only if x1 ≤ x2 ≤ x3 or x1 ≥ x2 ≥ x3. We can represent it by a DNF formula as
follows:

Sort3(x1, x2, x3) = (x1 ∧ x2) ∨ (x2 ∧ x3) ∨ (x1 ∧ x3) ∨ (x1 ∧ x3).

Copyright © Ryan O’Donnell, 2014, 2015, 2016, 2017, 2018, 2019, 2020, 2021.

93



<!-- pdf-page: 94 -->
94

4. DNF formulas and small-depth circuits

The DNF representation says that the bits are sorted if either the rst two
bits are 1, or the last two bits are 0, or the rst bit is 0 and the last bit is 1, or
the rst bit is 1 and the last bit is 0.

The complexity of a DNF formula is measured by its size and width:

Denition 4.3. The size of a DNF formula is its number of terms. The width
is the maximum width of its terms. Given f : {−1, 1}n → {−1, 1} we write
DNFsize( f ) (respectively, DNFwidth( f )) for the least size (respectively, width)
of a DNF formula computing f .

The DNF formula for Sort3 from Example 4.2 has size 3 and width 2.
Every function f : {0, 1}n → {0, 1} can be computed by a DNF of size at most 2n
and width at most n (Exercise 4.1).

There is also a “dual” notion to DNF formulas:

Denition 4.4. A CNF (conjunctive normal form) formulas is a logical AND
of clauses, each of which is a logical OR of literals. Size and width are dened
as for DNFs.

Some functions can be represented much more compactly by CNFs than
DNFs (see Exercise 4.14). On the other hand, if we take a CNF computing f
and switch its ANDs and ORs, the result is a DNF computing the dual func-
tion f † (see Exercises 1.8 and 4.2). Since f and f † have essentially the same
Fourier expansion, there isn’t much difference between CNFs and DNFs when
it comes to Fourier analysis. We will therefore focus mainly on DNFs.

DNFs and CNFs are more powerful than decision trees for representing

Boolean-valued functions, as the following proposition shows:

Proposition 4.5. Let f : {0, 1}n → {0, 1} be computable by a decision tree T of
size s and depth k. Then f is computable by a DNF (and also a CNF) of size
at most s and width at most k.

Proof. Take each path in T from the root to a leaf labeled 1 and form the
logical AND of the literals describing the path. These are the terms of the
required DNF. (For the CNF clauses, take paths to label 0 and negate all

literals describing the path.)

Example 4.6. If we perform this conversion on the decision tree computing
Sort3 in Figure 3.1 we get the DNF

(x1 ∧ x3 ∧ x2) ∨ (x1 ∧ x3) ∨ (x1 ∧ x2 ∧ x3) ∨ (x2 ∧ x3).

This has size 4 (indeed at most the decision tree size 6) and width 3 (indeed
at most the decision tree depth 3). It is not as simple as the equivalent DNF
from Example 4.2, though; DNF representation is not unique.

Copyright © Ryan O’Donnell, 2014, 2015, 2016, 2017, 2018, 2019, 2020, 2021.



<!-- pdf-page: 95 -->
4.1. DNF formulas

95

The class of functions computable by small DNFs is intensively studied
in learning theory. This is one reason why the problem of analyzing spectral
concentration for DNFs is important. Let’s begin with the simplest method
for this: understanding low-degree concentration via total inuence. We will
switch to ±1 notation.

Proposition 4.7. Suppose that f : {−1, 1}n → {−1, 1} has DNFwidth( f ) ≤ w.
Then I[ f ] ≤ 2w.

Proof. We use Exercise 2.10, which states that

I[ f ] = 2 E

x∼{−1,1}n

[# (−1)-pivotal coordinates for f on x],

where coordinate i is “(−1)-pivotal” on input x if f (x) = −1 (logical True) but
f (x⊕i) = 1 (logical False). It thus sufces to show that on every input x there
are at most w coordinates which are (−1)-pivotal. To have any (−1)-pivotal
coordinates at all on x we must have f (x) = −1 (True); this means that at least
one term T in f ’s width-w DNF representation must be made True by x. But
now if i is a (−1)-pivotal coordinate then either xi or xi must appear in T;
otherwise, T would still be made true by x⊕i. Thus the number of (−1)-pivotal
coordinates on x is at most the number of literals in T, which is at most w. 

Since I[ f †] = I[ f ] the proposition is also true for CNFs of width at most w.
The proposition is very close to being tight: The parity function χ[w] : {−1, 1}n →
{−1, 1} has I[χ[w]] = w and DNFwidth(χ[w]) ≤ w (the latter being true for all w-
juntas). In fact, the proposition can be improved to give the tight upper
bound w (Exercise 4.17).

Using Proposition 3.2 we deduce:

Corollary 4.8. Let f : {−1, 1}n → {−1, 1} have DNFwidth( f ) ≤ w. Then for ≤ > 0,
the Fourier spectrum of f is ≤-concentrated on degree up to 2w/≤.

The dependence here on w is of the correct order (by the example of the
parity χ[w] again), but the dependence on ≤ can be signicantly improved as
we will see in Section 4.4.

There’s usually more interest in DNF size than in DNF width; for example,
learning theorists are often interested in the class of n-variable DNFs of size
poly(n). The following fact (similar to Exercise 3.22) helps relate the two,
suggesting O(log n) as an analogous width bound:

Proposition 4.9. Let f : {−1, 1}n → {−1, 1} be computable by a DNF (or CNF)
of size s and let ≤ ∈ (0, 1]. Then f is ≤-close to a function g computable by a
DNF of width log(s/≤).

Proof. Take the DNF computing f and delete all terms with more than log(s/≤)
literals; let g be the function computed by the resulting DNF. For any deleted

Copyright © Ryan O’Donnell, 2014, 2015, 2016, 2017, 2018, 2019, 2020, 2021.



<!-- pdf-page: 96 -->
96

4. DNF formulas and small-depth circuits

term T, the probability a random input x ∼ {−1, 1}n makes T true is at most
2− log(s/≤) = ≤/s. Taking a union bound over the (at most s) such terms shows

that Pr[g(x) 6= f (x)] ≤ ≤. (A similar proof works for CNFs.)

By combining Proposition 4.9 and Corollary 4.8 we can deduce (using Exer-
cise 3.17) that DNFs of size s have Fourier spectra ≤-concentrated up to degree
O(log(s/≤)/≤). Again, the dependence on ≤ will be improved in Section 4.4. We
will also later show in Section 4.3 that size-s DNFs have total inuence at
most O(log s), something we cannot deduce immediately from Proposition 4.7.

In light of the Kushilevitz–Mansour learning algorithm it would also be
nice to show that poly(n)-size DNFs have their Fourier spectra concentrated
on small collections (not necessarily low-degree). In Section 4.4 we will show
they are ≤-concentrated on collections of size nO(log log n) for any constant ≤ > 0.
It has been conjectured that this can be improved to poly(n):

Mansour’s Conjecture. Let f : {−1, 1}n → {−1, 1} be computable by a DNF
of size s > 1 and let ≤ ∈ (0, 1/2]. Strong conjecture: f ’s Fourier spectrum is ≤-
concentrated on a collection F with |F | ≤ sO(log(1/≤)). Weaker conjecture: if s ≤
poly(n) and ≤ > 0 is any xed constant, then we have the bound |F | ≤ poly(n).

4.2. Tribes

In this section we study the tribes DNF formulas, which serve as an important
examples and counterexamples in analysis of Boolean functions. Perhaps the
most notable feature of the tribes function is that (for a suitable choice of
parameters) it is essentially unbiased and yet all of its inuences are quite
tiny.

Recall from Chapter 2.1 that the function Tribesw,s : {−1, 1}sw → {−1, 1} is

dened by its width-w, size-s DNF representation:

Tribesw,s(x1, . . . , xw, . . . , x(s−1)w+1, . . . , xsw)

= (x1 ∧ · · · ∧ xw) ∨ · · · ∨ (x(s−1)w+1 ∧ · · · ∧ xsw).

(We are using the notation where −1 represents logical True and 1 represents
logical False.) As is computed in Exercise 2.13 we have:

Fact 4.10. Prx[Tribesw,s(x) = −1] = 1 − (1 − 2−w)s.

The most interesting setting of parameters makes this probability as close

to 1/2 as possible (a slightly different choice than the one in Exercise 2.13):

+, let s = sw be the largest integer such that
Denition 4.11. For w ∈
1 − (1 − 2−w)s ≤ 1/2. Then for n = nw = sw we dene Tribesn : {−1, 1}n → {−1, 1}
to be Tribesw,s. Note this is only dened only for certain n: 1, 4, 15, 40, . . .

Copyright © Ryan O’Donnell, 2014, 2015, 2016, 2017, 2018, 2019, 2020, 2021.



<!-- pdf-page: 97 -->
4.2. Tribes

97

Here s ≈ ln(2)2w, hence n ≈ ln(2)w2w and therefore w ≈ log n − log ln n and

s ≈ n/ log n. A slightly more careful accounting (Exercise 4.5) yields:

Proposition 4.12. For the Tribesn function as in Denition 4.11:

• s = ln(2)2w − Θw(1);
• n = ln(2)w2w − Θ(w), thus nw+1 = (2 + o(1))nw;
• w = log n − log ln n + on(1), and 2w = n

ln n (1 + on(1));

• Pr[Tribesn(x) = −1] = 1/2 − O





.

log n
n

Thus with this setting of parameters Tribesn is essentially unbiased. Re-

garding its inuences:

Proposition 4.13. Infi[Tribesn] = ln n
I[Tribesn] = (ln n)(1 ± o(1)).

n (1 ± o(1)) for each i ∈ [n] and hence

Proof. Thinking of Tribesn = Tribesw,s as a voting rule, voter i is pivotal if
and only if: (a) all other voters in i’s “tribe” vote −1 (True); (b) all other tribes
produce the outcome 1 (False). The probability of this is indeed

2−(w−1) · (1 − 2−w)s−1 = 2

2w−1 · Pr[Tribesn = 1] = ln n

n (1 ± o(1)),

where we used Fact 4.10 and then Proposition 4.12.



Thus if we are interested in (essentially) unbiased voting rules in which
every voter has small inuence, Tribesn is a much stronger example than
Majn where each voter has inuence Θ(1/
n). You may wonder if the max-

imum inuence can be even smaller than Θ
for unbiased voting rules.
Certainly it can’t be smaller than 1
n , since the Poincaré Inequality says that
I[ f ] ≥ 1 for unbiased f . In fact the famous KKL Theorem shows that the
Tribesn example is tight up to constants:

ln n
n

p



Kahn–Kalai–Linial (KKL) Theorem. For any f : {−1, 1}n → {−1, 1},

MaxInf[ f ] = max
i∈[n]

{Infi[ f ]} ≥ Var[ f ] · Ω

 log n
n



.

We prove the KKL Theorem in Chapter 9.

We conclude this section by recording a formula for the Fourier coefcients

of Tribesw,s. The proof is Exercise 4.6.

Proposition 4.14. Suppose we index the Fourier coefcients of the function
Tribesw,s{−1, 1}sw → {−1, 1} by sets T = (T1, . . . , Ts) ⊆ [sw], where Ti is the in-
tersection of T with the ith “tribe”. Then


·Tribesw,s(T) =

2(1 − 2−w)s − 1
2(−1)k+|T|2−kw(1 − 2−w)s−k

if T = ;,

if k = #{i : Ti 6= ;} > 0.

Copyright © Ryan O’Donnell, 2014, 2015, 2016, 2017, 2018, 2019, 2020, 2021.



<!-- pdf-page: 98 -->
98

4. DNF formulas and small-depth circuits

4.3. Random restrictions

In this section we describe the method of applying random restrictions. This is
a very “Fourier-friendly” way of simplifying a Boolean function. As motivation,
let’s consider the problem of bounding total inuence for size-s DNFs. One
plan is to use the results from Section 4.1: size-s DNFs are .01-close to width-
O(log s) DNFs, which in turn have total inuence O(log s). This suggests that
size-s DNFs themselves have total inuence O(log s). To prove this though
we’ll need to reverse the steps of the plan; instead of truncating DNFs to a
xed width and arguing that a random input is unlikely to notice, we’ll rst
pick a random (partial) input and argue that this is likely to make the width
small.

Let’s formalize the notion of a random partial input, or restriction:

Denition 4.15. For δ ∈ [0, 1], we say that J is a δ-random subset of N if it
is formed by including each element of N independently with probability δ.
We dene a δ-random restriction on {−1, 1}n to be a pair (J | z), where rst
J is chosen to be a δ-random subset of [n] and then z ∼ {−1, 1}J is chosen
uniformly at random. We say that coordinate i ∈ [n] is free if i ∈ J and is xed
if i ∉ J. An equivalent denition is that each coordinate i is (independently)
free with probability δ and xed to ±1 with probability (1 − δ)/2 each.

Given f : {−1, 1}n → and a random restriction (J | z), we can form the re-
stricted function f J|z : {−1, 1}J → as usual. However, it’s inconvenient that
the domain of this function depends on the random restriction. Thus when
dealing with random restriction we usually invoke the following convention:

Denition 4.16. Given f : {−1, 1}n → , I ⊆ [n], and z ∈ {−1, 1}I , we may iden-
tify the restricted function f I|z : {−1, 1}I → with its extension f I|z : {−1, 1}n →

in which the input coordinates {−1, 1}I are ignored.

As mentioned, random restrictions interact nicely with Fourier expan-

sions:

Proposition 4.17. Fix f : {−1, 1}n → and S ⊆ [n]. Then if (J | z) is a δ-
random restriction on {−1, 1}n,

E[ ̂f J|z(S)] = Pr[S ⊆ J] · f (S) = δ|S| f (S),

and

E[ ̂f J|z(S)2] =

∑

U⊆[n]

Pr[U ∩ J = S] · f (U)2 =

∑

U⊇S

δ|S|(1 − δ)|U\S| f (U)2,

where we are treating f J|z as a function {−1, 1}n → .

Copyright © Ryan O’Donnell, 2014, 2015, 2016, 2017, 2018, 2019, 2020, 2021.



<!-- pdf-page: 99 -->
4.3. Random restrictions

99

Proof. Suppose rst that J ⊆ [n] is xed. When we think of restricted func-
tions f J|z as having domain {−1, 1}n, Corollary 3.22 may be stated as saying
that for any S ⊆ [n],

E
z∼{−1,1}J

[ ̂f J|z(S)] = f (S) · 1S⊆J,

E
z∼{−1,1}J

[ ̂f J|z(S)2] =

∑

U⊆[n]

f (U)2 · 1U∩J=S.

The proposition now follows by taking the expectation over J.



Corollary 4.18. Fix f : {−1, 1}n → and i ∈ [n]. If (J | z) is a δ-random
restriction, then E[Infi[ f J|z]] = δInfi[ f ]. Hence also E[I[ f J|z]] = δI[ f ].

Proof. We have

E[Infi[ f J|z]] = E



∑

S3i

̂f J|z(S)2
∑

=



=

∑

∑

S3i

U⊆[n]

Pr[U ∩ J = S] f (U)2

Pr[U ∩ J 3 i] f (U)2 =

U⊆[n]

∑

U3i

δ f (U)2 = δInfi[ f ],

where the second equality used Proposition 4.17.



(Proving Corollary 4.18 via Proposition 4.17 is a bit more elaborate than
necessary; see Exercise 4.9.)

Corollary 4.18 lets us bound the total inuence of a function f by bounding
the (expected) total inuence of a random restriction of f . This is useful if f
is computable by a DNF formula of small size, since a random restriction is
very likely to make this DNF have small width. This is a consequence of the
following lemma:

Lemma 4.19. Let T be a DNF term over {−1, 1}n and x w ∈ +. Let (J | z) be
a (1/2)-random restriction on {−1, 1}n. Then Pr[width(TJ|z) ≥ w] ≤ (3/4)w.

Proof. We may assume the initial width of T is at least w, as otherwise its
restriction under (J | z) cannot have width at least w. Now if any literal
appearing in T is xed to False by the random restriction, the restricted term
TJ|z will be constantly False and thus have width 0 < w. Each literal is xed
to False with probability 1/4; hence the probability no literal in T is xed to
False is at most (3/4)w.


We can now bound the total inuence of small DNF formulas.

Theorem 4.20. Let f : {−1, 1}n → {−1, 1} be computable by a DNF of size s.
Then I[ f ] ≤ O(log s).

Copyright © Ryan O’Donnell, 2014, 2015, 2016, 2017, 2018, 2019, 2020, 2021.



<!-- pdf-page: 100 -->
100

4. DNF formulas and small-depth circuits

Proof. Let (J | z) be a (1/2)-random restriction on {−1, 1}n and write w =
DNFwidth( f J|z). By a union bound and Lemma 4.19 we have that Pr[w ≥ w] ≤
s(3/4)w. Hence

E[w] =

∞∑

w=1

Pr[w ≥ w] ≤ 3 log s +

∑

s(3/4)w

w>3 log s

≤ 3 log s + 4s(3/4)3 log s ≤ 3 log s + 4/s0.2 = O(log s).

From Proposition 4.7 we obtain E[I[ f J|z]] ≤ 2 · O(log s) = O(log s). And so from

Corollary 4.18 we conclude I[ f ] = 2 E[I[ f J|z]] ≤ O(log s).

4.4. Håstad’s Switching Lemma and the spectrum of DNFs

Let’s further investigate how random restrictions can simplify DNF formulas.
Suppose f is computable by a DNF formula of width w, and we apply to it a
δ-random restriction with δ ø 1/w. For each term T in the DNF, one of three
things may happen to it under the random restriction. First and by far most
likely, one of its literals may be xed to False, allowing us to delete it. If this
doesn’t happen, the second possibility is that all of T’s literals are made True,
in which case the whole DNF reduces to the constantly True function. With
δ ø 1/w, this is in turn much more likely than the third possibility, which is
that at least one of T’s literals is left free, but all the xed literals are made
True. Only in this third case is T not trivialized by the random restriction.

This reasoning might suggest that f is likely to become a constant func-
tion under the random restriction. Indeed, this is true, as the following theo-
rem shows:

Baby Switching Lemma. Let f : {−1, 1}n → {−1, 1} be computable by a DNF
or CNF of width at most w and let (J | z) be a δ-random restriction. Then

Pr[ f J|z is not a constant function] ≤ 5δw.

This is in fact the k = 1 case of the following much more powerful theorem:

Håstad’s Switching Lemma. Let f : {−1, 1}n → {−1, 1} be computable by a
DNF or CNF of width at most w and let (J | z) be a δ-random restriction. Then
for any k ∈ ,

Pr[DT( f J|z) ≥ k] ≤ (5δw)k.

What is remarkable about this result is that it has no dependence on the
size of the DNF, or on n. In words, Håstad’s Switching Lemma says that when
δ ø 1/w, it’s exponentially unlikely (in k) that applying a δ-random restriction
to a width-w DNF does not convert (“switch”) it to a decision tree of depth
less than k. The result is called a “lemma” for historical reasons; in fact, its
proof requires some work. You are asked to prove the Baby Switching Lemma

Copyright © Ryan O’Donnell, 2014, 2015, 2016, 2017, 2018, 2019, 2020, 2021.



<!-- pdf-page: 101 -->
4.4. Håstad’s Switching Lemma and the spectrum of DNFs

101

in Exercise 4.19; for Håstad’s Switching Lemma, consult Håstad’s original
proof [Hås87] or the alternate proof of Razborov [Raz93, Bea94].

Since we have strong results about the Fourier spectra of decision trees
(Proposition 3.16), and since we know random restrictions interact nicely with
Fourier coefcients (Proposition 4.17), Håstad’s Switching Lemma allows us
to prove some strong results about Fourier concentration of narrow DNF
formulas. We start with an intermediate result which will be of use:

Lemma 4.21. Let f : {−1, 1}n → {−1, 1} and let (J | z) be a δ-random restriction,
δ > 0. Fix k ∈ + and write ≤ = Pr[DT( f J|z) ≥ k]. Then the Fourier spectrum of
f is 3≤-concentrated on degree up to 3k/δ.

Proof. The key observation is that DT( f J|z) < k implies deg( f J|z) < k (Propo-
sition 3.16), in which case the Fourier weight of f J|z at degree k and above
is 0. Since this weight at most 1 in all cases we conclude



̂f J|z(S)2

≤ ≤.

E
(J|z)

 ∑

S⊆[n]
|S|≥k

Using Proposition 4.17 we have

 ∑



̂f J|z(S)2

E
(J|z)

S⊆[n]
|S|≥k

∑

=

S⊆[n]
|S|≥k

[ ̂f J|z(S)2] =

E
(J|z)

∑

U⊆[n]

Pr
(J|z)

[|U ∩ J| ≥ k] · f (U)2.

The distribution of random variable |U ∩ J| is Binomial(|U|, δ). When |U| ≥
3k/δ this random variable has mean at least 3k, and a Chernoff bound shows
Pr[|U ∩ J| < k] ≤ exp(− 2

3 k) ≤ 2/3. Thus
[|U ∩ J| ≥ k] · f (U)2 ≥

∑

|U|≥3k/δ

(1 − 2/3) · f (U)2

∑

U⊆[n]

Pr
(J|z)

≤ ≥



and hence

|U|≥3k/δ

f (U)2 ≤ 3≤ as claimed.



We can now improve the dependence on ≤ in Corollary 4.8’s low-degree

spectral concentration for DNFs:

Theorem 4.22. Suppose f : {−1, 1}n → {−1, 1} is computable by a DNF of
width w. Then f ’s Fourier spectrum is ≤-concentrated on degree up to O(w log(1/≤)).

Proof. This follows immediately from Håstad’s Switching Lemma together
with Lemma 4.21, taking δ = 1
10w and k = C log(1/≤) for a sufciently large

constant C.

In Lemma 4.21, instead of using the fact that depth-k decision trees have
no Fourier weight above degree k, we could have used the fact that their
Fourier 1-norm is at most 2k. As you are asked to show in Exercise 4.11, this
would yield:

Copyright © Ryan O’Donnell, 2014, 2015, 2016, 2017, 2018, 2019, 2020, 2021.



<!-- pdf-page: 102 -->
102

4. DNF formulas and small-depth circuits

Lemma 4.23. Let f : {−1, 1}n → {−1, 1} and let (J | z) be a δ-random restriction.
Then

∑

U⊆[n]

δ|U| · | f (U)| ≤ E
(J|z)

[2DT( f J|z)].

We can combine this with the Switching Lemma to deduce that width-w

DNFs have small Fourier 1-norm at low degree:

Theorem 4.24. Suppose f : {−1, 1}n → {−1, 1} is computable by a DNF of
width w. Then for any k,

∑

|U|≤k

| f (U)| ≤ 2 · (20w)k.

Proof. Apply Håstad’s Switching Lemma to f with δ = 1

20w to deduce

[2DT( f J|z)] ≤

E
(J|z)

∞∑



d=0

d · 2d = 2.

5
20

Thus from Lemma 4.23 we get

2 ≥

∑



U⊆[n]

|U| · | f (U)| ≥



k ·

1
20w

1
20w

∑

|U|≤k

| f (U)|,

as needed.



Our two theorems about the Fourier structure of DNF are almost enough

to prove Mansour’s Conjecture:

Theorem 4.25. Let f : {−1, 1}n → {−1, 1} be computable by a DNF of width w ≥
2. Then for any ≤ ∈ (0, 1/2], the Fourier spectrum of f is ≤-concentrated on a
collection F with |F | ≤ wO(w log(1/≤)).

Proof. Let k = Cw log(4/≤) and let g = f ≤k. If C is a large enough constant,
then Theorem 4.22 tells us that ‖ f − g‖2
2 ≤ ≤/4. Furthermore, Theorem 4.24
gives ˆ‖g ˆ‖1 ≤ wO(w log(1/≤)). By Exercise 3.16, g is (≤/4)-concentrated on some
collection F with |F | ≤ 4ˆ‖g ˆ‖2
1/≤ ≤ wO(w log(1/≤)). And so by Exercise 3.17, f is

≤-concentrated on this same collection.

For the interesting case of DNFs of width O(log n) and constant ≤, we get
concentration on a collection of cardinality O(log n)O(log n) = nO(log log n), nearly
polynomial. Using Proposition 4.9 (and Exercise 3.17) we get the same deduc-
tion for DNFs of size poly(n); more generally, for size s we have ≤-concentration
on a collection of cardinality at most (s/≤)O(log log(s/≤) log(1/≤)).

Copyright © Ryan O’Donnell, 2014, 2015, 2016, 2017, 2018, 2019, 2020, 2021.



<!-- pdf-page: 103 -->
4.5. Highlight: LMN’s work on constant-depth circuits

103

4.5. Highlight: LMN’s work on constant-depth circuits

Having derived strong results about the Fourier spectrum of small DNFs and
CNFs, we will now extend to the case of constant-depth circuits. We begin
by describing how Håstad applied his Switching Lemma to constant-depth
circuits. We then describe some Fourier-theoretic consequences coming from
a very early (1989) work in analysis of Boolean functions by Linial, Mansour,
and Nisan (LMN).

To dene constant-depth circuits it is best to start with a picture. Here is

an example of a depth-3 circuit:

Figure 4.1. Example of a depth-3 circuit, with the layer 0 nodes at the
bottom and the layer 3 node at the top

This circuit computes the function

x1x2 ∧ (x1x3 ∨ x3x4) ∧ (x3x4 ∨ x2),

where we suppressed the ∧ in concatenated literals. To be precise:

Denition 4.26. For an integer d ≥ 2, we dene a depth-d circuit over
Boolean variables x1, . . . , xn as follows: It is a directed acyclic graph in which
the nodes (“gates”) are arranged in d + 1 layers, with all arcs (“wires”) going
from layer j − 1 to layer j for some j ∈ [d]. There are exactly 2n nodes in
layer 0 (the “inputs”) and exactly 1 node in layer d (the “output”). The nodes
in layer 0 are labeled by the 2n literals. The nodes in layers 1, 3, 5, etc. have
the same label, either ∧ or ∨, and the nodes in layers 2, 4, 6, etc. have the
other label. Each node “computes” a function {−1, 1}n → {−1, 1}: the literals
compute themselves and the ∧ (respectively, ∨) nodes compute the logical
AND (respectively, OR) of the functions computed by their incoming nodes.
The circuit itself is said to compute the function computed by its output node.

In particular, DNFs and CNFs are depth-2 circuits. We extend the deni-

tions of size and width appropriately:

Copyright © Ryan O’Donnell, 2014, 2015, 2016, 2017, 2018, 2019, 2020, 2021.



<!-- pdf-page: 104 -->
104

4. DNF formulas and small-depth circuits

Denition 4.27. The size of a depth-d circuit is dened to be the number of
nodes in layers 1 through d − 1. Its width is the maximum in-degree of any
node at layer 1. (As with DNFs and CNFs, we insist that no node at layer 1 is
connected to a variable or its negation more than once.)

The layering we assume in our denition of depth-d circuits can be achieved
with a factor-2d size overhead for any “unbounded fan-in AND/OR/NOT cir-
cuit”. We will not discuss any other type of Boolean circuit in this section.

We now show that Håstad’s Switching Lemma can be usefully applied not

just to DNFs and CNFs but more generally to constant-depth circuits:

Lemma 4.28. Let f : {−1, 1}n → {−1, 1} be computable by a depth-d circuit of
size s and width w, and let ≤ ∈ (0, 1]. Set

)d−2

1
10w



1
10`

δ =

, where ` = log(2s/≤).

Then if (J | z) is a δ-random restriction, Pr[DT( f J|z) ≥ log(2/≤)] ≤ ≤.

Proof. The d = 2 case is immediate from Håstad’s Switching Lemma, so we
assume d ≥ 3.

The rst important observation is that random restrictions “compose”.
That is, making a δ1-random restriction followed by a δ2-random restriction
to the free coordinates is equivalent to making a δ1δ2-random restriction.
Thus we can think of (J | z) as being produced as follows:

10w -random restriction;

(1) make a 1
(2) make d − 3 subsequent 1
10`
(3) make a nal 1
10`

-random restriction.

-random restrictions;

Without loss of generality, assume the nodes at layer 2 of the circuit are
labeled ∨. Thus any node g at layer 2 computes a DNF of width at most w.
1
10w -random restriction g can
By Håstad’s Switching Lemma, after the initial
be replaced by a decision tree of depth at most ` except with probability at
most 2−`. In particular, it can be replaced by a CNF of width at most `, using
Proposition 4.5. If we write s2 for the number of nodes at layer 2, a union
bound lets us conclude:

Pr
1
-random
10w
restriction

[not all nodes at layer 2 replaceable by width-` CNFs] ≤ s2 · 2−`.

(4.1)

We now come to the second important observation: If all nodes at layer 2
can be switched to width-` CNFs, then layers 2 and 3 can be “compressed”,
producing a depth-(d − 1) circuit of width at most `. More precisely, we can
form an equivalent circuit by shortening all length-2 paths from layer 1 to

Copyright © Ryan O’Donnell, 2014, 2015, 2016, 2017, 2018, 2019, 2020, 2021.



<!-- pdf-page: 105 -->
4.5. Highlight: LMN’s work on constant-depth circuits

105

layer 3 into single arcs, and then deleting the nodes at layer 2. We give an
illustration of this in Figure 4.2:

Figure 4.2. At top is the initial circuit. Under the restriction xing x3 =
True, all three DNFs at layer 2 may be replaced by CNFs of width at most 2.
Finally, the nodes at layers 2 and 3 may be compressed.

Assuming the event in (4.1) does not occur, the initial

1
10w -random restric-
tion reduces the circuit to having depth-(d − 1) and width at most `. The
number of ∧-nodes at the new layer 2 is at most s3, the number of nodes at
layer 3 in the original circuit.

Next we make a 1
10`

-random restriction. As before, by Håstad’s Switching
Lemma this reduces all width-` CNFs at the new layer 2 to depth-` decision
trees (hence width-` DNFs), except with probability at most s3 · 2−`. We may
then compress layers and reduce depth again.

Proceeding for all

bound gives

1
10`

-random restrictions except the nal one, a union

Pr

[circuit does not reduce to depth 2 and width `]

1

10w ( 1

10` )d−3-random
restriction

≤ s2 · 2−` + s3 · 2−` + · · · + sd−1 · 2−` ≤ s · 2−` = ≤/2.

Copyright © Ryan O’Donnell, 2014, 2015, 2016, 2017, 2018, 2019, 2020, 2021.



<!-- pdf-page: 106 -->
106

4. DNF formulas and small-depth circuits

Assuming the event above does not occur, Håstad’s Switching Lemma tells us
that the nal 1
-random restriction reduces the circuit to a decision tree of
10`
depth less than log(2/≤) except with probability at most ≤/2. This completes

the proof.

We may now obtain the main theorem of Linial, Mansour, and Nisan:

LMN Theorem. Let f : {−1, 1}n → {−1, 1} be computable by a depth-d circuit
of size s > 1 and let ≤ ∈ (0, 1/2]. Then f ’s Fourier spectrum is ≤-concentrated up
to degree O(log(s/≤))d−1 · log(1/≤).

Proof. If the circuit for f also had width at most w, we would be able to
deduce 3≤-concentration up to degree 30w·(10 log(2s/≤))d−2 ·log(2/≤) by combin-
ing Lemma 4.28 with Lemma 4.21. But if we simply delete all layer-1 nodes
of width at least log(s/≤), the resulting circuit computes a function which is
≤-close to f , as in the proof of Proposition 4.9. Thus (using Exercise 3.17) f ’s
spectrum is O(≤)-concentrated up to degree O(log(2s/≤))d−1 · log(2/≤), and the

result follows by adjusting constants.

Remark 4.29. Håstad [Hås01a] has slightly sharpened the degree in the
LMN Theorem to O(log(s/≤))d−2 · log(s) · log(1/≤).

In Exercise 4.20 you are asked to use a simpler version of this proof, along

the lines of Theorem 4.20, to show the following:

Theorem 4.30. Let f : {−1, 1}n → {−1, 1} be computable by a depth-d circuit of
size s. Then I[ f ] ≤ O(log s)d−1.

These rather strong Fourier concentration results for constant-depth cir-
cuits have several applications. By introducing the Low-Degree Algorithm for
learning, Linial–Mansour–Nisan gave as their main application:

Theorem 4.31. Let C be the class of functions f : {−1, 1}n → {−1, 1} computable
depth-d poly(n)-size circuits. Then C can be learned from random examples
with error any ≤ = 1/poly(n) in time nO(log n)d .

In complexity theory the class of poly-size, constant-depth circuits is re-
ferred to as AC0. Thus the above theorem may be summarized as “AC0 is
learnable in quasipolynomial time”. In fact, under a strong enough assump-
tion about the intractability of factoring certain integers, it is known that
quasipolynomial time is required to learn AC0 circuits, even with query ac-
cess [Kha93].

The original motivation of the line of work leading to Håstad’s Switching
Lemma was to show that the parity function χ[n] cannot be computed in AC0.
Håstad even showed that AC0 cannot even approximately compute parity. We
can derive this result from the LMN Theorem:

Copyright © Ryan O’Donnell, 2014, 2015, 2016, 2017, 2018, 2019, 2020, 2021.



<!-- pdf-page: 107 -->
4.6. Exercises and notes

107

Corollary 4.32. Fix any constant ≤0 > 0. Suppose C is a depth-d circuit
over {−1, 1}n with Prx[C(x) = χ[n](x)] ≥ 1/2 + ≤0. Then the size of C is at least
2Ω(n1/(d−1)).

Proof. The hypothesis on C implies C([n]) ≥ 2≤0. The result then follows by
taking ≤ = 2≤2


0 in the LMN Theorem.

This corollary is close to being tight, since the parity χ[n] can be com-
puted by a depth-d circuit of size n2n1/(d−1) for any d ≥ 2; see Exercise 4.12.
The simpler result Theorem 4.30 is often handier for showing that certain
functions can’t be computed by AC0 circuits. For example, we know that
I[Majn] = Θ(
n); hence any constant-depth circuit computing Majn must have
size at least 2nΩ(1).

p

Finally, Linial, Mansour, and Nisan gave an application to cryptography.
Informally, a function f : {−1, 1}m ×{−1, 1}n → {−1, 1} is said to be a “pseudoran-
dom function generator with seed length m” if, for any efcient algorithm A,

∣
∣
∣
∣ Pr
s∼{−1,1}m

[A( f (s, ·)) = “accept”] −

Pr
g∼{−1,1}{−1,1}n

[A(g) = “accept”]

∣
∣
∣
∣ ≤ 1/nω(1).

Here the notation A(h) means that A has query access to target function h,
and g ∼ {−1, 1}{−1,1}n means that g is a uniformly random n-bit function. In
other words, for almost all “seeds” s the function f (s, ·) : {−1, 1}n → {−1, 1} is
nearly indistinguishable (to efcient algorithms) from a truly random func-
tion. Theorem 4.30 shows that pseudorandom function generators cannot be
computed by AC0 circuits. To see this, consider the algorithm A(h) which
chooses x ∼ {−1, 1}n and i ∈ [n] uniformly at random, queries h(x) and h(x⊕i),
and accepts if these values are unequal. If h is a uniformly random function,
A(h) will accept with probability 1/2. In general, A(h) accepts with probability
I[h]/n. Thus Theorem 4.30 implies that if h is computable in AC0 then A(h)
accepts with probability at most polylog(n)/n ø 1/2.

4.6. Exercises and notes

4.1 Show that every function f : {0, 1}n → {0, 1} can be represented by a DNF

formula of size at most 2n and width at most n.

4.2 Suppose we have a certain CNF computing f : {0, 1}n → {0, 1}. Switch
ANDs with ORs in the CNF. Show that the result is a DNF computing the
Boolean dual f † : {0, 1}n → {0, 1}.

4.3 A DNF formula is said to be monotone if its terms contain only unnegated
variables. Show that monotone DNFs compute monotone functions and
that any monotone function can be computed by a monotone DNF, but
that a nonmonotone DNF may compute a monotone function.

4.4 Let f : {−1, 1}n → {−1, 1} be computable by a DNF of size s.

Copyright © Ryan O’Donnell, 2014, 2015, 2016, 2017, 2018, 2019, 2020, 2021.



<!-- pdf-page: 108 -->
108

4. DNF formulas and small-depth circuits

(a) Show there exists S ⊆ [n] with |S| ≤ log(s) + O(1) and | f (S)| ≥ Ω(1/s).

(Hint: Use Proposition 4.9 and Exercise 3.30.)

(b) Let C be the concept class of functions : {−1, 1}n → {−1, 1} computable
by DNF formulas of size at most s. Show that C is learnable using
queries with error 1
2 − Ω(1/s) in time poly(n, s). (Such a result, with
error bounded away from 1

2 , is called weak learning.)

4.5 Verify Proposition 4.12.

4.6 Verify Proposition 4.14.

4.7 For each n that is an input length for Tribesn, show that there exists a
function f : {−1, 1}n → {−1, 1} that is truly unbiased (E[ f ] = 0) and has
Infi[ f ] ≤ O

for all i ∈ [n].



 log n
n

4.8 Suppose f : {−1, 1}n → {−1, 1} is computed by a read-once DNF (mean-
ing no variable is involved in more than one term) in which all terms
ˆ‖1 =
have width exactly w. Compute ˆ‖ f ˆ‖1 exactly. Deduce that ˆ‖Tribesn
(1±o(1)) and that there are n-variable width-2 DNFs with Fourier 1-
2
norm Ω(

3/2

n
log n

p

).

n

4.9 Give a direct (Fourier-free) proof of Corollary 4.18. (Hint: Condition on

whether i ∈ J.)

4.10 Tighten the constant factor on log s in Theorem 4.20 as much as you can
(avenues of improvement include the argument in Lemma 4.19, the choice
of δ, and Exercise 4.17).

4.11 Prove Lemma 4.23.
4.12 (a) Show that the parity function χ[n] : {−1, 1}n → {−1, 1} can be computed

by a DNF (or a CNF) of size 2n−1.

(b) Show that the bound 2n−1 above is exactly tight. (Hint: Show that

every term must have width exactly n.)

(c) Show that there is a depth-3 circuit of size O(n1/2)·2n1/2 computing χ[n].
(Hint: Break up the input into n1/2 blocks of size n1/2 and use (a) twice.
How can you compress the result from depth 4 to depth 3?)

(d) More generally, show there is a depth-d circuit of size O(n1−1/(d−1)) ·

2n1/(d−1) computing χ[n].

4.13 In this exercise we dene the most standard class of Boolean circuits. A
(De Morgan) circuit C over Boolean variables x1, . . . , xn is a directed acyclic
graph in which each node (“gate”) is labeled with either an xi or with ∧,
∨, or ¬ (logical NOT). Each xi is used as label exactly once; the associated
nodes are called “input” gates and must have in-degree 0. Each ∧ and ∨
node must have in-degree 2, and each ¬ node must have in-degree 1. Each
node “computes” a Boolean function of the inputs as in Denition 4.26.
Finally, one node of C is designated as the “output” gate, and C itself is

Copyright © Ryan O’Donnell, 2014, 2015, 2016, 2017, 2018, 2019, 2020, 2021.



<!-- pdf-page: 109 -->
4.6. Exercises and notes

109

said to compute the function computed by the output node. For this type
of circuit we dene its size, denoted size(C), to be the number of nodes.

Show that each of the following n-input functions can be computed by

De Morgan circuits of size O(n):
(a) The logical AND function.
(b) The parity function.
(c) The complete quadratic function from Exercise 1.1.

4.14 Show that computing Tribesw,s by a CNF formula requires size at least ws.
4.15 Show that there is a universal constant ≤0 > 0 such that the following
holds: Every 3
4 n-junta g : {−1, 1}n → {−1, 1} is ≤0-far from Tribesn (assum-
ing n > 1). (Hint: Letting J denote the coordinates on which g depends,
show that if J has non-full intersection with at least 1
4 of the tribes/terms
then when x ∼ {−1, 1}J, there is a constant chance that Var[ f|x] ≥ Ω(1).)

4.16 Using the KKL Theorem, show that if f : {−1, 1}n → {−1, 1} is a transitive-

symmetric function with Var[ f ] ≥ Ω(1), then I[ f ] ≥ Ω(log n).

4.17 Let f : {True,False}n → {True,False} be computable by a CNF C of width w
over variables x1, . . . , xn. In this exercise you will show that I[ f ] ≤ w.

Consider the following algorithm A , which takes as input a permu-
tation π ∈ Sn and a “seed” r ∈ {True,False}n, and which “tries” to output a
string z satisfying C:

A (π, r) :

For i = π(1), π(2), . . . , π(n):

If C contains the clause (xi) and the clause (xi), abort.
Else if C contains just the clause (xi), set zi = True.
Else if C contains just the clause (xi), set zi = False.
Else set zi = r i and say coordinate i was “unforced”.
Syntactically simplify C under the restriction xi = zi.

Output z.

We write F j(π, r) for the 0-1 indicator that coordinate j was forced in the
execution of A (π, r).
(a) Show that if A (π, r) does not abort, then its output z satises C.
(b) Fix any y satisfying C and write p(y) = Prπ,r[A (π, r) = y], where π
j=1(1/2)1−F j(π,y)].

and r are uniformly random. Show that p(y) = Eπ[

(c) Deduce 2n p(y) ≥ 2
(d) Suppose further that y⊕ j does not satisfy C. Show Eπ[F j(π, y)] ≥ 1/w.
(e) Deduce I[ f ] ≤ w.

j=1 Eπ[F j(π, y)].

n

n

+” is dened to be the logical AND of xi1

4.18 Given Boolean variables x1, . . . , xn, a “random monotone term of width w ∈
, where i1, . . . , iw are
chosen independently and uniformly at random from [n]. (If the i j’s are
not all distinct then the resulting term will in fact have width strictly
less than w.) A “random monotone DNF of width w and size s” is dened

, . . . , xiw

Copyright © Ryan O’Donnell, 2014, 2015, 2016, 2017, 2018, 2019, 2020, 2021.



<!-- pdf-page: 110 -->
110

4. DNF formulas and small-depth circuits

to be the logical OR of s independent random monotone terms. For this
exercise we assume n is a sufciently large perfect square, and we let ϕ
be a random monotone DNF of width
(a) Fix an input x ∈ {−1, 1}n and dene u = (

n].
Let V j be the event that the jth term of ϕ is made 1 (logical False)
by x. Compute Pr[V j] and Pr[ϕ(x) = 1], and show that the latter is
at least 10−9 assuming |u| ≤ 2.

n and size 2
n

n.
i=1 xi)/

n ∈ [−

n,

p

p

p

p

p

(b) Let U j be the event that the jth term of ϕ has exactly one 1 on input x.

Show that Pr[U j | V j] ≥ Ω(w2−w) assuming |u| ≤ 2.

(c) Suppose we condition on ϕ(x) = 1; i.e., ∩ jV j. Argue that the events U j
are independent. Further, argue that for the U j’s that do occur, the
indices of their uniquely-1 variables are independent and uniformly
random among the 1’s of x.
(d) Show that Pr[sensϕ(x) ≥ c
ciently small constant.

n | ϕ(x) = 1] ≥ 1 − 10−10 for c > 0 a suf-

p

(e) Show that Prx[|(
(f ) Deduce that there exists a monotone function f : {−1, 1}n → {−1, 1}
n] ≥ c′ for some universal

n| ≤ 2] ≥ Ω(1).
i=1 xi)/
with the property that Prx[sens f (x) ≥ c′p
constant c′ > 0.

n

p

(g) Both Majn and the function f from the previous exercise have average
n). Contrast the “way” in which this occurs for the two

p

sensitivity Θ(
functions.

4.19 In this exercise you will prove the Baby Switching Lemma with constant 3
in place of 5. Let φ = T1 ∨ T2 ∨ · · · ∨ Ts be a DNF of width w ≥ 1 over
variables x1, . . . , xn. We may assume δ ≤ 1/3, else the theorem is trivial.
(a) Suppose R = (J | z) is a “bad” restriction, meaning that φJ|z is not a
constant function. Let i be minimal such that (Ti)J|z is neither con-
stantly True or False, and let j be minimal such that x j or x j appears in
this restricted term. Show there is a unique restriction R′ = (J\{ j} | z′)
extending R that doesn’t falsify Ti.

(b) Suppose we enumerate all bad restrictions R, and for each we write
the associated R′ as in (a). Show that no restriction is written more
than w times.

(c) If (J | z) is a δ-random restriction and R and R′ are as in (a), show
Pr[(J | z) = R′].

that Pr[(J | z) = R] = 2δ
1−δ

(d) Complete the proof by showing Pr[(J | z) is bad] ≤ 3δw.

4.20 In this exercise you will prove Theorem 4.30. Say that a “(d, w, s′)-circuit”
is a depth-d circuit with width at most w and with at most s′ nodes at
layers 2 through d (i.e., excluding layers 0 and 1).
(a) Show by induction on d ≥ 2 that any f : {−1, 1}n → {−1, 1} computable

by a (d, w, s′)-circuit satises I[ f ] ≤ wO(log s′)d−2.

(b) Deduce Theorem 4.30.

Copyright © Ryan O’Donnell, 2014, 2015, 2016, 2017, 2018, 2019, 2020, 2021.



<!-- pdf-page: 111 -->
4.6. Exercises and notes

111

Notes. Mansour’s Conjecture dates from 1994 [Man94]. Even the weaker
version would imply that the Kushilevitz–Mansour algorithm learns the class
of poly(n)-size DNF with any constant error, using queries, in time poly(n). In
fact, this learning result was subsequently obtained in a celebrated work of
Jackson [Jac97], using a different method (which begins with Exercise 4.4).
Nevertheless, the Mansour Conjecture remains important for learning theory
since Gopalan, Kalai, and Klivans [GKK08] have shown that it implies the
same learning result in the more challenging and realistic model of “agnostic
learning”. Theorems 4.24 and 4.25 are also due to Mansour [Man95].

The method of random restrictions dates back to Subbotovskaya [Sub61].
Håstad’s Switching Lemma [Hås87] and his Lemma 4.28 are the culmina-
tion of a line of work due to Furst, Saxe, and Sipser [FSS84], Ajtai [Ajt83],
and Yao [Yao85]. Linial, Mansour, and Nisan [LMN89, LMN93] proved
Lemma 4.21, which allowed them to deduce the LMN Theorem and its con-
sequences. An additional cryptographic application of the LMN Theorem
is found in Goldmann and Russell [GR00]. The strongest lower bound cur-
rently known for approximately computing parity in AC0 is due to Impagli-
azzo, Matthews, and Paturi [IMP12] and independently to Håstad [Hås12].

Theorem 4.20 and its generalization Theorem 4.30 are from the work of
Boppana [Bop97]; Linial, Mansour, and Nisan had given the weaker bound
O(log s)d. Exercise 4.17 is due to Amano [Ama11], and Exercise 4.18 is due
to Talagrand [Tal96].

Copyright © Ryan O’Donnell, 2014, 2015, 2016, 2017, 2018, 2019, 2020, 2021.



<!-- pdf-page: 112 -->


<!-- pdf-page: 113 -->
Chapter 5

Majority and threshold
functions

This chapter is devoted to linear threshold functions, their generalization
to higher degrees, and their exemplar the majority function. The study of
LTFs leads naturally to the introduction of the Central Limit Theorem and
Gaussian random variables – important tools in analysis of Boolean functions.
We will rst use these tools to analyze the Fourier spectrum of the Majn
function, which in some sense “converges” as n → ∞. We’ll then extend to
analyzing the degree-1 Fourier weight, noise stability, and total inuence of
general linear threshold functions.

5.1. Linear threshold functions and polynomial threshold

functions

Recall from Chapter 2.1 that a linear threshold function (abbreviated LTF) is
a Boolean-valued function f : {−1, 1}n → {−1, 1} that can be represented as

f (x) = sgn(a0 + a1x1 + · · · + an xn)

(5.1)

for some constants a0, a1, . . . , an ∈ . (For deniteness we’ll take sgn(0) = 1.
If we’re using the representation f : {−1, 1}n → {0, 1}, then f is an LTF if it
can be represented as f (x) = 1{a0+a1 x1+···+an xn>0}.) Examples include majority,
AND, OR, dictators, and decision lists (Exercise 3.23). Besides representing
“weighted majority” voting schemes, LTFs play an important role in learning
theory and in circuit complexity.

There is also a geometric perspective on LTFs. Writing `(x) = a0 + a1x1 +
· · · + an xn, we can think of ` as an afne function n → . Then sgn(`(x)) is

Copyright © Ryan O’Donnell, 2014, 2015, 2016, 2017, 2018, 2019, 2020, 2021.

113



<!-- pdf-page: 114 -->
114

5. Majority and threshold functions

the ±1-indicator of a halfspace in n. A Boolean LTF is thus the restriction of
such a halfspace-indicator to the discrete cube {−1, 1}n ⊂ n. Equivalently, a
function f : {−1, 1}n → {−1, 1} is an LTF if and only if it has a “linear separator”;
i.e., a hyperplane in n that separates the points f labels 1 from the points f
labels −1.

An LTF f : {−1, 1}n → {−1, 1} can have several different representations
as in (5.1) – in fact it always has innitely many. This is clear from the
geometric viewpoint; any small enough perturbation to a linear separator will
not change the way it partitions the discrete cube. Because we can make
these perturbations, we may ensure that a0 + a1x1 + · · · + an xn 6= 0 for every
x ∈ {−1, 1}n. We’ll usually insist that LTF representations have this property
so that the nuisance of sgn(0) doesn’t arise. We also observe that we can scale
all of the coefcients in an LTF representation by the same positive constant
without changing the LTF. These observations can be used to show it’s always
possible to take the ai’s to be integers (Exercise 5.1). However, we will most
often scale so that
= 1; this is convenient when using the Central
Limit Theorem.

i=1 a2

n

i

The most elegant result connecting LTFs and Fourier expansions is Chow’s
Theorem, which says that a Boolean LTF is completely determined by its
degree-0 and degree-1 Fourier coefcients. In fact, it’s determined not just
within the class of LTFs but within the class of all Boolean functions:

Theorem 5.1. Let f : {−1, 1}n → {−1, 1} be an LTF and let g : {−1, 1}n → {−1, 1}
be any function. If g(S) = f (S) for all |S| ≤ 1, then g = f .

Proof. Let f (x) = sgn(`(x)), where ` : {−1, 1}n → has degree at most 1 and
is never 0 on {−1, 1}n. For any x ∈ {−1, 1}n we have f (x)`(x) = |`(x)| ≥ g(x)`(x),
with equality if and only if f (x) = g(x) (here we use `(x) 6= 0). Using this
observation along with Plancherel’s Theorem (twice) we have

∑

|S|≤1

f (S) `(S) = E[ f (x)`(x)] ≥ E[g(x)`(x)] =

∑

|S|≤1

g(S) `(S).

But by assumption, the left-hand and right-hand sides above are equal. Thus
the inequality must be an equality for every value of x; i.e., f (x) = g(x) ∀x. 

In light of Chow’s Theorem, the n +1 numbers g(;), g({1}), . . . , g({n}) are some-
times called the Chow parameters of the Boolean function g.

As we will show in Section 5.5, linear threshold functions are very noise-
stable; hence they have a lot of their Fourier weight at low degrees. Here is a
simple result along these lines:

Theorem 5.2. Let f : {−1, 1}n → {−1, 1} be an LTF. Then W≤1[ f ] ≥ 1/2.

Copyright © Ryan O’Donnell, 2014, 2015, 2016, 2017, 2018, 2019, 2020, 2021.



<!-- pdf-page: 115 -->
5.1. Linear threshold functions and polynomial threshold functions

115

Proof. Writing f (x) = sgn(`(x)) we have



‖`‖1 = E[|`(x)|] = 〈 f , `〉 = 〈 f ≤1, `〉 ≤ ‖ f ≤1‖2‖`‖2 =

W≤1[ f ] · ‖`‖2,

where the third equality follows from Plancherel and the inequality is Cauchy–
Schwarz. Assume rst that `(x) = a1x1 + · · · + an xn (i.e., `(x) has no constant
term). The Khintchine–Kahane Inequality (Exercise 2.55) states that ‖`‖1 ≥
1p
2

‖`‖2, and hence we deduce



1p
2

‖`‖2 ≤

W≤1[ f ] · ‖`‖2.

The conclusion W≤1[ f ] ≥ 1/2 follows immediately (since ‖`‖2 cannot be 0). The

case when `(x) has a constant term is handled in Exercise 5.5.

From Exercise 2.22 we know that W≤1[Majn] = W1[Majn] ≥ 2/π for all n;
it is reasonable to conjecture that majority is extremal for Theorem 5.2. This
is an open problem.

Conjecture 5.3. Let f : {−1, 1}n → {−1, 1} be an LTF. Then W≤1[ f ] ≥ 2/π.

A natural generalization of linear threshold functions is polynomial thresh-

old functions:

Denition 5.4. A function f : {−1, 1}n → {−1, 1} is called a polynomial thresh-
old function (PTF) of degree at most k if it is expressible as f (x) = sgn(p(x))
for some real polynomial p : {−1, 1}n → of degree at most k.

Example 5.5. Let f : {−1, 1}4 → {−1, 1} be the 4-bit equality function, which
is 1 if and only if all input bits are equal. Then f is a degree-2 PTF because it
has the representation f (x) = sgn(−3 + x1x2 + x1x3 + x1x4 + x2x3 + x2x4 + x3x4).

Every Boolean function f : {−1, 1}n → {−1, 1} is a PTF of degree at most n,
since we can take the sign of its Fourier expansion. Thus we are usually
interested in the case when the degree k is “small”, say, k = On(1). Low-
degree PTFs arise frequently in learning theory, for example, as hypotheses
in the Low-Degree Algorithm and many other practical learning algorithms.
Indeed, any function with low noise sensitivity is close to being a low-degree
PTF; by combining Propositions 3.3 and 3.31 we immediately obtain:

Proposition 5.6. Let f : {−1, 1}n → {−1, 1} and let δ ∈ (0, 1/2]. Then f is
(3NSδ[ f ])-close to a PTF of degree 1/δ.

For a kind of converse to this proposition, see Section 5.5.

PTFs also arise in circuit complexity, wherein a PTF representation
(



f (x) = sgn

s∑

ai xTi

Copyright © Ryan O’Donnell, 2014, 2015, 2016, 2017, 2018, 2019, 2020, 2021.

i=1



<!-- pdf-page: 116 -->
116

5. Majority and threshold functions

is thought of as a “threshold-of-parities circuit”: i.e., a depth-2 circuit with s
“parity gates” xTi at layer 1 and a single “(linear) threshold gate” at layer 2.
From this point of view, the size of the circuit corresponds to the sparsity of
the PTF representation:

Denition 5.7. We say a PTF representation f (x) = sgn(p(x)) has sparsity at
most s if p(x) is a multilinear polynomial with at most s terms.

For example, the PTF representation of the 4-bit equality function from Ex-
ample 5.5 has sparsity 7.

Let’s extend the two theorems about LTFs we proved above to the case of
PTFs. The generalization of Chow’s Theorem is straightforward; its proof is
left as Exercise 5.9:

Theorem 5.8. Let f : {−1, 1}n → {−1, 1} be a PTF of degree at most k and let
g : {−1, 1}n → {−1, 1} be any function. If g(S) = f (S) for all |S| ≤ k, then g = f .

We also have the following extension of Theorem 5.2:

Theorem 5.9. Let f : {−1, 1}n → {−1, 1} be a degree-k PTF. Then W≤k[ f ] ≥ e−2k.

Proof. Writing f (x) = sgn(p(x)) for p of degree k, we again have



‖p‖1 = E[|p(x)|] = 〈 f , p〉 = 〈 f ≤k, p〉 ≤ ‖ f ≤k‖2‖p‖2 =

W≤k[ f ] · ‖p‖2.

To complete the proof we need the fact that ‖p‖2 ≤ ek‖p‖1 for any degree-k
polynomial p : {−1, 1}n → . We will prove this much later in Theorem 9.22 of

Chapter 9 on hypercontractivity.

The e−2k in this theorem cannot be improved beyond 21−k; see Exercise 5.11.

We close this section by discussing PTF sparsity. We begin with a (simpler)
variant of Theorem 5.9, which is useful for proving PTF sparsity lower bounds:

Theorem 5.10. Let f : {−1, 1}n → {−1, 1} be expressible as a PTF over the
collection of monomials F ⊆ 2[n]; i.e., f (x) = sgn(p(x)) for some polynomial
p(x) =

S∈F p(S)xS. Then

S∈F | f (S)| ≥ 1.





Proof. Dene g : {−1, 1}n → by g(x) =
(Exercise 3.9) we have



f (S) xS. Since ˆ‖p ˆ‖∞ ≤ ‖p‖1

S∈F

ˆ‖p ˆ‖∞ ≤ ‖p‖1 = E[ f (x)p(x)] =

∑

S⊆[n]

f (S) p(S) =

∑

S∈F

g(S) p(S) ≤ ˆ‖g ˆ‖1

ˆ‖p ˆ‖∞,

and hence ˆ‖g ˆ‖1 ≥ 1 as claimed.



We can use this result to show that the “inner product mod 2 function”

(see Exercise 1.1) requires huge threshold-of-parities circuits:

Copyright © Ryan O’Donnell, 2014, 2015, 2016, 2017, 2018, 2019, 2020, 2021.



<!-- pdf-page: 117 -->
5.1. Linear threshold functions and polynomial threshold functions

117

Corollary 5.11. Any PTF representation of the inner product mod 2 function
IP2n :

2 → {−1, 1} has sparsity at least 2n.

2n

Proof. This follows immediately from Theorem 5.10 and the fact that |IP2n(S)| =
2−n for all S ⊆ [2n] (Exercise 1.1).



We can also show that any function f : {−1, 1}n → {−1, 1} with small Fourier
1-norm ˆ‖ f ˆ‖1 has a sparse PTF representation. In fact a stronger result holds:
such a function can be additively approximated by a sparse polynomial:

Theorem 5.12. Let f : {−1, 1}n → be nonzero, let δ > 0, and let s ≥ 4nˆ‖ f ˆ‖2
1/δ2
be an integer. Then there is a multilinear polynomial q : {−1, 1}n → of spar-
sity at most s such that ‖ f − q‖∞ < δ.

Proof. The proof is by the probabilistic method. Let T ⊆ [n] be randomly
chosen according to the distribution Pr[T = T] = | f (T)|
. Let T1, . . . , T s be inde-
ˆ‖ f ˆ‖1
pendent draws from this distribution and dene the multilinear polynomial

p(x) =

s∑

i=1

sgn( f (T i)) xT i .

When x ∈ {−1, 1}n is xed, each monomial sgn( f (T i)) xT i becomes a ±1-valued
random variable with expectation
∑

∑

| f (T)|
ˆ‖ f ˆ‖1

· sgn( f (T)) xT = 1
ˆ‖ f ˆ‖1

f (T) xT = f (x)
ˆ‖ f ˆ‖1

.

T⊆[n]

T⊆[n]

Thus by a Chernoff bound, for any ≤ > 0,

∣
∣
∣p(x) − f (x)
ˆ‖ f ˆ‖1



∣
∣
∣ ≥ ≤s

s

≤ 2 exp(−≤2s/2).

Pr
T1,...,T s
Selecting ≤ = δ/ˆ‖ f ˆ‖1 and using s ≥ 4nˆ‖ f ˆ‖2
1/δ2, the above probability is at most
2 exp(−2n) < 2−n. Taking a union bound over all 2n choices of x ∈ {−1, 1}n,
i=1 sgn( f (Ti)) xTi such that for all
we conclude that there exists some p(x) =
x ∈ {−1, 1}n,
∣
∣
∣p(x) − f (x)
ˆ‖ f ˆ‖1

∣
∣
∣ < ≤s = δ
ˆ‖ f ˆ‖1

· p(x) − f (x)

∣
∣
∣ < δ.

s =⇒

ˆ‖ f ˆ‖1
s

s

∣
∣
∣

s

Thus we may take q =

ˆ‖ f ˆ‖1
s

· p.



Corollary 5.13. Let f : {−1, 1}n → {−1, 1}. Then f is expressible as a PTF of
sparsity at most s = d4nˆ‖ f ˆ‖2
1e. Indeed, f can be represented as a majority of s
parities or negated-parities.

Proof. Apply the previous theorem with δ = 1; we then have f (x) = sgn(q(x)).
Since this is also equivalent to sgn(p(x)), the terms sgn( f (Ti)) xTi are the

required parities/negated-parities.

Copyright © Ryan O’Donnell, 2014, 2015, 2016, 2017, 2018, 2019, 2020, 2021.



<!-- pdf-page: 118 -->
118

5. Majority and threshold functions

Though functions computable by small DNFs need not have small Fourier
1-norm, it is a further easy corollary that they can be computed by sparse
PTFs: see Exercise 5.13. We also remark that there is no good converse to
Corollary 5.13: the Majn function has a PTF (indeed, an LTF) of sparsity n
but has exponentially large Fourier 1-norm (Exercise 5.26).

5.2. Majority, and the Central Limit Theorem

Majority is one of the more important functions in Boolean analysis, and
its study motivates the introduction of one of the more important tools: the
Central Limit Theorem (CLT). In this section we will show how the CLT can be
used to estimate the total inuence and the noise stability of Majn. Though
we already determined I[Majn] ∼
n in Exercise 2.22 using binomial
2/π
coefcients and Stirling’s Formula, computations using the CLT are more
exible and extend to other linear threshold functions.

p

p

We begin with a reminder about the CLT. Suppose X 1, . . . , X n are indepen-
dent random variables and S = X 1 + · · · + X n. Roughly speaking, the CLT says
that so long as no X i is too dominant in terms of variance, the distribution
of S is close to that of a Gaussian random variable with the same mean and
variance. Recall:

Notation 5.14. We write Z ∼ N(0, 1) denote that Z is a standard Gaussian
random variable. We use the notation

ϕ(z) = 1p
2π

e−z2/2, Φ(t) =

φ(z) dz, Φ(t) = Φ(−t) =

φ(z) dz

−∞

t

∫t

∫∞

for the pdf, cdf, and complementary cdf of this random variable. More gen-
d×d is a positive semidenite matrix, we write
erally, if µ ∈
Z ∼ N(µ, Σ) to denote that Z is a d-dimensional random vector with mean µ
and covariance matrix Σ.

d and Σ ∈

We give a precise statement of the CLT below in the form of the Berry–
Esseen Theorem. The CLT also extends to the multidimensional case (sums
of independent random vectors); we give a precise statement in Exercise 5.33.
In Chapter 11 we will show one way to prove such CLTs.

Let’s see how we can use the CLT to obtain the estimate I[Majn] ∼
Recall the proof of Theorem 2.33, which shows that Majn maximizes
among all f : {−1, 1}n → {−1, 1}. In it we saw that
n∑

I[Majn] =

ÉMajn(i) = E
x

[Majn(x)(

xi)] = E
x

[|

xi|].



i



i

i=1

When using the CLT, it’s convenient to dene majority (equivalently) as

Majn(x) = sgn

 n

i=1



xi

.

1p
n

Copyright © Ryan O’Donnell, 2014, 2015, 2016, 2017, 2018, 2019, 2020, 2021.

p
n

2/π

i=1

p

n.
f (i)

(5.2)



<!-- pdf-page: 119 -->
119

(5.3)

5.2. Majority, and the Central Limit Theorem

This motivates writing (5.2) as

I[Majn] =

p

n · E

x∼{−1,1}n

[|



i

1p
n

xi|].

n

n)2 = 1.
If we introduce S =
Thus the CLT tells us that the distribution of S is close (for large n) to that of
a standard Gaussian, Z ∼ N(0, 1). So as n → ∞ we have
∫∞

xi, then S has mean 0 and variance

i(1/

i=1

1p
n

p

p

e−z2/2 dz = −

2/πe−z2/2

=

2/π,

(5.4)

E
x

[|S|] ∼ E

Z∼N(0,1)

[|Z|] = 2

0

z · 1p
2π

∣
∣
∣

∞

0



p

p

p

n.

2/π

which when combined with (5.3) gives us the estimate I[Majn] ∼

To make this kind of estimate more precise we state the Berry–Esseen
Theorem, which is a strong version of the CLT giving explicit error bounds
rather than just limiting statements.

Berry–Esseen (Central Limit) Theorem. Let X 1, . . . , X n be independent
random variables with E[X i] = 0 and Var[X i] = σ2
= 1.
i
i=1 X i and let Z ∼ N(0, 1) be a standard Gaussian. Then for all u ∈ ,
Let S =

, and assume

i=1 σ2

n

n

i

where

| Pr[S ≤ u] − Pr[Z ≤ u]| ≤ cγ,

γ =

n∑

i=1

‖X i‖3
3

and c is a universal constant. (For deniteness, c = .56 is acceptable.)

Remark 5.15. If all of the X i’s satisfy |X i| ≤ ≤ with probability 1, then we
can use the bound

γ =

n∑

i=1

E[|X i|3] ≤ ≤ ·

n∑

i=1

E[|X i|2] = ≤ ·

n∑

i=1

σ2

i = ≤.

See Exercises 5.16 and 5.17 for some additional observations.

Our most frequent use of the Berry–Esseen Theorem will be in analyzing

random sums

S =

n∑

i=1

ai xi,



where x ∼ {−1, 1}n and the constants ai ∈
= 1.
are normalized so that
For majority, all of the ai’s were equal to 1p
. But from Remark 5.15 we see
n
that S is close in distribution to a standard Gaussian so long as each |ai| is
small. For example, in Exercise 5.31 you are asked to show the following:

i a2
i

Theorem 5.16. Let a1, . . . , an ∈

∣
∣
∣
∣ E
x∼{−1,1}n

satisfy

[|



i

ai xi|] −



i a2
i
p

= 1 and |ai| ≤ ≤ for all i. Then
∣
∣
∣
∣ ≤ C≤,

2/π

where C is a universal constant.

Copyright © Ryan O’Donnell, 2014, 2015, 2016, 2017, 2018, 2019, 2020, 2021.



<!-- pdf-page: 120 -->
120

5. Majority and threshold functions

Theorem 5.16 justies (5.4) with an error bound of O(1/

p

p

n), yielding the
n ± O(1) (cf. Exercise 2.22, which gives

2/π

more precise estimate I[Majn] =
an even better error bound).

p

Now let’s turn to the noise stability of majority. Theorem 2.45 stated the

formula

lim
n→∞

Stabρ[Majn] = 2
π

arcsin ρ = 1 − 2
π

arccos ρ.

(5.5)

Let’s now spend some time justifying this using the multidimensional CLT.
(For complete details, see Exercise 5.33.) By denition,

Stabρ[Majn] = E
(x,y)
ρ-correlated

[Majn(x) · Majn(y)] = E
(x,y)
ρ-correlated

[sgn(



i

1p
n

xi) · sgn(



i

1p
n

yi)]. (5.6)

For each i ∈ [n] let’s stack 1p
n
then write

xi and 1p
n



yi into a 2-dimensional vector and


n∑

~S =

1p
n
1p
n
We are summing n independent random vectors, so the multidimensional CLT
tells us that the distribution of ~S is close to that of a 2-dimensional Gaussian
~Z with the same mean and covariance matrix, namely (see Exercise 5.19)
]

∈ 2.

xi
yi

(5.7)

[

])

i=1

[

~Z ∼ N

0
0

,

1 ρ
ρ 1

.

Continuing from (5.6),

Stabρ[Majn] = E[sgn(~S1) · sgn(~S2)]

= Pr[sgn(~S1) = sgn(~S2)] − Pr[sgn(~S1) 6= sgn(~S2)]
= 2 Pr[sgn(~S1) = sgn(~S2)] − 1 = 4 Pr[~S ∈ Q−−] − 1,

2 and the last step uses the
where Q−− denotes the lower-left quadrant of
symmetry Pr[~S ∈ Q++] = Pr[~S ∈ Q−−]. Since Q−− is convex, the 2-dimensional
CLT lets us deduce

Pr[~S ∈ Q−−] = Pr[~Z ∈ Q−−].

lim
n→∞

So to justify the noise stability formula (5.5) for majority, it remains to verify

4 Pr[~Z ∈ Q−−] − 1 = 1 − 2
π

arccos ρ ⇐⇒ Pr[~Z ∈ Q−−] =

1
2

−

1
2

arccos ρ

π

.

And this in turn is a 19th-century identity known as Sheppard’s Formula:

Sheppard’s Formula. Let z1, z2 be standard Gaussian random variables
with correlation E[z1 z2] = ρ ∈ [−1, 1]. Then
1
2

Pr[z1 ≤ 0, z2 ≤ 0] =

arccos ρ

1
2

−

π

.

Copyright © Ryan O’Donnell, 2014, 2015, 2016, 2017, 2018, 2019, 2020, 2021.



<!-- pdf-page: 121 -->
5.3. The Fourier coefcients of Majority

121

Proving Sheppard’s Formula is a nice exercise using the rotational symmetry
of a pair of independent standard Gaussians; we defer the proof till Exam-
ple 11.19 in Chapter 11.1. This completes the justication of formula (5.5) for
the limiting noise stability of majority.

You may have noticed that once we applied the 2-dimensional CLT to (5.6),
the remainder of the derivation had nothing to do with majority. In fact,
the same analysis works for any linear threshold function sgn(a1x1 + · · · +
an xn), the only difference being the “error term” arising from the CLT. As in
Theorem 5.16, this error is small so long as no coefcient ai is too dominant:

Theorem 5.17. Let f : {−1, 1}n → {−1, 1} be an unbiased LTF, f (x) = sgn(a1x1 +
· · · + an xn) with



i a2
i

= 1 and |ai| ≤ ≤ for all i. Then for any ρ ∈ (−1, 1),
∣
∣
∣Stabρ[ f ] − 2
π

∣
∣
∣ ≤ O

arcsin ρ

≤p





.

1−ρ2

You are asked to prove Theorem 5.17 in Exercise 5.33. In the particular
for all i we can make a slightly stronger claim

case of Majn where ai = 1p
n
(see Exercise 5.23):

Theorem 5.18. For any ρ ∈ [0, 1), Stabρ[Majn] is a decreasing function of n,
with

2
π

arcsin ρ ≤ Stabρ[Majn] ≤ 2
π

arcsin ρ + O





.

1p
1−ρ2

p

n

We end this section by mentioning another way in which the majority
function is extremal: among all unbiased functions with small inuences, it
has (essentially) the largest noise stability.

Majority Is Stablest Theorem. Fix ρ ∈ (0, 1). Then for any f : {−1, 1}n →
[−1, 1] with E[ f ] = 0 and MaxInf[ f ] ≤ τ,

Stabρ[ f ] ≤ 2
π

arcsin ρ + oτ(1) = 1 − 2
π

arccos ρ + oτ(1).

For sufciently small ρ, we’ll prove this in Section 5.4. The proof of the full
Majority Is Stablest Theorem will have to wait until Chapter 11.

5.3. The Fourier coefcients of Majority

In this section we will analyze the Fourier coefcients of Majn. In fact, we
give an explicit formula for them in Theorem 5.19 below. But most of the time
this formula is not too useful; instead, it’s better to understand the Fourier
coefcients of Majn asymptotically as n → ∞.

Let’s begin with a few basic observations. First, Majn is a symmetric func-
tion and hence ÉMajn(S) only depends on |S| (Exercise 1.30). Second, Majn is
an odd function and hence ÉMajn(S) = 0 whenever |S| is even (Exercise 1.8).

Copyright © Ryan O’Donnell, 2014, 2015, 2016, 2017, 2018, 2019, 2020, 2021.



<!-- pdf-page: 122 -->
122

5. Majority and threshold functions



,

(5.8)

(5.9)



n
k

It remains to determine the Fourier coefcients ÉMajn(S) for |S| odd. By sym-
metry, ÉMajn(S)2 = Wk[Majn]/
for all |S| = k, so if we are content to know
the magnitudes of Majn’s Fourier coefcients, it sufces to determine the
quantities Wk(Majn).
In fact, for each k ∈

the quantity Wk(Majn) converges to a xed constant
as n → ∞. We can deduce this using our analysis of the noise stability of
majority. From the previous section we know that for all |ρ| ≤ 1,

lim
n→∞

Stabρ[Majn] = 2
π

arcsin ρ = 2
π

ρ + 1

6 ρ3 + 3

40 ρ5 + 5

112 ρ7 + · · ·



where we have used the power series for arcsin,

arcsin z =

∑

k odd

2
k2k

k − 1
k−1
2

(



· zk,

valid for |ρ| ≤ 1 (see Exercise 5.18). Comparing (5.8) with the formula

Stabρ[Majn] =

Wk[Majn] · ρk

∑

suggests the following: For each xed k ∈ ,

k≥0

lim
n→∞

Wk[Majn] = [ρk]( 2
π

arcsin ρ) =

k−1



k−1
2



4
πk2k
0

if k odd,

if k even.

(5.10)

(Here [zk]F(z) denotes the coefcient on zk in power series F(z).) Indeed, we
prove this identity below in Theorem 5.22. The noise stability method that
suggests it can also be made formal (Exercise 5.25).

Identity (5.10) is one way to formulate precisely the statement that the
“Fourier spectrum of Majn converges”. Introducing notation such as “Wk(Maj)”
for the quantity in (5.10), we have the further asymptotics

for k odd,

Wk(Maj) ∼

W>k(Maj) ∼

3/2

3/2





2
π

2
π

k−3/2,

k−1/2

as k → ∞.

(5.11)

(See Exercise 5.27.) The estimates (5.11), together with the precise value
W1(Maj) = 2
, are usually all you need to know about the Fourier coefcients
π
of majority.

Nevertheless, let’s now compute the Fourier coefcients of Majn exactly.

Theorem 5.19. If |S| is even, then ÉMajn(S) = 0. If |S| = k is odd,

ÉMajn(S) = (−1)

k−1
2



 n−1
2
k−1
2

n−1
k−1

 · 2
2n

n−1



n−1
2

.

Proof. The rst statement holds because Majn is an odd function; henceforth
we assume |S| = k is odd. The trick will be to compute the Fourier expansion of

Copyright © Ryan O’Donnell, 2014, 2015, 2016, 2017, 2018, 2019, 2020, 2021.



<!-- pdf-page: 123 -->
5.3. The Fourier coefcients of Majority

123

majority’s derivative DnMajn = Halfn−1 : {−1, 1}n−1 → {0, 1}, the 0-1 indicator of
the set of (n − 1)-bit strings with exactly half of their coordinates equal to −1.
By the derivative formula and the fact that Majn is symmetric, ÉMajn(S) =
·Halfn−1(T) for any T ⊆ [n − 1] with |T| = k − 1. So writing n − 1 = 2m and
k − 1 = 2 j, it sufces to show

·Half2m([2 j]) = (−1) j

 · 1
22m



2m
m

.

(5.12)



m
j
2m
2 j

By the probabilistic denition of Tρ, for any ρ ∈ [−1, 1] we have

TρHalf2m(1, 1, . . . , 1) =

E
x∼Nρ((1,1,...,1))

[Half2m(x)] = Pr[x has m 1’s and m −1’s],

where each coordinate of x is 1 with probability 1

TρHalf2m(1, 1, . . . , 1) =

2 ρ)m( 1
On the other hand, by the Fourier formula for Tρ and the fact that Half2m is
symmetric we have

(1 − ρ2)m.

2 + 1
( 1

2 − 1

(5.13)

22m



2m
m

2 + 1
2 ρ)m = 1

2 ρ. Thus

2m
m

TρHalf2m(1, 1, . . . , 1) =

∑

U⊆[2m]

·Half2m(U)ρ|U| =



2m
i

2m∑

i=0

·Half2m([i])ρ i.

(5.14)

Since we have equality (5.13) = (5.14) between two degree-2m polynomials
of ρ on all of [−1, 1], we can equate coefcients. In particular, for i = 2 j we
have



2m
2 j

·Half2m([2 j]) = 1
22m



2m
m

· [ρ2 j](1 − ρ2)m = 1
22m



2m
m

· (−1) j



m
j

,

conrming (5.12).



You are asked to prove the following corollaries in Exercises 5.20, 5.22:

Corollary 5.20. ÉMajn(S) = (−1) n−1
also Wn−k+1[Majn] = k

n−k+1 Wk[Majn].

2 ÉMajn(T) whenever |S| + |T| = n + 1. Hence

Corollary 5.21. For any odd k, Wk[Majn] is a strictly decreasing function
of n (for n ≥ k odd).

We can now prove the identity (5.10):

Theorem 5.22. For each xed odd k,
Wk[Majn] ↘ [ρk]( 2
π

arcsin ρ) = 4

πk2k

k−1



k−1
2

as n ≥ k tends to ∞ (through the odd numbers). Further, we have the error
bound

[ρk]( 2
π

arcsin ρ) ≤ Wk[Majn] ≤ (1 + 2k/n) · [ρk]( 2
π
for all k < n/2. (For k > n/2 you can use Corollary 5.20.)

arcsin ρ)

(5.15)

Copyright © Ryan O’Donnell, 2014, 2015, 2016, 2017, 2018, 2019, 2020, 2021.



<!-- pdf-page: 124 -->
124

5. Majority and threshold functions

Proof. Corollary 5.21 tells us that Wk[Majn] is decreasing in n; hence we
only need to justify (5.15). Using the formula from Theorem 5.19 we have

Wk[Majn]

[ρk]( 2
π

arcsin ρ)

=

/

2

2

n−1
k−1



n
k

4
22n

n−1

n−1
2

2  n−1

2
k−1
2

k−1



k−1
2

4
πk2k

= π

2 n · 2k−n

n−k



n−k
2

· 21−n

n−1



n−1
2

,

where the second identity is veried by expanding all binomial coefcients
2
to factorials. By Stirling’s approximation we have 2−m
πm , meaning
that the ratio of the left side to the right side increases to 1 as m → ∞. Thus

 m
m/2

↗





Wk[Majn]

[ρk]( 2
π

arcsin ρ)

↗

p

n
p

n − k

n − 1

= (1 − k+1

n + k

n2 )−1/2,

and the right-hand side is at most 1+2k/n for 1 ≤ k ≤ n/2 by Exercise 5.24. 

Finally, we can deduce the asymptotics (5.11) from this theorem (see Ex-

ercise 5.27):

Corollary 5.23. Let k ∈

be odd and assume n = n(k) ≥ 2k2. Then

Wk(Majn) =
W>k(Majn) =

3/2

3/2





2
π

2
π

k−3/2 · (1 ± O(1/k)),

k−1/2 · (1 ± O(1/k)),

and hence the Fourier spectrum of Majn is ≤-concentrated on degree up to
8
π3 ≤−2 + O≤(1).

5.4. Degree-1 weight

In this section we prove two theorems about the degree-1 Fourier weight of
Boolean functions:

n∑

W1[ f ] =

f (i)2.

i=1

This important quantity can be given a combinatorial interpretation thanks
to the noise stability formula Stabρ[ f ] =

k≥0 ρk · Wk[ f ]:



For f : {−1, 1}n → , W1[ f ] =

d
dρ

Stabρ[ f ]

∣
∣
∣

.

ρ=0

Thinking of ‖ f ‖2 as constant and ρ → 0, the noise stability formula implies
Stabρ[ f ] = E[ f ]2 + W1[ f ]ρ ± O(ρ2),

or equivalently,

[ f (x), f (y)] = W1[ f ]ρ ± O(ρ2).

Cov
(x,y)
ρ-correlated

Copyright © Ryan O’Donnell, 2014, 2015, 2016, 2017, 2018, 2019, 2020, 2021.



<!-- pdf-page: 125 -->
5.4. Degree-1 weight

125

In other words, for f : {−1, 1}n → {−1, 1} the degree-1 weight quanties the
extent to which Pr[ f (x) = f (y)] increases when x and y go from being uncor-
related to being slightly correlated.

There is an additional viewpoint if we think of f as the indicator of a
subset A ⊆ {−1, 1}n and its noise sensitivity NSδ[ f ] as a notion of A’s “surface
area”, or “noisy boundary size”. For nearly maximal noise rates – i.e., δ =
2 − 1
1
2 ρ where ρ is small – we have that A’s noisy boundary size is “small” if
and only if W1[ f ] is “large” (vis-à-vis A’s measure).

Two examples suggest themselves when thinking of subsets of the Ham-

ming cube with small “boundary”: subcubes and Hamming balls.

Proposition 5.24. Let f :
sion k ≥ 1 (e.g., the ANDk function). Then E[ f ] = 2−k, W1[ f ] = k2−2k.

n
2 → {0, 1} be the indicator of a subcube of codimen-

Proposition 5.25. Fix t ∈ . Consider the sequence of LTFs f n : {−1, 1}n →
(That is, f n is the
{0, 1} dened by f n(x) = 1 if and only if
indicator of the Hamming ball {x : ∆(x, (1, . . . , 1)) < n

n}.) Then

1p
n

n

i=1

xi > t.
p
2 − t
W1[ f n] = φ(t)2.

2

lim
n→∞

E[ f n] = Φ(t),

lim
n→∞

You are asked to verify these facts in Exercises 5.29, 5.30. Regarding
Proposition 5.25, it’s natural for φ(t) to arise since W1[ f n] is related to the in-
xi≈ t.
uences of f n, and coordinates are inuential for f n if and only if
If we write α = limn→∞ E[ f n] then this proposition can be thought of as saying
that W1[ f n] → U (α)2, where U is dened as follows:

1p
n

n

i=1

Denition 5.26. The Gaussian isoperimetric function U : [0, 1] → [0, 1p
] is
2π
dened by U = φ ◦ Φ−1. This function is symmetric about 1/2; i.e., U = φ ◦ Φ−1.

The name of this function will be explained when we study the Gaussian
Isoperimetric Inequality in Chapter 11.4. For now we’ll just use the following
fact:

Proposition 5.27. For α → 0+, U (α) ∼ α

p

2 ln(1/α).

Proof. Write α = Φ(t), where t → ∞. We use the well-known fact that Φ(t) ∼
φ(t)/t. Thus

α ∼ 1p

2πt

exp(−t2/2) =⇒ t ∼



2 ln(1/α),


φ(t) ∼ Φ(t) · t =⇒ U (α) ∼ α · t ∼ α

2 ln(1/α).



Given Propositions 5.24 and 5.25, let’s consider the degree-1 Fourier
weight of subcubes and Hamming balls asymptotically as their “volume”
α = E[ f ] tends to 0. For the subcubes we have W1[ f ] = α2 log(1/α). For the

Copyright © Ryan O’Donnell, 2014, 2015, 2016, 2017, 2018, 2019, 2020, 2021.



<!-- pdf-page: 126 -->
126

5. Majority and threshold functions

Hamming balls we have W1[ f n] → U (α)2 ∼ 2α2 ln(1/α). So in both cases we
have an upper bound of O(α2 log(1/α)).

You should think of this upper bound O(α2 log(1/α)) as being unusually
small. The obvious a priori upper bound, given that f : {−1, 1}n → {0, 1} has
E[ f ] = α, is

W1[ f ] ≤ Var[ f ] = α(1 − α) ∼ α.

Yet subcubes and Hamming balls have degree-1 weight which is almost quadrat-
ically smaller. In fact the rst theorem we will show in this section is the
following:

Level-1 Inequality. Let f : {−1, 1}n → {0, 1} have mean E[ f ] = α ≤ 1/2. Then

(For the case α ≥ 1/2, replace f by 1 − f .)

W1[ f ] ≤ O(α2 log(1/α)).

Thus all small subsets of {−1, 1}n have unusually small W1[ f ]; or equiva-
lently (in some sense), unusually large “noisy boundary”. This is another key
illustration of the idea that the Hamming cube is a “small-set expander”.

Remark 5.28. The bound in the Level-1 Inequality has a sharp form, W1[ f ] ≤
2α2 ln(1/α). Thus Hamming balls are in fact the “asymptotic maximizers” of
W1[ f ] among sets of small volume α. Also, the inequality holds more generally
for f : {−1, 1}n → [−1, 1] with α = E[| f |].

Remark 5.29. The name “Level-1 Inequality” is not completely standard;
e.g., in additive combinatorics the result would be called Chang’s Inequality.
We use this name because we will also generalize to “Level-k Inequalities” in
Chapter 9.5.

So far we considered maximizing degree-1 weight among subsets of the
Hamming cube of a xed small volume, α. The second theorem in this section
is concerned with what happens when there is no volume constraint. In
this case, maximizing examples tend to have volume α = 1/2; switching the
notation to f : {−1, 1}n → {−1, 1}, this corresponds to f being unbiased (E[ f ] =
0). The unbiased Hamming ball is Majn, which we know has W1[Majn] → 2
.
π
This is quite large. But unbiased subcubes are just the dictators χi and their
negations; these have W1[±χi] = 1 which is obviously maximal.

Thus the question of which f : {−1, 1}n → {−1, 1} maximizes W1[ f ] has a
trivial answer. But this answer is arguably unsatisfactory, since dictators
(and their negations) are not “really” functions of n bits. Indeed, when we
studied social choice in Chapter 2 we were motivated to rule out functions f
having a coordinate with unfairly large inuence. And in fact Proposition 2.58
showed that if all f (i) are equal (and hence small) then W1[ f ] ≤ 2
+ on(1). The
π
second theorem of this section signicantly generalizes Proposition 2.58:

Copyright © Ryan O’Donnell, 2014, 2015, 2016, 2017, 2018, 2019, 2020, 2021.



<!-- pdf-page: 127 -->
5.4. Degree-1 weight

127

The 2
π

Theorem. Let f : {−1, 1}n → {−1, 1} satisfy | f (i)| ≤ ≤ for all i ∈ [n]. Then

Further, if W1[ f ] ≥ 2
π

+ O(≤).

W1[ f ] ≤ 2
π
p
≤)-close to the LTF sgn( f =1).

− ≤, then f is O(

(5.16)

Functions f with | f (i)| ≤ ≤ for all i ∈ [n] are called (≤, 1)-regular; see Chap-
ter 6.1. So the 2
Theorem says (roughly speaking) that within the class of
π
(≤, 1)-regular functions, the maximal degree-1 weight is 2
, and any function
π
achieving this is an unbiased LTF. Further, from Theorem 5.17 we know that
all unbiased LTFs which are (≤, 1)-regular achieve this.

Remark 5.30. Since we have Stabρ[ f ] ≈ W1[ f ]ρ and 2
π
is small, the 2
π
ρ → 0+.

ρ when ρ
Theorem gives the Majority Is Stablest Theorem in the limit

arcsin ρ ≈ 2
π

Let’s now discuss how we’ll prove our two theorems about degree-1 weight.
Let f : {−1, 1}n → {0, 1} and α = E[ f ]; we think of α as small for the Level-1
Inequality and α = 1/2 for the 2
Theorem. By Plancherel, W1[ f ] = E[ f (x)L(x)],
π
where

L(x) = f =1(x) = f (1)x1 + · · · + f (n)xn.
To upper-bound E[ f (x)L(x)], consider that as x varies the real number L(x)
may be rather large or small, but f (x) is always 0 or 1. Given that f (x) is 1
on only a α fraction of x’s, the “worst case” for E[ f (x)L(x)] would be if f (x)
were 1 precisely on the α fraction of x’s where L(x) is largest. In other words,
W1[ f ] = E[ f (x)L(x)] ≤ E[1{L(x)≥t} · L(x)],

(5.17)

where t is chosen so that

Pr[L(x) ≥ t] ≈ α.

(5.18)

But now we can analyze (5.17) quite effectively using tools such as Hoeffding’s
bound and the CLT, since L(x) is just a linear combination of independent ±1
random bits.
In particular L(x) has mean 0 and standard deviation σ =

W1[ f ] so by the CLT it acts like the Gaussian Z ∼ N(0, σ2), at least if we
assume all | f (i)| are small. If we are thinking of α = 1/2, then t = 0 and we get

σ2 = W1[ f ] ≤ E[1{L(x)≥0} · L(x)] ≈ E[1{Z≥0} · Z] = 1p
2π

σ;

, as claimed in the 2
π

This implies σ2 / 1
Theorem (after adjusting f ’s range
2π
to {−1, 1}). If we are instead thinking of α as small then (5.18) suggest taking
t ∼ σ
2 ln(1/α) so that Pr[Z ≥ t] ≈ α. Then a calculation akin to the one in
Proposition 5.27 implies

p

W1[ f ] ≤ E[1{L(x)≥t} · L(x)] ≈ α · σ

2 ln(1/α),



from which the Level-1 Inequality follows. In fact, we don’t even need all | f (i)|
small for this latter analysis; for large t it’s possible to upper-bound (5.17)
using only Hoeffding’s bound:

Copyright © Ryan O’Donnell, 2014, 2015, 2016, 2017, 2018, 2019, 2020, 2021.



<!-- pdf-page: 128 -->
128

5. Majority and threshold functions

Lemma 5.31. Let `(x) = a1x1 + · · · + an xn, where

= 1. Then for any s ≥ 1,

i a2
i
E[1{|`(x)|>s} · |`(x)|] ≤ (2s + 2) exp(− s2

2 ).



Proof. We have

∫∞

E[1{|`(x)|>s} · |`(x)|] = s Pr[|`(x)| > s] +
∫∞

≤ 2s exp(− s2

2 ) +

s

Pr[|`(x)| > u] du

s
2 exp(− u2

2 ) du,

using Hoeffding’s bound. But for s ≥ 1,

∫∞

s

∫∞

s

2 exp(− u2

2 ) du ≤

u · 2 exp(− u2

2 ) du = 2 exp(− s2
2 ).



We now give formal proofs of the two theorems, commenting that rather

than L(x) it’s more convenient to work with

`(x) = 1
σ

f =1(x) =

f (1)
σ

x1 + · · · +

f (n)
σ

xn.

Proof of the Level-1 Inequality. Following Remark 5.28 we let f : {−1, 1}n →
[−1, 1] and α = E[| f |]. We may assume σ =
have 〈 f , `〉 = 1
σ

W1[ f ] > 0. Writing ` = 1
σ

W1[ f ] = σ and hence

〈 f , f =1〉 = 1
σ

f =1 we



σ = 〈 f , `〉 = E[1{|`(x)|≤s} · f (x)`(x)] + E[1{|`(x)|>s} · f (x)`(x)]

holds for any s ≥ 1. The rst expectation above is at most E[s| f (x)|] = αs, and
the second is at most (2+2s) exp(−s2/2) ≤ 4s exp(−s2/2) by Lemma 5.31. Hence

σ ≤ αs + 4s exp(−s2/2).

The optimal choice of s is s = (

p

2 + oα(1))

ln(1/α), yielding

p

σ ≤ (

2 + o(1))α

ln(1/α).

p



Squaring this establishes the claim σ2 ≤ (2 + oα(1))α2 ln(1/α).



Theorem. We may assume σ =

Proof of the 2
W1[ f ] ≥ 1/2: for the theo-
π
rem’s rst statement this is because otherwise there is nothing to prove; for
the theorem’s second statement this is because we may assume ≤ sufciently
small.



We start by proving (5.16). Let ` = 1
σ

i ∈ [n]. We have

f =1, so ‖`‖2 = 1 and | `(i)| ≤ 2≤ for all



2
π

+ C≤

(5.19)

σ = 〈 f , `〉 ≤ E[|`|] ≤

for some constant C, where we used Theorem 5.16. Squaring this proves (5.16).
We observe that (5.16) therefore holds even for f : {−1, 1}n → [−1, 1].

Now suppose we also have W1[ f ] ≥ 2
π



− ≤; i.e.,


σ ≥

2
π

− ≤ ≥

2
π

− 2≤.

Copyright © Ryan O’Donnell, 2014, 2015, 2016, 2017, 2018, 2019, 2020, 2021.



<!-- pdf-page: 129 -->
5.4. Degree-1 weight

129

Thus the rst inequality in (5.19) must be close to tight; specically,

(C + 2)≤ ≥ E[|`|] − 〈 f , `〉 = E[(sgn(`(x)) − f (x)) · `(x)].

(5.20)

By the Berry–Esseen Theorem (and Remark 5.15, Exercise 5.16),

p

Pr[|`| ≤ K

≤] ≤ Pr[|N(0, 1)| ≤ K

p

≤] + .56 · 2≤ ≤ 1p
2π

· 2K

p

≤ + 1.12≤ ≤ 2K

p

≤

for any constant K ≥ 1. We therefore have the implication

Pr[ f 6= sgn(`)] ≥ 3K

p

≤ =⇒ Pr[ f (x) 6= sgn(`(x)) ∧ |`(x)| > K
p

=⇒ E[(sgn(`(x)) − f (x)) · `(x)] ≥ K

≤] ≥ K
p

≤ · 2(K

p

p

≤

This contradicts (5.20) for K =
completing the proof.

p

C + 2, say. Thus Pr[ f 6= sgn(`)] ≤ 3

C + 2

≤) = 2K 2≤.
p
p

≤,


For an interpolation between these two theorems, see Exercise 5.44.

We conclude this section with an application of the Level-1 Inequality.

First, a quick corollary which we leave for Exercise 5.37:

Corollary 5.32. Let f : {−1, 1}n → {−1, 1} have | E[ f ]| ≥ 1−δ ≥ 0. Then W1[ f ] ≤
4δ2 log(2/δ).

In Chapter 2.5 we stated the FKN Theorem, which says that if f : {−1, 1}n →
{−1, 1} has W1[ f ] ≥ 1 − δ then it must be O(δ)-close to a dictator or negated-
dictator. The following theorem shows that once the FKN Theorem is proved,
it can be strengthened to give an essentially optimal (Exercise 5.36) closeness
bound:

Theorem 5.33. Suppose the FKN Theorem holds with closeness bound Cδ,
where C ≥ 1 is a universal constant. Then in fact it holds with bound δ/4 + η,
where η = 16C2δ2 max(log(1/Cδ), 1).

Proof. Suppose f : {−1, 1}n → {−1, 1} has W1[ f ] ≥ 1 − δ ≥ 0. By assumption f
is Cδ-close to ±χi for some i ∈ [n], say i = n. Thus we have

| f (n)| ≥ 1 − 2Cδ

and our task is to show that in fact | f (n)| ≥ 1−δ/2−2η. We may assume δ ≤ 1
10C
as otherwise 1 − δ/2 − 2η < 0 (Exercise 5.38) and there is nothing to prove. By
employing the trick from Exercise 2.49 we may also assume E[ f ] = 0.

Consider the restriction of f given by xing coordinate n to b ∈ {−1, 1};
i.e., f[n−1]|b. For both choices of b we have | E[ f[n−1]|b]| ≥ 1 − 2Cδ and so Corol-
lary 5.32 implies W1[ f[n−1]|b] ≤ 16C2δ2 log(1/Cδ). Thus

16C2δ2 log(1/Cδ) ≥ E
b

[W1[ f[n−1]|b]] =

∑

j<n

( f ({ j})2 + f ({ j, n})2) ≥

∑

j<n

f ( j)2,

Copyright © Ryan O’Donnell, 2014, 2015, 2016, 2017, 2018, 2019, 2020, 2021.



<!-- pdf-page: 130 -->
130

5. Majority and threshold functions

by Corollary 3.22. It follows that
∑

f (n)2 = W1[ f ] −

f ( j)2 ≥ 1 − δ − 16C2δ2 log(1/Cδ),

and the proof is completed by the fact that

j<n

1 − δ − 16C2δ2 log(1/Cδ) ≥ (1 − δ/2 − 2η)2

when δ ≤ 1

10C (Exercise 5.38).



5.5. Highlight: Peres’s Theorem and uniform noise stability

Theorem 5.17 says that if f is an unbiased linear threshold function f (x) =
sgn(a1x1 + · · · + an xn) in which all ai’s are “small”, then the noise stability
Stabρ[ f ] is at least (roughly) 2
arcsin ρ. Rephrasing in terms of noise sen-
π
sitivity, this means NSδ[ f ] is at most (roughly) 2
δ + O(δ3/2) (see the state-
π
ment of Theorem 2.45). On the other hand, if some ai were particularly large
then f would be pushed in the direction of the dictator function χi, which has
δ. This observation suggests that all unbiased LTFs f should
NSδ[χi] = δ ø
have NSδ[ f ] ≤ O(
δ). The unbiasedness assumption also seems inessential,
since biasing a function should tend to decrease its noise sensitivity.

p

p

p

Indeed, the idea here is correct, as was shown by Peres in 1999:

Peres’s Theorem. Let f : {−1, 1}n → {−1, 1} be any linear threshold function.
Then NSδ[ f ] ≤ O(

δ).

p

Pleasantly, the proof is quite simple and uses no heavy tools like the
Central Limit Theorem. Before getting to it, let’s make some remarks. First,
Peres’s Theorem shows that the class of all linear threshold functions is what’s
called uniformly noise-stable.

Denition 5.34. Let B be a class of Boolean-valued functions. We say that
B is uniformly noise-stable if there exists ≤ : [0, 1/2] → [0, 1] with ≤(δ) → 0 as
δ → 0+ such that NSδ[ f ] ≤ ≤(δ) holds for all f ∈ B.

This denition is only interesting for innite classes B. (Any class con-
taining functions of only nitely many input lengths is vacuously uniformly
noise-stable; see Exercise 5.34.) By Proposition 5.6 we see that functions
in a uniformly noise-stable class have “almost all of their Fourier weight at
such that W>k[ f ] ≤ ≤ for
constant degree”; i.e., for all ≤ > 0 there is a k ∈
all f ∈ B. In particular, from Corollary 3.34 we get that if B is a uniformly
noise-stable class then its restriction to n-input functions is learnable from
random examples to any constant error in poly(n) time.

Let’s make these observations more concrete in the context of linear
threshold functions. Peres’s Theorem immediately gives that LTFs have their
Fourier spectrum ≤-concentrated up to degree O(1/≤2) (Proposition 3.3) and

Copyright © Ryan O’Donnell, 2014, 2015, 2016, 2017, 2018, 2019, 2020, 2021.



<!-- pdf-page: 131 -->
5.5. Highlight: Peres’s Theorem and uniform noise stability

131

hence the class of LTFs is learnable from random examples with error ≤ in
time nO(1/≤2) (Corollary 3.34). The latter result is not too impressive since
it’s been long known that LTFs are learnable in time poly(n, 1/≤) using linear
programming. However, the noise sensitivity approach is much more exible.
Consider the concept class

C = {h = g( f1, . . . , f s) | f1, . . . , f s : {−1, 1}n → {−1, 1} are LTFs}.

For each h : {−1, 1}n → {−1, 1} in C , Peres’s Theorem and a union bound (Ex-
p
ercise 2.44) imply that NSδ[h] ≤ O(s
δ). Thus from Corollary 3.34 we get
that the class C is learnable in time nO(s2/≤2). This is the only known way of
showing even that an AND of two LTFs is learnable with error .01 in time
poly(n).

The trick for proving Peres’s Theorem is to employ a fairly general tech-
nique for bounding noise sensitivity using average sensitivity (total inuence):

+ → . Let B be a class of Boolean-
Theorem 5.35. Let δ ∈ (0, 1/2] and let A :
valued functions closed under negation and identication of input variables.
Suppose that each f ∈ B with domain {−1, 1}n has I[ f ] ≤ A(n). Then each
f ∈ B has NSδ[ f ] ≤ 1

m A(m), where m = b1/δc.

Proof. Fix any f : {−1, 1}n → {−1, 1} from B. Since noise sensitivity is an
increasing function of the noise parameter (see the discussion surround-
ing Proposition 2.51) we may replace δ by 1/m. Thus our task is to upper-
bound NS1/m[ f ] = Pr[ f (x) 6= f (y)] where x ∼ {−1, 1}n is uniformly random and
y ∈ {−1, 1}n is formed from x by negating each bit independently with proba-
bility 1/m. The rough idea of the proof is that this is equivalent to randomly
partitioning x’s bits into m parts and then negating a randomly chosen part.
More precisely, let z ∈ {−1, 1}n and let π : [n] → [m] be a partition of [n]

into m parts. Dene

g z,π : {−1, 1}m → {−1, 1},

g z,π(w) = f (z ◦ wπ),

where ◦ denotes entry-wise multiplication and wπ = (wπ(1), . . . , wπ(n)) ∈ {−1, 1}n.
Since g z,π is derived from f by negating and identifying input variables it
follows that g z,π ∈ B. So by assumption g z,π has total inuence I[g z,π] ≤ A(m)
and hence average inuence EEE [g z,π] ≤ 1

m A(m) (see Exercise 2.43(a)).

Now suppose z ∼ {−1, 1}n and π : [n] → [m] are chosen uniformly at ran-

dom. We certainly have

[EEE [g z,π]] ≤ 1

m A(m).

E
z,π

To complete the proof we will show that the left-hand side above is precisely
NS1/m[ f ]. Recall that in the experiment for average inuence EEE [g] we choose

Copyright © Ryan O’Donnell, 2014, 2015, 2016, 2017, 2018, 2019, 2020, 2021.



<!-- pdf-page: 132 -->
132

5. Majority and threshold functions

w ∼ {−1, 1}m and j ∼ [m] uniformly at random and check if g(w) 6= g(w⊕ j).
Thus

E
z,π

[EEE [g z,π]] = Pr

z,π,w, j

[g z,π(w) 6= g z,π(w⊕ j)] = Pr

w,π, j,z

[ f (z ◦ wπ) 6= f (z ◦ (w⊕ j)π)].

It is not hard to see that the joint distribution of z ◦ wπ, z ◦ (w⊕ j)π is the same
as that of x, y. To be precise, dene J = π−1( j), distributed as a random
subset of [n] in which each coordinate is included with probability 1/m, and
dene λ ∈ {−1, 1}n by λi = −1 if and only if i ∈ J. Then
[ f (z ◦ wπ) 6= f (z ◦ (w⊕ j)π)] = Pr

[ f (z ◦ wπ) 6= f (z ◦ wπ ◦ λ)].

Pr
w,π, j,z

w,π, j,z

But for every outcome of w, π, j (and hence J, λ), we may replace z with
z ◦ wπ since they have the same distribution, namely uniform on {−1, 1}n.
Then the above becomes

Pr
w,π, j,z

[ f (z) 6= f (z ◦ λ)] = NS1/m[ f ],

as claimed.



Peres’s Theorem is now a simple corollary of Theorem 5.35.

Proof of Peres’s Theorem. Let B be the class of all linear threshold func-
tions. This class is indeed closed under negating and identifying variables.
Since each linear threshold function on m bits is unate (i.e., monotone up to
negation of some input coordinates, see Exercises 2.5, 2.6), its total inuence
is at most
m (see Exercise 2.23). Applying Theorem 5.35 we get that for any
LTF f and any δ ∈ (0, 1/2],

p

NSδ[ f ] ≤ 1
m

p

m = 1/

p

m

p

δ).

≤ O(

(for m = b1/δc)



p

p

3/2

Remark 5.36. Our proof of Peres’s Theorem attains the upper bound
1/b1/δc.
δ + O(δ3/2) for small δ.
This is at most
To further improve the constant we can use Theorem 2.33 in place of Exer-
cise 2.23; it implies that all unate m-bit functions have total inuence at most
p
δ + O(δ3/2)

m + O(m−1/2). This lets us obtain the bound NSδ[ f ] ≤

δ for all δ ∈ (0, 1/2] and it’s also

2/π

2/π

p

p

p

p



for all LTF f .

p

p

Recall from Theorem 2.45 that NSδ[Majn] ∼ 2
π

δ for large n. Thus the
2/π in the bound from Remark 5.36 is fairly close to optimal. It
constant
seems quite likely that majority’s 2
is the correct constant here. There is
π
still slack in Peres’s proof because the random functions g z,π arising in Theo-
rem 5.35 are unlikely to be majorities, even if f is. The most elegant possible
result in this direction would be to prove the following conjecture of Benjamini,
Kalai, and Schramm:

Copyright © Ryan O’Donnell, 2014, 2015, 2016, 2017, 2018, 2019, 2020, 2021.



<!-- pdf-page: 133 -->
5.5. Highlight: Peres’s Theorem and uniform noise stability

133

Majority Is Least Stable Conjecture. Let f : {−1, 1}n → {−1, 1} be a linear
threshold function, n odd. Then for all ρ ∈ [0, 1], Stabρ[ f ] ≥ Stabρ[Majn].

(This is a precise statement about majority’s noise stability within the class
of LTFs; the Majority Is Stablest Theorem refers to its noise stability within
the class of small-inuence functions.) However, Sivakanth Gopi and others
found a counterexample to the above conjecture, already for n = 5. A plausible
replacement would be to conjecture that Stabρ[ f ] ≥ 2
arcsin ρ for all linear
π
threshold functions f .

A challenging problem in this area is to extend Peres’s Theorem to poly-

nomial threshold functions. Let

P n,k = { f : {−1, 1}n → {−1, 1} | f is a PTF of degree at most k}, P k =

⋃

n

P n,k.

Peres’s Theorem shows that the class P 1 (i.e., LTFs) is uniformly noise-stable.
Is the same true of P 2? What about P 100? More quantitatively, what upper
bound can we prove on NSδ[ f ] for f ∈ P k? Since P k is closed under negating
and identifying variables, a natural approach to bounding the noise sensitivity
of PTFs is to again use Theorem 5.35. For example, if we could show that
I[ f ] = o(n) for all f ∈ P k we could conclude that NSδ[ f ] = oδ(1) for all f ∈ P k;
i.e., that P k is uniformly noise-stable. (In fact, the total inuence approach
to bounding noise sensitivity is not just sufcient but is also necessary; see
n for
Exercise 5.40.) More ambitiously, if we could show that I[ f ] ≤ Ok(1)
all f ∈ P n,k then it would follow that NSδ[ f ] ≤ Ok(1)
δ for all f ∈ P k, strictly
generalizing Peres’s Theorem. In fact, a conjecture of Gotsman and Linial
dating back to 1990 proposes an even more rened bound:

p

p

n. More
Gotsman–Linial Conjecture. Let f ∈ P n,k. Then I[ f ] ≤ Ok(1)
strongly, I[ f ] ≤ O(k)
n. Most strongly, the f ∈ P n,k of maximal total inuence
is the symmetric one f (x) = sgn(p(x1+· · ·+xn)), where p is a degree-k univariate
polynomial which alternates sign on the k + 1 values of x1 + · · · + xn closest to 0.

p

p

The strongest form of the Gotsman–Linial Conjecture is true when k = 1,
by Theorem 2.33. However, even for k = 2 there was no progress on the con-
jecture for close to 20 years. At that point two independent works [DHK+10,
HKM10] showed that every f ∈ P n,k satises both I[ f ] ≤ O(n1−1/2k ) and
I[ f ] ≤ 2O(k)n1−1/O(k). The former (essentially weaker) bound has the advan-
tage of an elementary proof; see Exercise 5.45. It also sufces to show that P k,
the class of degree-k PTFs, is indeed uniformly noise-stable. This gives a nice
kind of converse to Proposition 5.6, which showed that every function in a
uniformly noise-stable class is close to being a constant-degree PTF.

The latest progress on the Gotsman–Linial Conjecture is the following

theorem of Kane [Kan12], which comes quite close to proving it:

Copyright © Ryan O’Donnell, 2014, 2015, 2016, 2017, 2018, 2019, 2020, 2021.



<!-- pdf-page: 134 -->
134

5. Majority and threshold functions

Theorem 5.37. Every f ∈ P n,k satises I[ f ] ≤
(via Theorem 5.35) that for a xed k ∈
p

n · (2k log n)O(k log k). It follows
+, every f ∈ P k satises NSδ[ f ] ≤

p

δ · polylog(1/δ).

5.6. Exercises and notes

5.1 (a) Suppose f : {−1, 1}n → {−1, 1} is an LTF. Show that it can be expressed
as f (x) = sgn(a0 + a1x1 + · · · an xn) where the ai’s are integers. (Hint:
First obtain rational ai’s by a perturbation.)

(b) Show also that a degree-d PTF has a representation in which all of

the degree-d polynomial’s coefcients are integers.

5.2 Let f (x) = sgn(a0 + a1x1 + · · · an xn) be an LTF.

(a) Show that if a0 = 0, then E[ f ] = 0. (Hint: Show that f is in fact an

odd function.)

(b) Show that if a0 ≥ 0, then E[ f ] ≥ 0. Show that the converse need not

hold.

(c) Suppose g : {−1, 1}n → {−1, 1} is an LTF with E[g] = 0. Show that g

can be represented as g(x) = sgn(c1x1 + · · · + cn xn).

5.3 Suppose f (x) = sgn(a0 + a1x1 + · · · an xn) is an LTF with |a1| ≥ |a2| ≥ · · · ≥
|an|. Show that Inf1[ f ] ≥ Inf2[ f ] ≥ · · · ≥ Infn[ f ]. (Hint: Why does it sufce
to prove this for n = 2?)

5.4 (a) Show that the number of functions f : {−1, 1}n → {−1, 1} that are LTFs

is at most 2n2+O(n). (Hint: Chow’s Theorem.)

(b) More generally, show that the number of functions f : {−1, 1}n →

{−1, 1} that are degree-k PTFs is at most 2nk+1+O(n).

5.5 (a) Suppose ` : {−1, 1}n → is dened by `(x) = a0 + a1x1 + · · · + an xn.
Dene ` : {−1, 1}n+1 → by `(x0, . . . , xn) = a0x0 + a1x1 + · · · an xn. Show
that ‖ `‖1 = ‖`‖1 and ‖ `‖2

2 = ‖`‖2
2.

(b) Complete the proof of Theorem 5.2.

5.6 Let f : {−1, 1}n → {−1, 1} be an unbiased linear threshold function. Show
for some i ∈ [n], improving the KKL Theorem for LTFs.

that Infi[ f ] ≥ 1p
2n

5.7 Consider the following “correlation distillation” problem (cf. Exercise 2.56).
For each i ∈ [n] there is a number ρ i ∈ [−1, 1] and an independent se-
quence of pairs of ρ i-correlated bits, (a(1)
), etc.
i
Party A on Earth has access to the stream of n-bit strings a(1), a(2),
a(3), . . . and a party B on Venus has access to the stream b(1), b(2), b(3), . . . .
Neither party knows the numbers ρ1, . . . , ρn. The goal is for B to estimate
these correlations. To assist in this, A can send a small number of bits
to B. A reasonable strategy is for A to send f (a(1)), f (a(2)), f (a(3)), . . . to B,
where f : {−1, 1}n → {−1, 1} is some Boolean function. Using this informa-
tion B can try to estimate E[ f (a)bi] for each i.

), (a(2)

), (a(3)

, b(1)
i

, b(2)
i

, b(3)
i

i

i

Copyright © Ryan O’Donnell, 2014, 2015, 2016, 2017, 2018, 2019, 2020, 2021.



<!-- pdf-page: 135 -->
5.6. Exercises and notes

135

(a) Show that E[ f (a)bi] = f (i)ρ i.
(b) This motivates choosing an f for which all f (i) are large. If we also
insist all f (i) be equal, show that majority functions f maximize this
common value.

5.8 For n ≥ 2, let f : {−1, 1}n → {−1, 1} be a randomly chosen function (as in
n2−n/2 except with probability at

p

Exercise 1.7). Show that ˆ‖ f ˆ‖∞ ≤ 2
most 2−n.

5.9 Prove Theorem 5.8.

5.10 (a) Give as simple a proof as you can that the parity function χ[n] : {−1, 1}n →

{−1, 1} is not a PTF of degree n − 1.

(b) Show that if f : {−1, 1}n → {−1, 1} is not ±χ[n], then it is a PTF of

degree n − 1. (Hint: Consider f ≤n−1.)

5.11 For each k ∈ +, show that there is a degree-k PTF f with W≤k[ f ] < 21−k.

5.12 In this exercise you will show that threshold-of-parities circuits can be
effectively simulated by threshold-of-threshold circuits, but not the con-
verse.
(a) Let f : {−1, 1}n → {−1, 1} be a symmetric function. Show that f is

computable as the sum of at most 2n LTFs, plus a constant.

(b) Deduce that if f : {−1, 1}n → {−1, 1} is computable by a size-s threshold-
of-parities circuit, then it is also computable by a size-2ns threshold-
of-thresholds circuit.

(c) Show that the complete quadratic function CQn :

n
2 → {−1, 1} (see Ex-
ercise 1.1) is computable by a size-2n threshold-of-thresholds circuit.
(d) Assume n even. Show that any threshold-of-parities circuit for CQn

requires size 2n/2.

5.13 Let f : {−1, 1}n → {−1, 1} be computable by a DNF of size s. Show that
f has a PTF representation of sparsity O(ns3). (Hint: Approximate the
ANDs using Theorem 5.12.) Can you improve this bound to O(ns2)?

5.14 In contrast to the previous exercise, show that there is a function f :
{−1, 1}n → {−1, 1} computable by a depth-3 AC0 circuit (see Chapter 4.5)
but requiring threshold-of-parities circuits of size at least nlog n. (Hint:
Involve the inner product mod 2 function and Exercise 4.12.)

5.15 Let F be a nonempty collection of subsets S ⊆ [n]. For each a ∈ {−1, 1}n,



S∈F

write 1{a} : {−1, 1}n → {0, 1} for the indicator of {a}, write 1F
{a}
̂1{a}(S) χS, and write ψa = 2n
for
(a) Show that ψa(a) = 1 and E[ψ2
{−1, 1}n, ψa(x) = ψx(a) and

|F | · 1F
{a}
a] = 1
|F | . Show also that for all x ∈

a:a6=x ψa(x)2 = 2n

: {−1, 1}n →



.

|F | − 1.

Copyright © Ryan O’Donnell, 2014, 2015, 2016, 2017, 2018, 2019, 2020, 2021.



<!-- pdf-page: 136 -->
136

5. Majority and threshold functions

(b) Fix 0 < ≤ < 1 and suppose |F | ≥ (1 − ≤2

6n )2n. Let f : {−1, 1}n → {−1, 1} be
a random function as in Exercise 1.7. Show that for each x ∈ {−1, 1}n,
except with probability at most 4−n we have |

a:a6=x f (a)ψa(x)| < ≤.



(c) Deduce that for all but a 2−n fraction of functions f : {−1, 1}n → {−1, 1},
there a multilinear polynomial q : {−1, 1}n → supported on the mono-
mials {χS : S ∈ F } such that ‖ f − q‖∞ < ≤.

(d) Deduce that all but a 2−n fraction of functions f : {−1, 1}n → {−1, 1}



have PTF representation of degree at most n/2 + O(

n log n).

5.16 (a) Show that in the Berry–Esseen Theorem we can also conclude

| Pr[S < u] − Pr[Z < u]| ≤ cγ.

(Hint: You’ll need that limδ→0+ Pr[Z ≤ u − δ] = Pr[Z ≤ u].)
(b) Deduce that if I ⊆ is any interval, we can also conclude

| Pr[S ∈ I] − Pr[Z ∈ I]| ≤ 2cγ.

5.17 Show that the assumptions E[X i] = 0 and

i=1 Var[X i] = 1 in the Berry–
Esseen Theorem are not restrictive, as follows. Let X 1, . . . , X n be indepen-
dent random variables with nite means and variances. Let S =
i=1 X i
n
and let Z ∼ N(µ, σ2), where µ =
i=1 Var[X i]. Assum-
ing σ2 > 0, show that for all u ∈ ,

i=1 E[X i] and σ2 =

n

n

n

where

| Pr[S ≤ u] − Pr[Z ≤ u]| ≤ c≤/σ3,

≤ =

n∑

i=1

‖X i − E[X i]‖3
3.

5.18 (a) Use the generalized Binomial Theorem to compute the power series

for (1 − z2)−1/2, valid for |z| < 1.

(b) Integrate to obtain the power series for arcsin z given in (5.9), valid

for |z| < 1.

(c) Conrm that equality holds also for z = ±1.

5.19 Verify that the random vector ~S dened in (5.7) has E[~S1] = E[~S2] = 0,
~S2] = ρ; i.e., E[~S] =

and Cov[~S] =

2] = 1, E[~S1

1] = E[~S

E[~S

[

[

]

]

2

2

.

1 ρ
ρ 1

0
0

5.20 Prove Corollary 5.20.
5.21 Fix n odd. Using Theorem 5.19 show that |ÉMajn(S)| is a decreasing func-
2 . Deduce (using also Corollary 5.20) that

tion of |S| for odd 1 ≤ |S| ≤ n−1
ˆ‖∞ = Majn({1}) ∼
ˆ‖Majn
5.22 Prove Corollary 5.21.

p
2/πp
n

.

5.23 Prove Theorem 5.18. (Hint: Corollary 5.21.)
5.24 Complete the proof of Theorem 5.22 by showing that (1 − k+1

n + k

n2 )−1/2 ≤

1 + 2k/n for all 1 ≤ k ≤ n/2.

Copyright © Ryan O’Donnell, 2014, 2015, 2016, 2017, 2018, 2019, 2020, 2021.



<!-- pdf-page: 137 -->
5.6. Exercises and notes

137

5.25 Using just the facts that Stabρ[Majn] → 2
π

arcsin ρ for all ρ ∈ [−1, 1] and
k≥0 Wk[Majn]ρk, deduce that limn→∞ Wk[Majn] →
arcsin ρ) for all k ∈ . (Hint: By induction on k, always taking ρ



that Stabρ[Majn] =
[ρk]( 2
π
“small enough”.)

5.26 (a) For 0 ≤ j ≤ m integers, show that ˆ‖Maj=2 j+1
2m+1






(b) Deduce ˆ‖Maj2m+1
(c) Deduce ˆ‖Majn

ˆ‖1 = E
1p
n

ˆ‖1 ∼ 2p
π

1
2X +1
2n/2.



m
j

1

ˆ‖1 =

2 j+1 · 2m+1
22m
, where X ∼ Binomial(m, 1/2).

.



2m
m

· 2m+1
2m

2m
m

5.27 (a) Show that for each odd k ∈ ,

3/2



2
π

k−3/2 ≤ [ρk]( 2
π

arcsin ρ) ≤

3/2



2
π

k−3/2(1 + O(1/k)).

(Hint: Stirling’s approximation.)

(b) Prove Corollary 5.23. (Hint: For the second statement you’ll need to
2
π

j−3/2 by an integral.)

approximate the sum

odd j>k

3/2





n

5.28 For integer 0 ≤ j ≤ n, dene K j : {−1, 1}n → by K j(x) =

i=1 xi. Thus we may dene K j : {0, 1, . . . , n} →

|S|= j xS. Since
K j is symmetric, the value K j(x) depends only on the number z of −1’s
in x; or equivalently, on
by K j(z) = K j(x) for any x with
(a) Show that K j(z) can be expressed as a degree- j polynomial in z. It
is called the Kravchuk (or Krawtchouk) polynomial of degree j. (The
dependence on n is usually implicit.)
j=0 K j(x) = 2n · 1(1,...,1)(x).
n

i xi = n − 2z.

(b) Show that

j=0 K j(x)ρ j = 2n Pr[y = (1, . . . , 1)], where y =

(c) Show for ρ ∈ [−1, 1] that

n





Nρ(x).

(d) Deduce the generating function identity K j(z) = [ρ j]((1−ρ)z(1+ρ)n−z).

5.29 Prove Proposition 5.24.
5.30 Prove Proposition 5.25 using the Central Limit Theorem. (Hint for W1[ f n]:

use symmetry to show it equals the square of E[ f n(x)

 1p



xi].)
i ai xi where x ∼ {−1, 1}n,

n

5.31 Consider the setting of Theorem 5.16. Let S =

and let Z ∼ N(0, 1).
(a) Show that Pr[|S| ≥ t], Pr[|Z| ≥ t] ≤ 2 exp(−t2/2) for all t ≥ 0.
(b) Recalling E[|Y |] =

∞
0 Pr[|Y | ≥ t] dt for any random variable Y , use
the Berry–Esseen Theorem (and Remark 5.15, Exercise 5.16) to show

∣
∣
∣E[|S|] − E[|Z|]

∣
∣
∣ ≤ O(≤T + exp(−T2/2))

for any T ≥ 1.
(c) Deduce | E[|S|] −
(d) Improve O(≤



p

2/π| ≤ O(≤



log(1/≤)).

log(1/≤)) to the bound O(≤) stated in Theorem 5.16 by
using the nonuniform Berry–Esseen Theorem, which states that the
bound cγ in the Berry–Esseen Theorem can be improved to Cγ ·
for some constant C.

1
1+|u|3

Copyright © Ryan O’Donnell, 2014, 2015, 2016, 2017, 2018, 2019, 2020, 2021.



<!-- pdf-page: 138 -->
138

5. Majority and threshold functions

5.32 Consider the sequence of LTFs dened in Proposition 5.25. Show that

lim
n→∞

Stabρ[ f n] = Λρ(µ).

Here µ = Φ(t) and Λρ(µ) is the Gaussian quadrant probability dened
by Λρ(µ) = Pr[z1 > t, z2 > t], where z1, z2 are standard Gaussians with
correlation E[z1 z2] = ρ. Verify also that Λρ(α) = Pr[z1 ≤ t, z2 ≤ t] where
α = Φ(t).

5.33 In this exercise you will complete the justication of Theorem 5.17 using

the following multidimensional Berry-Esseen Theorem:

d-valued random vectors,
Theorem 5.38. Let X 1, . . . , X n be independent
i=1 X i and assume Σ = Cov[S] is
each having mean zero. Write S =
invertible. Let Z ∼ N(0, Σ) be a d-dimensional Gaussian with the same
mean and covariance matrix as S. Then for all convex sets U ⊆ d,

n

| Pr[S ∈ U] − Pr[Z ∈ U]| ≤ Cd1/4γ,

where C is a universal constant, γ =
the Euclidean norm on d.

n

i=1 E[‖Σ−1/2 X i‖3

2], and ‖ · ‖2 denotes

(a) Let Σ =

]

[

1 ρ
ρ 1

where ρ ∈ (−1, 1). Show that

Σ−1 =

[

1 −ρ
1
0

] [

0

1
0 (1 − ρ2)−1

] [

1
0
−ρ 1

]

.

(b) Compute yΣ−1 y for y =

]

[

±a
±a

∈ 2.

(c) Complete the proof of Theorem 5.17.

5.34 Let B be a class of Boolean-valued functions, all of input length at most n.
Show that NSδ[ f ] ≤ nδ for all f ∈ B and hence B is uniformly noise-stable
(in a sense, vacuously). (Hint: Exercise 2.42.)

5.35 Give a simple proof of the following fact, which is a robust form of the
edge-isoperimetric inequality (for volume 1/2) and a weak form of the
FKN Theorem: If f : {−1, 1}n → {−1, 1} has E[ f ] = 0 and I[ f ] ≤ 1+ δ, then f
is O(δ)-close to ±χi for some i ∈ [n]. In fact, you should be able to achieve
δ-closeness (which can be further improved using Theorem 5.33). (Hint:
i | f (i)|) using Proposi-
Upper- and lower-bound
i
tion 3.2 and Exercise 2.5(a).)

f (i)2 ≤ (maxi | f (i)|)(





5.36 Show that Theorem 5.33 is essentially optimal by exhibiting functions
f : {−1, 1}n → {−1, 1} with f (1) = 1 − δ/2 and W1[ f ] ≥ 1 − δ + Ω(δ2 log(1/δ)),
for a sequence of δ tending to 0.

5.37 Prove Corollary 5.32.

5.38 Fill in the details of the proof of Theorem 5.33.

Copyright © Ryan O’Donnell, 2014, 2015, 2016, 2017, 2018, 2019, 2020, 2021.



<!-- pdf-page: 139 -->
5.6. Exercises and notes

139

5.39 Show that if f : {−1, 1}n → {−1, 1} is an LTF, then d
dδ

δ).
(Hint: The only fact needed about LTFs is the corollary of Peres’s Theorem
that W≥k[ f ] ≤ O(1/

NSδ[ f ] ≤ O(1/

k) for all k.)

p

p

5.40 As discussed in Section 5.5, Theorem 5.35 implies that an upper bound on
the total inuence of degree-k PTFs is sufcient to derive an upper bound
on their noise sensitivity. This exercise asks you to show necessity as well.
More precisely, suppose NSδ[ f ] ≤ ≤(δ) for all f ∈ P k. Show that I[ f ] ≤
O(≤(1/n) · n) for all f ∈ P n,k. Deduce that P k is uniformly noise-stable if
δ) for all f ∈
and only if I[ f ] = o(n) for all f ∈ P n,k and that NSδ[ f ] ≤ O(k
n) for all f ∈ P n,k. (Hint: Exercise 2.43(a).)
P k if and only if I[ f ] ≤ O(k
5.41 Estimate carefully the asymptotics of I[ f ], where f ∈ PTFn,k is as in the

p

p

strongest form of the Gotsman–Linial Conjecture.

5.42 Let A ⊆ {−1, 1}n have cardinality α2n, α ≤ 1/2. Thinking of {−1, 1}n ⊂ n,
let µA ∈ n be the center of mass of A. Show that µA is close to the origin
in Euclidean distance: ‖µA‖2 ≤ O(

log(1/α)).



5.43 Show that the Gaussian isoperimetric function satises U ′′ = −1/U on

(0, 1). Deduce that U is concave.

5.44 Fix α ∈ (0, 1/2). Let f : {−1, 1}n → [−1, 1] satisfy E[| f |] ≤ α and | f (i)| ≤ ≤
for all i ∈ [n]. Show that W1[ f ] ≤ U (α)2 + C≤, where U is the Gaussian
isoperimetric function and where the constant C may depend on α. (Hint:
You will need the nonuniform Berry–Esseen Theorem from Exercise 5.31.)
5.45 In this exercise you will show by induction on k that Inf[ f ] ≤ 2n1−1/2k for
all degree-k PTFs f : {−1, 1}n → {−1, 1}. The k = 0 case is trivial. So for
k > 0, suppose f = sgn(p) where p : {−1, 1}n → is a degree-k polynomial
that is never 0.
(a) Show for i ∈ [n] that E[ f (x)xisgn(Di p(x))] = Infi[ f ]. (Hint: First use
the decomposition f = xiDi f + Ei f to reach E[Di f · sgn(Di p)]; then
show that Di f = sgn(Di p) whenever Di f 6= 0.)



(b) Conclude that I[ f ] ≤ E[|

i xisgn(Di p(x))|]. Remark: When k = 2 and
thus each sgn(Di p) is an LTF, it is conjectured that this bound is
still O(

n).

p

(c) Apply Cauchy–Schwarz and deduce



I[ f ] ≤

n +

∑

i6= j

E[xi x jsgn(Di p(x))sgn(D j p(x))].

(d) Use Exercise 2.19 and the AM-GM inequality to obtain



I[ f ] ≤

n +

∑

i

I[sgn(Di p)].

(e) Complete the induction.

Copyright © Ryan O’Donnell, 2014, 2015, 2016, 2017, 2018, 2019, 2020, 2021.



<!-- pdf-page: 140 -->
140

5. Majority and threshold functions

(f ) Finally, deduce that the class of degree-k PTFs is uniformly noise-
stable, specically, that every degree-k PTF f satises NSδ[ f ] ≤ 3δ1/2k
for all δ ∈ (0, 1/2]. (Hint: Theorem 5.35.)

Notes. Chow’s Theorem was proved by independently by Chow [Cho61] and
by Tannenbaum [Tan61] in 1961; see also Elgot [Elg61]. The generaliza-
tion to PTFs (Theorem 5.8) is due to Bruck [Bru90], as is Theorem 5.10 and
Exercise 5.12. Theorems 5.2 and 5.9 are from Gotsman and Linial [GL94]
and may be called the Gotsman–Linial Theorems; this work also contains the
Gotsman–Linial Conjecture and Exercise 5.11. Conjecture 5.3 should be con-
sidered folklore. Corollary 5.13 was proved by Bruck and Smolensky [BS92];
they also essentially proved Theorem 5.12 (but see [SB91]). Exercise 5.13
is usually credited to Krause and Pudlák [KP97]. The upper bound in Exer-
cise 5.4 is asymptotically sharp [Zue89]. Exercise 5.15 is from O’Donnell and
Servedio [OS08].

Theorem 2.33 and Proposition 2.58, discussed in Section 5.2, were essen-
tially proved by Titsworth in 1962 [Tit62]; see also [Tit63]. More precisely,
Titsworth solved a version of the problem from Exercise 5.7. His motivation
was in fact the construction of “interplanetary ranging systems” for measuring
deep space distances, e.g., the distance from Earth to Venus. The connection
between ranging systems and Boolean functions was suggested by his advisor,
Solomon Golomb. Titsworth [Tit62] was also the rst to compute the Fourier
expansion of Majn. His approach involved generating functions and contour
integration. Other approaches have used special properties of binomial co-
efcients [Bra87] or of Kravchuk polynomials [Kal02]. The asymptotics of
Wk[Majn] described in Section 5.3 may have rst appeared in Kalai [Kal02],
with the error bounds being from O’Donnell [O’D03]. Kravchuk polynomials
were introduced by Kravchuk [Kra29].

The Berry–Esseen Theorem is due independently to Berry [Ber41] and
Esseen [Ess42]. Shevtsova [She13] has the record for the smallest known con-
stant B that works therein: roughly .5514. The nonuniform version described
in Exercise 5.31 is due to Bikelis [Bik66]. The multidimensional version
Theorem 5.38 stated in Exercise 5.33 is due to Bentkus [Ben04]. Sheppard
proved his formula in 1899 [She99]. The results of Theorem 5.18 may have
appeared rst in O’Donnell [O’D04, O’D03].

The Level-1 Inequality should probably be considered folklore; it was per-
haps rst published in Talagrand [Tal96] and we have followed his proof.
The rst half of the 2
Theorem is from Khot et al. [KKMO07]; the second
π
half is from Matulef et al. [MORS10]. Theorem 5.33, which improves the
FKN Theorem to achieve “closeness” δ/4, was independently obtained by Jen-
drej, Oleszkiewicz, and Wojtaszczyk [JOW12], as was Exercise 5.36 showing
optimality of this closeness. The closeness achieved in the original proof of

Copyright © Ryan O’Donnell, 2014, 2015, 2016, 2017, 2018, 2019, 2020, 2021.



<!-- pdf-page: 141 -->
5.6. Exercises and notes

141

the FKN Theorem [FKN02] was δ/2; that proof (like ours) relies on having
a separate proof of closeness O(δ). Kindler and Safra [KS02, Kin02] gave
a self-contained proof of the δ/2 bound relying only on the Hoeffding bound.
The content of Exercise 5.35 was communicated to the author by Eric Blais.
The result of Exercise 5.44 is from [KKMO07]; Exercise 5.42 was suggested
by Rocco Servedio.

Peres’s Theorem was published in 2004 [Per04] but was mentioned as
early as 1999 by Benjamini, Kalai, and Schramm [BKS99]. The work [BKS99]
introduced the denition of uniform noise stability and showed that the class
of all LTFs satises it; however, their upper bound on the noise sensitivity
of LTFs was O(δ1/4), worse than Peres’s. The proof of Peres’s Theorem that
we presented is a simplication due to Parikshit Gopalan and incorporates
an idea of Diakonikolas et al. [DHK+10, HKM10]. Regarding the total in-
uence of PTFs, the work of Kane [Kan12] shows that every degree-k PTF
on n variables has I[ f ] ≤ poly(k)n1−1/O(k), which is better than Theorem 5.37
for certain superconstant values of k. Exercise 5.39 was suggested by Nitin
Saurabh.

Copyright © Ryan O’Donnell, 2014, 2015, 2016, 2017, 2018, 2019, 2020, 2021.



<!-- pdf-page: 142 -->


<!-- pdf-page: 143 -->
Chapter 6

Pseudorandomness and

2-polynomials

In this chapter we discuss various notions of pseudorandomness for Boolean
functions; by this we mean properties of a xed Boolean function that are
in some way characteristic of randomly chosen functions. We will see some
deterministic constructions of pseudorandom probability density functions
with small support; these have algorithmic application in the eld of deran-
domization. Finally, several of the results in the chapter will involve interplay
between the representation of f : {0, 1}n → {0, 1} as a polynomial over the reals
and its representation as a polynomial over

2.

6.1. Notions of pseudorandomness

The most obvious spectral property of a truly random function f : {−1, 1}n →
{−1, 1} is that all of its Fourier coefcients are very small (as we saw in Exer-
cise 5.8). Let’s switch notation to f : {−1, 1}n → {0, 1}; in this case f (;) will not
be very small but rather very close to 1/2. Generalizing:

Proposition 6.1. Let n > 1 and let f : {−1, 1}n → {0, 1} be a p-biased random
function; i.e., each f (x) is 1 with probability p and 0 with probability 1 − p,
independently for all x ∈ {−1, 1}n. Then except with probability at most 2−n, all
of the following hold:

|f (;) − p| ≤ 2

p

n2−n/2,

∀S 6= ; |f (S)| ≤ 2

p

n2−n/2.

Proof. We have f (S) =
independent. If S = ;, then the coefcients 1

2n xS f (x), where the random variables f (x) are
2n xS sum to 1 and the mean

1

x



Copyright © Ryan O’Donnell, 2014, 2015, 2016, 2017, 2018, 2019, 2020, 2021.

143



<!-- pdf-page: 144 -->
144

6. Pseudorandomness and 2-polynomials

of f (S) is p; otherwise the coefcients sum to 0 and the mean of f (S) is 0.
Either way we may apply the Hoeffding bound to conclude that

Pr[|f (S) − E[f (S)]| ≥ t] ≤ 2 exp(−t2 · 2n−1)

for any t > 0. Selecting t = 2
The result follows by taking a union bound over all S ⊆ [n].

n2−n/2, the above bound is 2 exp(−2n) ≤ 4−n.


p

This proposition motivates the following basic notion of “pseudorandom-

ness”:

Denition 6.2. A function f : {−1, 1}n → is ≤-regular (sometimes called
≤-uniform) if | f (S)| ≤ ≤ for all S 6= ;.

Remark 6.3. By Exercise 3.9, every function f is ≤-regular for ≤ = ‖ f ‖1. We
are often concerned with f : {−1, 1}n → [−1, 1], in which case we focus on ≤ ≤ 1.

p

Example 6.4. Proposition 6.1 states that a random p-biased function is
n2−n/2)-regular with very high probability. A function is 0-regular if and
(2
only if it is constant (even though you might not think of a constant func-
tion as very “random”). If A ⊆ n
2 is an afne subspace of codimension k
then 1A is 2−k-regular (Proposition 3.12). For n even the inner product
n
mod 2 function and the complete quadratic function, IPn, CQn :
2 → {0, 1},
are 2−n/2−1-regular (Exercise 1.1). On the other hand, the parity functions
χS : {−1, 1}n → {−1, 1} are not ≤-regular for any ≤ < 1 (except for S = ;). By
Exercise 5.21, Majn is 1p
n

-regular.

The notion of regularity can be particularly useful for probability density

functions; in this case it is traditional to use an alternate name:

n

2 → ≥0 is a probability density which is ≤-regular,
Denition 6.5. If ϕ :
we call it an ≤-biased density. Equivalently, ϕ is an ≤-biased density if and
only if | Ex∼ϕ[χγ(x)]| ≤ ≤ for all γ ∈ n
2 \ {0}; thus one can think of “≤-biased” as
meaning “at most ≤-biased on subspaces”. Note that the marginal of such a
distribution on any set of coordinates J ⊆ [n] is also ≤-biased. If ϕ is ϕA =
1A/ E[1A] for some A ⊆ n
2 we call A an ≤-biased set.
Example 6.6. For ϕ a probability density we have ‖ϕ‖1 = E[ϕ] = 1, so every
density is 1-biased. The density corresponding to the uniform distribution
on n
2 , namely ϕ ≡ 1, is the only 0-biased density. Densities corresponding to
the uniform distribution on smaller afne subspaces are “maximally biased”:
if A ⊆ n
2 is an afne subspace of dimension less than n, then ϕA is not ≤-
biased for any ≤ < 1 (Proposition 3.12 again). If E = {(0, . . . , 0), (1, . . . , 1)}, then
E is a 1/2-biased set (an easy computation, see also Exercise 1.1(h)).

There is a “combinatorial” property of functions f that is roughly equiv-
4 has an equivalent

alent to ≤-regularity. Recall from Exercise 1.29 that ˆ‖ f ˆ‖4

Copyright © Ryan O’Donnell, 2014, 2015, 2016, 2017, 2018, 2019, 2020, 2021.



<!-- pdf-page: 145 -->
6.1. Notions of pseudorandomness

145

non-Fourier formula: Ex,y,z[ f (x) f (y) f (z) f (x+ y+ z)]. We show (roughly speak-
ing) that f is regular if and only if this expectation is not much bigger than
E[ f ]4 = Ex,y,z,w[ f (x) f (y) f (z) f (w)]:

Proposition 6.7. Let f :

n
2 → . Then

(1) If f is ≤-regular, then ˆ‖ f ˆ‖4
(2) If f is not ≤-regular, then ˆ‖ f ˆ‖4

4 − E[ f ]4 ≤ ≤2 · Var[ f ].
4 − E[ f ]4 ≥ ≤4.

Proof. If f is ≤-regular, then

ˆ‖ f ˆ‖4

4 − E[ f ]4 =

∑

S6=;

f (S)4 ≤ max
S6=;

{ f (S)2} ·

∑

S6=;

f (S)2 ≤ ≤2 · Var[ f ].

On the other hand, if f is not ≤-regular, then | f (T)| ≥ ≤ for some T 6= ;; hence
ˆ‖ f ˆ‖4


4 is at least f (;)4 + f (T)4 ≥ E[ f ]4 + ≤4.

The condition of ≤-regularity – that all non-empty-set coefcients are
small – is quite strong. As we saw when investigating the 2
Theorem in
π
Chapter 5.4 it’s also interesting to consider f that merely have | f (i)| ≤ ≤ for
all i ∈ [n]; for monotone f this is the same as saying Infi[ f ] ≤ ≤ for i. This
suggests two weaker possible notions of pseudorandomness: having all low-
degree Fourier coefcients small, and having all inuences small. We will
consider both possibilities, starting with the second.

Now a randomly chosen f : {−1, 1}n → {−1, 1} will not have all of its inu-
ences small; in fact as we saw in Exercise 2.12, each Infi[ f ] is 1/2 in expec-
tation. However, for any δ > 0 it will have all of its (1 − δ)-stable inuences
exponentially small (recall Denition 2.52). In Exercise 6.2 you will show:

Fact 6.8. Fix δ ∈ [0, 1] and let f : {−1, 1}n → {−1, 1} be a randomly chosen
function. Then for any i ∈ [n],

E[Inf(1−δ)
i

[ f ]] =

(1 − δ/2)n
2 − δ

.

This motivates a very important notion of pseudorandomness in the anal-
ysis of Boolean functions: having all stable-inuences small. Recalling the
discussion surrounding Proposition 2.54, we can also describe this as having
no “notable” coordinates.

Denition 6.9. We say that f : {−1, 1}n → has (≤, δ)-small stable inuences,
or no (≤, δ)-notable coordinates, if Inf(1−δ)
[ f ] ≤ ≤ for each i ∈ [n]. This condition
gets stronger as ≤ and δ decrease: when δ = 0, meaning Infi[ f ] ≤ ≤ for all i,
we simply say f has ≤-small inuences.

i

Example 6.10. Besides random functions, important examples of Boolean-
valued functions with no notable coordinates are constants, majority, and

Copyright © Ryan O’Donnell, 2014, 2015, 2016, 2017, 2018, 2019, 2020, 2021.



<!-- pdf-page: 146 -->
146

6. Pseudorandomness and 2-polynomials

large parities. Constant functions are the ultimate in this regard: they have
(0, 0)-small stable inuences. (Indeed, constant functions are the only ones
with 0-small inuences.) The Majn function has 1p
-small inuences. To see
n
the distinction between inuences and stable inuences, consider the parity
functions χS. Any parity function χS (with S 6= ;) has at least one coordinate
with maximal inuence, 1. But if |S| is “large” then all of its stable inuences
will be small: We have Inf(1−δ)
[χS] equal to (1 − δ)|S|−1 when i ∈ S and equal
to 0 otherwise; i.e., χS has ((1−δ)|S|−1, δ)-small stable inuences. In particular,
χS has (≤, δ)-small stable inuences whenever |S| ≥ ln(e/≤)

.

i

δ

The prototypical example of a function f : {−1, 1}n → {−1, 1} that does not
have small stable inuences is an unbiased k-junta. Such a function has
Var[ f ] = 1 and hence from Fact 2.53 the sum of its (1 − δ)-stable inuences is
at least (1 − δ)k−1. Thus Inf(1−δ)
[ f ] ≥ (1 − δ)k−1/k for at least one i; hence f
does not have ((1 − δ)k/k, δ)-small stable inuences for any δ ∈ (0, 1). A some-
what different example is the function f (x) = x0Majn(x1, . . . , xn), which has
Inf(1−δ)
0

δ; see Exercise 6.5(d).

[ f ] ≥ 1 −

p

i

Let’s return to considering the interesting condition that | f (i)| ≤ ≤ for all
i ∈ [n]. We will call this condition (≤, 1)-regularity. It is equivalent to saying
that f ≤1 is ≤-regular, or that f has at most ≤ “correlation” with every dictator:
|〈 f , ±χi〉| ≤ ≤ for all i. Our third notion of pseudorandomness extends this
condition to higher degrees:

Denition 6.11. A function f : {−1, 1}n → is (≤, k)-regular if | f (S)| ≤ ≤ for all
0 < |S| ≤ k; equivalently, if f ≤k is ≤-regular. For k = n (or k = ∞), this condition
n
2 → ≥0 is an (≤, k)-regular probability
coincides with ≤-regularity. When ϕ :
density, it is more usual to call ϕ (and the associated probability distribution)
(≤, k)-wise independent.

Below we give two alternate characterizations of (≤, k)-regularity; how-
ever, they are fairly “rough” in the sense that they have exponential losses
on k. This can be acceptable if k is thought of as a constant. The rst char-
acterization is that f is (≤, k)-regular if and only if xing k input coordinates
changes f ’s mean by at most O(≤). The second characterization is the condi-
tion that f has O(≤) covariance with every k-junta.

Proposition 6.12. Let f : {−1, 1}n → and let ≤ ≥ 0, k ∈ .

(1) If f is (≤, k)-regular then any restriction of at most k coordinates changes f ’s

mean by at most 2k≤.

(2) If f is not (≤, k)-regular then some restriction to at most k coordinates

changes f ’s mean by more than ≤.

Proposition 6.13. Let f : {−1, 1}n → and let ≤ ≥ 0, k ∈ .

Copyright © Ryan O’Donnell, 2014, 2015, 2016, 2017, 2018, 2019, 2020, 2021.



<!-- pdf-page: 147 -->
6.1. Notions of pseudorandomness

147

(1) If f is (≤, k)-regular, then Cov[ f , h] ≤ ˆ‖hˆ‖1≤ for any h : {−1, 1}n → with
deg(h) ≤ k. In particular, Cov[ f , h] ≤ 2k/2≤ for any k-junta h : {−1, 1}n →
{−1, 1}.

(2) If f is not (≤, k)-regular, then Cov[ f , h] > ≤ for some k-junta h : {−1, 1}n →

{−1, 1}.

We will prove Proposition 6.12, leaving the proof of Proposition 6.13 to the
exercises.

Proof of Proposition 6.12. For the rst statement, suppose f is (≤, k)-regular
and let J ⊆ [n], z ∈ {−1, 1}J, where |J| ≤ k. Then the statement holds because

E[ f

J|z

] = f (;) +

∑

;6=T⊆J

f (T) zT

(Exercise 1.15) and each of the at most 2k terms | f (T) zT | = | f (T)| is at most ≤.
For the second statement, suppose that | f (J)| > ≤, where 0 < |J| ≤ k. Then

a given restriction z ∈ {−1, 1}J changes f ’s mean by

∑

h(z) =

f (T) zT .

We need to show that ‖h‖∞ > ≤, and this follows from

;6=T⊆J

‖h‖∞ = ‖hχJ‖∞ ≥ | E[hχJ]| = |h(J)| = | f (J)| > ≤.



Taking ≤ = 0 in the above two propositions we obtain:

Corollary 6.14. For f : {−1, 1}n → , the following are equivalent:

(1) f is (0, k)-regular.

(2) Every restriction of at most k coordinates leaves f ’s mean unchanged.
(3) Cov[ f , h] = 0 for every k-junta h : {−1, 1}n → {−1, 1}.

If f is a probability density, condition (3) is equivalent to Ex∼ f [h(x)] = E[h] for
every k-junta h : {−1, 1}n → {−1, 1}.

For such functions, additional terminology is used:

Denition 6.15. If f : {−1, 1}n → {−1, 1} is (0, k)-regular, it is also called kth-
order correlation immune. If f is in addition unbiased, then it is called k-
2 → ≥0 is a (0, k)-regular probability density, then
resilient. Finally, if ϕ :
we call ϕ (and the associated probability distribution) k-wise independent.

n

Example 6.16. Any parity function χS : {−1, 1}n → {−1, 1} with |S| = k + 1
is k-resilient. More generally, so is χS · g for any g : {−1, 1}n → {−1, 1} that
does not depend on the coordinates in S. For a good example of a correlation
immune function that is not resilient, consider h : {−1, 1}3m → {−1, 1} dened
by h = χ{1,...,2m} ∧ χ{m+1,...,3m}. This h is not unbiased, being True on only a

Copyright © Ryan O’Donnell, 2014, 2015, 2016, 2017, 2018, 2019, 2020, 2021.



<!-- pdf-page: 148 -->
148

6. Pseudorandomness and 2-polynomials

1/4-fraction of inputs. However, its bias does not change unless at least 2m
input bits are xed; hence h is (2m − 1)th-order correlation immune.

We conclude this section with Figure 6.1, indicating how our various no-

tions of pseudorandomness compare:

Figure 6.1. Comparing notions of pseudorandomness: arrows go from
stronger notions to (strictly) weaker ones

For precise quantitative statements, counterexamples showing that no other
relationships are possible, and explanations for why these notions essentially
coincide for monotone functions, see Exercise 6.5.

6.2.

2-polynomials

We began our study of Boolean functions in Chapter 1.2 by considering their
In this section we take a
polynomial representations over the real eld.
2, with False,
brief look at their polynomial representations over the eld
True being represented by 0, 1 ∈ 2 as usual. Note that in the eld
2, the
arithmetic operations + and · correspond to logical XOR and logical AND,
respectively.

Example 6.17. Consider the logical parity (XOR) function on n bits, χ[n].
To represent it over the reals (as we have done so far) we encode False,True
; then χ[n] : {−1, 1}n → {−1, 1} has the polynomial representation
by ±1 ∈
χ[n](x) = x1x2 · · · xn. Suppose instead we encode False,True by 0, 1 ∈ 2; then
n
χ[n] :
2 → 2 has the polynomial representation χ[n](x) = x1 + x2 + · · · + xn.
Notice this polynomial has degree 1, whereas the representation over the
reals has degree n.

In general, let f :

n
2 → 2 be any Boolean function. Just as in Chapter 1.2
we can nd a (multilinear) polynomial representation for it by interpolation.
2 → 2 for a ∈ n
The indicator function 1{a} :
xi

2 can be written as
(1 − xi),

1{a}(x) =

(6.1)

∏

∏

n

i:a i=1

i:a i=0

Copyright © Ryan O’Donnell, 2014, 2015, 2016, 2017, 2018, 2019, 2020, 2021.



<!-- pdf-page: 149 -->
6.2.

2-polynomials

149

a degree-n multilinear polynomial. (We could have written 1 + xi rather than
1− xi since these are the same in 2.) Hence f has the multilinear polynomial
expression

∑

f (x) =

f (a)1{a}(x).

After simplication, this may be put in the form
cS xS,

f (x) =

∑

a∈ n
2

S⊆[n]

(6.2)

(6.3)



i∈S xi as usual, and each coefcient cS is in 2. We call (6.3)
2-polynomial representation of f . As an example, if f = χ[3] is the parity

where xS =
the
function on 3 bits, its interpolation is

χ[3](x) = (1 − x1)(1 − x2)x3 + (1 − x1)x2(1 − x3) + x1(1 − x2)(1 − x3) + x1x2x3

= x1 + x2 + x3 − 2(x1x2 + x1x3 + x2x3) + 4x1x2x3
= x1 + x2 + x3

(6.4)

as expected. We also have uniqueness of the
the quickest way to see this is to note that there are 22n functions
and also 22n possible choices for the coefcients cS. Summarizing:
n
2 → 2 has a unique

2-polynomial representation;
n
2 → 2

2-polynomial represen-

Proposition 6.18. Every f :
tation as in (6.3).

n
2 → 2 has the simple
Example 6.19. The logical AND function ANDn :
expansion ANDn(x) = x1x2 · · · xn. The inner product mod 2 function has the
degree-2 expansion IP2n(x1, . . . , xn, y1, . . . , yn) = x1 y1 + x2 y2 + · · · + xn yn.

Since the

2-polynomial representation is unique we may dene

2-

degree:

Denition 6.20. The
{False,True}, denoted deg
( f ), is the degree of its
tion. We reserve the notation deg( f ) for the degree of f ’s Fourier expansion.

2-degree of a Boolean function f : {False,True}n →
2-polynomial representa-

2

We can also give a formula for the coefcients of the

2-polynomial repre-

sentation:

Proposition 6.21. Suppose f :

f (x) =

S⊆[n] cS xS. Then cS =



n
2 → 2 has
supp(x)⊆S f (x).

2-polynomial representation

Corollary 6.22. Let f : {False,True}n → {False,True}. Then deg
only if f (x) = True for an odd number of inputs x.

2

( f ) = n if and

The proof of Proposition 6.21 is left for Exercise 6.10; Corollary 6.22 is just the
x f (x) by observing what
case S = [n]. You can also directly see that c[n] =
happens with the monomial x1x2 · · · xn in the interpolation (6.1), (6.2).



Copyright © Ryan O’Donnell, 2014, 2015, 2016, 2017, 2018, 2019, 2020, 2021.



<!-- pdf-page: 150 -->
150

6. Pseudorandomness and 2-polynomials

) and its

Given a generic Boolean function f : {False,True}n → {False,True} it’s nat-
ural to ask about the relationship between its Fourier expansion (i.e., poly-
2-polynomial representation. In fact
nomial representation over
-representation. Sup-
you can easily derive the
pose p(x) is the Fourier expansion of f ; i.e., f ’s
-multilinear representa-
tion when we interpret False, True as ±1 ∈
. From Exercise 1.9, q(x) =
1
2 − 1
-multilinear representation for f
2 p(1 − 2x1, . . . , 1 − 2xn) is the unique
when we interpret False, True as 0, 1 ∈ . But we can also obtain q(x) by car-
rying out the interpolation in (6.1), (6.2) over
2 representation
of f is obtained simply by reducing q(x)’s (integer) coefcients modulo 2.

2-representation from the

. Thus the

We saw an example of this derivation above with χ[3]. The ±1-representation

is x1x2x3. The representation over {0, 1} ∈ ⊆ is 1
2 (1 − 2x1)(1 − 2x2)(1 −
2x3), which when expanded equals (6.4) and has integer coefcients. Finally,
we obtain the
2 representation x1 +x2 +x3 by reducing the coefcients of (6.4)
modulo 2.

2 − 1

One thing to note about this transformation from Fourier expansion to
2-
representation is that it can only decrease degree. As noted in Exercise 1.11,
the rst step, forming q(x) = 1
2 p(1 − 2x1, . . . , 1 − 2xn), does not change the
degree at all (except if p(x) ≡ 1, q(x) ≡ 0). And the second step, reducing q’s
coefcients modulo 2, cannot increase the degree. We conclude:

2 − 1

Proposition 6.23. Let f : {−1, 1}n → {−1, 1}. Then deg

( f ) ≤ deg( f ).

2

Here is an interesting consequence of this proposition. Suppose that f :
{−1, 1}n → {−1, 1} is k-resilient; i.e., f (S) = 0 for all |S| ≤ k < n. Let g = χ[n] · f ;
thus g(S) = f ([n] \ S) and hence deg(g) ≤ n − k − 1. From Proposition 6.23
n
we deduce deg
2 → 2, then g =
(g) ≤ n − k − 1. But if we interpret f , g :
x1+· · ·+xn+ f and hence deg
( f ) (unless f is parity or its negation).
Thus:

(g) = deg

2

2

2

Proposition 6.24. Let f : {−1, 1}n → {−1, 1} be k-resilient, k < n − 1. Then
deg

( f ) ≤ n − k − 1.

2

This proposition was shown by Siegenthaler, a cryptographer who was
studying stream ciphers; his motivation is discussed further in the notes in
Section 6.6. More generally, Siegenthaler proved the following result (the
proof does not require Fourier analysis):

Siegenthaler’s Theorem. Proposition 6.24 holds. Further, if f is merely
kth-order correlation immune, then we still have deg

( f ) ≤ n − k (for k < n).

2

Proof. Pick any monomial xJ of maximal degree d = deg
2-
polynomial representation; we may assume d > 1 else we are done. Make

( f ) in f ’s

2

Copyright © Ryan O’Donnell, 2014, 2015, 2016, 2017, 2018, 2019, 2020, 2021.



<!-- pdf-page: 151 -->
6.3. Constructions of various pseudorandom functions

151

an arbitrary restriction to the n − d coordinates outside of J, forming func-
tion g :
2-polynomial repre-
sentation; thus by Corollary 6.22, g is 1 for an odd number of inputs.

2 → 2. The monomial xJ still appears in g’s

J

Let us rst show Proposition 6.24. Assuming f is k-resilient, it is unbi-
ased. But g is 1 for an odd number of inputs so it cannot be unbiased (since
2d−1 is even for d > 1). Thus the restriction changed f ’s bias, and we must
have n − d > k, hence d ≤ n − k − 1.

Suppose now f is merely kth-order correlation immune. Pick an arbi-
trary input coordinate for g and suppose its two possible restrictions give
subfunctions g0 and g1. Since g has an odd number of 1’s, one of g0 has
an odd number of 1’s and the other has an even number. In particular, g0
and g1 have different biases. One of these biases must differ from f ’s. Thus

n − d + 1 > k, hence d ≤ n − k.

We end this section by mentioning another bound related to correlation

immunity:

Theorem 6.25. Suppose f : {−1, 1}n → {−1, 1} is kth-order correlation immune
but not k-resilient (i.e., E[ f ] 6= 0). Then k + 1 ≤ 2

3 n.

The proof of this theorem (left to Exercise 6.14) uses the Fourier expan-
2-representation. The bounds in both Siegenthaler’s

sion rather than the
Theorem and Theorem 6.25 can be sharp in many cases; see Exercise 6.15.

6.3. Constructions of various pseudorandom functions

In this section we give some constructions of Boolean functions with strong
pseudorandomness properties. We begin by discussing bent functions:

Denition 6.26. A function f :
| f (γ)| = 2−n/2 for all γ ∈ n
2 .

n
2 → {−1, 1} (with n even) is called bent if

Bent functions are 2−n/2-regular. If the denition of ≤-regularity were
changed so that even | f (0)| needed to be at most ≤, then bent functions would
f (γ)2 = 1 for any f :
be the most regular possible functions. This is because
2 → {−1, 1} and hence at least one | f (γ)| must be at least 2−n/2. In particular,
bent functions are those that are maximally distant from the class of afne
functions, {±χγ : γ ∈ n
2 }.



n

γ

We have encountered some bent functions already. The canonical example
is the inner product mod 2 function, IPn(x) = χ(x1xn/2+1 +x2xn/2+2 +· · ·+xn/2xn).
(Recall the notation χ(b) = (−1)b.) For n = 2 this is just the AND2 function
2 + 1
1
2 x1x2, which is bent by inspection. For general n, the bentness
is a consequence of the following fact (proved in Exercise 6.16):

2 x1 + 1

2 x2 − 1

Copyright © Ryan O’Donnell, 2014, 2015, 2016, 2017, 2018, 2019, 2020, 2021.



<!-- pdf-page: 152 -->
152

6. Pseudorandomness and 2-polynomials

Proposition 6.27. Let f :
f ⊕ g :

n
2 → {−1, 1} and g :
n+n′
2 → {−1, 1} dened by ( f ⊕ g)(x, x′) = f (x)g(x′) is also bent.

n′
2 → {−1, 1} be bent. Then

Another example of a bent function is the complete quadratic function
1≤i< j≤n xi x j) from Exercise 1.1. Actually, in some sense it is the



CQn(x) = χ(
“same” example, as we now explain.

Proposition 6.28. Let f :
γ ∈ n

2 , as is f ◦ M for any invertible linear transformation M :

n

2 → n
2 .

n
2 → {−1, 1} be bent. Then ±χγ · f is bent for any

Proof. Multiplying by −1 does not change bentness, and both χγ · f and f ◦ M
have the same Fourier coefcients as f up to a permutation (see Exercise 3.1).


We claim that CQn arises from f = IPn as in Proposition 6.28. In the
1≤i< j≤4 xi x j = (x1 + x3)(x2 + x3)+(x1 + x2 + x3)x4 + x3



case n = 4, this is because
over

2; thus

CQ4(x) = IP4(M x) · χ(0,0,1,0)(x), where M =















1 0 1 0
1 1 1 0
0 1 1 0
0 0 0 1

is invertible.

The general case is left to Exercise 6.20. In fact, every bent f with deg
( f ) ≤ 2
arises by applying Proposition 6.28 to the inner product mod 2 function; see
Exercise 6.19. There are other large families of bent functions; however,
the problem of classifying all bent functions is open and seems difcult. We
content ourselves by describing one more family:

2

Proposition 6.29. Let f :
where g : {−1, 1}n → {−1, 1} is arbitrary. Then f is bent.

2n
2 → {−1, 1} be dened by f (x, y) = IP2n(x, y)g(y)

Proof. We will think of y ∈ n
γ ∈ ̂2n
2 as (γ1, γ2). Then indeed

2 , so IP2n(x, y) = χy(x). We’ll also write a generic

f (γ) = E
x,y

[χy(x)g(y)χ(γ1,γ2)(x, y)] = E
y

g(y)χγ2

(y) E
x

[χy+γ1

(x)]

= E
y

[g(y)χγ2

(y)1{y+γ1=0}] = 2−n g(γ1)χγ2

(γ1) = ±2−n. 





We next discuss explicit constructions of small ≤-biased sets, which are of
considerable use in the eld of algorithmic derandomization. The most basic
step in a randomized algorithm is drawing a string x ∼ n
2 from the uniform
distribution; however, this has the “cost” of generating n independent, random
bits. But sometimes it’s not necessary that x precisely have the uniform
distribution; it may sufce that x be drawn from an ≤-biased density. If we
can deterministically nd an ≤-biased (multi-)set A of cardinality, say, 2`, then

Copyright © Ryan O’Donnell, 2014, 2015, 2016, 2017, 2018, 2019, 2020, 2021.



<!-- pdf-page: 153 -->
6.3. Constructions of various pseudorandom functions

153

we can generate x ∼ ϕA using just ` independent random bits. We will see
some example derandomizations of this nature in Section 6.4; for now we
discuss constructions.

Fix ` ∈ + and recall that there exists a nite eld 2` with exactly 2`
elements. It is easy to nd an explicit representation for
2` – a complete
addition and multiplication table, say – in time 2O(`). (In fact, one can compute
within 2` even in deterministic poly(`) time.) The eld elements x ∈ 2` are
2 for
naturally encoded by distinct `-bit vectors; we will write enc :
this encoding. The encoding is linear; i.e., it satises enc(0) = (0, . . . , 0) and
enc(x + y) = enc(x) + enc(y) for all x, y ∈ 2`.

2` → `

Theorem 6.30. There is a deterministic algorithm that, given n ≥ 1 and 0 <
≤ ≤ 1/2, runs in poly(n/≤) time and outputs a multiset A ⊆ n
2 of cardinality at
most 16(n/≤)2 with the property that ϕA is an ≤-biased density.

Proof. It sufces to obtain cardinality (n/≤)2 under the assumption that
≤ = 2−t and n = 2`−t are integer powers of 2. We will describe a probabil-
ity density ϕ on n
2 by giving a procedure for drawing a string y ∼ ϕ which
uses 2` independent random bits. A will be the multiset of 22` = (n/≤)2 possi-
ble outcomes for y. It will be clear that A can be generated in deterministic
polynomial time. The goal will be to show that ϕ is 2−t-biased.

To draw y ∼ ϕ, rst choose r, s ∼ 2` independently and uniformly. This

uses 2` independent random bits. Then dene the ith coordinate of y by

yi = 〈enc(r i), enc(s)〉,

i ∈ [n],

where the inner product 〈·, ·〉 takes place in `
argue that | E[χγ(y)]| ≤ 2−t. Now over

`
2,

2. Fixing γ ∈ n

2 \ {0}, we need to

〈γ, y〉 =

n∑

i=1

γi〈enc(r i), enc(s)〉 =

〈 n∑

i=1

γienc(r i), enc(s)

〉

= 〈enc(

n

i=1

γi r i), enc(s)〉,

where the last step used linearity of enc. Thus

E[χγ(y)] = E[(−1)〈γ,y〉] = E
r

[(−1)〈enc(pγ(r)),enc(s)〉]


E
s



,

(6.5)

2` → 2` is the polynomial a 7→ γ1a + γ2a2 + · · · + γnan. This poly-
where pγ :
nomial is of degree at most n, and is nonzero since γ 6= 0. Hence it has at
most n roots (zeroes) over the eld
2`. Whenever r is one of these roots,
enc(pγ(r)) = 0 and the inner expectation in (6.5) is 1. But whenever r is not
a root of pγ we have enc(pγ(r)) 6= 0 and so the inner expectation is 0. (We are
using Fact 1.7 here.) We deduce that

0 ≤ E[χγ(y)] ≤ Pr[r is a root of pγ] ≤

n
2`

= 2−t,

which is stronger than what we need.



Copyright © Ryan O’Donnell, 2014, 2015, 2016, 2017, 2018, 2019, 2020, 2021.



<!-- pdf-page: 154 -->
154

6. Pseudorandomness and 2-polynomials

The bound of O(n/≤)2 in this theorem is fairly close to being optimally

small; see Exercise 6.24 and the notes for this chapter.

Another useful tool in derandomization is that of k-wise independent dis-
tributions. Sometimes a randomized algorithm using n independent random
bits will still work assuming only that every subset of k of the bits is indepen-
dent. Thus as with ≤-biased sets, it’s worthwhile to come up with deterministic
constructions of small sets A ⊂ n
2 such that the density function ϕA is k-wise
independent (i.e., (0, k)-regular). The best known examples have the addi-
n
tional pleasant feature that A is a linear subspace of
2 ; in this case, k-wise
independence is easy to characterize:

2 be the
Proposition 6.31. Let H be an m × n matrix over
span of H’s rows. Then ϕA is k-wise independent if and only if any sum of at
most k columns of H is nonzero in m

2 . (We exclude the “empty” sum.)

2 and let A ≤ n

Proof. Since ϕA =
γ∈A⊥ χγ (Proposition 3.11), ϕA is k-wise independent if
and only if |γ| > k for every γ ∈ A⊥ \ {0}. But γ ∈ A⊥ if and only if Hγ = 0. 



Here is a simple construction of such a matrix with m ∼ k log n:

Theorem 6.32. Let k, ` ∈ + and assume n = 2` ≥ k. Then for m = (k − 1)` + 1,
there is a matrix H ∈ m×n
such that any sum of at most k columns of H is
nonzero in m
2 .

2

Proof. Write α1, . . . , αn for the elements of the nite eld
the following matrix H′ ∈ k×n

:

n, and consider

n


H′ =









1
α1
α2
1
...
αk−1
1

1
α2
α2
2
...
αk−1
2











.

1
· · ·
· · ·
αn
α2
· · ·
n
...
. . .
· · · αk−1

n

Any submatrix of H′ formed by choosing k columns is a Vandermonde matrix
and is therefore nonsingular. Hence any subset of k columns of H′ is linearly
k
n. In particular, any sum of at most k columns of H′ is
independent in
nonzero in k
(i > 0)
with enc(αi
2. Since enc is a linear map we
j
may conclude that any sum of at most k columns of H is nonzero in m
2 . 

n. Now form H ∈ m×n
), thought of as a column vector in `

from H′ by replacing each entry αi
j

2

Corollary 6.33. There is a deterministic algorithm that, given integers 1 ≤
k ≤ n, runs in poly(nk) time and outputs a subspace A ≤ n
2 of cardinality at
most 2knk−1 such that ϕA is k-wise independent.

Copyright © Ryan O’Donnell, 2014, 2015, 2016, 2017, 2018, 2019, 2020, 2021.



<!-- pdf-page: 155 -->
6.4. Applications in learning and testing

155

Proof. It sufces to assume n = 2` is a power of 2 and then obtain cardinality
2nk−1 = 2(k−1)`+1. In this case, the algorithm constructs H as in Theorem 6.32
and takes A to be the span of its rows. The fact that ϕA is k-wise independent

is immediate from Proposition 6.31.

For constant k this upper bound of O(nk−1) is close to optimal. It can be
improved to O(nbk/2c), but there is a lower bound of Ω(nbk/2c) for constant k;
see Exercises 6.27, 6.28.

We conclude this section by noting that taking an ≤-biased density within

a k-wise independent subspace yields an (≤, k)-wise independent density:

Lemma 6.34. Suppose H ∈ m×n
of H is nonzero in m
y ∼ ϕ and setting z = yH ∈ n
dent.

2 . Let ϕ be an ≤-biased density on m

is such that any sum of at most k columns
2 . Consider drawing
2 . Then the density of z is (≤, k)-wise indepen-

2

Proof. Suppose γ ∈ n
and hence | E[χγ(z)]| = | E y∼ϕ[(−1)yHγ]| ≤ ≤ since ϕ is ≤-biased.

2 has 0 < |γ| ≤ k. Then Hγ is nonzero by assumption


As a consequence, combining the constructions of Theorem 6.30 and The-
orem 6.32 gives an (≤, k)-wise independent distribution that can be sampled
from using only O(log k + log log(n) + log(1/≤)) independent random bits:

Theorem 6.35. There is a deterministic algorithm that, given integers 1 ≤ k ≤
n and also 0 < ≤ ≤ 1/2, runs in time poly(n/≤) and outputs a multiset A ⊆ n
2 of
cardinality O(k log(n)/≤)2 (a power of 2) such that ϕA is (≤, k)-wise independent.

6.4. Applications in learning and testing

In this section we describe some applications of our study of pseudorandom-
ness.

We begin with a notorious open problem from learning theory, that of
n
2 → 2 | f is a k-junta}; we will always assume
learning juntas. Let C = { f :
that k ≤ O(log n). In the query access model, it is quite easy to learn C exactly
(i.e., with error 0) in poly(n) time (Exercise 3.37(a)). However, in the model of
random examples, it’s not obvious how to learn C more efciently than in the
nk · poly(n) time required by the Low-Degree Algorithm (see Theorem 3.36).
Unfortunately, this is superpolynomial as soon as k > ω(1). The state of
affairs is the same in the case of depth-k decision trees (a superclass of C ),
and is similar in the case of poly(n)-size DNFs and CNFs. Thus if we wish to
learn, say, poly(n)-size decision trees or DNFs from random examples only, a
necessary prerequisite is doing the same for O(log n)-juntas.

Copyright © Ryan O’Donnell, 2014, 2015, 2016, 2017, 2018, 2019, 2020, 2021.



<!-- pdf-page: 156 -->
156

6. Pseudorandomness and 2-polynomials

Whether or not ω(1)-juntas can be learned from random examples in poly-
nomial time is a longstanding open problem. Here we will show a modest
improvement on the nk-time algorithm:

Theorem 6.36. For k ≤ O(log n), the class C = { f :
can be exactly learned from random examples in time n(3/4)k · poly(n).

n
2 → 2 | f is a k-junta}

(The 3/4 in this theorem can in fact be replaced by ω/(ω + 1), where ω is any
number such that n × n matrices can be multiplied in time O(nω).)

The rst observation we will use to prove Theorem 6.36 is that to learn k-
juntas, it sufces to be able to identify a single coordinate that is relevant (see
Denition 2.18). The proof of this is fairly simple and is left for Exercise 6.31:

Lemma 6.37. Theorem 6.36 follows from the existence of a learning algorithm
n
that, given random examples from a nonconstant k-junta f :
2 → 2, nds
at least one relevant coordinate for f (with probability at least 1 − δ) in time
n(3/4)k · poly(n) · log(1/δ).

Assume then that we have random example access to a (nonconstant)
n
k-junta f :
2 → 2. As in the Low-Degree Algorithm we will estimate the
Fourier coefcients f (S) for all 1 ≤ |S| ≤ d, where d ≤ k is a parameter to
be chosen later. Using Proposition 3.30 we can ensure that all estimates
are accurate to within (1/3)2−k, except with probability most δ/2, in time
nd · poly(n) · log(1/δ). (Recall that 2k ≤ poly(n).) Since f is a k-junta, all of
its Fourier coefcients are either 0 or at least 2−k in magnitude; hence we
can exactly identify the sets S for which f (S) 6= 0. For any such S, all of the
coordinates i ∈ S are relevant for f (Exercise 2.11). So unless f (S) = 0 for all
1 ≤ |S| ≤ d, we can nd a relevant coordinate for f in time nd · poly(n) · log(1/δ)
(except with probability at most δ/2).

To complete the proof of Theorem 6.36 it remains to handle the case that
f (S) = 0 for all 1 ≤ |S| ≤ d; i.e., f is dth-order correlation immune. In this case,
( f ) ≤ k − d. (Note that d < k
by Siegenthaler’s Theorem we know that deg
since f is not constant.) But there is a learning algorithm running in time
O(n)3` · log(1/δ) that exactly learns any
2-polynomial of degree at most `
(except with probability at most δ/2). Roughly speaking, the algorithm draws
O(n)` random examples and then solves an 2-linear system to determine the
coefcients of the unknown polynomial; see Exercise 6.30 for details. Thus in
time n3(k−d) · poly(n) · log(1/δ) this algorithm will exactly determine f , and in
particular nd a relevant coordinate.

2

By choosing d =

we balance the running time of the two algorithms.
Regardless of whether f is dth-order correlation immune, at least one of the
two algorithms will nd a relevant coordinate for f (except with probability
at most δ/2 + δ/2 = δ) in time n(3/4)k · poly(n) · log(1/δ). This completes the proof
of Theorem 6.36.

⌈

⌉

3
4 k

Copyright © Ryan O’Donnell, 2014, 2015, 2016, 2017, 2018, 2019, 2020, 2021.



<!-- pdf-page: 157 -->
6.4. Applications in learning and testing

157

Our next application of pseudorandomness involves using ≤-biased dis-
tributions to give a deterministic version of the Goldreich–Levin Algorithm
(and hence the Kushilevitz–Mansour learning algorithm) for functions f with
small ˆ‖ f ˆ‖1. We begin with a basic lemma showing that you can get a good
estimate for the mean of such functions using an ≤-biased distribution:

Lemma 6.38. If f : {−1, 1}n → and ϕ : {−1, 1}n → is an ≤-biased density,
then

∣
∣
∣
∣ E
x∼ϕ

[ f (x)] − E[ f ]

∣
∣
∣
∣ ≤ ˆ‖ f ˆ‖1≤.

This lemma follows from Proposition 6.13.(1), but we provide a separate proof:

Proof. By Plancherel,

[ f (x)] = 〈ϕ, f 〉 = f (;) +

E
x∼ϕ

∑

S6=;

ϕ(S) f (S),

and the difference of this from E[ f ] = f (;) is, in absolute value, at most

∑

S6=;

| ϕ(S)| · | f (S)| ≤ ≤ ·

∑

S6=;

| f (S)| ≤ ˆ‖ f ˆ‖1≤.



Since ˆ‖ f 2 ˆ‖1 ≤ ˆ‖ f ˆ‖2

1 (Exercise 3.6), we also have the following immediate

corollary:

Corollary 6.39. If f : {−1, 1}n → and ϕ : {−1, 1}n → is an ≤-biased density,
then

∣
∣
∣
∣ E
x∼ϕ

[ f (x)2] − E[ f 2]

∣
∣
∣ ≤ ˆ‖ f ˆ‖2
∣
1≤.

We can use the rst lemma to get a deterministic version of Proposi-
tion 3.30, the learning algorithm that estimates a specied Fourier coefcient.

Proposition 6.40. There is a deterministic algorithm that, given query access
to a function f : {−1, 1}n → as well as U ⊆ [n], 0 < ≤ ≤ 1/2, and s ≥ 1, outputs
an estimate f (U) for f (U) satisfying

provided ˆ‖ f ˆ‖1 ≤ s. The running time is poly(n, s, 1/≤).

| f (U) − f (U)| ≤ ≤,

Proof. It sufces to handle the case U = ; because for general U, the algo-
rithm can simulate query access to f ·χU with poly(n) overhead, and Éf · χU (;) =
f (U). The algorithm will use Theorem 6.30 to construct an (≤/s)-biased den-
sity ϕ that is uniform over a (multi-)set of cardinality O(n2s2/≤2). By enumer-
ating over this set and using queries to f , it can deterministically output the
estimate f (;) = Ex∼ϕ[ f (x)] in time poly(n, s, 1/≤). The error bound now follows

from Lemma 6.38.

Copyright © Ryan O’Donnell, 2014, 2015, 2016, 2017, 2018, 2019, 2020, 2021.



<!-- pdf-page: 158 -->
158

6. Pseudorandomness and 2-polynomials

The other key ingredient needed for the Goldreich–Levin Algorithm was

Proposition 3.40, which let us estimate

WS|J[ f ] =

∑

T⊆J

f (S ∪ T)2 =

E
z∼{−1,1}J

[ ̂f J|z(S)2]

(6.6)

for any S ⊆ J ⊆ [n]. Observe that for any z ∈ {−1, 1}J we can use Proposi-
tion 6.40 to deterministically estimate ̂f J|z(S) to accuracy ±≤. The reason
is that we can simulate query access to the restricted function ̂f J|z, the
(≤/s)-biased density ϕ remains (≤/s)-biased on {−1, 1}J, and most importantly
ˆ‖ f J|z
ˆ‖1 ≤ ˆ‖ f ˆ‖1 ≤ s by Exercise 3.7. It is not much more difcult to determinis-
tically estimate (6.6):

Proposition 6.41. There is a deterministic algorithm that, given query access
to a function f : {−1, 1}n → {−1, 1} as well as S ⊆ J ⊆ [n], 0 < ≤ ≤ 1/2, and s ≥ 1,
outputs an estimate β for WS|J[ f ] that satises

provided ˆ‖ f ˆ‖1 ≤ s. The running time is poly(n, s, 1/≤).

|WS|J[ f ] − β| ≤ ≤,

Proof. Recall the notation F

f from Denition 3.20; by (6.6), the algo-

S|J
z∼{−1,1}J [(F

rithm’s task is to estimate E
≤
4s2 -biased density, Corollary 6.39 tells us that
∣
∣
∣ E
z∼ϕ

∣
∣
∣ ≤ ˆ‖F

f )2(z)] −

f )2(z)]

[(F

[(F

S|J

S|J

S|J

E
z∼{−1,1}J

f )2(z)]. If ϕ : {−1, 1}J → ≥0 is an

f ˆ‖2

1 · ≤

4s2 ≤ ˆ‖ f ˆ‖2

1 · ≤

4s2 ≤ ≤

4 , (6.7)

S|J

≤

where the second inequality is immediate from Proposition 3.21. We now
f )2(z)]. For each
show the algorithm can approximately compute Ez∼ϕ[(F
z ∈ {−1, 1}J, the algorithm can use ϕ to deterministically estimate (F
f )(z) =
̂f J|z(S) to within ±s ·
4 in poly(n, s, 1/≤) time, just as was described in
the text following (6.6). Since | ̂f J|z(S)| ≤ 1, the square of this estimate is
within, say, 3≤
f )2(z). Hence by enumerating over the support of ϕ, the
f )2(z)]
algorithm can in deterministic poly(n, s, 1/≤) time estimate Ez∼ϕ[(F
to within ± 3≤
4 , which by (6.7) gives an estimate to within ±≤ of the desired

z∼{−1,1}J [(F
quantity E

4s2 ≤ ≤

4 of (F

f )2(z)].

S|J

S|J

S|J

S|J

S|J

Propositions 6.40 and 6.41 are the only two ingredients needed for a de-
randomization of the Goldreich–Levin Algorithm. We can therefore state a
derandomized version of its corollary Theorem 3.38 on learning functions with
small Fourier 1-norm:

Theorem 6.42. Let C = { f : {−1, 1}n → {−1, 1} | ˆ‖ f ˆ‖1 ≤ s}. Then C is determin-
istically learnable from queries with error ≤ in time poly(n, s, 1/≤).

Copyright © Ryan O’Donnell, 2014, 2015, 2016, 2017, 2018, 2019, 2020, 2021.



<!-- pdf-page: 159 -->
6.4. Applications in learning and testing

159

Since any f : {−1, 1}n → {−1, 1} with sparsity( f ) ≤ s also has ˆ‖ f ˆ‖1 ≤ s, we

may also deduce from Exercise 3.37(c):

Theorem 6.43. Let C = { f : {−1, 1}n → {−1, 1} | sparsity( f ) ≤ 2O(k)}. Then C is
deterministically learnable exactly (0 error) from queries in time poly(n, 2k).

Example functions that fall into the concept classes of these theorems are deci-
sion trees of size at most s, and decision trees of depth at most k, respectively.

We conclude this section by discussing a derandomized version of the

Blum–Luby–Rubinfeld linearity test from Chapter 1.6:

Derandomized BLR Test. Given query access to f :

n
2 → 2:
2 and y ∼ ϕ, where ϕ is an ≤-biased density.

(1) Choose x ∼ n

(2) Query f at x, y, and x + y.

(3) “Accept” if f (x) + f (y) = f (x + y).

Whereas the original BLR Test required exactly 2n independent random
bits, the above derandomized version needs only n + O(log(n/≤)). This is very
close to minimum possible; a test using only, say, .99n random bits would only
be able to inspect a 2−.01n fraction of f ’s values.

If f is

2-linear then it is still accepted by the Derandomized BLR Test
with probability 1. As for the approximate converse, we’ll have to make a
slight concession: We’ll show that any function accepted with probability
close to 1 must be close to an afne function, i.e., satisfy deg
( f ) ≤ 1. This
n
2 → 2 might be 1 everywhere
concession is necessary: the function f :
except on the (tiny) support of ϕ. In that case the acceptance criterion f (x) +
f (y) = f (x + y) will almost always be 1 + 0 = 1; yet f is very far from every
linear function. It is, however, very close to the afne function 1.

2

Theorem 6.44. Suppose the Derandomized BLR Test accepts f :
with probability 1
afne g :

2 θ. Then f has correlation at least
p

2 → 2; i.e., dist( f , g) ≤ 1

2 + 1

2 − 1

θ2 − ≤.

p

n

2

n
2 → 2
θ2 − ≤ with some

Remark 6.45. The bound in this theorem works well both when θ is close to 0
and when θ is close to 1; e.g., for θ = 1 − 2δ we get that if f is accepted with
probability 1 − δ, then f is nearly δ-close to an afne function, provided ≤ ø δ.

Proof. As in the analysis of the BLR Test (Theorem 1.30) we encode f ’s
outputs by ±1 ∈ . Using the rst few lines of that analysis we see that our
hypothesis is equivalent to

θ ≤ E

x∼ n
2
y∼ϕ

[ f (x) f (y) f (x + y)] = E
y∼ϕ

[ f (y) · ( f ∗ f )(y)].

Copyright © Ryan O’Donnell, 2014, 2015, 2016, 2017, 2018, 2019, 2020, 2021.



<!-- pdf-page: 160 -->
160

6. Pseudorandomness and 2-polynomials

By Cauchy–Schwarz,







[ f (y) · ( f ∗ f )(y)] ≤

E
y∼ϕ

[ f (y)2]

E
y∼ϕ

E
y∼ϕ

[( f ∗ f )2(y)] =

[( f ∗ f )2(y)],

E
y∼ϕ

and hence

θ2 ≤ E
y∼ϕ

[( f ∗ f )2(y)] ≤ E[( f ∗ f )2] + ˆ‖ f ∗ f ˆ‖1≤ =

f (γ)4 + ≤,

∑

γ∈ n
2

where the inequality is Corollary 6.39 and we used Åf ∗ f (γ) = f (γ)2. The
conclusion of the proof is as in the original analysis (cf. Proposition 6.7, Exer-
cise 1.29):

θ2 − ≤ ≤

∑

γ∈ n
2

f (γ)4 ≤ max
γ∈ n
2

{ f (γ)2} ·

∑

γ∈ n
2
p

f (γ)2 = max
γ∈ n
2

{ f (γ)2},

θ2 − ≤.



and hence there exists γ∗ such that | f (γ∗)| ≥

6.5. Highlight: Fooling 2-polynomials

Recall that a density ϕ is said to be ≤-biased if its correlation with every
2-
linear function f is at most ≤ in magnitude. In the lingo of pseudorandomness,
one says that ϕ fools the class of

2-linear functions:

Denition 6.46. Let ϕ :
of functions

n
2 → . We say that ϕ ≤-fools C if

n

2 → ≥0 be a density function and let C be a class

∣
∣
∣ E
y∼ϕ

[ f (y)] − E

x∼ n
2

[ f (x)]

∣
∣
∣ ≤ ≤

for all f ∈ C .

2

Theorem 6.30 implies that using just O(log(n/≤)) independent random
n
2 → {−1, 1} with
bits, one can generate a density that ≤-fools the class of f :
( f ) ≤ 1. A natural problem in the eld of derandomization is: How
deg
many independent random bits are needed to generate a density which ≤-fools
2-degree at most d? A naive hope might be that ≤-biased
all functions of
densities automatically fool functions of
2-degree d > 1. The next example
shows that this hope fails badly, even for d = 2:

2-degree 2. Let ϕ :

n
2 → {0, 1},
Example 6.47. Recall the inner product mod 2 function, IPn :
2 → ≥0 be the density of the uniform dis-
which has
tribution on the support of IPn. Now IPn is an extremely regular function
(see Example 6.4), and indeed ϕ is a roughly 2−n/2-biased density (see Exer-
cise 6.7). But ϕ is very bad at fooling at least one function of
2-degree 2,
namely IPn itself:

n

[IPn(x)] ≈ 1/2,

E
x∼ n
2

E
y∼ϕ

[IPn(y)] = 1.

Copyright © Ryan O’Donnell, 2014, 2015, 2016, 2017, 2018, 2019, 2020, 2021.



<!-- pdf-page: 161 -->
6.5. Highlight: Fooling

2-polynomials

161



The problem of using few random bits to fool n-bit,

2-degree-d functions
was rst taken up by Luby, Veliˇckovi´c, and Wigderson [LVW93]. They showed
how to generate a fooling distribution using exp(O(
d log(n/d) + log(1/≤))) in-
dependent random bits. There was no improvement on this for 14 years, at
which point Bogdanov and Viola [BV07] achieved O(log(n/≤)) random bits for
d = 2 and O(log n) + exp(poly(1/≤)) random bits for d = 3. In general, they
suggested that
2-degree-d functions might be fooled by the sum of d inde-
pendent draws from a small-bias distribution. Soon thereafter Lovett [Lov08]
showed that a sum of 2d independent draws from a small-bias distribu-
2-degree-d functions can be fooled using just
tion sufces, implying that
2O(d) · log(n/≤) random bits. More precisely, if ϕ is any ≤-biased density on n
2 ,
Lovett showed that

E
y(1),...,y(2d )∼ϕ

[ f (y(1) + · · · + y(2d))] − E
x∼ n
2

[ f (x)]

∣
∣
∣ ≤ O(≤1/4d

).

In other words, the 2d-fold convolution ϕ∗2d density fools functions of
degree d.

2-

The current state of the art for this problem is Viola’s Theorem [Vio09b],
which shows that the original idea of Bogdanov and Viola [BV07] works:
Summing d independent draws from an ≤-biased distribution fools
2-degree-
d polynomials.

Viola’s Theorem. Let ϕ be any ≤-biased density on n
and dene ≤d = 9≤1/2d−1. Then the class of all f :
is ≤d-fooled by the d-fold convolution ϕ∗d; i.e.,

2 , 0 ≤ ≤ ≤ 1. Let d ∈ +
( f ) ≤ d

n
2 → {−1, 1} with deg

2

E
y(1),...,y(d)∼ϕ

[ f (y(1) + · · · + y(d))] − E
x∼ n
2

[ f (x)]

∣
∣
∣ ≤ 9≤1/2d−1

.

∣
∣
∣

∣
∣
∣

In light of Theorem 6.30, Viola’s Theorem implies that one can ≤-fool n-bit
2-degree d using only O(d log n) + O(d2d log(1/≤)) independent

functions of
random bits.

The proof of Viola’s Theorem is an induction on d. To reduce the case
of degree d + 1 to degree d, Viola makes use of a simple concept: directional
derivatives.

Denition 6.48. Let f :
∆y f :

n
2 → 2 is dened by

n

2 → 2 and let y ∈ n

2 . The directional derivative

∆y f (x) = f (x + y) − f (x).

Over

2 we may equivalently write ∆y f (x) = f (x + y) + f (x).

As expected, taking a derivative reduces degree by 1:

Fact 6.49. For any f :

n

2 → 2 and y ∈ n

2 we have deg

(∆y f ) ≤ deg

2

2

( f ) − 1.

Copyright © Ryan O’Donnell, 2014, 2015, 2016, 2017, 2018, 2019, 2020, 2021.



<!-- pdf-page: 162 -->
162

6. Pseudorandomness and 2-polynomials

In fact, we’ll prove a slightly stronger statement:

Proposition 6.50. Let f :
g :

n
2 → 2 have deg
n
2 → 2 by g(x) = f (x + y) − f (x + y′). Then deg

( f ) = d and x y, y′ ∈ n
(g) ≤ d − 1.

2

2

2 . Dene

Proof. In passing from the
2-polynomial representation of f (x) to that
of g(x), each monomial xS of maximal degree d is replaced by (x+ y)S −(x+ y′)S.
Upon expansion the monomials xS cancel, leaving a polynomial of degree at

most d − 1.

We are now ready to give the proof of Viola’s Theorem.

Proof of Viola’s Theorem. The proof is by induction on d. The d = 1 case is
immediate (even without the factor of 9) because ϕ is ≤-biased. Assume that
the theorem holds for general d ≥ 1 and let f :
( f ) ≤
d + 1. We split into two cases, depending on whether the bias of f is large or
small.

n
2 → {−1, 1} have deg

2

Case 1: E[ f ]2 > ≤d. In this case,
∣
∣
∣ E
z∼ϕ∗(d+1)

≤d ·

p

[ f (z)] − E

x∼ n
2

∣
∣
∣

[ f (x)]

< | E[ f ]| ·

∣
∣
∣ E
z∼ϕ∗(d+1)

[ f (z)] − E

x∼ n
2

∣
∣
∣

[ f (x)]

∣
∣
∣

∣
∣
∣

∣
∣
∣

=

=

=

E

x′∼ n

2 ,z∼ϕ∗(d+1)

[ f (x′) f (z)] − E

x′,x∼ n
2

E

y∼ n

2 ,z∼ϕ∗(d+1)

[ f (z + y) f (z)] − E

y,x∼ n
2

[ f (x′) f (x)]

∣
∣
∣

[ f (x + y) f (x)]

∣
∣
∣

E

[∆y f (z)] − E

y,x∼ n
2

y∼ n

2 ,z∼ϕ∗(d+1)
∣
∣
∣ E
z∼ϕ∗(d+1)

≤ E

y∼ n
2

[∆y f (z)] − E

x∼ n
2

[∆y f (x)]
∣

∣
∣

[∆y f (x)

∣
∣
∣

.

For each outcome y = y the directional derivative ∆y f has
2-degree at most d
(Fact 6.49). By induction we know that ϕ∗d ≤d-fools any such polynomial, and
it follows from Exercise 6.29 that ϕ∗(d+1) does too. Thus each quantity in the
expectation over y is at most ≤d, and we conclude
p

∣
∣
∣ E
z∼ϕ∗(d+1)

[ f (z)] − E

[ f (x)]

x∼ n
2

∣
∣
∣ ≤

≤d
p
≤d

=

≤d = 1

3 ≤d+1 ≤ ≤d+1.

Case 2: E[ f ]2 ≤ ≤d. In this case we want to show that Ew∼ϕ∗(d+1)[ f (w)]2 is

nearly as small. By Cauchy–Schwarz,

E
w∼ϕ∗(d+1)

[ f (w)]2 = E

z∼ϕ∗d



= E

z∼ϕ∗d

E
y,y′∼ϕ



[ f (z + y)]

E
y∼ϕ

2

≤ E



E
y∼ϕ


z∼ϕ∗d



[ f (z + y) f (z + y′)]

= E

y,y′∼ϕ

E
z∼ϕ∗d



[ f (z + y)]2

[ f (z + y) f (z + y′)]



.

Copyright © Ryan O’Donnell, 2014, 2015, 2016, 2017, 2018, 2019, 2020, 2021.



<!-- pdf-page: 163 -->
6.6. Exercises and notes

163

For each outcome of y = y, y′ = y′, the function f (z + y) f (z + y′) is of
2-degree
at most d in the variables z, by Proposition 6.50. Hence by induction we have



E
y,y′∼ϕ

E
z∼ϕ∗d

[ f (z + y) f (z + y′)]





≤ E

y,y′∼ϕ

E
x∼ n
2

[ f (x + y) f (x + y′)]

+ ≤d



= E

x∼ n
2
∑

=

[(ϕ ∗ f )(x)2] + ≤d

ϕ(γ)2 f (γ)2 + ≤d

γ∈ n
2

≤ f (0)2 + ≤2

≤ 2≤d + ≤2,

∑

γ6=0

f (γ)2 + ≤d

where the last step used the hypothesis of Case 2. We have thus shown

and hence | E[ f (w)]| ≤ 2

≤d. Since we are in Case 2, | E[ f ]| ≤

p

≤d, and so

E
w∼ϕ∗(d+1)
p

∣
∣
∣ E
w∼ϕ∗(d+1)

[ f (w)]2 ≤ 2≤d + ≤2 ≤ 3≤d ≤ 4≤d,

[ f (w)] − E[ f ]

∣
∣
∣ ≤ 3

p

≤d = ≤d+1,

as needed.



We end this section by discussing the tightness of parameters in Viola’s
Theorem. First, if we ignore the error parameter, then the result is sharp: a
counting argument (see [BV07]) shows that the d-fold convolution of ≤-biased
2-degree d + 1. More explicitly,
densities cannot in general fool functions of
for any d ∈ +, ` ≥ 2d + 1, Lovett and Tzur [LT09] gave an explicit `
2n -biased
density on (`+1)n
→ {−1, 1} of degree d + 1
for which

and an explicit function f :

(`+1)n
2

2

∣
∣
∣ E
w∼ϕ∗d

[ f (w)] − E[ f ]

∣
∣
∣ ≥ 1 −

2d
2n

.

Regarding the error parameter in Viola’s Theorem, it is not known whether
the quantity ≤1/2d−1 can be improved, even in the case d = 2. However, ob-
taining even a modest improvement to ≤1/1.99d (for d as large as log n) would
constitute a major advance since it would imply progress on the notorious
problem of “correlation bounds for polynomials”; see Viola [Vio09a].

6.6. Exercises and notes

6.1 Let f be chosen as in Proposition 6.1. Compute Var[f (S)] for each S ⊆ [n].

6.2 Prove Fact 6.8.
6.3 Show that any nonconstant k-junta has Inf(1−δ)

least one coordinate i.

[ f ] ≥ (1/2−δ/2)k−1/k for at

i

Copyright © Ryan O’Donnell, 2014, 2015, 2016, 2017, 2018, 2019, 2020, 2021.



<!-- pdf-page: 164 -->
164

6. Pseudorandomness and 2-polynomials

6.4 Let ϕ :

n

2 → ≥0 be an ≤-biased density. For each d ∈ + show that the

d-fold convolution ϕ∗d is an ≤d-biased density.

6.5 (a) Show that if f : {−1, 1}n → has ≤-small inuences, then it is

p

≤-

regular.

(b) Show that for all even n there exists f : {−1, 1}n → {−1, 1} that is 2−n/2-

regular but does not have ≤-small inuences for any ≤ < 1/2.

(c) Show that there is a function f : {−1, 1}n → {−1, 1} with ((1 − δ)n−1, δ)-

small stable inuences that is not ≤-regular for any ≤ < 1.

(d) Verify that the function f (x) = x0Majn(x1, . . . , xn) from Example 6.10
[ f ] = Stab1−δ[Majn] for δ ∈ (0, 1), and thus does not

satises Inf(1−δ)
have (≤, δ)-small stable inuences unless ≤ ≥ 1 −

δ.

p

0

(e) Show that the function f : {−1, 1}n+1 → {−1, 1} from part (d) is 1p
n

regular.

-

(f ) Suppose f : {−1, 1}n → has (≤, δ)-small stable inuences. Show that
≤/(1 − δ)k−1.

f is (η, k)-regular for η =



p

≤, 1)-

(g) Show that f has (≤, 1)-small stable inuences if and only if f is (

regular.

(h) Let f : {−1, 1}n → {−1, 1} be monotone. Show that if f is (≤, 1)-regular

then f is ≤-regular and has ≤-small inuences.

6.6 (a) Let f : {−1, 1}n → . Let (J, J) be a partition of [n] and let z ∈ {−1, 1}J.
For z ∼ {−1, 1}J uniformly random, give a formula for Varz[E[ f J|z]]
in terms of f ’s Fourier coefcients. (Hint: Direct application of Corol-
lary 3.22.)

(b) Using the above formula and the probabilistic method, give an alter-

nate proof of the second statement of Proposition 6.12.

6.7 Let ϕ :

n

2 → ≥0 be the density corresponding to the uniform distribution
2 → {0, 1}. Show that ϕ is ≤-biased for ≤ = 2−n/2/(1−

n

on the support of IPn :
2−n/2), but not for smaller ≤.

6.8 Prove Proposition 6.13.

6.9 Compute the

2-polynomial representation of the equality function Equn :

{0, 1}n → {0, 1}, dened by Equn(x) = 1 if and only if x1 = x2 = · · · = xn.

6.10 (a) Let f : {0, 1}n → and let q(x) =

S⊆[n] cS xS be the (unique) multilin-



ear polynomial representation of f over

. Show that

cS =

∑

R⊆S

(−1)|S|−|R| f (R),

where we identify R ⊆ [n] with its 0-1 indicator string. This formula
is sometimes called Möbius inversion.

(b) Prove Proposition 6.21.

Copyright © Ryan O’Donnell, 2014, 2015, 2016, 2017, 2018, 2019, 2020, 2021.



<!-- pdf-page: 165 -->
6.6. Exercises and notes

165

6.11 (Cf. Lemma 3.5.) Let f :

( f ) ≤ k.
Show that Pr[ f (x) 6= 0] ≥ 2−k. (Hint: As in the similar Exercise 3.4, use
induction on n.)

n
2 → 2 be nonzero and suppose deg

2

6.12 Let f : {−1, 1}n → {0, 1}.
(a) Show that deg

2

( f ) ≤ log(sparsity( f )).

(Hint: You will need Exer-

cise 3.7, Corollary 6.22, and Exercise 1.3.)
(b) Suppose f is 2−k-granular. Show that deg
result than part (a), by Exercise 3.32.)

( f ) ≤ k. (This is a stronger

2

6.13 Let f : {−1, 1}n → {−1, 1} be bent, n > 2. Show that deg

( f ) ≤ n/2. (Note

2

that the upper bound n/2 + 1 follows from Exercise 6.12(b).)

6.14 In this exercise you will prove Theorem 6.25.

(a) Suppose p(x) = c0 + cS xS + r(x) is a real multilinear polynomial over
x1, . . . , xn with c0, cS 6= 0, |S| > 2
3 n for all monomials
xT appearing in r(x). Show that after expansion and multilinear
reduction (meaning x2
i
(b) Deduce Theorem 6.25.

7→ 1), p(x)2 contains the term 2c0 cS xS.

3 n, and |T| > 2

6.15 In this exercise you will explore the sharpness of Siegenthaler’s Theorem

and Theorem 6.25.
(a) For all n and k < n − 1, nd an f : {0, 1}n → {0, 1} that is k-resilient and

has deg

( f ) = n − k − 1.

2

(b) For all n ≥ 3, nd an f : {0, 1}n → {0, 1} that is 1st-order correlation

immune and has deg

( f ) = n − 1.
(c) For all n divisible by 3, nd a biased f : {0, 1}n → {0, 1} that is ( 2

2

3 n−1)th-

order correlation immune.

6.16 Prove Proposition 6.27.

6.17 Bent functions come in pairs: Show that if f :
2n/2 f is also a bent function (with domain n
2 ).

n
2 → {−1, 1} is bent, then

6.18 Extend Proposition 6.29 to show that if π is any permutation on n

f (x, y) = IP2n(x, π(y))g(y) is bent.

6.19 Dickson’s Theorem says the following: Any polynomial p :

degree at most 2 can be expressed as

p(x) = `0(x) +

k∑

j=1

` j(x)`′

j(x),

2 , then

n
2 → 2 of

(6.8)

where `0 is an afne function and `1, `′
are linearly indepen-
dent linear functions. Here k depends only on p and is called the “rank” of
n
2 → {−1, 1} dened by g(x) = χ(p(x)) is bent if
p. Show that for n even, g :
and only if k = n/2, if and only if g arises from IPn as in Proposition 6.28.

1, . . . , `k, `′
k

Copyright © Ryan O’Donnell, 2014, 2015, 2016, 2017, 2018, 2019, 2020, 2021.



<!-- pdf-page: 166 -->
166

6. Pseudorandomness and 2-polynomials

6.20 Without appealing to Dickson’s Theorem, prove that the complete qua-
1≤i< j≤n xi x j can be expressed as in (6.8), with k = bn/2c. (Hint:

dratic x 7→
Induction on n, with different steps depending on the parity of n.)



6.21 Dene mod3 : {−1, 1}n → {0, 1} by mod3(x) = 1 if and only if

ible by 3. Derive the Fourier expansion

n

j=1 xi is divis-

mod3(x) = 1

3 + 2

3 (−1/2)n

∑

(−1)(|S| mod 4)/2

p

|S|

3

xS

S⊆[n]
|S| even

and conclude that mod3 is 2
3 (
p
−3
2 )x j.)

p

3

2 )n-regular.

(Hint: Consider

n

j=1(− 1

2 +

6.22 In Theorem 6.30, show that given r, s any xed bit yi can be obtained in

deterministic poly(`) time.

6.23 (a) Slightly modify the construction in Theorem 6.30 to obtain a (2−t −
2−`)-biased density. (Hint: Arrange for pγ to have degree at most n −
1.)
(b) Since

2` is a dimension-` vector space over

2, it has some basis
v1, . . . , v`. Suppose we modify the construction in Theorem 6.30 so that
ϕ is a density on n`
2 , with yi j = 〈enc(v j r i), enc(s)〉 for i ∈ [n], j ∈ [`].
Show that ϕ remains 2−t-biased.
. Let A ⊆ n

2 be a randomly chosen multiset in
which dCn/≤2e elements are included, independently and uniformly. Show
that if C is a large enough constant, then A is ≤-biased except with proba-
bility at most 2−n.

6.24 Fix ≤ ∈ (0, 1) and n ∈

2

6.25 Consider the problem of computing the matrix multiplication C = AB,
where A, B ∈ n×n
. There is an algorithm [LG14] for solving this problem
in time O(nω), where ω < 2.373; however, the algorithm is very compli-
cated. Suppose you are given A, B, and the outcome C′ of running this
algorithm; you want to test that indeed C′ = AB.
(a) Give an algorithm using n random bits and time O(n2) with the fol-
lowing property: If C′ = AB, then the algorithm “accepts” with prob-
ability 1; if C′ 6= AB, then the algorithm “accepts” with probability at
most 1/2. (Hint: Compute C′x and ABx for a random x ∈ n
2 .)

(b) Show how to reduce the number of random bits used to O(log n) at the
expense of making the false acceptance probability 2/3, while keeping
the running time O(n2). (You may use the fact that in Theorem 6.30,
the time required to compute y given r and s is n · polylog(`).)

6.26 Simplify the exposition and analysis of Theorem 6.32 and Corollary 6.33
in the case of k = 2, and show that you can take m to be one less (i.e.,
m = `).

Copyright © Ryan O’Donnell, 2014, 2015, 2016, 2017, 2018, 2019, 2020, 2021.



<!-- pdf-page: 167 -->
6.6. Exercises and notes

167

6.27 Consider the matrix H′ ∈ k×n

n

constructed in Theorem 6.32, and suppose
we delete all rows corresponding to even (nonzero) powers of the α j’s.
Show that H′ retains the property that any sum of at most k columns
of H′ is nonzero in k
for any
n. (Hint: Prove and use that (
sequence of β j ∈ n.) Deduce that the cardinality of A in Corollary 6.33
can be decreased to 2(2n)bk/2c.

j β j)2 =

j β2
j





6.28 Let A ⊆ {−1, 1}n be a multiset and suppose that the probability density φA
is k-wise independent. In this exercise you will prove the lower bound
|A| ≥ Ω(nbk/2c) (for k constant).
(a) Suppose F ⊆ 2[n] is a collection of subsets of [n] such that |S ∪ T| ≤ k
∈ {−1, 1}|A| ⊆ |A| to be the
i∈S ai.
: S ∈ F } is orthonormal and hence

for all S, T ∈ F . For each S ∈ F dene χA
S
real vector with entries indexed by A whose ath entry is aS =
Show that the set of vectors { 1p



χA
S

|A|

|A| ≥ |F |.

(b) Show that we can nd F satisfying |F | ≥
 n−1
(k−1)/2

(k−1)/2
j=0

if k is odd.

|F | ≥

n
j

+





k/2
j=0



n
j

if k is even and

6.29 Let C be a class of functions

f +z ∈ C whenever f ∈ C and z ∈ n
the class of functions of
that ≤-fools C , then ψ ∗ ϕ also ≤-fools C for any density ϕ.

n
2 → that is closed under translation; i.e.,
2 (recall Denition 3.24). An example is
2-degree at most d. Show that if ψ is a density

6.30 Fix an integer ` ≥ 1. In this exercise you will generalize Exercise 3.43 by
showing how to exactly learn 2-polynomials of degree at most `.
(a) Fix p :

n
2 → 2 with deg

(p) ≤ ` and suppose that x(1), . . . , x(m) ∼ n
2
are drawn uniformly and independently from n
2 . Assume that m ≥
C · 2`(n` + log(1/δ)) for 0 < δ ≤ 1/2 and C a sufciently large constant.
n
Show that except with probability at most δ, the only q :
2 → 2
(q) ≤ ` that satises q(x(i)) = p(x(i)) for all i ∈ [m] is q = p.
with deg
(Hint: Exercise 6.11 with q − p.)

2

2

(b) Show that the concept class of all polynomials

n
2 → 2 of degree
at most ` can be learned from random examples only, with error 0,
in time O(n)3`. (Remark: As in Exercise 3.43, since the key step is
solving a linear system, the learning algorithm can also be done in
O(n)ω` time, assuming matrix multiplication can be done in O(nω)
time.)

(c) Extend this learning algorithm so that in running time O(n)3`·log(1/δ)
it achieves success probability at least 1 − δ. (Hint: Similar to Exer-
cise 3.40.)

6.31 In this exercise you will prove Lemma 6.37.

Copyright © Ryan O’Donnell, 2014, 2015, 2016, 2017, 2018, 2019, 2020, 2021.



<!-- pdf-page: 168 -->
168

6. Pseudorandomness and 2-polynomials

(a) Give a poly(n, 2k)·log(1/δ)-time learning algorithm that, given random
2 → 2, determines (except with probabil-

examples from a k-junta n
ity at most δ) if f is a constant function, and if so, which one.

(b) Given access to random examples from a k-junta f :

n
2 → 2, let
P ⊆ [n] be a set of relevant coordinates for f and let z ∈ P
2 . Show
how to obtain M independent random examples from the (k − |P|)-
in time poly(n, 2k) · M · log(1/δ) (except with probability at
junta f
most δ).

P|z

(c) Complete the proof of Lemma 6.37. (Hint: Build a depth-k decision

tree for f .)

6.32 (a) Improve the bound in Lemma 6.38 to ˆ‖ f ˆ‖1≤ − | f (;)|≤ and the bound in
2≤.

Corollary 6.39 to ˆ‖ f ˆ‖2

1≤ − ‖ f ‖2

p

p

(b) Improve the bound in Theorem 6.44 to

θ2 − ≤/

1 − ≤.

6.33 Improve on Theorem 6.44 by a factor of roughly 2 in the case of acceptance
probability near 1. Specically, show that if f passes the Derandomized
BLR Test with probability 1 − δ, then there exists γ∗ ∈ n
2 with | f (γ∗)| ≥
p

p

1 − 2δ − ≤/

1 − ≤.

6.34 Fix an integer k ∈ +. Let ( f s)s∈{0,1}k be a collection of functions indexed
n
2 → . Dene the kth Gowers

by length-k binary sequences, each f s :
“inner product” 〈( f s)s〉U k ∈

by

〈( f s)s〉U k = E

x,y1,...,yk



∏

f s(x +

s∈{0,1}k



yi)

,



i:s i=1

where the k+1 random vectors x, y1, . . . , yk are independent and uniformly
distributed on n
by

2 . Dene the kth Gowers norm of a function f :

n
2 →

‖ f ‖U k = 〈( f , f , . . . , f )〉1/2k
U k ,

where ( f , f , . . . , f ) denotes that all 2k functions in the collection equal f .
(You will later verify that 〈( f , f , . . . , f )〉U k is always nonnegative.)
(a) Check that 〈 f0, f1〉U 1 = E[ f0] E[ f1] and therefore ‖ f ‖2
(b) Check that

U 1 = E[ f ]2.

〈 f00, f10, f01, f11〉U 2 =

∑

γ∈ n
2

f00(γ) f10(γ) f01(γ) f11(γ)

and therefore ‖ f ‖4

4. (Cf. Exercise 1.29(b).)

U 2 = ˆ‖ f ˆ‖4


∏

(c) Show that



〈( f s)s〉U k =

E
y1,...,yk−1

E
x

f s(x +



i:s i=1

yi)

· E
x′

s:sk=0





f s(x′ +



i:s i=1



yi)

,

∏

s:sk=1

(6.9)
where x′ is independent of x, y1, . . . , yk−1 and uniformly distributed.

Copyright © Ryan O’Donnell, 2014, 2015, 2016, 2017, 2018, 2019, 2020, 2021.



<!-- pdf-page: 169 -->
6.6. Exercises and notes

169

(d) Show that 〈( f , f , . . . , f )〉U k is always nonnegative, as promised.
(e) Using (6.9) and Cauchy–Schwarz, show that





〈( f s)s〉U k ≤

〈( f(s1,...,sk−1,0))S〉U k

〈( f(s1,...,sk−1,1))s〉U k .

(f ) Show that

〈( f s)s〉U k ≤

∏

‖ f s‖U k .

(6.10)

(g) Fixing f :

s∈{0,1}k
n
2 → , show that ‖ f ‖U k ≤ ‖ f ‖U k+1.
( f s)s∈{0,1}k+1 dened by f s = f if sk+1 = 0 and f s = 1 if sk+1 = 1.)

(Hint: Consider

(h) Show that ‖ · ‖U k satises the triangle inequality and is therefore a

seminorm. (Hint: First show that

‖ f0 + f1‖2k

U k =

∑

S⊆{0,1}k

〈( f1[s∈S])s∈{0,1}k 〉U k

and then use (6.10).)

(i) Show that ‖·‖U k is in fact a norm for all k ≥ 2; i.e., ‖ f ‖U k = 0 =⇒ f = 0.

2-polynomial representation of a Boolean function f is often
Notes. The
called its algebraic normal form. It seems to have rst been explicitly intro-
duced by Zhegalkin in 1927 [Zhe27].

For functions f :

n → , the idea of ≤-regularity as a pseudorandomness
notion dates back to Chung and Graham [CG92], as does the equivalent com-
binatorial condition Proposition 6.7. (In the context of quasirandom graphs,
the ideas date further back to Thomason [Tho87] and to Chung, Graham,
and Wilson [CGW89].) The idea of treating functions with small (stable) in-
uences as being “generic” has its origins in the work of Kahn, Kalai, and
Linial [KKL88]. The notion was brought to the fore in work on hardness of ap-
proximation – implicitly, by Håstad [Hås96, Hås99], and later more explicitly
by Khot, Kindler, Mossel, and O’Donnell [KKMO07].

The notion of ≤-biased sets (and also (≤, k)-wise independent distributions)
was introduced by Naor and Naor [NN93] (see also the independent work of
Peralta [Per90]). The construction in Theorem 6.30 is due to Alon, Goldre-
ich, Håstad, and Peralta [AGHP92] (as is Exercise 6.23). As noted by Naor
and Naor [NN93], ≤-biased sets are closely related to error-correcting codes
2; indeed, they are equivalent to linear error-correcting in which all
over
pairs of codewords have relative distance in [ 1
2 ≤]. In particular, the
construction in Theorem 6.30 is the concatenation of the well-known Reed–
Solomon and Hadamard codes (see, e.g., MacWilliams and Sloane [MS77]
for denitions). The nonconstructive upper bound in Exercise 6.24 is essen-
tially the Gilbert–Varshamov bound and is close to known lower bound of
) (assuming ≤ ≥ 2−Ω(n)), which follows from the work of McEliece,
Ω(

2 − 1

2 + 1

2 ≤, 1

n
≤2 log(1/≤)

Copyright © Ryan O’Donnell, 2014, 2015, 2016, 2017, 2018, 2019, 2020, 2021.



<!-- pdf-page: 170 -->
170

6. Pseudorandomness and 2-polynomials

Rodemich, Rumsey, and Welch [MRRW77] (see [MS77]). Additionally, con-
structive upper bounds of O( n
≤5/2 ) are known using tools from coding
theory; see the work of Ben-Aroya and Ta-Shma [BT09] and Matthews and
Peachey [MP11].

≤3 ) and O( n5/4

The probabilistic notion of correlation immunity – i.e., condition (2) of
Corollary 6.14 – was rst introduced by Siegenthaler [Sie84]; we further dis-
cuss his work below. Independently and shortly thereafter, Chor, Friedman,
Goldreich, Håstad, Rudich, and Smolensky [CFG+85] introduced the deni-
tion of resilience and also connected it to (0, k)-regularity of the Fourier spec-
trum; i.e., they proved Corollary 6.14. (In the cryptography literature, Corol-
lary 6.14 is called the Xiao–Massey Theorem [XM88].) The work [CFG+85]
also essentially contains Theorem 6.25 and the relevant function from Exam-
ple 6.16; cf. the work of Mossel et al. [MOS04].

The problem of constructing explicit k-wise distributions of small support
arose in different guises in different areas – in the study of orthogonal arrays
(in statistics), error-correcting codes, and algorithmic derandomization. Alon,
Babai, and Itai [ABI85] gave the construction in Theorem 6.32 – in fact, the
stronger one from Exercise 6.27 – based on the analysis of dual BCH codes
in MacWilliams and Sloane [MS77]. The lower bound from Exercise 6.28
is essentially due to Rao [Rao47]; see also independent proofs [CFG+85,
ABI85].

Siegenthaler’s Theorem dates from 1984 [Sie84]. His motivation was the
study of cryptographic stream ciphers in cryptography. In this application, a
short random sequence of bits (“secret key”) is transformed via some scheme
into a very long sequence of pseudorandom bits (“keystream”), which can then
be used as a one-time pad for encryption. A basic component of most schemes
is a linear feedback shift register (LFSR), which can efciently generate long,
fairly statistically-uniform sequences. However, due to its
2-linearity, it
suffers from some simple cryptanalytic attacks. An early idea for combating
this is to take n independent LFSR streams and combine them via some
n
function f :
2 → 2. Effective attacks are possible in such a scheme if f is
correlated with any of its input bits – or indeed (as Siegenthaler pointed out)
any input pair, triple, etc. This led Siegenthaler to dene the probabilistic
notion of correlation-immunity. Although χ[n] is the maximally correlation-
immune function, it is not suitable as a LFSR combining function precisely
because of its
2-linearity; the same is true of any function of low 2-degree.
Siegenthaler precisely captured this tradeoff between correlation-immunity
and 2-degree in his theorem.

Bent functions were named and rst studied by Rothaus around 1966;
he didn’t publish the notion until 1976, however [Rot76], at which point

Copyright © Ryan O’Donnell, 2014, 2015, 2016, 2017, 2018, 2019, 2020, 2021.



<!-- pdf-page: 171 -->
6.6. Exercises and notes

171

there were already several works on subject, see, e.g., [Dil72]. Bent func-
tions have application in cryptography and coding theory; see, e.g., Carlet’s
survey [Car10]. The basic constructions presented in Section 6.3 are due
to Rothaus; the class of bent functions described in Exercise 6.18 is called
the Maiorana–McFarland family. Dickson’s Theorem is from a 1901 publica-
tion [Dic01, Theorem 199]; see also MacWilliams and Sloane [MS77, Theo-
rem 15.4].

Theorem 6.36 is from Mossel et al. [MOS04]; there is an improved al-
gorithm for learning k-juntas that runs in time roughly n.6024kpoly(n), due
to Gregory Valiant [Val12]. Avrim Blum offers a prize of $1,000 for solv-
ing the case of k = log log n in poly(n) time [Blu03]. Theorem 6.42 is due to
Kushilevitz and Mansour [KM93]. The Derandomized BLR Test and The-
orem 6.44 (and Exercise 6.32) are due to Ben-Sasson, Sudan, Vadhan, and
Wigderson [BSSVW03].

The result of Exercise 6.11 is due to Muller [Mul54a, Theorem 6]; deriving
Exercise 6.30 from it and from Blumer et al. [BEHW87] is folklore. The result
of Exercise 6.12(a) is due to Bernasconi and Codenotti [BC99]; Exercise 6.13
is from MacWilliams and Sloane [MS77]. In Exercise 6.25, part (a) is due
to Freivalds [Fre79] and part (b) to Naor and Naor [NN93]. The Gowers
norm and results of Exercise 6.34 are from Gowers [Gow01]. Our proof of the
second statement in Proposition 6.12 was suggested by Noam Lifshitz.

Copyright © Ryan O’Donnell, 2014, 2015, 2016, 2017, 2018, 2019, 2020, 2021.



<!-- pdf-page: 172 -->


<!-- pdf-page: 173 -->
Chapter 7

Property testing,
PCPPs, and CSPs

In this chapter we study several closely intertwined topics: property testing,
probabilistically checkable proofs of proximity (PCPPs), and constraint sat-
isfaction problems (CSPs). All of our work will be centered around the task
of testing whether an unknown Boolean function is a dictator. We begin by
extending the BLR Test to give a 3-query property testing algorithm for the
class of dictator functions. This in turn allows us to give a 3-query testing
algorithm for any property, so long as the right “proof ” is provided. We then in-
troduce CSPs, which are in fact identical to string testing algorithms. Finally,
we explain how dictator tests can be translated into computational complex-
ity results for CSPs, and we sketch the proofs of some of Håstad’s optimal
inapproximability results.

7.1. Dictator testing

In Chapter 1.6 we described the BLR property testing algorithm: Given query
access to an unknown function f : {0, 1}n → {0, 1}, this algorithm queries f on a
few random inputs and approximately determines whether f has the property
of being linear over
2. The eld of property testing for Boolean functions is
concerned with coming up with similar algorithms for other properties. In
general, a “property” can be any collection C of n-bit Boolean functions; it’s
the same as the notion of “concept class” from learning theory. Indeed, before
running an algorithm to try to learn an unknown f ∈ C , one might rst run a
property testing algorithm to try to verify that indeed f ∈ C .

Copyright © Ryan O’Donnell, 2014, 2015, 2016, 2017, 2018, 2019, 2020, 2021.

173



<!-- pdf-page: 174 -->
174

7. Property testing, PCPPs, and CSPs

Let’s encapsulate the key aspects of the BLR linearity test with some

denitions:

Denition 7.1. An r-query function testing algorithm for Boolean functions
f : {0, 1}n → {0, 1} is a randomized algorithm that:

• chooses r (or fewer) strings x(1), . . . , x(r) ∈ {0, 1}n according to some prob-

ability distribution;

• queries f (x(1)), . . . , f (x(r));

• based on the outcomes, decides (deterministically) whether to “accept” f .

Denition 7.2. Let C be a “property” of n-bit Boolean functions, i.e., a collec-
tion of functions {0, 1}n → {0, 1}. We say a function testing algorithm is a local
tester for C (with rejection rate λ > 0) if it satises the following:

• If f ∈ C , then the tester accepts with probability 1.

• For all 0 ≤ ≤ ≤ 1, if dist( f , C ) > ≤ (in the sense of Denition 1.29), then

the tester rejects f with probability greater than λ · ≤.

Equivalently, if the tester accepts f with probability at least 1 − λ · ≤,
then f is ≤-close to C ; i.e., ∃g ∈ C such that dist( f , g) ≤ ≤.

By taking ≤ = 0 in the above denition you see that any local tester gives
a characterization of C : a function is in C if and only if it is accepted by
the tester with probability 1. But a local tester furthermore gives a “robust”
characterization: Any function accepted with probability close to 1 must be
close to satisfying C .

Example 7.3. By Theorem 1.30, the BLR Test is a 3-query local tester for the
property C = { f :

n
2 → 2 | f is linear} (with rejection rate 1).

Remark 7.4. To be pedantic, the BLR linearity test is actually a family of
local testers, one for each value of n. This is a common scenario: We will
usually be interested in testing natural families of properties (C n)n∈ +, where
C n contains functions {0, 1}n → {0, 1}. In this case we need to describe a family
of testers, one for each n. Generally, these testers will “act the same” for
all values of n and will have the property that the rejection rate λ > 0 is a
universal constant independent of n.

There are a number of standard variations of Denition 7.2 that one could
consider. One variation is to allow for an adaptive testing algorithm, mean-
ing that the algorithm can decide how to generate x(t) based on the query
outcomes f (x(1)), . . . , f (x(t−1)). However, in this book we will only consider
nonadaptive testing. Another variation is to relax the requirement that ≤-far
functions be rejected with probability Ω(≤); one could allow for smaller rates
such as Ω(≤2), or Ω(≤/ log n). For simplicity, we will stick with the strict de-
mand that the rejection probability be linear in ≤. Finally, the most common

Copyright © Ryan O’Donnell, 2014, 2015, 2016, 2017, 2018, 2019, 2020, 2021.



<!-- pdf-page: 175 -->
7.1. Dictator testing

175

denition of property testing allows the number of queries to be a function
r(≤) of ≤ but requires that any function ≤-far from C be rejected with proba-
bility at least 1/2. This is easier to achieve than satisfying Denition 7.2; see
Exercise 7.1.

So far we have seen that the property of being linear over

2 is locally
testable. We’ll now spend some time discussing local testability of an even sim-
pler property, the property of being a dictator. In other words, we’ll consider
the property

D = { f : {0, 1}n → {0, 1} | f (x) = xi for some i ∈ [n]}.

As we will see, dictatorship is in some ways the most important property to
be able to test.

We begin with a reminder: Even though D is a subclass of the linear
functions and we have a local tester for linearity, this doesn’t mean we auto-
matically have a local tester for dictatorship. (This is in contrast to learning
theory, where a learning algorithm for a concept class automatically works for
any subclass.) The reason is that the non-dictator linear functions – i.e., χS
for |S| 6= 1 – are at distance 1
2 from D but are accepted by any linearity test
with probability 1.

Still, we could use a linearity test as a rst component of a test for dicta-
torship; this essentially reduces the problem to testing if an unknown lin-
ear function is a dictator. Historically, the rst local testers for dictator-
ship [BGS95, PRS01] worked this way; after testing linearity, they chose
x, y ∼ {0, 1}n uniformly and independently, set z = x ∧ y (the bitwise logical
AND), and tested whether f (z) = f (x) ∧ f (y). The idea is that the only parity
functions that satisfy this “AND test” with probability 1 are the dictators (and
the constant 0). The analysis of the test takes a bit of work; see Exercise 7.8
for details.

Here we will describe a simpler dictatorship test. Recall we have already
seen an important result that characterizes dictatorship: Arrow’s Theorem,
from Chapter 2.5. Furthermore the robust version of Arrow’s Theorem (Corol-
lary 2.60) involves evaluating a 3-candidate Condorcet election under the
impartial culture assumption, and this is the same as querying the election
rule f on 3 correlated random inputs. This suggests a dictatorship testing
component we call the “NAE Test”:

NAE Test. Given query access to f : {−1, 1}n → {−1, 1}:

• Choose x, y, z ∈ {−1, 1}n by letting each triple (xi, yi, zi) be drawn inde-
pendently and uniformly at random from among the 6 triples satisfying
the not-all-equal predicate NAE3 : {−1, 1}3 → {0, 1}.

• Query f at x, y, z.

Copyright © Ryan O’Donnell, 2014, 2015, 2016, 2017, 2018, 2019, 2020, 2021.



<!-- pdf-page: 176 -->
176

7. Property testing, PCPPs, and CSPs

• Accept if NAE3( f (x), f (y), f (z)) is satised.

The NAE Test by itself is almost a 3-query local tester for the property of
being a dictator. Certainly if f is a dictator then the NAE Test accepts with
probability 1. Furthermore, in Chapter 2.5 we proved:

Theorem 7.5 (Restatement of Corollary 2.60). If the NAE Test accepts f with
probability 1 − ≤, then W1[ f ] ≥ 1 − 9
2 ≤, and hence f is O(≤)-close to ±χi for some
i ∈ [n] by the FKN Theorem.

There are two slightly unsatisfactory aspects to this theorem. First, it
gives a local tester only for the property of being a dictator or a negated-
dictator. Second, though the deduction W1[ f ] ≥ 1 − 9
2 ≤ requires only simple
Fourier analysis, the conclusion that f is close to a (negated-)dictator relies
on the non-trivial FKN Theorem. Fortunately we can x both issues simply
by adding in the BLR Test:

Theorem 7.6. Given query access to f : {−1, 1}n → {−1, 1}, perform both the
BLR Test and the NAE Test. This is a 6-query local tester for the property of
being a dictator (with rejection rate .1).

Proof. The rst condition in Denition 7.2 is easy to check: If f : {−1, 1}n →
{−1, 1} is a dictator, then both tests accept f with probability 1. To check
the second condition, x 0 ≤ ≤ ≤ 1 and assume the overall test accepts f with
probability at least 1−.1≤. Our goal is to show that f is ≤-close to some dictator.

Since the overall test accepts with probability at least 1−.1≤, both the BLR
and the NAE tests must individually accept f with probability at least 1 − .1≤.
By the analysis of the NAE Test we deduce that W1[ f ] ≥ 1 − 9
2 · .1≤ = 1 − .45≤.
By the analysis of the BLR Test (Theorem 1.30) we deduce that f is .1≤-close
to some parity function; i.e., f (S∗) ≥ 1 − .2≤ for some S∗ ⊆ [n]. Now if |S∗| 6= 1
we would have

1 =

n∑

k=0

Wk[ f ] ≥ (1 − .45≤) + (1 − .2≤)2 ≥ 2 − .85≤ > 1,

a contradiction. Thus we must have |S∗| = 1 and hence f is .1≤-close to the

dictator χS∗, stronger than what we need.

As you can see, we haven’t been particularly careful about obtaining the
largest possible rejection rate. Instead, we will be more interested in using as
few queries as possible (while maintaining some positive constant rejection
rate). Indeed we now show a small trick which lets us reduce our 6-query
local tester for dictatorship down to a 3-query one. This is best possible since
dictatorship can’t be locally tested with 2 queries (see Exercise 7.6).

BLR+NAE Test. Given query access to f : {−1, 1}n → {−1, 1}:

Copyright © Ryan O’Donnell, 2014, 2015, 2016, 2017, 2018, 2019, 2020, 2021.



<!-- pdf-page: 177 -->
7.1. Dictator testing

177

• With probability 1/2, perform the BLR Test on f .

• With probability 1/2, perform the NAE Test on f .

Theorem 7.7. The BLR+NAE Test is a 3-query local tester for the property of
being a dictator (with rejection rate .05).

Proof. The only observation we need to make is that if the BLR+NAE Test
accepts with probability 1−.05≤ then both the BLR and the NAE tests individ-
ually must accept f with probability at least 1 − .1≤. The result then follows

from the analysis of Theorem 7.6.

Remark 7.8. In general, this trick lets us take the maximum of the query
complexities when we combine tests, rather than the sum (at the expense
of worsening the rejection rate). Suppose we wish to combine t = O(1) dif-
ferent testing algorithms, where the ith tester uses r i queries. We make
an overall test that performs each subtest with probability 1/t. This gives a
max(r1, . . . , r t)-query testing algorithm with the following guarantee: If the
overall test accepts f with probability 1 − λ
t ≤ then every subtest must accept f
with probability at least 1 − λ≤.

We can now explain one reason why dictatorship is a particularly impor-
tant property to be able to test locally. Given the BLR Test for linear functions
it still took us a little thought to nd a local test for the subclass D of dictators.
But given our dictatorship test, it’s easy to give a 3-query local tester for any
subclass of D. (On a related note, Exercise 7.15 asks you to give a 3-query
local tester for any afne subspace of the linear functions.)

Theorem 7.9. Let S be any subclass of n-bit dictators; i.e., let S ⊆ [n] and let

S = {χi : {0, 1}n → {0, 1} | i ∈ S}.

Then there is a 3-query local tester for S (with rejection rate .01).

Proof. Let 1S ∈ {0, 1}n denote the indicator string for the subset S. Given
access to f : {0, 1}n → {0, 1}, the test is as follows:

• With probability 1/2, perform the BLR+NAE Test on f .

• With probability 1/2, apply the local correcting routine of Proposition 1.31

to f on string 1S; accept if and only if the output value is 1.

This test always makes either 2 or 3 queries, and whenever f ∈ S it accepts
with probability 1. Now let 0 ≤ ≤ ≤ 1 and suppose the test accepts f with
probability at least 1 − λ≤, where λ = .01. Our goal will be to show that f is
≤-close to a dictator χi with i ∈ S.

Since the overall test accepts f with probability at least 1−λ≤, the BLR+NAE

Test must accept f with probability at least 1 − 2λ≤. By Theorem 7.7 we may

Copyright © Ryan O’Donnell, 2014, 2015, 2016, 2017, 2018, 2019, 2020, 2021.



<!-- pdf-page: 178 -->
178

7. Property testing, PCPPs, and CSPs

deduce that f is 40λ≤-close to some dictator χi. Our goal is to show that i ∈ S;
this will complete the proof because 40λ≤ ≤ ≤ (by our choice of λ = .01).

So suppose by way of contradiction that i 6∈ S; i.e., χi(1S) = 0. Since f is

40λ≤-close to the parity function χi, Proposition 1.31 tells us that

Pr[locally correcting f on input 1S produces the output χi(1S) = 0] ≥ 1−80λ≤.

On the other hand, since the overall test accepts f with probability at least
1 − λ≤, the second subtest must accept f with probability at least 1 − 2λ≤. This
means

Pr[locally correcting f on input 1S produces the output 0] ≤ 2λ≤.

But this is a contradiction, since 2λ≤ < 1 − 80λ≤ for all 0 ≤ ≤ ≤ 1 (by our choice

of λ = .01). Hence i ∈ S as desired.

7.2. Probabilistically Checkable Proofs of Proximity

In the previous section we saw that every subproperty of the dictatorship
property has a 3-query local tester. In this section we will show that any
property whatsoever has a 3-query local tester – if an appropriate “proof ” is
provided.

To make sense of this statement let’s rst generalize the setting in which
we study property testing. Denitions 7.1 and 7.2 are concerned with testing a
Boolean function f : {0, 1}n → {0, 1} by querying its values on various inputs. If
we think of f ’s truth table as a Boolean string of length N = 2n, then a testing
algorithm simply queries various coordinates of this string. It makes sense to
generalize to the notion of testing properties of N-bit strings, for any length N.
Here a property C will just be a collection C ⊆ {0, 1}N of strings, and we’ll be
concerned with relative Hamming distance dist(w, w′) = 1
N ∆(w, w′) between
strings. For simplicity, we’ll begin to write n instead of N.

Denition 7.10. An r-query string testing algorithm for strings w ∈ {0, 1}n is
a randomized algorithm that:

• chooses r (or fewer) indices i1, . . . , ir ∈ [n] according to some probability

distribution;

• queries wi1
• based on the outcomes, decides (deterministically) whether to “accept” w.

, . . . , wir

;

We may also generalize this denition to testing strings w ∈ Ωn over nite
alphabets Ω of cardinality larger than 2.

Denition 7.11. Let C ⊆ {0, 1}n be a “property” of n-bit Boolean strings. We
say a string testing algorithm is a local tester for C (with rejection rate λ > 0)
if it satises the following:

Copyright © Ryan O’Donnell, 2014, 2015, 2016, 2017, 2018, 2019, 2020, 2021.



<!-- pdf-page: 179 -->
7.2. Probabilistically Checkable Proofs of Proximity

179

• If w ∈ C , then the tester accepts with probability 1.

• For all 0 ≤ ≤ ≤ 1, if dist(w, C ) > ≤, then the tester rejects w with probabil-

ity greater than λ · ≤.

Equivalently, if the tester accepts w with probability at least 1 − λ · ≤,
then w is ≤-close to C ; i.e., ∃w′ ∈ C such that dist(w, w′) ≤ ≤.

Example 7.12. Let Z = {(0, 0, . . . , 0)} ⊆ {0, 1}n be the property of being the all-
zeroes string. Then the following is a 1-query local tester for Z (with rejection
rate 1): Pick a uniformly random index i and accept if wi = 0.

Let E = {(0, 0, . . . , 0), (1, 1, . . . , 1)} ⊆ {0, 1}n be the property of having all co-
ordinates equal. Then the following is a 2-query local tester for E : Pick two
independent and uniformly random indices i and j and accept if wi = w j.
In Exercise 7.4 you are asked to show that if dist(w, E ) = ≤, then this tester
rejects w with probability 1

2 − 1

2 (1 − 2≤)2 ≥ ≤.

Let O = {w ∈ n

2 : w has an odd number of 1’s}. This property does not
have a local tester making few queries.
In fact, in Exercise 7.5 you are
asked to show that any local tester for O must make the maximum number
of queries, n.

As the last example shows, not every property has a local tester making a
small number of queries; indeed, most properties of n-bit strings do not. This
is rather too bad: Imagine that for any large n and any complicated property
C ⊆ {0, 1}n there were an O(1)-query local tester. Then if anyone supplied you
with a string w claiming it satised C , you wouldn’t have to laboriously check
this yourself, nor would you have to trust the supplier; you could simply spot-
check w in a constant number of coordinates and become convinced that w is
(close to being) in C .

But what if, in addition to w ∈ {0, 1}n, you could require the supplier to
give you some additional side information Π ∈ {0, 1}` about w so as to assist
you in testing that w ∈ C ? One can think of Π as a kind of “proof ” that w
satises C . In this case it’s possible that you can spot-check w and Π together
in a constant number of coordinates and become convinced that w is (close
to being) in C – all without having to “trust” the supplier of the string w
and the purported proof Π. These ideas lead to the notion of probabilistically
checkable proofs of proximity (PCPPs).

Denition 7.13. Let C ⊆ {0, 1}n be a property of n-bit Boolean strings and
let ` ∈ . We say that C has an r-query, length-` probabilistically checkable
proof of proximity (PCPP) system (with rejection rate λ > 0) when the following
holds: There exists an r-query testing algorithm T for (n + `)-bit strings,
thought of as pairs w ∈ {0, 1}n and Π ∈ {0, 1}`, such that:

Copyright © Ryan O’Donnell, 2014, 2015, 2016, 2017, 2018, 2019, 2020, 2021.



<!-- pdf-page: 180 -->
180

7. Property testing, PCPPs, and CSPs

• (“Completeness.”) If w ∈ C , then there exists a “proof ” Π ∈ {0, 1}` such

that T accepts with probability 1.

• (“Soundness.”) For all 0 ≤ ≤ ≤ 1, if dist(w, C ) > ≤, then for every “proof ”

Π ∈ {0, 1}` the tester T rejects with probability greater than λ · ≤.
Equivalently, if there exists Π ∈ {0, 1}` that causes T to accept with
probability at least 1 − λ · ≤, then w must be ≤-close to C .

PCPP systems are also known as assisted testers, locally testable proofs, or
assignment testers.

Remark 7.14. A word on the three parameters: We are usually interested in
xing the number of queries r to a very small universal constant (such as 3)
while trying to keep the proof length ` = `(n) relatively small (e.g., poly(n) is
a good goal). We are usually not very concerned with the rejection rate λ so
long as it’s a positive universal constant (independent of n).

Example 7.15. In Example 7.12 we stated that O = {w ∈ n
2 : w1 +· · ·+ wn = 1}
has no local tester making fewer than n queries. But it’s easy to give a 3-query
PCPP system for O with proof length n − 1 (and rejection rate 1). The idea is
to require the proof string Π to contain the partial sums of w:

Π j =

j+1∑

i=1

wi

(mod 2).

The tester will perform one of the following checks, uniformly at random:

Π1 = w1 + w2
Π2 = Π1 + w3
Π3 = Π2 + w4

· · ·

Πn−1 = Πn−2 + wn
Πn−1 = 1

Evidently the tester always makes at most 3 queries. Further, in the “com-
pleteness” case w ∈ O , if Π is a correct list of partial sums then the tester will
accept with probability 1. It remains to analyze the “soundness” case, w 6∈ O .
Here we are signicantly aided by the fact that dist(w, O ) must be exactly 1/n
(since every string is at Hamming distance either 0 or 1 from O ). Thus to
conrm the claimed rejection rate of 1, we only need to observe that if w 6∈ O
then at least one of the tester’s n checks must fail.

This example generalizes to give a very efcient PCPP system for testing
that w satises any xed
2-linear equation. What about testing that w
2-linear equations? This interesting question is
satises a xed system of
explored in Exercise 7.16, which serves as a good warmup for our next result.

Copyright © Ryan O’Donnell, 2014, 2015, 2016, 2017, 2018, 2019, 2020, 2021.



<!-- pdf-page: 181 -->
7.2. Probabilistically Checkable Proofs of Proximity

181

We now extend Theorem 7.9 to show the rather remarkable fact that
any property of n-bit strings has a 3-query PCPP system. (The proof length,
however, is enormous.)

Theorem 7.16. Let C ⊆ {0, 1}n be any class of strings. Then there is a 3-query,
length-22n PCPP system for C (with rejection rate .001).

Proof. Let N = 2n and x an arbitrary bijection ι : {0, 1}n → [N]. The tester
will interpret the string w ∈ {0, 1}n to be tested as an index ι(w) ∈ [N] and will
interpret the 2N -length proof Π as a function Π : {0, 1}N → {0, 1}. The idea
is for the tester to require that Π be the dictator function corresponding to
index ι(w); i.e., χι(w) : {0, 1}N → {0, 1}.

Now under the identication ι, we can think of the string property C as a

subclass of all N-bit dictators, namely

C ′ = {χι(w′) : {0, 1}N → {0, 1} | w′ ∈ C }.

In particular, C ′ is a property of N-bit functions. We can now state the twofold
goal of the tester:

(1) check that Π ∈ C ′;
(2) given that Π is indeed some dictator χι(w′) : {0, 1}N → {0, 1} with w′ ∈ C ,

check that w′ = w.

To accomplish the latter the tester would like to check w j = w′
for a random
j
j ∈ [n]. The tester can query any w j directly but accessing w′
requires a little
j
thought. The trick is to prepare the string

X ( j) ∈ {0, 1}N dened by X ( j)
ι(y)

= yj.

and then to locally correct Π on X ( j) (using Proposition 1.31).

Thus the tester is dened as follows:

(1) With probability 1/2, locally test the function property C ′ using Theo-

rem 7.9.

(2) With probability 1/2, pick j ∼ [n] uniformly at random; locally correct Π

on the string X ( j) and accept if the outcome equals w j.

Note that the tester makes 3 queries in both of the subtests.

Verifying “completeness” of this PCPP system is easy: if w ∈ C and Π is
indeed the (truth table of) χι(w) : {0, 1}N → {0, 1} then the test will accept with
probability 1. It remains to verify the “soundness” condition. Fix w ∈ {0, 1}n,
Π : {0, 1}N → {0, 1}, and 0 ≤ ≤ ≤ 1 and suppose that the tester accepts (w, Π)
with probability at least 1 − λ≤, where λ = .001. Our goal is to show that w is
≤-close to some string w′ ∈ C .

Copyright © Ryan O’Donnell, 2014, 2015, 2016, 2017, 2018, 2019, 2020, 2021.



<!-- pdf-page: 182 -->
182

7. Property testing, PCPPs, and CSPs

Since the overall test accepts with probability at least 1 − λ≤, subtest (1)
above accepts with probability at least 1 − 2λ≤. Thus by Theorem 7.9, Π must
be 200λ≤-close to some dictator χι(w′) with w′ ∈ C . Since dictators are parity
functions, Proposition 1.31 tells us that
∀ j, Pr[locally correcting Π on X ( j) produces χι(w′)(X ( j)) = w′

j] ≥ 1−400λ≤ ≥ 1/2,
(7.1)

where we used 400λ≤ < 400λ ≤ 1/2 by the choice λ = .001.

On the other hand, since the overall test accepts with probability at least

1 − λ≤, subtest (2) above rejects with probability at most 2λ≤. This means


Pr[locally correcting Π on X ( j) doesn’t produce w j]



≤ 2λ≤.

E
j∼[n]

By Markov’s inequality we deduce that except for at most a 4λ≤ fraction of
coordinates j ∈ [n] we have

Pr[locally correcting Π on X ( j) doesn’t produce w j] < 1/2.

Combining this information with (7.1) we deduce that w j = w′
except for at
j
most a 4λ≤ ≤ ≤ fraction of coordinates j ∈ [n]. Since w′ ∈ C we conclude that

dist(w, C) ≤ ≤, as desired.

You may feel that the doubly-exponential proof length 22n in this theorem
is quite bad, but bear in mind there are 22n different properties C . Actually,
giving a PCPP system for every property is a bit overzealous since most prop-
erties are not interesting or natural. A more reasonable goal would be to give
efcient PCPP systems for all “explicit” properties. A good way to formalize
this is to consider properties decidable by polynomial-size circuits. Here we
use the denition of general (De Morgan) circuits from Exercise 4.13. Given
an n-variable circuit C we consider the set of strings which it “accepts” to be
a property,

C = {w ∈ {0, 1}n : C(w) = 1}.

(7.2)

For properties computed by modest-sized circuits C we may hope for PCPP
systems with proof length much less than 22n . We saw such a case in Exam-
ple 7.15.

Another advantage of considering “explicit” properties is that we can de-
ne a notion of constructing a PCPP system, “given” a property. A theorem
of the form “for each explicit property C there exists an efcient PCPP sys-
tem. . . ” may not be useful, practically speaking, if its proof is nonconstructive.
We can formalize the issue as follows:

Denition 7.17. A PCPP reduction is an algorithm which takes as input a
circuit C and outputs the description of a PCPP system for the string prop-
erty C decided by C as in (7.2), where n is the number of inputs to C. If the
output PCPP system always makes r queries, has proof length `(n, size(C))

Copyright © Ryan O’Donnell, 2014, 2015, 2016, 2017, 2018, 2019, 2020, 2021.



<!-- pdf-page: 183 -->
7.3. CSPs and computational complexity

183

(for some function `), and has rejection rate λ > 0, we say that the PCPP
reduction has the same parameters. Finally, the PCPP reduction should run
in time poly(size(C), `).

(We haven’t precisely specied what it means to output the description of
a PCPP system; this will be explained more carefully in Section 7.3. In brief
it means to list – for each possible outcome of the tester’s randomness – which
bits are queried and what predicate of them is used to decide acceptance.)

Looking back at the results on testing subclasses of dictatorship (Theo-
rem 7.9) and PCPPs for any property (Theorem 7.16) we can see they have
the desired sort of “constructive” proofs. In Theorem 7.9 the local tester’s de-
scription depends in a very simple way on the input 1S. As for Theorem 7.16,
it sufces to note that given an n-input circuit C we can write down its truth
table (and hence the property it decides) in time poly(size(C))·2n, whereas the
allowed running time is at least poly(size(C), 22n ). Hence we may state:

Theorem 7.18. There exists a 3-query PCPP reduction with proof length 22n
(and rejection rate .001).

In Exercise 7.18 you are asked to improve this result as follows:

Theorem 7.19. There exists a 3-query PCPP reduction with proof length
2poly(size(C)) (and positive rejection rate).

(The fact that we again have just 3 queries is explained by Exercise 7.12;
there is a generic reduction from any constant number of queries down to 3.)

Indeed, there is a much more dramatic improvement:

The PCPP Theorem. There exists a 3-query PCPP reduction with proof
length poly(size(C)) (and positive rejection rate).

This is (a slightly strengthened version of) the famous “PCP Theorem”
[FGL+96, AS98, ALM+98] from the eld of computational complexity, which
is discussed later in this chapter. Though the PCPP Theorem is far stronger
than Theorem 7.18, the latter is not unnecessary; it’s actually an ingredient
in Dinur’s proof of the PCP Theorem [Din07], being applied only to circuits of
“constant” size. The current state of the art for PCPP length [Din07, BS08]
is highly efcient:

Theorem 7.20. There exists a 3-query PCPP reduction with proof length
size(C) · polylog(size(C)) (and positive rejection rate).

7.3. CSPs and computational complexity

This section is about the computational complexity of constraint satisfaction
problems (CSPs), a fertile area of application for analysis of Boolean functions.

Copyright © Ryan O’Donnell, 2014, 2015, 2016, 2017, 2018, 2019, 2020, 2021.



<!-- pdf-page: 184 -->
184

7. Property testing, PCPPs, and CSPs

To study it we need to introduce a fair bit of background material; in fact, this
section will mainly consist of denitions.

In brief, a CSP is an algorithmic task in which a large number of “vari-
ables” must be assigned “labels” so as to satisfy given “local constraints”. We
start by informally describing some examples:

Example 7.21.

• In the “Max-3-Sat” problem, given is a CNF formula of width at most 3
over Boolean variables x1, . . . , xn. The task is to nd a setting of the
inputs that satises (i.e., makes True) as many clauses as possible.

• In the “Max-Cut” problem, given is an undirected graph G = (V , E). The
task is to nd a “cut” – i.e., a partition of V into two parts – so that as
many edges as possible “cross the cut”.

• In the “Max-E3-Lin” problem, given is a system of linear equations
2, each equation involving exactly 3 variables. The system may in
over
general be overdetermined; the task is to nd a solution which satises
as many equations as possible.

• In the “Max-3-Coloring” problem, given is an undirected graph G =
(V , E). The task is to color each vertex either red, green, or blue so as to
make as many edges as possible bichromatic.

Let’s rephrase the last two of these examples so that the descriptions
have more in common. In Max-E3-Lin we have a set of variables V , to be
assigned labels from the domain Ω = 2. Each constraint is of the form
v1 + v2 + v3 = 0 or v1 + v2 + v3 = 1, where v1, v2, v3 ∈ V . In Max-3-Coloring
we have a set of variables (vertices) V to be assigned labels from the domain
Ω = {red, green, blue}. Each constraint (edge) is a pair of variables, constrained
to be labeled by unequal colors.

We now make formal denitions which encompass all of the above exam-

ples:

Denition 7.22. A constraint satisfaction problem (CSP) over domain Ω
is dened by a nite set of predicates (“types of constraints”) Ψ, with each
ψ ∈ Ψ being of the form ψ : Ωr → {0, 1} for some arity r (possibly different for
different predicates). We say that the arity of the CSP is the maximum arity
of its predicates.

Such a CSP is associated with an algorithmic task called “Max-CSP(Ψ)”,
which we will dene below. First, though, let us see how the CSPs from
Example 7.21 t into the above denition.

• Max-3-Sat: Domain Ω = {True,False}; Ψ contains 14 predicates: the 8
logical OR functions on 3 literals (variables/negated-variables), the 4

Copyright © Ryan O’Donnell, 2014, 2015, 2016, 2017, 2018, 2019, 2020, 2021.



<!-- pdf-page: 185 -->
7.3. CSPs and computational complexity

185

logical OR functions on 2 literals, and the 2 logical OR functions on 1
literal.

• Max-Cut: Domain Ω = {−1, 1}; Ψ = {6=}, where 6=: {−1, 1}2 → {0, 1} is the

“not-equal” predicate.

• Max-E3-Lin: Domain Ω = 2; Ψ contains the two 3-ary predicates

(x1, x2, x3) 7→ x1 + x2 + x3 and (x1, x2, x3) 7→ x1 + x2 + x3 + 1.

• Max-3-Coloring: Domain Ω = {red, green, blue}; Ψ contains just the sin-

gle not-equal predicate 6=: Ω2 → {0, 1}.

Remark 7.23. Let us add a few words about traditional CSP terminology.
Boolean CSPs refer to the case |Ω| = 2. If ψ : {−1, 1}r → {0, 1} is a Boolean pred-
icate we sometimes write “Max-ψ” to refer to the CSP where all constraints
are of the form ψ applied to literals; i.e., Ψ = {ψ(±v1, . . . , ±vr)}. As an example,
Max-E3-Lin could also be called Max-χ[3]. The “E3” in the name Max-E3-Lin
refers to the fact that all constraints involve “E”xactly 3 variables. Thus e.g.
Max-3-Lin is the generalization in which 1- and 2-variable equations are al-
lowed. Conversely, Max-E3-Sat is the special case of Max-3-Sat where each
clause must be of width exactly 3 (a CSP which could also be called Max-OR3).

To formally dene the algorithmic task Max-CSP(Ψ), we begin by dening

its input:

Denition 7.24. An instance (or input) P of Max-CSP(Ψ) over variable set V
is a list (multiset) of constraints. Each constraint C ∈ P is a pair C = (S, ψ),
where ψ ∈ Ψ and where the scope S = (v1, . . . , vr) is a tuple of distinct variables
from V , with r being the arity of ψ. We always assume that each v ∈ V
participates in at least one constraint scope. The size of an instance is the
number of bits required to represent it; writing n = |V | and treating |Ω|, |Ψ|
and the arity of Ψ as constants, the size is between n and O(|P | log n).

Remark 7.25. Let’s look at how the small details of Denition 7.24 affect
input graphs for Max-Cut. Since an instance is a multiset of constraints, this
means we allow graphs with parallel edges. Since each scope must consist
of distinct variables, this means we disallow graphs with self-loops. Finally,
since each variable must participate in at least one constraint, this means in-
put graphs must have no isolated vertices (though they may be disconnected).

Given an assignment of labels for the variables, we are interested in the
number of constraints that are “satised”. The reason we explicitly allow
duplicate constraints in an instance is that we may want some constraints
to be more important than others. In fact it’s more convenient to normalize
by looking at the fraction of satised constraints, rather than the number.
Equivalently, we can choose a constraint C ∼ P uniformly at random and look
at the probability that it is satised. It will actually be quite useful to think

Copyright © Ryan O’Donnell, 2014, 2015, 2016, 2017, 2018, 2019, 2020, 2021.



<!-- pdf-page: 186 -->
186

7. Property testing, PCPPs, and CSPs

of a CSP instance P as a probability distribution on constraints. (Indeed, we
could have more generally dened weighted CSPs in which the constraints
are given arbitrary nonnegative weights summing to 1; however, we don’t
want to worry about the issue of representing, say, irrational weights with
nitely many bits.)

Denition 7.26. An assignment (or labeling) for instance P of Max-CSP(Ψ)
is just a mapping F : V → Ω. For constraint C = (S, ψ) ∈ P we say that F
satises C if ψ(F(S)) = 1. Here we use shorthand notation: if S = (v1, . . . , vr)
then F(S) denotes (F(v1), . . . , F(vr)). The value of F, denoted ValP (F), is the
fraction of constraints in P that F satises:

ValP (F) = E

(S,ψ)∼P

[ψ(F(S))] ∈ [0, 1].

(7.3)

The optimum value of P is

If Opt(P ) = 1, we say that P is satisable.

Opt(P ) = max
F:V →Ω

{ValP (F)}.

Remark 7.27. In the literature on CSPs there is sometimes an unfortunate
blurring between a variable and its assignment. For example, a Max-E3-Lin
instance may be written as

x1 + x2 + x3 = 0
x1 + x5 + x6 = 0
x3 + x4 + x6 = 1;

then a particular assignment x1 = 0, x2 = 1, x3 = 0, x4 = 1, x5 = 1, x6 = 1 may be
given. Now there is confusion: Does x2 represent the name of a variable or
does it represent 1? Because of this we prefer to display CSP instances with
the name of the assignment F present in the constraints. That is, the above
instance would be described as nding F : {x1, . . . , x6} → 2 so as to satisfy as
many as possible of the following:

F(x1) + F(x2) + F(x3) = 0
F(x1) + F(x5) + F(x6) = 0
F(x3) + F(x4) + F(x6) = 1,

Finally, we dene the algorithmic task associated with a CSP:

Denition 7.28. The algorithmic task Max-CSP(Ψ) is dened as follows: The
input is an instance P . The goal is to output an assignment F with as large
a value as possible.

Having dened CSPs, let us make a connection to the notion of a string
testing algorithm from the previous section. The connection is this: CSPs

Copyright © Ryan O’Donnell, 2014, 2015, 2016, 2017, 2018, 2019, 2020, 2021.



<!-- pdf-page: 187 -->
7.3. CSPs and computational complexity

187

and string testing algorithms are the same object. Indeed, consider a CSP
instance P over domain Ω with n variables V . Fix an assignment F : V →
Ω; we can also think of F as a string in Ωn (under some ordering of V ).
Now think of a testing algorithm which chooses a constraint (S, ψ) ∼ P at
random, “queries” the string entry F(v) for each v ∈ S, and accepts if and only
if the predicate ψ(F(S)) is satised. This is indeed an r-query string testing
algorithm, where r is the arity of the CSP; the probability the tester accepts
is precisely ValP (F).

Conversely, let T be some randomized testing algorithm for strings in Ωn.
Assume for simplicity that T’s randomness comes from the uniform distribu-
tion over some sample space U. Now suppose we enumerate all outcomes
in U, and for each we write the tuple of indices S that T queries and the
predicate ψ : Ω|S| → {0, 1} that T uses to make its subsequent accept/reject
decision. Then this list of scope/predicates pairs is precisely an instance of
an n-variable CSP over Ω. The arity of the CSP is equal to the (maximum)
number of queries that T makes and the predicates for the CSP are precisely
those used by the tester in making its accept/reject decisions. Again, the
probability that T accepts a string F ∈ Ωn is equal to the value of F as an
assignment for the CSP. (Our actual denition of string testers allowed any
form of randomness, including, say, irrational probabilities; thus technically
not every string tester can be viewed as a CSP. However, it does little harm
to ignore this technicality.)

In particular, this equivalence between string testers and CSPs lets us
properly dene “outputting the description of a PCPP system” as in Deni-
tion 7.17 of PCPP reductions.

n

Example 7.29. The PCPP system for O = {w ∈ 2 : w1 + · · · + wn = 1} given in
Example 7.15 can be thought of as an instance of the Max-3-Lin CSP over the
2n − 1 variables {w1, . . . , wn, Π1, . . . , Πn−1}. The BLR linearity test for functions
2 → 2 can also be thought of as instance of Max-3-Lin over 2n variables
(recall that function testers are string testers). In this case we identify the
variable set with n
2 ; if n = 2 then the variables are named (0, 0), (0, 1), (1, 0),
and (1, 1); and, if we write F :

2
2 → 2 for the assignment, the instance is

F(0, 0) + F(0, 0) + F(0, 0) = 0

F(0, 1) + F(0, 0) + F(0, 1) = 0

F(1, 0) + F(0, 0) + F(1, 0) = 0

F(1, 1) + F(0, 0) + F(1, 1) = 0

F(0, 0) + F(0, 1) + F(0, 1) = 0

F(0, 1) + F(0, 1) + F(0, 0) = 0

F(1, 0) + F(0, 1) + F(1, 1) = 0

F(1, 1) + F(0, 1) + F(1, 0) = 0

F(0, 0) + F(1, 0) + F(1, 0) = 0

F(0, 1) + F(1, 0) + F(1, 1) = 0

F(1, 0) + F(1, 0) + F(0, 0) = 0

F(1, 1) + F(1, 0) + F(0, 1) = 0

F(0, 0) + F(1, 1) + F(1, 1) = 0

F(0, 1) + F(1, 1) + F(1, 0) = 0

F(1, 0) + F(1, 1) + F(0, 1) = 0

F(1, 1) + F(1, 1) + F(0, 0) = 0.

Cf. Remark 7.27; also, note the duplicate constraints.

We end this section by discussing the computational complexity of nding
high-value assignments for a given CSP – equivalently, nding strings that
make a given string tester accept with high probability. Consider, for example,

Copyright © Ryan O’Donnell, 2014, 2015, 2016, 2017, 2018, 2019, 2020, 2021.



<!-- pdf-page: 188 -->
188

7. Property testing, PCPPs, and CSPs

the task of Max-Cut on n-vertex graphs. Of course, given a Max-Cut instance
one can always nd the optimal solution in time roughly 2n, just by trying all
possible cuts. Unfortunately, this is not very efcient, even for slightly large
values of n. In computational complexity theory, an algorithm is generally
deemed “efcient” if it runs in time poly(n). For some subfamilies of graphs
there are poly(n)-time algorithms for nding the maximum cut, e.g., bipartite
graphs (Exercise 7.14) or planar graphs. However, it seems very unlikely
that there is a poly(n)-time algorithm that is guaranteed to nd an optimal
Max-Cut assignment given any input graph. This statement is formalized by
a basic theorem from the eld of computational complexity:

Theorem 7.30. The task of nding the maximum cut in a given input graph
is “NP-hard”.

We will not formally dene NP-hardness in this book (though see Exer-
cise 7.13 for some more explanation). Roughly speaking it means “at least as
hard as the Circuit-Sat problem”, where “Circuit-Sat” is the following task:
Given an n-variable Boolean circuit C, decide whether or not C is satisable
(i.e., there exists w ∈ {0, 1}n such that C(w) = 1). It is widely believed that
Circuit-Sat does not have a polynomial-time algorithm (this is the “P 6= NP”
conjecture). In fact it is also believed that Circuit-Sat does not have a 2o(n)-
time algorithm.

For essentially all CSPs, including Max-E3-Sat, Max-E3-Lin, and Max-3-
Coloring, nding an optimal solution is NP-hard. This motivates considering
a relaxed goal:

Denition 7.31. Let 0 ≤ α ≤ β ≤ 1. We say that algorithm A is an (α, β)-
approximation algorithm for Max-CSP(Ψ) (pronounced “α out of β approxima-
tion”) if it has the following guarantee: on any instance with optimum value
at least β, algorithm A outputs an assignment of value at least α. In case A is
a randomized algorithm, we only require that its output has value at least α
in expectation.

A mnemonic here is that when the βest assignment has value β, the αlgorithm
gets value α.

Example 7.32. Consider the following algorithm for Max-E3-Lin: Given
an instance, output either the assignment F ≡ 0 or the assignment F ≡ 1,
whichever has higher value. Since either 0 or 1 occurs on at least half of the
instance’s “right-hand sides”, the output assignment will always have value
at least 1
2 , β)-approximation algorithm for any β.
In the case β = 1 one can do better: performing Gaussian elimination is an
efcient (1, 1)-approximation algorithm for Max-E3-Lin (or indeed Max-r-Lin
for any r).

2 . Thus this is an efcient ( 1

Copyright © Ryan O’Donnell, 2014, 2015, 2016, 2017, 2018, 2019, 2020, 2021.



<!-- pdf-page: 189 -->
7.3. CSPs and computational complexity

189

As a far more sophisticated example, Goemans and Williamson [GW95]
showed that there is an efcient (randomized) algorithm which (.878β, β)-
approximates Max-Cut for every β.

Not only is nding the optimal solution of a Max-E3-Sat instance NP-hard,

it’s even NP-hard on satisable instances. In other words:

Theorem 7.33. (1, 1)-approximating Max-E3Sat is NP-hard. The same is true
of Max-3-Coloring.

On the other hand, it’s easy to (1, 1)-approximate Max-3-Lin (Example 7.32)
or Max-Cut (Exercise 7.14). Nevertheless, the “textbook” NP-hardness results
for these problems imply the following:

Theorem 7.34. (β, β)-approximating Max-E3-Lin is NP-hard for any xed
β ∈ ( 1

2 , 1). The same is true of Max-Cut.

In some ways, saying that (1, 1)-distinguishing Max-E3-Sat is NP-hard is
not necessarily that disheartening. For example, if (1 − δ, 1)-approximating
Max-E3-Sat were possible in polynomial time for every δ > 0, you might con-
sider that “good enough”. Unfortunately, such a state of affairs is very likely
ruled out:

Theorem 7.35. There exists a positive universal constant δ0 > 0 such that
(1 − δ0, 1)-approximating Max-E3-Sat is NP-hard.

In fact, Theorem 7.35 is equivalent to the “PCP Theorem” mentioned in
Section 7.2. It follows straightforwardly from the PCPP Theorem, as we now
sketch:

Proof sketch. Let δ0 be the rejection rate in the PCPP Theorem. We want
to show that (1 − δ0, 1)-approximating Max-E3-Sat is at least as hard as the
Circuit-Sat problem. Equivalently, we want to show that if there is an efcient
algorithm A for (1−δ0, 1)-approximating Max-E3-Sat then there is an efcient
algorithm B for Circuit-Sat. So suppose A exists and let C be a Boolean
circuit given as input to B. Algorithm B rst applies to C the PCPP reduction
given by the PCPP Theorem. The output is some arity-3 CSP instance P
over variables w1, . . . , wn, Π1, . . . , Π`, where ` ≤ poly(size(C)). By Exercise 7.12
we may assume that P is an instance of Max-E3-Sat. From the denition
of a PCPP system, it is easy to check (Exercise 7.19) the following: If C is
satisable then Opt(P ) = 1; and, if C is not satisable then Opt(P ) < 1 − δ0.
Algorithm B now runs the supposed (1 − δ0, 1)-approximation algorithm A
on P and outputs “C is satisable” if and only if A nds an assignment of

value at least 1 − δ0.

Copyright © Ryan O’Donnell, 2014, 2015, 2016, 2017, 2018, 2019, 2020, 2021.



<!-- pdf-page: 190 -->
190

7. Property testing, PCPPs, and CSPs

7.4. Highlight: Håstad’s hardness theorems

In Theorem 7.35 we saw that it is NP-hard to (1 − δ0, 1)-approximate Max-
E3Sat for some positive but inexplicit constant δ0. You might wonder how
large δ0 can be. The natural limit here is 1
8 because there is a very simple
algorithm that satises a 7
8 -fraction of the constraints in any Max-E3Sat
instance:

Proposition 7.36. Consider the Max-E3-Sat algorithm that outputs a uni-
formly random assignment F. This is a ( 7

8 , β)-approximation for any β.

Proof. In instance P , each constraint is a logical OR of exactly 3 literals
and will therefore be satised by F with probability exactly 7
8 . Hence in
expectation the algorithm will satisfy a 7


8 -fraction of the constraints.

(It’s also easy to “derandomize” this algorithm, giving a deterministic guaran-
tee of at least 7

8 of the constraints; see Exercise 7.21.)

This algorithm is of course completely brainless – it doesn’t even “look
at” the instance it is trying to approximately solve. But rather remarkably,
it achieves the best possible approximation guarantee among all efcient
algorithms (assuming P 6= NP). This is a consequence of the following 1997
theorem of Håstad [Hås01b], improving signicantly on Theorem 7.35:

Håstad’s 3-Sat Hardness. For any constant δ > 0, it is NP-hard to ( 7
approximate Max-E3-Sat.

8 + δ, 1)-

Håstad gave similarly optimal hardness-of-approximation results for sev-

eral other problems, including Max-E3-Lin:

Håstad’s 3-Lin Hardness. For any constant δ > 0, it is NP-hard to ( 1
δ)-approximate Max-E3-Lin.

2 + δ, 1 −

In this hardness theorem, both the “α” and “β” parameters are optimal;
2 , β)-approximate and also

as we saw in Example 7.32 one can efciently ( 1
(1, 1)-approximate Max-E3-Lin.

The goal of this section is to sketch the proof of the above theorems, mainly
Håstad’s 3-Lin Hardness Theorem. Let’s begin by considering the 3-Sat hard-
ness result.
If our goal is to increase the inexplicit constant δ0 in Theo-
rem 7.35, it makes sense to look at how the constant arises. From the proof
of Theorem 7.35 we see that it’s just the rejection rate in the PCPP Theorem.
We didn’t prove that theorem, but let’s consider its length-22n analogue, Theo-
rem 7.18. The key ingredient in the proof of Theorem 7.18 is the dictator test.
Indeed, if we strip away the few local correcting and consistency checks, we
see that the dictator test component controls both the rejection rate and the
type of predicates output by the PCPP reduction. This observation suggests

Copyright © Ryan O’Donnell, 2014, 2015, 2016, 2017, 2018, 2019, 2020, 2021.



<!-- pdf-page: 191 -->
7.4. Highlight: Håstad’s hardness theorems

191

that to get a strong hardness-of-approximation result for, say, Max-E3-Lin,
we should seek a local tester for dictatorship which (a) has a large rejection
rate, and (b) makes its accept/reject decision using 3-variable linear equation
predicates.

This approach (which of course needs to be integrated with efcient “PCPP
technology”) was suggested in a 1995 paper of Bellare, Goldreich, and Su-
dan [BGS95]. Using it, they managed to prove NP-hardness of (1 − δ0, 1)-
approximating Max-E3-Sat with the explicit constant δ0 = .026. Håstad’s
key conceptual contribution (originally from [Hås96]) was showing that given
known PCPP technology, it sufces to construct a certain kind of relaxed
dictator test. Roughly speaking, dictators should still be accepted with prob-
ability 1 (or close to 1), but only functions which are “very unlike” dictators
need to be rejected with substantial probability. Since this is a weaker re-
quirement than in the standard denition of a local tester, we can potentially
achieve a much higher rejection rate, and hence a much stronger hardness-of-
approximation result.

For these purposes, the most useful formalization of being “very unlike
a dictator” turns out to be “having no notable coordinates” in the sense of
Denition 6.9. We make the following denition which is appropriate for
Boolean CSPs.

Denition 7.37. Let Ψ be a nite set of predicates over the domain Ω =
{−1, 1}. Let 0 < α < β ≤ 1 and let λ : [0, 1] → [0, 1] satisfy λ(≤) → 0 as ≤ → 0.
Suppose that for each n ∈ + there is a local tester for functions f : {−1, 1}n →
{−1, 1} with the following properties:

• If f is a dictator then the test accepts with probability at least β.

• If f has no (≤, ≤)-notable coordinates – i.e., Inf(1−≤)

[ f ] ≤ ≤ for all i ∈ [n] –

i

then the test accepts with probability at most α + λ(≤).

• The tester’s accept/reject decision uses predicates from Ψ; i.e., the tester

can be viewed as an instance of Max-CSP(Ψ).

Then, abusing terminology, we call this family of testers an (α, β)-Dictator-vs.-
No-Notables test using predicate set Ψ.

Remark 7.38. For very minor technical reasons, the above denition should
actually be slightly amended. In this section we freely ignore the amendments,
but for the sake of correctness we state them here. One is a strengthening,
one is a weakening.

• The second condition should be required even for functions f : {−1, 1}n →

[−1, 1]; what this means is explained in Exercise 7.22.

Copyright © Ryan O’Donnell, 2014, 2015, 2016, 2017, 2018, 2019, 2020, 2021.



<!-- pdf-page: 192 -->
192

7. Property testing, PCPPs, and CSPs

• When the tester makes accept/reject decisions by applying ψ ∈ Ψ to
query results f (x(1)), . . . , f (x(r)), it is allowed that the query strings are
not all distinct. (See Exercise 7.31.)

Remark 7.39. It’s essential in this denition that the “error term” λ(≤) = o≤(1)
be independent of n. On the other hand, we otherwise care very little about
the rate at which it tends to 0; this is why we didn’t mind using the same
parameter ≤ in the “(≤, ≤)-notable” hypothesis.

Just as the dictator test was the key component in our PCPP reduction
(Theorem 7.18), Dictator-vs.-No-Notables tests are the key to obtaining strong
hardness-of-approximation results. The following result (essentially proved
in Khot et al. [KKMO07]) lets you obtain hardness results from Dictator-vs.-
No-Notables tests in a black-box way:

Theorem 7.40. Fix a CSP over domain Ω = {−1, 1} with predicate set Ψ. Sup-
pose there exists an (α, β)-Dictator-vs.-No-Notables test using predicate set Ψ.
Then for all δ > 0, it is “UG-hard” to (α + δ, β − δ)-approximate Max-CSP(Ψ).

In other words, the distinguishing parameters of a Dictator-vs.-No-Notables

test automatically translate to the distinguishing parameters of a hardness
result (up to an arbitrarily small δ).

The advantage of Theorem 7.40 is that it reduces a problem about compu-
tational complexity to a purely Fourier-analytic problem, and a constructive
one at that. The theorem has two disadvantages, however. The rst is that
instead of NP-hardness – the gold standard in complexity theory – it merely
gives “UG-hardness”, which roughly means “at least as hard as the Unique-
Games problem”. We leave the denition of the Unique-Games problem to
Exercise 7.27, but sufce it to say it’s not as universally believed to be hard
as Circuit-Sat is. The second disadvantage of Theorem 7.40 is that it only
has β − δ rather than β. This can be a little disappointing, especially when
you are interested in hardness for satisable instances (β = 1), as in Håstad’s
3-Sat Hardness. In his work, Håstad showed that both disadvantages can
be erased provided you construct something similar to, but more complicated
than, an (α, β)-Dictator-vs.-No-Notables test. This is how the Håstad 3-Sat
and 3-Lin Hardness Theorems are proved. Describing this extra complica-
tion is beyond the scope of this book; therefore we content ourselves with the
following theorems:

Theorem 7.41. For any 0 < δ < 1
Notables test which uses logical OR functions on 3 literals as its predicates.

8 , there exists a ( 7

8 + δ, 1)-Dictator-vs.-No-

Theorem 7.42. For any 0 < δ < 1
Notables test using 3-variable

2 , there exists a ( 1

2 , 1 − δ)-Dictator-vs.-No-

2-linear equations as its predicates.

Copyright © Ryan O’Donnell, 2014, 2015, 2016, 2017, 2018, 2019, 2020, 2021.



<!-- pdf-page: 193 -->
7.4. Highlight: Håstad’s hardness theorems

193

Theorem 7.42 will be proved below, while the proof of Theorem 7.41 is
left for Exercise 7.29. By applying Theorem 7.40 we immediately deduce the
following weakened versions of Håstad’s Hardness Theorems:

Corollary 7.43. For any δ > 0, it is UG-hard to ( 7
Max-E3-Sat.

8 + δ, 1 − δ)-approximate

Corollary 7.44. For any δ > 0, it is UG-hard to ( 1
Max-E3-Lin.

2 + δ, 1 − δ)-approximate

Remark 7.45. For Max-E3-Lin, we don’t mind the fact that Theorem 7.40
has β − δ instead of β because our Dictator-vs.-No-Notables test only accepts
dictators with probability 1 − δ anyway. Note that the 1 − δ in Theorem 7.42
cannot be improved to 1; see Exercise 7.7.)

To prove a result like Theorem 7.42 there are two components: the design
of the test, and its analysis. We begin with the design. Since we are looking
for a test using 3-variable linear equation predicates, the BLR Test naturally
suggests itself; indeed, all of its checks are of the form f (x) + f (y) + f (z) = 0.
It also accepts dictators with probability 1. Unfortunately it’s not true that
it accepts functions with no notable coordinates with probability close to 1
2 .
There are two problems: the constant 0 function and “large” parity functions
are both accepted with probability 1, despite having no notable coordinates.
The constant 1 function is easy to deal with: we can replace the BLR Test by
the “Odd BLR Test”.

Odd BLR Test. Given query access to f :

n
2 → 2:

2 and y ∼ n

• Choose x ∼ n
2 independently.
• Choose b ∼ 2 uniformly at random and set z = x + y + (b, b, . . . , b) ∈ n
2 .
• Accept if f (x) + f (y) + f (z) = b.

Note that this test uses both kinds of 3-variable linear equations as its
predicates. For the test’s analysis, we as usual switch to ±1 notation and
think of testing f (x) f (y) f (z) = b. It is easy to show the following (see the
proof of Theorem 7.42, or Exercise 7.15 for a generalization):

Proposition 7.46. The Odd BLR Test accepts f : {−1, 1}n → {−1, 1} with prob-
ability

1

2 + 1

2

∑

S⊆[n]
|S| odd

f (S)3 ≤ 1

2 + 1

2 max
S⊆[n]
|S| odd

{ f (S)}.

This twist rules out the constant 1 function; it passes the Odd BLR Test
with probability 1
2 . It remains to deal with large parity functions. Håstad’s
innovation here was to add a small amount of noise to the Odd BLR Test.
Specically, given a small δ > 0 we replace z in the above test with z′ ∼

Copyright © Ryan O’Donnell, 2014, 2015, 2016, 2017, 2018, 2019, 2020, 2021.



<!-- pdf-page: 194 -->
194

7. Property testing, PCPPs, and CSPs

N1−δ(z); i.e., we ip each of its bits with probability δ/2. If f is a dictator, then
there is only a δ/2 chance this will affect the test. On the other hand, if f is a
parity of large cardinality, the cumulative effect of the noise will destroy its
chance of passing the linearity test. Note that parities of small odd cardinality
will also pass the test with probability close to 1; however, we don’t need to
worry about them since they have notable coordinates. We can now present
Håstad’s Dictator-vs.-No-Notables test for Max-E3-Lin.

Proof of Theorem 7.42. Given a parameter 0 < δ < 1, dene the following
test, which uses Max-E3-Lin predicates:

Håstadδ Test. Given query access to f : {−1, 1}n → {−1, 1}:
• Choose x, y ∼ {−1, 1}n uniformly and independently.
• Choose bit b ∼ {−1, 1} uniformly and set z = b · (x ◦ y) ∈ {−1, 1}n (where ◦

denotes entry-wise multiplication).

• Choose z′ ∼ N1−δ(z).
• Accept if f (x) f (y) f (z′) = b.

We will show that this is a ( 1
let us analyze the test assuming b = 1.

2 , 1 − δ/2)-Dictator-vs.-No-Notables test. First,

Pr[Håstadδ Test accepts f | b = 1] = E[ 1
2 + 1
2 + 1
2 + 1

= 1

= 1

= 1

2

2 f (x) f (y) f (z′)]

2 + 1
2 E[ f (x) · f (y) · T1−δ f (x ◦ y)]]
[ f (x) · ( f ∗ T1−δ f )(x)]
2 E
x
∑

f (S) · ·f ∗ T1−δ f (S)

= 1

2 + 1

2

S⊆[n]
∑

S⊆[n]

(1 − δ)|S| f (S)3.

On the other hand, when b = −1 we take the expectation of 1
and note that z′ is distributed as N−(1−δ)(x ◦ y). Thus

2 − 1

2 f (x) f (y) f (z′)

Pr[Håstadδ Test accepts f | b = −1] = 1

2 − 1

2

Averaging the above two results we deduce

∑

S⊆[n]

(−1)|S|(1 − δ)|S| f (S)3.

Pr[Håstadδ Test accepts f ] = 1

2 + 1

2

∑

|S| odd

(1 − δ)|S| f (S)3.

(7.4)

(Incidentally, by taking δ = 0 here we obtain the proof of Proposition 7.46.)

From (7.4) we see that if f is a dictator, f = χS with |S| = 1, then it is
accepted with probability 1 − δ/2. (It’s also easy to see this directly from the
denition of the test.) To complete the proof that we have a ( 1
2 , 1−δ/2)-Dictator-
vs.-No-Notables test, we need to bound the probability that f is accepted given

Copyright © Ryan O’Donnell, 2014, 2015, 2016, 2017, 2018, 2019, 2020, 2021.



<!-- pdf-page: 195 -->
7.5. Exercises and notes

that it has (≤, ≤)-small stable inuences. More precisely, assuming
∑

(1 − ≤)|S|−1 f (S)2 ≤ ≤

for all i ∈ [n]

Inf(1−≤)
i

[ f ] =

S3i

195

(7.5)

we will show that

Pr[Håstadδ Test accepts f ] ≤ 1

2 + 1

2

p

≤, provided ≤ ≤ δ.

(7.6)

This is sufcient because we can take λ(≤) in Denition 7.37 to be

λ(≤) =



p

≤

1
2
1
2

for ≤ ≤ δ,

for ≤ > δ.

Now to obtain (7.6), we continue from (7.4):

Pr[Håstadδ Test accepts f ] ≤ 1

2 + 1

2 max
|S| odd

≤ 1

2 + 1

2 max
|S| odd


{(1 − δ)|S| f (S)} ·

{(1 − δ)|S| f (S)}

∑

f (S)2

|S| odd

≤ 1

2 + 1

2

≤ 1

2 + 1

2

≤ 1

2 + 1

2

{(1 − δ)2|S| f (S)2}

{(1 − δ)|S|−1 f (S)2}

max
|S| odd

max
|S| odd





max
i∈[n]

{Inf(1−δ)
i

[ f ]},

where we used that |S| odd implies S nonempty. And the above is indeed at
most 1


≤ provided ≤ ≤ δ, by (7.5).

p

2 + 1

2

7.5. Exercises and notes

7.1 Suppose there is an r-query local tester for property C with rejection
rate λ. Show that there is a testing algorithm that, given inputs 0 <
≤, δ ≤ 1/2, makes O( r log(1/δ)
) (nonadaptive) queries to f and satises the
following:

λ≤

• If f ∈ C , then the tester accepts with probability 1.
• If f is ≤-far from C , then the tester accepts with probability at

most δ.

7.2 Let M = {(x, y) ∈ {0, 1}2n : x = y}, the property that a string’s rst half
matches its second half. Give a 2-query local tester for M with rejection
rate 1. (Hint: Locally test that x ⊕ y = (0, 0, . . . , 0).)

7.3 Reduce the proof length in Example 7.15 to n − 2.

7.4 Verify the claim from Example 7.12 regarding the 2-query tester for the
property that a string has all its coordinates equal. (Hint: Use ±1 nota-
tion.)

Copyright © Ryan O’Donnell, 2014, 2015, 2016, 2017, 2018, 2019, 2020, 2021.



<!-- pdf-page: 196 -->
196

7. Property testing, PCPPs, and CSPs

7.5 Let O = {w ∈ n

2 : w has an odd number of 1’s}. Let T be any (n − 1)-query
string testing algorithm that accepts every w ∈ O with probability 1. Show
that T in fact accepts every string v ∈ n
2 with probability 1 (even though
dist(w, O ) = 1
n > 0 for half of all strings w). Thus locally testing O re-
quires n queries.

7.6 Let T be a 2-query testing algorithm for functions {−1, 1}n → {−1, 1}. Sup-
pose that T accepts every dictator with probability 1. Show that it also
accepts Majn′ with probability 1 for every odd n′ ≤ n. This shows that
there is no 2-query local tester for dictatorship assuming n > 2. (Hint:
You’ll need to enumerate all predicates on up to 2 bits.)

7.7 For every α < 1, show that there is no (α, 1)-Dictator-vs.-No-Notables test

using Max-E3-Lin predicates. (Hint: Consider large odd parities.)

7.8 (a) Consider the following 3-query testing algorithm for f : {0, 1}n → {0, 1}.
Let x, y ∼ {0, 1}n be independent and uniformly random, dene z ∈
{0, 1}n by zi = xi ∧ yi for each i ∈ [n], and accept if f (x) ∧ f (y) = f (z).
Let pk be the probability that this test accepts a parity function χS :
{0, 1}n → {0, 1} with |S| = k. Show that p0 = p1 = 1 and that in general
pk ≤ 1
4 −
1
4 (−1)k)2−k. (Hint: It sufces to consider k = n and then compute the
correlation of χ{1,...,n} ∧ χ{n+1,...,2n} with the bent function IP2n.)

In fact, you might like to show that pk = 1

2 + 2−|S|.

2 + ( 3

(b) Show how to obtain a 3-query local tester for dictatorship by combin-
ing the following subtests: (i) the Odd BLR Test; (ii) the test from
part (a).

7.9 Obtain the largest explicit rejection rate in Theorem 7.7 that you can. You
might want to return to the Fourier expressions arising in Theorem 1.30
and 2.56, as well as Exercise 1.28. Can you improve your bound by doing
the BLR and NAE Tests with probabilities other than 1/2, 1/2?

7.10 (a) Say that A is an (α, β)-distinguishing algorithm for Max-CSP(Ψ) if
it outputs ‘YES’ on instances with value at least β and outputs ‘NO’
on instances with value strictly less than α. (On each instance with
value in [α, β), algorithm A may have either output.) Show that if
there is an efcient (α, β)-approximation algorithm for Max-CSP(Ψ),
then there is also an efcient (α, β)-distinguishing algorithm for Max-
CSP(Ψ).

(b) Consider Max-CSP(Ψ), where Ψ be a class of predicates that is closed
under restrictions (to nonconstant functions); e.g., Max-3-Sat. Show
that if there is an efcient (1, 1)-distinguishing algorithm, then there
is also an efcient (1, 1)-approximation algorithm. (Hint: Try out all
labels for the rst variable and use the distinguisher.)

7.11 (a) Let φ be a CNF of size s and width w ≥ 3 over variables x1, . . . , xn.
Show that there is an “equivalent” CNF φ′ of size at most (w −2)s and

Copyright © Ryan O’Donnell, 2014, 2015, 2016, 2017, 2018, 2019, 2020, 2021.



<!-- pdf-page: 197 -->
7.5. Exercises and notes

197

width 3 over the variables x1, . . . , xn plus auxiliary variables Π1, . . . , Π`,
with ` ≤ (w − 3)s. Here “equivalent” means that for every x such that
φ(x) = True there exists Π such that φ′(x, Π) = True; and, for every x
such that φ(x) = False we have φ′(x, Π) = False for all Π.

(b) Extend the above so that every clause in φ′ has width exactly 3 (the

size may increase by O(s)).

7.12 Suppose there exists an r-query PCPP reduction R1 with rejection rate λ.
Show that there exists a 3-query PCPP reduction R2 with rejection rate
at least λ/(r2r). The proof length of R2 should be at most r2r · m plus the
proof length of R1 (where m is the description-size of R1’s output) and
the predicates output by the reduction should all be logical ORs applied
to exactly three literals. (Hint: Exercises 4.1, 7.11.)

7.13 (a) Give a polynomial-time algorithm R that takes as input a general
Boolean circuit C and outputs a width-3 CNF formula φ with the
following guarantee: C is satisable if and only if φ is satisable.
(Hint: Introduce a variable for each gate in C.)

(b) The previous exercise in fact formally justies the following state-
ment: “(1, 1)-distinguishing Max-3-Sat is NP-hard”. (See Exercise 7.10
for the denition of (1, 1)-distinguishing.) Argue that, indeed, if (1, 1)-
distinguishing (or (1, 1)-approximating) Max-3-Sat is in polynomial
time, then so is Circuit-Sat.

(c) Prove Theorem 7.33. (Hint: Exercise 7.11(b).)

7.14 Describe an efcient (1, 1)-approximation algorithm for Max-Cut.

7.15 (a) Let H be any subspace of

n
2 → {−1, 1} | γ ∈ H⊥}.
Give a 3-query local tester for H with rejection rate 1. (Hint: Similar
to BLR, but with 〈ϕH ∗ f , f ∗ f 〉.)

n
2 and let H = {χγ :

(b) Generalize to the case that H is any afne subspace of

n
2 .

7.16 Let A be any afne subspace of

2 . Construct a 3-query, length-2n PCPP
system for A with rejection rate a positive universal constant.
(Hint:
2 , the tester should expect the proof Π ∈ {−1, 1}2n to encode
Given w ∈ n
the truth table of χw. Use Exercise 7.15 and also a consistency check
based on local correcting of Π at e i, where i ∈ [n] is uniformly random.)

n

7.17 (a) Give a 3-query, length-O(n) PCPP system (with rejection rate a posi-
2 : IPn(w) = 1}, where IPn

tive universal constant) for the class {w ∈ n
is the inner product mod 2 function (n even).

(b) Do the same for the complete quadratic function CQn from Exer-

cise 1.1. (Hint: Exercise 4.13.)

7.18 In this exercise you will prove Theorem 7.19.

(a) Let D ∈ n×n

be a nonzero matrix and suppose x, y ∼ n
2 are uniformly
random and independent. Show that Pr[yD x 6= 0] ≥ 1
4 .

2

Copyright © Ryan O’Donnell, 2014, 2015, 2016, 2017, 2018, 2019, 2020, 2021.



<!-- pdf-page: 198 -->
198

7. Property testing, PCPPs, and CSPs

2

(b) Let γ ∈ n

. Suppose x, y ∼ n

2 and Γ ∈ n×n

2 are uniformly random and
independent. Show that Pr[(γx)(γ y) = Γ • (x y)] is 1 if Γ = γγ and
is at most 3
i, j Bi jCi j
4 otherwise. Here we use the notation B • C =
for matrices B, C ∈ n×n



2

.

(c) Suppose you are given query access to two functions ` :

n
2 → 2 and
n×n
q :
2 → 2. Give a 4-query testing algorithm with the following
two properties (for some universal constant λ > 0): (i) if ` = χγ and
q = χγγ for some γ ∈ n
2 , the test accepts with probability 1; (ii) for
all 0 ≤ ≤ ≤ 1, if the test accepts with probability at least 1 − γ · ≤, then
there exists some γ ∈ n
2 such that ` is ≤-close to χγ and q is ≤-close
to χγγ . (Hint: Apply the BLR Test to ` and q, and use part (b) with
local correcting on q.)

(d) Let L be a list of homogenous degree-2 polynomial equations over vari-
i, j=1 ci jwiw j = b
ables w1, . . . , wn ∈ 2. (Each equation is of the form
for constants b, ci j ∈ 2; we remark that w2
= wi.) Dene the string
i
property L = {w ∈ n
2 : w satises all equations in L}. Give a 4-query,
length-(2n + 2n2) PCPP system for L (with rejection rate a positive
universal constant). (Hint: The tester should expect the truth table of
χw and χww. You will need part (c) as well as Exercise 7.15 applied
to “q”.)

n

(e) Complete the proof of Theorem 7.19. (Hints: given w ∈ {0, 1}n, the
tester should expect a proof consisting of all gate values ¯w ∈ {0, 1}size(C)
in C’s computation on w, as well as truth tables of χ ¯w and χ ¯w ¯w.
Show that ¯w being a valid computation of C is encodable with a list
of homogeneous degree-2 polynomial equations. Add a consistency
check between w and ¯w using local correcting, and reduce the number
of queries to 3 using Exercise 7.12.)

7.19 Verify the connection between Opt(P ) and C’s satisability stated in the
proof sketch of Theorem 7.35. (Hint: Every string w is 1-far from the
empty property.)

7.20 A randomized assignment for an instance P of a CSP over domain Ω is a
mapping F that labels each variable in V with a probability distribution
over domain elements. Given a constraint (S, ψ) with S = (v1, . . . , vr), we
write ψ(F(S)) ∈ [0, 1] for the expected value of ψ(F(v1), . . . , F(vr)). This is
simply the probability that ψ is satised when one actually draws from
the domain-distributions assigned by F. Finally, we dene the value of F
to be ValP (F) = E(S,ψ)∼P [ψ(F(S))].
(a) Suppose that A is a deterministic algorithm that produces a random-
ized assignment of value α on a given instance P . Show a simple
modication to A that makes it a randomized algorithm that pro-
duces a (normal) assignment whose value is α in expectation. (Thus,

Copyright © Ryan O’Donnell, 2014, 2015, 2016, 2017, 2018, 2019, 2020, 2021.



<!-- pdf-page: 199 -->
7.5. Exercises and notes

199

in constructing approximation algorithms we may allow ourselves to
output randomized assignments.)

(b) Let A be the deterministic Max-E3-Sat algorithm that on every in-
stance outputs the randomized assignment that assigns the uniform
distribution on {0, 1} to each variable. Show that this is a ( 7
8 , β)-
approximation algorithm for any β. Show also that the same algo-
rithm is a ( 1
2 , β)-approximation algorithm for Max-3-Lin.
(c) When the domain Ω is {−1, 1}, we may model a randomized assign-
ment as a function f : V → [−1, 1]; here f (v) = µ is interpreted as the
unique probability distribution on {−1, 1} which has mean µ. Now
given a constraint (S, ψ) with S = (v1, . . . , vr), show that the value of
f on this constraint is in fact ψ( f (v1), . . . , f (vr)), where we identify
ψ : {−1, 1}r → {0, 1} with its multilinear (Fourier) expansion.
(Hint:
Exercise 1.4.)

(d) Let Ψ be a collection of predicates over domain {−1, 1}, and dene
ν = minψ∈Ψ{ ψ(;)}. Show that outputting the randomized assignment
f ≡ 0 is an efcient (ν, β)-approximation algorithm for Max-CSP(Ψ).

7.21 Let F be a randomized assignment of value α for CSP instance P (as
in Exercise 7.20). Give an efcient deterministic algorithm that outputs
a usual assignment F of value at least α. (Hint: Try all possible label-
ings for the rst variable and compute the expected value that would be
achieved if F were used for the remaining variables. Pick the best label
for the rst variable and repeat.)

7.22 Given a local tester for functions f : {−1, 1}n → {−1, 1}, we can interpret
it also as a tester for functions f : {−1, 1}n → [−1, 1]; simply view the
tester as a CSP and view the acceptance probability as the value of
f when treated as a randomized assignment (as in Exercise 7.20(c)).
Equivalently, whenever the tester “queries” f (x), imagine that what is re-
turned is a random bit b ∈ {−1, 1} whose mean is f (x). This interpretation
completes Denition 7.37 of Dictator-vs.-No-Notables tests for functions
f : {−1, 1}n → [−1, 1] (see Remark 7.38). Given this denition, verify that
the Håstadδ Test is indeed a ( 1
2 , 1−δ)-Dictator-vs.-No-Notables test. (Hint:
Show that (7.4) still holds for functions f : {−1, 1}n → [−1, 1]. There is only
one subsequent inequality that uses that f ’s range is {−1, 1}, and it still
holds with range [−1, 1].)

7.23 Let Ψ be a nite set of predicates over domain Ω = {−1, 1} that is closed
under negating variables. (An example is the scenario of Max-ψ from Re-
mark 7.23.) In this exercise you will show that Dictator-vs.-No-Notables
tests using Ψ may assume f : {−1, 1}n → [−1, 1] is odd without loss of
generality.

Copyright © Ryan O’Donnell, 2014, 2015, 2016, 2017, 2018, 2019, 2020, 2021.



<!-- pdf-page: 200 -->
200

7. Property testing, PCPPs, and CSPs

(a) Let T be an (α, β)-Dictator-vs.-No-Notables test using predicate set Ψ
that works under the assumption that f : {−1, 1}n → [−1, 1] is odd.
Modify T as follows: Whenever it is about to query f (x), with proba-
bility 1
2 let it use − f (−x). Call
the modied test T′. Show that the probability T′ accepts an arbitrary
f : {−1, 1}n → [−1, 1] is equal to the probability T accepts f odd (recall
Exercise 1.8).

2 let it use f (x) and with probability 1

(b) Prove that T′ is an (α, β)-Dictator-vs.-No-Notables test using predi-

cate set Ψ for functions f : {−1, 1}n → [−1, 1].

7.24 This problem is similar to Exercise 7.23 in that it shows you may assume
that Dictator-vs.-No-Notables tests are testing “smoothed” functions of
the form T1−δh for h : {−1, 1}n → [−1, 1], so long as you are willing to
lose O(δ) in the probability that dictators are accepted.
(a) Let U be an (α, β)-Dictator-vs.-No-Notables test using an arity-r pred-
icate set Ψ (over domain {−1, 1}) which works under the assumption
that the function f : {−1, 1}n → [−1, 1] being tested is of the form T1−δh
for h : {−1, 1}n → [−1, 1]. Modify U as follows: whenever it is about
to query f (x), let it draw y ∼ N1−δ(x) and use f (y) instead. Call the
modied test U ′. Show that the probability U ′ accepts an arbitrary
h : {−1, 1}n → [−1, 1] is equal to the probability U accepts T1−δh.
(b) Prove that U ′ is an (α, β − rδ/2)-Dictator-vs.-No-Notables test using

predicate set Ψ.

7.25 Give a slightly alternate proof of Theorem 7.42 by using the original

BLR Test analysis and applying Exercises 7.23, 7.24.

7.26 Show that when using Theorem 7.40, it sufces to have a “Dictators-
[ f ] in Denition 7.37

vs.-No-Inuentials test”, meaning replacing Inf(1−≤)
with just Infi[ f ]. (Hint: Exercise 7.24.)

i

7.27 For q ∈ +, Unique-Games(q) refers to the arity-2 CSP with domain Ω =
[q] in which all q! “bijective” predicates are allowed; here ψ is “bijective” if
there is a bijection π : [q] → [q] such that ψ(i, j) = 1 iff π( j) = i. Show that
(1, 1)-approximating Unique-Games(q) can be done in polynomial time.
(The Unique Games Conjecture of Khot [Kho02] states that for all δ > 0
there exists q ∈ + such that (δ, 1 − δ)-approximating Unique-Games(q)
is NP-hard.)

7.28 In this problem you will show that Corollary 7.43 actually follows directly

from Corollary 7.44.
(a) Consider the

2-linear equation v1 + v2 + v3 = 0. Exhibit a list of 4
clauses (i.e., logical ORs of literals) over the variables such that if the
equation is satised, then so are all 4 clauses, but if the equation is
not satised, then at most 3 of the clauses are. Do the same for the
equation v1 + v2 + v3 = 1.

Copyright © Ryan O’Donnell, 2014, 2015, 2016, 2017, 2018, 2019, 2020, 2021.



<!-- pdf-page: 201 -->
7.5. Exercises and notes

201

(b) Suppose that for every δ > 0 there is an efcient algorithm for ( 7

8 +
δ, 1 − δ)-approximating Max-E3-Sat. Give, for every δ > 0, an efcient
algorithm for ( 1
2 + δ, 1 − δ)-approximating Max-E3-Lin.
(c) Alternatively, show how to transform any (α, β)-Dictator-vs.-No-Notables

test using Max-E3-Lin predicates into a ( 3
Notables test using Max-E3-Sat predicates.

4 + 1

4 α, β)-Dictator-vs.-No-

7.29 In this exercise you will prove Theorem 7.41.

(a) Recall the predicate OXR from Exercise 1.1. Fix a small 0 < δ < 1. The
remainder of the exercise will be devoted to constructing a ( 3
4 + δ/4, 1)-
Dictator-vs.-No-Notables test using Max-OXR predicates. Show how
to convert this to a ( 7
8 +δ/8, 1)-Dictator-vs.-No-Notables test using Max-
E3-Sat predicates. (Hint: Similar to Exercise 7.28(c).)

(b) By Exercise 7.23, it sufces to construct a ( 3

4 + δ/4, 1)-Dictator-vs.-No-
Notables test using the OXR predicate assuming f : {−1, 1}n → [−1, 1]
is odd. Håstad tests OXR( f (x), f (y), f (z)) where x, y, z ∈ {−1, 1}n are
chosen randomly as follows: For each i ∈ [n] (independently), with
probability 1 − δ choose (xi, yi, zi) uniformly subject to xi yi zi = −1,
and with probability δ choose (xi, yi, zi) uniformly subject to yi zi = −1.
Show that the probability this test accepts an odd f : {−1, 1}n → [−1, 1]
is

3

4 − 1

4 Stab−δ[ f ] − 1

4

f (S)2 E

J⊆1−δS

[(−1)|J| f (J)],

(7.7)

∑

S⊆[n]

where J ⊆1−δ S denotes that J is a (1 − δ)-random subset of S in
the sense of Denition 4.15. In particular, show that dictators are
accepted with probability 1.

(c) Upper-bound (7.7) by

3

4 + δ/4 + 1

4



(1 − δ)t + 1
4

∑

|S|≤t

f (S)2 E

J⊆1−δS

[| f (J)|],

or something stronger. (Hint: Cauchy–Schwarz.)

(d) Complete the proof that this is a ( 3

4 + δ/4, 1)-Dictator-vs.-No-Notables

test, assuming f is odd.

7.30 In this exercise you will prove Theorem 7.40. Assume there exists an
(α, β)-Dictator-vs.-No-Notables test T using predicate set Ψ over domain
{−1, 1}. We dene a certain efcient algorithm R, which takes as input
an instance G of Unique-Games(q) and outputs an instance P of Max-
CSP(Ψ). For simplicity we refer to the variables V of the Unique-Games
instance G as “vertices” and its constraints as “edges”. We also assume
that when G is viewed as an undirected graph, it is regular. (By a result of
Khot–Regev [KR08] this assumption is without loss of generality for the
purposes of the Unique Games Conjecture.) The Max-CSP(Ψ) instance P
output by algorithm R will have variable set V × {−1, 1}q, and we write

Copyright © Ryan O’Donnell, 2014, 2015, 2016, 2017, 2018, 2019, 2020, 2021.



<!-- pdf-page: 202 -->
202

7. Property testing, PCPPs, and CSPs

assignments for it as collections of functions ( fv)v∈V , where f : {−1, 1}q →
{−1, 1}. The draw of a random of constraint for P is dened as follows:

• Choose u ∈ V uniformly at random.
• Draw a random constraint from the test T; call it ψ( f (x(1)), . . . , f (x(r))).
• Choose r random “neighbors” v1, . . . , vr of u in G , independently
and uniformly. (By a neighbor of u, we mean a vertex v such that
either (u, v) or (v, u) is the scope of a constraint in G .) Since G ’s
constraints are bijective, we may assume that the associated scopes
are (u, v1), . . . , (u, vr) with bijections π1, . . . , πr : [q] → [q].

• Output the constraint ψ( f π1
v1

(x(1)), . . . , ψ( f πr
vr

the permutation notation f π from Exercise 1.30.

(x(r))), where we use

(a) Suppose Opt(G ) ≥ 1 − δ. Show that there is an assignment for P with
value at least β − O(δ) in which each fv is a dictator. (You will use
regularity of G here.) Thus Opt(P ) ≥ β − O(δ).

(b) Given an assignment F = ( fv)v∈V for P , introduce for each u ∈ V the
function gu : {−1, 1}q → [−1, 1] dened by g(x) = Ev[ f π
v (x)], where v is
a random neighbor of u in G and π is the associated constraint’s per-
mutation. Show that ValP (F) = Eu∈V [ValT (gu)] (using the denition
from Exercise 7.22).

(c) Fix an ≤ > 0 and suppose that ValP (F) ≥ s + 2λ(≤), where λ is the
“rejection rate” associated with T. Show that for at least a λ(≤)-fraction
of vertices u ∈ V , the set NbrNotableu = {i ∈ [q] : Inf(1−≤)
[gu] > ≤} is
nonempty.

i

(d) Show that for any u ∈ V , i ∈ [q] we have E[Inf(1−≤)
π−1(i)

[gu],
where v is a random neighbor of u and π is the associated constraint’s
permutation. (Hint: Exercise 2.48.)

[ fv]] ≥ Inf(1−≤)

i

(e) For v ∈ V , dene also the set Notableu = {i ∈ [q] : Inf(1−≤)

[ fv] ≥ ≤/2}.
Show that if i ∈ NbrNotableu, then Prv[π−1(i) ∈ Notablev] ≥ ≤/2, where
v and π are as in the previous part.

i

(f ) Show that for every u ∈ V we have |Notableu ∪NbrNotableu| ≤ O(1/≤2).

(Hint: Proposition 2.54.)

(g) Consider the following randomized assignment for G (see Exericse 7.20):
for each u ∈ V , give it the uniform distribution on Notableu∪NbrNotableu
(if this set is nonempty; otherwise, give it an arbitrary labeling). Show
that this randomized assignment has value Ω(λ(≤)≤5).

(h) Conclude Theorem 7.40, where “UG-hard” means “NP-hard assuming

the Unique Games Conjecture”.

7.31 Technically, Exercise 7.30 has a small bug: Since a Dictator-vs.-No-Notables

test using predicate set Ψ is allowed to use duplicate query strings in its
predicates (see Remark 7.38), the reduction in the previous exercise does
not necessarily output instances of Max-CSP(Ψ) because our denition
of CSPs requires that each scope consist of distinct variables. In this

Copyright © Ryan O’Donnell, 2014, 2015, 2016, 2017, 2018, 2019, 2020, 2021.



<!-- pdf-page: 203 -->
7.5. Exercises and notes

203

exercise you will correct this bug. Let M ∈ + and suppose we modify
the algorithm R from Exercise 7.30 to a new algorithm R′, producing an
instance P ′ with variable set V × [M] × {−1, 1}q. We now think of assign-
ments to P ′ as M-tuples of functions f 1
v , one tuple for each v ∈ V .
Further, thinking of P as a function tester, we have P ′ act as follows:
Whenever P is about to query fv(x), we have P ′ instead query f j
v (x) for
a uniformly random j ∈ [M].
(a) Show that Opt(P ) = Opt(P ′).
(b) Show that if we delete all constraints in P ′ for which the scope con-
tains duplicates, then Opt(P ′) changes by at most r2/M, where r is
the maximum arity of a constraint in Ψ.

v , . . . , f M

(c) Show that the deleted version of P ′ is a genuine instance of Max-
CSP(Ψ). Since the constant r2/M can be arbitrarily small, this cor-
rects the bug in Exercise 7.30’s proof of Theorem 7.40.

Notes. The study of property testing was initiated by Rubinfeld and Su-
dan [RS96] and signicantly expanded by Goldreich, Goldwasser, and Ron
[GGR98]; the stricter notion of local testability was introduced (in the context
of error-correcting codes) by Friedl and Sudan [FS95]. The rst local tester
for dictatorship was given by Bellare, Goldreich, and Sudan [BGS95, BGS98]
(as in Exercise 7.8); it was later rediscovered by Parnas, Ron, and Samorod-
nitsky [PRS01, PRS02]. The relevance of Arrow’s Theorem to testing dicta-
torship was pointed out by Kalai [Kal02].

The idea of assisting testers by providing proofs grew out of complexity-
theoretic research on interactive proofs and PCPs; see the early work Ergün,
Kumar, and Rubinfeld [EKR99] and the references therein. The specic
denition of PCPPs was introduced independently by Ben-Sasson, Goldreich,
Harsha, Sudan, and Vadhan [BSGH+04] and by Dinur and Reingold [DR04]
in 2004. Both of these works obtained the PCPP Theorem, relying on the
fact that previous literature essentially already gave PCPP reductions of
exponential (or greater) proof length: Ben-Sasson et al. [BSGH+04] observed
that Theorem 7.19 can be obtained from Arora et. al. [ALM+98] (their proof is
Exercise 7.18), while Dinur and Reingold [DR04] pointed out that the slightly
easier Theorem 7.18 can be extracted from the work of Bellare, Goldreich,
and Sudan [BGS98]. The proof we gave for Theorem 7.16 is inspired by the
presentation in Dinur [Din07].

The PCP Theorem and its stronger forms (the PCPP Theorem and Theo-
rem 7.20) have a somewhat remarkable consequence. Suppose a researcher
claims to prove a famous mathematical conjecture, say, “P 6= NP”. To ensure
maximum condence in correctness, a journal might request the researcher
submit a formalized proof, suitable for a mechanical proof-checking system.

Copyright © Ryan O’Donnell, 2014, 2015, 2016, 2017, 2018, 2019, 2020, 2021.



<!-- pdf-page: 204 -->
204

7. Property testing, PCPPs, and CSPs

If the submitted formalized proof w is a Boolean string of length n, the proof-
checker will be implementable by a circuit C of size O(n). Notice that the
string property C decided by C is nonempty if and only if there exists a
(length-n) proof of P 6= NP. Suppose the journal applies Theorem 7.20 to C and
requires the researcher submit the additional proof Π of length n · polylog(n).
Now the journal can run a rather amazing testing algorithm, which reads
just 3 bits of the submitted proof (w, Π). If the researcher’s proof of P 6= NP
is correct then the test will accept with probability 1. On the other hand, if
the test accepts with probability at least 1 − γ (where γ is the rejection rate
in Theorem 7.20), then w must be 1-close to the set of strings accepted by C.
This doesn’t necessarily mean that w is a correct proof of P 6= NP – but it does
mean that C is nonempty, and hence a correct proof of P 6= NP exists! By
querying a larger constant number of bits from (w, Π) as in Exercise 7.1, say,
d30/γe bits, the journal can become 99.99% convinced that indeed P 6= NP.

CSPs are very widely studied in computer science; it is impossible to sur-
vey the topic here. In the case of Boolean CSPs various monographs [CKS01,
KSTW01] contain useful background regarding complexity theory and ap-
proximation algorithms. The notion of approximation algorithms and the de-
randomized ( 7
8 , 1)-approximation algorithm for Max-E3-Sat (Proposition 7.36,
Exercise 7.21) are due to Johnson [Joh74]. Incidentally, there is also an
efcient ( 7
8 , 1)-approximation algorithm for Max-3-Sat [KZ97], but both the
algorithm and its analysis are extremely difcult, the latter requiring com-
puter assistance [Zwi02].

Håstad’s hardness theorems appeared in 2001 [Hås01b], building on ear-
lier work [Hås96, Hås99]. Håstad [Hås01b] also proved NP-hardness of
p + δ, 1 − δ)-approximating Max-E3-Lin(mod p) (for p prime) and of ( 7
( 1
8 , 1)-
approximating Max-CSP({NAE4}), both of which are optimal. Using tools due
to Trevisan et al. [TSSW00], Håstad also showed NP-hardness of ( 11
16 + δ, 3
4 )-
approximating Max-Cut, which is still the best known such result. The
best known inapproximability result for Unique-Games(q) is NP-hardness of
( 3
8 + q−Θ(1), 1
2 )-approximation [OW12]. Khot’s inuential Unique Games Con-
jecture dates from 2002 [Kho02]; the peculiar name has its origins in a work
of Feige and Lovász [FL92]. The generic Theorem 7.40, giving UG-hardness
from Dictator-vs.-No-Notables tests, is essentially from Khot et al. [KKMO07];
the rst explicit proof appearing in print may be due to Austrin [Aus08]. (We
remark that the terminology “Dictator-vs.-No-Notables test” is not standard.)
If one is willing to assume the Unique Games Conjecture, there is an almost-
complete theory of optimal inapproximability due to Raghavendra [Rag09].
Many more inapproximability results, with and without the Unique Games
Conjecture, are known; for some surveys, see those of Khot [Kho05, Kho10a,
Kho10b].

Copyright © Ryan O’Donnell, 2014, 2015, 2016, 2017, 2018, 2019, 2020, 2021.



<!-- pdf-page: 205 -->
7.5. Exercises and notes

205

As mentioned, Exercise 7.8 is due to Bellare, Goldreich, and Sudan [BGS95]

and to Parnas, Ron, and Samorodnitsky [PRS01]. The technique described in
Exercise 7.21 is known as the Method of Conditional Expectations. The trick
in Exercise 7.23 is closely related to the notion of “folding” from the theory of
PCPs. The bug described in Exercise 7.31 is rarely addressed in the literature;
the trick used to overcome it appears in, e.g., Arora et al. [ABH+05].

Copyright © Ryan O’Donnell, 2014, 2015, 2016, 2017, 2018, 2019, 2020, 2021.



<!-- pdf-page: 206 -->


<!-- pdf-page: 207 -->
Chapter 8

Generalized domains

So far we have studied functions f : {0, 1}n → . What about, say, f : {0, 1, 2}n →
? In fact, very little of what we’ve done so far depends on the domain be-
ing {0, 1}n; what it has mostly depended on is our viewing the domain as a
product probability distribution. Indeed, much of analysis of Boolean func-
tions carries over to the case of functions f : Ω1 × · · · × Ωn → where the
domain has a product probability distribution π1 ⊗ · · · ⊗ πn. There are two
main exceptions: the “derivative” operator Di does not generalize to the case
when |Ωi| > 2 (though the Laplacian operator Li does), and the important
notion of hypercontractivity (introduced in Chapter 9) depends strongly on
the probability distributions πi.

In this chapter we focus on the case where all the Ωi’s are the same, as
are the πi’s. (This is just to save on notation; it will be clear that everything
we do holds in the more general setting.) Important classic cases include
functions on the p-biased hypercube (Section 8.4) and functions on abelian
groups (Section 8.5). For the issue of generalizing the range of functions – e.g.,
studying functions f : {0, 1, 2}n → {0, 1, 2} – see Exercise 8.33.

8.1. Fourier bases for product spaces

We will now begin to discuss functions on (nite) product probability spaces.

Denition 8.1. Let (Ω, π) be a nite probability space with |Ω| ≥ 2 and as-
sume π has full support. For n ∈ + we write L2(Ωn, π⊗n) for the (real) inner
product space of functions f : Ωn → , with inner product

〈 f , g〉 = E

x∼π⊗n

[ f (x)g(x)].

Here π⊗n denotes the product probability distribution on Ωn.

Copyright © Ryan O’Donnell, 2014, 2015, 2016, 2017, 2018, 2019, 2020, 2021.

207



<!-- pdf-page: 208 -->
208

8. Generalized domains

Example 8.2. A simple example to keep in mind is Ω = {a, b, c} with π(a) =
π(b) = π(c) = 1/3. Here a, b, and c are simply abstract set elements.

We can (and will) generalize to nondiscrete probability spaces, and to
complex inner product spaces. However, we will keep to the above denition
for now.

Notation 8.3. We will write π1/2 for the uniform probability distribution
on {−1, 1}. Thus so far in this book we have been studying functions in
L2({−1, 1}n, π⊗n
1/2

). For simplicity, we will write this as L2({−1, 1}n).

Notation 8.4. Much of the notation we used for L2({−1, 1}n) extends naturally
to the case of L2(Ωn, π⊗n): e.g., ‖ f ‖p = Ex∼π⊗n [| f (x)|p]1/p, or the restriction
notation from Chapter 3.3.

As we described in Chapter 1.4, the essence of Boolean Fourier analysis
is in deriving combinatorial properties of a Boolean function f : {−1, 1}n →
from its coefcients over a particular basis of L2({−1, 1}n), the basis of
parity functions. We would like to achieve the same thing more generally for
functions in L2(Ωn, π⊗n). We begin by considering vector space bases more
generally.

Denition 8.5. Let |Ω| = m. The indicator basis (or standard basis) for
L2(Ω, π) is just the set of m indicator functions (1x)x∈Ω, where

1x(y) =



1 if y = x,

0 if y 6= x.

Fact 8.6. The indicator basis is indeed a basis for L2(Ω, π) since the functions
(1x)x∈Ω are nonzero, spanning, and orthogonal. Hence dim(L2(Ω, π)) = m.

We will usually x Ω and π and then consider L2(Ωn, π⊗n) for n ∈
+.
Applying the above denition gives us an indicator basis (1x)x∈Ωn for the mn-
dimensional space L2(Ωn, π⊗n). The representation of f ∈ L2(Ω, π) in this
basis is just f =
x∈Ω f (x)1x. This is not very interesting; the coefcients are
just the values of f so they don’t tell us anything new about the function. We
would like a different basis that will generate useful “Fourier formulas” as in
Chapter 1.4.



For inspiration, let’s look critically at the familiar case of L2({−1, 1}n).
i∈S xi. It will be
Here we used the basis of all parity functions, χS(x) =
helpful to think of the basis function χS : {−1, 1}n → as follows: Identify S
with its 0-1 indicator vector and write



χS(x) =

n∏

i=1

φS i

(xi),

where φ0 ≡ 1, φ1 = id.

Copyright © Ryan O’Donnell, 2014, 2015, 2016, 2017, 2018, 2019, 2020, 2021.



<!-- pdf-page: 209 -->
8.1. Fourier bases for product spaces

209

(Here id is just the identity map id(b) = b.) We will identify three properties
of this basis which we’d like to generalize.

First, the parity basis is a product basis. We can break down its “prod-
uct structure” as follows: For each coordinate i ∈ [n] of the product domain
{−1, 1}n, the set {1, id} is a basis for the 2-dimensional space L2({−1, 1}, π1/2).
We then get a basis for the 2n-dimensional product space L2({−1, 1}n) by tak-
ing all possible n-fold products. More generally, suppose we are given an
inner product space L2(Ω, π) with |Ω| = m. Let φ0, . . . , φm−1 be any basis for
this space. Then the set of all products φi1
(0 ≤ i j < m) forms a basis
for the space L2(Ωn, π⊗n).

· · · φi n

φi2

Second, it is convenient that the parity basis is orthonormal. We will later
check that if a basis φ0, . . . , φm−1 for L2(Ω, π) is orthonormal, then so too is
the associated product basis for L2(Ωn, π⊗n). This relies on the fact that π⊗n
is the product distribution. For example, the parity basis for L2({−1, 1}n)
is orthonormal because the basis {1, id} for L2({−1, 1}, π1/2) is orthonormal:
E[12] = E[x2
] = 1, E[1 · xi] = 0. Orthonormality is the property that makes
i
Parseval’s Theorem hold; in the general context, this means that if f ∈ L2(Ω, π)
has the representation

m−1

m−1

i=0 ciφi then E[ f 2] =

i=0 c2

.

i

Finally, the parity basis contains the constant function 1. This fact leads
to several of our pleasant Fourier formulas. In particular, when you take
an orthonormal basis φ0, . . . , φm−1 for L2(Ω, π) which has φ0 ≡ 1, then 0 =
〈φ0, φi〉 = Ex∼π[φi(x)] for all i > 0. Hence if f ∈ L2(Ω, π) has the expansion
f =

i=0 ciφi, then E[ f ] = c0 and Var[ f ] =

i>0 c2
i

m−1



.

We encapsulate the second and third properties with a denition:

Denition 8.7. A Fourier basis for an inner product space L2(Ω, π) is an
orthonormal basis φ0, . . . , φm−1 with φ0 ≡ 1.

Example 8.8. For each n ∈
Fourier basis for L2({−1, 1}n, π⊗n
1/2

+, the 2n parity functions (χS)S⊆[n] form a
).

Remark 8.9. A Fourier basis for L2(Ω, π) always exists because you can ex-
tend the set {1} to a basis and then perform the Gram–Schmidt process. On the
other hand, Fourier bases are not unique. Even in the case of L2({−1, 1}, π1/2)
there are two possibilities: the basis {1, id} and the basis {1, −id}.

Example 8.10. In the case of Ω = {a, b, c} with π(a) = π(b) = π(c) = 1/3, one
possible Fourier basis (see Exercise 8.4) is

φ0 ≡ 1,

φ1(a) = +
φ1(b) = −
φ1(c) = −

p
p
p

2
2/2
2/2,

φ2(a) = 0
φ2(b) = +
φ2(c) = −

p
p

6/2,
6/2.

Copyright © Ryan O’Donnell, 2014, 2015, 2016, 2017, 2018, 2019, 2020, 2021.



<!-- pdf-page: 210 -->
210

8. Generalized domains

As mentioned, given a Fourier basis for L2(Ω, π) you can construct a
Fourier basis for any L2(Ωn, π⊗n) by “taking all n-fold products”. To make
this precise we need some notation.

Denition 8.11. An n-dimensional multi-index is a tuple α ∈ n. We write

supp(α) = {i : αi 6= 0}, #α = |supp(α)|,

|α| =

n∑

i=1

αi.

We may write α ∈ n
1}.

<m when we want to emphasize that each αi ∈ {0, 1, . . . , m−

Denition 8.12. Given functions φ0, . . . , φm−1 ∈ L2(Ω, π) and a multi-index
α ∈ n

<m, we dene φα ∈ L2(Ωn, π⊗n) by
n∏

φα(x) =

φαi

(xi).

i=1

Now we can show that products of Fourier bases are Fourier bases.

Proposition 8.13. Let φ0, . . . , φm−1 be a Fourier basis for L2(Ω, π). Then the
is a Fourier basis for L2(Ωn, π⊗n) (with the understanding
collection (φα)α∈ n
that α = (0, 0, . . . , 0) indexes the constant function 1).

<m

Proof. First we check orthonormality. For any multi-indices α, β ∈ n
have

<m we

〈φα, φβ〉 = E

x∼π⊗n

= E

x∼π⊗n

[φα(x) · φβ(x)]
 n∏

n∏

φαi

(xi) ·

i=1

i=1



φβi

(xi)

E
xi∼π

[φαi

(xi) · φβi

(xi)]

(since π⊗n is a product distribution)

(since {φ0, . . . , φm−1} is orthonormal)

n∏

i=1
n∏

=

=

1{αi=βi}

i=1
= 1{α=β}.

This conrms that the collection (φα)α∈ n
is orthonormal, and consequently
linearly independent. It is therefore also a basis because it has cardinality mn,
which we know is the dimension of L2(Ωn, π⊗n) (see Fact 8.6).


<m

Given a product Fourier basis as in Proposition 8.13, we can express any
f ∈ L2(Ωn, π⊗n) as a linear combination of basis functions. We will write f (α)
for the “Fourier coefcient” on φα in this expression.

Copyright © Ryan O’Donnell, 2014, 2015, 2016, 2017, 2018, 2019, 2020, 2021.



<!-- pdf-page: 211 -->
8.2. Generalized Fourier formulas

211

Denition 8.14. Having xed a Fourier basis φ0, . . . , φm−1 for L2(Ω, π), every
f ∈ L2(Ωn, π⊗n) is uniquely expressible as

∑

f =

α∈ n

<m

f (α)φα.

This is the Fourier expansion of f with respect to the basis. The real number
f (α) is called the Fourier coefcient of f on α and it satises

f (α) = 〈 f , φα〉.

Example 8.15. Fix the Fourier basis as in Example 8.10. Let f : {a, b, c}2 →
{0, 1} be the function which is 1 if and only if both inputs are c. Then you can
check (Exercise 8.5) that

f = 1

9 −

p
2
18 φ(1,0)−

p
6
18 φ(2,0)−

p
2
18 φ(0,1)−

p

6

18 φ(0,2)+ 1

18 φ(1,1)+

p
12
36 φ(2,1)+

p

12

36 φ(1,2)+ 1

6 φ(2,2).

The notation f (α) may seem poorly chosen because it doesn’t show the de-
pendence on the basis. However, the Fourier formulas we develop in the next
section will have the property that they are the same for every product Fourier
basis. We will show a basis-independent way of developing the formulas in
Section 8.3.

8.2. Generalized Fourier formulas

In this section we will revisit a number of combinatorial/probabilistic no-
tions and show that for functions f ∈ L2(Ωn, π⊗n), these notions have familiar
Fourier formulas that don’t depend on the Fourier basis.

The orthonormality of Fourier bases gives us some formulas almost imme-

diately:

Proposition 8.16. Let f , g ∈ L2(Ωn, π⊗n). Then for any xed product Fourier
basis, the following formulas hold:

E[ f ] = f (0)
∑

E[ f 2] =

f (α)2

(Parseval)

α∈ n
∑

<m

f (α)2

Var[ f ] =

α6=0
∑

〈 f , g〉 =

f (α) g(α)

(Plancherel)

Cov[ f , g] =

α∈ n
∑

<m

f (α) g(α).

Copyright © Ryan O’Donnell, 2014, 2015, 2016, 2017, 2018, 2019, 2020, 2021.

α6=0



<!-- pdf-page: 212 -->
212

8. Generalized domains

Proof. We verify Plancherel’s Theorem, from which the other identities follow
(Exercise 8.6):

〈 f , g〉 =

=

=

〈 ∑

∑

f (α)φα,

g(β)φβ

〉

α∈ n
∑

<m

β∈ n
f (α) g(β)〈φα, φβ〉

<m

α,β∈ n
∑

<m

f (α) g(α)

by orthonormality of (φα)α∈ n

<m

.

α∈ n

<m



We now give the key denition for developing basis-independent Fourier
In the case of L2({−1, 1}) this denition appeared already in

expansions.
Exercise 3.28.

Denition 8.17. Let J ⊆ [n] and write J = [n] \ J. Given f ∈ L2(Ωn, π⊗n), the
projection of f on coordinates J is the function f ⊆J ∈ L2(Ωn, π⊗n) dened by

f ⊆J(x) = E

[ f (xJ, x′)],

x′∼π⊗J
where xJ ∈ ΩJ denotes the values of x in the J-coordinates. In other words,
f ⊆J(x) is the expectation of f when the J-coordinates of x are rerandomized.
Note that we take f ⊆J to have Ωn as its domain, even though it only depends
on the coordinates in J.

Forming f ⊆J is indeed the application of a projection linear operator to f ,
. We take this as the denition of

namely the expectation over J operator, E
the operator: E

J

f = f ⊆J. When J = {i} is a singleton we write simply Ei.

J

Remark 8.18. This denition of Ei is consistent with Denition 2.23. You
are asked to verify that E
is indeed a projection, self-adjoint linear operator
in Exercise 8.7.

J

Proposition 8.19. Let J ⊆ [n] and f ∈ L2(Ωn, π⊗n). Then for any xed product
Fourier basis,

∑

f ⊆J =

f (α) φα.

α∈ n
supp(α)⊆J

<m

Proof. Since E

J

is a linear operator, it sufces to verify for all α that

φ⊆J

α =



φα
0

if supp(α) ⊆ J,

otherwise.

If supp(α) ⊆ J, then φα does not depend on the coordinates J; hence indeed

φ⊆J
,
(xi)
depends only on the coordinates in J,
we can write φα = φαJ

α = φα. So suppose supp(α) 6⊆ J. Since φα(x) =
· φαJ

, where φαJ

i∈J φαi

(xi)



φαi



i∈J

Copyright © Ryan O’Donnell, 2014, 2015, 2016, 2017, 2018, 2019, 2020, 2021.



<!-- pdf-page: 213 -->
8.2. Generalized Fourier formulas

213

depends only on the coordinates in J, and E[φαJ

φαJ
supp(α) 6⊆ J. Thus for every x ∈ Ωn,

] = 0 precisely because

φ⊆J

α (x) = E

x′∼π⊗J

[φαJ

(xJ)φαJ

(x′)] = φαJ

(xJ) · E

x′∼π⊗J

[φαJ

(x′)] = 0

as needed.



Corollary 8.20. Let f ∈ L2(Ωn, π⊗n) and x a product Fourier basis. If f
depends only on the coordinates in J ⊆ [n] then f (α) = 0 whenever supp(α) 6⊆ J.

Proof. This follows from Proposition 8.19 because f = f ⊆J.



Corollary 8.21. Let i ∈ [n] and f ∈ L2(Ωn, π⊗n). Then for any xed product
Fourier basis,

∑

Ei f =

f (α) φα.

α:αi=0

Let us now dene inuences for functions f ∈ L2(Ωn, π⊗n). In the case of
Ω = {−1, 1}, our denition of Infi[ f ] from Chapter 2.2 was E[(Di f )2]. However,
the notion of a derivative operator does not make sense for more general
domains Ω. In fact, even in the case of Ω = {−1, 1} it isn’t a basis-invariant
notion: the choice of f (x(i7→1))− f (x(i7→−1))
is inherently
arbitrary. Instead we can fall back on the Laplacian operators, and take the
identity Infi[ f ] = 〈 f , Li f 〉 from Proposition 2.26 as a denition.

rather than f (x(i7→−1))− f (x(i7→1))

2

2

Denition 8.22. Let i ∈ [n] and f ∈ L2(Ωn, π⊗n). The ith coordinate Laplacian
operator Li is the self-adjoint, projection linear operator dened by

Li f = f − Ei f .

The inuence of coordinate i on f is dened to be

The total inuence of f is dened to be I[ f ] =

n

i=1 Infi[ f ].

Infi[ f ] = 〈 f , Li f 〉 = 〈Li f , Li f 〉.

You can think of Li f as “the part of f which depends on the ith coordinate”.

Proposition 8.23. Let i ∈ [n] and f ∈ L2(Ωn, π⊗n). Then for any xed product
Fourier basis,

Li f =

∑

α:αi6=0

f (α) φα,

Infi[ f ] =

∑

α:αi6=0

f (α)2,

I[ f ] =

∑

α

#α · f (α)2,

Proof. The rst formula is immediate from Corollary 8.21, the second from

Plancherel, and the third from summing over i.

Exercise 8.9 asks you to verify the following formulas (cf. Exercise 2.21),

which are often useful for computations:

Copyright © Ryan O’Donnell, 2014, 2015, 2016, 2017, 2018, 2019, 2020, 2021.



<!-- pdf-page: 214 -->
214

8. Generalized domains

Proposition 8.24. Let i ∈ [n] and f ∈ L2(Ωn, π⊗n). Then

Infi[ f ] = E

x∼π⊗n

[Var
x′
∼π
i

[ f (x1, . . . , xi−1, x′

i, xi+1, . . . , xn)]].

If furthermore f ’s range is {−1, 1}, then

Infi[ f ] = E[|Li f |] = 2 Pr
x∼π⊗n
x′
i∼π

[ f (x) 6= f (x1, . . . , xi−1, x′

i, xi+1, . . . , xn)].

Example 8.25. Let’s continue Example 8.15, in which {a, b, c} has the uniform
distribution and f : {a, b, c}2 → {0, 1} is 1 if and only if both inputs are c. We
compute Inf1[ f ] two ways. Using Proposition 8.24 we have Var[ f (x1, a)] =
3 · 2
Var[ f (x1, b)] = 0 and Var[ f (x1, c)] = 1
9 (because f (x1, c) is Bernoulli with
parameter 1
9 = 2
27 . Alternatively, using the formula from
Proposition 8.23 as well as the Fourier expansion from Example 8.15, we can
compute Inf1[ f ] = (−

3 ); thus Inf1[ f ] = 1

3 = 2

3 · 2

18 )2 + ( 1

18 )2 + (

36 )2 + ( 1

18 )2 + (−

6 )2 = 2
27 .

36 )2 + (

12

12

p

p

p

p

2

6

Next, we straightforwardly extend our denitions of the noise operator

and noise stability to general product spaces.

Denition 8.26. Fix a nite product probability space (Ωn, π⊗n). For ρ ∈ [0, 1]
and x ∈ Ωn we write y ∼ Nρ(x) to denote that y ∈ Ωn is randomly chosen as
follows: For each i ∈ [n] independently,



yi =

xi
drawn from π with probability 1 − ρ.

with probability ρ,

If x ∼ π⊗n and y ∼ Nρ(x), we say that (x, y) is a ρ-correlated pair under π⊗n.
(This denition is symmetric in x and y.)

Denition 8.27. For a xed space L2(Ωn, π⊗n) and ρ ∈ [0, 1], the noise oper-
ator with parameter ρ is the linear operator Tρ on functions f ∈ L2(Ωn, π⊗n)
dened by

The noise stability of f at ρ is

Tρ f (x) = E

y∼Nρ(x)

[ f (y)].

Stabρ[ f ] = 〈 f , Tρ f 〉 =

E
(x,y) ρ-correlated
under π⊗n

[ f (x) f (y)].

Proposition 8.28. Let ρ ∈ [0, 1] and let f ∈ L2(Ωn, π⊗n). Then for any xed
product Fourier basis,
∑

∑

Tρ f =

ρ#α f (α) φα,

Stabρ[ f ] =

ρ#α f (α)2.

α∈ n

<m

α∈ n

<m

Copyright © Ryan O’Donnell, 2014, 2015, 2016, 2017, 2018, 2019, 2020, 2021.



<!-- pdf-page: 215 -->
8.2. Generalized Fourier formulas

215

Proof. Let J denote a ρ-random subset of [n]; i.e., J is formed by including
each i ∈ [n] independently with probability ρ. Then by denition Tρ f (x) =
EJ[ f ⊆J(x)], and so from Proposition 8.19 we get

f (α) φα(x)

ρ#α f (α) φα(x),

 ∑

∑

=

Tρ f (x) = E
J

[ f ⊆J(x)] = E
J

α∈ n
supp(α)⊆J

<m

α∈ n

<m

since for a xed α, the probability of supp(α) ⊆ J is ρ#α. The formula for

Stabρ[ f ] now follows from Plancherel.

Remark 8.29. The rst formula in this proposition may be used to extend
the denition of Tρ f to values of ρ outside [0, 1].

We also dene ρ-stable inuences. The factor of ρ−1 in our denition is

for consistency with the L2({−1, 1}n) case.

Denition 8.30. For f ∈ L2(Ωn, π⊗n), ρ ∈ (0, 1], and i ∈ [n], the ρ-stable inu-
ence of i on f is

Inf(ρ)
i

[ f ] = ρ−1Stabρ[Li f ] =

We also dene I(ρ)[ f ] =

n

i=1 Inf(ρ)

i

[ f ].

∑

α:αi6=0

ρ#α−1 f (α)2.

Just as in the case of L2({−1, 1}n) we can use stable inuences to dene
the “notable” coordinates of a function, of which there is a bounded quantity.
A verbatim repetition of the proof of Proposition 2.54 yields the following
generalization:

Proposition 8.31. Suppose f ∈ L2(Ωn, π⊗n) has Var[ f ] ≤ 1. Given 0 < δ < 1,
0 < ≤ ≤ 1, let J = {i ∈ [n] : Inf(1−δ)

[ f ] ≥ ≤}. Then |J| ≤ 1
δ≤

.

i

We end this section by discussing the “degree” of functions on general
product spaces. For f ∈ L2({−1, 1}n) the Fourier expansion is a real polynomial;
this yields an obvious denition for degree. But for general f ∈ L2(Ωn, π⊗n)
the domain is just an abstract set so we need to look for a more intrinsic
denition. We take our cue from Exercise 1.10(b):

Denition 8.32. Let f ∈ L2(Ωn, π⊗n) be nonzero. The degree of f , written
deg( f ), is the least k ∈
such that f is a sum of k-juntas (functions depending
on at most k coordinates).

Proposition 8.33. Let f ∈ L2(Ωn, π⊗n) be nonzero. Then for any xed product
Fourier basis we have deg( f ) = max{#α : f (α) 6= 0}.

Proof. The inequality deg( f ) ≤ max{#α : f (α) 6= 0} is immediate from the
Fourier expansion:

∑

f =

f (α) φα

α: f (α)6=0

Copyright © Ryan O’Donnell, 2014, 2015, 2016, 2017, 2018, 2019, 2020, 2021.



<!-- pdf-page: 216 -->
216

8. Generalized domains

and each function f (α) φα depends on at most #α coordinates. For the reverse
inequality, suppose f = g1 + · · · + gm where each g i depends on at most k
coordinates. By Corollary 8.20 each g i has its Fourier support on functions φα
with #α ≤ k. But f (α) = g1(α) + · · · + gm(α), so the same is true of f .


8.3. Orthogonal decomposition

In this section we describe a basis-free kind of “Fourier expansion” for func-
tions on general product domains. We will refer to it as the orthogonal decom-
position of f ∈ L2(Ωn, π⊗n), though it goes by several other names in the liter-
ature: e.g., Hoeffding decomposition, Efron–Stein decomposition, or ANOVA
decomposition. The general idea is to express

∑

f =S

f =

S⊆[n]

(8.1)

where each function f =S ∈ L2(Ωn, π⊗n) gives the “contribution to f coming
from coordinates S (but not from any subset of S)”.

To make this more precise, let’s start with the familiar case of f : {−1, 1}n →
. Here it is possible to dene the functions f =S : {−1, 1}n → simply by
f =S = f (S) χS. (Later we will give an equivalent denition that doesn’t in-
volve the Fourier basis.) This denition satises (8.1) as well as the following
two properties:

(1) f =S depends only on the coordinates in S.

(2) If T ( S and g is a function depending only on the coordinates in T,

then 〈 f =S, g〉 = 0.

These properties describe what we mean precisely when we say that f =S is
the “contribution to f coming from coordinates S (but not from any subset
of S)”. Furthermore, decomposition (8.1) is orthogonal, meaning 〈 f =S, f =T 〉 =
0 whenever S 6= T.

To make this denition basis-free, recall the “projection of f onto coordi-
nates J”, f ⊆J, from Exercise 3.28 and Denition 8.17. You can think of f ⊆J
as the “contribution to f coming from coordinates J (collectively)”. It has a
probabilistic denition not depending on any basis, and with the denition
f =S = f (S) χS we have from Exercise 3.28 or Proposition 8.19 that

f ⊆J =

∑

S⊆J

f =S.

(8.2)

It is precisely by inverting (8.2) that we can give a basis-free denition of the
functions f =S.

Let’s do this inversion for a general f ∈ L2(Ωn, π⊗n). The projection func-
tions f ⊆J ∈ L2(Ωn, π⊗n) can be dened as in Denition 8.17. If we want (8.2)

Copyright © Ryan O’Donnell, 2014, 2015, 2016, 2017, 2018, 2019, 2020, 2021.



<!-- pdf-page: 217 -->
8.3. Orthogonal decomposition

217

to hold for J = ; then we should dene

f =; = f ⊆;

(which is the constant function equal to E[ f ]). Given this, if we want (8.2) to
hold for singleton sets J = { j}, then we need

f ⊆{ j} = f =; + f ={ j} ⇐⇒ f ={ j} = f ⊆{ j} − f ⊆;.

In other words,

f ={ j}(x) = E

x∼π⊗n

[ f | x j = x j] − E

x∼π⊗n

[ f (x)].

Notice this function only depends on the input value x j; it measures the
change in expectation of f if you know the value x j. Moving on to sets of
cardinality 2, if we want (8.2) to hold for J = {i, j}, then we need

f ⊆{i, j} = f =; + f ={i} + f ={ j} + f ={i, j}

= f ⊆; + ( f ⊆{i} − f ⊆;) + ( f ⊆{ j} − f ⊆;) + f ={i, j}

and hence

f ={i, j} = f ⊆{i, j} − f ⊆{i} − f ⊆{ j} + f ⊆;.

It’s clear that we can continue this and dene all the functions f =S by the
principle of inclusion-exclusion. To show this denition leads to an orthogonal
decomposition we will need the following lemma:

Lemma 8.34. Let f , g ∈ L2(Ωn, π⊗n). Assume that f does not depend on any
coordinate outside I ⊆ [n], and g does not depend on any coordinate outside
J ⊆ [n]. Then 〈 f , g〉 = 〈 f ⊆I∩J, g⊆I∩J〉.

Proof. We may assume without loss of generality that I ∪ J = [n]. Given any
x ∈ Ωn we can break it into the parts (xI∩J, xI\J, xJ\I ). We then have

〈 f , g〉 =

E
xI∩J ,xI\J ,xJ\I

[ f (xI∩J, xI\J) · g(xI∩J, xJ\I )],

where we have abused notation slightly by writing f and g as functions just
of the coordinates on which they actually depend. Since xI\J and xJ\I are
independent, the above equals

[

]

E
xI∩J

E
xI\J

[ f (xI∩J, xI\J)] · E
xJ\I

[g(xI∩J, xJ\I )]

.

But now ExI\J
ExJ\I

[ f (xI∩J, xI\J)] is nothing more than f ⊆I∩J(xI∩J), and similarly

[g(xI∩J, xJ\I )] = g⊆I∩J(xI∩J). Thus the above equals

[ f ⊆I∩J(xI∩J) · g⊆I∩J(xI∩J)] = 〈 f ⊆I∩J, g⊆I∩J〉.



E
xI∩J

We can now give the main theorem on orthogonal decomposition:

Copyright © Ryan O’Donnell, 2014, 2015, 2016, 2017, 2018, 2019, 2020, 2021.



<!-- pdf-page: 218 -->
218

8. Generalized domains

Theorem 8.35. Let f ∈ L2(Ωn, π⊗n). Then f has a unique decomposition as
∑

f =

f =S

where the functions f =S ∈ L2(Ωn, π⊗n) satisfy the following:

S⊆[n]

(1) f =S depends only on the coordinates in S.
(2) If T ( S and g ∈ L2(Ωn, π⊗n) depends only on the coordinates in T, then

〈 f =S, g〉 = 0.

This decomposition has the following additional properties:

(3) Condition (2) additionally holds whenever S 6⊆ T.
(4) The decomposition is orthogonal: 〈 f =S, f =T 〉 = 0 for S 6= T.



S⊆T f =S = f ⊆T .

(5)
(6) For each S ⊆ [n], the mapping f 7→ f =S is a linear operator.

Proof. We rst show the existence of a decomposition satisfying (1)–(6). We
then show uniqueness for decompositions satisfying (1) and (2). As suggested
above, for each S ⊆ [n] we dene

f =S =

∑

J⊆S

(−1)|S|−|J| f ⊆J,

where the functions f ⊆J ∈ L2(Ωn, π⊗n) are as in Denition 8.17. Since each f ⊆J
depends only on the coordinates in J, condition (1) certainly holds. It is also
immediate that condition (5) holds by inclusion-exclusion; you are asked to
prove this explicitly in Exercise 8.14. Condition (6) also follows because each
f 7→ f ⊆J is a linear operator, as discussed after Denition 8.17.

We now verify (2). Assume T ( S and that g ∈ L2(Ωn, π⊗n) only depends

on the coordinates in T. We have

〈 f =S, g〉 =

∑

J⊆S

(−1)|S|−|J|〈 f ⊆J, g〉.

(8.3)

Take any i ∈ S \ T and pair up the summands in (8.3) as J′, J′′, where J′ 63 i
and J′′ = J′ ∪ {i}. By Lemma 8.34 we have

〈 f ⊆J′′

, g〉 = 〈 f ⊆J′′∩T , g⊆T 〉 = 〈 f ⊆J′∩T , g⊆T 〉,

the latter equality using i 6∈ T. But the signs (−1)|S|−|J′| and (−1)|S|−|J′′| are
opposite, so the summands in (8.3) cancel in pairs. This shows the sum is 0,
conrming (2).

We complete the existence proof by noting that (2) =⇒ (3) =⇒ (4) (as-
suming (1)). The rst implication is because 〈 f =S, g〉 = 〈 f =S, g⊆S∩T 〉 when
g depends only on the coordinates in T (Lemma 8.34), and S ∩ T ( S when
S 6⊆ T. The second implication is because S 6= T implies either S 6⊆ T or T 6⊆ S.

Copyright © Ryan O’Donnell, 2014, 2015, 2016, 2017, 2018, 2019, 2020, 2021.



<!-- pdf-page: 219 -->
8.3. Orthogonal decomposition

219

It remains to prove the uniqueness statement. Suppose f has two repre-
sentations satisfying (1) and (2). By subtracting them we get a decomposition
of the 0 function that satises (1) and (2); our goal is to show that each func-
tion in this decomposition is the 0 function. We can do this by showing that
any decomposition satisfying (1) and (2) also satises “Parseval’s Theorem”:
2. But this is an easy consequence of (4), which we just
〈 f , f 〉 =

noted is itself a consequence of (1) and (2).

S⊆[n] ‖ f =S‖2



We can connect the orthogonal decomposition of f to its expansion under

Fourier bases as follows:

Proposition 8.36. Let f ∈ L2(Ωn, π⊗n) have orthogonal decomposition f =


S⊆[n] f =S. Fix any Fourier basis φ0, . . . , φm−1 for L2(Ω, π). Then

∑

f =S =

f (α) φα.

(8.4)

α∈ n
supp(α)=S

<m

Proof. This follows easily from the uniqueness part of Theorem 8.35. If we
S f =S = f
take (8.4) as the denition of functions f =S, it is immediate that
and that f =S depends only on the coordinates in S. Further, if g depends
only on coordinates T ( S, then f =S and g have disjoint Fourier support by
Corollary 8.20; hence 〈 f =S, g〉 = 0 by Plancherel (Proposition 8.16).




Example 8.37. Let’s compute the orthogonal decomposition of the function
f : {a, b, c}2 → {0, 1} from Example 8.15. Recall that in this example {a, b, c}
has the uniform distribution and f (x1, x2) = 1 if and only if x1 = x2 = c. First,
f =; = E[ f ] = 1
9 .

Next, for i = 1, 2 we have that f ⊆{i}(x) is 1



f ={i}(x1, x2) =

3 if xi = c and 0 otherwise; hence
+ 2
9
− 1
9

if xi = c,
else.

Finally, it’s easiest to compute f ={1,2} as f − f =; − f ={1} − f ={2}; this yields

f ={1,2}(x1, x2) =






+ 4
9
− 2
9
+ 1
9

if x1 = x2 = c,
if exactly one of x1, x2 is c,
if x1, x2 6= c.

You can check (Exercise 8.20) that this is consistent with Proposition 8.36 and
the Fourier expansion from Example 8.15.

We can write all of the Fourier formulas from Section 8.2 in terms of the

orthogonal decomposition; e.g.,
∑

〈 f , g〉 =

〈 f =S, g=S〉,

Infi[ f ] =

S⊆[n]

∑

S3i

‖ f =S‖2

2, Tρ f =

∑

S⊆[n]

ρ|S| f =S.

Copyright © Ryan O’Donnell, 2014, 2015, 2016, 2017, 2018, 2019, 2020, 2021.



<!-- pdf-page: 220 -->
220

8. Generalized domains

These formulas can be proved either by using the connection from Proposi-
tion 8.36 or by reasoning directly from the dening Theorem 8.35; see Ex-
ercise 8.18. The orthogonal decomposition also gives us the natural way of
stratifying f by degree; we end this section by generalizing some more deni-
tions from Chapter 1.4:

Denition 8.38. For f ∈ L2(Ωn, π⊗n) and k ∈ we dene the degree k part
|S|=k f =S and the weight of f at degree k to be Wk[ f ] = ‖ f =k‖2
of f to be f =k =
2.
We also use notation like f ≤k =

|S|≤k f =S and W>k[ f ] =

|S|>k ‖ f =S‖2
2.







8.4. p-biased analysis

Perhaps the most common generalized domain in analysis of Boolean func-
tions is the case of the hypercube with “biased” bits. In this setting we think of
a random input in {−1, 1}n as having each bit independently equal to −1 (True)
with probability p ∈ (0, 1) and equal to 1 (False) with probability q = 1 − p.
(We could also consider different parameters pi for each coordinate; see Ex-
ercise 8.24.) In the notation of the chapter this means L2(Ωn, π⊗n
p ), where
Ω = {−1, 1} and πp is the distribution on Ω dened by πp(−1) = p, πp(1) = q.
This context is often referred to as p-biased Fourier analysis, though it would
be more consistent with our terminology if it were called “µ-biased”, where

µ = E

xi∼πp

[xi] = q − p = 1 − 2p.

One of the more interesting features of the setting is that we can x a combi-
natorial Boolean function f : {−1, 1}n → {−1, 1} and then consider its properties
for various p between 0 and 1; we will discuss this further later in this sec-
tion. We will also sometimes use the abbreviated notation Prπp
[·] in place of
Prx∼π⊗n

[·], and similarly Eπp

[·].

p

The p-biased hypercube is one of the generalized domains where it can
pay to look at an explicit Fourier basis. In fact, since we have |Ω| = 2 there is
a unique Fourier basis {φ0, φ1} (up to negating φ1). For notational simplicity
we’ll write φ instead of φ1 and use “set notation” rather than multi-index
notation:

Denition 8.39. In the context of p-biased Fourier analysis we dene the
basis function φ : {−1, 1} → by

φ(xi) =

xi − µ
σ

,

where

µ = E

xi∼πp

[xi] = q − p = 1 − 2p, σ = stddev

xi∼πp



4pq = 2



p

p

1 − p.

[xi] =

Note that σ2 = 1 − µ2. We also have the formula φ(1) =



p/q, φ(−1) = −



q/p.

Copyright © Ryan O’Donnell, 2014, 2015, 2016, 2017, 2018, 2019, 2020, 2021.



<!-- pdf-page: 221 -->
8.4. p-biased analysis

221

We will use the notation µ and σ throughout this section. It’s clear that
{1, φ} is indeed a Fourier basis for L2({−1, 1}, πp) because E[φ(xi)] = 0 and
E[φ(xi)2] = 1 by design.

Denition 8.40. In the context of L2({−1, 1}n, π⊗n
Fourier basis functions (φS)S⊆[n] by

p ) we dene the product

∏

φS(x) =

φ(xi).

Given f ∈ L2({−1, 1}n, π⊗n
i.e.,

p ) we write f (S) for the associated Fourier coefcient;

i∈S

f (S) = E

x∼π⊗n
p

[ f (x) φS(x)].

Thus we have the biased Fourier expansion

∑

f (x) =

f (S) φS(x).

S⊆[n]

Although the notation is very similar to that of the classic uniform-distribution

Fourier analysis, we caution that in general,

φSφT 6= φS4T .

Example 8.41. Let χi ∈ L2({−1, 1}n, π⊗n
xi, viewed under the p-biased distribution. We have

p ) be the ith dictator function, χi(x) =

φ(xi) =

xi − µ
σ

=⇒ xi = µ + σφ(xi),

and the latter is evidently f ’s (biased) Fourier expansion. That is,

χi(;) = µ,

χi({i}) = σ,

χi(S) = 0 otherwise.

This example lets us see a link between a function’s “usual” Fourier expan-
sion and its biased Fourier expansion. (For more on this, see Exercise 8.25.)
Let’s abuse notation a little by writing simply φi instead of φ(xi). We have
the formulas

φi =

xi − µ
σ

⇐⇒ xi = µ + σφi,

(8.5)

and we can go from the usual Fourier expansion to the biased Fourier expan-
sion simply by plugging in the latter.

Example 8.42. Recall the “selection function” Sel : {−1, 1}3 → {−1, 1} from
Exercise 1.1(j); Sel(x1, x2, x3) outputs x2 if x1 = −1 and outputs x3 if x1 = 1.
The usual Fourier expansion of Sel is

Sel(x1, x2, x3) = 1

2 x2 + 1
Using the substitution from (8.5) we get
2 (µ + σφ3) − 1
Sel(x1, x2, x3) = 1
2 + 1

2 (µ + σφ2) + 1
2 − 1

2 µ)σ φ2 + ( 1

= µ + ( 1

2 x3 − 1

2 x1x2 + 1

2 x1x3.

2 (µ + σφ1)(µ + σφ2) + 1

2 (µ + σφ1)(µ + σφ3)

2 µ)σ φ3 − 1

2 σ2 φ1φ2 + 1

2 σ2 φ1φ3.

(8.6)

Copyright © Ryan O’Donnell, 2014, 2015, 2016, 2017, 2018, 2019, 2020, 2021.



<!-- pdf-page: 222 -->
222

8. Generalized domains

Thus if we write Sel(p) for the selection function thought of as an element of
L2({−1, 1}3, π⊗3

p ), we have

ÉSel(p)(;) = µ, ÉSel(p)(2) = ( 1
ÉSel(p)({1, 2}) = − 1

2 σ2, ÉSel(p)({1, 3}) = 1

2 µ)σ, ÉSel(p)(3) = ( 1

2 µ)σ,
2 σ2, ÉSel(p)(S) = 0 else.

2 + 1

2 − 1

By the Fourier formulas of Section 8.2 we can deduce, e.g., that E[Sel(p)] = µ,
Inf1[Sel(p)] = (− 1

2 σ2)2 + ( 1

2 σ2)2 = 1

2 σ4, etc.

Let’s codify a piece of notation from this example:

Notation 8.43. Let f : {−1, 1}n → and let p ∈ (0, 1). We write f (p) for the
function when viewed as an element of L2({−1, 1}n, π⊗n

p ).

We now discuss derivative operators. We would like to dene an opera-
p ) that acts like differentiation on the biased Fourier

tor Di on L2({−1, 1}n, π⊗n
expansion. For example, referring to (8.6) we would like to have

D3Sel(p) = ( 1

2 + 1

2 µ)σ + 1

2 σ2 φ1.

In general we are seeking ∂
∂φi
ship (8.5), satises

which, by basic calculus and the relation-

∂
∂φi

=

∂xi
∂φi

·

∂
∂xi

= σ ·

∂
∂xi

.

Recognizing ∂
∂xi
lowing:

as the “usual” ith derivative operator, we are led to the fol-

Denition 8.44. For i ∈ [n], the ith (discrete) derivative operator Di on
L2({−1, 1}n, π⊗n

p ) is dened by

Di f (x) = σ ·

f (x(i7→1)) − f (x(i7→−1))
2

.

Note that this denes a different operator for each value of p. We sometimes
write the above denition as

Dφi

= σ · Dxi

.

With respect to the biased Fourier expansion of f ∈ L2({−1, 1}n, π⊗n
ator Di satises

p ) the oper-

∑

Di f =

f (S) φS\{i}.

(8.7)

S3i

Given this denition we can derive some additional formulas for inu-

ences, including a generalization of Proposition 2.21:

Copyright © Ryan O’Donnell, 2014, 2015, 2016, 2017, 2018, 2019, 2020, 2021.



<!-- pdf-page: 223 -->
8.4. p-biased analysis

223

Proposition 8.45. Suppose f ∈ L2({−1, 1}n, π⊗n
range {−1, 1}). Then

p ) is Boolean-valued (i.e., has

for each i ∈ [n], and

Infi[ f ] = σ2 Pr
x∼π⊗n
p

[ f (x) 6= f (x⊕i)]

I[ f ] = σ2 E

x∼π⊗n
p

[sens f (x)].

If furthermore f is monotone, then Infi[ f ] = σ f (i).

Proof. Using Denition 8.44’s notation we have

Infi[ f ] = E
πp

[(Dφi

f )2] = σ2 E
πp

[(Dxi

f )2].

f )2 is the 0-1 indicator that i is pivotal for f , the rst formula
Since (Dxi
follows. The second formula follows by summing over i. Finally, when f is
monotone we furthermore have that (Dxi

Infi[ f ] = σ2 E
πp

[Dxi

f ] = σ E
πp

f )2 = Dxi
[Dφi

f and hence
f ] = σ f (i),

as claimed.



The remainder of this section is devoted to the topic of threshold phenom-
ena in Boolean functions. Much of the motivation for this comes from theory
of random graphs, which we now briey introduce.

Denition 8.46. Given an undirected graph G on v ≥ 2 vertices, we identify
it with the string in {True,False}(v
2) which indicates which edges are present
(True) and which are absent (False). We write G (v, p) for the distribution

⊗(v
2)
p

; this is called the Erd˝os–Rényi random graph model. Note that if we
edges.

π
permute the v vertices of a graph, this induces a permutation on the
A (v-vertex) graph property is a Boolean function f : {True,False}(v
that is invariant under all v! such permutations of its input; colloquially, this
means that f “does not depend on the names of the vertices”.

2) → {True,False}

v
2



Graph properties are always transitive-symmetric functions in the sense of
Denition 2.10.

Example 8.47. The following are all v-vertex graph properties:

Conn(G) = True if G is connected;

3Col(G) = True if G is 3-colorable;

Cliquek(G) = True if G is contains a clique on at least k vertices;




Majn(G) = True (assuming n =

is odd) if G has at least

/2 edges;

v
2

v
2

χ[n](G) = True if G has an odd number of edges.

Copyright © Ryan O’Donnell, 2014, 2015, 2016, 2017, 2018, 2019, 2020, 2021.



<!-- pdf-page: 224 -->
224

8. Generalized domains

Note that each of these actually denes a family of Boolean functions, one
for each value of v; this is the typical situation in the study of graph proper-
ties. An example of a function f : {True,False}(v
2) → {True,False} that is not a
graph property is the one dened by f (G) = True if vertex #1 has at least one
neighbor; this f is not invariant under permuting the vertices.

Graph properties which are monotone are particularly nice to study; these
are the ones for which adding edges can never make the property go from True
to False. The properties Conn, Cliquek, and Majn dened above are all mono-
tone, as is ¬3Col. Now suppose we take a monotone graph property, say, Conn.
A typical question in random graph theory would be, “how many edges does a
graph need to have before it is likely to be connected?” Or more precisely, how
does PrG∼G (v,p)[Conn(G) = True] vary as p increases from 0 to 1?

There’s no need to ask this question just for graph properties. Given any
monotone Boolean function f : {True,False}n → {True,False} it is intuitively
[ f (x) = True] to in-
clear that when p increases from 0 to 1 this causes Prπp
crease from 0 to 1 (unless f is a constant function). As illustration, we show a
[ f (x) = True] versus p for the dictator function, AND2, and Maj101.
plot of Prπp

Figure 8.1. Plot of Prπp [ f (x) = True] versus p for f a dictator (dotted),
f = AND2 (dashed), and f = Maj101 (solid)

The Margulis–Russo Formula quanties the rate at which Prπp

[ f (x) =
True] increases with p; specically, it relates the slope of the curve at p to the
total inuence of f under π⊗n
p . To prove the formula we switch to ±1 notation.

Margulis–Russo Formula. Let f : {−1, 1}n → . Recalling Notation 8.43
and the relation µ = 1 − 2p, we have

d
dµ

E[ f (p)] =

1

σ

·

n∑

i=1

̂f (p)(i).

(8.8)

Copyright © Ryan O’Donnell, 2014, 2015, 2016, 2017, 2018, 2019, 2020, 2021.



<!-- pdf-page: 225 -->
8.4. p-biased analysis

In particular, if f : {−1, 1}n → {−1, 1} is monotone, then

d
d p

Pr
x∼π⊗n
p

[ f (x) = −1] =

d
dµ

E[ f (p)] =

1
σ2

· I[ f (p)].

Proof. Treating f as a multilinear polynomial over x1, . . . , xn we have

E[ f (p)] = Tµ f (1, . . . , 1) = f (µ, . . . , µ)

(this also follows from Exercise 1.4). By basic calculus,

d
dµ

f (µ, . . . , µ) =

n∑

i=1

Dxi

f (µ, . . . , µ).

225

(8.9)

But

Dxi

f (µ, . . . , µ) = E[Dxi

f (p)] =

1

σ

E[Dφi

f (p)] =

̂f (p)(i),

1

σ

completing the proof of (8.8). As for (8.9), the second equality follows immedi-
ately from Proposition 8.45. The rst equality holds because µ = 1 − 2p and

E[ f ] = 1 − 2 Pr[ f = −1]; the two factors of −2 cancel.

Remark 8.48. If f : {True,False}n → {True,False} is a nonconstant monotone
[ f (x) = True] is a
function, the Margulis–Russo Formula implies that Prπp
strictly increasing function of p, because I[ f (p)] is always positive.

Looking again at Figure 8.1 we see that the plot for Maj101 looks very
much like a step function, jumping from nearly 0 to nearly 1 around the
critical value p = 1/2. For Majn, this “sharp threshold at p = 1/2” becomes
more and more pronounced as n increases. This is clearly suggested by the
Margulis–Russo Formula: the derivative of the curve at p = 1/2 is equal to
I[Majn] (the usual, uniform-distribution total inuence), which has the very
large value Θ(
n) (Theorem 2.33). Such sharp thresholds exist for many
Boolean functions; we give some examples:

p

Example 8.49. In Exercise 8.23 you are asked to show that for every ≤ > 0
there is a C such that

Pr
π1/2−C/

p

n

[Majn = True] ≤ ≤,

Pr
π1/2+C/

p

n

[Majn = True] ≥ 1 − ≤.

Regarding the Erd˝os–Rényi graph model, the following facts are known:

Pr
G∼G (v,p)

[Cliquelog v(G) = True] −−−−→
v→∞

Pr
G∼G (v,p)

[Conn(G) = True] −−−−→
v→∞





0 if p < 1/4,

1 if p > 1/4.

0 if p < ln v
1 if p > ln v

v (1 − log log v
log v ),
v (1 + log log v
log v ).

Copyright © Ryan O’Donnell, 2014, 2015, 2016, 2017, 2018, 2019, 2020, 2021.



<!-- pdf-page: 226 -->
226

8. Generalized domains

In the above examples you can see that the “jump” occurs at various values
of p. To investigate this phenomenon, we rst single out the value for which
Prπp

[ f (x) = True] = 1/2:

Denition 8.50. Let f : {True,False}n → {True,False} be monotone and non-
constant. The critical probability for f , denoted pc, is the unique value
[ f (x) = True] = 1/2. We also write qc = 1 − pc,
in (0, 1) for which Prx∼π⊗n
µc = qc − pc = 1 − 2pc, and σc =

4pc qc.



p

In Exercise 8.27 you are asked to verify that pc is well dened.

Looking at the connectivity property from Example 8.49 we see that not
[Conn = True] jump from near 0 to near 1 in an interval of
only does Prπp
the form pc ± o(1), it actually makes the jump in an interval of the form
pc(1 ± o(1)). This latter phenomenon is (roughly speaking) what is meant
by a “sharp threshold”. To investigate this further, suppose that f is a (non-
[ f (x) = True] at
constant) monotone function and ∆ is the derivative of Prπp
[ f (x) = True] to jump from near 0 to
p = pc. Intuitively, we would expect Prπp
near 1 in an interval of around pc of width about 1/∆. Thus a “sharp thresh-
old” should roughly correspond to the case that 1/∆ is small even compared
to min(pc, qc). The Margulis–Russo Formula says that ∆ = 1
I[ f (p c)], and
σ2
c
since min(pc, qc) is proportional to 4pc qc = σ2
c it follows that 1/∆ is “small”
compared to min(pc, qc) if and only if I[ f (p c)] is “large”. Thus we have a neat
criterion:
Sharp threshold principle: Let f : {True,False}n → {True,False} be monotone.
[ f (x) = True] has a “sharp threshold” if and only
Then, roughly speaking, Prπp
if f has “large” (“superconstant”) total inuence under its critical probability
distribution.

Of course this should all be made a bit more precise; see Exercise 8.28
for details. In light of this principle, we may try to prove that a given f
has a sharp threshold by proving that I[ f (p c)] is not “small”. In turn, this
strongly motivates the problem of “characterizing” Boolean-valued functions
f ∈ L2({−1, 1}n, π⊗n
p ) for which I[ f ] is small. Friedgut’s Junta Theorem, men-
tioned at the end of Chapter 3.1 and proved in Chapter 9.6, tells us that in
the uniform distribution case p = 1/2, the only way I[ f ] can be small is if f
is close to a junta. In particular, any monotone graph property with pc = 1/2
must have a very large derivative d
[ f = True] at p = pc: since the func-
d p Prπp
tion is transitive-symmetric, all n coordinates are equally inuential and it
can’t be close to a junta. These results also hold so long as p is bounded
away from 0 and 1; see Chapter 10.3. However, many interesting monotone
graph properties have pc very close to 0: e.g., connectivity, as we saw in Ex-
ample 8.49. Characterizing the functions f ∈ L2({−1, 1}n, π⊗n
p ) with small I[ f ]

Copyright © Ryan O’Donnell, 2014, 2015, 2016, 2017, 2018, 2019, 2020, 2021.



<!-- pdf-page: 227 -->
8.5. Abelian groups

227

when p = on(1) is a trickier task; see the work of Friedgut, Bourgain, and
Hatami described in Chapter 10.5.

8.5. Abelian groups

The previous section covered the case of f ∈ L2(Ωn, π⊗n) with |Ω| = 2; there,
we saw it could be helpful to look at explicit Fourier bases. When |Ω| ≥ 3
this is often not helpful, especially if the only “operation” on the domain is
}n → , then it’s best to just work
equality. For example, if f : {
,
abstractly with the orthogonal decomposition. However, if there is a notion
of, say, “addition” in Ω, then there is a natural, canonical Fourier basis for
L2(Ω, π) when π is the uniform distribution.

,

More precisely, suppose the domain Ω is a nite abelian group G, with
operation + and identity 0. We will consider the domain G under the uni-
form probability distribution π; this is quite natural because π is translation-
invariant: π(X ) = π(t + X ) for any X ⊆ G, t ∈ G. In this setting it is more
convenient to allow functions with range the complex numbers; thus we come
to the following denition:

Denition 8.51. Let G be a nite abelian group with operation + and iden-
+ we write L2(G n) for the complex inner product space of
tity 0. For n ∈
functions f : G n → , with inner product

〈 f , g〉 = E

x∼G n

[ f (x)g(x)].

Here and throughout this section x ∼ G n denotes that x is drawn from the
uniform distribution on G n.

Everything we have done in this chapter for the real inner product space
L2(Ωn, π⊗n) generalizes easily to the case of a complex inner product; the main
difference is that Plancherel’s Theorem becomes

∑

∑

〈 f , g〉 =

f (α) g(α) =

〈 f =S, g=S〉.

See Exercise 8.32 for more.

α∈ n

<m

S⊆[n]

A natural Fourier basis for L2(G) comes from a natural family of functions
G → , namely the characters. These are dened to be the group homomor-
× is the abelian group of nonzero complex
×, where
phisms from G to
numbers under multiplication.

Denition 8.52. A character of the (nite) group G is a function χ : G → ×
which is a homomorphism; i.e., satises χ(x + y) = χ(x)χ(y). Since G is nite
there is some m ∈ + such that 0 = x+ x+· · ·+ x (m times) for each x ∈ G. Thus
1 = χ(0) = χ(x)m, meaning the range of χ is in fact contained in the mth roots
of unity. In particular, |χ(x)| = 1 for all x ∈ G.

Copyright © Ryan O’Donnell, 2014, 2015, 2016, 2017, 2018, 2019, 2020, 2021.



<!-- pdf-page: 228 -->
228

8. Generalized domains

We have the following easy facts:

Fact 8.53. If χ and φ are characters of G, then so are χ and φ · χ.

Proposition 8.54. Let χ be a character of G. Then either χ ≡ 1 or E[χ] = 0.

Proof. If χ 6≡ 1, pick some y ∈ G such that χ(y) 6= 1. Since x + y is uniformly
distributed on G when x ∼ G,

[χ(x)] = E
x∼G
Since χ(y) 6= 1 it follow that E[χ(x)] must be 0.

[χ(x + y)] = E
x∼G

E
x∼G

[χ(x)χ(y)] = χ(y) E
x∼G

[χ(x)].



Proposition 8.55. The set of all characters of G is orthonormal. (As a conse-
quence, G has at most dim(L2(G)) = |G| characters.)

Proof. First, if χ is a character, then 〈χ, χ〉 = E[|χ|2] = 1 because |χ| ≡ 1. Next,
if φ is another character distinct from χ then 〈φ, χ〉 = E[φ · χ]. But φ · χ is a
character by Fact 8.53, and φ · χ = φ/χ 6≡ 1 because φ and χ are distinct; here

we used χ = 1/χ because |χ| ≡ 1. Thus 〈φ, χ〉 = 0 by Proposition 8.54.

As we will see next, G in fact has exactly |G| characters. It thus follows
from Proposition 8.55 that the set of all characters (which includes the con-
stant 1 function) constitutes a Fourier basis for L2(G).

To check that each nite abelian group G has |G| distinct characters, we
begin with the case of a cyclic group, m for some m. In this case we know
that every character’s range will be contained in the mth roots of unity.

Denition 8.56. Fix an integer m ≥ 2 and write ω for the mth root of unity
exp(2πi/m). For 0 ≤ j < m, we dene χ j : m → by χ j(x) = ω jx. It is easy to
see that these are distinct characters of m.

Thus the functions χ0 ≡ 1, χ1, . . . , χm−1 form a Fourier basis for L2( m).
Furthermore, Proposition 8.13 tells us that we can get a Fourier basis for
L2( n

m) by taking all products of these functions.

Denition 8.57. Continuing Denition 8.56, let n ∈
dene χα :

n
m → by

n∏

χα(x) =

χα j

(x j).

+. For α ∈

n
<m we

j=1
These functions are easily seen to be (all of the) characters of the group n
m,
and they constitute a Fourier basis of L2( n

m).

Most generally, by the Fundamental Theorem of Finitely Generated Abelian

Groups we know that any nite abelian G is a direct product of cyclic groups
of prime-power order. In Exercise 8.35 you are asked to check that you get all
of the characters of G – and hence a Fourier basis for L2(G) – by taking all

Copyright © Ryan O’Donnell, 2014, 2015, 2016, 2017, 2018, 2019, 2020, 2021.



<!-- pdf-page: 229 -->
8.6. Highlight: Randomized decision tree complexity

229

products of the associated cyclic groups’ characters. In the remainder of the
section we mostly stick to groups of the form n

m for simplicity.

Returning to the characters χ0, . . . , χm−1 from Denition 8.56, it is easy
to see (using ωm = 1) that they satisfy χ j · χ j′ = χ j+ j′ (mod m) and also 1/χ j =
χ j = χ− j (mod m). Thus the characters themselves form a group under mul-
tiplication, isomorphic to m. As in Chapter 3.2, we index them using the
notation ̂
m. More generally, indexing the Fourier basis/characters of L2( n
m)
by ̂n

m instead of multi-indices, we have:

Fact 8.58. The characters (χα)

α∈̂n
m

of

n
m form a group under multiplication:

• χα · χβ = χα+β,
• 1/χα = χα = χ−α.

As mentioned, the salient feature of L2(G) distinguishing it from other
spaces L2(Ω, π) is that there is a notion of addition on the domain. This
means that convolution plays a major role in its analysis. We generalize the
denition from the setting of

n
2 :

Denition 8.59. Let f , g ∈ L2(G). Their convolution is the function f ∗ g ∈
L2(G) dened by

( f ∗ g)(x) = E
y∼G

[ f (y)g(x − y)] = E
y∼G

[ f (x − y)g(y)].

Exercise 8.36 asks you to check that convolution is associative and com-

mutative, and that the following generalization of Theorem 1.27 holds:

Theorem 8.60. Let f , g ∈ L2(G). Then Åf ∗ g(α) = f (α) g(α).

We conclude this section by mentioning vector space domains. When
doing Fourier analysis over the group n
m, it is natural for subgroups to arise.
Things are simplest when the only subgroups of m are the trivial ones, {0}
n′
m for some n′ ≤
and m; in this case, all subgroups will be isomorphic to
n. Of course, this simple situation occurs if and only if m is equal to some
n
prime p. In that case,
p as an n-dimensional
p can be thought of as a eld,
vector space over this eld, and its subgroups as subspaces. We use the
notation n
p to index the Fourier basis/characters;
this generalizes the notation introduced for p = 2 in Chapter 3.2. Indeed, all
of the notions from Chapters 3.2 and 3.3 regarding afne subspaces and
restrictions thereto generalize easily to L2( n

p in this setting and write n

p).

8.6. Highlight: Randomized decision tree complexity

A decision tree T for f : {−1, 1}n → {−1, 1} can be thought of as a deterministic
algorithm which, given adaptive query access to the bits of an unknown string

Copyright © Ryan O’Donnell, 2014, 2015, 2016, 2017, 2018, 2019, 2020, 2021.



<!-- pdf-page: 230 -->
230

8. Generalized domains

x ∈ {−1, 1}n, outputs f (x). For example, to describe a natural decision tree for
f = Maj3 in words: “Query x1, then x2. If they are equal, output their value;
otherwise, query and output x3.” For a worst-case input (one where x1 6= x2)
this algorithm has a cost of 3, meaning it makes 3 queries. The cost of the
worst-case input is the depth of the decision tree.

As is often the case with algorithms it can be advantageous to allow ran-
domization. For example, consider using the following randomized query
algorithm for Maj3: “Choose two distinct input coordinates at random and
query them. If they are equal, output their value; otherwise, query and out-
put the third input coordinate.” Now for every input there is at least a 1/3
chance that the algorithm will nish after only 2 queries. Indeed, if we dene
the cost of an input x to be the expected number of queries the algorithm
makes on it, it is easy to see that the worst-case inputs for this algorithm
have cost (1/3) · 2 + (2/3) · 3 = 8/3 < 3.

Let’s formalize the notion of a randomized decision tree:

Denition 8.61. Given f : {−1, 1}n → , a (zero-error) randomized decision
tree T computing f is formally dened to be a probability distribution over
(deterministic) decision trees that compute f . The cost of T on input x ∈
{−1, 1}n is dened to be the expected number of queries T makes on x when
T ∼ T . The cost of T itself is dened to be the maximum cost of any input.
Finally, the (zero-error) randomized decision tree complexity of f , denoted
RDT( f ), is the minimum cost of a randomized decision tree computing f .

We can get further savings from randomization if we are willing to assume
that the input x is chosen randomly. For example, if x ∼ {−1, 1}3 is uniformly
random then any of the deterministic decision trees for Maj3 will make 2
queries with probability 1/2 and 3 queries with probability 1/2, for an overall
expected 5/2 < 8/3 < 3 queries.

Denition 8.62. Let T be a randomized decision tree. We dene

δi(T ) = Pr

x∼{−1,1}n,
T∼T

[T queries xi],

∆(T ) =

n∑

i=1

δi(T ) =

E
x∼{−1,1}n,
T∼T

[# of coordinates queried by T on x].

(8.10)

Given f : {−1, 1}n → , we dene ∆( f ) to be the minimum of ∆(T ) over all
randomized decision trees T computing f .

We can also generalize these denitions for functions f ∈ L2(Ω, π⊗n). A
deterministic decision tree over domain Ω is the natural generalization in
which each internal query node has |Ω| outgoing edges, labeled by the ele-
ments of Ω. We write δ(π)
(T ), ∆(π)(T ), ∆(π)( f ) for the generalizations to trees

i

Copyright © Ryan O’Donnell, 2014, 2015, 2016, 2017, 2018, 2019, 2020, 2021.



<!-- pdf-page: 231 -->
8.6. Highlight: Randomized decision tree complexity

231

over Ω; in the case of L2({−1, 1}n, π⊗n
(πp) for brevity.

p ) we use the superscript (p) instead of

It follows immediately from the denitions that for any f ∈ L2(Ωn, π⊗n),

∆(π)( f ) ≤ RDT( f ) ≤ DT( f ).

Remark 8.63. In the denition of ∆(π)( f ) it is equivalent if we only allow
deterministic decision trees; this is because in (8.10) we can always choose
the “best” deterministic T in the support of T .

Example 8.64. It follows from our discussions that RDT(Maj3) ≤ 8/3 and
∆(Maj3) ≤ 5/2; indeed, it’s not hard to show that both of these bounds are
equalities.
In Exercise 8.38 you are asked to generalize to the recursive
majority of 3 function on n = 3d inputs; it satises DT(Maj⊗d

3 ) = 3d = n, but

RDT(Maj⊗d

3 ) ≤ (8/3)d = nlog3(8/3) ≈ n.89,
3 ) ≤ (5/2)d = nlog3(5/2) ≈ n.83.

∆(Maj⊗d

Incidentally, these bounds are not asymptotically sharp; estimating RDT(Maj⊗d
3 )
in particular is a well-studied open problem.

Example 8.65. In Exercise 8.39 you are asked to show that for the logical OR
function, ∆(p)(ORn) = 1−(1−p)n
, which is roughly 2 for p = 1/2 but is asymptotic
to n/(2 ln 2) at the critical probability pc.

p

Example 8.64 illustrates a mildly surprising phenomenon: using random-
ness it’s possible to evaluate certain unbiased n-bit functions f while reading
only a 1/nΘ(1) fraction of the input bits. This is even more interesting when f
is transitive-symmetric like Maj⊗d
3 . In that case it’s not hard to show (Exer-
cise 8.37) that any randomized decision tree T computing f can be converted
to one where ∆(T ) remains the same but all δi(T ) are equal to ∆( f )/n. Then f
can be evaluated despite the fact that each input bit is only queried with prob-
ability 1/nΘ(1).

In this section we explore the limits of this phenomenon. In particular,
a longstanding conjecture of Yao [Yao77] says that this is not possible for
monotone graph properties:

Yao’s Conjecture. Let f : {−1, 1}n → {−1, 1} be a nonconstant monotone v-
vertex graph property, where n =

. Then RDT( f ) ≥ Ω(n).



v
2

Toward this conjecture we will present a lower bound due to O’Donnell,
Saks, Schramm, and Servedio [OSSS05]. (Two other incomparable bounds
are discussed in the notes for this chapter.) It has the advantages that it
works for the more general class of transitive-symmetric functions and that
it even lower-bounds ∆(p c)( f ):

Copyright © Ryan O’Donnell, 2014, 2015, 2016, 2017, 2018, 2019, 2020, 2021.



<!-- pdf-page: 232 -->
232

8. Generalized domains

Theorem 8.66. Let f : {−1, 1}n → {−1, 1} be a nonconstant monotone transitive-
symmetric function with critical probability pc. Then

∆(p c)( f ) ≥ (n/σc)2/3.

Theorem 8.66 is essentially sharp in several interesting cases. Whenever
the critical probability pc is Θ(1/n) or 1 − Θ(1/n) then σc = Θ(1/
n) and The-
orem 8.66 gives the strongest possible bound, ∆(p c)( f ) ≥ Ω(n). This occurs,
e.g., for the ORn function (Example 8.65). Furthermore, Theorem 8.66 can
be tight up to a logarithmic factor when pc = 1/2 as the following theorem of
Benjamini, Schramm, and Wilson shows:

p

Theorem 8.67. [BSW05]. There exists an innite family of monotone transitive-
symmetric functions f n : {−1, 1}n → {−1, 1} with critical probability pc = 1/2 and
∆( f ) ≤ O(n2/3 log n).

Theorem 8.66 follows easily from two inequalities [OS06, OS07], [OSSS05],

which we now present:

OS Inequality. Let f ∈ L2({−1, 1}n, π⊗n

p ). Then

n

i=1

f (i) ≤ ‖ f ‖2 ·



In particular, if f has range {−1, 1} and is monotone, then I[ f ] ≤ σ

∆(p)( f ).


∆(p)( f ).

OSSS Inequality. Let f ∈ L2(Ωn, π⊗n) have range {−1, 1} and let T be any
randomized decision tree computing f . Then

Var[ f ] ≤

n∑

i=1

δ(π)
i

(T ) · Infi[ f ].

Remark 8.68. An interesting corollary of the OSSS Inequality is that

MaxInf[ f ] ≥ Var[ f ]/∆(π)( f ) ≥ Var[ f ]/DT( f ) ≥ Var[ f ]/ deg( f )3,

the last inequality assuming Ω = {−1, 1}. See Exercise 8.44.

These two inequalities can be thought of as strengthenings of basic Fourier
inequalities which take into account the decision tree complexity of f . The
OS Inequality essentially generalizes the result that majority functions maxi-
f (i); i.e., Theorem 2.33. The OSSS Inequality is a generalization
mizes
of the Poincaré Inequality, discounting the inuences of coordinates that are
rarely read.

n

i=1

We will rst derive the query complexity lower bound Theorem 8.66 from
the OS and OSSS Inequalities. We will then prove the latter two inequalities.

Proof of Theorem 8.66. We consider f to be an element of L2({−1, 1}n, π⊗n
).
p c
Let T be a randomized decision tree achieving ∆(p c)( f ). In the OSSS Inequal-
ity, we have Var[ f ] = 1 since pc is the critical probability and Infi[ f ] = I[ f ]/n

Copyright © Ryan O’Donnell, 2014, 2015, 2016, 2017, 2018, 2019, 2020, 2021.



<!-- pdf-page: 233 -->
8.6. Highlight: Randomized decision tree complexity

233

for each i ∈ [n] since f is transitive-symmetric. Thus

1 ≤

∑

i=1

δ(p c)
i

(T ) ·

I[ f ]
n

=⇒ n ≤ ∆(p c)( f ) · I[ f ] ≤ σ∆(p c)( f )3/2,

where we used the OS Inequality. The theorem follows by rearranging.



Now we prove the OS and OSSS Inequalities, starting with the latter. We

will need a simple lemma that uses the decomposition f = Ei f + Li f .

Lemma 8.69. Let f , g ∈ L2(Ωn, π⊗n) and let j ∈ [n]. Given ω ∈ Ω, write f|ω
for the restriction of f in which the jth coordinate is xed to value ω, and
similarly for g. Then

Cov[ f , g] =

E
ω,ω′∼π
independent

[Cov[ f|ω, g|ω′]] + 〈L j f , L j g〉.

Proof. Since the covariances and Laplacians are unchanged when constants
are added, we may assume without loss of generality that E[ f ] = E[g] = 0.
Then Cov[ f , g] = 〈 f , g〉 and

E
ω,ω′

[Cov[ f|ω, g|ω′]] = E
ω,ω′
[〈 f|ω, g|ω′〉] − E[ f ] E[g] = E
ω,ω′

[〈 f|ω, g|ω′〉 − E[ f|ω] E[g|ω′]]

= E
ω,ω′

[〈 f|ω, g|ω′〉] = 〈E j f , E j g〉.

Thus the stated equality reduces to the basic (Exercise 8.8) identity

〈 f , g〉 = 〈E j f , E j g〉 + 〈L j f , L j g〉.



Proof of the OSSS Inequality. More generally we show that if g : {−1, 1}n →
{−1, 1} is also an element of L2(Ωn, π⊗n), then

Cov[ f , g] ≤

n∑

i=1

δ(π)
i

(T ) · Infi[g].

(8.11)

The result then follow by taking g = f . We may also assume that T = T is a
single deterministic tree computing f ; this is because (8.11) is linear in the
quantities δ(π)
(T ). We prove (8.11) by induction on the structure of T. If T is
depth-0, then f must be a constant function; hence Cov[ f , g] = 0 and (8.11) is
trivial. Otherwise, let j ∈ [n] be the coordinate queried at the root of T. For
each ω ∈ Ω, write Tω for the subtree of T given by the ω-labeled child of the
root. By applying Lemma 8.69 and induction (noting that Tω computes the

i

Copyright © Ryan O’Donnell, 2014, 2015, 2016, 2017, 2018, 2019, 2020, 2021.



<!-- pdf-page: 234 -->
234

8. Generalized domains

restricted function f|ω), we get

Cov[ f , g] =

[Cov[ f|ω, g|ω′]] + 〈L j f , L j g〉



(Tω) · Infi[gω′]

+ 〈L j f , L j g〉

δ(π)
i

(T) · Infi[g] + 〈 f , L j g〉

(in part since E[L j g] = 0)

δ(π)
i

(T) · Infi[g] + E[|L j g|]

(since | f | ≤ 1)

δ(π)
i

(T) · Infi[g],

E
ω,ω′∼π
independent
∑

i6= j

ω,ω′∼π
∑

δ(π)
i

≤ E

=

≤

=

i6= j
∑

i6= j
n∑

i=1

where the last step used δ(π)
inductive proof of (8.11).

j

(T) = 1 and Proposition 8.24. This completes the


Finally, we prove the OS Inequality. For this we require a denition.

Denition 8.70. Let (Ω, π) be a nite probability space and T a deterministic
decision tree over Ω. The decision tree process associated to T generates
a random string x distributed according to π (and some additional random
variables), as follows:

(1) Start at the root node of T; say it queries coordinate j1. Choose x j1

∼ π

and follow the outgoing edge labeled by the outcome.

(2) Suppose the node of T which is reached queries coordinate j2. Choose

x j2

∼ π and follow the outgoing edge labeled by the outcome.

(3) Repeat until a leaf node is reached. Then, dene J = { j1, j2, j3, . . . } ⊆ [n]

to be the set of coordinates queried.

(4) Draw the as-yet-unqueried coordinates, denoted x

, from π⊗J.

J

Despite the fact that the coordinates xi are drawn in a random, dependent
order, it’s not hard to see (Exercise 8.42) that the nal string x = (xJ, x
) is
distributed according the product distribution π⊗n.

J

Proof of the OS Inequality. We will prove the claim
the “in particular” statement follows immediately from Proposition 8.45. Fix
a deterministic decision tree T achieving ∆(p)( f ) (see Remark 8.63) and let
x = (xJ, x
) be drawn from the associated decision tree process. Using the
notation φ from Denition 8.39 we have

i=1

J

f (i) ≤ ‖ f ‖2·

n



∆(p)( f );

n∑

i=1

f (i) = E

J,xJ ,xJ

[ f (x)

n

i=1

φ(xi)] = E
J,xJ

[ f (xJ) E
xJ

[

n

i=1

φ(xi)]].

Copyright © Ryan O’Donnell, 2014, 2015, 2016, 2017, 2018, 2019, 2020, 2021.



<!-- pdf-page: 235 -->
8.7. Exercises and notes

235

Here we abused notation slightly by writing f (xJ); in the decision tree process,
f ’s value is determined once xJ is. Since E[φ(xi)] = 0 for each i 6∈ J we may
continue:

E
J,xJ

[ f (xJ) E
xJ

[

n

i=1

[ f (xJ)

n

i=1

φ(xi)]] = E
J,xJ


[ f (xJ)2]

≤

E
J,xJ



1{i∈J}φ(xi)]

[ n

E
J,xJ

i=1

1{i∈J}φ(xi)

]

2

,

by Cauchy–Schwarz. Now
To complete the proof it sufces to show that
]
2

EJ,xJ

[ n

E
J,xJ

i=1

1{i∈J}φ(xi)

= ∆(p)( f ).

[ f (xJ)2] is simply ‖ f ‖2 since T computes f .

To see this, expand the square:

[ n

i=1

E
J,xJ

1{i∈J}φ(xi)

]

2

=

n∑

i=1

E
J,xJ

[1{i∈J}φ(xi)2] +

∑

i6=i′

E
J,xJ

[1{i,i′∈J}φ(xi)φ(xi′)].

Conditioned on i ∈ J the quantity E[φ(xi)2] is simply 1. Thus

n∑

i=1

E
J,xJ

[1{i∈J}φ(xi)2] =

n∑

i=1

Pr[i ∈ J] = ∆(p)( f ).

It remains to show that EJ,xJ

[1{i,i′∈J}φ(xi)φ(xi′)] = 0 whenever i 6= i′. Sup-
pose we condition on the event that i, i′ ∈ J and we further condition on i
being queried before i′ is queried. Certainly this may affect the conditional
distribution of xi, but the conditional distribution of xi′ remains πp; hence
E[φ(xi′)] = 0 under this conditioning. Of course the same argument holds
when we condition on i′ being queried before i. From this it follows that

EJ,xJ

[1{i,i′∈J}φ(xi)φ(xi′)] is indeed 0, completing the proof.

8.7. Exercises and notes

8.1 Explain how to generalize the denitions and results in Sections 8.1
and 8.2 to general nite product spaces L2(Ω1 × · · · × Ωn, π1 × · · · × πn).
8.2 Verify that Denition 8.1 indeed denes a real inner product space. (Where

is the fact that π has full support used?)
8.3 Verify the formula for f (α) in Denition 8.14.

8.4 Verify that φ0, φ1, φ2 from Example 8.10 indeed constitute a Fourier basis

for Ω = {a, b, c} with the uniform distribution.

8.5 Verify the Fourier expansion in Example 8.15.

8.6 Complete the proof of Proposition 8.16.

Copyright © Ryan O’Donnell, 2014, 2015, 2016, 2017, 2018, 2019, 2020, 2021.



<!-- pdf-page: 236 -->
236

8. Generalized domains

8.7 Prove that the expectation over I operator, EI , is a linear operator on
L2(Ωn, π⊗n) (i.e., EI ( f + g) = EI f +EI g), a projection (i.e., EI ◦EI = EI ), and
self-adjoint (i.e., 〈 f , EI g〉 = 〈EI f , g〉). Deduce that Tρ is also self-adjoint.
8.8 Show for any f , g ∈ L2(Ωn, π⊗n) and j ∈ [n] that f = E j f + L j f and that

〈 f , g〉 = 〈E j f , E j g〉 + 〈L j f , L j g〉.

8.9 Prove Proposition 8.24. (Hint: Exercise 1.17.)
8.10 Let f ∈ L2(Ωn, π⊗n) have range {−1, 1}. Proposition 8.24 tells us that

2 = Infi[ f ].

‖Li f ‖1 = ‖Li f ‖2
(a) Show that ‖Li f ‖p
p ≤ 2pInfi[ f ] for any p ≥ 1.
(b) In case 1 ≤ p ≤ 2, show that in fact ‖Li f ‖p

p ≤ Infi[ f ]. (Hint: Use the
general form of Hölder’s inequality to bound ‖Li f ‖p in terms of ‖Li f ‖1
and ‖Li f ‖2.)

8.11 Generalize all of Exercise 2.35 to the setting of L2(Ωn, π⊗n). Caution: the
two statements referring to ρ ∈ [−1, 1] should refer only to ρ ∈ [0, 1] in this
more general setting.

8.12 Assume |Ω| = m and let π denote the uniform distribution on Ω.

(a) For x ∈ Ωn and y ∼ Nρ(x), write a formula for Pr[yi = ω] in terms of ρ

(there are two cases depending on whether or not xi = ω).

(b) Verify that your formula denes a valid probability distribution on Ω
m−1 ≤ ρ < 0. We may therefore extend the denition of

even when − 1
Nρ to this case. (Cf. the second half of Denition 2.40.)

(c) Verify that for x ∼ π⊗n and y ∼ Nρ(x), the distribution of (x, y) is

symmetric in x and y.
(d) Show that when y ∼ N− 1

m−1

Ω \ {xi}.

(x), each yi is uniformly distributed on

(e) Verify that the formula for Tρ from Proposition 8.28 continues to hold
m−1 ≤ ρ < 0. (Hint: Use the fact that it holds for ρ ∈ [0, 1] and

for − 1
that the formula in part (a) is a polynomial in ρ.)

8.13 Show that Denition 8.30 extends by continuity to

Inf(0)
i

[ f ] =

f (α)2.

∑

#α=1
αi6=0

Extend also Proposition 8.31 to the case of δ = 1.

8.14 Prove explicitly that condition 5 holds in Theorem 8.35.

8.15 Prove that condition 6 must hold in Theorem 8.35 directly from the
uniqueness statement (i.e., without appealing to the explicit construc-
tion).

8.16 Let f ∈ L2(Ωn, π⊗n). Prove directly from the dening Theorem 8.35 that

( f =S)⊆T is equal to f =S if S ⊆ T and is equal to 0 otherwise.

Copyright © Ryan O’Donnell, 2014, 2015, 2016, 2017, 2018, 2019, 2020, 2021.



<!-- pdf-page: 237 -->
8.7. Exercises and notes

237

8.17 Let f ∈ L2(Ωn, π⊗n) and let x ∼ π⊗n. In this exercise you should think
about how the (conditional) expectation of f changes as the random vari-
ables x1, . . . , xn are revealed one at a time.
(a) Recalling that f ⊆[t](x) depends only on x1, . . . , xt, show that the se-
quence of random variables ( f ⊆[t](x))t=0...n is a martingale (where
f ⊆[0] denotes f ;); i.e.,

E[ f ⊆[t](x) | f ⊆[0](x), . . . , f ⊆[t−1](x)] = f ⊆[t−1](x) ∀t ∈ [n].

(This is the Doob martingale for f .)

(b) For each t ∈ [n] dene

dt f = f ⊆[t] − f ⊆[t−1] =

∑

f =S.

S⊆[n]
max(S)=t

Show that E[dt f (x) | f ⊆[0](x), . . . , f ⊆[t−1](x)] = 0.
the martingale difference sequence for f .)

(Here (dt f )t=1...n is

8.18 For f , g ∈ L2(Ωn, π⊗n), prove the following directly from Theorem 8.35:
∑

〈 f , g〉 =

〈 f =S, g=S〉

S⊆[n]

∑

Infi[ f ] =

S3i

‖ f =S‖2
2

n∑

I[ f ] =

k · Wk[ f ]

k=0
Tρ( f =S) = (Tρ f )=S = ρk f =S
n∑

Stabρ[ f ] =

ρk · Wk[ f ].

k=0

8.19 Let f ∈ L2(Ωn, π⊗n) and let S ⊆ [n]. Show that ‖ f =S‖∞ ≤ 2|S|‖ f ‖∞.
8.20 Explicitly verify that Proposition 8.36 holds for the function in Exam-

ples 8.15 and 8.37.

8.21 Let f ∈ L2(Ωn, π⊗n) and let i ∈ S ⊆ [n]. Suppose we take f =S and restrict
its ith coordinate to have value ωi, forming the subfunction g = ( f =S)|ωi
.
Show that g = g=S\{i}. In particular, E[g] = 0 assuming |S| ≥ 2.

8.22 Let f ∈ L2(Ωn, π⊗n) be a symmetric function. Show that if 1 ≤ |S| ≤ |T| ≤ n,

then 1

|S| Var[ f ⊆S] ≤ 1

|T| Var[ f ⊆T ].

8.23 Prove the sharp threshold statement about the majority function made
in Example 8.49. (Hint: Chernoff bound.) In the social choice literature,
this fact is known as the Condorcet Jury Theorem.

8.24 Let p1, . . . , pn ∈ (0, 1) and let π = πp1

⊗ · · · πpn

tribution on {−1, 1}n. Write µi = 1−2pi and σi = 2
Proposition 8.45 to the setting of L2({−1, 1}n, π).

be the associated product dis-
1 − pi. Generalize

pi



p

Copyright © Ryan O’Donnell, 2014, 2015, 2016, 2017, 2018, 2019, 2020, 2021.



<!-- pdf-page: 238 -->
238

8. Generalized domains

8.25 Let f : {−1, 1}n → and consider the general product distribution setting

of Exercise 8.24.
(a) For S = {i1, . . . , i k} ⊆ [n], write DφS
=

Show that DφS

i∈S σi · DxS



.

for Dφi1

◦· · ·◦Dφik

and similarly DxS

.

(b) Writing f (µ) for the function f viewed as an element of L2({−1, 1}n, π),

show that

∏

̂f (p)(S) =

σi · DxS

f (µ1, . . . , µn).

(c) Show that ˆ‖ f (p) ˆ‖∞ ≤



i∈S
i∈S σi · ‖ f ‖∞.

8.26 (a) Generalize Exercise 2.10 by showing that for f ∈ L2({−1, 1}n, π⊗n

p ) with

range {−1, 1},

Pr
x∼π⊗n
p

[i is b-pivotal for f on x] = πp(b)Infi[ f ]

for i ∈ [n] and b ∈ {−1, 1}.

(b) Generalize Proposition 4.7 by showing that if f : {−1, 1}n → {−1, 1} has
DNFwidth( f ) ≤ w, then I[ f (p)] ≤ 4qw ≤ 4w, and if f has CNFwidth( f ) ≤ w,
then I[ f (p)] ≤ 4pw ≤ 4w.

8.27 Fix any α ∈ (0, 1). Let f : {True,False}n → {True,False} be a nonconstant
monotone function. Show that there exists p ∈ (0, 1) such that Prπp
[ f (x) =
True] = α. (Hint: Intermediate Value Theorem.)

8.28 Fix a small constant 0 < ≤ < 1/2. Let f : {True,False}n → {True,False}
be a nonconstant monotone function. Let p0 (respectively, pc, p1) be
[ f (x) = True] = ≤ (respec-
the unique value of p ∈ (0, 1) such that Prπp
tively, 1/2, 1 − ≤).
(This is a valid denition by Exercise 8.27.) Dene
also σ2
c = 4pc(1 − pc). The threshold interval for f is dened to be [p0, p1],
and δ = p1 − p0 is the threshold width. Now let ( f n)n∈
be a sequence
of nonconstant monotone Boolean functions (usually “naturally related”,
with f n’s input length an increasing function of n). Dene the sequences
p0(n), pc(n), p1(n), σ2
c(n), δ(n). We say that the family ( f n) has a sharp
threshold if δ(n)/σ2
c(n) → 0 as n → ∞; otherwise, we say it has a coarse
threshold. (Note: If pc(n) ≤ 1/2 for all n, this is the same as saying that
δ(n)/pc(n) → 0.) Show that if ( f n) has a coarse threshold, then there
exists C < ∞, an innite sequence n1 < n2 < n3 < · · · , and a sequence
(p(ni))i∈

such that:
[ f n i

• ≤ < Prπp(ni )
• I[ f (p(n i))
n i

] ≤ C for all i.

(x) = True] < 1 − ≤ for all i;

(Hint: Margulis–Russo and the Mean Value Theorem.)

8.29 Let f : {−1, 1}n → {−1, 1} be a nonconstant monotone function and let
F : [0, 1] → [0, 1] be the (strictly increasing) function dened by F(p) =
[ f (x) = −1]. Let pc be the critical probability such that F(pc) = 1/2.
Prπp
Assume that pc ≤ 1/2. (This is without loss of generality since we can

Copyright © Ryan O’Donnell, 2014, 2015, 2016, 2017, 2018, 2019, 2020, 2021.



<!-- pdf-page: 239 -->
8.7. Exercises and notes

239

replace f by f †. We often think of pc ø 1/2.) The goal of this exercise is to
show a weak kind of threshold result: roughly speaking, F(p) = o(1) when
p = o(pc) and F(p) = 1 − o(1) when p = ω(pc).
(a) Using the Margulis–Russo Formula and the Poincaré Inequality show

that for all 0 < p < 1,

F ′(p) ≥

F(p)(1 − F(p))
p(1 − p)

.

(b) Show that for all p ≤ pc we have F ′(p) ≥ F(p)

2p and hence d

d p ln F(p) ≥

1
2p .

(c) Deduce that for any 0 ≤ p0 ≤ pc we have F(p0) ≤ 1
2

≤ if p0 ≤ (2≤)2 pc.



p0/pc; i.e., F(p0) ≤

(d) Show that the factor (2≤)2 can be improved to Θ(τ)≤1+τ for any small
constant τ > 0. (Hint: The quadratic dependence on ≤ arose because
we used 1 − F(p) ≥ 1/2 for p ≤ pc; but from part (c) we have the im-
proved bound 1 − F(p) ≥ 1 − τ once p ≤ (2τ)2 pc.)
(e) In the other direction, show that so long as p1 = 1

(2≤)2 pc ≤ 1/2, we have
F(p1) ≥ 1 − ≤. (Hint: Work with ln(1 − F(p)).) In case p1 ≤ 1/2 does not
hold, show that we at least have F(1/2) ≥ 1 −



pc/2.

(f ) The bounds in part (e) are not very interesting when pc is close to 1/2.

p

Show that we also have F(1 − δ) ≥ 1 −

δ/2 (even when pc = 1/2).

8.30 Consider the sequence of functions f n : {True,False}n → {True,False} de-
ned for odd n ≥ 3 as follows: f n(x1, . . . , xn) = Maj3(x1, x2, Majn−2(x3, . . . , xn)).
(a) Show that f n is monotone and has critical probability pc = 1/2.
[ f n(x) = True] versus p (assuming n very large).
(b) Sketch a plot of Prπp
p
(c) Show that I[ f n] = Θ(
n).
(d) Show that the sequence f n has a coarse threshold as dened in Exer-

cise 8.28 (assuming ≤ < 1/4).

8.31 (a) Consider the following probability distributions on strings x ∈ n
2 :

(1) First choose k ∼ {0, 1, 2, . . . , n} uniformly. Then choose x uni-

formly from the set of all strings of Hamming weight k.

(2) First choose a uniformly random “path π from (0, 0, . . . , 0) up
to (1, 1, . . . , 1)”; i.e., let π be a uniformly random permutation
from Sn and let π≤i ∈ n
2 denote the string whose jth coordi-
nate is 1 if and only if π( j) ≤ i. Then choose k ∼ {0, 1, 2, . . . , n}
uniformly and let x be the “kth string on the path”, namely π≤k.

(3) First choose p ∼ [0, 1]. Then choose x ∼ π⊗n
p .

Show that these are in fact the same distribution. (Hint: Imagine
choosing n + 1 indistinguishable points uniformly from [0, 1] and then
randomly assigning them the labels “p”, 1, 2, . . . , n.)

Copyright © Ryan O’Donnell, 2014, 2015, 2016, 2017, 2018, 2019, 2020, 2021.



<!-- pdf-page: 240 -->
240

8. Generalized domains

(b) We denote by νn the distribution on [n]
2

from part (a); more generally,
N
we use the notation νN for the distribution on
2 where N is an
abstract set of cardinality n. Given a nonempty J ⊆ [n], show that if
x ∼ νn and xJ ∈ J
2 denotes the restriction of x to coordinates J, then
xJ has the distribution νJ.

(c) Let f :
be

n
2 → and x i ∈ [n]. The ith Shapley value of f is dened to

Shapi[ f ] = E
x∼νn
n

[ f (x(i7→1)) − f (x(i7→0))].

Show that

(d) Suppose f :

i=1 Shapi[ f ] = f (1, 1, . . . , 1) − f (0, 0, . . . , 0).
n
2 → {0, 1} is monotone. Show Shapi[ f ] = 4

1
0 Infi[ f (p)] d p.
8.32 Explain how to generalize the denitions and results in Sections 8.1, 8.2
to the case of the complex inner product space L2(Ωn, π⊗n). In particular,
verify the following formulas from Proposition 8.16:

E[ f ] = f (0)

E[| f |2] = E[〈 f , f 〉] =

∑

α∈ n

<m

〈 f (α), f (α)〉 =

∑

α∈ n

<m

| f (α)|2

Var[ f ] = 〈 f − E[ f ], f − E[ f ]〉 =

〈 f , g〉 =

∑

α∈ n

<m

〈 f (α), g(α)〉 =

∑

α6=0
∑

| f (α)|2

f (α) g(α)

α∈ n
∑

<m

Cov[ f , g] = 〈 f − E[ f ], g − E[g]〉 =

f (α) g(α).

α6=0

8.33 (a) As in Exercise 2.58, explain how to generalize the denitions and
results in Sections 8.1, 8.2 to the case of functions f : Ωn → V , where
V is a real inner product space with inner product 〈·, ·〉V . Here the
Fourier coefcients f (α) will be elements of V , and 〈 f , g〉 is dened
to be Ex∼π⊗n [〈 f (x), g(x)〉V ]. In particular, verify the formulas from
Proposition 8.16, including Placherel: 〈 f , g〉 =

α〈 f (α), g(α)〉V .



(b) For Σ a nite set we write 4Σ for the set of all probability distributions
over Σ (cf. Exercise 7.22). Writing |Σ| = m, we also identify 4Σ with
the standard convex simplex in m, namely {µ ∈ m : µ1 + · · · + µm =
1, µi ≥ 0 ∀i} (where we assume some xed ordering of Σ). Finally,
we identify the m elements of Σ with the constant distributions in
4Σ; equivalently, the vertices of the form (0, . . . , 0, 1, 0, . . . , 0). Given a
function f : Ωn → Σ, often the most useful way to treat it analytically
is to interpret it as a function f : Ωn → 4Σ ⊂ m and then use the
setting described in part (a), with V = m. Using this idea, show that
if f : Ωn → Σ and π is a distribution on Ω, then

Stabρ[ f ] =

Pr
x∼π⊗n,y∼Nρ(x)

[ f (x) = f (y)].

Copyright © Ryan O’Donnell, 2014, 2015, 2016, 2017, 2018, 2019, 2020, 2021.



<!-- pdf-page: 241 -->
8.7. Exercises and notes

241

(Here in Stabρ[ f ] we are interpreting f ’s range as 4Σ ⊂ m, whereas
in the expression f (x) = f (y) we are treating f ’s range as the abstract
set Σ.)

8.34 We say a function f ∈ L2(Ωn, π⊗n) is a linear threshold function if it is
expressible as f (x) = sgn(`(x)), where ` : Ωn → has degree at most 1 (in
the sense of Denition 8.32).
(a) Given ω(+1), ω(−1) ∈ Ωn and x ∈ {−1, 1}n, we introduce the notation ω(x)
for the string (ω(x1)
n ) ∈ Ωn. Show that if ω(+1), ω(−1) ∼ π⊗n are
drawn independently and (x, y) ∼ {−1, 1}n × {−1, 1}n is a ρ-correlated
pair of binary strings, then (ω(x), ω(y)) is a ρ-correlated pair under
π⊗n.

, . . . , ω(xn)

1

(b) Let f ∈ L2(Ωn, π⊗n) be a linear threshold function. Given a pair
ω(+1), ω(−1) ∈ Ωn, dene gω(+1),ω(−1) : {−1, 1}n → {−1, 1} by gω(+1),ω(−1)(x) =
f (ω(x)). Show that gω(+1),ω(−1) is a linear threshold function in the
“usual” sense.

(c) Prove that Peres’s Theorem (from Chapter 5.5) applies to linear thresh-

old functions in L2(Ωn, π⊗n), with the same bounds.

8.35 Let G be a nite abelian group. We know by the Fundamental Theorem
where each

of Finitely Generated Abelian Groups that G ∼= m1
m j is a prime power.
(a) Given α ∈ G, dene χα : G → by

× · · · mn

χα(x) =

n∏

j=1

exp(2πiα j x j/m j).

Show χα is a character of G and that the χα’s are distinct functions
for distinct α’s. Deduce that the set of all χα’s forms a Fourier basis
for L2(G).

(b) Show that this set of characters forms a group under multiplication
and that this group is isomorphic to G; i.e., generalize Fact 8.58. This
is called the dual group of G and it is written G. We also identify the
characters in G with their indices α.

8.36 Verify that the convolution operation on L2(G) is associative and commu-
tative, and that it satises Åf ∗ g(α) = f (α) g(α) for all α ∈ G. (See Exer-
cise 8.35 for the denition of G.)

8.37 (a) Let f ∈ L2(Ωn, π⊗n) be any transitive-symmetric function and let T
be a randomized decision tree computing f . Show that there exists
a randomized decision tree T ′ computing f with ∆(π)(T ′) = ∆(π)(T )
and such that δ(π)
(T ′) is the same for all i ∈ [n]. (Hint: Randomize
over the automorphism group Aut( f ) and use Exercise 2.47.)
(b) Given a randomized decision tree T , let δ(π)(T ) = maxi∈[n]{δ(π)
i

(T )}.
Given f ∈ L2({−1, 1}n, π⊗n), dene δ(π)( f ) to be the minimum value of

i

Copyright © Ryan O’Donnell, 2014, 2015, 2016, 2017, 2018, 2019, 2020, 2021.



<!-- pdf-page: 242 -->
242

8. Generalized domains

δ(π)(T ) over all T which compute f ; this is called the revealment of f .
Show that if f is transitive-symmetric, then δ(π)( f ) = 1

n ∆(π)( f ).

8.38 (a) Show that DT(Maj⊗d

3 ) = 3d, RDT(Maj⊗d

3 ) ≤ (8/3)d, and ∆(Maj⊗d

3 ) ≤

(5/2)d.

(b) Show that RDT(Maj⊗2

3 ) < (8/3)2. How small can you make your upper

bound?

8.39 (a) Show that for every deterministic decision tree T computing the logi-

cal OR function on n bits,

∆(p)(T) = p · 1 + (1 − p)p · 2 + (1 − p)2 p · 3 + · · ·

· · · + (1 − p)n−2 p · (n − 1) + (1 − p)n−1 · n =

1 − (1 − p)n
p

.

Deduce ∆(p)(ORn) = 1−(1−p)n

p

.

(b) Show that ∆(p c)(ORn) ∼ n/(2 ln 2) as n → ∞, where pc denotes the

critical probability for ORn.

8.40 Let NAND : {True,False}2 → {True,False} be the function that outputs True

unless both its inputs are True.
(a) Show that for d even, NAND⊗d = Tribes⊗d/2
2,2 .

(Thus the recursive

NAND function is sometimes known as the AND-OR tree.)

(b) Show that DT(NAND⊗d) = 2d.
(c) Show that RDT(NAND) = 2.
(d) For b ∈ {True,False} and T a randomized decision tree computing
a function f , let RDTb(T ) denote the maximum cost of T among
inputs x with f (x) = b. Show that there is a randomized decision
tree T computing NAND with RDTFalse(T ) = 3/2.

(e) Show that RDT(NAND⊗2) ≤ 3.
(f ) Show that there is a family of randomized decision trees (Td)d∈ +,

with Td computing NAND⊗d, satisfying the inequalities

RDTFalse(Td) ≤ 2RDTTrue(Td−1)
RDTTrue(Td) ≤ RDTFalse(Td−1) + (1/2)RDTTrue(Td−1).

(g) Deduce RDT(NAND⊗d) ≤ ( 1+

)d ≈ n.754, where n = 2d.

4
8.41 Let C = {monotone f : {−1, 1}n → {−1, 1} | DT( f ) ≤ k}. Show that C is learn-
k/≤). (Hint: OS In-

able from random examples with error ≤ in time nO(
equality and Corollary 3.32.)

p

p

33

8.42 Verify that the decision tree process described in Denition 8.70 indeed
generates strings distributed according to π⊗n. (Hint: Induction on the
structure of the tree.)

Copyright © Ryan O’Donnell, 2014, 2015, 2016, 2017, 2018, 2019, 2020, 2021.



<!-- pdf-page: 243 -->
8.7. Exercises and notes

243

8.43 Let T be a deterministic decision tree of size s. Show that ∆(T) ≤ log s.
(Hint: Let P be a random root-to-leaf path chosen as in the decision tree
process. How can you bound the entropy of the random variable P?)

8.44 Let f ∈ L2(Ωn, π⊗n) be a nonconstant function with range {−1, 1}.

(a) Show that MaxInf[ f ] ≥ Var[ f ]/∆(π)( f ) (cf. the KKL Theorem from

Chapter 4.2).

(b) In case Ω = {−1, 1} show that MaxInf[ f ] ≥ Var[ f ]/ deg( f )3. (You should
use the result of Midrij ¯anis mentioned in the notes in Chapter 3.6.)
(c) Show that I[ f ] ≥ Var[ f ]/δ(π)( f ), where δ(π)( f ) is the revealment of f ,

dened in Exercise 8.37(b).

8.45 Let f ∈ L2(Ωn, π⊗n) have range {−1, 1}.

(a) Let T be a randomized decision computing f and let i ∈ [n]. Show

that Infi[ f ] ≤ δ(π)
i

(T ). (Hint: The decision tree process.)
(b) Suppose f is transitive-symmetric. Show that ∆(π)( f ) ≥

Var[ f ] · n.
log n)
(Hint: Exercise 8.37(b).) This result can be sharp up to an O(
factor even for an f : {−1, 1}n → {−1, 1} with Var[ f ] = 1; see [BSW05].





8.46 In this exercise you will give an alternate proof of the OSSS Inequality
that is sharp when Var[ f ] = 1 and is weaker by only a factor of 2 when
Var[ f ] is small. Let f ∈ L2(Ωn, π⊗n) have range {−1, 1}. Given a random-
ized decision tree T we write err(T ) = Prx∼π⊗n [T (x) 6= f (x)].
(a) Let T be a depth-k deterministic decision tree (not necessarily com-
puting f ) whose root queries coordinate i. Let T be the distribution
over deterministic trees of depth at most k − 1 given by following
a random outgoing edge from T’s root (according to π). Show that
err(T ) ≤ err(T) + 1

2 Infi[ f ].

(b) Let T be a randomized decision tree of depth 0. Show that err(T ) ≥

min{Pr[ f (x) = 1], Pr[ f (x) = −1]}.

n

(c) Prove by induction on depth that if T is any randomized decision tree,
then 1
(T )·Infi[ f ] ≥ min{Pr[ f (x) = 1], Pr[ f (x) = −1]}−err(T ).
2
Verify that this yields the OSSS Inequality when Var[ f ] = 1 and in
general yields the OSSS Inequality up to a factor of 2.

i=1 δ(π)

i

8.47 Show that the OSSS Inequality fails for functions f : {−1, 1}n → . (Hint:
The simplest counterexample uses a decision tree with the shape in Fig-
ure 8.2.)

Copyright © Ryan O’Donnell, 2014, 2015, 2016, 2017, 2018, 2019, 2020, 2021.



<!-- pdf-page: 244 -->
244

8. Generalized domains

Figure 8.2. The basis for a counterexample to the OSSS Inequality when
f : {−1, 1}n →

Can you make the ratio of the left-hand side to the right-hand side

equal to 130+20
157

3

? Larger?

p

, . . . , X i k

), where g :

2, ‖ f =S‖2

Notes. The origins of the orthogonal decomposition described in Section 8.3
date back to the work of Hoeffding [Hoe48] (see also von Mises [vM47]). Ho-
effding’s work introduced U-statistics, i.e., functions f of independent random
k →
variables X 1, . . . , X n of the form avg1≤i1<···<i k≤n g(X i1
is a symmetric function. Such functions are themselves symmetric. For
these functions, Hoeffding introduced f ⊆S (which, by symmetry, depends only
on |S|) and proved certain inequalities (e.g., those in Exercise 8.22) relating
Var[ f ] to the quantities ‖ f ⊆S‖2
2. Nonsymmetric functions f were
considered only rarely in the subsequent three decades of statistics research.
One notable exception comes in the work of Hájek [Háj68], who effectively
introduced f ≤1, known as the Hájek projection of f . Also, a work of Bour-
k f =k. The rst
gain [Bou79] essentially describes the decomposition f =
work that mentions the general orthogonal decomposition for not-necessarily-
symmetric functions appears to be that of Efron and Stein [ES81] from the
late 1970s. Efron and Stein’s description is brief; the subsequent work of
Karlin and Rinott [KR82] gives a more thorough development. Efron and
Stein’s main result was a proof of the statement Var[ f ] ≤ I[ f ] for symmet-
ric f ; in the statistics literature this is known as the Efron–Stein Inequality.
Steele [Ste86a] extended this to the case of nonsymmetric f by a simple proof
that used the Fourier basis approach to orthogonal decomposition. This ap-
proach via Fourier bases originated in the work of Rubin and Vitale [RV80];
see also Takemura [Tak83] and Vitale [Vit84]. The terminology “Fourier
basis” we use is not standard.



The p-biased hypercube distribution is strongly motivated by the Erd˝os–
Rényi [ER59] theory of random graphs (see e.g., Bollobás and Riordan [BR08]
for history) and by percolation theory (introduced in Broadbent and Hammer-
sley [BH57]). Inuences under the p-biased distribution – and their connec-
tion to threshold phenomena – were studied by Russo [Rus81, Rus82]. The
former work proved the Margulis–Russo formula independently of Margulis,

Copyright © Ryan O’Donnell, 2014, 2015, 2016, 2017, 2018, 2019, 2020, 2021.



<!-- pdf-page: 245 -->
8.7. Exercises and notes

245

who had proven it earlier [Mar74]. Fourier analysis under the p-biased distri-
bution seems to have been rst introduced to the theoretical computer science
literature by Furst, Jackson, and Smith [FJS91], who extended the LMN
learning algorithm for AC0 to this setting. Talagrand [Tal93, Tal94] devel-
oped p-biased Fourier for the study of threshold phenomena, strengthening
Margulis and Russo’s work and proving the KKL Theorem in the p-biased
setting. Similar results were obtained by Friedgut and Kalai [FK96] using
an earlier work of Bourgain, Kahn, Kalai, Linial, and Katznelson [BKK+92]
that proved a version of the KKL Theorem in the setting of general product
spaces. The statements about sharp thresholds for cliques and connectivity
in Example 8.49 are essentially due to Matula and to Erd˝os–Rényi, respec-
tively; see, e.g., Bollobás [Bol01]. Weak threshold results similar to the ones
in Exercise 8.29 were proved by Bollobás and Thomason [BT87], using the
Kruskal–Katona Theorem rather than the Poincaré Inequality.

Fourier analysis on nite abelian groups – and more generally, on locally
compact abelian groups – is an enormous subject upon which we have touched
only briey. We cannot survey it here but refer instead to the standard text-
book of Rudin [Rud62] and to the reader-friendly textbook of Terras [Ter99],
which focuses on nite groups.

One of the earliest works on randomized decision tree complexity is that
of Saks and Wigderson [SW86]; they proved the contents of Exercise 8.40.
(We note that RDT( f ) is usually denoted R( f ) in the literature, and DT( f ) is
usually denoted D( f ).) One basic lower bound in the area is that RDT( f ) ≥

DT( f ) for any f : {−1, 1}n → {−1, 1}; in fact, this lower bound holds even
for “nondeterministic decision tree complexity”, as proved in [BI87, Tar89].
Yao’s Conjecture is also sometimes attributed to Richard Karp. Regarding
the recursive majority-of-3 function, Ravi Boppana was the rst to point out
that RDT(Maj⊗d
3 ) = 3d. Saks and Wigderson
noted the bound RDT(Maj⊗d
3 ) ≤ (8/3)d and also that it is not optimal. Fol-
lowing subsequent works [JKS03, She08] the best known upper bound is
O(2.65d) [MNSX11] and the best known lower bound is Ω(2.55d) [Leo12].

3 ) = o(3d) even though DT(Maj⊗d

The proof of the OSSS Inequality we presented is essentially Lee’s [Lee10];
the alternate proof from Exercise 8.46 is due to Jain and Zhang [JZ11].
The Condorcet Jury Theorem (see Exercise 8.23) is from [dC85]. The Shap-
ley value described in Exercise 8.31 was introduced by the Nobelist Shap-
ley [Sha53]; for more, see Roth [Rot88]. Exercise 8.34 is from Blais, O’Donnell,
and Wimmer [BOW10]. Exercises 8.37(a) and 8.45 are from the work of
Benjamini, Schramm, and Wilson [BSW05]; the term “revealment” was intro-
duced by Schramm and Steif [SS10]. Exercise 8.47 is from [OSSS05]. Related
to this, it is extremely interesting to ask whether something like the result of

Copyright © Ryan O’Donnell, 2014, 2015, 2016, 2017, 2018, 2019, 2020, 2021.



<!-- pdf-page: 246 -->
246

8. Generalized domains

Exercise 8.44(b) holds for functions f : {−1, 1}n → [−1, 1]. It has been suggested
that the answer is yes:

Aaronson–Ambainis Conjecture. [Aar08, AA11] Let f : {−1, 1}n → [−1, 1].
Then MaxInf[ f ] ≥ poly(Var[ f ]/ deg( f )).

If true, this conjecture would have signicant consequences for the limitations
of efcient quantum computation; see Aaronson and Ambainis [AA11]. The
best result in the direction of the conjecture, due to Dinur et al. [DFKO07], is
the lower bound MaxInf[ f ] ≥ poly(Var[ f ]/2deg( f )).

Copyright © Ryan O’Donnell, 2014, 2015, 2016, 2017, 2018, 2019, 2020, 2021.



<!-- pdf-page: 247 -->
Chapter 9

Basics of
hypercontractivity

In 1970, Bonami proved the following central result:

The Hypercontractivity Theorem. Let f : {−1, 1}n → and let 1 ≤ p ≤ q ≤ ∞.

Then ‖Tρ f ‖q ≤ ‖ f ‖p for 0 ≤ ρ ≤



p−1
q−1 .

As stated, this theorem may look somewhat opaque. In this chapter we
consider some special cases of it that are easier to understand, easier to prove,
and that encompass almost all of the theorem’s uses. The proof of the full
theorem is deferred to Chapter 10. The special cases in this chapter are the
following:

Bonami Lemma. Let f : {−1, 1}n → have degree k. Then ‖ f ‖4 ≤

p

k

3

‖ f ‖2.

The fundamental idea of this statement is that if x ∼ {−1, 1}n and f : {−1, 1}n →
has low degree then the random variable f (x) is quite “reasonable”; e.g.,
it is “nicely” distributed around its mean. The Bonami Lemma has a very
easy inductive proof and is already powerful enough to obtain many of the
well-known applications of “hypercontractivity”, including the KKL Theorem
(proven at the end of this chapter) and the Invariance Principle.

(2, q)-Hypercontractivity Theorem. Let f : {−1, 1}n → and let 2 ≤ q ≤ ∞.
Then ‖T
f ‖q ≤ ‖ f ‖2. As a consequence, if f has degree at most k then
1/


p

q−1
k

‖ f ‖q ≤

q − 1

‖ f ‖2.

This theorem quanties the extent to which Tρ is a “smoothing” operator;
equivalently, it gives even more control over the “reasonableness” of low-
degree polynomials. Its consequences include a generalization of the Level-1

Copyright © Ryan O’Donnell, 2014, 2015, 2016, 2017, 2018, 2019, 2020, 2021.

247



<!-- pdf-page: 248 -->
248

9. Basics of hypercontractivity

Inequality (from Chapter 5.4) to “Level-k Inequalities”, as well as a Chernoff-
like tail bound for low-degree polynomials of random bits.

(p, 2)-Hypercontractivity Theorem. Let f : {−1, 1}n → and let 1 ≤ p ≤ 2.
Then ‖Tp

f ‖2 ≤ ‖ f ‖p. Equivalently, Stabρ[ f ] ≤ ‖ f ‖2

1+ρ for 0 ≤ ρ ≤ 1.

p−1

This theorem is actually “equivalent” to the (2, q)-Hypercontractivity Theorem
by virtue of Hölder’s inequality. When specialized to the case of f : {−1, 1}n →
{0, 1} it gives a precise quantication of the fact that the “noisy hypercube
graph” is a “small-set expander”. Qualitatively, this means that if A ⊆ {−1, 1}n
is “small”, x ∼ A, and y ∼ Nρ(x), then y is very unlikely to be in A.

9.1. Low-degree polynomials are reasonable

As anyone who has worked in probability knows, a random variable can some-
times behave in rather “unreasonable” ways. It may be never close to its
expectation. It might exceed its expectation almost always, or almost never.
It might have nite 1st, 2nd, and 3rd moments, but an innite 4th moment.
All of this poor behavior can cause a lot of trouble – wouldn’t it be nice to have
a class of “reasonable” random variables?

A very simple condition on a random variable that guarantees some good
behavior is that its 4th moment is not too large compared to its 2nd moment.

Denition 9.1. For a real number B ≥ 1, we say that the real random variable
X is B-reasonable if E[X 4] ≤ B E[X 2]2. (Equivalently, if ‖X ‖4 ≤ B1/4‖X ‖2.)

The smaller B is, the more “reasonable” X is. This denition is scale-
invariant (i.e., cX is B-reasonable if and only if X is, for c 6= 0) but not
translation-invariant (c + X and X may not be equally reasonable). The latter
fact can sometimes be awkward, a point we’ll address further in Section 9.3.
Indeed, we’ll later encounter a few alternative conditions that also capture
“reasonableness”. For example, in Chapter 11 we’ll consider the analogous
3rd moment condition, E[|X |3] ≤ B E[X 2]3/2. Strictly speaking, the 4th mo-
ment condition is stronger: if X is B-reasonable, then
p





E[|X |3] = E[|X | · X 2] ≤

E[X 2]

E[X 4] ≤

B E[X 2]3/2;

on the other hand, there exist random variables with nite 3rd moment and
innite 4th moment. However, such unusual random variables almost never
arise for us, and morally speaking the 4th and 3rd moment conditions are
about equally good proxies for reasonableness.

Example 9.2. If x ∼ {−1, 1} is uniformly random then x is 1-reasonable. If
g ∼ N(0, 1) is a standard Gaussian, then E[g4] = 3, so g is 3-reasonable. If
u ∼ [−1, 1] is uniform, then you can calculate that it is 9
5 -reasonable. In all

Copyright © Ryan O’Donnell, 2014, 2015, 2016, 2017, 2018, 2019, 2020, 2021.



<!-- pdf-page: 249 -->
9.1. Low-degree polynomials are reasonable

249

of these examples B is a “small” constant, and we think of these random
variables simply as “reasonable”. An example of an “unreasonable” random
variable would be highly biased Bernoulli random variable; say, Pr[y = 1] =
2−n, Pr[y = 0] = 1 − 2−n, where n is large. This y is not B-reasonable unless
B ≥ 2n.

Let’s give a few illustrations of why reasonable random variables are nice
to work with. First, they have slightly better tail bounds than what you would
get out of the Chebyshev inequality:

Proposition 9.3. Let X 6≡ 0 be B-reasonable. Then Pr[|X | ≥ t‖X ‖2] ≤ B/t4 for
all t > 0.

Proof. This is immediate from Markov’s inequality:

Pr[|X | ≥ t‖X ‖2] = Pr[X 4 ≥ t4‖X ‖4

2] ≤

E[X 4]
t4 E[X 2]2

≤

B
t4

.



More interestingly, they also satisfy anticoncentration bounds; e.g., you

can upper-bound the probability that they are near 0.

Proposition 9.4. Let X 6≡ 0 be B-reasonable. Then Pr[|X | > t‖X ‖2] ≥ (1 −
t2)2/B for all t ∈ [0, 1].

Proof. Applying the Paley–Zygmund inequality (also called the “second mo-
ment method”) to X 2, we get

Pr[|X | ≥ t‖X ‖2] = Pr[X 2 ≥ t2 E[X 2]] ≥ (1 − t2)2 E[X 2]2
E[X 4]

≥

(1 − t2)2
B

.



For a generalization of this proposition, see Exercise 9.12.

For a discrete random variable X , a simple condition that guarantees
reasonableness is that X takes on each of its values with nonnegligible prob-
ability:

Proposition 9.5. Let X be a discrete random variable with probability mass
function π. Write

λ = min(π) = min

x∈range(X )

{Pr[X = x]}.

Then X is (1/λ)-reasonable.

Proof. Let M = ‖X ‖∞. Since Pr[|X | = M] ≥ λ we get

E[X 2] ≥ λM2 =⇒ M2 ≤ E[X 2]/λ.

On the other hand,

E[X 4] = E[X 2 · X 2] ≤ M2 · E[X 2],

and thus E[X 4] ≤ (1/λ) E[X 2]2 as required.



Copyright © Ryan O’Donnell, 2014, 2015, 2016, 2017, 2018, 2019, 2020, 2021.



<!-- pdf-page: 250 -->
250

9. Basics of hypercontractivity

x1 + · · · + 1p
n

The converse to Proposition 9.5 is certainly not true. For example, if
X = 1p
xn where x ∼ {−1, 1}n, then X is very close to a standard
n
Gaussian random variable (for n large) and is, unsurprisingly, 3-reasonable.
On the other hand, the “λ” for this X is tiny, 2−n.

This discussion raises the issue of how you might try to construct an
unreasonable random variable out of independent uniform ±1 bits. By Propo-
sition 9.5, at the very least you must use a lot of them. Furthermore, it also
seems that they must be combined in a high-degree way. For example, to
construct the unreasonable random variable y from Example 9.2 requires
degree n: y = (1 + x1)(1 + x2) · · · (1 + xn)/2n.

Indeed, the idea that high degree is required for unreasonableness is

correct, as the following crucial result shows:

The Bonami Lemma. For each k, if f : {−1, 1}n → has degree at most k
and x1, . . . , xn are independent, uniformly random ±1 bits, then the random
variable f (x) is 9k-reasonable, i.e.,

E[ f 4] ≤ 9k E[ f 2]2 ⇐⇒ ‖ f ‖4 ≤

p

k

3

‖ f ‖2.

In other words, low-degree polynomials of independent uniform ±1 bits are
reasonable. As we will explain later, the Bonami Lemma is a special case of
more general results in the theory of “hypercontractivity”. However, many key
theorems using hypercontractivity – e.g., the KKL Theorem, the Invariance
Principle – really need only the simple Bonami Lemma. (We should also note
that the name “Bonami Lemma” is not standard; however, the result was rst
proved by Bonami and it’s often used as a lemma, so the name ts. See the
discussion in the notes in Section 9.7.)

One pleasant thing about the Bonami Lemma is that once you decide
to prove it by induction on n, the proof practically writes itself. The only
“non-automatic” step is an application of Cauchy–Schwarz.

Proof of the Bonami Lemma. We assume k ≥ 1 as otherwise f must be
constant and the claim is trivial. The proof is by induction on n. Again,
if n = 0, then f must be constant and the claim is trivial. For n ≥ 1 we
can use the decomposition f (x) = xnDn f (x) + En f (x) (Proposition 2.24), where
deg(Dn f ) ≤ k − 1, deg(En f ) ≤ k, and the polynomials Dn f (x) and En f (x) don’t
depend on xn. For brevity we write f = f (x), d = Dn f (x), and e = En f (x). Now
E[ f 4] = E[(xnd + e)4]
= E[x4

nd2 e2] + 4 E[xnde3] + E[e4]

nd3 e] + 6 E[x2

nd4] + 4 E[x3
n] E[d4] + 4 E[x3

= E[x4

n] E[d3 e] + 6 E[x2

n] E[d2 e2] + 4 E[xn] E[de3] + E[e4].

In the last step we used the fact that xn is independent of d and e, since Dn f
and En f do not depend on xn. We now use E[xn] = E[x3
n] =

n] = 0 and E[x2

Copyright © Ryan O’Donnell, 2014, 2015, 2016, 2017, 2018, 2019, 2020, 2021.



<!-- pdf-page: 251 -->
9.1. Low-degree polynomials are reasonable

E[x4

n] = 1 to deduce

E[ f 4] = E[d4] + 6 E[d2 e2] + E[e4].

A similar (and simpler) sequence of steps shows that

E[ f 2] = E[d2] + E[e2].

251

(9.1)

(9.2)

To upper-bound (9.1), recall that d = Dn f (x) where Dn f is a multilinear
polynomial of degree at most k − 1 depending on n − 1 variables. Thus we
can apply the induction hypothesis to deduce E[d4] ≤ 9k−1 E[d2]2. Similarly,
E[e4] ≤ 9k E[e2]2 since deg(En f ) ≤ k. To bound E[d2 e2] we apply Cauchy–
E[e4] and letting us use induction again. Thus we
Schwarz, getting
have

E[d4]





E[ f 4] ≤ 9k−1 E[d2]2 + 6






9k−1 E[d2]2

≤ 9k

E[d2]2 + 2 E[d2] E[e2] + E[e2]2

= 9k

E[d2] + E[e2]

9k E[e2]2 + 9k E[e2]2




2

,

where we used 9k−1 E[d2]2 ≤ 9k E[d2]2. In light of (9.2), this completes the

proof.

Some aspects of the sharpness of the Bonami Lemma are explored in
Exercises 9.2, 9.3, 9.37, and 9.38. Here we make one more observation. At
the end of the proof we used the wasteful-looking inequality 9k−1 E[d2]2 ≤
9k E[d2]2. Tracing back through the proof, it’s easy to see that it would still
be valid even if we just had E[x4
] = 1. For example,
i
the Bonami Lemma holds not just if the xi’s are random bits, but if they are
standard Gaussians, or are uniform on [−1, 1], or there are some of each. We
leave the following as Exercise 9.4.

] ≤ 9 rather than E[x4
i

Corollary 9.6. Let x1, . . . , xn be independent, not necessarily identically dis-
tributed, random variables satisfying E[xi] = E[x3
] = 0. (This holds if, e.g.,
i
each −xi has the same distribution as xi.) Assume also that each xi is B-
reasonable. Let f = F(x1, . . . , xn), where F is a multilinear polynomial of degree
at most k. Then f is max(B, 9)k-reasonable.

As a rst application of the Bonami Lemma, let us combine it with Propo-
sition 9.4 to show that a low-degree function is not too concentrated around
its mean:

Theorem 9.7. Let f : {−1, 1}n → be a nonconstant function of degree at
Var[ f ]. Then
most k; write µ = E[ f ] and σ =



Pr
x∼{−1,1}

[| f (x) − µ| > 1

2 σ] ≥ 1

16 91−k.

Copyright © Ryan O’Donnell, 2014, 2015, 2016, 2017, 2018, 2019, 2020, 2021.



<!-- pdf-page: 252 -->
252

9. Basics of hypercontractivity

Proof. Let g = 1
( f − µ), a function of degree at most k satisfying ‖g‖2 = 1. By
σ
the Bonami Lemma, g is 9k-reasonable. The result now follows by applying
Proposition 9.4 to g with t = 1

2 .

Using this theorem, we can give a short proof of the FKN Theorem from
Chapter 2.5: If f : {−1, 1}n → {−1, 1} has W1[ f ] = 1 − δ then f is O(δ)-close to
±χi for some i ∈ [n].

Proof of the FKN Theorem. Write ` = f =1, so E[`2] = 1 − δ by assumption.
We may assume without loss of generality that δ ≤ 1
1600 . The goal of the proof
is to show that Var[`2] is small; specically we’ll show that Var[`2] ≤ 6400δ.
This will complete the proof because (using Exercise 1.20 for the rst equality
below)

1

2 Var[`2] =

∑

i6= j

f (i)2 f ( j)2 =

2

f (i)2

 n

i=1

−

n

i=1

f (i)4

= (1 − δ)2 −

n

i=1

f (i)4 ≥ (1 − 2δ) −

n

i=1

f (i)4

and hence Var[`2] ≤ 6400δ implies

1 − 3202δ ≤

n

i=1

f (i)4 ≤ max

i

{ f (i)2}

n

i=1

f (i)2 ≤ max

i

{ f (i)2} ≤ max

i

{| f (i)|},

as required.

To bound Var[`2] we rst apply Theorem 9.7 to the degree-2 function `2;

this yields

∣
∣`2 − (1 − δ)

Pr



∣
∣ ≥ 1
2



Var[`2]

≥ 1

16 91−2 = 1

144 .

Now suppose by way of contradiction that Var[`2] > 6400δ; then the above
implies

∣
∣`2 − (1 − δ)

∣
∣ > 40

p



δ

≤ Pr

∣
∣`2 − 1

∣
∣ > 39

p



δ

.

(9.3)

1
144 ≤ Pr

This says that |`| is frequently far from 1. Since | f | = 1 always, we can deduce
that | f − `|2 is frequently large. More precisely, a short calculation (Exer-
cise 9.5) shows that ( f −`)2 ≥ 169δ whenever |`2 −1| > 39
δ. But now (9.3) im-
plies E[( f −`)2] ≥ 1
144 ·169δ > δ, a contradiction since E[( f −`)2] = 1−W1[ f ] = δ

by assumption.

p

9.2. Small subsets of the hypercube are noise-sensitive

An immediate consequence of the Bonami Lemma is that for any f : {−1, 1}n →

and k ∈ ,

p

‖T1/

3 f =k‖4 = 1

p

3

k ‖ f =k‖4 ≤ ‖ f =k‖2.

(9.4)

Copyright © Ryan O’Donnell, 2014, 2015, 2016, 2017, 2018, 2019, 2020, 2021.



<!-- pdf-page: 253 -->
9.2. Small subsets of the hypercube are noise-sensitive

253

This is a special case of the (2, 4)-Hypercontractivity Theorem (whose name
will be explained shortly), which says that the assumption of degree-k homo-
geneity is not necessary:

(2, 4)-Hypercontractivity Theorem. Let f : {−1, 1}n → . Then

p

‖T1/

3 f ‖4 ≤ ‖ f ‖2.

It almost looks as though you could prove this theorem simply by sum-
ming (9.4) over k. In fact that proof strategy can be made to work given a
few extra tricks (see Exercise 9.6), but it’s just as easy to repeat the induction
technique used for the Bonami Lemma.

3 f (x)4] ≤ E[ f (x)2]2 using the same induction as in
Proof. We’ll prove E[T1/
the Bonami Lemma. Retaining the notation d and e, and using the shorthand
T = T1/

3, we have

p

p

T f = xn · 1p
3
Similar computations to those in the Bonami Lemma proof yield
4 E[(Td)4] + 6

2 E[(Td)2(Te)2] + E[(Te)4]

E[(T f )4] =

Td + Te.





1p
3

1p
3

≤ E[(Td)4] + 2 E[(Td)2(Te)2] + E[(Te)4]

≤ E[(Td)4] + 2





E[(Td)4]

E[(Te)4] + E[(Te)4]

≤ E[d2]2 + 2 E[d2] E[e2] + E[e2]2



2 = E[ f 2]2,
where the second inequality is Cauchy–Schwarz, the third is induction, and

the nal equality is a simple computation analogous to (9.2).

E[d2] + E[e2]

=

p

3 a “contraction” on L2({−1, 1}n) – meaning ‖T1/

The name “hypercontractivity” in this theorem describes the fact that not
only is T1/
3 f ‖2 ≤ ‖ f ‖2 for
all f (Exercise 2.33) – it’s even a contraction when viewed as an operator from
L2({−1, 1}n) to L4({−1, 1}n). You should think of hypercontractivity theorems
as quantifying the extent to which Tρ is a “smoothing”, or “reasonable-izing”
operator.

p

Unfortunately the quantity ‖T1/

3 f ‖4 in the (2, 4)-Hypercontractivity The-
orem does not have an obvious combinatorial meaning. On the other hand,
the quantity

p





p

‖T1/

3 f ‖2 =

p

〈T1/

3 f , T1/

p

3 f 〉 =

〈 f , T1/

p

p

3T1/

3 f 〉 =



Stab1/3[ f ],

does have a nice combinatorial meaning. And we can make this quantity
appear in the Hypercontractivity Theorem via a simple trick from analysis,
3 is a self-adjoint operator. We “ip the norms
just using the fact that T1/
across 2” using Hölder’s inequality:

p

Copyright © Ryan O’Donnell, 2014, 2015, 2016, 2017, 2018, 2019, 2020, 2021.



<!-- pdf-page: 254 -->
254

9. Basics of hypercontractivity

(4/3, 2)-Hypercontractivity Theorem. Let f : {−1, 1}n → . Then

(9.5)

(9.6)

i.e.,

Proof. Writing T = T1/
‖T f ‖2

p

‖T1/

3 f ‖2 ≤ ‖ f ‖4/3;

Stab1/3[ f ] ≤ ‖ f ‖2

4/3.

p

3 for brevity we have

2 = 〈T f , T f 〉 = 〈 f , TT f 〉 ≤ ‖ f ‖4/3‖TT f ‖4 ≤ ‖ f ‖4/3‖T f ‖2

by Hölder’s inequality and the (2, 4)-Hypercontractivity Theorem. Dividing
through by ‖T f ‖2 (which we may assume is nonzero) completes the proof. 

In the inequality (9.5) the left-hand side is a natural quantity. The right-
hand side is just 1 when f : {−1, 1}n → {−1, 1}, which is not very interesting.
But if we instead look at f : {−1, 1}n → {0, 1} we get something very interesting:

Corollary 9.8. Let A ⊆ {−1, 1}n have volume α; i.e., let 1A : {−1, 1}n → {0, 1}
satisfy E[1A] = α. Then

Stab1/3[1A] = Pr

x∼{−1,1}n
y∼N1/3(x)

[x ∈ A, y ∈ A] ≤ α3/2.

Equivalently (for α > 0),

[y ∈ A] ≤ α1/2.

Pr
x∼A
y∼N1/3(x)

Proof. This is immediate from inequality (9.5), since

‖1A‖2

4/3 =



E
x

[|1A(x)|4/3]3/4

2

[1A(x)]3/2 = α3/2.

= E
x



See Section 9.5 for the generalization of this corollary to noise rates other

than 1/3.

Example 9.9. Assume α = 2−k, k ∈ +, and A is a subcube of codimension k;
n
e.g., 1A :
2 → {0, 1} is the logical AND function on the rst k coordinates.
For every x ∈ A, when we form y ∼ N1/3(x) we’ll have y ∈ A if and only if the
rst k coordinates of x do not change, which happens with probability (2/3)k =
(2/3)log(1/α) = αlog(3/2) ≈ α.585 ≤ α1/2. In fact, the bound α1/2 in Corollary 9.8 is
essentially sharp when A is a Hamming ball; see Exercise 9.24.

We can phrase Corollary 9.8 in terms of the expansion in a certain graph:

Denition 9.10. For n ∈ + and ρ ∈ [−1, 1], the n-dimensional ρ-stable hy-
percube graph is the edge-weighted, complete directed graph on vertex set
{−1, 1}n in which the weight on directed edge (x, y) ∈ {−1, 1}n × {−1, 1}n is equal
to Pr[(x, y) = (x, y)] when (x, y) is a ρ-correlated pair. If ρ = 1 − 2δ for δ ∈ [0, 1],
we also call this the δ-noisy hypercube graph. Here the weight on (x, y) is

Copyright © Ryan O’Donnell, 2014, 2015, 2016, 2017, 2018, 2019, 2020, 2021.



<!-- pdf-page: 255 -->
9.2. Small subsets of the hypercube are noise-sensitive

255

Pr[(x, y) = (x, y)] where x ∼ {−1, 1}n is uniform and y is formed from x by
negating each coordinate independently with probability δ.

Remark 9.11. The edge weights in this graph are nonnegative and sum to 1.
The graph is also “regular” in the sense that for each x ∈ {−1, 1}n the sum of
all the edge weight leaving (or entering) x is 2−n. You can also consider the
graph to be undirected, since the weight on (x, y) is the same as the weight
on (y, x); in this viewpoint, the weight on the undirected edge (x, y) would be
21−nδ∆(x,y)(1 − δ)n−∆(x,y). In fact, the graph is perhaps best thought of as the
discrete-time Markov chain on state space {−1, 1}n in which a step from state
x ∈ {−1, 1}n consists of moving to state y ∼ Nρ(x). This is a reversible chain
with the uniform stationary distribution. Each discrete step is equivalent to
running the “usual” continuous-time Markov chain on the hypercube for time
t = ln(1/ρ) (assuming ρ ∈ [0, 1]).

With this denition in place, we can see Corollary 9.8 as saying that the
1/3-stable (equivalently, 1/3-noisy) hypercube graph is a “small-set expander”:
given any small α-fraction of the vertices A, almost all of the edge weight
touching A is on its boundary. More precisely, if we choose a random vertex
x ∈ A and take a random edge out of x (with probability proportional to its
edge weight), we end up outside A with probability at least 1 − α1/2. You
can compare this with the discussion surrounding the Level-1 Inequality in
Section 5.4, which is the analogous statement for the ρ-stable hypercube
graph “in the limit ρ → 0+”. The appropriate statement for general ρ is
appears in Section 9.5 as the “Small-Set Expansion Theorem”.

Corollary 9.8 would apply equally well if 1A were replaced by a function g :
{−1, 1}n → {−1, 0, 1}, with α denoting Pr[g 6= 0] = E[|g|] = E[g2]. This situation
occurs naturally when g = Di f for some Boolean-valued f : {−1, 1}n → {−1, 1}.
In this case Stab1/3[g] = Inf(1/3)
[ f ], the 1/3-stable inuence of i on f . We
conclude that for a Boolean-valued function, if the inuence of i is small then
its 1/3-stable inuence is much smaller:

i

Corollary 9.12. Let f : {−1, 1}n → {−1, 1}. Then Inf(1/3)

i

[ f ] ≤ Infi[ f ]3/2 for all i.

We remark that the famous KKL Theorem (stated in Chapter 4.2) more or
less follows by summing the above inequality over i ∈ [n]; if you’re impatient
to see its proof you can skip directly to Section 9.6 now.

Let’s take one more look at the “small-set expansion result”, Corollary 9.8.
Since noise stability roughly measures how “low” a function’s Fourier weight
is, this corollary implies that a function f : {−1, 1}n → {0, 1} with small mean α
cannot have much of its Fourier weight at low degree. More precisely, for any

Copyright © Ryan O’Donnell, 2014, 2015, 2016, 2017, 2018, 2019, 2020, 2021.



<!-- pdf-page: 256 -->
256

9. Basics of hypercontractivity

k ∈ we have

α3/2 ≥ Stab1/3[ f ] ≥ (1/3)kW≤k[ f ] =⇒ W≤k[ f ] ≤ 3kα3/2.
For k = 1 this gives W≤1[ f ] ≤ 3α3/2, which is nontrivial but not as strong
as the Level-1 Inequality from Section 5.4. But (9.7) also gives us “level-k
inequalities” for larger values of k. For example,

(9.7)

W≤.25 log(1/α)[ f ] ≤ α−.25 log 3+3/2 ≤ α1.1 ø α = ‖ f ‖2
2;

i.e., almost all of f ’s Fourier weight is above degree .25 log(1/α). We will give
slightly improved versions of these level-k inequalities in Section 9.5.

9.3. (2, q)- and (p, 2)-hypercontractivity for a single bit

Although you can get a lot of mileage out of studying the 4-norm of random
variables, it’s also natural to consider other norms. For example, we would
get improved versions of our concentration and anticoncentration results,
Propositions 9.3 and 9.4, if we could bound the higher norms of a random
variable in terms of its 2-norm. As we’ll see, we can also get stronger “level-k
inequalities” by bounding the (2+≤)-norm of a Boolean function for small ≤ > 0.

We started with the 4-norm due to the simplicity of the proofs of the
Bonami Lemma and the (2, 4)-Hypercontractivity Theorem. To generalize
these results to other norms it’s a bit more elegant to work with the latter.
Partly this is because it’s “formally stronger” (see Theorem 9.21). But the
main reason is that the hypercontractivity version alleviates the inelegant
issue that being “B-reasonable” is not translation-invariant. Thus instead of
generalizing the condition that ‖ρ X ‖4 ≤ ‖X ‖2 (“X is ρ−4-reasonable”) we’ll
generalize the condition that ‖a + ρbX ‖4 ≤ ‖a + bX ‖2 (cf. the n = 1 case of the
(2, 4)-Hypercontractivity Theorem).

Denition 9.13. Let 1 ≤ p ≤ q ≤ ∞ and let 0 ≤ ρ < 1. We say that a real
random variable X (with ‖X ‖q < ∞) is (p, q, ρ)-hypercontractive if

‖a + ρbX ‖q ≤ ‖a + bX ‖p

for all constants a, b ∈ .

Remark 9.14. By homogeneity, it sufces to check the condition for a = 1,
b ∈
or for a ∈ , b = 1 (cf. Exercise 9.9(a)). It’s also true (Exercise 9.11) that
if X is (p, q, ρ)-hypercontractive then it is (p, q, ρ′)-hypercontractive for ρ′ < ρ
as well.

In Exercise 9.10 you will show that if X is hypercontractive then E[X ]
must be 0. Thus hypercontractivity, like reasonableness, is not a translation-
invariant notion. Nevertheless, the fact that the denition involves transla-
tion by an arbitrary a greatly facilitates proofs by induction. For example, an
elegant property we gain from the denition is the following (Exercise 10.2):

Copyright © Ryan O’Donnell, 2014, 2015, 2016, 2017, 2018, 2019, 2020, 2021.



<!-- pdf-page: 257 -->
9.3. (2, q)- and (p, 2)-hypercontractivity for a single bit

257

Proposition 9.15. Let X and Y be independent (p, q, ρ)-hypercontractive ran-
dom variables. Then X + Y is also (p, q, ρ)-hypercontractive.

The n = 1 case of our (2, 4)-Hypercontractivity Theorem precisely says that
3)-hypercontractive;
a single uniformly random ±1 bit x is (2, 4, 1/
the (4/3, 2)-Hypercontractivity Theorem says that the bit x is also (4/3, 2, 1/
3)-
hypercontractive. We’ll spend the remainder of this section generalizing these
facts to (2, q, ρ)- and (p, 2, ρ)-hypercontractivity for other values of p and q.
We remark that in our study of hypercontractivity we’ll focus mainly on the
cases of p = 2 or q = 2. The study of hypercontractivity for p, q 6= 2 and for
random variables other than uniform ±1 bits is deferred to Chapter 10.

p

p

p

We now consider hypercontractivity of a uniformly random ±1 bit x. We
know that x is (2, q, 1/
3)-hypercontractive for q = 4; what about other values
of q? Things are most pleasant when q is an even integer because then you
don’t need to take the absolute value when computing ‖a + ρbX ‖q. So let’s try
q = 6.

Proposition 9.16. For x a uniform ±1 bit, we have ‖a + ρbx‖6 ≤ ‖a + bx‖2 for
5)-hypercontractive.
all a, b ∈

5. That is, x is (2, 6, 1/

if (and only if) ρ ≤ 1/

p

p

Proof. Raising the inequality to the 6th power, we need to show

E[(a + ρbx)6] ≤ E[(a + bx)2]3.

(9.8)

The result is trivial when a = 0; otherwise, we may assume a = 1 by homo-
geneity. We expand both quantities inside expectations and use the fact that
E[xk] is 0 when k is odd and 1 when k is even. Thus (9.8) is equivalent to

1 + 15ρ2b2 + 15ρ4b4 + ρ6b6 ≤ (1 + b2)3 = 1 + 3b2 + 3b4 + b6.

(9.9)

Comparing the two sides term-by-term we see that the coefcient on b2 is
the limiting factor: in order for (9.9) to hold for all b ∈
it is sufcient that
15ρ2 ≤ 3; i.e., ρ ≤ 1/
5. By considering b → 0 it’s also easy to see that this

condition is necessary.

p

If you repeat this analysis for the case of q = 8 you’ll nd that again the
limiting factor is the coefcient on b2, and that x is (2, 8, ρ)-hypercontractive
if (and only if)
7. In light of this it is natural to guess
that the following is true:

; i.e., ρ ≤ 1/

ρ2 ≤

8
2

4
1

p





Theorem 9.17. Let x be a uniform ±1 bit and let q ∈ (2, ∞]. Then ‖a+ρbx‖q ≤
‖a + bx‖2 for all a, b ∈

assuming ρ ≤ 1/



Equivalent statements are that ‖a + (1/



(2, q, 1/

q − 1)-hypercontractive, and that ‖T

q − 1)bx‖2
p

q ≤ a2 + b2, that x is
f ‖q ≤ ‖ f ‖2 holds for any

1/

q−1

q − 1.


f : {−1, 1} → .

Copyright © Ryan O’Donnell, 2014, 2015, 2016, 2017, 2018, 2019, 2020, 2021.



<!-- pdf-page: 258 -->
258

9. Basics of hypercontractivity

For q an even integer it is not hard (see Exercise 9.36) to prove Theo-
rem 9.17 just as we did for q = 6. Indeed, the proof works even under more
general moment conditions on x, as in Corollary 9.6. Unfortunately, obtaining
Theorem 9.17 for all real q > 2 takes some more tricks. A natural idea is to try
forging ahead as in Proposition 9.16, using the series expansions for (1+ρbx)q
and (1+ b2)q/2 provided by the Generalized Binomial Theorem. However, even
when |b| < 1 (so that convergence is not an issue) there is a difculty because
the coefcients in the expansion of (1 + b2)q/2 are sometimes negative.

Luckily, this issue of negative coefcients in the series expansion goes
away if you try to prove the analogous (p, 2, ρ)-hypercontractivity statement.
Thus the slick proof of Theorem 9.17 proceeds by rst proving that statement,
then “ipping the norms across 2”.

Theorem 9.18. Let x be a uniform ±1 bit and let 1 ≤ p < 2. Then ‖a +ρbx‖2 ≤
‖a + bx‖p for all a, b ∈
p − 1)-
hypercontractive.

p − 1. That is, x is (p, 2,

assuming 0 ≤ ρ ≤





Proof. By Remark 9.14 we may assume a = 1 and ρ =
p − 1. By Exercise 9.7
we may also assume without loss of generality that 1 + bx ≥ 0 for x ∈ {−1, 1};
i.e., that |b| ≤ 1. It then sufces to prove the result for all |b| < 1 because the
|b| = 1 case follows by continuity. Writing b = ≤ for the sake of intuition, we
need to show





p − 1 · ≤x‖p

2 ≤ ‖1 + ≤x‖p

p

‖1 +


⇐⇒ E[(1 +

p − 1 · ≤x)2]p/2 ≤ E[(1 + ≤x)p].

(9.10)

Here we were able to drop the absolute value on the right-hand side because
|≤| < 1. The left-hand side of (9.10) is

(1 + (p − 1)≤2)p/2 ≤ 1 + p(p−1)

2

≤2,

(9.11)

where we used the inequality (1 + t)θ ≤ 1 + θt for t ≥ 0 and 0 ≤ θ ≤ 1 (easily
proved by comparing derivatives in t). As for the right-hand side of (9.10),
since |≤x| < 1 we may use the Generalized Binomial Theorem to show it equals


1 + p≤x + p(p−1)

E

≤2x2 + p(p−1)(p−2)

3!

≤3x3 + p(p−1)(p−2)(p−3)

4!

≤4x4 + · · ·

2!



= 1 + p≤ E[x] + p(p−1)

2!

≤2 E[x2] + p(p−1)(p−2)

3!

≤3 E[x3] + p(p−1)(p−2)(p−3)

≤4 E[x4] + · · ·

= 1 + p(p−1)

2

≤2 + p(p−1)(p−2)(p−3)

4!

≤4 + p(p−1)(p−2)(p−3)(p−4)(p−5)

6!

4!
≤6 + · · · .

In light of (9.11), to verify (9.10) it sufces to note that each “post-quadratic”
term above,

p(p−1)(p−2)(p−3)···(p−(2k−1))
(2k)!

≤2k,

is nonnegative. This follows from 1 ≤ p ≤ 2: the numerator has two positive

factors and an even number of negative factors.

Copyright © Ryan O’Donnell, 2014, 2015, 2016, 2017, 2018, 2019, 2020, 2021.



<!-- pdf-page: 259 -->
9.4. Two-function hypercontractivity and induction

259

To deduce Theorem 9.17 from Theorem 9.18 we again just need to ip the
norms across 2 using the fact that Tρ is self-adjoint. This is accomplished
by taking Ω = {−1, 1}, π = π1/2, q = 2, T = Tp
, and C = 1 in the following
proposition (and noting that 1/

p−1
p − 1):

p′ − 1 =





Proposition 9.19. Let T be a self-adjoint operator on L2(Ω, π), let 1 ≤ p, q ≤
∞, and let p′, q′ be their conjugate Hölder indices. Assume ‖T f ‖q ≤ C‖ f ‖p for
all f . Then ‖T g‖p′ ≤ C‖g‖q′ for all g.

Proof. This follows from

‖T g‖p′ = sup
‖ f ‖p=1

〈 f , T g〉 = sup
‖ f ‖p=1

〈T f , g〉 ≤ sup
‖ f ‖p=1

‖T f ‖q‖g‖q′ ≤ C‖g‖q′,

where the rst equality is the sharpness of Hölder’s inequality, the second
equality holds because T is self-adjoint, the subsequent inequality is Hölder’s,

and the nal inequality uses the hypothesis ‖T f ‖q ≤ C‖ f ‖p.



q − 1)-hypercontractive and (p, 2,

At this point we have established that if x is a uniform ±1 bit, then it
is (2, q, 1/
p − 1)-hypercontractive. In the
next section we will give a very simple induction which transforms these
facts into the full (2, q)- and (p, 2)-Hypercontractivity Theorems stated at the
beginning of the chapter.



9.4. Two-function hypercontractivity and induction

At this point we have established that if f : {−1, 1} → then for any p ≤ 2 ≤ q,

‖Tp

p−1

f ‖2 ≤ ‖ f ‖p,

p

‖T

1/

q−1

f ‖q ≤ ‖ f ‖2.

We would like to extend these facts to the case of general f : {−1, 1}n → ;
i.e., establish the (p, 2)- and (2, q)-Hypercontractivity Theorems stated at the
beginning of the chapter. A natural approach is induction.

In analysis of Boolean functions, there are two methods for proving state-
ments about f : {−1, 1}n → by induction on n. One method, which might be
called “induction by derivatives”, uses the decomposition f (x) = xnDn f (x) +
En f (x). We saw this approach in our inductive proof of the Bonami Lemma.
The other method, which might be called “induction by restrictions”, goes via
the subfunctions f±1 obtained by restricting the nth coordinate of f to ±1. We
saw this approach in our proof of the OSSS Inequality in Chapter 8.6. In both
methods we reduce inductively from one function f to two functions: either
Dn f and En f , or f−1 and f+1. Because of this, when trying to prove a fact
by induction on n it’s often helpful to try proving a generalized fact about
two functions. Our proof of the OSSS Inequality gives a good example of this
technique.

Copyright © Ryan O’Donnell, 2014, 2015, 2016, 2017, 2018, 2019, 2020, 2021.



<!-- pdf-page: 260 -->
260

9. Basics of hypercontractivity

So to facilitate induction, let’s nd a two-function version of the hypercon-
tractivity statements we’ve proven so far. Perhaps the most natural statement
we’ve seen is the noise-stability rephrasing of the (4/3, 2)-Hypercontractivity
Theorem, namely Stab1/3[ f ] ≤ ‖ f ‖2
. At least in the case n = 1, our work in
4/3
the previous section (Theorem 9.18) generalizes this to Stabp−1[ f ] ≤ ‖ f ‖2
p for
1 ≤ p ≤ 2. I.e.,

Stabρ[ f ] =

E
(x,y)
ρ-correlated

[ f (x) f (y)] ≤ ‖ f ‖2

1+ρ

for 0 ≤ ρ ≤ 1. Looking at this, you might naturally guess a (correct) general-
ization for two functions f , g : {−1, 1}n → , namely

E
(x,y)
ρ-correlated

[ f (x)g(y)] ≤ ‖ f ‖1+ρ‖g‖1+ρ.

(9.12)

We have a nice interpretation of this inequality when f , g : {−1, 1}n → {0, 1}
are indicators of subsets A, B ⊆ {−1, 1}n as in Corollary 9.8; it gives an upper
bound on the probability of going from A to B in one step on the ρ-stable
hypercube graph. This bound is sharp when A and B have the same volume,
but for A and B of different sizes you might imagine it’s helpful to measure f
and g by different norms in (9.12). To see what we can expect, let’s break up
the ρ-correlation in (9.12) into two parts; say, write

p

rs,

ρ =

0 ≤ r, s ≤ 1,

E
(x,y)

[ f (x)g(y)] = E[Tp

r f · Tp

s g].

and use

rs-correlated
Then Cauchy–Schwarz implies

p

E
(x,y)
ρ-correlated

[ f (x)g(y)] = E[Tp

r f · Tp

s g] ≤ ‖Tp

r f ‖2‖Tp

s g‖2 ≤ ‖ f ‖1+r‖g‖1+s,

(9.13)
where the last step used (p, 2)-hypercontractivity – which we have so far
only proven in the case n = 1 (Theorem 9.18). The inequality (9.13), restated
below, is precisely the desired two-function version of the (2, q)- and (p, 2)-
Hypercontractive Theorems.

(Weak) Two-Function Hypercontractivity Theorem. Let f , g : {−1, 1}n →
p

, let 0 ≤ r, s ≤ 1, and assume 0 ≤ ρ ≤

rs ≤ 1. Then

E
(x,y)
ρ-correlated

[ f (x)g(y)] ≤ ‖ f ‖1+r‖g‖1+s.

We call this the “Weak” Two-Function Hypercontractivity Theorem be-
cause the hypothesis r, s ≤ 1 is not actually necessary; see Chapter 10.1. As
mentioned, we have so far established this theorem in the case n = 1. However,

Copyright © Ryan O’Donnell, 2014, 2015, 2016, 2017, 2018, 2019, 2020, 2021.



<!-- pdf-page: 261 -->
9.4. Two-function hypercontractivity and induction

261

the beauty of hypercontractivity in this form is that it extends to general n
by an almost trivial induction. The form of the induction is “induction by
restrictions”. (It’s also possible – but a little trickier – to extend the (2, q)-
Hypercontractivity Theorem from n = 1 to general n via “induction by deriva-
tives”; see Exercise 9.16.) For future use, we will write the induction in more
general notation.

Two-Function Hypercontractivity Induction Theorem. Let 0 ≤ ρ ≤ 1
and assume that

[ f (x)g(y)] ≤ ‖ f ‖p‖g‖q

E
(x,y)
ρ-correlated

holds for every f , g ∈ L2(Ω, π). Then the inequality also holds for every f , g ∈
L2(Ωn, π⊗n).

Proof. The proof is by induction on n, with the n = 1 case holding by assump-
tion. For n > 1, let f , g ∈ L2(Ωn, π⊗n) and let (x, y) denote a ρ-correlated pair
under π⊗n. We’ll use the notation x = (x′, xn) where x′ = (x1, . . . , xn−1), and
similar notation for y. Note that (x′, y′) and (xn, yn) are both ρ-correlated
for the
pairs (of length n−1 and 1, respectively). We’ll also write f xn
restriction of f in which the last coordinate is xed to value xn, and similarly
for g. Now

= f[n−1]|xn

E
(x,y)

[ f (x)g(y)] = E

(xn,yn)

E
(x′,y′)

[ f xn

(x′)g yn

(y′)] ≤ E

(xn,yn)

[‖ f xn

‖p‖g yn

‖q]

by induction. If we write F ∈ L2(Ω, π) for the function xn 7→ ‖ f xn
larly write G(yn) = ‖g yn

‖q, then we may continue the above as

‖p and simi-

E
(xn,yn)

[‖ f xn

‖p‖g yn

‖q] = E

(xn,yn)

[F(xn)G(yn)] ≤ ‖F‖p,xn

‖G‖q,yn

,

where we used the base case of the induction. Finally,

‖F‖p,xn

= E
xn

[|F(xn)|p]1/p = E
xn

[‖ f xn

‖p
p]1/p =



E
xn

E
x′

| f xn

(x′)|p]

1/p = ‖ f ‖p

by denition, and similarly for ‖G‖q,yn
‖ f ‖p‖g‖q, completing the induction.

. Thus we have established E[ f (x)g(y)] ≤


Remark 9.20. More generally, if we assume the inequality holds over each
of (Ω1, π1), . . . , (Ωn, πn), then it also holds over (Ω1 × · · · × Ωn, π1 ⊗ · · · ⊗ πn); the
only change needed to the proof is notational.

At this point, we have fully established the Weak Two-Function Hyper-
contractivity Theorem. By taking g = f and r = s = ρ in the theorem we
obtain the full (p, 2)-Hypercontractivity Theorem stated at the beginning of
the chapter. Finally, by applying Proposition 9.19 we also obtain the (2, q)-
Hypercontractivity Theorem for all f : {−1, 1}n → .

Copyright © Ryan O’Donnell, 2014, 2015, 2016, 2017, 2018, 2019, 2020, 2021.



<!-- pdf-page: 262 -->
262

9. Basics of hypercontractivity

9.5. Applications of hypercontractivity

With the (2, q)- and (p, 2)-Hypercontractivity Theorems in hand, let’s revisit
some applications we saw in Sections 9.1 and 9.2. We begin by deducing a
generalization of the Bonami Lemma:

Theorem 9.21. Let f : {−1, 1}n → have degree at most k. Then ‖ f ‖q ≤


k

q − 1

‖ f ‖2 for any q ≥ 2.

Proof. We have

‖ f ‖2

q = ‖T

p

1/

q−1

Tp

q−1

f ‖2

q ≤ ‖Tp

q−1

f ‖2
2

using the (2, q)-Hypercontractivity Theorem.
denition of Tρ to ρ > 1 via Tρ f =
now follows since



(Here we are extending the
j ρ j f = j; see also Remark 8.29.) The result

‖Tp

f ‖2

2 =

q−1

k∑

j=0

(q − 1) jW j[ f ] ≤ (q − 1)k

k∑

j=0

W j[ f ] = (q − 1)k‖ f ‖2
2.



Using a trick similar to the one in our proof of the (4/3, 2)-Hypercontractivity
p − 1)k‖ f ‖p when f has de-
Theorem you can use this to deduce ‖ f ‖2 ≤ (1/
gree k for any 1 ≤ p ≤ 2; see Exercise 9.14. However, a different trick yields a
strictly better result, including a nite bound for p = 1:



Theorem 9.22. Let f : {−1, 1}n → have degree at most k. Then ‖ f ‖2 ≤ ek‖ f ‖1.
More generally, for 1 ≤ p ≤ 2 it holds that ‖ f ‖2 ≤ (e

−1)k‖ f ‖p.

2
p

Proof. We prove the statement about the 1-norm, leaving the case of general
1 + 1−θ
1 ≤ p ≤ 2 to Exercise 9.15. For ≤ > 0, let 0 < θ < 1 be the solution of 1
2+≤
(namely, θ = 1
). Applying the general version of Hölder’s inequality and
2
then Theorem 9.21, we get

2 = θ

≤
1+≤

‖ f ‖2 ≤ ‖ f ‖1−θ

2+≤ ‖ f ‖θ

1 ≤

p

1 + ≤

k(1−θ)

‖ f ‖1−θ
2

‖ f ‖θ
1.

Dividing by ‖ f ‖1−θ
2
result to the power of 1/θ yields

(which we may assume is nonzero) and then raising the



‖ f ‖2 ≤

(1 + ≤)

k

1−θ
2θ



‖ f ‖1 =

(1 + ≤)

k

1
≤

+ 1
2

‖ f ‖1.

The result follows by taking the limit as ≤ → 0.





In the linear case of k = 1, Theorems 9.21 and 9.22 taken together show
that c p‖
i ai xi‖2 for some constants 0 < c p < C p
depending only on p ∈ [1, ∞). This fact is known as Khintchine’s Inequality.

i ai xi‖p ≤ C p‖

i ai xi‖2 ≤ ‖





Theorem 9.21 can be used to get a strong concentration bound for degree-k
ai xi

Boolean functions. Chernoff tells us that the probability a linear form



Copyright © Ryan O’Donnell, 2014, 2015, 2016, 2017, 2018, 2019, 2020, 2021.



<!-- pdf-page: 263 -->
9.5. Applications of hypercontractivity

263

exceeds t standard deviations decays like exp(−Θ(t2)). The following theorem
generalizes this to degree-k forms, with decay exp(−Θ(t2/k)):

Theorem 9.23. Let f : {−1, 1}n → have degree at most k. Then for any
t ≥

we have

2e

p

k

Pr
x∼{−1,1}n

[| f (x)| ≥ t‖ f ‖2] ≤ exp





.

− k

2e t2/k

Proof. We may assume ‖ f ‖2 = 1 without loss of generality. Let q ≥ 2 be a
parameter to be chosen later. By Markov’s inequality,

Pr[| f (x)| ≥ t] = Pr[| f (x)|q ≥ tq] ≤

E[| f (x)|q]
tq

.

By Theorem 9.21 we have

E[| f (x)|q] ≤ (



k

q − 1

)q‖ f ‖q

2 = (q − 1)(k/2)q ≤ q(k/2)q.

Thus Pr[| f (x)| ≥ t] ≤ (qk/2/t)q. It’s not hard to see that the q that minimizes
this expression should be just slightly less than t2/k. Specically, by choosing
q = t2/k/e ≥ 2 we get

Pr[| f (x)| ≥ t] ≤ exp(−(k/2)q) = exp





− k

2e t2/k

as claimed.



We can use Theorem 9.22 to get a “one-sided” analogue of Theorem 9.7,
showing that a low-degree function exceeds its mean with noticeable proba-
bility:

Theorem 9.24. Let f : {−1, 1}n → be a nonconstant function of degree at
most k. Then



Pr
x∼{−1,1}n

f (x) > E[ f ]



≥ 1

4 e−2k.

Proof. We may assume E[ f ] = 0 without loss of generality. We then have

1

2 ‖ f ‖1 = 1

2



E[ f · 1{ f (x)>0}] − E[ f · (1 − 1{ f (x)>0})]



= E[ f · 1{ f (x)>0}];

hence,

1

4 ‖ f ‖2

1 = E[ f · 1{ f (x)>0}]2 ≤ E[ f 2] · E[12

{ f (x)>0}] ≤ e2k‖ f ‖2

1 · Pr[ f (x) > 0]

using Cauchy–Schwarz and Theorem 9.22. The result follows.



Next we turn to noise stability. Using the (p, 2)-Hypercontractivity Theo-
rem we can immediately deduce the following generalization of Corollary 9.8:

Copyright © Ryan O’Donnell, 2014, 2015, 2016, 2017, 2018, 2019, 2020, 2021.



<!-- pdf-page: 264 -->
264

9. Basics of hypercontractivity

Small-Set Expansion Theorem. Let A ⊆ {−1, 1}n have volume α; i.e., let
1A : {−1, 1}n → {0, 1} satisfy E[1A] = α. Then for any 0 ≤ ρ ≤ 1,

Stabρ[1A] = Pr

x∼{−1,1}n
y∼Nρ(x)

[x ∈ A, y ∈ A] ≤ α

2
1+ρ .

Equivalently (for α > 0),

[y ∈ A] ≤ α

1−ρ
1+ρ .

Pr
x∼A
y∼Nρ(x)

In other words, the δ-noisy hypercube is a small-set expander for any δ > 0:
the probability that one step from a random x ∼ A stays inside A is at most
αδ/(1−δ). It’s also possible to derive a “two-set” generalization of this fact using
the Two-Function Hypercontractivity Theorem; we defer the discussion to
Chapter 10.1 since the most general result requires the non-weak form of the
theorem. We can also obtain the generalization of Corollary 9.12:

Corollary 9.25. Let f : {−1, 1}n → {−1, 1}. Then for any 0 ≤ ρ ≤ 1 we have
Inf(ρ)
i

2
1+ρ for all i.

[ f ] ≤ Infi[ f ]

Finally, from the Small-Set Expansion Theorem we see that indicators
of small-volume sets are not very noise-stable and hence can’t have much
of their Fourier weight at low levels. Indeed, using hypercontractivity we
can deduce the Level-1 Inequality from Chapter 5.4 and also generalize it to
higher degrees.

Level-k Inequalities. Let f : {−1, 1}n → {0, 1} have mean E[ f ] = α and let
k ∈ + be at most 2 ln(1/α). Then

W≤k[ f ] ≤



2e
k ln(1/α)

k

α2.

Proof. By the Small-Set Expansion Theorem,

W≤k[ f ] ≤ ρ−kStabρ[ f ] ≤ ρ−kα2/(1+ρ) ≤ ρ−kα2(1−ρ)
for any 0 < ρ ≤ 1. Basic calculus shows the right-hand side is minimized when

ρ =

2 ln(1/α) ≤ 1; substituting this into ρ−kα2(1−ρ) yields the claim.

k

For the case k = 1, a slightly different argument gives the sharp Level-1

Inequality W1[ f ] ≤ 2α2 ln(1/α); see Exercise 9.18.

9.6. Highlight: The Kahn–Kalai–Linial Theorem

Recalling the social choice setting of Chapter 2.1, consider a 2-candidate, n-
voter election using a monotone voting rule f : {−1, 1}n → {−1, 1}. We assume
the impartial culture assumption (that the votes are independent and uni-
formly random), but with a twist: one of the candidates, say b ∈ {−1, 1}, is able

Copyright © Ryan O’Donnell, 2014, 2015, 2016, 2017, 2018, 2019, 2020, 2021.



<!-- pdf-page: 265 -->
9.6. Highlight: The Kahn–Kalai–Linial Theorem

265

to secretly bribe k voters, xing their votes to b. (Since f is monotone, this is
always the optimal way for the candidate to x the bribed votes.) How much
can this inuence the outcome of the election? This question was posed by
Ben-Or and Linial in a 1985 work [BL85, BL90]; more precisely, they were
interested in designing (unbiased) voting rules f that minimize the effect of
any bribed k-coalition.

Let’s rst consider k = 1.

If voter i is bribed to vote for candidate b
(but all other votes remain uniformly random), this changes the bias of f by
b f (i) = bInfi[ f ]. Here we used the assumption that f is monotone (i.e., Propo-
sition 2.21). This led Ben-Or and Linial to the question of which unbiased
f : {−1, 1}n → {−1, 1} has the least possible maximum inuence:

Denition 9.26. Let f : {−1, 1}n → . The maximum inuence of f is

MaxInf[ f ] = max{Infi[ f ] : i ∈ [n]}.

Ben-Or and Linial constructed the (nearly) unbiased Tribesn : {−1, 1}n →
{−1, 1} function (from Chapter 4.2) and noted that MaxInf[Tribesn] = O( log n
n ).
They further conjectured every unbiased function f has MaxInf[ f ] = Ω( log n
n ).
This conjecture was famously proved by Kahn, Kalai, and Linial [KKL88]:

Kahn–Kalai–Linial (KKL) Theorem. For any f : {−1, 1}n → {−1, 1},

MaxInf[ f ] ≥ Var[ f ] · Ω

 log n
n



.

Notice that the theorem says something sensible even for very biased
functions f , i.e., those with low variance. The variance of f is indeed the right
“scaling factor” since

1
n

Var[ f ] ≤ MaxInf[ f ] ≤ Var[ f ]

holds trivially, by the Poincaré Inequality and Exercise 2.8.

Before proving the KKL Theorem, let’s see an additional consequence for

Ben-Or and Linial’s problem.

Proposition 9.27. Let f : {−1, 1}n → {−1, 1} be monotone and assume E[ f ] ≥
−.99. Then there exists a subset J ⊆ [n] with |J| ≤ O(n/ log n) that if “bribed to
vote 1” causes the outcome to be 1 almost surely; i.e.,

E[ f

J|(1,...,1)

] ≥ .99.

(9.14)

Similarly, if E[ f ] ≤ .99 there exists J ⊆ [n] with |J| ≤ O(n/ log n) such that
E[ f

] ≤ −.99.

J|(−1,...,−1)

Proof. By symmetry it sufces to prove the result regarding bribery by can-
didate +1. The candidate executes the following strategy: First, bribe the
voter i1 with the largest inuence on f0 = f ; then bribe the voter i2 with

Copyright © Ryan O’Donnell, 2014, 2015, 2016, 2017, 2018, 2019, 2020, 2021.



<!-- pdf-page: 266 -->
266

9. Basics of hypercontractivity

the largest inuence on f1 = f (i17→1); then bribe the voter i3 with the largest
inuence on f2 = f (i1,i27→1); etc. For each t ∈ we have

E[ f t+1] ≥ E[ f t] + MaxInf[ f t].

If after t bribes the candidate has not yet achieved (9.14) we have −.99 ≤
E[ f t] < .99; thus Var[ f t] ≥ Ω(1) and the KKL Theorem implies MaxInf[ f t] ≥
Ω( log n
n ). Thus the candidate will achieve a bias of at least .99 after bribing at
most (.99 − (−.99))/Ω( log n


n ) = O(n/ log n) voters.

Thus in any monotone election scheme, there is always a candidate b ∈
{−1, 1} and a o(1)-fraction of the voters that b can bribe such that the election
becomes 99%-biased in b’s favor. And if the election scheme was not terribly
biased to begin with, then both candidates have this ability. For a more
precise version of this result, see Exercise 9.27; for a nonmonotone version,
see Exercise 9.28. Note also that although the Tribesn function is essentially
optimal for standing up to a single bribed voter, it is quite bad at standing
up to bribed coalitions: by bribing just a single tribe (DNF term) – about
log n voters – the outcome can be completely forced to True. Nevertheless,
Proposition 9.27 is close to sharp: Ajtai and Linial [AL93] constructed an
unbiased monotone function f : {−1, 1}n → {−1, 1} such that bribing any set of
at most ≤n/ log2 n voters changes the expectation by at most O(≤).

The remainder of this section is devoted to the proof of the KKL The-
orem and some variants. As mentioned earlier, the proof quickly follows
from summing Corollary 9.12 over all coordinates; but let’s give a more
leisurely description. We’ll focus on the main case of interest: showing that
MaxInf[ f ] ≥ Ω( log n
n ) when f is unbiased (i.e., Var[ f ] = 1). If f ’s total inu-
ence is at least, say, .1 log n, then even the average inuence is Ω( log n
n ). So we
may as well assume I[ f ] ≤ .1 log n.

This leads us to the problem of characterizing (unbiased) functions with
small total inuence. (This is the same issue that arose at the end of Chap-
ter 8.4 when studying sharp thresholds.) It’s helpful to think about the case
that the total inuence is very small – say I[ f ] ≤ K where K = 10 or K = 100,
though we eventually want to handle K = .1 log n. Let’s think of f as the indi-
cator of a volume-1/2 set A ⊂ {−1, 1}n, so I[ f ]
n is the fraction of Hamming cube
edges on the boundary of A. The edge-isoperimetric inequality (or Poincaré
Inequality) tells us that I[ f ] ≥ 1: at least a 1
n fraction of the cube’s edges must
be on A’s boundary, with dictators and negated-dictators being the minimiz-
ers. Now what can we say if I[ f ] ≤ K; i.e., A’s boundary has only K times
more edges than the minimum? Must f be “somewhat similar” to a dictator
or negated-dictator? Kahn, Kalai, and Linial showed that the answer is yes:

Copyright © Ryan O’Donnell, 2014, 2015, 2016, 2017, 2018, 2019, 2020, 2021.



<!-- pdf-page: 267 -->
9.6. Highlight: The Kahn–Kalai–Linial Theorem

267

f must have a coordinate with inuence at least 2−O(K). This should be con-
sidered very large (and dictator-like), since a priori all of the inuences could
have been equal to K
n .

KKL Edge-Isoperimetric Theorem. Let f : {−1, 1}n → {−1, 1} be noncon-
stant and let I[ f ] = I[ f ]/ Var[ f ] ≥ 1 (which is just I[ f ] if f is unbiased). Then




MaxInf[ f ] ≥

9
I[ f ]2

· 9−I[ f ].

This theorem is sharp for I[ f ] = 1 (cf. Exercises 1.19, 5.35), and it’s non-
trivial (in the unbiased case) for I[ f ] as large as Θ(log n). This last fact lets us
complete the proof of the KKL Theorem as originally stated:

Proof of the KKL Theorem from the Edge-Isoperimetric version.
We may assume f is nonconstant. If I[ f ] = I[ f ]/ Var[ f ] ≥ .1 log n, then we
are done: the total inuence is at least .1 Var[ f ]·log n and hence MaxInf[ f ] ≥
.1 Var[ f ] · log n

n . Otherwise, the KKL Edge-Isoperimetric Theorem implies

MaxInf[ f ] ≥ Ω





1
log2 n

· 9−.1 log n = Ω(n−.1 log 9) = Ω(n−.317) ¿ Var[ f ] · Ω



log n
n



.


(You are asked to be careful about the constant factors in Exercise 9.30.)

We now turn to proving the KKL Edge-Isoperimetric Theorem. The high-
level idea is to look at the contrapositive: supposing all of f ’s inuences are
small, we want to show its total inuence must be large. The assumption here
is that each derivative Di f is a {−1, 0, 1}-valued function which is nonzero only
on a “small” set. Hence “small-set expansion” implies that each derivative has
“unusually large” noise sensitivity. (We are really just repeating Corollary 9.12
in words here.) In turn this means that for each i ∈ [n], the Fourier weight
of f on coefcients containing i must be quite “high up”. Since this holds for
all i we deduce that all of f ’s Fourier weight must be quite “high up” – hence
f must have “large” total inuence. We now make this story formal:

Proof of the KKL Edge-Isoperimetric Theorem. We treat only the case
that f is unbiased, leaving the general case to Exercise 9.29 (see also the ver-
sion for product space domains in Chapter 10.3). The theorem is an immediate
consequence of the following chain of inequalities:

3 · 3−I[ f ]

(a)
≤ 3Stab1/3[ f ]

(b)
≤ I(1/3)[ f ]

(c)
≤

Infi[ f ]3/2 (d)

≤ MaxInf[ f ]1/2 · I[ f ].

n∑

i=1

The key inequality is (c), which comes from summing Corollary 9.12 over all
coordinates i ∈ [n]. Inequality (d) is immediate from Infi[ f ]3/2 ≤ MaxInf[ f ]1/2·

Copyright © Ryan O’Donnell, 2014, 2015, 2016, 2017, 2018, 2019, 2020, 2021.



<!-- pdf-page: 268 -->
268

9. Basics of hypercontractivity

Infi[ f ]. Inequality (b) is trivial from the Fourier formulas (recall Fact 2.53):

I(1/3)[ f ] =

∑

|S|≥1

|S|(1/3)|S|−1 f (S)2 ≥ 3

∑

|S|≥1

(1/3)|S| f (S)2 = 3Stab1/3[ f ]

(the last equality using f (;) = 0). Finally, inequality (a) is quickly proved
using the spectral sample: for S ∼ S f we have

3Stab1/3[ f ] = 3

∑

S⊆[n]

(1/3)|S| f (S)2 = 3 E[3−|S|] ≥ 3 · 3− E[|S|] = 3 · 3−I[ f ],

(9.15)

the inequality following from convexity of s 7→ 3−s.



We end this chapter by deriving an even stronger version of the KKL Edge-
Isoperimetric Theorem, and deducing Friedgut’s Junta Theorem (from the end
of Chapter 3.1) as a consequence. The KKL Edge-Isoperimetric Theorem tells
us that if f is unbiased and I[ f ] ≤ K then f must look somewhat like a 1-junta,
in the sense of having a coordinate with inuence at least 2−O(K). Friedgut’s
Junta Theorem shows that in fact f must essentially be a 2O(K)-junta. To
obtain this conclusion, you really just have to sum Corollary 9.12 only over
the coordinates which have small inuence on f . It’s also possible to get
even stronger conclusions if f is known to have particularly good low-degree
Fourier concentration. In aid of this, we’ll start by proving the following
somewhat technical-looking result:

Theorem 9.28. Let f : {−1, 1}n → {−1, 1}. Given 0 < ≤ ≤ 1 and k ≥ 0, dene

τ =

≤2
I[ f ]2

9−k,

J = { j ∈ [n] : Inf j[ f ] ≥ τ},

so |J| ≤ (I[ f ]3/≤2)9k.

Then f ’s Fourier spectrum is ≤-concentrated on

F = {S : S ⊆ J} ∪ {S : |S| > k}.

In particular, suppose f ’s Fourier spectrum is also ≤-concentrated on degree up
to k. Then f ’s Fourier spectrum is 2≤-concentrated on

F ′ = {S : S ⊆ J, |S| ≤ k},

and f is ≤-close to a |J|-junta h : {−1, 1}J → {−1, 1}.

Proof. Summing Corollary 9.12 just over i 6∈ J we obtain

∑

i6∈J

Inf(1/3)
i

[ f ] ≤

∑

i6∈J

Infi[ f ]3/2 ≤ max
i6∈J

{Infi[ f ]1/2} ·

∑

i6∈J

Infi[ f ] ≤ τ1/2 · I[ f ] ≤ 3−k≤,

Copyright © Ryan O’Donnell, 2014, 2015, 2016, 2017, 2018, 2019, 2020, 2021.



<!-- pdf-page: 269 -->
9.6. Highlight: The Kahn–Kalai–Linial Theorem

269

where the last two inequalities used the denitions of J and τ, respectively.
On the other hand,
∑

∑

∑

∑

(1/3)|S|−1 f (S)2 =

|S ∩ J| · 31−|S| f (S)2

Inf(1/3)
i

[ f ] =

i6∈J

i6∈J

S3i

S
|S ∩ J| · 31−|S| f (S)2 ≥ 3−k

≥

∑

S6∈F

∑

S6∈F

f (S)2.

Here the last inequality used that S 6∈ F implies |S ∩ J| ≥ 1 and 31−|S| ≥ 3−k.
Combining these two deductions yields

f (S)2 ≤ ≤, as claimed.



S6∈F

As for the second part of the theorem, when f ’s Fourier spectrum is 2≤-
concentrated on F ′ it follows from Proposition 3.31 that f is 2≤-close to the
Boolean-valued |J|-junta sgn( f ⊆J). From Exercise 3.34 we may deduce that f
is in fact ≤-close to some h : {−1, 1}J → {−1, 1}.


Remark 9.29. As you are asked to show in Exercise 9.31, by using Corol-
lary 9.25 in place of Corollary 9.12, we can achieve junta size (I[ f ]2+η/≤1+η) ·
C(η)k in Theorem 9.28 for any η > 0, where C(η) = (2/η + 1)2.

In Theorem 9.28 we may always take k = I[ f ]/≤, by the “Markov argument”

Proposition 3.2. Thus we obtain as a corollary:

Friedgut’s Junta Theorem. Let f : {−1, 1}n → {−1, 1} and let 0 < ≤ ≤ 1. Then
f is ≤-close to an exp(O(I[ f ]/≤))-junta.
Indeed, there is a set J ⊆ [n] with
|J| ≤ exp(O(I[ f ]/≤)) such that f ’s Fourier spectrum is 2≤-concentrated on {S ⊆
J : |S| ≤ I[ f ]/≤}.

As mentioned, we can obtain stronger results for functions f that are ≤-
concentrated up to degree much less than I[ f ]/≤. Width-w DNFs, for example,
are ≤-concentrated on degree up to O(w log(1/≤)) (by Theorem 4.22). Thus:

Corollary 9.30. Any width-w DNF is ≤-close to a (1/≤)O(w)-junta.

Uniformly noise-stable functions do even better. From Peres’s Theorem we
know that linear threshold functions are ≤-concentrated up to degree O(1/≤2).
Thus Theorem 9.28 and Remark 9.29 imply:

Corollary 9.31. Let f : {−1, 1}n → {−1, 1} be a linear threshold function and
let 0 < ≤, η ≤ 1/2. Then f is ≤-close to a junta on I[ f ]2+η · (1/η)O(1/≤2) coordinates.

Assuming ≤ is a small universal constant we can take η = 1/ log(O(I[ f ])) and
deduce that every LTF is ≤-close to a junta on I[ f ]2 · polylog(I[ f ]) coordinates.
This is essentially best possible since I[Majn] = Θ(
n), but Majn is not even
.1-close to any o(n)-junta. By virtue of Theorem 5.37 on the uniform noise
stability of PTFs, we can also get this conclusion for any constant-degree PTF.

p

Copyright © Ryan O’Donnell, 2014, 2015, 2016, 2017, 2018, 2019, 2020, 2021.



<!-- pdf-page: 270 -->
270

9. Basics of hypercontractivity

One more interesting fact we may derive is that every Boolean function
has a Fourier coefcient that is at least inverse-exponential in the square of
its total inuence:

Corollary 9.32. Assume f : {−1, 1}n → {−1, 1} satises Var[ f ] ≥ 1/2. Then
there exists S ⊆ [n] with 0 < |S| ≤ O(I[ f ]) such that f (S)2 ≥ exp(−O(I[ f ]2)).

Proof. Taking ≤ = 1/8 in Friedgut’s Junta Theorem we get a set of coordinates
J with |J| ≤ exp(O(I[ f ])) such that f has Fourier weight at least 1 − 2≤ =
3/4 on F = {S ⊆ J : |S| ≤ 8I[ f ]}. Since f (;)2 = 1 − Var[ f ] ≤ 1/2 we conclude
that f has Fourier weight at least 1/4 on F ′ = F \ {;}. But |F ′| ≤ |J|8I[ f ] =
exp(O(I[ f ]2)), so the result follows by the Pigeonhole Principle. (Here we used
that (1/4) exp(−O(I[ f ]2)) = exp(−O(I[ f ]2)) because I[ f ] ≥ Var[ f ] ≥ 1


2 .)

Remark 9.33. Of course, if Var[ f ] < 1/2, then f has a large empty Fourier
coefcient: f (;)2 ≥ 1/2. For a more rened version of Corollary 9.32, see
Exercise 9.32.

It is an open question whether Corollary 9.32 can be improved to give a

Fourier coefcient satisfying f (S)2 ≥ exp(−O(I[ f ])) (but see Exercise 9.33).

9.7. Exercises and notes

9.1 For every 1 < b < B show that there is a b-reasonable random variable X

such that 1 + X is not B-reasonable.

9.2 For k = 1, improve the 9 in the Bonami Lemma to 3. More precisely,
suppose f : {−1, 1}n → has degree at most 1 and that x1, . . . , xn are
independent 3-reasonable random variables satisfying E[xi] = E[x3
] = 0.
i
(For example, the xi’s may be uniform ±1 bits.) Show that f (x) is also
3-reasonable. (Hint: By direct computation, or by running through the
Bonami Lemma proof with k = 1 more carefully.)

9.3 Let k be a positive multiple of 3 and let n ≥ 2k be an integer. Dene

f : {−1, 1}n → by

f (x) =

∑

xS.

S⊆[n]
|S|=k

(a) Show that



E[ f 4] ≥

n
k/3, k/3, k/3, k/3, k/3, k/3, n−2k
2
n
k



E[ f 2]2,

where the numerator of the fraction is a multinomial coefcient –
specically, the number of ways of choosing six disjoint size-k/3 sub-
sets of [n]. (Hint: Given such size-k/3 subsets, consider quadruples of
size-k subsets that hit each size-k/3 subset twice.)

Copyright © Ryan O’Donnell, 2014, 2015, 2016, 2017, 2018, 2019, 2020, 2021.



<!-- pdf-page: 271 -->
9.7. Exercises and notes

271

(b) Using Stirling’s Formula, show that


lim
n→∞

n
k/3, k/3, k/3, k/3, k/3, k/3, n−2k
2
n
k



= Θ(k−29k).

k

p

Deduce the following lower bound for the Bonami Lemma: ‖ f ‖4 ≥
Ω(k−1/2) ·
(In fact, ‖ f ‖4 = Θ(k−1/4) ·
‖ f ‖2 and such an
upper bound holds for all f homogeneous of degree k; see Exercise
and 9.38(f ).)

‖ f ‖2.

p

3

3

k

9.4 Prove Corollary 9.6.
9.5 Let 0 ≤ δ ≤ 1

1600 and let f , ` be real numbers satisfying |`2 − 1| > 39

δ
and | f | = 1. Show that | f − `|2 ≥ 169δ. (This is a loose estimate; stronger
ones are possible.)

p

9.6 Theorem 9.21 shows that the (2, 4)-Hypercontractivity Theorem implies
the Bonami Lemma. In this exercise you will show the reverse implication.

(a) Let f : {−1, 1}n → . For a xed δ ∈ (0, 1), use the Bonami Lemma to

show that

‖T(1−δ)/

p

3 f ‖4 ≤

∞∑

k=0

(1 − δ)k‖ f =k‖2 ≤ 1
δ

‖ f ‖2.

(b) For g : {−1, 1}n → and d ∈ +, let g⊕d : {−1, 1}dn → be the function
dened by g⊕d(x(1), . . . , x(d)) = g(x(1))g(x(2)) · · · g(x(d)) (where each x(i) ∈
{−1, 1}n). Show that ‖Tρ(g⊕d)‖p = ‖Tρ g‖d
p holds for every p ∈ + and
ρ ∈ [−1, 1]. Note the special case ρ = 1.

(c) Deduce from parts (a) and (b) that in fact ‖T(1−δ)/
Apply part (a) to f ⊕d for larger and larger d.)
p

(d) Deduce that in fact ‖T1/

3 f ‖4 ≤ ‖ f ‖2; i.e., the (2, 4)-Hypercontractivity
Theorem follows from the Bonami Lemma. (Hint: Take the limit as
δ → 0+.)

p

3 f ‖4 ≤ ‖ f ‖2. (Hint:

9.7 Suppose we wish to show that ‖Tρ f ‖q ≤ ‖ f ‖p for all f : {−1, 1}n → . Show
that it sufces to show this for all nonnegative f . (Hint: Exercise 2.34.)

9.8 Fix k ∈ . The goal of this exercise is to show that “projection to degree k

is a bounded operator in all L p norms, p > 1”. Let f : {−1, 1}n → .
(a) Let q ≥ 2. Show that ‖ f ≤k‖q ≤

‖ f ‖q. (Hint: Use Theorem 9.21

q − 1



k

to show the stronger statement ‖ f ≤k‖q ≤

(b) Let 1 < q ≤ 2. Show that ‖ f ≤k‖q ≤ (1/

(Hint: Either
give a similar direct proof using the (p, 2)-Hypercontractivity Theo-
rem, or explain how this follows from part (a) using the dual norm
Proposition 9.19.)

q − 1)k‖ f ‖q.

k

q − 1

‖ f ‖2.)



9.9 Let X be (p, q, ρ)-hypercontractive.

Copyright © Ryan O’Donnell, 2014, 2015, 2016, 2017, 2018, 2019, 2020, 2021.



<!-- pdf-page: 272 -->
272

9. Basics of hypercontractivity

(a) Show that cX is (p, q, ρ)-hypercontractive for any c ∈ .
(b) Show that ρ ≤ ‖X ‖p
‖X ‖q

.

9.10 Let X be (p, q, ρ)-hypercontractive. (For simplicity you may want to as-

sume X is a discrete random variable.)
(a) Show that E[X ] must be 0. (Hint: Taylor expand ‖1 + ρ≤X ‖r to one

term around ≤ = 0; note that ρ < 1 by denition.)



p−1
q−1 . (Hint: Taylor expand ‖1 + ρ≤X ‖r to two terms

(b) Show that ρ ≤
around ≤ = 0.)

9.11 (a) Suppose E[X ] = 0. Show that X is (q, q, 0)-hypercontractive for all

q ≥ 1. (Hint: Use monotonicity of norms to reduce to the case q = 1.)

(b) Show further that X is (q, q, ρ)-hypercontractive for all 0 ≤ ρ < 1.
(Hint: Write (a + ρ X ) = (1 − ρ)a + ρ(a + X ) and employ the triangle
inequality for ‖ · ‖q.)

(c) Show that if X is (p, q, ρ)-hypercontractive, then it is also (p, q, ρ′)-
hypercontractive for all 0 ≤ ρ′ < ρ. (Hint: Use the previous exercise
along with Exercise 9.10(a).)

9.12 Let X be a (nonconstant) (2, 4, ρ)-hypercontractive random variable. The
goal of this exercise is to show the following anticoncentration result: For
all θ ∈

and 0 < t < 1,

Pr[|X − θ| > t‖X ‖2] ≥ (1 − t2)2ρ4.

(a) Reduce to the case ‖X ‖2 = 1.
(b) Letting Y = (X − θ)2, show that E[Y ] = 1 + θ2 and E[Y 2] ≤ (ρ−2 + θ2)2.
(c) Using the Paley–Zygmund inequality, show that

Pr[|X − θ| > t] ≥



ρ2(1 − t2) + ρ2θ2
1 + ρ2θ2

)2

.

(d) Show that the right-hand side above is minimized for θ = 0, thereby

completing the proof.

9.13 Let m ∈ + and let f : {−1, 1}n → [m] be “unbiased”, meaning Pr[ f (x) =
i] = 1
m for all i ∈ [m]. Let 0 ≤ ρ ≤ 1 and let (x, y) be a ρ-correlated pair.
Show that Pr[ f (x) = f (y)] ≤ (1/m)(1−ρ)/(1+ρ). (More generally, you might
show that this is an upper bound on Stabρ[ f ] for all f : {−1, 1}n → 4m
with E[ f ] = ( 1

m ); see Exercise 8.33.)

m , . . . , 1

9.14 (a) Let f : {−1, 1}n → have deg( f ) ≤ k. Prove that ‖ f ‖2 ≤ (1/

p − 1)k‖ f ‖p
for any 1 ≤ p ≤ 2 using the Hölder inequality strategy from our proof of
the (4/3, 2)-Hypercontractivity Theorem, together with Theorem 9.21.
p − 1 for all 1 ≤ p < 2; i.e., the trickier

(b) Verify that exp( 2



p − 1) < 1/

Theorem 9.22 strictly improves on the bound from part (a).



Copyright © Ryan O’Donnell, 2014, 2015, 2016, 2017, 2018, 2019, 2020, 2021.



<!-- pdf-page: 273 -->
9.7. Exercises and notes

273

9.15 Prove Theorem 9.22 in full generality.

(Hint: Let θ be the solution of

1

2 = θ

p + 1−θ

2+≤

. You will need to show that 1−θ
2θ

= ( 2

p − 1) 1

≤

+ ( 1

p − 1

2 ).)

9.16 As mentioned, it’s possible to deduce the (2, q)-Hypercontractivity The-
orem from the n = 1 case using induction by derivatives. From this
one can also obtain the (p, 2)-Hypercontractivity Theorem via Proposi-
tion 9.19. Employing the notation x = (x′, xn), T = T
, d = Dn f (x′),
and e = En f (x′), ll in details and justications for the following proof
sketch:

q−1

p

1/

p

‖T

1/

q−1

f ‖2

q = E
x′





E
xn



|Te + (1/

q − 1)xnTd|q

2/q



≤ E
x′

((Te)2 + (Td)2)q/2

2/q

= ‖(Te)2+(Td)2‖q/2 ≤ ‖(Te)2‖q/2+‖(Td)2‖q/2 = ‖Te‖2

q+‖Td‖2

q ≤ ‖e‖2

2+‖d‖2

2 = ‖ f ‖2
2.

9.17 Deduce the p < 2 < q cases of the Hypercontractivity Theorem from the
(2, q)- and (p, 2)-Hypercontractivity Theorems. (Hint: Use the semigroup
property of Tρ, Exercise 2.32.)
9.18 Let f : {−1, 1}n → {0, 1} have E[ f ] = α.

(a) Show that W1[ f ] ≤ 1
ρ
(b) Deduce the sharp Level-1 Inequality W1[ f ] ≤ 2α2 ln(1/α). (Hint: Take

(α2/(1+ρ) − α2) for any 0 < ρ ≤ 1.

the limit ρ → 0+.)

9.19 For f : {−1, 1}n → {0, 1} with E[ f ] = α, show that W≤k[ f ] = o(α) (as α → 0)

provided k ≤ .373 ln(1/α).

9.20 Show that the KKL Theorem fails for functions f : {−1, 1}n → [−1, 1], even
under the assumption Var[ f ] ≥ Ω(1). (Hint: f (x) = trunc[−1,1]( x1+···+xnp

).)

n

9.21 (a) Show C = { f : {−1, 1}n → {−1, 1} | I[ f ] ≤ O(



log n)} is learnable from
(Hint: Theo-

queries to any constant error ≤ > 0 in time poly(n).
rem 9.28.)



(b) Show C = {monotone f : {−1, 1}n → {−1, 1} | I[ f ] ≤ O(

log n)} is learn-
able from random examples to any constant error ≤ > 0 in time poly(n).
(c) Show that C = {monotone f : {−1, 1}n → {−1, 1} | DTsize( f ) ≤ poly(n)}
is learnable from random examples to any constant error ≤ > 0 in
time poly(n). (Hint: the OS Inequality and Exercise 8.43.)

9.22 Deduce the following generalization of the (2, q)-Hypercontractivity The-
orem: Let f : {−1, 1}n → , q ≥ 2, and assume 0 ≤ ρ ≤ 1 satises ρλ ≤
1/

q − 1 for some 0 ≤ λ ≤ 1. Then



(Hint: Show ‖Tρ f ‖2

q ≤

‖Tρ f ‖q ≤ ‖Tρ f ‖1−λ


‖ f ‖λ
2 .
S(ρ2|S| f (S)2)1−λ · ( f (S)2)λ and use Hölder.)

2

9.23 Let f : {−1, 1}n → [−1, 1], let 0 ≤ ≤ ≤ 1, and assume q ≥ 2 + 2≤. Show that

‖T1−≤ f ‖q

q ≤ ‖T 1p

1+2≤

f ‖q

q ≤ (‖ f ‖2

2)1+≤.

Copyright © Ryan O’Donnell, 2014, 2015, 2016, 2017, 2018, 2019, 2020, 2021.



<!-- pdf-page: 274 -->
274

9. Basics of hypercontractivity

9.24 Recall the Gaussian quadrant probability Λρ(µ) dened in Exercise 5.32
by Λρ(µ) = Pr[z1 > t, z2 > t], where z1, z2 are standard Gaussians with
correlation E[z1 z2] = ρ and t is dened by Φ(t) = µ. The goal of this
exercise is to show that for xed 0 < ρ < 1 we have the estimate

Λρ(µ) = Θ(µ

2
1+ρ )

(9.16)

as µ → 0. In light of Exercise 5.32, this will show that the Small-Set
Expansion Theorem for the ρ-stable hypercube graph is essentially sharp
due to the example of Hamming balls of volume µ.
(a) First let’s do an imprecise “heuristic” calculation. We have Pr[z1 >
t] = Pr[z1 ≥ t] = µ by denition. Conditioned on a Gaussian being
at least t it is unlikely to be much more than t, so let’s just pretend
1 − ρ2 y,
that z1 = t. Then the conditional distribution of z2 is ρt +
where y ∼ N(0, 1) is an independent Gaussian. Using the fact that
Φ(u) ∼ φ(u)/u as u → ∞, deduce that Pr[z2 > t | z1 = t] = Θ(µ
“hence” (9.16) holds.

1−ρ
1+ρ ) and



(b) Let’s now be rigorous. Recall that we are treating 0 < ρ < 1 as xed
and letting µ → 0 (hence t → ∞). Let φρ(z1, z2) denote the joint pdf of
z1, z2 so that

Λρ(µ) =

∫∞

∫∞

t

t

φρ(z1, z2) dz1 dz2.

Derive the following similar-looking integral:

∫∞

∫∞

t

t

(z2 −ρz1)(z1 −ρt)φρ(z1, z2) dz1 dz2 =

(1 − ρ2)3/2
2π



exp

−

)

2
1 + ρ

t2
2

(9.17)

and show that the right-hand side is Θ(µ

2
1+ρ ).

(c) Show that



Pr

z1 > t−1
ρ



∫∞

=

t−1
ρ

φ(z1) dz1 = Θ(µ

1
ρ2 ),

and that this is asymptotically smaller than Θ(µ

2
1+ρ ).

(d) Deduce (9.16).

(Hint: Try to arrange that the extraneous factors

(z2 − ρz1), (z1 − ρt) in (9.17) are both at least 1.)

9.25 Let f : {−1, 1}n → {−1, 1}, let J ⊆ [n], and write J = [n] \ J. Dene the

coalitional inuence of J on f to be

˜InfJ[ f ] = Pr

[ f J|z is not constant].

z∼{−1,1}J

Copyright © Ryan O’Donnell, 2014, 2015, 2016, 2017, 2018, 2019, 2020, 2021.



<!-- pdf-page: 275 -->
9.7. Exercises and notes

275

Furthermore, for b ∈ {−1, +1} dene the coalitional inuence toward b of J
on f to be

˜Inf

b
J[ f ] = Pr

z∼{−1,1}J

[ f J|z can be made b] − Pr[ f = b]

= Pr

[ f J|z 6≡ −b] − Pr[ f = b].

z∼{−1,1}J

For brevity, we’ll sometimes write ˜Inf
(a) Show that for coalitions of size 1 we have Infi[ f ] = ˜Inf{i}[ f ] = 2˜Inf
±
(b) Show that 0 ≤ ˜Inf
J [ f ] ≤ 1.
+
(c) Show that ˜InfJ[ f ] = ˜Inf
J [ f ] + ˜Inf
(d) Show that if f is monotone, then

±
J [ f ] rather than ˜Inf

±1
J [ f ].

−
J [ f ].

±
{i}[ f ].

˜Inf

b
J[ f ] = Pr[ f

J|(b,...,b)

= b] − Pr[ f = b].

p

p

(e) Show that ˜InfJ[χ[n]] = 1 for all J 6= ;.
(f ) Supposing we write t = |J|/

±
J [Majn] = Φ(t) − 1

n, show that ˜Inf

2 ± o(1)
and hence ˜InfJ[Majn] = 2Φ(t) − 1 ± o(1). Thus ˜InfJ[Majn] = o(1) if
|J| = o(
n). (Hint: Central
Limit Theorem.)
(g) Show that max{˜Inf

n) and ˜InfJ[Majn] = 1 − o(1) if |J| = ω(

n ). On the
other hand, show that max{˜Inf
n ). De-
duce that for some positive constant c we have max{˜InfJ[Tribesn] :
|J| ≤ cn/ log n} ≤ .51. (Hint: Refer to Proposition 4.12.)

[Tribesn] : |J| ≤ log n} = 1/2 + Θ( log n

[Tribesn] : |J| ≤ k} ≤ k · O( log n

False
J

True
J

p

9.26 Show that the exponential dependence on I[ f ] in Friedgut’s Junta Theo-

rem is necessary. (Hint: Exercise 4.15.)

9.27 Let f : {−1, 1}n → {−1, 1} be a monotone function with Var[ f ] ≥ δ > 0, and

let 0 < ≤ < 1/2 be given.
(a) Improve Proposition 9.27 as follows: Show that there exists J ⊆ [n]
with |J| ≤ O(log 1
(Hint: How
≤δ
many bribes are required to move f ’s mean outside the interval [1 −
2η, 1 − η]?)

log n such that E[ f

] ≥ 1 − ≤.

) · n

J|(1,...,1)

(b) Show that there exists J ⊆ [n] with |J| ≤ O(log 1
≤δ

log n such that
˜InfJ[ f ] ≥ 1 − ≤. (Hint: Use Exercise 9.25(d) and take the union of two
inuential sets.)

) · n

9.28 Let f : {−1, 1}n → {−1, 1}.

(a) Let f ∗ : {−1, 1}n → {−1, 1} be the “monotonization” of f as dened in
b
J[ f ] for all J ⊆ [n] and b ∈

b
J[ f ∗] ≤ ˜Inf
Exercise 2.52. Show that ˜Inf
{−1, 1}, and hence also ˜InfJ[ f ∗] ≤ ˜InfJ[ f ].

Copyright © Ryan O’Donnell, 2014, 2015, 2016, 2017, 2018, 2019, 2020, 2021.



<!-- pdf-page: 276 -->
276

9. Basics of hypercontractivity

(b) Let Var[ f ] ≥ δ > 0 and let 0 < ≤ < 1/2 be given. Show that there
log n such that ˜InfJ[ f ] ≥ 1 − ≤. (Hint:

exists J ⊆ [n] with |J| ≤ O(log 1
≤δ
Combine part (a) with Exercise 9.27(b).)

) · n

9.29 Establish the general-variance case of the KKL Edge-Isoperimetric Theo-

rem. (Hint: You’ll need to replace (9.15) with

∑

3

(1/3)|S| f (S)2 ≥ 3 Var[ f ] · 3−I[ f ]/ Var[ f ].

|S|≥1

Use the same convexity argument, but applied to the random variable S
that takes on each outcome ; 6= S ⊆ [n] with probability f (S)2/ Var[ f ].)

9.30 The goal of this exercise is to attain the best known constant factor in the

statement of the KKL Theorem.
(a) By using Corollary 9.25 in place of Corollary 9.12, obtain the follow-
ing generalization of the KKL Edge-Isoperimetric Theorem: For any
(nonconstant) f : {−1, 1}n → {−1, 1} and 0 < δ < 1,
I[ f ]







MaxInf[ f ] ≥

 1
δ

1+δ
1−δ

 1
δ ·

1
I[ f ]

 1
δ

1−δ
1+δ

,

where I[ f ] denotes I[ f ]/ Var[ f ]. (Hint: Write ρ = 1−δ
1+δ
for any constant C > e2 we have

.) Deduce that

MaxInf[ f ] ≥ Ω(C−I[ f ]).
(b) More carefully, show that by taking δ = 1

2I[ f ]1/3

we can achieve

MaxInf[ f ] ≥ exp(−2I[ f ]) · e2 ·

2I[ f ]1/3



1
I[ f ]

· exp(− 1
4

I[ f ]1/3).

(Hint: Establish

1−δ
1+δ
(c) By distinguishing whether or not I[ f ] ≥ 1



 1
δ ≥ exp(−2 − δ2) for 0 < δ ≤ 1/2.)



2 (ln n −

following form of the KKL Theorem: For any f : {−1, 1}n → {−1, 1},

log n), establish the

MaxInf[ f ] ≥ 1

2 Var[ f ] ·

ln n
n

(1 − on(1)).

9.31 Establish the claim in Remark 9.29.
9.32 Show that if f : {−1, 1}n → {−1, 1} is nonconstant, then there exists S ⊆ [n]
with 0 < |S| ≤ O(I[ f ]/ Var[ f ]) such that f (S)2 ≥ exp(−O(I[ f ]2/ Var[ f ]2)).
(Hint: By mimicking Corollary 9.32’s proof you should be able to establish
the lower bound Ω(Var[ f ]) · exp(−O(I[ f ]2/ Var[ f ]2)). To show that this
quantity is also exp(−O(I[ f ]2/ Var[ f ]2)), use Theorem 2.39.)

9.33 Let f : {−1, 1}n → {−1, 1} be a nonconstant monotone function. Improve
on Corollary 9.32 by showing that there exists S 6= ; satisfying f (S)2 ≥
exp(−O(I[ f ]/ Var[ f ])). (Hint: You can even get |S| ≤ 1; use the KKL Edge-
Isoperimetric Theorem and Proposition 2.21.)

9.34 Let f : {−1, 1}n → . Prove that ‖ f ‖4 ≤ sparsity( f )1/4‖ f ‖2.

Copyright © Ryan O’Donnell, 2014, 2015, 2016, 2017, 2018, 2019, 2020, 2021.



<!-- pdf-page: 277 -->
9.7. Exercises and notes

277

9.35 Let q = 2r be a positive even integer, let ρ = 1/

q − 1, and let f1, . . . , f r :
{−1, 1}n → . Generalize the (2, q)-Hypercontractivity Theorem by show-
ing that





E

r∏

i=1



(Tρ f i)2

≤

r∏

i=1

E[ f 2
i ].

(Hint: Hölder’s inequality.)

9.36 In this exercise you will give a simpler, stronger version of Theorem 9.17

under the assumption that q = 2r is a positive even integer.
(a) Using the idea of Proposition 9.16, show that if x is a uniformly
random ±1 bit then x is (2, q, ρ)-hypercontractive if and only if ρ ≤
1/

q − 1.



(b) Show the same statement for any random variable x satisfying E[x2] =

1 and

E[x2 j−1
i

] = 0, E[x2 j
i

] ≤ (2r − 1) j



r
j
2r
2 j



for all integers 1 ≤ j ≤ r.

(c) Show that none of the even moment conditions in part (b) can be

relaxed.

9.37 Let q = 2r be a positive even integer and let f : {−1, 1}n → be homoge-
neous of degree k ≥ 1 (i.e., f = f =k). The goal of this problem is to improve
slightly on the generalized Bonami Lemma, Theorem 9.21.
(a) Show that

∑

E[ f q] =

f (S1) · · · f (Sq) ≤

∑

| f (S1)| · · · | f (Sq)|,

(9.18)

where the sum is over all tuples S1, . . . , Sk satisfying S14 · · · 4Sq = ;.
(b) Let G denote the complete q-partite graph over vertex sets V1, . . . , Vq,
each of cardinality k. Let M denote the set of all perfect matchings
in G. Show that the right-hand side of (9.18) is equal to

∑

∑

| f (T1(M, `))| · · · | f (Tq(M, `))|,

(9.19)

1
(k!)q

M∈M

`:M→[n]


where T j(M, `) denotes
(c) Show that (9.19) is equal to

{`(e) : e ∈ M, e ∩ Vj 6= ;}.

1
(rk)! · (k!)q

∑

n∑

n∑

n∑

· · ·

| f (U1(M, i1, . . . , i rk))| · · · | f (Uq(M, i1, . . . , i rk))|,

M∈M

i1=1

i2=1

i rk=1

(9.20)
where M is the set of ordered perfect matchings of G, and now
U j(M, i1, . . . , i rk) denotes

{i t : M(t) ∩ Vj 6= ;}.



Copyright © Ryan O’Donnell, 2014, 2015, 2016, 2017, 2018, 2019, 2020, 2021.



<!-- pdf-page: 278 -->
278

9. Basics of hypercontractivity

(d) Show that for any M ∈ M we have

n∑

n∑

n∑

· · ·

i1=1

i2=1

i rk=1

| f (U1(M, i1, . . . , i rk))| · · · | f (Uq(M, i1, . . . , i rk))|

(

≤

n∑

j1,..., jk=1

r

f ({ j1, . . . , jk})2

(Hint: Use Cauchy–Schwarz rk times.)

(e) Deduce that ‖ f ‖q

q ≤

1

(rk)!·(k!)q · |M | · (k!)r‖ f ‖2r
|M |1/q
p

‖ f ‖q ≤

‖ f ‖2.

k!

2 and hence

9.38 The goal of this problem is to estimate |M | from Exercise 9.37 so as to

give a concrete improvement on Theorem 9.21.
(a) Show that for q = 4, k = 2 we have |M | = 60.
(b) Show that |M | ≤ (qk − 1)!!. (Hint: Show that (qk − 1)!! is the number
of perfect matchings in the complete graph on qk vertices.) Deduce
‖ f ‖q ≤

qk‖ f ‖2.

p

(c) Show that |M | ≤ ( 2r−1

r

)rk(rk)!2, and thereby deduce

‖ f ‖q ≤ Cq,k ·



k

q − 1

‖ f ‖2,

1/q



(rk)!
k!r rrk

where Cq,k =
. (Hint: Suppose that the rst t edges of the
perfect matching have been chosen; show that there are ( 2r−1
)(rk− t)2
choices for the next edge. The worst case is if the vertices used up so
far are spread equally among the q parts.)

r

(d) Give a simple proof that Cq,k ≤ 1, thereby obtaining Theorem 9.21.
(e) Show that in fact Cq,k = Θ(1) · k−1/4+1/(2q). (Hint: Stirling’s Formula.)
(f ) Can you obtain the improved estimate

|M |1/q
p

k!

= Θq(1) · k−1/4 ·



q − 1

k

?

(Hint: First exactly count – then estimate – the number of perfect
matchings with exactly e i j edges between parts i and j. Then sum
your estimate over a range of the most likely values for e i j.)

Notes. The history of the Hypercontractivity Theorem is complicated. Its
earliest roots are in the work of Paley [Pal32] from 1932; he showed that for
1 < p < ∞ there are constants 0 < c p < C p < ∞ such that c p‖S f ‖p ≤ ‖ f ‖p ≤
n
C p‖S f ‖p holds for any f : {−1, 1}n → . Here S f =
t=1(dt f )2 is the
f (S) χS is the martingale differ-
“square function” of f , and dt f =
ence sequence for f dened in Exercise 8.17. The main task in Paley’s work
is to prove the statement when p is an even integer; other values of p follow

S:max(S)=t

n

t=1



Copyright © Ryan O’Donnell, 2014, 2015, 2016, 2017, 2018, 2019, 2020, 2021.



<!-- pdf-page: 279 -->
9.7. Exercises and notes

279

by the Riesz(–Thorin) interpolation theorem. Using this result, Paley showed
the following hypercontractivity result: If f : {−1, 1}n → is homogeneous of
degree 2, then c′
p‖ f ‖2 for any p ∈ +. Some extensions of
Paley’s work are in [Wat64].

p‖ f ‖2 ≤ ‖ f ‖p ≤ C′

p

In 1968 Bonami [Bon68] stated the following variant of Theorem 9.21:
If f : {−1, 1}n → is homogeneous of degree k, then for all q ≥ 2, ‖ f ‖q ≤
ck
q‖ f ‖2, where the constant ck may be taken to be 1 if q is an even integer.
She remarks that this theorem can be deduced from Paley’s result but with a
much worse (exponential) dependence on q. The proof she gives is combinato-
rial and actually only treats the case k = 2 and q an even integer; it is similar
to Exercise 9.37.

Independently in 1969, Kiener [Kie69] published his Ph.D. thesis, which
extended Paley’s hypercontractivity result as follows: If f : {−1, 1}n → is
homogeneous of degree k, then c p,k‖ f ‖2 ≤ ‖ f ‖p ≤ C p,k‖ f ‖2 for any p ∈ +.
The proof is an induction on k, and again the bulk of the work is the case of
even integer p. Kiener also gave a long combinatorial proof showing that if
f : {−1, 1}n → is homogeneous of degree 2, then E[ f 4] ≤ 51 E[ f 2]2. (Exer-
cise 9.38(a) improves this 51 to 15.)

Also independently in 1969, Schreiber [Sch69] considered multilinear
polynomials f over a general orthonormal sequence x1, . . . , xn of centered real
(or complex) random variables. He showed that if f has degree at most k,
then for any even integer q ≥ 4 it holds that ‖ f ‖q ≤ C‖ f ‖2, where C depends
only on k, q, and the q-norms of the xi’s. Again, the proof is very similar to
Exercise 9.37; Schreiber does not estimate his analogue of |M | but merely
notes that it’s nite. Schreiber was interested mainly in the case that the xi’s
are Gaussian; indeed, his 1969 work [Sch69] is a generalization of his earlier
work [Sch67] specic to the Gaussian case.

In 1970, Bonami published her Ph.D. thesis [Bon70], which contains the
full Hypercontractivity Theorem as stated at the beginning of the chapter. Her
proof follows the standard template seen in essentially all proofs of hypercon-
tractivity: rst an elementary proof for the case n = 1 and then an induction
to extend to general n. She also gives the sharper combinatorial result appear-
ing in Exercises 9.37 and 9.38(c). (The stronger bound from Exercise 9.38(f )
is due to Janson [Jan97, Remark 5.20].) As in Corollary 9.6, Bonami notes
that her combinatorial proof can be extended to a general sequence of sym-
metric orthonormal random variables, at the expense of including factors of
‖xi‖q into the bound. She points out that this includes the Gaussian case
independently studied by Schreiber.

Bonami’s work was published in French, and it remained unknown to
most English-language mathematicians for about a decade. In the late 1960s
and early 1970s, researchers in quantum eld theory developed the theory

Copyright © Ryan O’Donnell, 2014, 2015, 2016, 2017, 2018, 2019, 2020, 2021.



<!-- pdf-page: 280 -->
280

9. Basics of hypercontractivity

p

1/

p

q−1

of hypercontractivity for the Gaussian analogue of Tρ, namely, the Ornstein–
Uhlenbeck operator Uρ. This is now recognized as essentially being a special
case of hypercontractivity for bits, in light of the fact that x1+···+xn
tends
to a Gaussian as n → ∞ by the CLT (see Chapter 11.1). We summarize
here some of the work in this setting. In 1966 Nelson [Nel66] showed that
f ‖q ≤ Cq‖ f ‖2 for all q ≥ 2. Glimm [Gli68] gave the alternative result
‖U
f ‖q ≤ ‖ f ‖2.
that for each q ≥ 2 there is a sufciently small ρ q > 0 such that ‖Uρ q
Segal [Seg70] observed that hypercontractive results can be proved by induc-
tion on the dimension n. In 1973 Nelson [Nel73] gave the full Hypercon-
tractivity Theorem in the Gaussian setting: ‖Up
f ‖q ≤ ‖ f ‖p for all
1 ≤ p < q ≤ ∞. He also proved the combinatorial Exercise 9.37. The equiva-
lence to the Two-Function Hypercontractivity Theorem is from the work of
Neveu [Nev76].

(p−1)/(q−1)

n

In 1975 Gross [Gro75] introduced the notion of Log-Sobolev Inequalities
(see Exercise 10.23) and showed how to deduce hypercontractivity inequalities
from them. He established the Log-Sobolev Inequality for 1-bit functions, used
induction (citing Segal) to obtain it for n-bit functions, and then used the CLT
to transfer results to the Gaussian setting. (For some earlier results along
these lines, see the works of Federbush and Gross [Fed69, Gro72].) This gave
a new proof of Nelson’s result and also independently established Bonami’s
full Hypercontractivity Theorem. Also in 1975, Beckner [Bec75] published his
Ph.D. thesis, which proved a sharp form of the hypercontractive inequality for
purely complex ρ. (It is unfortunate that the inuential paper of Kahn, Kalai,
and Linial [KKL88] miscredited the Hypercontractivity Theorem to Beckner.)
The case of general complex ρ was subsequently treated by Weissler [Wei79],
with the sharp result being obtained by Epperson [Epp89]. Weissler [Wei80]
also appears to have been the rst to make the connection between this line
of work and Bonami’s thesis.

Independently of all this work, the (q, 2)-Hypercontractivity Theorem was
reproved (without sharp constant) in the Banach spaces community by Rosen-
thal [Ros76] in 1975, using methods similar to those of Paley and Kiener. For
additional early references, see Müller [Mül05, Chapter 1].

The term “hypercontractivity” was introduced in a work of Simon and
Høegh-Krohn [SHK72]; Denition 9.13 of a hypercontractive random vari-
able is due to Krakowiak and Szulga [KS88]. The short inductive proof
of the Bonami Lemma may have appeared rst in Mossel, O’Donnell, and
Oleszkiewicz [MOO05a]. Theorems 9.22 and 9.24 appear in Janson [Jan97].
Theorem 9.23 dates back to Pisier and Zinn and to Borell [PZ78, Bor79].
As discussed further in the notes to Chapter 10, the Small-Set Expansion
Theorem originates in the work of Ahlswede and Gács [AG76]. The Level-k
Inequalities appear in several places but can probably be fairly credited to

Copyright © Ryan O’Donnell, 2014, 2015, 2016, 2017, 2018, 2019, 2020, 2021.



<!-- pdf-page: 281 -->
9.7. Exercises and notes

281

Kahn, Kalai, and Linial [KKL88]. The optimal constants for Khintchine’s
Inequality were established by Haagerup [Haa82]; see also Nazarov and Pod-
korytov [NP00]. They always occur either when
x2
or in the limiting Gaussian case of ai ≡ 1p
n

i ai xi is just 1p
2

x1 + 1p
2

, n → ∞.



Ben-Or and Linial’s work [BL85, BL90] was motivated both by game
theory and by the Byzantine Generals problem [LSP82] from distributed
computing; the content of Exercise 9.25 is theirs. In turn it motivated the
watershed paper by Kahn, Kalai, and Linial [KKL88]. (See also the intermedi-
ate work of Chor and Geréb-Graus [CGG87].) The “KKL Edge-Isoperimetric
Theorem” (which is essentially a strengthening of the basic KKL Theorem)
was rst explicitly proved by Talagrand [Tal94] (possibly independently of
Kahn, Kalai, and Linial [KKL88]?); he also treated the p-biased case. There
is no known combinatorial proof of the KKL Theorem (i.e., one which does not
involve real-valued functions). However, several slightly different analytic
proofs are known; see Falik and Samorodnitsky [FS07], Rossignol [Ros06],
and O’Donnell and Wimmer [OW13]. The explicit lower bound on the “KKL
constant” achieved in Exercise 9.30 is the best known; it appeared rst in
Falik and Samorodnitsky [FS07]. It is still a factor of 2 away from the best
known upper bound, achieved by the tribes function.

Friedgut’s Junta Theorem dates from 1998 [Fri98]. The observation that
its junta size can be improved for functions which have Wk[ f ] ≤ ≤ for k ø I[ f ]/≤
was independently made by Li-Yang Tan in 2011; so was the consequence
Corollary 9.31 and its extension to constant-degree PTFs. A stronger result
than Corollary 9.31 is known: Diakonikolas and Servedio [DS09] showed
that every LTF is ≤-close to a I[ f ]2poly(1/≤)-junta. As for Corollary 9.30, it’s
incomparable with a result from Gopalan, Meka, and Reingold [GMR12],
which shows that every width-w DNF is ≤-close to a (w log(1/≤))O(w)-junta.

Exercise 9.3 was suggested to the author by Krzysztof Oleszkiewicz.
Exercise 9.12 is from Gopalan et al. [GOWZ10]. Exercise 9.21 appears in
O’Donnell and Servedio [OS07]; Exercise 9.22 appears in O’Donnell and Wu
[OW09]. The estimate in Exercise 9.24 is from de Klerk, Pasechnik, and
Warners [dKPW04] (see also works of Rinott and Rotar’ [RR01] and Khot
et al. [KKMO07]). Exercises 9.27 and 9.28 are due to Kahn, Kalai, and
Linial [KKL88]. Exercise 9.34 was suggested to the author by John Wright.
Exercise 9.36 appears in Kauers et al. [KOTZ16].

Copyright © Ryan O’Donnell, 2014, 2015, 2016, 2017, 2018, 2019, 2020, 2021.



<!-- pdf-page: 282 -->

