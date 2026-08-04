<!-- generated-by: proofmatch local extraction -->
<!-- source-pdf-sha256: abed77da6b7a75ec4d93cc73615f95b277fa31571f1e9c7c831aea094e4909e1 -->
<!-- extractor: pdfminer.six v20260107 -->

<!-- pdf-page: 1 -->
IEEE  TRANSACTIONS  ON  INFORMATION 

THEORY,  VOL. 

IT-%,  NO.  2,  MARCH  1977 

157 

New Upper Bounds on the Rate of a Code via the Delsarte- 

MacWiIliams Inequalities 

ROBERT J. McELIECE, MEMBER, 

IEEE,  EUGENE R. RODEMICH, HOWARD RUMSEY, JR., 
AND  LLOYD R. WELCH 

Abstract-With 

as  a 
the  Delsarte-MacWilliams 
starting  point,  an  upper  bound  is obtained  on  the  rate  of  a binary 
code  as a function  of  its  minimum  distance.  This  upper  bound  is 
less than  Levenshtein’s  bound,  and  so also Elias’s. 
asymptotically 

inequalities 

I.  INTRODUCTION 

L ET  V,  DENOTE  the  set  of  all  2n  binary  n- 

tuples, and, for x,y  E  V,,  denote by  j/x -  yI/ the 
Hamming distance1 between x and y, i.e., the number of 
components in which x  and y  differ. A subset C =  {xi, 
* . . ,x~]  g  V,  is called a code of length n; the xi are called 
codewords;  the  minimum  distance  of  C  is  d,i,(C) 
= 
mini /I Xi -  Xj  I] : i  #  j);  and the code’s rate is R(C) = n-l 
logs M.  We are interested in the relationship between a 
code’s rate and its minimum distance, and in this paper we 
shall obtain asymptotic upper bounds on R(C)  in terms of 
dmin(C)* 

To describe our results compactly, we need more nota- 
tion. First, we define M(n,d) 
to be the largest possible 
number of codewords in a code of lengthn and minimum 
distance at least d. Next, define R(n,d)  =  n-l 
as the rate of the best code of length n and minimum dis- 
tance at least d. Finally, for each real number 0 I  6 _< 1, 
define 

logs M(n,d) 

t 
“(Xl 

1 

H 

x- 

I 

Fig.  1.  The function  g(x). 

Hz(x)  =  --x logs X -  (1 -  X) logs (1 -  X). 

(1.3) 

The function g(r) is monotonically increasing and concave 
on [O,l]. The lower bound in  (1.2), which is usually ex- 
pressed as 1 -  HZ(~), is due to Gilbert; the upper bound, 
to Elias. The Gilbert and Elias bounds are plotted in Fig. 
2, the unknown function R(6) lying somewhere between 
them. Gilbert’s lower bound is still  the best one, but re- 
cently Sidelnikov [6] and Levenshtein [5] obtained new 
upper bounds on R(6) which are strictly less than Elias’, 
for all 0 <  6 <  l/2. However, the numerical improvement 
over the Elias bound is not large. (See Table I.) 

In this paper, we will obtain a new upper bound to R(6), 
for 0 < 6 < Ys, which, so far as we know, is strictly less than 
any other bound. It  is 

R(6)  = sup lim  R(n,d,), 

n-m 

(1.1) 

R(6)  _<  min  1 + g(u2)  -  g(u2  +  26~ +  26). 

(1.4) 

o_cu51-26 

where the supremum in (1.1) is taken over all sequences 
(d,)  for which d,ln  -  6. 

It  is known (see, e.g., [2, ch. 131) that R(0)  = 1, and R(6) 
= 0 for i’s I  6 5  1, but R (6) is unknown for 0 < 6 < $$. Until 
fairly recently, the best upper and lower bounds for R (6) 
in this range were 

1 -  g(46(1 -  6)) 5 R(6)  5  1 -  g(26), 

(1.2) 

where in (1.2) the function g(x), plotted in Fig. 1, is defined 
for 0 I  x 5  1 by 

g(x) = Hs((1 -  fi)/2), 

Manuscript  received April  19, 1976. This  paper presents the  results 
of  one phase of  research carried out  at  the  Jet Propulsion  Laboratory, 
California  Institute  of  Technology,  under  Contract  No.  NAS  7-100, 
sponsored by the  National  Aeronautics and Space Administration. 

R. J. McEliece, E. R. Rodemich, and H. Rumsey are with  the Jet Pro- 

pulsion  Laboratory,  Pasadena, CA 91103. 

L.  R. Welch is with  the University of Southern California, Los Angeles, 

CA 90007. 

1 For a single vector x,  /1x1/ =  11x -  O// is the  Hamming  weight  of x. 

Note that, if we evaluate the expression 1 
+ 26~ + 26) at u =  1 -  26, we obtain g((1 
(1.4) implies the bound 

f  gb2) -  g(u2 
-  28)2), and so 

R(6)  5  g((1 -  26)2). 

(1.5) 

Surprisingly, the bound (1.4) is actually equal to (1.5) for 
0.273 1  6 I  1/2 and so the minimization over u improves 
(1.5) only for relatively small values of 6. Also note that for 
u = 0, (1.4) yields the Elias bound; it is easy to check that 
the derivative ofg(u2) -  g(u2 +  26~ +  26) at u = 0 is neg- 
ative, so the bound (1.4) is always strictly less than the 
Elias bound. (However, the bound (1.5) is larger than the 
Elias bound for 6 < 0.150, and even larger than the obsolete 
Hamming bound 1 -  H2(6/2) for 6 < 0.114.) The bounds 
(1.4), (1.5), and Levenshtein’s bound are plotted in Fig. 3, 
and tabulated in Table I.2 

11 One of the referees has invited  us to make a conjecture about the re- 
lationship  between our bound N(6), Gilbert’s  bound G(6), and the actual 
value R(6), so here goes. Conjecture: C(S) <R(6)  <N(6),  for all 0 <  6 < 
l/2.  (See also footnotes 4 and 7.) 

Authorized licensed use limited to: Univ of Calif Berkeley. Downloaded on August 03,2026 at 11:10:52 UTC from IEEE Xplore.  Restrictions apply. 



<!-- pdf-page: 2 -->
158 

IFZE  TRANSACTIONS ON  INFORMATION  THEORY, MARCH  1977 

S- 

Fig.  2.  Elias and Gilbert  bounds. 

TASLE  I 
BOUNDSON R(6) 
L  =  LEVENSHTEIN,E  =  EIJAS,  G  =  GII.HEW 

f- 

- 

6 

.oo 

.02 
.04 
.06 
. 08 
.lO 
.12 
.14 
.16 
.18 
.20 
.22 
.24 
.26 
.2a 
.30 
.32 
.34 
.36 
.3a 
.40 
.42 
.44 
.46 
.4a 
.50 

Upper Bounds 

x 

1.000 
.943 
.886 
.831 
.776 
.722 

.669 
,617 
.567 
.517 
.469 
.422 
.377 
.333 
.291 
.250 
.212 
.175 
.141 
.llO 
.081 
,056 
.035 
.017 
.005 
,000 

1.4 

1.000 
.918 
.a54 
.797 
,744 
.693 
.644 
.597 
.551 
,505 
.461 
,418 
,375 
.333 
.291 
.250 
.212 
.175 
,141 
.llO 
,081 
.056 
.035 
.017 
,005 
,000 

Lower 
Bounds 

L 

E 

G 

1.000 
.919 
.856 
.8oi 
.749 
.701 
.655 
.612 
.570 
.p 
,490 
.451 
.414 
.377 
.342 
.307 
.272 
.23a 
,205 
.172 
.140 
,107 
.076 
.045 
,018 
.ooo 

1.000 
.919 
.856 
.801 
.75o 

.7w 
.656 
.613 
.571 
.531 
.492 
.454 
,417 
.3a1 
.346 
.312 
.27a 
.245 
.213 
.181 
,150 
.119 
.oaa 
.059 
.029 
. 000 

l.QOO 
.a59 
.758 
,673 
,598 
.531 
.471 
,416 
.366 
,320 
.278 
.240 
.205 
.173 
.145 
.119 
.096 
.075 
.057 
.042 
.029 
.019 
.OlO 
.005 
,001 
. 000 

Here is the plan of the rest of the paper. In Section II,  Elias bound and (1.5): , so we regard (1.5) as the most sig- 

we outline our proofs of (1.4) and (1.5). In Section III,  we  nificant contribution of this paper, 
will  prove (1.5); and in Section IV, we will  prove (1.4). As 
we have pointed out, (1.4) contains (1.5) as a special case, 
and so Section III  is not strictly necessary to our’exposition. 
However, we have included a separate proof of (1.5) in 
order to introduce the reader to the rather intricate ideas 
Let C = (xi,*..,  XM) be a code of length n with  11 xA1 - 
necessary for the full proof of (1.4). In any case, the general  xv11 1 d if CL f  u. For each i  = O,l, - * . ,n, define ai to be the 
bound (1.4) is not much better than the minimum of the  average number of codewords at distance i  from a given 

AND LINEAR  PROGRAMMING BOUNDS 

II.  THE  DELSARTE-MACWILLIAMS 

INEQUALITIES 

Authorized licensed use limited to: Univ of Calif Berkeley. Downloaded on August 03,2026 at 11:10:52 UTC from IEEE Xplore.  Restrictions apply. 



<!-- pdf-page: 3 -->
MC  ELIECE  et al.:  NEW  UPPER  BOUNDS 

159 

.9- 

.8 - 

.7 - 

.6  - 

t 
R& 

- 

.4  - 

.3  - 

.2  - 

.l- 

Fig. 3.  Bounds (1.4) and (1.5) versus Levenshtein’s  bound. 

codeword3, i.e., 

define, for 0 _< 6 I  1, 

The vector a =  (ao,al, . . . ,a,) is called the distance dis- 
tribution  of the code; it  is immediate that 

a0 = 1 

al=a2=...=q+.1=o 

uo+al+~~.+a,=M. 

(2.2) 

Now let Kj  (i) be the coefficient of yj  in the polynomial (1 
-  ~)~(l + Y)“-~. The Delsarte-MacWilliams inequalities 
are 

e  uiKj(i)  10, 
i=o 

j  = O,l, *. * ,n. 

(2.3) 

(A simple proof of these inequalities is given in  [a]. The 
numbers Kj(i)  are discussed at length in Appendix A.) 

Now let us denote by M~p(n,d)  the value of the following 

linear program 

maximize:  a0 + a1 + * * * + a,, 

subject to:  uo = 1, 

(2.4a) 

RLP(Q 

-7- 

=  SUP ,‘+ll; 

log2 MLPh&), 

(2.5) 

where the supremum is the same as in (1.1). Clearly R (6) 
5  RLP(~). In  Section III,  we will  show that,4 for 0 <  6 
- 
<  Yi 

RLP(@ 

5  &do 

-  m2), 

(2.6) 

and this will  establish (1.5). 

We now describe how the tighter bound (1.4) arises. If 
B  is a subset of  V,,  denote by M~(n,d) 
the maximum 
number of codewords x1, . . . ,xM which can be chosen from 
B such that  Ilx, -  x,/I > d, for all P #  u. Then it  is well- 
known that 

M(n,d) 

I  5  MB(n,d). 

(2.7) 

(A proof of (2.7) may be found in [5, corollary 1 to lemma 
31 or [3, theorem 3.71. The result is variously attributed to 
Elias or Bassalygo.) 

If in (2.7) we take for B the set of all 

vectors of weight 

w for some fixed w E  (O,l, * . - ,Lnl2J, and denote the cor- 
responding M~(n,d)  by M(n,d,w),  (2.7) becomes 

a1 = . . . = Q-1  = 0 

CLi 1  0, 

i  = d,d +  1, * * * ,n, 

2  uiKj(i)  >  0, 
i=o 

j  = O,l, s s s ,n. 

(2.4b) 

M(n,d) 

(2.4~) 

2” ~ 
n 
0 W 
(2.4d)  Now if we define R(G,cr) by 

I 

M(n,d,w). 

(2.8) 

7 
R(6,a)  =  sup hm ‘log2  M(n,d,,w,), 
njm  n 

(2.9) 

Then, because of (2.2) and (2.3), it  follows that M(n,d)  5 
MLp(n,d);  this is the linear  programming  bound.  Also, 

3 In  (2.1), and elsewhere, we use the notation  (XI  to denote the number 

of elements in  the  finite  set X. 

4 We do not  believe this  bound to  be tight  for  any 0 <  6 <  l/2. 
R To obtain  (2.10), we have used the fact that  l/n  loge (I,,)  =  Hz(n)  + 
o(n),  for  01 I  YJ, a result  which  can be deduced from  Stirling’s  approxi- 
mation  to  the factorial. 

Authorized licensed use limited to: Univ of Calif Berkeley. Downloaded on August 03,2026 at 11:10:52 UTC from IEEE Xplore.  Restrictions apply. 



<!-- pdf-page: 4 -->
160 

IEEE  TRANSACTIONS ON  INFORMATION  THEORY, MARCH  1977 

TABLE  II 
BOUNDS ON R(6,a)  FOR 6 =  0.48(6* =  0.40) 

CL 

.40 

.41 

.42 

.43 

.44 

.45 

.46 

.47 

.48 

.49 

.50 

Levenshtein 

')  00000 

0.00117 

0.00361 

0.00657 

0.00965 

0.01240 

0.01457 

0.01612 

0.01721 

0.01764 

0.01764 

(2.16) 

0.00000 

0.00027 

O.OOOR5 

0.00158 

0.00236 

0.00311 

0.00378 

0.00433 

0.00475 

0.00501 

0.00509 

Gilbert 

(lower  bound) 

0.00000 

0.00004 

0.00016 

0.00031 

0.00049 

0.00066 

0.00082 

0.00096 

0.00107 

0.00113 

0.00115 

where the supremum in (2.9) is taken over all sequences 
(d,) and (w,) for which d,/n  -  F and w,/n  -  CY, it follows 
from (1.1) and (2.8) that5 

qualities (2.3) and (2.13) appear as extremely special cases. 
The numbers Qj(i)  are defined and many of their prop- 
erties are given in Appendix B.) As before, if we denote by 
M&n,d,w) 

the value of the following linear program 

R(6) 5  1 -  H&Y)  + R(CJ,CX), 

(2.10) 

for all 0 5  a 5  i/s. 

In Section IV, we will  restrict ourselves entirely to the 
problem of obtaining a bound for M(n,d,w).  The asymp- 
totic form of this bound, when combined with (2.10), will 
yield our main result (1.4). We conclude this section with 
a  brief  description  of  our  technique for  bounding 
M(n,d,w). 

Let (xl, . . . ,x~} be a set of M  binary codewords of length 
n and weight w such that 1) x,  -  x,11 1  d, if p #  Y. For each 
i .= O,J, . . . ,w, let ai be the average number of codewords 
at distance 2i  from a given codeword6, i.e., 

ai  =  i- 

(((p,v):lIx, 

-  x,1( =  2i)(. 

(2.11) 

As before (cf. (2.2)), it  is immediate that 

a0 = 1 

ai  =  0, 

for 1 5 i  <  d/2 

a0 +  * - * +  a,  =  M, 

(2.12) 

Delsarte 13, theorem 3.31 has discovered numbers Qj (i) 
which serve the same function in this setting as the Kj(i) 
did earlier; viz., 

fJ  aiQj(i) 
i=o 

IO, 

j  = O,l, . . . ,w. 

(2.13) 

(Actually, Delsarte has established a beautiful general 
theory of “association schemes” in which the pivotal ine- 

(2.14a) 

(2.14b) 

(2.14~) 

maximize:  ao+a1+*--+a, 

subject to:  a0 = 1 

ai = 0, 

for 1 I  i  <  d/2, 

ai 1  0, 

all i, 

fJ  aiQj(i)  2  0, 
i=o 

j  = O,l, . . a ,w, 

(2.14d) 

then M(n,d,w) 

I  M&n,d,w).  Now define RLP(~,cx) by 

R&&a)  = sup lim  1 logs M&n,dn,w,), 
n-m n 

(2.15) 

where the supremum is the same as in (2.9). In Section IV, 
we will  prove that7 for fixed 6,O < 6 < ‘$2, 

RLP@,(w)  5  0,  OICX16” 

du2), 

6”  I  CY I  Ik, 

(2.16) 

where 6* = (1 -  v”i?8)/2 
and u = -6  + (a2 -  26 + 4cr(l 
-  (~))i/~. As cy varies from 6* to i/2, u increases monotoni- 
cally from 0 to 1 -  26; and since HZ(Q) = g(u2 + 26~ + 26), 
together (2.10) and (2.16) yield the bound (1.4). In  [5], 
Levenshtein has also given an upper bound on R(~,LY). The 
complexity of Levenshtein’s bound has prevented us from 
making an analytic comparison of the two, but apparently 
the bound (2.16) is superior to Levenshtein’s, at least for 
relatively large 6. For example, in Table II  we have tabu- 
lated Levenshtein’s bound, our bound (2.16), and the 
Gilbert lower bound Hz(a) -  &?~(c?/~cx) 
-  (1 -  LY) H2(6/2( 1 
-  (u)), for 6 = 0.48 and 0.40 I  cx I  0.50. 

fi Note that  since the xi  all have the same weight, the distances among 

them are necessarily even. 

7 We do not  believe the  interesting  part  of this  bound to be tight,  i.e., 

we conjecture that  R&&n) 

< g(u2),  for  0 <  6 <  l/2,6*  <  01 5  l/2. 

Authorized licensed use limited to: Univ of Calif Berkeley. Downloaded on August 03,2026 at 11:10:52 UTC from IEEE Xplore.  Restrictions apply. 



<!-- pdf-page: 5 -->
MC  ELIECE  et  al.:  NEW  UPPER  BOUNDS 

161 

(3.6) 

(3.7) 

Fig. 4.  Relationship  between Kt+l(x)  and K,(x),j  5  t. 

III.  PROOF  OF  (2.6) 

Our first result is really only a formulation of the dual 

of the linear program (2.4). 

Now define 

P(x) = -___ 

P*  (x)2 
u-x 

Theorem  1: Let (ho,Xr, . . . J,,)  be real numbers satis- 

= & 

(;)  [&+lb)Kt(a) - Kt(xKt+~(a)l 

fying 

Then, 

X0 >  0, Aj  1  0, 

j  =  1,. . . ,n 

C  AjKj(i)  5  0, 
j=O 

i  = d,d +  1, * * * ,n. 

MLP(n,d) 5 -  C  xjKj(O)* 

1  n 

X0  j=O 

(3.1) 

(3.2) 

(3.3) 

Proof: Let (as,ai, . . . ,a,) be real numbers satisfying 
the constraints (2.4) for which as -I-. . . + a,  = Mr,p(n,d), 
and let bj  =  Zr==, oiKj(i).  Then, (by (3.1) and (2.4d)) 

Xobo I  5  Ajbj  =  2  Ui  2  AjKj(i)  5  2  AjKj(O) 
j=O 

j-0 

j=O 

i=o 

(3.4) 

(by (3.2) and (2.4a,b,c)). Now by definition Kc(i) = coef- 
ficient of 1 in (1 -  ~)~(l+  Y)“-~ = 1, and so bo =  X$o ai  = 
M~&n,d). This fact, combined with (3.4), yields Theorem 
1. 

It  is known that Kj(i) 

is a polynomial of degree j  in i. 
is called a 
This polynomial, which we denote by Kj(x), 
Krawtchouk  polynomial. In the following argument, we 
shall frequently refer to results about Krawtchouk poly- 
nomials and refer the reader to Appendix A for details. At 
first,  n  and d will  be fixed integers; later, after we have 
derived the bound (3.13) on M(n,d), we will  proceed to 
asymptotic analysis. 

Let  t  be an integer, I  5  t  5  n/2,  and let a be a real 
number in the interval [O,n]. (They will be specified more 
precisely later.) Define 

P*(x)  = Kt+rb)Ktb) 

-  &b)Kt+l(a). 

According to property (A.16), 

2(a-x) 

P*(x)  = ---- 

n 
t  kio  Kk<X.)Kko 

0 

/n\ 
\k/ 

(3.5) 

. .& &(z)K/h). 
k = 0 

n 
0 k 

Now (see Appendix A) for each j,Kj(x)  has j  distinct real 
zeros in the interval (0,n). Denote by xjj’  the smallest such 
zero. Then by (A.17), x1 w’)  < xv). Let us now choose a so 
that 

X(ltfl) < a < xp. 

(3.8) 

Then since Kj  (0) =  n 
0 j 

> 0 (A.B), it follows that Kj(a)  > 

0, for j  5  t,  and Kt+l(a)  <  0. (See Fig. 4.) Hence in (3.7) 
P(X) is expressed as a sum, with nonnegative coefficients, 
of products of Krawtchouk polynomials. By (A.19), any 
product Ki(x)Kj(x)  can be expressed as a sum ZakKk(3c) 
with each Cyk > 0. We conclude that P(X) itself has an ex- 
pansion in  Krawtchouk polynomials with  nonnegative 
coefficients. 

Next, observe from (3.6) that P(X) 5 0, if n I  a. Hence 
if we assume a 5 d, it follows that P(z) 5 0 if x 1 d. Hence 
the Xj satisfy the hypotheses of 
if  P(X) =  2,”  AjKj(x), 
Theorem 1, and so MLp(n,d) 
I  P(O)&.  From (3.6), we 
have 

To compute he we use the formula (A.12) X0 =  JP(x)  dp 
and the orthogonality properties (A.ll)  and conclude 

ho = - &~Kl+~(aKtb)  SKt2(x) do 

=  -  -& 

(;)  K,(u)~Q. 

(3.10) 

Authorized licensed use limited to: Univ of Calif Berkeley. Downloaded on August 03,2026 at 11:10:52 UTC from IEEE Xplore.  Restrictions apply. 



<!-- pdf-page: 6 -->
162 

IEEE  TRANSACTIONS  ON 

INFORMATION 

THEORY,  MARCH  1977 

Combining (3.9) and (3.10), we get the following bound: 

then 

MLdn,d)  5 

n 0 (n  -  t  -  (t  +  1)Q)2 
t 

-2u(t  +  1)Q 

’ 

(4.3) 

where 

Q = Kt+~(a)/Kt(a) 
xl(t+l’  < a < XI(t) 
a  <  d. 

I 

(3.11) 

For fixed (n,d,w),  choose an integer t, 1 I  t I  w, a real 

number a in the interval (O,UI), and define 

P*(x)  = Qt+l(x)Qtb)  -  Qt(x)Qt+~(a). 

(4.4) 

BY (B14Ls 

To simplify this, choose t so that xit)  I  d and a so that Q 
= Kt+l(u)/Kt(u) 

(n  -  2t)(n  -  2t  -  1) 
= -1  (see Fig. 4.) Then (3.11) becomes  p*(x)  =  (a -  x)  - (t +  l)(w  -  t)(w’  -  t) 

M&v0 

5 

n 

(n+  1)2 

0 t  2u(t  +  1) 

(3.12) 

.~t 2  &kb)Qkb) 
, 

(4.5) 

k=O 

Pk 

(provided xit)  I  d, t  I  n/2).  Now, since a 1 xitfl’  and by 
(A.18) xy+‘)  >  1, we get 

where w’  = n -  w, and the constants ,.Lk are given by (B.l). 
Now define9 

Mdn,d) 

5  0 n 

(n  +  1)2 I 
t  2(t  +  1) 

n 

0 t (n  +  1)2  (3.13)  P(x)  = P*(x)~/(u  -  x) 

(provided xf)  I  d, t  5  n/2). 

We now proceed to  an asymptotic analysis of (3.13). 
Choose 7 so that l/2  -  d/6( 1 -  6) < 7 < ‘&, and let (d,)  and 
(t,)  be sequences of integers such that d,/n  -  6 and t,ln 
-  T. Now, according to  (A.20), G 
l/2  - 
d~(l  -  7) <  6, and so, for  sufficiently  large n,  the hy- 
potheses of (3.13) will  be satisfied. Thus 

xfn)/n  5 

- 
hm L log2 ML&d,) 
n-m  n 

=  lim  L logs  tn 

n-m  n 

(  > n 

=  H2(7), 

(3.14) 

tn  -  H2(t,).  Combining (3.14) with (2.5), 
since n-l  log2 
0 
n 

I  HZ(T) whenever l/2  -  m 

< 
we see that Rip 
7 <  l/2. Since HZ(T)  is a continuous function of  7, this 
implies Rip 
which is the promised bound (2.6). 

I  Hs(1/2 -  w) 

=  g((1 -  26)2), 

(4.6) 

(4.7) 

(n  -  2t)(n  -  2t  - 
(t  +  l)(w  -  t)(w’ 

-  t) 

‘)  pt  [Qt+l(x)Qt(u) 

= 

-  Qt(x)Qt+lb)l - ,i  Qt(x;k(u) 

k=O 

, 

Now (see Appendix B) for each j,  Qj(x) has j  distinct real 
zeros in the open interval (O,w), and if xp) denotes the least 
zero of &j(x),  xP+~)  < x-4’) (see (B.16)). If  we choose a so 
that 

(t+l) 

Xl 

< 

u 

< 

x(t) 

1  9 

(4.8) 

then since &j(O) = pj > 0 (B.lO), it follows that Q,(o) > 0 
for j  5 t  and Qt+l(u) < 0. (The situation is the same as in 
Fig. 4.) Hence in  (4.7) P(X) is expressed as a sum, with 
nonnegative coefficients, of products of Qj-polynomials. 
By  (B.17), (B.18) this implies that P(x)  =  2)‘:”  AjQj(x) 
with each Xj 1  0. Next, observe from (4.6) that P(X)  F: 0, 
if x > a, and so, if we assume a I  d/2,  it follows that P(x) 
I  0, if x  I  d/2,  and so we can apply Theorem 2 and con- 
I  P(O)/Xs. If  we further assume 
clude that MLp(n,d,w) 
that  xlt)  <  d/2  and that  a  is  chosen in  the  interval 
that Qt+l(u)/Qt(u)  = -1, then using (4.6) and 
(~~~+‘),xj’))~o 
(4.4) we calculate 

P(0)  =  i  Qua 

(;)’ 

[ n(,-‘~;-l;;;+,-l;“]2. 

(4.9) 

IV.  PROOF  OF  (2.16) 

(The techniques involved in this section are virtually 
identical to those of Section III,  and so we have omitted 
some of the computational details.) 

Our first  result is analogous to Theorem 1; its proof is 

virtually  the same, so we omit it. 

To  compute X0, we  apply  the  formula  (B.14)  ho = 
JP(x)  do(x)  to (4.6) an  use the orthogonality relations 
(B.13). The result is 

d 

(n  -  2t)(n  -  2t  -  1)  Qt(u)2 
. 

X”=pt(t+l)(w-t)(w’-t) 

(4.10) 

Theorem  2:  If  X0,X1,. . . ,X,  are real numbers satisfy- 

Combining these results and recalling that xit+l) < a, we 

ing 

Aj  >O, 

Aj  2  0, 

j  = 1,. . . ,n 

$J AjQj(i)  IO, 
j=O 

for i  >  d/2, 

(4.1) 

(4.2) 

s Throughout  this section, we will  invoke facts about the numbers Q,(i) 

which  are discussed in  detail  in  Appendix  B. 

g The  polynomial  defined  by  (4.5) may have degree >  w. We should 
really define p(n)  to he the unique polynomial  of degree at most w which 
agrees with  the right  side of  (4.5) for  n  =  O,l, . . * ,w. 

Authorized licensed use limited to: Univ of Calif Berkeley. Downloaded on August 03,2026 at 11:10:52 UTC from IEEE Xplore.  Restrictions apply. 



<!-- pdf-page: 7 -->
MCELIECE 

et  al.:  NEW  UPPER  BOUNDS 

obtain the following bound on M&n,d,w): 

MLdn,d,w)  5 

n 
t 
0 

(n2 -  (2t  -  1)n -  2t)2(w  -  t)(w’ 

-  t) 
l)(n  -  2t)(n  -  2t  +  1)’ 

xf+l)(t  +  l)(n  -  t  +  l)(n  -  2t  - 

163 

(4.11) 

provided rp)  I  d/2. 

We now proceed to an asymptotic.analysis of thebound 
(4.11). Let  (d,),  (zu,), and (t,)  be sequences of integers 
with 

d,ln  -  6 

w,/n  - 

ff 

t,ln 

-  P, 

05p<CY<y2. 

APPENDIX A 

Some Properties  of Kruwtchouk  Polynomials 

In  this  appendix  we collect  for  reference purposes several im- 
portant  properties of the Krawtchouk  polynomials Kj (X ) defined 
in  Section  II.‘0  First  recall  the  definition 

Kj(x)  = coef (1 -  ~)~(l+  y)“-“. 

(A.11 

(4.12) 

9 
From  (A.l),  it  follows  that 

Now by (B.lO), the polynomial Qtn(njwa)(~) 
is positive at 
it  is also positive at x  = 1 for suffi- 
x  = 0 and, by (B.ll), 
ciently large n.  Hence, if  it  has any zeroes in the interval 
(O,l), it must have at least two. This is, however, not pos- 
sible since by the remarks following (B.16) there must be 
an integer between any two zeroes, and so we conclude 
that 

xp  2  1, 

n sufficiently large. 

(4.13) 

This  means that  the fraction on the right  of  (4.11) is 
growing no faster than O(n6), and so the bound is domi- 

nated by the binomial coefficient 

n 
0 tn  . 

But n-l  log2  n 
0 tn 

-+ H&3),  and so, combining (4.11) with (2.15), we obtain 
the bound R~p(8,a) 5 H&3),  provided p is chosen so that 
xpn) < d,/2,  for large n. But according to (B.21) this will 
be thecase if  ((~(1 -  LY) -  p(l  -  p)) . (1 -  2 d/p(l  -  p))l(l 
-  2p)2 I  6/2. Summarizing, 

RLP(~) 

5  H2(P), 

(4.14a) 

if 

K,(x)  = #” 

(-l)k 

(i) 

(II:>. 

(A.21 

If  in  (A.1) we write  (1 -  y)”  =  (1 +  y  -  2~)”  and expand, we get 
the  alternative  formula 

K,(x) = kio (-2jk  (;II) (5 I,“>. 

(A.3) 

From  (A.2) or (A.3), it  follows that  Kj(r) 
j  in  x,  and it  is easily verified  that 

is a polynomial  of degree 

Kohl  =  1, 

Kl(x)  =  -2x  +  n, 

Kz(x) =  2x2 -  2xn +  (n2 -  n)/2, 

K.(x)  =  oj 
I! 

J 

xj  +  lower degree terms, 

(A.4) 

(A.5) 

L4.6) 

(A.7) 

(A.8) 

K,(l)  =  - 

n-2j 
j 

n-l 
j-l 

( 

’ 
> 

ifj  #  0. 

t-4.9) 

From  (A.l),  it  is easy to verify  that 

7  Kj(i)  = coef  ofyjz’ 

in  (1 

+  y  +  z  -  ye)“;  since this  is  symm&ric 
that 

in  y  and  z,  it  follows 

0 

(‘i”)  Kj(i)  =  (7)  Kiti). 

(A.lO) 

a(’  -(;I  -2;;;  -  ‘)  (1 -  2x+(1  -  p))  I  6/2.  (4.14b) 

We come now to the crucial orthogonality properties. Let p(x) 

If cw(l -  a) I  6/2 already, then (4.14b) will be satisfied with 
p = 0 and so 

be a step function  with  jumps  of 2-n 

at x = k, k = O,l,  - -.  ,n. 

i 
0 

Regard /3(x) as a Stieltjes integrator,  i.e., for any polynomial  P(X), 

RLP@,~ 

=  0, 

if  a(1 -  LY) 5  a/2. 

(4.15) 

Otherwise define u and u by u2/4 = cr(1 -  a), u2/4 = fi(l  - 
p). Then the condition (4.14b) becomes simply (u2 -  u2)/(1 
+ U) I  26. Clearly, the smallest u for which this is satisfied 
is the unique positive solution to (u2 -  u2)/(1 + u) = 26, 
i.e., u2 +  26~ +  26 =  u2. But, since Hz(P)  = g(u2),  this 
means that 

RLP(%~ 

Ig(u2), 

if  cu(l -  a) 16/2. 

(4.16) 

This, combined with  (4.15), gives the promised bound 
(2.16). 

define  J-P(x) d/3 =  2-”  &P(k)  (i).  The  polynomials  KJ (x) are 
orthogonal with  respect to p, i.e., 

(A.ll) 

(see Szego [7, $2.821). Hence for  any P(X)  of degree at most  n, 

P(i)  =  2  akKk(i), 

i  = O,l, . . . ,n, 

k=O 

Cyk  = 

n 
k 

0 

-' 

J-P(x) 

d& 

(A.12) 

Many  important  facts follow  from  this  orthogonality.  (Formulas 
(A.13)-(A.18)  are all  derived  from  facts in  Szego [7, $3.2-3.41.) 

For  example, there  is a recurrence formula 

ACKNOWLEDGMENT 

0’  +  l)K;+i(x) 

’ 

(n -  2x)Kj(x)  +  (n -  j  +  l)Kj-l(X) 

The authors wish to thank Philippe Delsarte, Andrew 
Odlyzko, and Neil Sloane for their helpful comments on 
this paper. 

lo The dependence of  K.(x)  .on n  will  usually  be suppressed, but,  if 

necessary (e.g. in the proo i  of  (A.20)), we will  use the  notation  K)“‘(X). 

=  0. 
(A.13) 

Authorized licensed use limited to: Univ of Calif Berkeley. Downloaded on August 03,2026 at 11:10:52 UTC from IEEE Xplore.  Restrictions apply. 



<!-- pdf-page: 8 -->
164 

IEEE  TRANSACTIONS  ON 

INFORMATION 

THEORY,  MARCH  1977 

By  using the  reciprocity  formula  (A.lO),  it  is easy to  transform 
(A.13) into  a difference  equation 

(n  - 

i)Ki(i  +  1)  - 

(n  -  2j)Kj(i) 

+  iKj(i 

-  1)  =  0. 

(A.14) 

To  prove  (A.20),  observe that  if  it  is false, then  for  all  suffi- 
ciently  smalll”  c, there exists an infinite  sequence of n such that 
.ijn’  1. n(r  +  a~), where r  =  r(T)  =  l/2  -  d/7(1  -  T). Define  for 
each n  in  this  sequence integers  i  and j  by 

Also, we have the  Christoffel-Darbour 
formula,  which  says that 
if  Pc,Pl,  . . . ,  are  polynomials  orthogonal  with  respect  to  the 
Stieltjes  integrator  a(x),  i.e.,  JPi(X)Pj(X)  da(x)  =  Gijwj, then 

i  =  i,  =  Ln(r  +  t)] 

j= 

j,. 

6) 

(ii) 

.$  Pkb)Pk(Y) 

k=O 

Pk 

_  1  Lj 

Pj+l(X)Pj(Y) 

-Pj(X)Pj+l(Y) 

Pj  Ljil 

[ 

X-Y 

(A  15) 

, 

1 

where Lj  is the leading coefficient  of Pi(x).  For  the Krawtchouk 

polynomials,  pk = 

1  by  (A.ll),  and Lj/Lj+l  =  -0’  +  I)/2  by 

0 

(A.7),  and  (A.15)  becomes 

Kj+l(X)Kj(Y) 

-  Kj(X)Kj+l(Y) 

Let  Kj(x)  =  (-2)//j! 

(X -  x~)(x  -  ~2) * * * (X -  rj).  Then, 

But  from  (i)  Ii 
xk  1  2 
+  O(nF2). Therefore, 

- 

tn,  and so log (1 +  (i  -  xk)-l)  =  (i  -  x,,)-1 

log Kj(i  +  1) 

K,(i) 

=  kl  $ 

+  O(n-l). 

Similarly, 

Hence 

loeKjti - l) 

Kj(i) = - s1 &  + OW’I. 

logK,(i  +  1) 
- 
Kj(i) 

log 

K,(i) 

Kj(i  _  1)  =  OW’L 

Kj(i  +  1) 

K,(i) 

=  K,~~‘ll 

(1 +  O(n-l)). 

Furthermore,  K,(X)  has j  distinct  real zeroes xF’  <  r!i’  <  * . . < 
x?’ 
in  the open interval  (O,n), and the zeroes of Kj  and Kj+l  are 
interlaced: 

and so 

&l,  <  xci+l’  <  x.f), 

i  =  1,2,.  . . ,j  +  1, 

(A.17) 

where in  (A.17)  we have defined  x$’  =  0, x$,  =  n.  In  addition, 
each interval  (xp’,x,‘i!J  must  contain  a point  of increase of P(r), 
i.e., an integer.  Since by  (A.8),  K,(O)  >  0 and by  (A.9), K,(l)  > 
0 if  j  <  n/2,  it  follows  that 

Now  the difference  equation  (A.14) can be written  as 

(n  +K,(i+ 

1) 

K,  (4 

K,(i) 

‘Kj(i 

-  1) 

+i=O. 

xp  2  1, 

if  j  <  n/2. 

(A.18) 

If  we denote the  ratio  Kj(i)/Kj(i 

-  1) by  p, this  becomes 

The  next  two  results about  Krawtchouk  polynomials  we shall 

derive  in  detail.  Our  first  result  is that  any product  Ki  (x)Kj(x) 
can be expressed as a linear  combination  of the &  with  nonne- 
gative  coefficients,ll 

i.e., 

Ki(x)Kj(x) 

=  kco 

akKk(x), 

OIk  2  0. 

(A.19) 

To  prove (A.19), observe that  Ki(x)Kj(x) 
in  (1 -  y)X(l  +  y)n-n(l 
z)/(l 
+  z)/(l  + YZ))~ =  z$=&k(x)(y.+  ~)~(l+  YZ)“-~.  The coefficients 
of this  last polynomial  in y  and z are obviously  nonnegative  and 
in  fact  this  shows that  in  (A.19), 

-  z)X(1 +  z)n-x  =  (1 +  yz)“(l 
= 

is the coefficient  of y’2.i 
-  (y  + 

(y  +  z)/(l 

~j&&kb)((y 

(1  +  yz)” 

+  yz))“(l 

+  ye))“-” 

+ 

>( 

where  a binomial  coefficient  with  fractional  or  negative  lower 
index  is to  be interpreted  as zero.12 

Finally,  we come to an important  result  about the asymptotic 

behavior of the smallest zero x1 
of integers for which j,/n 
smallest  zero of K(  j(x).  The:’ 

” 
in 

of K,(“)(x).  Let  (jn)  be a sequence 
-  7,O I  r  5  1, and let x iin’  denote the 

lim  sup $ 
n-m 

I 

l/2  -  m. 

(A.20) 

(Actually  it  is possible to prove that  for  7 I 
‘/2, the limit  in  (A.20) 
exists and equals l/2  -  d/7(1  -  7) (for  7 2  l/z, the limit  is 0), but 
the  present  estimate  is sufficient  for  our  purposes and  is much 
easier to  prove.) 

11 Formula (A.19) must be taken to mean that  the polynomials  on the 
left  and right  are equal for x  = O,l, * * * ,n, since, viewed as a polynomial, 
K, (x)K;(x)  has degree i  + j,  which  may exceed n. 

1s Note that  LYE is the number  of vectors of weight  i  in  V,  at distance 

j  from  a fixed  vector of weight  h. 

(n  -  i)p2(1 +  O(n-l)) 

-  (n  -  2jj)p +  i  =  0. 

(iv) 

Since  p  is  real,  the  discriminant  of  (iv)  must  be  nonnegative, 
i.e., 

(n  -  2j)2  -  4i(n  -  i)  +  O(n) IO. 

However,  by  (i)  and  (ii),  this  is equivalent  to 

(1 -  2~)~ -  4(r  +  t)(l  -  r  -  t)  +  O(n-l)  >  0, 

but  (1 -  2~)~ =  4r(l- 

r)  and so 

-t(l 

-  2r)  +  t2 +  O(n-l)  2  0. 

(VI 

But,  if  6 is selected so that  -e(l 
is  clearly  violated  for  sufficiently 
proof  of  (A.20). 

-  2r)  +  t2 < 0, i.e., t  <  1 -  2r, (v) 
large  n.  This  completes  the 

APPENDIX  B 

Some  Properties  of the  Q-Polynomials 

In  this  appendix  we collect  for  reference purposes several im- 
portant  properties  of the numbers  Q;(i)  cited in  Section  II  (2.13). 
Most  of these properties  were originally  discovered by Delsarte 
[3],  and  we have given  references to  his  work  where  appropri- 
ate. 

The  numbers  Qj (i)  actually  depend on j,  i,  n, and w, and if  it 
is  necessary  to  emphasize  this  dependence,  we  will  use  the 
notation  Qj”,““(i).  To  define  these numbers,  we first  introduce 

I:’  In  the following  argument, t should be thought  of as fixed.  Its value 
will  be specified  more precisely  later.  (See the  remarks  following  (v), 
below.) 

Authorized licensed use limited to: Univ of Calif Berkeley. Downloaded on August 03,2026 at 11:10:52 UTC from IEEE Xplore.  Restrictions apply. 



<!-- pdf-page: 9 -->
MC ELIECE  et  al.:  NEW  UPPER BOUNDS 

165 

the  auxiliary  constants 

Hence for  any polynomial  P(x)  of degree at  most  w, 

P(i) = jgo ajQj(i), 

i  =  O,l,  . . . ,w, 

Then  the  definition 

is 

w’  =  n  -  w. 

03.2) 

where 

aj  =  hyl  SPtx)Qjtx) 

d@(x) 

Q,(i)  =  f. 

coef (1 -  yz)j(l  +  y)UJ-j(l  +  z)U”-j. 

I  Y’Z’ 

If  in  (B.3)  we expand  (1 +  y)“‘-j 

=  ((1  -  yz)  +  y(1  +  z))“‘-j 

= 

zgz(j 

(1 -  yz)u’--i-kyk 

(1 +  z)“,  we get the formula  (cf. [3, 

U3.3) 

=  pil$oPG) 

(y) 

(y) 

(L)-l. 

(B.14) 

Now we invoke the general theory  of orthogonal polynomials  (see 
S zegii [7, chapter  21 and Appendix  A),  and obtain  the  Christof- 
fel-Darboux 

formula  for  the  &j(x),  viz., 

Qj+ltx)QjtY) 

-  Qjtx)Qj+ltY) 

eq.  (4.3311) 

Q,(j)  =  Li.  u-j 

ui  k~o t-l)i-k 

(;:L) 

(w; 

j>  (w’ 

-L  +  k). 

=  (’ 

-  ‘) 

’  ~~~~~(~~)~$---~) 

‘j,& 

Qk(xjF(y)’ 

(B’15) 

U3.4) 

Each  Q;(x)  has j  distinct  real zeroes x r/) <  xv’  <  . . . <  x p’  in  the 
open interval  (d,w),  and the  zeroes of &j(x)and  Qj+i(x)  are in- 
terlaced: 

Similarly,  expanding  (1 -  yzP  =  ZiZO 

L  (-yz)“,  we get (cf.  [3, 

0 

the  equation  between  (4.33) and  (4.34)]) 

QjCi)=~k$o(-l)i-k 

(i 

jk) 

(“ii) 

(“‘ii). 

(B.5) 

Also, expanding  (1 -  yz)j,  1))1+  y)(l 

-  z)  +  (1 -  y)(l  +  z))/2]j 

=  2-j  zhEo  J 
k 
0 

(1  +  y)“(l 

-  z)“(l 

-  y)-‘-” 

(1 +  z)j-k,  we get, 

xp1  <  xi-‘+‘)  <  x,‘l”, 

i  =  1,2,.  a a j  +  1, 

(B.16) 

where  in  (B.17)  we have defined  x8)  =  0, xpjl  =  w.  Each  open 
interval  (xti)  xV+l))  must  contain  a point  of increase of /3(x), i.e., 
an integer. 

I  > 1 

If  we expand  the  product  Qj (X  )QI (x)  as 

w 

Qjti)Qlti) 

=  C  4$)&k(i), 

k=O 

(B.17) 

using the  formulas  (A.l)  and  (A.lO), 

where, according  to  (B.14),  the constants  411’  are given  by 

j 
0 
’ 
2, k=O (j  _”  k) 

i 

Q,(i)=c”j 

(“h?  Kj”‘,ti)Kk”‘ti). 

U3.6) 

then  Delsarte  ([3, lemma  2.41) has shown that 

q$’  =  ok’  J”Qj(x)Ql(X)Qk(X)  d@(x), 

(B.18) 

Finally,  we  remark  that  Qj(X)  belongs  to  the  family  of  Hahn 
polynomials  and that  it  can be expressed as [l],  [4] 

Q,(x)  =  pj$‘Z(-j,-x,j 

-  n  - 

l;-w,-~‘;l) 

/j\ 

ln  +  1  -.i\ 

=  cL.  & 
I 

k=O 

(-1)” 

‘k’ 

’ 
(;> 

k 
(;J 

’ 

’ 
(k)’ 

(B’7) 

Formulas  (B.6)  and (B.7)  show that  Qj(i)  is a polynomial  of de- 
gree j  in i.  We shall  denote this  polynomial  by Qj(x)  or Q:“,““(x). 
From  (B.3)-(B.6),  the following  elementary  properties  are easily 
verified: 

Qotx:) =  1, 

Qltx) = (n -  1) (1 -s), 

Qjto)  =  pj, 
Qj(l) = pj (l - jtn ’  ’  - j)), 

ww’ 

tB.8) 

(J-1 

(B.lO) 

(B.ll) 

Qj(x)  =  (-,‘)j  0 w 

n 

J! 

xj  +  lower  degree terms. 

(B.12) 

Delsarte  has shown ([3, sections 2,4])  that  the polynomials  Qj (x) 
are orthogonal  with  respect to  the  Stieltjes  integrator  p(x)  with 

jumpsof 

(~)(~)(~)-l,ati 

=O,l,.a.,w,i.e.,that 

JQj(X)Qk(x) 

dB(x) 

=  Pjhj,k. 

(B.13) 

qj$’  2  0, 

all  j,k,l,  E  (O,l, . . - ,w). 

(B.19) 

The  last  result  we take  from  Delsarte  is the following  difference 
equation  [3, p. 491: 

(W 

- 

i)(w’ 

-  i)Qj(i  +  1) -  (ww’ 

-  j(n  -  2i) 

-  j(n  +  1 -  i))Qj(i)  +  i2Qj(i  -  1) =  0. 

(B.20) 

Our  final  result  here concerns the  asymptotic  behavior  of the 

smallest  zero xy)  of QpW)(x)  as j,  w, and n all  approach  infinity 
at the same rate. Thus  let  (w,)  and (jn)  be sequences of integers 
with  w,/n  -  cr, j,/n 
-  p with  6 I  01 I  $,  and let xlCj,w,n)  denote 
the  smallest  zero of  Qj”z”)(x).  Then, 

lim  sup 
n-m 

xltjn,wn,n) 
n 

I  a(1  -  a)  -  p(1 -  fl) 

(1 7  2p)a 

- (1 -  2~‘\/p(1 -  /3)). 

(B.21) 

in  (B.21) exists and 
(Actually  it  is possible to prove that  the limit 
equals the  right  side  of  (B.21)  for  all  p  I  01 L  3/2, but,  since the 
proof  is very long and we do not require  it  in the derivation  of the 
bound  (2.15), we omit  it.) 

To  prove  (B.21),  observe that  if  it  is false, then  for  all  suffi- 
ciently  small14 e, there  exists  an infinite  sequence of n such that 
xl(jn,wn,n)  1  n(F  +  2e), where F  denotes the  constant  on the 
right  side of  (B.21).  For  a fixed  n  in  this  sequence, define  i  =  i, 
6119 J = Jm w  =  w,,  W’  =  n  -  w,,  and let  Q~“~“‘(x)  = Lj(x 
f  I..)’ 

. 

. 

.a’(~:  -xc)).Then 

I 

ti) 

l4 In the  following  argument  e should  be regarded as fixed.  Its  value 
will  be specified  more  precisely  later  (see the  remarks  following  (xi), 
below). 

Authorized licensed use limited to: Univ of Calif Berkeley. Downloaded on August 03,2026 at 11:10:52 UTC from IEEE Xplore.  Restrictions apply. 



<!-- pdf-page: 10 -->
166 

IEEE  TRANSACTIONS  ON  INFORMATION 

THEORY,  MARCH  1977 

But  i  I  n(F  +  t)  and ICY’ L  n(F  +  2t), and so Ii  -  ~2’1  L  tn,  for 
Iz =  1,2,.  . . j.  Thus 

The  two  zeroes of the  quadratic  polynomial  (n  -  2j)‘Jiz  -  2n(w 
-  j)(w’ 

-  j)i  +  (w  -  jJz  (w’  -j):!  are given  by 

. 

log  1 It- 
( 

1- 

1 
xp  > 

=  f$jj 

+  O(ne2). 

(ii) 

Combining  (i)  and  (ii),  we have 

log “tja,l’ 

=  f  kc1 & 

+  OWlI. 

(iii) 

il  i2 =  (w  -jjtw’ 

-8 

(n  -  2j)2 

(n  l  2 dj(n 

- 

j)), 

(xl 

Recalling  that  w,/n 

-  cr, j,/n 

-  p, etc., then  for  large n, 

equation  in  (iii),  we 

il 
i2 
------f 
n’  n 

a(1  ,;y2;,‘i’ 

-  @) (1 f  2 d\/p(l  -  P)). 

(xi) 

Subtracting  the I‘+”  equation  from  the “-” 
obtain 

- 
log QjCi +  1) _  log  Q,(i) 

Qjci  _  l)  =  OW’), 

Q,(i) 

and so 

(iv) 

Hence, if  t is selected so that  i  =  i,  =  Ln(F  +  t)l  lies between il 
in  (ix)  will  for  large  n  behave like  a 
and  i2,  the  discriminant 
negative  constant  times  n4, a contradiction.  This  completes the 
proof  of  (B.21). 

Q]Ci + 1) 
Q/(i) 

=  QjT:(i)l) 

- (1 +  O(n-I)}. 

(VI 

REFERENCES 

The  difference  equation  (B.20)  can be written  as 
i)  QjCi + 1).  Qj(i) 

i)(w, 

(w 

_ 

_ 

Q,(i)  Q,Ci -  1) 

-  (Ww’  -  j(n  -  2i)  -  j(n  +  1  - 

i)) 

Qj(i) 
Q,;Ci -  1) 

+  i2  =  0. 

(vi) 

If  we denote the  ratio  Qj(i)/Q](i 

-  1) by  P, then  (vi)  becomes 

111 

[21 
~31 

(w  -  i)(w’ 

-  i)p”(l  +  0(X’)) 
- 
-  (ww’ 

i(n  -  2i)  -  j(n  +  1 -  j))p  +  i’  =  0. 

[41 

(vii) 

[5] 

Since p is perforce  real, the  discriminant  of the quadratic  equa- 
tion  (vii)  must  be at  least 0, i.e., 

(ww’ 

-  j(n  -  2i)  -  j(n  +  1 -  i))2 

M 

-  4(w  -  i)(w’ 

-  i)i2  +  O(nzi) 10. 

(viii) 

Despite  appearances, this  is actually  only  quadratic  in  (9,  and 
a little  rearrangement  of  (viii)  yields 

(n  -  2j)‘i’ 

-  2n(w  -  j)(w’ 

-  j)i 

+  (w  -  j)2(w’ 

-  j)2  +  O(n:j) L  0. 

(ix) 

[71 

PI 

R. Askey, Orthogonal  Polynomials  and Special Functions.  (vol. 21 
in  SIAM’s  Regional Conference Lectures  in  Applied  Math.)  Phila- 
delphia:  SIAM,  1975. 
E. R. Berlekamp,  Algebraic  Coding  Theory.  New York:  McGraw- 
Hill,  1968. 
P. Delsarte, An  Algebraic  Approach  to the Association  Schemes of 
Codinz Theory.  Eindhoven: Philips Research Reports Supplements 
no. lOyl973.  ” 
S. Karlin  and J. L. McGregor, “The  Hahn polynomials, formulas, and 
an anolication.”  Scrinta  Muthematica,  vol. 26, pp. X-46,  1961. 
V.  I:  Levenshtein,  %n 
the  minimal  redundancy  of  binary  error- 
correcting codes”  (in Russian), Problemy Peredachi Informatsii,  vol. 
10, pp. 26-42,1974. (English translation  in Information  and  Control, 
vol. 28, pp. 268-291, 1975.) 
V. M. Sidelnikov,, “Upper  bounds on the cardinality  of a binary  code 
with  a given minimum  distance”  (in Russian), Problemy  Peredachi 
Znformatsii,  vol.  10, pp. 43-51,  1974. (English  translation  in Znfor- 
mution  and  Control,  vol. 28, pp. 2922303, 1975.) 
G. &ego,  Orthogonal  Polynomials.  Providence: American  Mathe- 
matical  Society, 1939. 
L.  R. Welch,  R.  J. McEliece,  and  H.  Rumsey, Jr.,  “A  low-rate  im- 
IEEE  Trans.  Inform.  Theory,  vol. 
provement  on the  Elias bound,” 
IT-20,  pp. 676-678, Sept. 1974. 

Authorized licensed use limited to: Univ of Calif Berkeley. Downloaded on August 03,2026 at 11:10:52 UTC from IEEE Xplore.  Restrictions apply. 


