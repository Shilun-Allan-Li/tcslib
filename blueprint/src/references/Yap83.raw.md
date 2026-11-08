<!-- generated-by: proofmatch local extraction -->
<!-- source-pdf-sha256: 1a201b3020697c11026a8960d25aa9c472f55d033017ef3ddb0948be261f2347 -->
<!-- extractor: pdfminer.six v20260107 -->

<!-- pdf-page: 1 -->
Theoretical  Computer  Science  26  ( 1983)  287-300 
North-Holland 

287 

SOME  CONSEQUENCES  OF  NONdJNIFORM  CONDITIONS 
ON  UNIFORM  CLASSES* 

by  A.  Meyer 

Communicated 
Received  April  1982 
Revised  December  1982 

Abstract.  We  obtain  some  results  of the  form:  If  certain  complexity  classes  satisfy  a non-uniform 
condition, 

then  some  unlikely  consequences 
polynomial-time 

(1)  If  the  ‘non-uniform 

follow.  More  precisely: 
hierarchy’  collapses  at  level 

Ui/pOly, 
strengthens 

then 

the  Meyer-Stockmeyer 

hierarchy  collapses  at  Ieke 
of  a  result  of  Karp  and  Lipton  ( IWP). 

i+2, 

a  generalization 

i  >O. 

i.e.,  &/poly  = 
i.e.,  Ii+?  =  I7,,  ?.  This 

reducible 

to  a sparse  set,  then  P = NP.  This  generalizes  a  theorem 

of  Fortune 

(2)  If  co-NP  is conjunctively 
(1979). 
(3)  If NP  is conjunctively 

and  disjunctively 

reducible 

to  a sparse  NP-cor,lplete  set,  then  P =  NP. 

is  a  partial  generalization 

This 
reducibility  were  introduced  by  Ladner,  Lynch  and  Selman  (1975). 

of  a  result  of  Mahaney 

(1980).  Conjuctive 

and  disjunctive 

(4)  If  co-NP  is  y-reducible 

to  a  sparse  set,  then  NP  = co-NP.  y-reducibility  was  introduced 

by  Adleman  and  Manders 

(1977). 

1.  Introduction 

Circuit  complexity  has  become  an  important 

tool  in  computational  complexity 
through  a program  of  research  which  attempts  to  reduce  the  complexity  of machine 
to  finite  combinatorial  questions  about  circuits.  Until  the  recent  paper 
computation 
of  Karp  and  Lipton  [S],  results  connecting  circuit  complexity  to  Turing  machines 
had  thti  flavor  “If  a  set  S  has  small  Turing-machine  complexity,  then  it  has  small 
circuits”  (Savage,  Fischer  and  Pippenger,  Schnorr).  The  (surprising)  results  in  [S] 
show  that  interesting  reverse  implications  exist. 

In  a  different  line  of  research  initiated  by  Hartmanis  and  his students  (e.g.,  [?I), 
a  lovely  theory  of  polynomial 
isomorphism  was  invented.  One  open  question  was 
reducible  to  a sparse  set.  This  was  recently  ‘solved’ 
whether  NP  can  be  many-one 
in  the  sense  that  strong  negative  evidences  are  obtained,  since  a  positive  answer 
leads  to  P = NP  [ 111. 

*  This  work  was  sugported 
**  Present  address:  Courant 
10012,  U.S.A. 

in  part  by  NSF  Grant  MCS  80-05469. 
Institute  of  Matheinatical  Sciences,  251  Mercer  Street.  NL’W York,  NY 

0304-3975/83/$3.00 

@  1983,  Elsewer  Science  Publishers  B.V.  (North-Holland) 



<!-- pdf-page: 2 -->
288 

C.K.  Yap 

Both  these  programs  of research  can be regarded  as attempts  to  reduce  ‘uniform’ 
complexity  to ‘non-uniform’  complexity.  The  new results  of [8,  1 l]  say that  imposing 
suitable  ‘non-uniform’  conditions  on ‘uniform’ complexity  classes leads  to significant 
consequences.  In  this  paper  we continue  to  explore  this  theme.  We  shall  introduce 
a non-uniform  version  of the polynomial-time  hierarchy.  The  techniques  introduced 
i.:  [2,4,&l 
l]  are  used  to  generalize  and  sharpen  some  of  their  results.  Related 
and  additional  results  are  found  in [lo,  12, 14,151. 

Notation.  For  X, y E (0,  l}“,  let  x  . y E (0, 1)” refer  to  the  result  of  applying  a  fixed 
‘pairing’  function  “  - ” 
instead  of 
computable.  We  conveniently  write  x1 l  x2  9 .  . .  l  xk  or  ~1x2 * 9 l  xk 
is 1 - l-u:!  * .  . .  ’  (A-r,  1 - xk  )).  The  projection  functions  are  implicit,  e.g.,  we can  extract 
.Y from  .t- - y. 

that  “  l  ”  be  polynomial-time 

to  x  and  y.  ‘i;t’e require 

To  conserve  symbols,  we  adopt  p*(  l  )  as  a  ‘generic  polynomial’.  Thus  if  the 
function  f  is bounded  by  some  polynomial,  we  write  “f(n)  <p*(rr  )“.  The  asterisk 
has  properties  like  Kleene’s  star,  as in 

(In  recent  papers  IS, 61 a related  notation  appeared.) 

For  polynomially  bounded  quantifiers,  instead  of  writing 

we write 

&x)[s 

l  ~1  and  OLx)[* l  -1. 

2.  Non-uniform  conditions 

In  this  section  our  main  results  are  stated. 
For  a set S c  (0,  l}*, let  9”  - -  S n  (0,  1)“. Recently,  two ‘non-uniform‘  conditions 

on  S  were  studied: 
(1)  Sparsmess: 
(2)  Small  circuits:  The  characteristic  function  of S’“’ can be computed  by a circuit 

IP’l=qP(t2). 

of size  sP*(n  ). 

Xt is  easy  to  see  that  even  non-recursive  sets  can  fulfill  these  conditions. 
in 
complexity  theory,  we are  mainly  interested  in sets  L  which  are  ‘uniform’-for  our 
purposes  they  are sets accepted  by some standard  machines  using resources  bounded 
by  nice  functions.  The  interest  in  non-uniform  sets  3‘ comes  from  results  of  which 
the  following  are  examples: 



<!-- pdf-page: 3 -->
Consequences  of non-uniform  conditions 

289 

(3)  Mahaney  [ 111: If  NP  GL S, a sparse  set,  then  NP = P. 
(4)  Karp  and  Lipton  [8]:  If  every  S E NP  has  small  circuits, 

then  2;  = I7:. 

in  polynomial-bounded 

Here  GE  is  polynomial-time  many-one 

reducibility,  and  Z,!,  ZTp are  the  usual 
classes  in  the  polynomial-time  hierarchy  [ 131 of  Meyer-Stockmeyer.  Since  we  arc 
only  interested 
versions  of  the  concepts  involved,  we shall 
henceforth  omit  the  superscript  “P”  in  &  Ep,  etc.  All  complexity  classes  (e.g., 
P, NP,  &)  are  assumed  to  be  families  of  subsets  of  (0, 1)“. 
We  now  consider  an  alternative  view of  small  circuits. 
For  any  complexity  class  K,  Karp  and  Lipton  [8]  introduced 

the  non-uniform 
class  JC/poly:  An  adoice  frrnctiou (Y : (0,  l}* +{O,  l)*  is a  function  with  the  property 
1.x I=  Iy 1 +  QI (x ) = a  (y ). We  can  unambiguously  write  (Y (n )  for  Q) (x )  if  n  =  Ix I. The 
advice  CY is polynomial  if  Ia (n )I <p*(n).  Let  poly  be  the  class of  polynomial  advice 
functions.  If  L c  (0,  I)“,  let  L/O  =  {x  : s 
is  the  class  of  sets  of 
to  consider  the  non-uniform 
the  form  L/a  where  L  E K,  ar E poly.  It  is  natural 
analog  of  the  Meyer-Stockmeyer  hierarchy: 

.  N (s  ) E L}.  K/poly 

, 

We  call  this  the  non-uniform  polynomial-time  hierarchy  (or  advice  hierarchy).  Let 
PH  = Uiao  Xi. It  is well  known 
hierarchy  collapses, 

that  if Ci = fli  for  any  i > 0,  the  Meyer-Stockmeyer 

i.e., 

We  show  an  analogous  result  in  the  advice  hierarchy. 

Theorem  1.  For  i > 0, 

Zi/pOly  = Hi/pOly  3  JZi/poly = PH/polY  = ni/polY* 

If  Z;  = Hi,  then  surely  Ei/polY  = I7JpolY.  The  r_Xt  result  shows 

that  a  partial 

converse 

is  true. 

Theorem  2.  For  i > 0, 

Xi/polY  = Ui/pOlY  *  Ci +z = Iii+,. 

To  see  the  connection  of  (4)  to  this  theorem, 

recall  [8]  that  S  has  small  circuits 

iff S  E p/poly  = I&Jpoly.  Thus  (4)  is equivalent 

to 

This  generalizes 

to 

For  i  2  0, 

1yibI  Gl7i/pOly 

+?  Ei+2=ni+2. 



<!-- pdf-page: 4 -->
290 

C.K. Yap 

Our  Theorem  2  is  a  strengthening  of  (*)  when  i > 0  since  it  will  be  shown  that 
Ci+ 1 C  IlJpOly 

implies  Zi/pOly  = I7if poly. 

An  open  question  in  connection  with  (3) is whether  s,,,  can  be  replaced  by  +, 
truth-table  reducibility  (see also  [14,15]).  A  more  modest  generalization  would  be 
to consider  scan, conjunctive reducibility (see [9] where  6,,  and  scan were  introduced. 
A  ‘practical’  application  of  conjunctive  reductions  may  be  seen  in  the  recent  thesis 
of  Jefferson  [7]  where  a  non-polynomial  version  of  gCon was  used  to  show  the 
decidability  of  a rich  assertion  language  for  sorting  programs  which  handle  vectors 
and  integers).  We show here  that  the  Berman-Fortune 
search  technique  [4] extends 
to  <co”. 

More  precisely,  assume  finite  subsets  of  (0,  1)”  are  canonically  encoded  by 
elementq  of (0, l)*.  If f  : (0,  l}* + (0, l}*, define  [:  (0,  l}* +  2”*i’* by f(x)  = X  where 
f(x)  encodes  X  E (0,  l}*.  We  say L  scan L’ iff for  some  p-time  function  f, 

xEL 

iff 

f(x)CL’. 

We  also  assume  that  f(x)  is nonempty  for  all x. 

Theorem  3.  If  co-NP  &,,,  S, a  sparse set, then  NP I= P. 

If  CO-L <co” m- L’,  we  say  L  is disjunctively  reducible  to  L’,  denoted  L  G&s L’. 
This  was  also  introduced  in  [9].  Note  that  NP s,,,  S  implies  that  NP  <con  S  and 
NP sdis S.  In  this  sense,  the  next  theorem  is a partial  generalization  of  Mahaney’s 
result  (3). 

Theorem  4.  If S E NP  is sparse, NP 6,,,  S and  NP sdis S, then  P = NP. 

This  theorem  would  be  a full  generalization  of  (3) if the  requirement  S E NP can 

be dropped.  Note  the  difference  in  the  hypotheses  of Theorems  3 and  4. 

For  the  next  result  about  sparse  sets  we  need  a  definition.  Let  M  be  a  non- 

deterministic  transducer  and 

G(1M) = (x  . y : for some  computation,  iM produces  y  on  input  x}. 

Following  [l]  we  say  that  L  is  y-  reducible  to  L’,  L  6,  L’,  if  for  some  p-time 
non-deterministic 

transducer  M, 

ti)  V.v  3~.  .v . v E G(M), 
(ii)  x  . ): EG(A~)  3  x EL  @  y EL’. 

Without  loss of generality  we may  assume  that  M  always  halts  in  polynomial  time, 
with or rvithout an output. 

Theorem  5.  If  co-SAT  6,  S, u sparse set, then  NP = co-NP. 

It  is  interesting  to  note  that  none  of  the  previous  results  in  [8],  [ll],  etc.,  has 

this  particular  conclusion,  i.e.,  NP = co-NP. 



<!-- pdf-page: 5 -->
Consequences of  non-uniform condition; 

291 

3.  Collapse  of the advice hierarchy 

In  this  section,  Theorems  1 and  2 will be  proved. 
The  following  is a simple  but  useful  result. 

Lemma 6.  (CO-K )/ply  = ~-(Klpoly). 

Proof.  Let  L E co-(K/poly). 

_YEL 

iff  xeco-L~K/poly 

iff  x  n ar(x)~LkK 

(whereto-L=L’/cu) 

iff  Y v(~)Eco-L’ 

iff  x  E (co-L’)/a  E (co-K  b/~~oly. 

0 

An  immediate  consequence 

is  that 

if K  is closed  under  complementation, 

so  is 

WPOlY  l 

The  following  is the  key  lemma  (cf, 

[S, Lemma  6.21). 

Lemma 

7,  Vi  >  @, I&  C  EJpOly 

implies xi  +l/pOlY  = silPolY* 

Proof.  The  proof  here  for  i -  1  extends  mutatis  mutandis  for  III  i >  1.  Asscme 
11, c  &/poly  and  L E &/poly.  The  lemma  follows  if we  show  L t: -WI /poiy.  So: 

(1)  Since  L E &!poly, 

(3 &E&,CE  ~poly)(\Jx)[~  EL  e 

x  . a(X)E&j. 

(2)  Since  Sz E &, 

(3)  Since  27, C_ C 1 /poly 

, 

(3S1~~1,a’~poly)(Vx,a)[.~ 

*a  l X)EPI 

e 

x  . a  l  a(x)  9 a’(x 

l  a  l  a(X))ESJ- 

Let  yx,a denote  x  - a  8 cy (x)  8 ar ‘(x  l  a  9 a  (x )). 
(4)  Since  S1 E&, 

We  ‘telescope’  ( 1 I--(4) into  the  follcwing: 
(5)  From  WI(~), 

(3  PI  E n,,  cy E poly)(Vx)[x  EL  <j  (31,&X 

’  a  l  a(x)  E PI]. 



<!-- pdf-page: 6 -->
b

‘

4

 =
u

w

-

 -
c

.

4
 c

r
r

-

*

t
J

L
f

=
L

-
.
-
L

‘

4

-
-
_

‘

p

 5

Y

t
t

.

Z

1
c

U
J

y

h

=
U

c
d

 5

I
I

 =
u

a

I
I

r
s
,
e

$

c

-
-

G

-

 s

Q

)

 z

-
 Y

“
0

-
 C

-
 .

I

.

‘

a

U
J

*

 -
c
c

I
I
’

.

A

-

e

W

c

*

U

2

-
 z

.

c
1

W

Q

-
=

I
I

c

V

-
-

-

G

-

-
 ;
I
:

.

f
-
4

U
J

0

4

.

c

:

-

h

;
:

c
/
l

c
-
”

 _
-

U
J

 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 


<!-- pdf-page: 7 -->
Consequences  of non-uniform  conditions 

293 

Suppose  (ii) holds.  Thus 

ni  E Zi/poly 

and  hence  Xi+ I/poly  = xi/poly 

(Lemma  7). 

Therefore 

Zi/poIy  = u  (Xj/poly)  = (U  sj)  /poly  = PH/poly, 

jli 

pi 

i.e.,  (iii)  holds.  The  same  type  of  reasoning  will  prove 
manner. 

Cl 

the  other  cases  in  a  routine 

(Note  that  Theorem  1 is contained  in  this  corollary.)  Theorem  2 will  be  proved 

below. 

’ 
A  recursive 

structure (cf. [8]) is (B ; F1,  . . . , F,;  GI,  . . . , G,)  where 

B  : (0, 1, +’ -* (0,  l},  Fj : (0,  1)” + (0,  l},  Gk : (0,  1)"  +  (0,  :}*, 

j=l,..., 

r,k=l,..., 

s. 

Let chL denote  the characteristic  function  of a set L. Call (B ; F1,  . . . , F,;  G1,  . . . , G,) 
a recursive  structure  for L  if the  following  hold: 

(i)  Wx)[chdx)  = BWdxh  . .  . J?(x),  &,GWh 
. . . , G,}  induces  a well-founded 
(ii,  {Gl, 

. .  . , chdG,~.d))]. 

that  for  all  A-, and  k  =  1,  . . . , s.  we  have  G,, (.u ) -CY  or  Gk IX ) =  A-.  Further, 
<-minimal 

itf  C;k IS I =  s  for  all  GI,. 
(iii)  If  x  is  a  4  -minimal  element, 

then 

stricf  partial  order-ins  -C on  (0,  I}* such 
.\a is 

B(Fl(x)  ,...,  F,(x),),,,...,y,)=B(F,(x) 

,... 

,F,(x),y’,, 

. . ..v.> 

forall\‘k,&, 

k  =  1,. 

. .,s. 

If  {4}  and  (G k  are  ail  computable 
recursive structure. 

} 

in  polynomial  time,  we say  L  has  a polyrromiaf 

Let  Ai  be  any  reasonable  encoding  of  the  set  of  true  prenex  sentences  of  the  form 

.  . .  , .Fi)  is  a  quantifier-free 
for  j= 

where  Mt.&, 
included 
l,..., 
2  a  sequence  of  Boolean  variables. 
E,  is similarly  defined  except 

in  &,. 

.  .,.f,, 

Boolean 

formula  whose  variables  are 
and  ii 

otherwise 

if  j=odd,  Qj=3 

i,  Qj=V 

for  Ai.  The  structure 

the  roles  of  V  and  3  are  reversed.  As  noted 
in  [8], 
recursive  structures.  We  sketch  the  polynomial.  recursive 
is  (B;  F1, F2; Go,  GJ  where  F*(x)  =  1 iff x’ encodes 

Ai  and  Ei  have  polynomial 
structure 
a  sentence  of  the  form  (10)  in  which  M  is  non-constant;  Fz(x)  =  1 iff x  encodes  a 
sentence  of  the  form  ( 10)  and  either  M  =  1 or  the  leftmost  variable 
(_C*, .  .  .  , ft)  which  actually  occurs 
Go(.x ) =  s  ii  F,(x  ) =  0,  otherwise  G&Y )  is  the  sentence  obtained  by  substituting 
for  all  occurrences 

in  the  sequence 
by  an  existential  quantifier; 

0 
(_C,, .  . .  , x7;)  which 

left-most  variable 

in  the  sequence 

is  bounded 

of  the 

in  M 

1 

, 



<!-- pdf-page: 8 -->
294 

C.K.  Yap 

actually  occurs 
replaced  by  1. It should  be  clear  how  B(x 1, ~2, y I, ~2) = z  is defined: 

. . . , _ c).  G,  is  similar 

to  Go  except 

in  A&& 

, 

the  occurrences  are 

With  a suitable  encoding  scheme,  we can  further  assume  that the  Gk’s are length 

preserving, i.e.,  (Gk (x)1 = Ix 1. 

Proof of Theorem  2.  We now complete  the  proof  of Theorem  2. Assume Si/pOly 
= 
It  is sufficient  to  show  that  Ai +2 E iSi+* since  Aj  is complete  for fTj under 
&/poly. 
SO,  for some  Pi E: Hi, 
s,-reductions.  By the  corollary  to  Lemma  7, Ai+z E Lfi/pOly. 
CY E poly,  Ai+z = Pi/am Let  (B;  F1, &;  Go, G1) be  the  polynomial  recursive  structure 
for  Ai+? just  defined  above.  Consider  the  predicate  W(x,  IV): 

Note  that,  for  all  x,  W(x, (Y (x )) is true.  If  W(x,  w ) holds,  we  say  w  is a  witness 

for  x.  We  claim  that 

(12j 

x  EAi+z 

iff 

(~I~~w)[.x .  w  EPi A W(X, ~‘11. 

side 
To  see  this,  suppose  x  E Ai+>. Then  choosing  w  = cy (x)  makes 
of  (12)  true.  Conversely,  let  the  right-hand  side  of  (12)  hold,  and  w  be  a  witness 
for  x.  It  is sufficient  to  show 

the  right-hand 

Vy, 

\yj=/_U/ 3 

0’  * lt*EP,  iff !‘EAi+l). 

Since  the  G1,‘s arc  length  preserving, 
For  such  a  y, 

there  is  a  y  which  is  <-minimal 

and  IyI =  IA- I. 

(13, 

chp(y 

* H-1 =  1 

iti 

1’ EA,  &?. 

This  is because  chp, ( y  - a  ( y )) =: 1 iff y E Ai+xn But 

chp,(y  . w)=chp,(y 

‘a(y))=B(Fl(y),F2(y)r~lr2:) 

of  the  zi ‘s. By induction  on  -c,  we  see  that  (13)  holds  for  all 

which  is  independent 
\‘* j,(  = )_l_i, 
Observe 

that  W(x,  W) is  a  predicate 

in  Hi+.,  since  Pi E Hi. Hence  the  Iight-hand 

3ide  of  (12)  is in  Zi-+z. This  shows  that  Ai+z E Ci+l,  proving  Theorem  2. 

[7 

1.  Conjunctive  reduction 

In  this  section  Theorems  3  and  4  will  be  proved. 
Define  the  census  function cs(  l  ) of  a set  S  by 

c&z)  = 

IPI. 

i 

i-0 



<!-- pdf-page: 9 -->
Consequences  of non-uniform  conditions 

29.5 

Proof of Theorem 3.  Let SAT be any reasonable encoding of the satisfiable Boolean 
formulas  without  quantifiers  (SAT  is  essentially  E1  in  the  last  section).  Let  co- 
SAT sco,, S  via g. Given  a Boolean  formula F,  we  show  how  to  test  if F  E SAT  in 
time p*(lFl),  which will prble  our theorem. 

The  depth-first search of  Fortune  [4] is conducted.  The nodes  of  the  search tree 
are partially instantiated  versions  of F.  Let  G  be  a node  in the  tree.  We  call G  a 
formula if it  has  no  variables. If  G  is  not  a constant  formula,  it  has two 
constant 
children Go and Gi  obtained by substituting 0 and 1 (resp.) for the leftmost variable 
of G. The  leaves  of  the  tree  are  exactly  the  constant  formulas  which  are  identically 
true  or  identically  false  (denoted  ~1  or  “0,  resp.).  As  a  node  G  is  visited,  we 
compute  the  label  g(G)  for  it.  All  visited  nodes  are  considered  ‘alive’  until  some 
time  when  it is declared  ‘dead’. Beginning  at  F,  successive  nodes  to  be  visited  are 
chosen  by  the  depth-first  rule,  subject  to  the  condition  that  we do  not  search  below 
a  dead  node.  The  whole  search  tree  is  exponential  in  size  and  is  therefore  only 
implicit.  Instead,  a node  is constructed  from its parent just before  we  visit  it.  We 
maintain 
the  search  a  set  S  of  elements  where  SC  S.  Initially  S  is 
empty.  The  following  subroutine  is used to visit a node  G. 

throughout 

vmr(G) 

Step  1.  If G =  1,  declare  F  satisfiable.  Halt. 
Step  2.  Compute  the  label  g(G)  of  G. 
Srep 3.  If  G = 0,  then  do:  $  := S u  g(G)  and  declare  G  ‘dead’. 
Step  4.  (Propagate  Death).  For  each  previously  visited  node  G’ which  is still  alive, 
test  if either  g’(G’) c  S or both  G:  and  Gi  are  dead.  If so, do:  S :=S  ug(G’) 
and  declare  G’ ‘dead’.  (Note:  G’  will be  non-constant,  so GA and  Gi  exist.) 

The  search  ,halts  if F  is  declared  satisfiable  (Step  1) or  dead  (Step  3  or  Step  4) 

while  visiting‘a  node.  The  description  of our  search  procedure  is now  complete. 

Observe  that,  inductively,  if  a  node  is declared  dead,  then  it  is unsatisfiable.  In 
particular, 
if  F  is  declared  dead,  it  is  unsatisfiable,  Similarly  if  F  is  declared 
satisfiable,  then  it  clearly  is satisfiable.  This  proves  the  ‘partial  correctness’  of  the 
procedure,  i.e., F is correctly  declared  if there  is any declaration.  A logical  possibility 
is that  all  nodes  may  be  visited  without  any  declaration  on F. A moment’s  reflection 
will dispose  of  it.  This  proves  the  total  correctness. 

It  remains 
follows  from: 

to  show  that 

the  procedure  has  polynomial 

running 

time.  This 

(A) 

(B) 

The  number  of nodes  visited  by our  procedure  is polynomial  in IFI. 

The  time  to visit a node  is polynomial  in  IFI. 

Fix an  arbitrary  instant  during  the  search  procedure.  Let  N  be  the  set  of  already 
visited  nodes  and  D  EN  be  those  nodes  which  are  either  dead  or  lie  below  a dead 
if  F  is  dead,  then  D  = N.  We  shall  show  IN~G~(IFI). This 
node.  In  particular, 
implies  (A) since  the  chosen  arbitrary  instant  can be at the  termination  of the  search. 



<!-- pdf-page: 10 -->
296 

C.K. Yap 

that  if N  -D 

It  is easy  to  show  by  induction 

then  the  nodes  N  -D 
IN -DI  QZ  < IFI where  n  is  the 
in  F.  Let  u  be  the  root  F  if  N  = D,  otherwise  u  is  any  node 
is  in  N  ---LX Let  T  be  the  subtree  whose  nodes  are  all  the  elements 

form  a  single  path  from  the  root  F.  This  implies 
number  of  variables 
whose  parent 
in  D  which  are  descendents  of  ZJ. ?’ lg.  1 illustrates 

the  situation. 

is  nonempty, 

v=F 

Or‘ 

n 

Fig.  1. 

Theye  are  at  most  1+  IN -421  s  IFI such  trees  T. Therefore, 

(1)  follows  if we  can 

show  !,r! ~p*(jF\). 

Call  node  G  E T penultimate if  both  Go  and  G  I  are  leaves  in  T. The  number  of 
nodes  in  T. This  is 
leaves  in  T  is  s(n  + 1)~ where  11 is the  number  of  penultimate 
because  at  most  n + 1 leaves  can  have  parents  which  are  on  the  path  frc;n  the  root 
node.  So  ITI s  2(/t  + 1)~  and  it  suffices  to  show  that  II <  p*(lFI). 
to  a  penultimate 
nodes  by  defining  G  C G’  if  G  was  visited  before 
We  totally  order  the  penultimate 
otherwise  G’  would  be 
G’.  Note 
declared  dead  when  it  was  visited  and  would  be  in  leaf  in  T. Hence  u  is  bounded 
by  the  census  number  c&k)  where  k  is a  bound  on  the  lengths  of  elements 
in  i(G 
for  G  in  T. But  k ~p*(lGl)~p*(IFl) 
so es(k)  sp*(lF\).  This  proves  (A). 

that  G  <  G’  implies  g(G’)  -  i(G) 

is  nonempty, 

j 

Finally,  (B)  follows  from 
nodes  are  examined  during 

the  observation 
the  propagation  of  death. 

c1! 

that  Is^l~p*(lFI) and  at  most  )I  (live) 

Proof  of  Theorem  4.  Define  the  pseudo-complement 

of  S  [ 1 I]  by 

pc_S  z  {()‘I .  1 k  . .\  : ;.I ; --- II  and  citlw 

ik 

=  <+I~  1 ,Y .Y k? S  1 

f r 

that  pc-S  E NP,  consider 

TO  show 
the  I~c~ll-d~t~~lnil~isti~ ~~1px-ifhrn: “OH  input 
.  1’  . x,  reject  if IX I>  n.  Guess  and  verify  k  distinct  members  of  IJ:’  ;() S”‘.  Accept 
is in  NP  since  S  E NP. 
the 

ifI x  is distinct  from  each  of  the  k  elements.”  This  algorithm 
it  is  easy  to  see  that  if  k  <Q(H), 
input  is  accepted 
By  hypothesis, 

iff s  @S. 
there  exist  p-time  functions  $  and  II such  that 

is  accepted  and  if  k  = c-&r j, then 

the  input 

pc-s  -‘ c(,t, S 

(via!:), 

SAT  sdib S 

(via  t’~ ). 

Define  for  each  IZ, k  :I  0  the  function 

/,,,k : (0, 

l)*  -+ (n,  1)” where 



<!-- pdf-page: 11 -->
Cansequences of non -uniform conditions 

297 

Clearly  L,k  is  p-time  computable 
wherex’uJ= 

2  is easy  to  compute. 

Suppose  n  and  k  satisfy 

assuming 

that  the  set-union 

function 

(x, y ) I+  z 

(‘)  i”k 

=  max(ixl:  3G,  IGl s IFI, x  E l;(G)} 
=cs(n) 

so 

it  is  not  hard 

to  F.  Then 
(For  G  e SAT 

to  see  that  G&  SAT  and  IGI s  1~1 implies 
implies 

implies  6(G)  c  co-S  and  x E /f(G)  n  co-S 

with  respect 
f,t.k(G)  C_ S. 
0”  .  1’  . s  E PC-S  and 
implies  fn,k (G)  g  S.  Hence  {G  E co-SAT:  JGI s  IF/> scan  S  (viaf,&.  Assuming 
for  all  G,  1~1 a  ~G(,I and 
if  the  search  of  Theorem 
conducted  on  F  usingf,,,k  to  compute 
Furthermore, 
only  depends  on  g,  Ir  and  S)  such  that  for  all  F, IZ and  k  satisfying 

labels,  the  correct  declaration  on  F  is obtained. 
is a polynomial  q(.  ) (which 

the  proof  of  Theorem  3 shows  that  there 

.  1’  : X)C  S.)  Similarly,  G  E SAT 

IGj 6  IFI 
that, 
3  is 

iC,l,  we  conclude 

(C)  we have 

i(0” 

that 

and 

(D) 

q([Fl)  2  t1, k  and  at  most  q([FI)  nodes  are  visited  when 

fn.k  is used  to  compute 

labels  during  the  search  of F. 

the 

labels  of  nodes.  We  caI1  this  search 

We  now  claim  that  the  following  algorithm  can  check  if FE  SAT:  For  each  pair 
(12, k)  where  rz, k  <q(lFI),  we  conduct 
the  tree  search  of  Theorem  3,  using  f,,,~  to 
in 
compute 
to  visit  more  than 
Theorem  3  is  modified  only  in  stipulating 
that  stage.  If,  at  any  stage,  F  is declared  satisfiable,  we 
y(lFI)  nodes,  we  terminate 
if  a  stag,: 
halt  the  main  algorithm 
than  q(lFI) nodes  or  because  F 
terminates 
was  declared  unsatisfiable,  we  simply  go  to  the  next  stage.  If  all  the  stages  are 
completed  with  F  not  found  satisfiable,  we  declare 

arid  declare  F  satisfiable.  On  the  other  hand, 

the  (n, k)-stamp.  The  search 

that  if  it  ever  attempts 

either  because 

it  unsatisfiable. 

to  visit  more 

it  attempts 

II- 

It  is  clear  that  if  the  above  a!gorithm  declared  F  satisfiable, 

then  it  is so.  On  the 

if  F 

is  satistiable, 

other  h;lnd. 
the  satisfiability  of  F  will  be  declared 
before 

then  at  the  (II, k  )-stage  where  11, k  satisfies 

(C‘J, 

since  this  stage  visits  at  most  q{lFI)  nodes 

it  makes  a declaration  on  F. This  completes 

the  proof  of  Theorem  4. 

[3 

5.  Proof  of  Theorem  5 

We  shall  describe  a  non-deterministic 

F E SAT  iff  decry  computation 

search,  such  that,  on  an  input  formula  F, 
accepts.  This  search  always  halts  in  p*(lFi)  steps, 

thereby 

establishing  SAT  E co-NP. 

Let  co-SAT  sv  S  via  A4. We  will  perform 

the  tree  search  as  in  [4]  and  Theorem 
3 except  that  the  label  on  each  node  G  is computed  nondeterministically 
by  running 
M  on  G.  If  M  produces  no  output,  we  halt  the  search  and  accept.  If  II4  produces 
any  output, 
the  label  of  G  and  we  proceed  as  before.  As  in  the  proof 
of  Theorem  3,  we  can  show  that  at  most  p*(jFj)  nodes  will  be  visited. 

this  becomes 



<!-- pdf-page: 12 -->
298 

C.K.  Yap 

6.  Final remarks 

The  investigation  of  non-uniform  classes  gives  us  valuable 

insights  into  the 
uniform  ones.  For  instance,  Theorem  2  says  that  the  uniform  and  non-uniform 
hierarchies  are  either  both  finite  or  both  infinite,  a  somewhat  striking  connection 
since  the  non-uniform  hierarchy  contains  even  non-recursively  enumerable  sets. 
Other  non-uniform  conditions  can  be  studied.  An  interesting  one  which  deserves 
further  investigation  is the  following: 

A  k-genera;;?  Ear a set S (“) E (0,  I)”  is a circuit  which  computes  some  f  : (0,  l}k + 
(0,  1)” such  that  S(“)  is  the  range  of f,  We  say  S  has  small genewtors  if,  for  all  n, 
St”) has  a p*(n)-generator  of  size  <  p*(n).  Note  that  if S  has  small  circuits,  then 
it  has  small  generators.  The  converse  is unlikely. 

We  present  another  view  of  generators.  For  a  complexity  class  K,  let  NP(K) 

denote  the  class  of  languages  L  such  that,  for  some  A  E K  and  non-deterministic 
polynomial-time  oracle  machine  M, L 3s accepted  by M  using oracle  A.  For  instance, 
Xi+1 =NP(Ci),  i 20. 

We  would  like  to  examine  consequences  of  assuming 

L  has small generators. 

(*) 

Fact 1.  (*)  implies L E NP(&/poly). 

Proof.  From  (*)  we have,  for  some  a! E poly,  S E &, 

x EL 

iff 

(31,iy)(x  l  y  - a(x)ES) 

iff 

(31Xly)((~ l  y)  - cu’(x l  ykS’) 
(where  CY’(X . ~1) =  CY (x),  and  for  some  S’ E &) 

iff 

(314y)(x  - y E S’/cu’) 

which  proves  L  E NP(&/poly). 

q 

The  converse  of  Fact  1 is not  known. 
The  operators  NP  and  /poly  commute 

in  the  following  sense. 

Pact  2.  NP(Ei)/poly  = NP(xi/poly)q  i 3  “* 

iff 

(31,1,1)(x l  ar (x)  - y E L’) 

for  some  L’ECi 

iff 

(31,jy)(x  l  y c L”/d) 

for  some  L’k  &  and  cy ’ is given  by  Q ‘(s  - y ) =  a  (X ). 



<!-- pdf-page: 13 -->
Cmsequettce~  of non-uniform  conditions 

299 

‘ G ’ Let (Y E poly, L’ E Xi  and  L  E NP(&/poly)  s.t. 

x EL 

iff 

(3ixjy)(x l y E L’/a) 

iff 

(31xly)(x l  y  l Q! (x  s y) E L’). 

Define  cy’ by  ar’(n)=a(n) 

l  a(n  +  1) 9.. 

.  l  a(n  +p’(n)) 

for  some  suitable  poly- 

nomial p’(n),  and let 

L”={X  l (Z[,‘Z] ‘.  ..*Zp’{nj)‘y: 

IX1=n,IZilsp*(n), 

Iylq*(n), 

andx 

n  y  . z~,,l~t’}. 

Clearly, a ’ E poly and L” E Xi. Observe that 

(31,ly)(x  l  y  l  (u(x 

l  y)  E L’) 

iff  &j)(x 

9 d(x)  9 y EL”) 

iff  x  .cu’(x)~L”‘forsome  L’%NP(&). 

Thus L E NP(&)/poly.  EY! 

Thus  (*) 

implies  L E &/poly.  Combined  with  Theorem  2  we  concluds 

the 

foIlowing. 

Theorem.  If  every  set in l7,  has  a small  generator, then &  = l7,. 

Other  open  questions  raised  by  this  paper  are  the  following. 

(1)  Is the  converse  of  Theorem  2 true? 

(2)  Can  Theorem  4 be  made  a full  generalization 

of  Mahaney’s 

result? 

(3)  Related  to  (2), obtain  consequences  of  co-NP  <djs S, where  S  is sparse. 

(4)  What is the  analogue  of  advice if we  consider  circuit  depth  or  width  instead  of 
size? 

(5)  Conjecture :  Every  NP-complete 
recursive 
complete 

structure.  Note  that  the  Berman-Hartmanis 
implies  our  conjecture. 
sets  are  isomorphic 

set  (with  respect 

I 

to  So)  has  a  polynomial 
conjecture 

[3]  that  all  NP- 

Acknowledgment 

The  constructive 

criticisms  of  the  referees  have  been 

invaluable. 

I  am  indebted 

to  them  for  the  references  114,  151.  Our  Theorem  3  also  appeared 

in  [ 141. 



<!-- pdf-page: 14 -->
300 

C.K.  Yap 

References 

randomness 

complexity  of  NP-complete 

,71st S~,np.  FOCS  (1980,  pp.  348-359. 

and  intractibility,  Pruc.  Vflt AC&f  STOC 

L.  Adleman  and  K.  Manders,  Reducibility, 
(1977)  pp.  151-163. 
languages, 
P.  Berman,  Relationship  between  density  and  deterministic 
Stir  fwenlnt.  Co/l.  OPT Automatcl,  Lnngunges  ad  Progrclmmirtg,  Udine,  Lecture  Notes  in  Comput. 
Sci.  62  (Springer,  Berlin,  1978  I. 
I.... Berman  and  J.  Hartmanis,  On  isomorphisms  and  density  of  Nj)  and  other  complete  sets.  SIAM 
J.  Compur.  6t2,  (1977)  305-322. 
S.  Fortune,  A  note  on  sparse  compkte  sets,  SIAM  J.  Comp~rr. 8  ( 1979)  43 l-433. 
Jia-Wei  Hong,  On  similarity  and  duality  of  computation, 
N.  Immerman,  Upper  and  lower  hounds  for  first  order  expressibility.  21.~1 Syntp.  FOCUS (19801 
pp. 74-82. 
D.R.  Jefferson.  Type  reduction  and  program  verification,  CMU  Ph.D.  Thesis,  1980. 
K. M. Karp  and  R.J.  Lipton,  Some  co!mections  between  non-uniform 
Proc.  1.M  Aw.  ACMSTOC 
R.E.  Ladner,  N.A.  Lynch  and  A.  I_.. Selman,  A  comparison  of  polynomial 
Theoret.  Comput.  Sci.  1 (1975)  103-123. 
T.J.  Long,  A  note  on  co-sparse  polynomial 
Sci.  (1980)  submitted. 
S.R.  Mahaney,  Sparse  complete  sets  for  NP:  Solution  of  a  conjecture  of  Berman  and  Hartmanis, 
Proc. 21sf  Ann.  Symp.  FOCS  (1980  I pp.  54-60. 
A.R.  Meyer  and  M.S.  Paterson,  With  what  frequency  are  apparently 
MIT  Tech.  Memo.  126,  1979;  Theoret.  Comput.  Sci.,  to  appear. 
1,. J.  Stockmcycr,  The  polynomial-time 
E.  Ukkonen,  Two  results  on  polynomial 
to  appear. 
Y.  Yesha,  On  certain  polynomial-time 
Tech.  Rept.  152/81,  Department  of  Computer  Science,  Univ.  of  Toronto,  Canada,  1981. 

time  turing  complete  sets  for  NP,  J.  Compur.  Systems 

hierarchy,  Tl~wrtv.  Comp~.  Sci.  3  ( 19771  1-X. 

to  sparse  sets,  SIAM  J.  Comput., 

of  complete  sets  to  sparse  sets, 

intractable  problems  difficult, 

truth  table  reducibilities 

time  Turing  reductions 

t 19801 pp. X12-309. 

time  reducibilities, 

ar d uniform  complexity  classes. 


