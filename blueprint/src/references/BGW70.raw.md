<!-- generated-by: proofmatch local extraction -->
<!-- source-pdf-sha256: b9fb35a232afa44db5cfedc06bddceac01ca1307fe84b43c3fa07f1796f76b55 -->
<!-- extractor: pdfminer.six v20260107 -->

<!-- pdf-page: 1 -->
IOURNAL  OF COMPUTER AND SYSTEM SCIENCES:  4,  606--621  (1970) 

Time-  and  Tape-Bounded Turing Acceptors and  AFLs* 

RONALD V.  BOOK 

Aiken Computation Laboratory,  Harvard  University, 
Cambridge, Massachusetts 02138 

SHEILA A.  GREIBACH 

Department  of System Science,  University  of California, 
Los  Angeles,  California  90024 

AND 

BEN  WEGBREIT 

Aiken Computation Laboratory,  Harvard  University, 
Cambridge, Massachusetts 02138 

Received February  23,  1970 

Complexity classes of formal languages  defined  by  time-  and  tape-bounded  Turing 
acceptors  are  studied.  Sufficient  conditions  for  these  classes  to  be  AFLs  are  given. 
Further,  it is  shown  that  a time-bounded nondeterministic Turing acceptor need have 
only two storage  tapes. 

INTRODUCTION 

Much  recent work in automata  theory has focused on the  computational  complexity 
of functions  and  of languages.  In  particular,  families  of languages  have  been  defined 
by various  measures  of complexity  (among  others  see  1,  2,  8,  9,  11-14,  16,  19).  At 
the  same  time  researchers  in  formal  language  theory  have  attempted  to  discover 
unifying  concepts which  underlie  the  study of formal  languages  3,  10.  One  approach 
is  to  define  abstract  families  of languages  or  AFLs  as  collections  of languages  closed 

* These results  were announced at the Second ACM Symposium on the Theory of Computing, 
Northampton,  Massachusetts,  May,  1970.  This  research  was  supported  in  part  by  Air  Force 
Cambridge  Research  Laboratories,  Office  of  Aerospace  Research,  USAF,  under  Contract 
F19628-68-C-0029,  and by the Division of Engineering and Applied Physics,  Harvard University. 

6O6 



<!-- pdf-page: 2 -->
TURING  ACCEPTORS AND  AFLs 

607 

under  certain  operations  common  to  several  families  studied  extensively in  formal 
language theory.  This  viewpoint has  influenced the  study of formal languages to  the 
extent  that  in  studying  properties  of  formal  languages,  one  now  asks  if  these  are 
properties  of AFLs  or  at  least  of certain  types  of AFLs.  Here  we  study complexity 
classes of formal languages as determined by time- and tape-bounded Turing acceptors 
with the aim of showing sufficient conditions for these classes to be AFLs. 

In  Section  1 we  define the  classes  of languages to  be  studied by placing bounds on 
the amount of time (i.e., number of steps used) or the amount of tape (i.e.,  number of 
tape  squares  visited)  in  an  accepting  computation  by  (deterministic  or  nondetermi- 
nistic)  multitape  Turing  acceptors.  Certain  useful  "representation"  theorems  are 
established,  relating  these  families  to  certain  homomorphic  images  of the  family Q 
of  quasirealtime  languages,  the  family  CS  of  context-sensitive  languages,  and  the 
family  DetLBA  of  languages  accepted  by  deterministic  linear  bounded  automata. 
it  is  shown 
From  one  of these  representation theorems  and  results  on  Q  in  Ref.  2, 
that  a  time-bounded  nondeterministic Turing  acceptor  need  have  only two  storage 
tapes,  one  a pushdown store  and the  other  a  stack. 

In  Section  2  certain  lemmas  are  given  which  are  useful  in  establishing  sufficient 
conditions for  the  families studied  to  be  AFLs.  Some  of these  lemmas  are  directed 
toward clarifying the role of the operator which takes the family ~90~, I (those languages 
determined  by  machines  whose/~-complexity  is  bounded  by  function f  where  #  is 
time or tape)  to the family 5g(-~P~d )  =  .)k  ~-.1k,  where for any positive integer k and 
all real x, fk(x)  =  f(kx).  It is shown that there are two questions to be  asked in order 
that  ~ . . I   be  an AFL:  (i) what are  the  conditions such that  s 
is  an AFL ? and 
(ii) what are the conditions such that 5r176 
=  ~ . , I   ? It is shown that for the families 
is an AFL i f f  is superadditive (Vx Vy(f(x  +  y) ~  f(x)  +  f(y))) 
studied here, 5r 
and .5r 

=  -~'a..l i f f i s   semihomogeneous 

(Vk 1 >  0  3k 2 >  0 Vx  >  O(f(k,x)~  k2f(x)) ). 

In  addition,  it  is  shown  that  under  certain  conditions the  families  defined by  time- 
the  corresponding 
bounded  Turing  acceptors  are  principal  AFLs  4. 
results are given for the families defined by tape-bounded acceptors. 

In  Ref.  20 

1.  REPRESENTATION  THEOREMS 

We begin this section by formally defining multitape Turing acceptors so as to give 
a  precise  definition of the  families of languages  involved.  There  are  many different 
models of Turing  machines available  and  it is well-known that  many variations (e.g., 
one-way  vs  two-way)  do  not  affect  the  computational  power  even  with  respect  to 
time and tape bounds.  The  model given below was chosen to facilitate proofs of some 



<!-- pdf-page: 3 -->
6 0 8  

BOOK,  GREIBACH,  AND  WEGBREIT 

of  the  results  and  to  be  readily  comparable  to  the  definition  of  an  abstract  family  of 
acceptors  found  in  Ref.  3. 

DEFINITION  1.1.  An n-tape  Turing  machine  is a (n  +  6)-tuple 

M  =  (K,  2:,  F 1 ,...,  F n ,   3, q0, F,  n), 

where 

(1)  K,  2:,  F 1 ,...,  F n  are  finite  sets,  q0 ~ K,  F  _C K,  n  is  a  nonnegative  integer, 

and  E  is a  special  symbol not  in  Fi  for  1 ~< i ~   n; 

(2)  8  is  a  function  from 

K  X  (2: U  {e})  x 

(F  1 u  {e})  x 

"'"  x  (/-',  u  {e}) 

into  the  finite  subsets  of 

K  X  (F  1  X  {I,  0,  --1})  W/~1"  U  {E} 

x 

" ' "   X  (.F n  X  {1,  0,  --1})  U  -/"n*  t..) {E}.  1 

M  is deterministic  if for all q ~ K,  Ai  e  Fi  U  {e}, 

(3)  3(q,  e, A 1 ,...,  An)  :~  4'  implies  3(q,  a,  A x ,...,  An)  ----- r  for  all  a  E 2:,  and 

(4) 

for  all a  e  27 tA {e}, #8(q,  a,  A 1 ,...,  An) ~<  1. 3 

DEFINITION  1.2  A  configuration  of  M  =  (K,  X,/'1  ,...,  F n ,   3, q0,F,  n) 

is  a 

(2n  -k  2)-tuple  (q, w, Yl  ,..., Yn  ,  il  ,...,  in),  where 

(1)  q ~ K ,   w E Z * ,  

(2) 

for  1<~  k<~  n, y k E P k *   and0~<  ik~<  lYk  1.3 

Notation  1.3.  We  define  a  relation  w-- between  configurations  as  follows: 

(i)  Let  (q, aw, Yl ,..., Yn,  il,.-.,  in)  be  a  configuration,  a  ~ X  k.) {e}. 

Let  (q',  a x ,...,  an) be  in  8(q,  a,  A 1 ,...,  An).  T h e n  

(q,  aw, Yx  ,..., Y ,   ,  il,...,  in)  e -   (q',  w, Yl',...,  Y , ' ,  Jl  ,..., J~) 

if for  each  k,  1 ~< k ~< n,  either 

(1)  A k e F k ,  

(r~  =  (B,i),  Yk  =  x A ~ y ,   Yk'  =  x B y ,  

ik  = 

I x  I §  1,  O<~jk  = 

i k + i ~ < l y k l o r  

(2)  A k   =  e  =  Yk  ,  ak  =  zk  e  Fk*, y~'  =  zk  ,  andjk  --    zk  I or 

x F o r   a  set  A,  A *   is  t h e   m o n o i d   with  identity  e  freely  generated  b y   A.  A +  =  A * A .  

F o r   a  finite  set  S,  let  # S   be  t h e   cardinality  of  S. 

s  F o r   a  string  w,  I w    is  t h e   l e n g t h   of w. 



<!-- pdf-page: 4 -->
TURING ACCEPTORS AND  AFLs 

609 

(3)  A k e F k , a k - - - - z k e F k * , y k = x A k , i k = x l + l , y k ' = X z k , j k = x z ~  

o r  

(4)  Ak ~ F , ,   ak  ---- E, Yk  =  x A k y ,   ik  = 

  xAk  ,  y , '   =  e, Jk  =-  0. 

(ii)  Define the  relations  ~-  (m  ~  0) and  ~2_ as follows:  For  any configuration  C, 
C  ~  C.  I f C  o ~-  C I  ~--  .-.  ~-- Cm,  then  C O ~-  Cm,  and  if C o  ---- (qo,  w, e,...,  e, 0,...,  0) 
then  Co,  C 1 ,...,  C m is  called  a  m-step  computation  on  w;  if  Cm  ~  (q, e, e,...,  e, 0,...,  0) 
and  q ~F,  then  it  is  an  accepting  computation.  For  C1,  C~,  C 1 ~-  C,  if  C 1 ~ -   C 2 for 
some  m  >/0.  If  C o ~  C 1 ~--  ...  ~-- Cm  and  k  >  0  is  a  constant  such  that,  for  each 
configuration,  C~  =-  (q, % ,   Yl ,..., Yn,  il,...,  is),  every Yt  is  such  that    Yt  I ~< k,  then 
M  visits  no  more  than  k  tape  squares  on  any  one  of its  storage  tapes  in  the  computation 
c0,...,  c,~. 

(iii)  Finally,  define 

L ( M )   ---- {w ~ ~ *     ~ q ~ F,  (qo,  w, e .....  e, 0,...,  O) ~-  (q,  e, e,...,  e, 0,...,  0)}. 

T h e   functions  which  we  shall  use  as  upper  bounds  on  the  amount  of  tape  or  the 
amount  of time  used  in  a  computation  or  on  the  amount  of erasing  a  homomorphism 
may  perform  are  total  functions  which  are  real-valued  functions  of  a  single  real 
variable.  Each  such  function  f  has  the  following  properties: 

(i) 

i f x   ~> 0,  t h e n f ( x )   >~ 0; 

(ii) 

for  some  constant  t f / >   0  and  all  x  >~ t l ,   f ( x )   >~ x. 

We  shall  assume  that  any  function  used  in  this  paper  has  these  properties. 

DEFINITION  1.4.  An  online  multitape  Turing  acceptor  M  operates  within  time 
boundf  if for  each  input  string  w  accepted  by  M,  every  accepting  computation  of M 
on  w  has  no  more  than  max(I  w  ,  f(I  w  ))  steps.  Define  T I M E ( f )   ~  {L(M)    U 
is  a 
nondeterministic  multitape  Turing  acceptor  which  operates  within  time  bound  f} 
and  D e t T I M E ( f )   ---- {L(M)  I M  is  a  deterministic  multitape  Turing  acceptor  which 
operates  within  time  bound f}. 

For  any  function f  and  any  constant  k  >  0,  the  methods  of  Refs.  8  and  2  can  be 
applied  to  show  that  T I M E ( k f )   =  T I M E ( f ) .   T h e   methods  of Ref.  8 
can  be  applied 
to  show  that  DetTIME(k-f  +  i)  ---- D e t T I M E ( f )   where  i  is  the  identity  function, 
i(x)  ~-  x,  and  for  any  function  g  and  all  x,  (g  +  i)(x)  ~- g(x)  +  x. 4 T h e   languages 
accepted  in  quasirealtime  by  nondeterministic  multitape  Turing  acceptors  form  the 

v--n 

For  any real number x,  x  is  the  least  integer  greater  than  or  equal  to  x,  and  x  is  the 
greatest  integer  less  than  or  equal  to  x.  For  any  function  f,  r-~ is  the  function  given  by 
r~(x)  =  ~ 

is  the  function  given  b y f ( x ) =  

f(t~x). 

and f 



<!-- pdf-page: 5 -->
610 

BOOK,  GREIBACH,  AND  WEGBREIT 

family  Q  --- TIME(i)  2.  The  family of realtime  definable languages  of  Ref.  14 
the family DetTIME(i). 

is 

DEFINITION 1.5.  A  multitape Turing  acceptor  M  operates  within  tape  bound f  if 
for each input  string w accepted by M,  every accepting computation of M  on w visits 
no  more  than  max(  w  I,ft  w  I))  tape  squares  on  any  one  of its  storage  tapes.  Define 
TAPE(f)  =  {L(M)  I M  
is  a  nondeterministic  multitape  Turing  acceptor  which 
operates  within  tape  bound  f}  and  DetTAPE(f)  =  { L ( M ) M  
is  a  deterministic 
multitape  Turing  acceptor which  operates within tape  bound f}. 

For  any  function  f  and  any  constant  k  >  0,  T A P E ( h f ) ~ - T A P E ( f )   and 
DetTAPE(f)  =  DetTAPE(kf)  16.  As  shown  in  Refs.  11,  16  when  considering 
TAPE(f)  or  DetTAPE(f),  we  need  only consider Turing  acceptors with  one storage 
tape.  The context-sensitive languages  form the  family CS  =  TAPE(i)  and  the  family 
of  languages  accepted  by  deterministic  linear  bounded  automata  is  the  family 
DetLBA  =  DetTAPE(i). 

The  definition  of  acceptance  by  a  nondeterministic  Turing  acceptor  differs  from 
the  usual  one  in  that  we  require  all  accepting  computations  to  meet  the  appropriate 
condition instead  of simply requiring the  existence of some computation which meets 
that  condition.  If the  bounding  function is  the  appropriate  generalization of the  real- 
time  countable  functions  of  Ref.  18  or  the  constructable  functions  of  Ref.  16 
to 
nondeterministic  machines,  the  definitions  are  equivalent  in  the  sense  that  the  same 
families are  defined. In  Section 2 we  discuss  the  invariance of our  results  with  regard 
to variations on the definitions of acceptance. 

We  now  establish  certain  "representation"  theorems  for  the  families  T I M E ( f ) ,  

TAPE(f),  and  DetTAPE(f). 

DEFINITION 1.6. 

If h  : 27* --* A*  is  a homomorphism, L  _C 27*, and f  is  a function 
such  that  for  some  k  >  0  and  all  w 6L,    w  14  kf(  h(w)),  then  h  is f-bounded  on L. 
For  any  family .LP of languages 5 and  any  function f,  the  image  of ~  under f-bounded 
erasing is HIoL,r   =  {h(L)  fL  ~ .LP and h is a homomorphism which is f-bounded onL}. 

THEOREM 1.7.  For  any  function  f,  T I M E ( f )   =-  HIQ  .  That  is,  a  language  L  is 
accepted  by  a  (nondeterministic)  multitape  Turing  machine  which  operates  within  time 
bound f  if and only if there is a quasirealtime  language L'  and a homomorphism  h  which is 
f-bounded on L'  such that h(L')  =  L. 

Proof.  First we show that T I M E ( f )   _C HIQ.  Let M  ---- (K, X, F 1 ,..., F~, 5, q0 ,F, n) 
be  a  n-tape  Turing  acceptor  which  operates  within  time  bound f.  Let  d  be  a  new 

5  W e   a s s u m e  

that 

(i)  ifL ~ .L a, then there is a finite alphabet 27 such thatL  _C 27", and 
(ii)  there exists L ~ .Z such that L  ~  4. 



<!-- pdf-page: 6 -->
TURING  ACCEPTORS  AND  AFLs 

611 

symbol  not  in  Z,  let  Z a  =  Z  tA {d},  and  let  /~a : Za*  ~  s   be  the  homomorphism 
determined  by defining ga(d)  =  e and ga(a)  =  a  for a  ~ s 

Let  M '   =  ( K ,   Za  ,  1"1 ,...,  F,~ ,  3',  qo , F,  n),  where  for  any 

(q,  a 1,...,  an)  6  K  X  (F 1 k/{e})  X  "'"  X  ( F  n  k)  {e}), 

{ 3(q,  a,  al  ,...,  o,), 
3'(q,  a,  al  ,...,  an)  =  13(q,  e,  al  ,...,  %), 

if  a  e  S 
if  a  =  d 
if  a z e  

Note that  the  symbol d  serves  as a  " d u m m y   s y m b o l " - - M '   advances  the  input  tape  on 
scanning  d  in just  those  cases where  M  executes  an  e-move. 

tza(w),  so  t~aL(M') 

It  is  immediate  that  M  accepts  an  input  string  w'  if and  only if M '   accepts  some  w 
with  w'  = 
=  L ( M ) .   A  computation  of  M '   which  accepts  w  is 
simply an imitation  of a computation of M  which accepts I~a(w). M '   advances the  input 
at  each  step  so  that  any  computation  of  M '   which  accepts  w  has  exactly    w    steps. 
This  means L ( M ' )   is  a  quasirealtime  language.  Since  M  operates  within  time  bound 
f,  the  imitated  computation  of m  on  tza(w)  has  no  more  than f(/~a(w)) 
steps.  Thus 
  w  4   f( 

I~a(w)l)  so that/z a is f-bounded  on L ( M ' ) .   Hence L ( M )   ~  HIQ  . 

We  now  show  that  HIQ    C  T I M E ( f )   Let  L  _C X*  be  a  quasirealtime  language 
and  let  h  : Z*  --+ A*  be  a  homomorphism  which  is f-hounded  on L.  Let  d  be  a  new 
symbol  not  in  A,  let  A a  =  A  k) {d},  and  let  va  : Aa*  --~ A *   be  the  homomorphism 
determined  by  defining  va(d)  =  e  and  va(a)  =  a  for  a  6 A.  Let  g  : X *   --,-  Aa*  be  the 
homomorphism  determined  by  defining  g(a)  =  h(a)  if  h(a)  ~  e  and  g(a)  =  d  if 
h(a)  ---- e.  Let L o =  g(L).  Since  g  is  nonerasing,  L  6  Q,  and  Q  is  an  A F L ,   L o 6  Q  2. 
Since h i l l   =  vaLo 
o n L o .   Thus  it  is sufficient to  show that  vaLo  E T I M E ( f ) .  

a n d g   is nonerasing,  h f-bounded  o n L   implies  that  va is f-bounded 

Since L o E Q,  there  is  a  nondeterministic  multitape  Turing  machine 

M  =  (K,  A a ,   1"1,...,  I n , 8 ,   q o , F , n )  

which  accepts  L 0  and  which  operates  within  time  bound  i.  Let 

M '   =  (K,  A,/"1  ,...,  F , ,   3', q0, F,  n), 

where for any (q,  F 1 ,...,  _P,) ~ K 

(cid:141) 

(Px  u  {e})  (cid:141) 

...  (cid:141) 

(F n u  {e}), 

8 ' ( q , a , a  1 .... , a , ) =  

t3(q,  a,  a 1 ,...,  a,), 
I3(q,d,  cr 1,...,a.), 

if  a  E A 
if  a =  

e. 

Note that  M '   executes  an e-move in just  those  cases where  M  advances  the  input  tape 
upon  scanning  the  input  symbol  d. 

It is immediate thatL(M')  =  vaiL(M)  =  vaL0.  A computation of M '   which accepts 



<!-- pdf-page: 7 -->
612 

BOOK,  GREIBACH,  AND  WEGBREIT 

input  string  w  is  simply  an  imitation  of  a  computation  of  M  which  accepts  some 
%  ~ v~t(w) (~ L(M).  M  operates  within  time  bound  i  so  that  any computation of M 
which  accepts %  has  exactly i(I w01  =  I Wo I steps,  and thus  any computation of M' 
steps  for  some  w o ~ v~l(w)nL(M).  Since  Va  is 
which  accepts  w  has  exactly  1% 
f-bounded  on L o ~  L(M),  there  is  a  constant  k  such  that  for  any  w' ~L 0 =  L(M), 
I w'l  ~< kf(I  v~(w')l). Thusforanywo~v~l(w)  c~L(M),  1%   ~< kf(  va(Wo)l) =  kf(  w  I). 
Hence  M'  operates  within  time  bound  kf  and L(M') ~ TIME(kf)  =  TIME(f),  so 
that vaLo  ~ TIME(f). 

In the proof of the Theorem 1.7, the construction of the new machines involves only 
changing the way the  input was advanced.  No  new tapes were added.  Thus  from the 
Theorem  1.7  and  the  results  in  Ref.  2  characterizing  the  family Q,  we  obtain  the 
following: 

THEOREM 1.8.  For  any function f,  the following  are equivalent: 

(i)  L ~ T I M E ( f ) ;  

(ii)  L  is the f-bounded homomorphic image of a quasirealtime language; 

(iii)  L  is the f-bounded homomorphic image of the intersection of three context- 

free languages; 

(iv)  L  is  accepted  by  a  nondeterministic one  stack,  one  pushdown  store  auto- 

maton operating within time bound f. 

The  methods used in the proof of Theorem  1.7 generalize to the families TAPE(f) 
and  DetTAPE(f),  and thus we obtain Theorem  1.9 below.  Results closely related to 
Theorem  1.9  were  established  in  Ref.  7  but  the  definition  of  a  homomorphism 
being f-bounded  on a  language L  differs from Definition  1.6 in  that  the  function f  is 
applied to the other side of the inequality. 

THEOREM 1.9.  For  any  function  f,  T A P E ( f ) =   HrCS    and  D e t T A P E ( f ) =  

HIDetLBA. 

The  "representation" Theorems  1.7 and  1.9 are very useful since they allow one to 
use results obtained for families of the form Hf.2~,  where S~' is an arbitrary family of 
languages  or  is  an  AFL.  This  is  the  tactic  used  here,  i.e.,  we  shall  establish  certain 
results  concerning  families  of  languages  of  the  form  HI~ a  and  then  apply  these 
results  to  the  families  TIME(f),  TAPE(f),  and  DetTAPE(f)  since  they  can  be 
expressed as HfQ,  H1CS,  and HIDetLBA, 

respectively. 

We  note  that  the  representations  T I M E ( f )   =  HIQ, 

etc.,  are  deceptive  at  first 
glance. I l L   is any recursively enumerable set, then for some L'  ~ Q  and some homo- 
morphism h, h(L')  = L   (see Ref. 2).  In this case the amount of erasing thath performs 
on words of L'  is not restricted.  Here we wish to restrict the amount of erasing that h 
performs on all words of L'  by the  same function which bounds the  number of steps 
in an accepting computation of a Turing  acceptor M  such that L(M)  -~ L.  To  obtain 



<!-- pdf-page: 8 -->
T U R I N G   ACCEPTORS  A N D   AFLs 

613 

the  equation  h(L')  =  L  where  h  is f-bounded  on L',  it  is  necessary  to  construct L' 
in such a  way that  substrings that will be  erased  do not get too long.  This  is the  role 
played by the  requirement  in Definition  1.4 that  for every w eL(M),  every accepting 
computation of M  on w has no more than max(  w l, f(I  w ))  steps. In the construction 
used  in  the  proof  of  Theorem  1.7, the  number  of  "dummy"  symbols  in  words  in 
L'  cannot  become  too  large.  Similar  remarks  hold  for  the  cases  of  Tape(f)  and 
DetTAPE(f). 

DEFINITION 1.10.  A 

if  for  every  x,  y  ~> 0, 
f(x)  +  f ( y )   ~  f ( x   +  y).  A  function f  is semihomogeneous if for every k I  >  0 there  is 
a k 2 >  0  such that for all x  >/0, f(klx )  ~  k2f(x ). 

is  superadditive 

function  f 

It is straightforward to verify the following properties of any superadditive function f: 

(i)  f  is nondecreasing; 

(ii) 

for every integer k  >  0  and every x  >  0, kf(x)  <~ f(kx); 

(iii) 

for  every  Xl,...,x n  >~ O,f(xl)  +  ""  +f(xn)  <~ f(x~  +  ""  +  xn). 

Note  that  a  nondecreasing  function f  is  semihomogeneous  if and  only  if there  is  a 
k 1 >  1 such that for some k S >  0 and all x  ~  O,f(klX )  <~ k2f(x ). 

Notation  1.11.  For any function f  and any integer k  >  0, fk is the  function given 

byfk(x)  =  f(kx). 

It is immedeate that for any functionf and any constant k  >  0, i f f  is superadditive, 

so is f , ,   and if f  is semihomogeneous, so isfk. 

DEFINITION 1.12.  For any function f, define 

6:TIME(f)  =  U  TIME(A), 

6:DetTIME(f)  =  U  DetTIME(fk), 

k 

k 

6:TAPE(f)  =  U  TAPE(A), 

and 

6:DetTAPE(f)  =  U  DetTAPE(fk). 

k 

For any family ~q~ of languages and any function f,  S:H:~ 
From Theorems  1.7 and 1.9, the following is immediate: 

COROLLARY 1.13.  For  any function f, 

k 

=  U, H:~~. 

and 

6aTIME(f)  =  S#H:Q, 

6:TAPE(f)  =  6:H:CS, 

6:DetTAPE(f)  =  ~5'~H:DetLBA. 



<!-- pdf-page: 9 -->
614 

BOOK,  GREIBACH, AND  WEGBREIT 

We  note  that  representation  theorems  similar to  Theorem  1.7  and  Corollary  1.14 

may be obtained for time-bounded AFA (as defined in Ref. 3). 

DEFINITION 1.14.  An  abstract family  of languages (AFL)  is  defined in  Ref.  3 

to 

be a nonempty collection Lg of languages such that 

(i)  at least one language in 5r  is nonempty; 

(if) 

ifL e ~L~, there is a finite vocabulary I  such thatL  _C I * ;  

(iii)  5e  is  closed  under  union,  concatenation,  Kleene  + ,   intersection  with 
regular sets, nonerasing homomorphic mappings, and inverse homomorphic mappings. 

The  smallest AFL containing a family ~  of languages is denoted by ~ ( ~ ) .   An AFL 
&e is principal  if there is a language L  such that .LP =  ~-(L) (see  Ref.  4). 

In Section 2 we investigate the problem of finding sufficient conditions o n f  so that 
TIME(f),  TAPE(f),  etc.,  will  be  AFLs.  As  suggested by results in  Refs.  3  and  7, 
it  is  suitable  to  carry  out  this  task  by  asking two  questions:  (i)  What  conditions are 
sufficient for f  so  that  5~ 
5aTAPE(f),  etc.,  will  be  AFLs ?,  and  (if)  what 
conditions  are  sufficient  for  f  so  that  T I M E ( f ) =   5gTIME(f),  T A P E ( f ) =  
5PTAPE(f),  etc. ? In  addition, we  give sufficient conditions such that  T I M E ( f )   will 
be  a  principal  AFL. In  this  case  it  is  appropriate  to  ask for sufficient conditions on f 
such that if 5gTIME(f)  is an AFL, then 5~TIME(f)  is a principal  AFL. 

We may summarize the main results of Section 2 as follows: 

(i) 

If  f 

is  a  superadditive  function,  then  5eTIME(f),  5gTAPE(f),  and 

5eDetTAPE(f)  are AFLs (Theorem 2.9). 

(if) 

If  f 

is  a  semihomogeneous  function,  then  5 a T I M E ( f ) =   TIME(f), 

SgTAPE(f)  ~-  TaPE(f),  and  5PDetTAPE(f)  =  DetTAPE(f)  (Corollary  2.6). 

(iii) 

I f / i s   a  superadditive  running time,  then  5gTIME(f)  is  a  principal  A F L  

(Theorem 2.16). 

2.  TURING ACCEPTORS AND AFLs 

In this section we shall establish results connecting the families TIME(f), TAPE(f), 
DetTAPE(f)  with AFLs.  We begin with  a general result about families of languages 
of the form HIs 

. 

LEMMA 2. l.  For any function f  and any family s  of languages ~9~ 

C ~-(H/~a). 

Proof. 

If L 1 e  5PHs5~', 

so there is a 
h o m o m o r p h i s m   h 1 : ~'*  ~  A *  and  a  language L 2 6 ~ '   such  that  hl(L~)  =  L 1 and  h i 
t  >  0  such  that  for  every  w e Lz, 
is  a 
is  fk-bounded  on  Lz.  Thus 

then there is a k  >  0  such that L 1 e Hlks 

there 



<!-- pdf-page: 10 -->
TURING  ACCEPTORS  AND  AFLs 

615 

I w  I ~  tf~(I hl(W))  =  tf(k  t ht(w)l).  Let c be a symbol not in A and let A~  ---= A v  {c}. 
Let  h~:A*  ~ A ~ *   be  the  homomorphism  determined  by  defining  h~(a)=  ac ~-1 
for  a  ~ A.  Let  Lz  =  h~(hl(L~) )  ---- {ale ~-~ "'"  a~c ~-~ l ai ~ A, al  "'"  a~ ~  ht(L~)}.  If 
hz  : X* --+ A~*  is  the  homomorphism  determined  by  defining  hz(a)  =  h2(ht(a))  for 
a ~ L', then  for any w ~ Z*,    hz(w)  ---- k  I hl(w)l,  so  for any w ~Lz, 

I w  I  ~ 

tf(klhl(w)l) 

= 

tf(I  hs(w)l). 

Thus  h 8 is f-bounded on L~ so h3(L~) ~ H I Z   .  Since ~'(h,~) 
homomorphism,  h~(h3(L2))=  h~(h2(hl(L2))=  hi(L2)=  La  is  in  ~(H~Z). 
S~H,Z 

is closed under inverse 
Thus 

_C o~-(Hr 

COROLLARY 2.2.  For any function f  and any family  Z  of languages, 5z-(S~H1Z)  = 
is  the  smallest  AFL  containing 

,  i.e.,  the  smallest  AFL  containing  SfHf@ 

J"(HIZ) 
H~Z. 

Proof. 

If  ~1  and  Z 2  are  families  of  languages  such 

that  ~  C ~ ,  

then 

o~(Zl) _C ~,~-(Z2). Thus H I Z     =  H&Z  _C 5eH~Z 
By Lemma  2.1,  .SeHIZ    _C ~-(HIZ) 

so  that 

implies ~-(H~Z)  C~'(5~H~.U). 

,.~'-(~H~Z)  C .~(,~'(H,Z)) 

=  .~(H,Z). 

COROLLARY 2.3.  For  any function  f  and  any family  Z  of  languages,  if  H r Z     is 

an AFL,  then  5 f H I Z     =  H I Z   . 

Proof.  By Lemma  2.1,  6 f H I Z     C #T(HIZ)  =  H I Z   .  But 

H I Z     =  HI~Z    C 5aHIZ 

so that  SaHIZ  =  H I Z   . 

As shown by Theorems  1.7 and  1.9 and by Corollary 1.13, the results of Lemma 2.1 
and  Corollaries 2.2  and  2.3  could  be  restated in  terms  of T I M E ( f )   and  5eTIME(f), 
TAPE(f) and  5eTAPE(f),  and  DetTAPE(f)  and  5PDetTAPE(f).  Thus  in obtaining 
conditions  for  T I M E ( f ) ,   TAPE(f)  or  DetTAPE(f)  to  be  AFLs,  the  families 
5aTIME(f),  .Y~TAPE(f), and  5eDetTAPE(f),  respectively, play a vital role. 

LEMMA 2.4.  For  any  semihomogeneous function f  and  any family  Z  of  languages, 

6eH,Z 

_C HeZ  . 

Proof. 

IfL 1 ~ 5eHIZ, 

then for some k 1 >  0, L x 6 H&IZ  .  Thus there is a homo- 
morphism  h  and  a language L~ 6 Z  such that h(L2)  =  L 1 and  h  is fk -bounded  on L~, 
and  so  for  some  constant  t  >  0  and  all  w ELz,  I w    ~< tfkl(I h(w))  =  tf(k x   h(w)l). 
is  semihomogeneous,  there  is  a  constant  k 2  such  that  for  all  x  >  0, 
Since  f 
f(kxx )  <  kj(x).  Thus for every w ~Lz,    w    <  tf(h 1   h(w)l)  ~  tk2f(  h(w))  so that h 
is f-bounded  on L 2 .  Hence, L 1 ---- h(L~) ~ H I Z   . 



<!-- pdf-page: 11 -->
616 

BOOK,  GREIBACH~ AND  WEGBREIT 

COROLLARY 2.5.  For any semihomogeneous function f  and any family  ~q~ of languages, 

6aHs.c.~  =  H1s176 

Proof.  This is immediate from Lemma 2.4 if we notice that 

H,.W 

---- H,I.~ a  _C  U  H,~.W  =  S~H,s 

k>~l 

We  use  Theorems  1.7  and  1.8  to  express  the  preceding  corollary  in  terms  of 

dgWIME(f) and TIME(f),  etc. 

COROLLARY 2.6.  For  each  semihomogeneous  function  f,  6PTIME(f)  =  TIME(f), 

~eTAPE(f)  =  TAPE(f),  and 6aDetTAPE(f)  =  DetTAPE(f). 

Proof.  We give the proof for 6aTIME(f); the others are similar. By Corollary 1.13, 
6aTIME(f)  =  6eH~Q  and by Theorem  1.7, T I M E ( f )   =  HfQ.  By Corollary 2.5, 
HIQ  =  6eH,Q 

so 6 e T I M E ( f )   =  T I M E ( f ) .  

In  order  to  show  that  TIME(f),  etc.,  forms  an  AFL  when f  is  sufficiently well- 
behaved, we rely on a result of Ref. 6.  The result as stated here is in a slightly different 
form from that stated in  Ref.  6 
in that we use the  ":T"  operator here and we define 
the operator " H / '   in a somewhat different manner.  However, it is immediate that the 
proof in  Res  6  can  be altered to the form of the result stated below.  Alternatively, 
it  is not  difficult to  verify this  result directly. 

THEOREM 2.7.  For any superadditive function f  and any AFL ~a, ~ H s ~  

is an AFL. 

COROLLARY 2.8.  For any superadditive semihomogeneous function  f  and any AFL ~o, 

Hf.~ a  is an AFL. 

From  Corollary 1.13 and  Theorem  2.7  and  from the  fact that  the  families Q,  CS, 

and DetLBA form AFLs, the following is immediate. 

TI~OREM 2.9.  For any superadditive function f,  the families ~ T I M E ( f ) ,   ~ T A P E ( f )  

and ~ D e t T A P E ( f )   are AFLs. 

COROLLARY 2.10.  For  any  superadditive  semihomogeneous  function  f,  the  families 

TIME(f),  TAPE(f),  DetTAPE(f)  are AFLs. e 

It is not difficult to verify Theorem 2.9 and Corollary 2.10 directly, and in doing so 
the  superadditivity o f f   is  not  necessary in  the  cases  of TAPE(f)  and  DetTAPE(f). 
However,  in  order  to  show  that  T I M E ( f )   is  closed  under  Kleene  + ,   the  super- 
additivity o f f  appears  to be  necessary. 

e This  result  has  been  noted  independently  by  O.  Ibarra  for  the  cases  of  T A P E ( f )   and 

D e t T A P E ( f ) .  



<!-- pdf-page: 12 -->
TURING ACCEPTORS AND A F L s  

617 

In  Ref.  1 

it is shown that results similar to  Theorem 2.9 and  Corollary 2.10  hold 

for the families of languages generated by time-bounded grammars. 

There  are several variations on the definitions of the families TIME(f),  TAPE(f), 
and DetTAPE(f)  such that Theorem 2.9 and  Corollary 2.10 still hold. In  particular, 
these results hold if we define T I M E ( f )  to be any of the following families of languages: 

(i) 

( L ( M )   I for  each  w eL(M),  there  exists  an  accepting computation of M  on 

w which has no more than max(  w I,f(  w 1)) steps}; 

(ii)  {L(M)   for each input string w, every computation of M  on w has no more 

than max(I w I,f(  w I)) steps}; 

If T I M E ( f )   is defined by either (i) or (ii)  above, it is straightforward to verify that 
Theorem  2.9  and  Corollary  2.10  hold  for  the  families  T I M E ( f )   and  S:TIME(f). 
However, these families may not be equal to the family H:Q 
so that the various results 
(or  H:~~  may not  be  used.  I f f   is  the  appropriate  generalization 
concerning H:Q 
of a realtime countable function 18, 
then defining T I M E ( f )   either by (i) or (ii) yields 
the family H:Q 

so that all the proofs hold in the form given here. 

In  the  definitions (i)  or (ii)  above, if the bound on the  number of steps  is replaced 
by the same bound on the number of tape squares visited, then  we  obtain  the  corre- 
sponding definitions of TAPE(f)  or  DetTAPE(f).  In  this  case,  it  is  straightforward 
to  verify that  Theorem  2.9  and  Corollary 2.10  hold  for  the  families  TAPE(f)  and 
S#TAPE(f),  and  for  DetTAPE(f)  and  5:DetTAPE(f).  These  families may  not  be 
equal to  the  families H:CS  or  H/DetLBA,  but  equality can  be  assured  i f f   is  the 
appropriate generalization of a constructable function 16. 

We now consider the case of DetTIME(f).  I f f  is superadditive, then DetTIME(f) 
is  closed  under  marked  union,  marked  concatenation,  marked  Kleene §   and  inter- 
section with regular sets 5,  and 5eDetTIME(f) is dosed under all of these operations 
as  well  as  inverse  homomorphism.  Thus  if f  is  superadditive,  then  S:'DetTIME(f) 
is a pre-AFL 5,  so that 5:DetTIME(f) is an AFL if and only if H(SPDetTIME(f))  C 
YDetTIME(f),  where H  =  Hi (again, i is the identity function). It is straightforward 
to  show  that  for  any  function  f,  any  integer  k  >~  1,  and  any  constant  t  >  1, 
H(DetTIME(fk))  _C 5:DetTIME(t,f)  where  for  all  x,  t,f(x) 
~-  t~f(x).  Thus  for 
any  t  >  1,  H(S:DetTIME(f))  _C 5:DetTIME(t,f). 
Suppose  f  has  the  property 
that  for  some  ~ >  0  and  all  sufficiently large  x,  (f(2x)/f(x))  >/(1  +  E) z.  Then  for 
any t  >  1 there is an integer k t  ~  1 such that for all sufficiently large x 

fk,(x)  =  f ( k t x )   >~ t*f(x)  ---- t,f(x), 

and hence 

DetTIME(t,f)  _C DetTIME(fk,) _C ~9~ 

Thus we have the following: 

571/4/6-8 



<!-- pdf-page: 13 -->
618 

BOOK,  GREIBACH, AND  WEGBREIT 

THEOREM 2.11. 

I f  f  is  a  superadditive function  such  that for  some  E >  0  and  all 

sufciently  large x,  (f(2x)/f(x))  >1 (1  +  ,)~,  then  StDetTIME(f)  is an AFL. 

We now consider special  classes  of functions and compare the families of languages 

defined. 

L e t f b e  a superadditive function such that for some ~ >  0 and all sufficiently large x, 
(f(2x)/f(x))  >/(f(x))'Y  Then  for  any integer  t / >   1,  there  is  an  integer  k  such  that 
for  all  sufficiently  large  x,  f k ( x ) = f ( k x ) > ~   (f(x))'.  Define  the  function  f '   by 
if(x)  -= (f(x))'.  Then we have 

DetTIME(fl)  _C StDetTIME(f), 

TIME(fl)  _C StTIME(f), 

DetTAPE(fl)  _C StDetTAPE(f), 

and 

TAPE(fl) _c StTAPE(f). 

Since for sufficiently large x,f(x)  >~ x  and sof~(x)  >~ f(x),  this implies the following: 

LEMMA 2.12. 

I f   f  is  a  superadditive  function  such  that  for  some  ~ >  0  and  all 
sufficiently  large  x,  (f(2x)/f(x))  >/(f(x))',  then for  every  integer  t  >~ 1,  the following 
hold: 

(i)  StDetTIME(fl)  =  StDetTIME(f), 

(ii)  ~'(TIME(fl))  =  StTIME(fl)  =  StTIME(f)  =  ~-(TIME(f)), 
(iii)  oq~(TAPE(fl))  =  StTAPE(fl)  =  StTAPE(f)  =  ~(TAPE(f)),  and 
(iv)  ~(DetTAPE(fl) =  StDetTAPE(fl) =  StDetTAPE(f) = ~ ( D e t T A P E ( f ) ) .  

THEOREM 2.13.  Let f  be  a  superadditive function  such  that for  some  ~ >  0  and  all 
by  a 

sufciently  large x,  (f(2x)/f(x))  >~ (f(x)).  Further,  let  f  be  constructable  16 
deterministic  Turing machine.  Then ~(DetTAPE(f))  =  ~(TAPE(f)). 

Proof.  The  results  of  Ref.  15 

can  be  applied  to  show  that  TAPE(f)C__ 
that  ~(TAPE(f))_C~(DetTAPE(f2)).  By  Lemma  2.12, 
DetTAPE(f2), 
~(DetTAPE(f~))  =  ~-(DetTAPE(f)).  Thus  ~ ( T A P E ( f ) )   =  ~-(DetTAPE(f)), 
since  DetTAPE(f)  __C TAPE(f)  implies  o~-(DetTAPE(f)) _C oqr(TAPE(f)). 

so 

Remarks  2.14. 

(i)  The  question  of  whether  the  inclusion  DetLBA C  CS  is 
proper  is  a  long-standing  open  question.  If  DetLBA  =  CS,  then  for  any  f, 
DetTAPE(f)  =  TAPE(f),  since  HIDetLBA   =  HICS  .  Theorem  2.13  shows that 
even if DetLBA  :~  CS, for certain functions the AFL defined by TAPE(f)  is exactly 
the  AFL  defined by  DetTAPE(f),  i.e., ~ ( T A P E ( f ) )   ---- o~(DetTAPE(f)). 

(ii)  Note that the family DetLBA is an AFL which is closed under intersection 
and which contains the context-free languages. Hence Q  C  DetLBA 2,  and so for any 
f, 
St(TIME(f))  _C 
St(DetTAPE(f)).  Thus  for  superadditive  f,  #Z-(DetTIME(f))_C~-(TIME(f))__ 
o~-(DetTAPE(f))  _C o~(TAPE(f)). 

T I M E ( f )   =  HIQ    _C HIDetLBA   ---- DetTAPE(f) 

and 

7 For example, f(x)  =  2 x is such a function. 



<!-- pdf-page: 14 -->
TURING  ACCEPTORS  AND  AFLs 

619 

(iii) 

If we consider functions f  such  that  for some k  >  1 and all sufficiently large 

x,  (f(2x)/f(x))~  k I{~,  then  it  is  straightforward  to  show  that  ~ ' ( T I M E ( f ) ) =  
~'(DetTIME(f))  =  ~a~'(TAPE(f))  =  ~'(DetTAPE(f)). s 

(iv)  An  interesting  open  question  is the  relationship  between ~'(DetTIME(f)) 
and ~-(TIME(f)).  For the identity function i, ~'(DetTIME(i))  =  H(DetTIME(i))  = 
Q  =  TIME(/)  =  ~'(TIME(i)).  Also  for  large  functions,  as  above,  the  families  are 
the same. However, it is not known in general whether the inclusion ~-(DetTIME(f)  _C 
~-(TIME(f))  is proper. 

(v)  The  results  of  Ref.  8 

on  imitating  multitape  on-line  Turing  acceptors 
with  single  tape  off-line  Turing  acceptors  can  be  applied  here  to  show  that  for  any 
function f,  if L  ~ 6e(DetTIME(f),  then L  is  accepted  by  a  single  tape  off-line  deter- 
ministic Turing  acceptor M  such that  for some k  ~/1,  M  operates within time-bound 
f~.  I f f   satisfies  the  hypothesis  of  Lemma  2.12,  then  by  (i)  of  Lemma  2.12,  we  see 
that  L  ~ 6eDetTIME(f)  if  and  only  if L  is  accepted  by  a  single  tape  off-line  deter- 
ministic  Turing  acceptor M  such that  for some k  ~/1,  M  operates within  time bound 
fk (cid:12)9 Clearly,  this  result  can be  extended to  nondeterministic  machines. 

We  now  show  that  under  certain  conditions  T I M E ( f )   is  a  principal  AFL.  The 

corresponding  results  for  TAPE(f)  and  DetTAPE(f)  are  established  in  Ref.  20. 

DEFINITION 2.15.  A  function  f  is  a  running  time  (deterministic  running  time)  if 
there  is  a  multitape  Turing  machine  (deterministic  multitape  Turing  machine) 
M  such  that  for  any  input  w to  M,  every resulting  computation  of M  on  w  requires 
precisdyf(I  w l) steps. 

THEOREM 2.16. 

I f  f  is a  superadditive  running  time, then  S~TIME(f)is  a principal 

AFL. 

The  proof  depends  on  the  fact  that  for  any  function  g,  if L  is  in  TIME(g),  then 
there  is  a  Turing  acceptor  which  (i)  accepts  L,  (ii)  operates  within  time  bound  g, 
and  (iii)  has just two storage tapes  (Theorem  1.8).  Using this fact, the proof is a slight 
modification  of the  proof of Theorem  1 of Ref.  20;  hence  it  is not  given here. 

COROLLARY  2.17. 

l f  f  is  a  superadditive  running  time  and  T I M E ( f )   is  an  AFL, 

then TIME(f)  is a principal AFL. 

COROLLARY  2.18. 

I f   f 

is  a  superadditive  semihomogeneous 

running  time,  then 

TIME(f)  is a principal AFL. 

8 An  example  of such  a  function  is 

..a~ 

f ( x )  

=  X  x" 

. 



<!-- pdf-page: 15 -->
620 

BOOK, GREIBACH, AND  WEGBREIT 

Consider  the  family  . ~ D e t T I M E ( f ) .   Suppose  f  is  a  superadditive  deterministic 

running  time  such  that  for  some  E >  0  and  all  sufficiently  large  x,  (f(2x)/f(x)) 
max((1  +e)~,  (f(x))').  Then  5 f D e t T I M E ( f )  
is  an  A F L   (Theorem  2.11)  and 
5 ~  
tape  off-line  deterministic  Turing 
is  a  single 
acceptor  which  operates  within  time  bound  fk}  (Remark  2.14,  v).  In  this  case,  the 
methods  used  to  establish  Theorem  2.16  can  be  applied  to  yield  the  following: 

=  u k { L ( M )   I M  

THEOREM 2.19.  Let f  be a  superadditive  deterministic  running  time such  that for  some 
(f(Zx)/f(x))>~  max((1  +  E) x,  (f(x))E).  Then 
>  0  and  all  sufficiently 

large  x, 

5 ~ D e t T I M E ( f )   is a principal  AFL. 

Remark  2.20.  Let f  be  a  superadditive  deterministic  running  time  and  let  g  be 
the  function  defined  for  all  x  by g(x)  =  21~x). Cook  21  has  shown  that  a  language L 
is accepted by a nondeterministic  auxiliary  pushdown  acceptor  which  operates  within 
tape  b o u n d f   if and  only i f L   is accepted  by a  single-tape  off-line deterministic  Turing 
acceptor  M  such  that  for  some  k  >  0,  M  operates  within  time  bound  gk.  Thus 
Theorem  2.19  shows  that  the  family  of  languages  accepted  by  nondeterministic 
auxiliary  pushdown  acceptors  which  operate  within  tape  bound  f  forms  a  principal 
this  shows  that  the  family  of  languages  accepted  by 
A F L .   By  results  of  Ref.  21, 
nondeterministic  (deterministic)  stack  automata  is  a  principal  AFL. 

REFERENCES 

1.  R.  BooK,  "Grammars  with  time  functions,"  Ph.D.  thesis,  Harvard  University,  1969. Also 
appears  as  Mathematical  Linguistics  and  Automatic  Translation,  Report  No.  NSF-23, 
Aiken  Computation  Laboratory, Harvard  University,  1969. 

2.  R. BOOK AND S. GREIBACH, Quasirealtime  languages,  Math.  Systems Theory 4 (1970), 97-111. 
3.  S. GINSBURG AND S. GREIBACH, Abstract families of languages, Amer. Math.  Soc. Mem. No. 87 

(1969),  1-32. 

4.  S.  GINSBtTRG AND S.  GaEmACH, Principal  AFL, SDC  Technical Report,  1969. 
5.  S.  GINSBUaG, S.  GREmACH, AND J.  HOPCROFT, Pre-AFL,  Amer.  Math.  Soc.  Mem.  No. 87 

(1969),  33-40. 

6.  S.  GINSBUR6 AND J.  HOPCROFT, Images of AFL under certain  families  of homomorphisms, 

SDC  Technical Report,  1969. 

7.  S.  GaEmACH AND J.  HOPCaOFT, Independence of AFL operations,  Amer.  Math.  Soc.  Mem. 

No.  87 (1969), 41-51. 

8.  J.  HARTMANIS AND R. STEARNS, On the computation complexity  of algorithms,  Trans.  Amer. 

Math.  Soc.  (1965),  385-406. 

9.  J.  HARTMANIS AND  R.  STEARNS, Automata-based  computational  complexity,  Information 

Sciences  1 (1969), 173-184. 

I0.  J.  HOPCaOFT aND  J.  ULLMAN, An  approach  to  a  unified  theory  of automata,  Bell  System 

Tech.  J.  46 (1967),  1763-1829. 

11.  J.  HOPCROFT AND  J.  ULLMAN, "Formal  Languages  and  their  Relation  to  Automata," 

Addison-Wesley, Reading,  Mass.,  1969. 



<!-- pdf-page: 16 -->
TURING ACCEPTORS AND  AFLs 

621 

12.  J.  HOPCROFT AND J.  ULLMAN, Some  results  on  tape-bounded Turing machines,  J.  Assoc. 

Comput.  Much.  16 (1969),  168-177. 

13.  P. M. LEwis, II, R. STEARNS, AND J. HAr~TMANIS, Memory bounds for recognition or context- 
free  and  context-sensitive  languages,  1965 IEEE  Conference  Record  on  Switching  Circuit 
Theory  and Logical  Design,  191-202. 

t4.  A.  L.  ROSEN~ERC, Real-time  definable  languages,  J.  Assoc.  Comput.  Much.  14  (1967), 

645-662. 

15.  W.  SAviwcrt, Relationships  between nondeterministic and  deterministic tape  complexities, 

J. Comput.  System Sci.  4 (1970), 177-192. 

16.  R.  ST~AVa~S, J.  HARTMANIS, AND P.  M.  LEWIS, II, Hierarchies  of memory limited computa- 
tions, 1965 IEEE Conference Record on Switching Circuit  Theory and LogicaI Design,  179-190. 
17.  B.  WEGBREIT, A generator of context-sensitive  languages,  J.  Comput.  System  Sci.  3 (1969), 

456-462. 

18.  H.  YAMADA, Real-time  computation  and  reeursive  functions  not  real-time  computable, 

IEEE  Trans.  Electron.  Comput.  11  (1962), 753-760. 

19.  P.  R.  YOUNC, Toward  a  theory  of  enumeration,  J.  Assoc.  Computing  Much.  16  (1969), 

328-348. 

20.  R.  BOOK, S.  GREmACH, O.  IBARRA, AND B. WEGBaEIT, Tape-bounded Turing acceptors  and 

principal AFLs,  J.  Comput.  System Sciences 4 (1970), 622-625. 

21.  S.  COOK, Variations  on pushdown machines,  Proc.  First ACM  Symposium on  Theory  of 

Computing, May,  1969, 229-230. 


