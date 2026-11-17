<!-- generated-by: proofmatch local extraction -->
<!-- source-pdf-sha256: c8033d2fd70553fb96969a3e3923f8ca9112f6e635667da8a3cecd473f5c5bc3 -->
<!-- extractor: pdfminer.six v20260107 -->

<!-- pdf-page: 1 -->
JOURNAL OF COMPUTER AND SYSTEM SCIENCES: 4,  177-192  (1970) 

Relationships Between Nondeterministic 
and  Deterministic Tape Complexities* 

WALTER  J.  SAVITCH 

Department  of  Applied  Physics  and  Information  Science, 
University  of California,  San  Diego, La  Jolla,  California  92037 

Received August  29,  1969 

The  amount  of storage needed to simulate a  nondeterministic tape bounded Turing 
machine  on  a  deterministic  Turing  machine  is  investigated.  Results  include  the 
following:  Theorem. A  nondeterministic L(n)-tape  bounded  Turing  machine  can  be 
simulated  by  a  deterministic  [L(n)]2-tape  bounded  Turing  machine,  provided 
L(n)  >~ log2 n.  Computations of  nondeterministic machines  are  shown  to  correspond 
to  threadings  of certain mazes.  This  correspondence is used  to  produce a  specific set, 
namely the  set of all  codings of threadable mazes,  such  that,  if there is  any  set which 
distinguishes nondeterministic tape  complexity classes  from  deterministic tape  com- 
plexity classes, then this is one such set. 

INTRODUCTION 

A  well-known  open  problem  in  the  theory  of  formal  languages  and  computational 
complexity is to decide whether or not there exists a nondeterministic context-sensitive 
language,  that  is,  to  decide  whether  or  not  there  is  a  set  which  is  accepted  by  a  non- 
deterministic  linear  bounded  automaton,  but  is  accepted  by  no  such  deterministic 
machine.  In  this  paper,  we  give  some  partial  answers  to  a  natural  generalization  of 
this problem. We attempt to answer the following question:  "Given a nondeterministic 
tape bounded  Turing machine which accepts a set .4, how much addition storage does a 
deterministic Turing machine require to recognize .4 ?" 

More  specifically,  we  show  that  any  nondeterministic  L(n)-tape  bounded  Turing 
machine  can  be  simulated  by  a  deterministic  [L(n)]2-tape  bounded  Turing  machine, 
provided L(n) ~  logz n.  Thus,  in  particular,  every  context-sensitive  language  can  be 
recognized  within  deterministic  storage  n 2,  where  n  is  the  length  of  the  input.  As 
a  corollary of the  proof of this  theorem,  we  get  that  if a  context-sensitive  language  is 

* This  work  is  based  on  a  portion  of  the  author's  doctoral  dissertation  in  the  Department 
of Mathematics  of the  University of  California,  Berkeley.  Most  of the  results  were  announced 
in  [9].  Part  of  this  research  was  done  while  the  author  was  a  National  Science  Foundation 
Graduate  Fellow. 

177 



<!-- pdf-page: 2 -->
178 

SAVITCH 

accepted  by  a  nondeterministic  linear  bounded  automaton  within  polynomial  time, 
then  the  language  is  accepted  by  a  deterministic  Turing  machine  within  storage 
n log 2 n.  It  is  also  shown  that if nondeterministic  and  deterministic  tape  complexity 
classes are equal for "small"  functions, then they are equal for "large" functions. 

The notion of a maze is formalized and computations of nondeterministic machines 
are related to threadings of certain mazes. This relation is used to obtain a specific set, 
namely  the  set  of codings  of threadable  mazes,  such  that,  if there  is  any  set  which 
distinguishes  nondeterministic  tape  complexity  classes 
from  deterministic  tape 
complexity  classes,  then  this  is  one  such  set.  That  is,  there  is  a  nondeterministic 
Turing machine which accepts the  codings of threadable mazes within storage log S n. 
Also,  if there  is  a  deterministic Turing machine which  accepts them  within  the  same 
storage,  log S n,  then,  for  every storage  function L(n)  ~  log S n,  any  nondeterministic 
L(n)-tape  bounded  Turing  machine  can  be  stimulated  by  a  deterministic L(n)-tape 
bounded  Turing  machine. 

MACHINE MODEL 

The  device studied  in this  paper is the multitape Turing  Machine.  In  the termino- 
logy of  3, 
it  is  a  Turing  machine  with  finitely many two-way infinite  storage  tapes 
and a read only input tape provided with end markers. We shall give only an informal 
definition  of the  device.  A  multitape  Turing  machine  (hereafter  called  simply  Turing 
machine)  is  a finite state  control attached  to  a  read  only input  tape  and  finitely many 
read/write storage tapes.  The  tapes  are divided into squares.  Each  square of a storage 
tape  is  capable  of holding  one  symbol  from  the  finite  storage  tape  alphabet  _P. The 
input tape will always contain a finite string w of symbols from the finite input alphabet 
Z.  The  string  w  is  separated  by 'two  symbols  not  in  Z  called  left  and  right  end 
markers.  Each tape has  one head  communicating with  the  finite control. 

At  any  point  in  time,  each  head  will  scan  one  square  on  its  tape  and  the  control 
will  be  in  one  state.  Depending  on  this  state  and  the  symbols scanned  by the  heads, 
the machine will, in one step, assume another state, overwrite a symbol on the scanned 
square of each of its storage tapes,  and then shift some of its heads (including possibly 
the input head) either left or right one square. The finite control is designed so that the 
input  head  will  never  leave  the  segment  of tape  containing  w  and  the  end  markers. 
The machine is said to be deterministic  if there is only one possible action at each step. 
It  is said to be nondeterministic  if there are finitely many possible actions at  each step. 
Some states are distinguished and called accepting states and one state is distinguished 
and called the initial state.  We say the deterministic machine Z  accepts the input string 
w  over 27 if Z  enters  an  accepting state  after finitely many  steps,  when  started  in  the 
initial state, with all storage tapes blank, w on its input tape and its input head scanning 
the  left  end  marker.  The  definition  is  the  same  in  the  ease  Z  is  nondeterministic 



<!-- pdf-page: 3 -->
NONDETERMINISTIC  AND  DETERMINISTIC  TAPE COMPLEXITIES 

179 

except that  we merely require that there be a possible finite sequence of steps  leading 
to an accepting state, starting from the initial configuration described above. 

DEFINITION.  Suppose L(n)  is  a  function  on  the  natural  numbers,  Z  is  a  Turing 
machine  (deterministic  or  nondeterministic),  and  A  is  a  set  of strings  over the  input 
alphabet of Z.  Z  is said to accept the set A  within storage L(n) provided that 

(i)  for  each  string  w  in  A,  there  is  at  least  one  possible  computation  of Z  which 

accepts w and  in which each storage tape  head scans at most L(  ,0  )  squares,  and 

(ii)  Z  accepts no string not in A.    w    is the length of the string, w. 

In this paper we are considering only the growth rates of storage functions. That is, 
for our  purposes,  the  storage  functions L(n) and EL(n) are the  same,  for any constant 
E >  0. This identification of functions follows from the fact that our Turing machines 
are  allowed  arbitrary  finite storage tape  alphabets.  Thus,  any Turing  machine which 
operates in storage L(n) can be modified to operate in storage eL(n) and still accept the 
same  set of tapes.  (See,  for example,  3.)  We  assume the  reader is familiar with  such 
tape  reduction techniques. 

In what follows, it will sometimes be convenient to assume that the storage functions 

are  "nice".  The  niceness  condition  we  want  is  that  the  functions  be  measurable  4. 

DEFINITION.  A  function L(n)  is  said  to  be  measurable if  there  is  some  Turing 
machine with just one storage tape such that,  given any input of length n, the machine 
will halt after a computation in which the storage tape head scans exactlyL(n) squares. 
Apparently,  all  common  storage  functions L(n)  >/log 2 n are  measurable. In partic- 

ular, any polynomial in n and log z n is measurable. 

DETERMINISTIC  SIMULATION  OF  NONDETERMINISTIC  TURING  MACHINES 

THEOREM  1. 

If a  set,  A,  is  accepted by  a  nondeterministic Turing  machine,  Z/~, 
within  storage  L(n)>~  log s n,  then  A  is  accepted  by  some  deterministic  Turing 
machine, ZD,  within storage L(n)  2. 

Proof.  The theorem is proved by exhibiting an algorithm whereby ZD can simulate 
the computations of Z N . The  algorithm is similar to that used by Lewis, Stearns,  and 
Hartmanis  7 
to show that  every context-free language is accepted by a deterministic 
Turing machine within storage (log~ n) 2. 

Suppose  the  Turing  machine  ZN  has  k  storage  tapes,  storage  tape  alphabet  F, 
and  internal  state  set  Q.  Let  A  =  Q w  F  t.) {1, 2,  *,  ~},  where  ~ and  (cid:12)9  are  two  new 
symbols.  An  instantaneous description (ID)  of  Z N  is  a  string  over  A  of  the  form 



<!-- pdf-page: 4 -->
180 

SAVITCH 

pq  *  u 1 ~ v 1 *  u,  ~ v,  (cid:12)9  ""  (cid:12)9  u k  .~ vk  ,  where p  is a number  in  dyadic  notation 1 indicating 
the  position  of  the  input  head  of  Z N ,  q  is  an  element  of Q  indicating  that  the  finite 
control  of  Z N  is  in  state  q,  and  ui,  vi  are  elements  o f / ' * ,   i  ---- 1, 2,...,  k.  ui  ~ v,  is 
interpreted  to  mean  that  uivi  is the  contents  of the  ith  storage  tape  of Z N and  the  head 
on  this  tape  is  scanning  the  first  symbol  of string  v~.  Thus,  except  for the contents  of 
the  input  tape,  an I D   of Z N is a complete  description  of a configuration  of Z N . 

Since  Z N  accepts  the  set  A  within  storage  L(n)  >1 log 2 n,  it  follows  that  for  each 
string  w  of  length  n  accepted  by  Z N ,  there  is  a  computation  of  Z N  accepting  w  in 
which  every  I D   has  length  not  exceeding  cL(n).  Furthermore,  since  each  I D   is  of 
length  at  most  eL(n),  the  computation  need  take  no  more  than  2 c'Ll~) steps,  c  and  c' 
are  constants  depending  only  on  Z N and  not  on  the  input  w. 
We  first give the  algorithm  for the  case: L(n)  is measurable. 
Given  an  input  of  length  n,  Z D  initializes  its  computation  by  dividing  one  of  its 
followed 
storage tapes  into  c'L(n) 
+  1  blocks  (called  tags),  each  capable  of  storing  either  0  or  1.  This  it  can 
by  c'L(n) 
easily  do  if L(n)  is  measurable.  y 
is  the  largest  integer  not  exceeding  y.  Note  that 
each  register  is  capable  of  holding  any  I D   o f   Zn  in  which  the  nonblank  portion  of 
every storage tape is at mostL(n).  Z D has a second  storage tape for scratch work. 

+  1 blocks  (called  registers),  each  of length  eL(n), 

T h e   idea  of the  algorithm  is  as  follows.  ZD  has  the  string  w  as  input.  In  the  course 
of  the  algorithm,  Z 9   will  consider  two  I D ' s   I,  I "   stored  in  particular  registers.  For 
a  prechosen  m,  it  will  need  to  check  if,  with  input  w,  Z N can  in  2 m steps  change  its 
configuration  from  I 
to  I".  Furthermore,  Z D  will  have  to  perform  this  task  using 
only  m  registers.  Zo  proceeds  as  follows.  It  runs  through  (in  a  systematic  way)  all 
I D ' s   I '   of  Z N and  for  each  I ' ,   checks  to  see  if there  is  a  computation  of at  most  2 m-1 
steps  from I  to I ' ,   and  a  computation  of at  most  2 "*-1 steps  from I '   to I".  Z D needs  one 
register  to  keep  track  of  the  I ' ,   leaving  it  with  m  --  1  registers.  So  Z D  has  reduced 
the task  of simulating  2 m moves of Z N using  m registers  to  simulating  2 m-1 moves of Z N 
using  m 
- -   1  registers.  Zo  then  reduces  each  computation  of 2 m-1  steps  to  two  com- 
putations  of 2 m-2 steps.  Z D continues  to  reduce  the  length  of the  computations  it  need 
check  until  it  need  only  check,  for  appropriate  I D ' s  11 and  I2,  whether,  with  input  w, 
Z N can  in  one  step  go  from 11 to 1,,,.  This  it  can  easily  do  using  zero  storage.  Now  if 
there  is  any  accepting  computation  of  Z N ,  then  there  is  one  which  accepts  in  2 c'Lcn) 
steps.  So  ZD  can  simulate  this  computation  using  c'L(n)  registers  or  about  L(n)  2 
squares  of storage tape. 

We  now  define  some  notation  for  a  formal  statement  of  the  algorithm.  Since  I D ' s  
are  strings  over  a  finite  alphabet,  A,  they  may  be  considered  to  be  integers  in  m-adic 
notation,  where m is the number  of symbols in A.  More precisely,  i f d   ~  {a I  , a,,  ,...,  a,~} 
then  the  string  a~a~,_~  ""  a~o will  represent  the  number  Xj~o tim.  We  will  not  &sun- 
guish  between  a  string  and  the  number  it  represents. 

/ r  

(cid:12)9 

(cid:12)9 

j 

. 

. 

. 

. 

The  string  d ~ d , - t   "'"  do  over  the  alphabet  {1, 2} is the  dyadic  representation of the  number 

E~. o di2 ~. 



<!-- pdf-page: 5 -->
NONDETERMINISTIC AND  DETERMINISTIC TAPE COMPLEXITIES 

181 

DEFINITION. 

If I  and  I '   are  I D ' s   of Z N  and  if  Z N can  in  one  step,  with  input  w, 
pass  from  configuration I  to  configuration I',  or  if I  =  1',  then  we  will  write  I  ~-~ 1'. 
In the algorithm  we will test i f I   ~-~ 1' is true  for arbitrary strings/,  I '   over A. If either I 
o r I '   is not an I D   of Z N ,   then  the test  fails. 

In  the  following  algorithm,  x~  denotes  the  contents  of  the  i-th  register  and  T~ 
denotes  the  contents  of the  i-th  tag  1  <~ i  <~ c'L(n)  +  1.  ZD  has  a  string  w  as  input 
and  all  references  to  computations  of Z N mean  computations  of ZN under  the  input  w 
and  in  which  the  nonblank  portion  of each  work  tape  remains  at  most L(I w  t) squares 
long. At any point in the  computation  of Z o ,   if  Ti  =  1, then  there  is a computation  of 
Z N from  the  start  I D   to  x~. 

ALGORITHM FOR  MACHINE Z D 

Summary  of Notation 

~o  is  the  input  string. 

n 

r 

is  the  length  of w. 

is  the  least  integer  such  that  r  ~  c'L(n). 

is  such  that,  with  w  as  input,  if Z N accepts  w  at  all,  then  Z N accepts  w  in  2 ~'L~n~ 

c' 
steps. 

I 0  is  the  initial  I D   of Z N . 

N  is  the  largest  integer  whose  m-adic  representation  can  be  stored 

in  a  register. 

xi  is the  contents  of the  i-th  register. 

T~ is the  contents  of the i-th tag. 

DO (Initialize).  Compute  r  and  set  up  the  r  +  1 registers and tags.  For i  =  1, 2,...,  r 

set x~ +--  1 and  Ti  ~-  0.  Set  x~+ 1 ~-- 1 o (the  initial  ID)  and  T~+ t  ~ 

I. 

D1  (Test).  If  each  T~  =  1,  go  to  D3.  Otherwise,  let j  be  the  smallest  index  such 

that  Tj  =  0.  Test:  For  some  index  h,  Th  =  1 and  xh ~-~ xj. 

Yes:  Go  to  D2. 
No:  Go  to  D3. 

D2  (Clear  Storage)  ( j   as  in  D1).  If  x~  is  an  accepting  ID,  A C C E P T .   Otherwise, 

set  T~ +--  1  and  for  i  =  1,2,...,j  --  1  set  xi ~  1  and  T~ ~-- 0.  Go  to  D I .  

D3  (Back Track).  If xi  =  N  for each i  ~< r,  R E J E C T .   Otherwise,  let  k  be the  smal- 
I,  2,...,  k  --  1 

lest  index  such  that  x~  4:  N.  Set  x~ ~-- x~  +  1,  T~ ~-- 0,  and  for  i  = 
set x~ ~--  1,  T~ ~  0.  Go to D 1. 

Clearly the algorithm works within storage c"L(n)  2, where c" is a constant depending 
the  constant  can be  reduced  to one.  A  simple 

only on  ZN (cid:12)9 By standard  techniques  3 

57x/412-7 



<!-- pdf-page: 6 -->
182 

SAVITCH 

induction  on  the  number  of  steps  completed  shows  that  if  Z D  accepts  an  input  w, 
then  the  nondeterministic  machine  Z,v  does.  Thus,  it  will  suffice  to  show  that  ZD 
accepts  all  strings  that  ZN  accepts.  T o   show  this,  we  need  some  preliminary  lemmas. 
T h e   lemmas  are  easier  to  state  in  case  the  machine  does  not  stop  when  it  accepts. 
So  assume  D2  (Clear  Storage)  has  been  modified  to  omit  the  first  line  ( " I f   x~  is  an 
accepting ID,  A C C E P T " ) .   We  shall say Z n  is in configuration 

<Xl,  x~,...,  xr+l>,  < r l ,   T~ .... ,  r,+l> 

if it  is about  to  execute  D1,  and  the  contents  of the  registers  and  tags  are,  respectively, 
x i ,   x2 ,...,  X~+l and  7'1,  T 2 .....  T~+ 1 . 

LEMMA  1.  (For  modified  D2). 

For  each  index  i  (i  =  1, 2,...,  r)  and  each  integer  x 
(x  =  1, 2,...,  N )   if  at  some  time  in  a  computation  of  ZD  the  configuration  of  ZD  is 

<1,  1,...,  1, Xi+l, xi+~ .... , x~,  I0> , 

<0, 0,...,  0,  ri+x,  Ti+~ ,...,  T~,  1> 

(1) 

i 

for  some  xi+l, xt+~ ,...,  x~  and  some  Ti+l,  T~+z ,...,  T~,  then  at  some  later  time  the 
configuration  will  be 

<1,  1,...,  1, x,  Xi+I,  Xi+ 2 ,...,  Xr  ,  0>, 

(0,  0,...,  0,  T i + l ,   Ti+~ ,...,  T~,  1> 

(2) 

t 

or 

(1,  1,...,  1, x s , xs+l ,...,  x , ,  Io>, 

<0, 0,...,  0,  1,  Ti+ 1 ,...,  T , ,   1>, 

(3) 

j - t  

wherej  is the  least index  in (1) such  t h a t j   >  i and  Tj  =  0.  (If no s u c h j   exists,  then  (2) 
happens.) 

T h e   algorithm  is trying  to  establish  that  there  is a  computation  of Z N from  the  start 
to  the  left  of  x~.  So  the  lemma 

I D   to  xs.  It  is  trying  to  do  this  using  only  registr 
says that  Z D can get any I D   into  any  register,  if it needs  to. 

Proof.  A  formal proof would  use  induction  on  i  and  x.  We  list  some  representative 
configurations  in  a  computation.  This  should  make the  lemma clear.  Note  that  since N 
is  a  string  all  of whose  digits  are  the  same,  N  is  not  an  I D   and,  hence,  x  %- N  is  not 
true  for  any  integer  x.  Suppose  Zo  is  started  in  configuration  (1)  and  that  at  no  later 



<!-- pdf-page: 7 -->
NONDETERMINISTIC  AND  DETERMINISTIC  TAPE  COMPLEXITIES 

183 

time  does  Z o  assume  configurations  (3).  Z D  will  then  assume  the  following  con- 
figurations: 

(1,  1,...,  1, x  --  1; Xi+l  , xi+2  ,...,  x~,  lo) , 

(0,  0,...,  O,  Ti+l,  Ti+2 ,...,  Tr  ,  l )  

i - 1  

2 

(1,  1,...,  1, N,  x  --  1, xi+l,  xi+~ ,...,  Xr, Io), 

(0,  0,...,  O,  Ti  ,  Ti+l  ,  Ti+z  ,...,  Tr,  1) 

i--2 

where  7 " / =   0 

or 

I. 

( N ,   N,...,  N,  x  --  1,  X i + t ,   Xi+ 2  ,...,  X r ,   I 0 )  , 

(0,  0,...,  0,  T i ,   Ti+t,  Ti+2  ,...,  Z r ,   1) 

i--I 

i--1 

Finally,  via  D3,  Z v  assumes  (2)  as  desired. 

LEMMA  2.  (For  modified  D2).  Suppose  that  at  some  time  in  a  computation  the 

configuration  of Z n   is 

(1,  1,...,  1, x,  Xj+I, Xj+ 2  , . . . ,   X r ,   I 0 )   , 

(0,  0,...,  0,  T~,  Tj+I,  Tj+z ,...,  T~,  1) 

(4) 

j - I  

j - I  

with  Tj  =  0  and  any values for the x's and  remaining  T's.  I f  for some index  q,  Tq  =  1 
and  there  is  a  computation  of Z N  of  at  most  2 5 steps  from  xq to  x,  then  at  some  later 
time  the  configuration  of ZD will  be  (4)  with  Tj  =  1. 

T h e   lemma  says  that j  registers  are  sufficient  for  Z D  to  check  a  computation  of  2 5 

steps  of Z N .  

LEMMA  3.  (For  modified  D2).  Suppose  that  at  some  time  in  a  computation  the 

configuration  of  Z D  is 

(1,  1,...,  1, x~,  x~+ 1 ,...,  xj+~,, x,  xj+~+ 2 ,...,  x~, Io) , 

i - 1  
<0, 0,...,  0,  1,  I,...,  1, 0,  Tj+u+z,  Tj+~+ a ,...,  T~,  1> 

p+, 

(5) 

j - I  

p + l  

for  any  values  of the  x's  and  T's.  If for  some  index  q,  Tq  = 
l  and  there  is  a  computa- 
tion  of Z~  of at  most  2 j  steps  from  xq to  x,  then  at  some  later  time  the  configuration 
of  ZD  will  be 

(1,  1,...,  1, x,  x~+~+e,  x~+~+ 3 ,...,  x r ,   I0), 

J+P 

(0,  0,...,  0,  l,  Tj+~+2,  Tj+ao+3 ,...,  T~,  1). 

(6) 

J + p  



<!-- pdf-page: 8 -->
184 

SAVITCH 

Proof  of  Both  Lemmas.  Lemmas  2  and  3  are  basically  a  single  lemma  and  are 
proven simultaneously by induction  on j.  The  base case, j  =  1, is clear.  Assume both 
lemmas hold withj  replaced by j - -   1. We will show that  Lemma 2  holds forj. 

Suppose Z D is in  configuration  (4)  with  T~ =  0  and that  for sqme index,  q,  there  is 
a  computation  of Z~  from xq to  x  of at  most 2 ~ steps.  Decomposing this  computation 
from xr  to x, we get that  there  is  a y  such  that  there  are computations  of at  most 2 j-1 
steps  from x~ to y  and  from y  to  x.  By  Lemma  1,  it  follows that,  at  some  later  time, 
either  the  configuration of Z D is 

<1,  1 .... ,  1, y,  x, xj+l,  xj+ 2 ,...,  x~ , I0>, 

j-2 

<o, o,..., o, 
-2 

o, 

,...,  T,,  l> 

(7) 

with  Tj_ 1 =  0  or the  configuration is (4)  with  Tj  =  1.  Configuration  (4) with  Tj  ----- 1 
is  the  desired  outcome.  So  assume  Z D assumed  configuration  (7)  with  Tj_ 1 =  0.  By 
induction  hypothesis  on  Lemma  2,  it  follows  that  at  some  still  later  time  the  con- 
figuration  of Z D will be (7)  with  T~_ I  ----- 1. If we then  apply the  induction  hypothesis 
on  Lemma  3,  we  get  that  at  a  still  later  time the  configuration  of Z D will  be  (4)  with 
Tj  =  1.  So  Lemma  2  holds  for j.  Lemma  3  for j  is  established  in  a  similar  fashion. 
Thus,  the  induction  hypothesis  is  established  and  the  proof of both  lemmas  is  com- 
pleted. 

Using  Lemmas  1 and 2  it is easy to complete the  proof of the  theorem. Suppose the 
nondeterministie  machine ZN accepts w.  We  must  show  that  ZD  accepts w.  Since ZN 
accepts w,  there  is an  accepting ID,  x,  of Z N such  that  there  is a  computation,  with  zo 
as input,  of at most 2" steps from 10 (the initial ID of ZN) to x.  By Lemma  1, it follows 
that  ZD eventually assumes configuration 

(1,  1,...,  1, x, Io>, 

<0, 0,...,  0,  T~,  1> 

(8) 

r--1 

r - - I  

with  Tr  ----- 0.  By Lemma 2, it follows that at some later time Z o  will assume configura- 
tion  (8)  with  T,  =  1.  All  this  was  for  the  modified  D2.  The  unmodified  D2  will 
accept w rather than  set  T, +-- 1.  This  completes the  proof of Theorem  1 in  the  case: 
L(n) is measurable. 

IfL(n) is not  measurable, then the above algorithm must be altered,  since Zo cannot 
necessarily  mark  off  blocks  of  length  eL(n)  within  storage  proportionate  to  L(n)  2. 
However,  if ZD were  somehow given the  value  of L(n),  then  by the  above procedure, 
Zp.  could  determine  whether  or  not  Z~  accepts  the  input  w  within  storage L(n).  So 
ZD  operates  as  follows.  ZD  first  assumes  L(n)  =  1.  If  Z~r  accepts  within  storage 
L(n)  =  1,  then  ZD will  accept.  If Zs,  does  not  accept  within  storage  1,  then  ZD next 



<!-- pdf-page: 9 -->
NONDETERMINISTIC  AND  DETERMINISTIC  TAPE  COMPLEXITIES 

185 

assumes L(n)  =  2.  If Ztr  accepts  within  storage  2,  then  Z o  accepts.  If not,  then  Z D 
next assumes L(n)  =  3. Z D proceeds in this  manner trying  larger and larger values  for 
L(n).  If Ztr  accepts the input  w, then Z D will eventually find the correct value for L(n) 
and accept w within storage proportionate to [L(n)]L If ZN does not accept w, then ZD 
computes forever on input w. This completes the proof of Theorem 1. 

The  context-sensitive  languages  are  precisely  those  sets  accepted  by  nondeter- 
ministic Turing  machines  within  storage L(n)  =  n  (see, for example,  [3]).  So,  setting 
L(n)  ~  n  in Theorem  1, we get, 

COROLLARY  1.  Every context-sensitive language is accepted by some deterministic 

Turing machine within storage n z. 

Theorem  1 can be generalized as follows. 

THEOREM 2. 

If  a  set,  A,  is  accepted  by  a  nondeterministic  Turing  machine 
within  storage L(n)  and  time  T(n),  then  A  is  accepted by some  deterministic Turing 
machine  within  storage L(n) log 2 T(n). 

DEFINITION.  A  Turing  machine,  Z,  is  said  to  accept  a  set,  A,  within  storage L(n) 

and time  T(n) provided that 

(i)  for each w in A,  there is at least one computation of Z  which accepts w,  takes at 
most T(n) steps, and in which each work tape head scans at most L(n) squares, where n 
is the length of w, and provided that 

(ii)  Z  accepts no  string not  in A. 

Proof of Theorem 2.  An analysis of the proof of Theorem 1 shows that the algorithm 
uses  a  bound  on  the  storage  of  the  nondeterministic  machine  to  obtain  a  bound, 
namely  exponential  in  the  storage,  on  the  time  of the  nondeterministic  machine.  It 
then  marks  off  [log z T(n)]  blocks  of  storage,  where  T(n)  is  a  bound  on  the  time. 
Clearly, if the time bound were easy to compute, the algorithm could be modified to use 
it as the bound  on the time. We would then get Theorem 2. If the time function is not 
easy to  compute,  then  we  use  the  same  sort  of trick  as  that  used  for  nonmeasurable 
functions in the  proof of Theorem  1. 

COROLLARY 2. 

If  a  context-sensitive  language  is  accepted by a  nondeterministic 
Turing  machine  within  linear  storage  and  polynomial  time,  then  it  is  accepted  by 
some  deterministic Turing  machine within  storage n logz n. 

The  following  theorem  says  that  for  any  "well  behaved"  storage  function L(n), 
if every nondeterministic L(n)-tape  bounded  Turing  machine  can  be  simulated  by  a 
deterministic L(n)-tape bounded Turing machine, then for all larger storage functions 
nondeterministic and  deterministic tape  complexities are  the  same. 



<!-- pdf-page: 10 -->
186 

SAVITCH 

THEO~M  3.  Suppose  that  L(n)  and  H(n)  are  measurable,  that L(n)  is  monotone 
increasing and unbounded and that logan  <~ L(n)  <~ H(n),  for all n.  Let the function 
k(n) he defined as follows. For each natural number n, k(n) is the least natural number 
such  that  H(n)  <~ Lk(n). 

Suppose  further that for any set,  A,  if A  is accepted by a  nondeterministic Turing 
machine within storage L(n),  then  A  is  accepted  by  a  deterministic Turing  machine 
within  storage L(n).  It  then  follows that  for  any set,  B,  if B  is  accepted  by  a  non- 
deterministic  Turing  machine  within  storage  H(n),  then  B  is  accepted  by  a  deter- 
ministic Turing machine within storage Lk(n). 

The  theorem  is a  bit  stronger than it seems.  For  most common storage functions, 
L,  there  is a  constant c such that cLk(n)  <~ H(n)  <~ Lk(n), 
for all H  and  n.  Thus, 
in these cases,  the conclusion can be strengthened to say that  any set accepted within 
nondeterministic  storage  H(n)  can  be  accepted  within  deterministic  storage  H(n). 
In  particular, 

COROLLARY 3.  SupposeL(n) is a polynomial in log 2 n, n and : ,   for some constant c. 
Suppose  further  that  for  any set,  A,  if A  is  accepted  by  a  nondeterministic  Turing 
machine within storageL(n), then A is accepted by some deterministic Turing machine 
within storage L(n). 

It  then follows that for any measurable function H(n)  >~ L(n)  and any set,  B,  if B 
is  accepted  by  a  nondeterministic  Turing  machine  within  storage  H(n),  then  B  is 
accepted hy some deterministic Turing machine within storage H(n) 

Among other  things, the  corollary says that  if every context-sensitive language  is 
xccepted  by  a  deterministic  linear  bounded  automaton  (i.e.,  deterministic  Turing 
machine  with  storage bound  n),  then  nondeterministic and  deterministic tape  com- 
plexities are the same for all measurable tape bounds H(n)  >1 n. 

Proof of Corollary  3. 

It  is  easy to  check that  for  any such polynomial L(n), there 
is  a  constant  c  such  that  L(n)/L(n  +  1)  f> c  for  all  n.  So cLk(n)  <~ Lk(n)  --  1. 
k(n)  is  the  function  defined in  the  statement  of the  theorem.  By  definition of k(n), 
Lk(n)  --  1  ~< a(n).  So cLk(n)  <~ H(n). 

Assume the  hypothesis of the  corollary and suppose  B  is  accepted by a  nondeter- 
ministie Turing machine within storage H(n).  By the Theorem  3,  B  is accepted  by a 
deterministic Turing  machine within storage Lk(n).  So,  by standard tape  reduction 
techniques 3, 
it follows that B  is accepted by a deterministic Turing machine within 
storage cLk(n).  Finally,  since cLk(n)  <<. H(n),  this means  that B  is  accepted  by  a 
deterministic Turing machine within storage H(n). 

I ~ f   of  Theorem 3.  Assume the  hypothesis of the  Theorem  3  and  suppose  B  is 
a  set  accepted  by  a  nondeterministic  Turing  machine,  Zg,  within  storage  H(n). 



<!-- pdf-page: 11 -->
NONDETERMINISTIC  AND  DETERMINISTIC TAPE COMPLEXITIES 

187 

We  will  construct  a  deterministic  machine,  Zg,  which  accepts  B  within  storage 
Lk(n). 

Let  fl  be  a  new  symbol.  Let  A  =  {wflhw 

in  B  and  I wl  +  h  ~> k(I  w  I)).  A  non- 
deterministic  Turing  machine,  Z~r, which  accepts A  within  storage L(n)  can  be  con- 
structed  as  follows.  Given  input  wfl h,  Z~  first  marks  off L(n)  squares  of  storage, 
l w~ h 1.  It  then  checks  to  see  if L(n)  ~  H(I w  1).  If  this  is  not  the  case, 
where  n  ~ 
l w  j +  h  <  k(t  w  l)  and  the  computation  halts.  I f  L(n)  >~ H(I w  I),  then 
then  n  = 
to see if w is in B.  If Z g  accepts,  then  it does.  Since L(n)  >/H(I w ), 
Z~  mimics Z(cid:127) 
this  machine  will  accept  A  within  storage L(n).  So,  by  hypothesis,  there  is  a  deter- 
ministic  machine,  Z~,  which  accepts  A  within  storage L(n).  Furthermore,  since L 
is measurable,  we  may assume that  on every input  of length  n,  Z~  halts  after a  com- 
putation  in  which  at  most L(n)  squares  of storage  tape  are  scanned.  (Our  definitions 
merely require this when the machine accepts the input.) 

The  deterministic machine,  Zg,  which accepts B  within  storage  Lk(n) 

operates as 
follows.  Given an  input  w,  Z g   mimics Z~  operating  on wfl h  for various values of h. 
It first tries h  =  0.  If Z~ accepts  w,  then Zo n  does.  If not,  it  then  tries h  =  1.  If Z~ 
accepts  wE,  then  ZD n  does.  If not,  it  then  tries  h  ---- 2.  If ZD L  accepts  wfl ~,  the  Zo u 
does.  If not,  it  then  tries  h  ---- 3,  and  so  forth.  If w  is  in  B,  then  Z g   will  eventually 
find  the  least  h  such  that  I w  +  h  >~ k(  w  l)  and  will  accept  w  within  storage 
L(  wfl ~ )  =  Lk(  w  ).  This  completes the  proof of Theorem  3. 

It  is  natural  to  ask  if there  is  any  storage  function  whose  deterministic  and  non- 
deterministic  complexity  classes  are  equal.  The  answer  was  given  by  Manuel  Blum 
and  is "yes".  Blum  showed  that  there  are  arbitrarily large storage functions L(n)  such 
that  a  set  is  accepted  within  deterministic  storage L(n)  if,  and  only  if,  it  is  accepted 
within  nondeterministic  storage L(n).  These  functions L(n)  are  not,  however,  "well- 
behaved"  and  Theorem 3  does not  apply to them.  They  are not measurable.  A  sketch 
of the  proof of Blum's result  appears in  8. 

One may also ask if there is a storage function (large enough to be interesting)  whose 
deterministic  and  nondeterministic  complexity classes  are  different.  The  next  section 
is  devoted  to  this  question.  Only  an  incomplete  answer  is  given,  however,  and  the 
question  is  open. 

MAZES  AND  TURING  MACHINES 

Informally, a maze is a set of rooms connected by one-way corridors.  Certain  rooms 
are  designated  goal  rooms  and  one  room  is  designated  the  start  room.  Thus,  a  maze 
is a directed graph with  certain  nodes  or rooms distinguished.  The  maze is threadable 
if there is a path from the start room to some goal room. 

A  nondeterministic  Turing  machine,  with  input  w,  gives  rise  in  a  natural  way 
to  a  maze.  The  rooms  of the  maze  are  the  instantaneous  descriptions  of the  machine 



<!-- pdf-page: 12 -->
18 8 

$AVITCH 

and  the  corridors  are  given by the  transition  function  of the  machine.  That  is there  is 
a  corridor  from  room  11  to  room  I~  if,  with  input  to,  the  machine  can  in  one  step 
change  its  configuration  from  I 1 to  12.  T h e   initial  instantaneous  description  of  the 
machine  is designated  the  start  room.  Those  instantaneous  descriptions  which  include 
an  accepting  state  are  designated  goal  rooms.  T h e   machine  will  ,ccept  the  input  zo 
if,  and  only if, the  corresponding  maze  is threadable. 

T h e   algorithm  for simulating  a  nondeterministic  Turing  machine,  given  in  the  last 
section,  is really an  efficient method  for determining  whether  the  corresponding  maze 
is threadable.  In this section we show that if an efficient enough method for "threading" 
mazes  could  be  found,  then  deterministic  machines  could  simulate  nondeterministic 
machines  in  the  same  storage.  More  precisely,  the  set  of  threadable  mazes,  suitably 
coded,  can be recognized by a nondeterministic  Turing  machine within  storage  logz n. 
This  set  can  be  recognized  by  some  deterministic  Turing  machine  within  storage 
logs n  if,  and  only if,  deterministic L(n)-tape  bounded  Turing  machines  can  simulate 
nondeterministic L(n)-tape bounded  Turing  machines,  for all L(n)  >/log 2 n. 

DEFINITION.  A  maze over 27 (a finite  alphabet)  is  a  quadruple,  r 1 6 2   (X,  R,  s,  G), 
where  X  is a  finite set  of strings  over 27 (X  is the  set  of rooms),  R  is  a  binary  relation 
on X  (giving the  corridors), s is an element  of X  (s is the start  room),  and  G  is a subset 
of X  (G is the  set of goal rooms). 

DEFINITION.  T h e   maze  ~r  =  (X,  R,  s, G)  is  threadable  if  there  is  a  sequence 
r t  , rz ..... r6 of rooms such that  r t  ---- s (the  start  room),  r,  is  an  element  of G  (the goal 
rooms),  and  R(ri,  rt+l )  holds  for  i  =  1, 2,...,  e  --  1. 

DEFINITION.  Let ,  ,  (cid:12)9 be three new symbols. A coding of the m a z e . C / =   (X, R, s, G) 

is a string  of the  form 

sxl  *YI* *Ys* *  ""y~tl)xs 

1 

.yiS  .y22  .  ...  * Y~(s) 

2 

(cid:12)9 "  x~  *  y l   ~ *  "" Y ~ 0   Ul  *  u s   *  "'"  ug 

(1) 

where  s  is the  start  room  of J t ;   Xx, x2 ,...,  x~ is  an  enumeration  without  repetitions  of 
the  rooms  in  X;  for  1  ~< i  ~< l, yl i, yz~,..., y~,,~  is  an  enumeration  without  repetitions 
of  all y  in  X  such  that  R(xi, y)  holds;  and  u 1 , u 2 ,...,  ug  is  an  enumeration  without 
repetitions  of the  rooms in  G. 

Notation.  Mr  denotes the  set of all codings  of threadable mazes over 27. 

THEOREM 4.  For any finite alphabet 27, there is a nondeterministic  Turing  machine 

which  accepts M r   within storage log s n. 



<!-- pdf-page: 13 -->
NONDETERMINISTIC  AND  DETERMINISTIC  TAPE  COMPLEXITIES 

189 

Proof. 

If the  maze  has  length  n,  then  it  has  at  most  n  rooms.  So  each  room  can  be 
coded  by  a  number  which  can  be  stored  in  log 2 n  squares  of  tape.  More  specifically, 
if the  maze is given by (1), then  the  room xi is coded  by the  number i in dyadic notation. 
T h e   algorithm  is  very  simple.  T h e   machine  writes  down  the  code  number  of  the 
initial  room  on  its  work  tape,  finds  the  possible  next  rooms,  guesses  at  one  of  them, 
erases  its  work  tape,  and  writes  down  a  coding  of  its  guess.  It  then  finds  the  possible 
next  rooms,  guesses  at  one  of them  and  so  forth.  After  each  guess  it  checks  to  see  if 
it  has  reached  a  goal  room.  If  it  has,  it  accepts.  Clearly  the  work  tape  will  be bounded 
by  c log 2 n,  for  some  constant  c. 

A  straight  forward  crossing  sequence  argument,  like that  of Cobham  2 
the  bound,  log 2 n  in T h e o r e m   4,  is the  best possible,  up  to  a constant  factor. 

shows  that 

Applying  Theorems  1 and  4  to  M r   yields 

COROLLARY 4.  For  any  finite  alphabet  27, there  is  a  deterministic  Turing  machine 

which  accepts  h/It within  storage  (log 2 n)L 

LEMMA  4.  For  any  finite  alphabets  27  and  A  with  at  least  two  elements,  M r   is 
accepted  by  some  deterministic  Turing  machine  within  storage  logz n  if,  and  only  if, 
Ma  is. 

Proof.  For  every  coding,  w,  of  a  maze  over  27,  there  is  a  coding,  8(w),  of  a  maze 
over  A  which  is  isomorphic  to  w.  So  w  is  in  M r   if,  and  only  if,  8(w)  is  in  M,j  .  More 
specifically,  if w  is 

SXl  * Yl 1 * Y21 *  "" Yn(1)xa 

1 

* Y l  ~ * Y z  2 *  "'"  * Yn~2) 

2 

t 
"'" xt  *Yl z *  ""Yn(O  Ux *  u2 *  "'" ug 

then  8(w)  may  be  taken  to  be 

~(S)~(Xl)  *  ~ ( y l  1)  *  8(y21)  *  "" 8(y~(1))8(x2) 

*  8(yl 2)  *  8(y~ 2) . . . .   *  8(y~z)) 

(cid:12)9 "" 8(x3  *  8(yl t)  * " "   8(y~,0  8(u0  *  8(u2)  *  "'" 8(ua) 

where  if k  is the  number  of symbols  in A,  then  8(xi)  is the  k-adic  representation  of the 
number  i  and  so is an  element  of A*.  Since  the  u's and y ' s  and  s are  each  equal  to  some 
x i ,   this  defines  8 on  them  as well. 

Given  a  deterministic  machine,  Z a ,   which  accepts  MA  within  storage  log~ n,  we 
construct  a  deterministic  machine,  Z r ,   which  accepts  M r   within  storage  loga n,  as 
follows.  Given  an  input  w,  Z r   operates  by  mimicking  Za  operating  in  8(,0).  More 
specifically,  suppose  Zz  has  input  w  as in  (1).  When  Z r  is simulating  Z 4  with  the  input 
head  of Za  someplace  in  8(z),  where  z  is some  s,  x, y,  or  u  in  (1),  then  Z r   will  have  its 
input  head  reading  the  first  symbol  of  z  and  will  have  8(z)  written  on  an  auxiliary 



<!-- pdf-page: 14 -->
190 

SAVITCH 

storage  tape.  Zs  uses  this  auxiliary  storage  tape  containing  8(z)  to  mimic  the  input 
tape  of Z,j  .  When,  in  the  mimicking  process,  the  input  head  of Z 4  would  leave the 
left  (respectively,  right)  end  of 8(z),  then  Zr  moves its  input  head  to  the  s,  x, y,  or  u 
to  the  left  (respectively,  right)  of z,  calculates  8  of this  s,  x, y,  or  u  and  replaces 8(z) 
by 8 of this s, x, y,  or u.  8 of this  s, x, y,  or u  becomes the new 8(z)'and  the  simulation 
continues.  To  calculate the new 8(z),  Zz need  only compare the new z  to  each xi until 
it  finds  the  x i  which  equals  z.  This  it  can  do  symbol  by  symbol  and,  thus,  keep  the 
amount of storage tape used less than c log 2 n, for some constant c. 

Since  Z' and  A  are  symmetric  in  the  statement  of  the  lemma,  this  is  sufficient  to 

prove the  le.mma. 

THEO~M  5.  For  any finite  alphabet,  27,  with  at  least two  elements,  the  following 

statements are  equivalent: 

(1)  M~  is  accepted  by  some  deterministic  Turing  machine  within  storage  log s n. 

(2)  For  any  finite  alphabet  F,  any  set,  A,  of  strings  over  F  and  any  function 
L(n)  >/log 2 n,  if A  is  accepted  by  a  nondeterministic  Turing  machine  within  storage 
L(n),  then  A  is  accepted  by  some  deterministic  Turing  machine  within  storage L(n). 

Proof.  Statement  (1)  follows from statement  (2)  by Theorem 4. 
Assume  (1)  holds  and  that  A  is  a  set  accepted  by  some  nondeterministic  Turing 
machine, Z n  , within storageL(n)  ~> log s n. We will construct a deterministic machine, 
ZD,  which  accepts A  within the  same storage bound L(n).  Assume L(n) is measurable. 
We will later indicate  how this  restriction  may be eliminated.  With  each string w over 
the  input  alphabet  of ZN associate the  maze ~r162  =  (X, R, s, G),  where  X  is the  set 
of all I D ' s   of Z~r  in  which  the  nonblank  portion  of each work tape  has  length  at  most 
L(I w  ),  s is the  start I D   of Z n ,   G  is the  set  of I D ' s   in  X  which  include  an  accepting 
state,  and  R  is  defined  by: R(x, y)  holds  if,  and  only if,  x  ~  y.  Clearly,  Z~r  accepts w 
if,  and  only if, J/(w)  is threadable.  Let re(w) denote  a  coding of the  maze JC'(w).  The 
deterministic  machine  Z D  which  accepts  A  operates  as  follows.  Given  an  input  w, 
Z D  constructs  m(w)  on  one  of  its  storage  tapes,  and  then  simulates  the  machine  of 
statement  (1)  to  determine  whether  re(w) is  in  Mz.  If  it  is,  then  Zo  accepts  w.  By 
Lemma 4,  we may assume 2~ is large enough  so that  all I D ' s  of Z N are strings  over ~. 
So  re(w) is  in  Me  if,  and  only if,  Zn  accepts w.  Thus,  Z D accepts precisely the  set  A. 
m(w)  is  of  the  length  at  most  h z{nl, where  n  =  I w    and  h  is  a  constant  depending 
only  on  Z N . Except  for the  tape  used  to  store m(w), Z 9  operates  in  storage log s h Ll'~ 
which  is proportionate to L(n). 

The  machine  Z D cannot  write  down  the  entire  string,  re(w),  at  once  and  still  work 
within  the  allotted  storage.  However,  all  that  is  necessary  in  order  to  simulate  the 
machine  of statement  (1)  is  that  Z 9  be  able  to  compute  one  symbol  at  a  time  of the 
string re(w) and  keep track of the  symbols position in re(w). This  it could do provided 
it  could,  within  storage L(n),  generate re(w), from right  to  left,  one  symbol at  a  time. 



<!-- pdf-page: 15 -->
NONDETERMINISTIC  AND  DETERMINISTIC  TAPE  COMPLEXITIES 

191 

Our  remarks  so far applied to  any  coding m(w)  of the  maze ~/(w).  W e   now  fix m(zo) 

to  be the  following coding of the  maze d//(w) 

sxt 

(cid:12)9 y l  ~ * y2 ~ *  "" yn(1)x2  * y  Z ,   Y2" *  "'"  * Y,,(2) 

2 

1 

1 
"'"  x t   *  y l   t  *  "'" Yn(O  ul  *  u2 *  "'" Ua 

where  x 1  <  x 2  <  x 3  <  "-  <  x~ for  each  i  =  1, 2,...,  l, y l  i  <  y2 i  <  y3 i  < 
. "   <  Y~{o 
and u a  <  u 2 <  ""  <  ug.  <  is  the  usual  "less  than"  ordering  on  the  natural  numbers. 
Recall  that  the  x's,  y's,  and  u's  are  strings  over  a  finite  alphabet  and,  thus,  may  be 
regarded  as  numbers  in  k-adic  notation,  for  some  k.  By  definition  of ~ ( w ) ,   the  x's, 
y's,  u's,  and  s are D ' s   of ZN of length  less than  cL(n),  where  c  is a  constant  depending 
only on ZN  (cid:12)9 Z o  can generate re(w) symbol by symbol, in the allotted storage, as follows. 
ZD can easily calculate s, the initial I D  of Z N . Having generated s, Z D next runs through 
in  numerical  order,  all strings  of  length  less  than  cL(n)  until  if finds  one  which  is  an 
I D   of Z N  .  This  will be  x t  .  So  Zo  has  generated  x I  .  Next  it  produces  all y  such  that 
x 1 ~  y.  I n   this  way,  it  generates  the  yjt.  Next  it  runs  through,  in  numerical  order, 
all  strings  of  length  less  than  cL(n)  until  it  finds  the  first  such  string  which  is  an  I D  
of Z N and  is greater than  x t  .  T h i s   is x 2 .  It  now  may  erase x 1 .  T h e   only thing  it need 
keep  in  storage  at  this  point  is  x 2 .  ZD  then  proceeds  to  generate  the y 2 .   It  generates 
x 8  from  x2  in  the  same  way  it  computed  x 2  from  x I  .  It  proceeds  in  this  way  until 
it  finds  the  largest  xi  (cid:12)9 Having  generated  the  largest  x i  and  its  associated y's,  it  then 
generates  the  u~'s  as  follows.  It  runs  through  all  strings  of  length  at  most  eL(n)  and 
checks  to  see which  are  I D ' s   which  include  an  accepting  state.  Those  that  do  are  the 
u i .   T h i s  completes the generating process and the proof for the case:L(n) is measurable. 
I f L ( n )   is  not  measurable,  then  Z D  cannot  necessarily generate  precisely the  strings 
of  length  less  than  cL(n)  within  storage  proportionate  to  L(n)  and  so  the  above  pro- 
cedure  will not  work.  However,  if ZD  were  somehow  given the  value  of L(n),  then  by 
the  above  procedure  it  could  determine  whether  or  not  w  is  accepted  by  Z N within 
storage L(n).  ZD  uses  the  same  sort  of trick  as  was  used  for  nonmeasurable  functions 
in  the  proof of T h e o r e m   1.  T h a t   is,  first  it  assumes L(n)  ---- 1.  I f  Z N accepts  the  input 
zo within  storage L(n)  =  1,  then  Zn  accepts  w.  If  not,  Z o  next  tries L(n)  =  2.  If  Z1v 
accepts  within  storage L(n)  =  2,  then  Z D does.  If not,  Z D tries L(n)  =  3  next,  and  so 
forth.  I f   Z N  accepts  the  input  w,  then  Z~  will  eventually  find  the  correct  value  for 
L(n)  and  accept w within  storage proportionate to L(n). 

A n   unsolved  problem  in  the  theory  of tape  complexity is whether  there  is some  set 
A  of  strings  and  some  function L(n)  ~ 
log 2 n  such  that  A  is  accepted  by  some  non- 
deterministic  T u r i n g   machine  within  storage L(n)  but  accepted  by  no  deterministic 
T u r i n g   machine  within  storage L(n).  T h e o r e m   5  shows  that  if  any  such  A  and L(n) 
exist, then  A  ~-  M r   a n d L ( n )   = 

log 2 n  will do. 



<!-- pdf-page: 16 -->
192 

SAVITCH 

ACKNOWLEDGMENT 

The  author  thanks  Stephen  A.  Cook  for  his  help  and  encouragement  in  this  work. 

REFERENCES 

I.  M.  BLUM, A  machine-independent  theory  of the  complexity of recursive functions,  J.  Assoc. 

Comput. Mach.  14 (1967),  322-336. 

2.  A.  COBHAM, " T h e   Recognition Problem  for  the  Set  of Perfect  Squares."  IEEE  Conference 
Record  of  the  Seventh  Annual  Symposium  on  Switching  and  Automata  Theory, Berkeley, 
Calif.,  1966,  pp.  78-87. 

3.  J.  E.  HOPCROFT AND J.  D.  ULLMAN, "Formal  Languages  and  Their  Relation to  Automata." 

Addison-Wesley,  Reading,  Mass.,  1969. 

4.  J.  E.  HOPCROFT AND J.  D.  ULLM~'q, Relations  between time and  tape  complexities.  J. Assoc. 

Comput. Mach.  15 (1968),  414-427. 

5.  S.  Y.  KURODA, Classes  of  languages  and  linear-bound  automata.  Information  and  Control 

7  (1964),  207-223.  (The  relevant material  also  appears  in  3,  pp.  115-119.) 

6.  P.  S.  LANDWEBER, Three  theorems  on  phrase  structure  grammars  of type  1. Information  and 

Control 6  (1963),  131-136.  (The  relevant  material  also  appears  in  3,  pp.  115-119.) 

7.  P.  M.  LEwm  II,  R.  E.  STEARNS, AND J.  HAaTMANm, "Memory  Bounds  for  the  Recognition 
of  Context-Free  and  Context-Sensitive  Languages."  1EEE  Conference Record on  Switching 
Circuit  Theory  and  Logical  Design, Ann  Arbor,  Mich.,  1965,  pp.  191-202.  (The  relevant 
material  also appears  in  3,  pp.  162-164.) 

8.  E.  M.  McCaEtCHT AND A. R.  M E ~ a ,   "Classes of Computable  Functions  Defined by Bounds 
on  Computation:  Preliminary  Report."  Conference Record of A C M   Symposium  on  Theory of 
Computing, Marina  del  Rey,  Calif.,  May  1969,  pp.  79-88. 

9.  W.  J.  SAVITCH, "Deterministic Simulation  of Non-deterministic  Turing  Machines  (Detailed 
Abstract).  Conference Record of A C M   Symposium on  Theory of Computing,  Marina  del  Rey, 
Calif.,  May  1969,  pp.  247-248. 

Printed in Belgium 


