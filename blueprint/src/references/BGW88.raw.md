<!-- generated-by: proofmatch local extraction -->
<!-- source-pdf-sha256: b3f55f2a43328aca91e075d51ea095aec08ec5ef522814d751e6192376c9e8a9 -->
<!-- extractor: pdfminer.six v20260107 -->

<!-- pdf-page: 1 -->
Completeness  Theorems 

for  Non-Cryptographic 

Fault-Tolerant 

Distributed 

Computation 

(Extended  Abstract) 

Michael  Ben-Or* 
Hebrew  University 

Shafi  Goldwassert 
MIT 

Avi  Wigdemon* 
Hebrew  University 

Abstract 

Every  function  of n  inputs  can  be efficiently  computed 
by  a  complete  network  of  n  processors  in  such  a  way 
that: 

1. 

2. 

If  no  faults  occur,  no  set of size  t  <  n/2  of  players 
gets  any  additional 
the 
function  value), 

information 

(other 

than 

Even  if  Byzantine 
size  t  <  n/3  can  either  disrupt 
or  get  additional 

information. 

faults  are  allowed,  no  set  of 

the  computation 

Furthermore, 

the  above  bounds  on  t  are  tight! 

Introduction 

over  the  past  ten  years  addressed 

systems  raised 
The  rapid  development  of  distributed 
the  natural  question  of  what 
tasks  can  be  performed 
by  them  (especially  when  faults  occur).  A  large  body 
this 
of  literature 
question.  There  are  two  approaches 
to  this  question, 
depending  on  whether  a  limit  on  the  computational 
power  of  processors  is  assun 

or  not. 
inaugurated  by  Difiie 
and  Hellman 
[DH],  assumes  the  players  are  computa- 
tionally  bounded,  and  further  assumes  the  existence 

The  cryptographic 

approach, 

*Supported 
tSupported 

by  Alon  Fellowship. 
by  NSF 
in  part 

grant  DAALOWSK-017, 
Jerusalem, 

Israel. 

AR0 
and  US-Israel  BSF  grant  8640301, 

865727~CCR, 

grant 

:Supported 

by  Alon  Fellowship. 

that 

Permission 
provided 
commercial 
the  publication 
is  by  permission 
copy 
otherwise. 
permissiotl. 

to  copy  without 
the  copies 
- 
advantage. 
its  date  appear, 
and 
the  Association 
of 
republish. 
or 

the  ACM 

to 

fee  all  or  part  of 

this  material 

are  not  made 

or  distributed 
notice 

and 

copyright 

is  granted 
for  direct 
title  of 

the 

a&l  notice 
for  Computing 
requires 

a 

is  given 

that  copying 

Machinery. 

TO 

fee  and/or 

specfk 

@  1988  ACM-O-89791-264-O/88/0005/0001 

$1.50 

1 

(one-way) 
of  certain 
but  not  inverted  by  the  player. 

functions, 

that  can  be  computed 

[GMR], 

through 

This  simple  assumption  was  ppstulated 

in  [DH]  in 
order  to  achieve  the  basic  task  of  secure  message  ex- 
change  between  two  of  the  processors,  but  turned  out 
In  subsequent  years  ingenious  pro- 
to  be  universal! 
tocols  baaed  on  the  same  assumption  were  given 
for 
increasingly  harder  tasks  such  as contract  signing,  se- 
cret  exchange,  joint  coin  flipping,  voting  and  playing 
the  defini- 
Poker.  These  results  culminated, 
their  existence 
tion  of  zero-knowledge  proofs 
in  completeness 
for  NP-complete  problems 
[GMW2] 
theorems  for  two-party  pl]  and  multi-party 
cryptographic 
In  particu- 
lar  the  results  of  Goldreich,  Micali  and  Wigdesrson 
in  [GMWB]  were  the  main 
to  our  work. 
one  way  functions 
They  show,  that 
of  n  input,s 
exist 
then  every  (probabilistic) 
can  be  computed  by  n  computationally 
bounded  pro- 
cessors  in  such  a  way 
If  no  faults  occur, 
that: 
no  subset  of  the  players  can  compute  any  additional 
information, 
and  (2)  Even  if  Byzantine 
lowed,  no  set  of  size  t  <  n/2  can  either  disrupt 
information. 
or  compute  additional 
computation 

faults  are  al- 
the 

if  (non-uniform) 

computation. 

distributed 

inspiration 

function 

[GMWl] 

(1) 

the  computational 

(or  information-theoretic) 

The  non-Cryptographic 
approach  does  not  limit 
the  processors.  Here,  the  notion  of  privacy 
stronger  - for  a piece  of  data  to  be  unknown 
players 
it  within  a  certain 
but  simply 

power  of 
is  much 
to  a set  of 
they  cannot  compute 
they  know, 
from  what 

it  cannot  be  computed  at  all! 

that 
time  bound 

it  does  not  suffice 

that 

To  facilitate 

the  basic  primitive 

of  secret  message 
exchange  between  a  pair  of  players,  we  have  secure 
channels. 
(For  an excellent  source  of  results  and  prob- 
lems  in  the  case  no  secure  channels  exist,  see [BL]). 
the  cryptographic 
Unlike 
case,  very  little  was  known 
the  capabilities  of  this  model.  Two  main  basic 
about 
problems  were  studied  and  solved  (in  the  synchronous 
case):  Byzantine  agreement 
and  collec- 
tive  coin  flipping  p2]. 

[LPS,DS,...] 



<!-- pdf-page: 2 -->
while 

later) 

these  results 

two  (non-faulty) 

theorems.  Comparing 

is  useless,  and  indeed 

This  paper  provides  a  full  understanding 

of  the: 
power  and  limits  of  this  model,  by  proviug  a few  com- 
pleteness 
t#o the 
case  of  [GMW:!],  one  gets  the  imprcs- 
cryptographic 
th:tn 
sion  that  one-way  functions  ar’e “more  powerful” 
secure  channels.  This  should  not  be  surprising, 
if  ale 
the  case  of  n  =  2.  Clearl,y,  here  a  secure 
considers 
channel 
play- 
the  OR  function  of  their  bits  using 
ers  can  compute 
the  reader  can  convince  herself 
cryptography, 
(it  will  be  proven 
leak 
that  any  protocol  will 
sense.  The 
information 
the  same  phz- 
lower  bounds  we  provide  show 
nomenon 
arises  in  the  Byzantine 
phy  one  can  allow 
non-Cryptogra.phic 
As  happened 

is true  for  any  value  of n.  A  similar  situation 
case  where,  using  cryptogr,i- 

t  <  n/2 
case one  must  have  t  <  n/3. 

in  the  information-theoretic 
that 

case,  the  proto- 
in  the  crypt.ographic 
cols  are  based  on  a  new  mc,thod  for  comput,ing  with 
are  based  on  AIgc:- 
shared  secrets.  Our  constructions 
hraic  Coding  Theory,  particul;rrly 
the  use  of  gcnc>ral- 
izcd  BCll  codes. 
It  is  important 

faulty  players,  but  in  tile 

to  stress  here  that  our  main  proto- 
amount  of  work  from 
to  be 

cols  require  only  a  polynomial 
the  players. 
(In  fact,  they  are  efficient  enough 
Putting 
practical!). 
power  serves  only 
nition  of  privacy  and  the  most 
faultiness,  both  of  which  we  can  handle. 

the  most  stringent 

no  bound  on  the  computational 

liberal  definition 

deli- 
cf 

to  allow 

faults 

[CCD].  We  briefly  point  out 

is almost  identical.  Their  solution 

the  same  results  we  obtain  here  were 
Essentially 
discovered  by  Chaum,  Crepeau  and 
independentIy 
Darngard 
the  small  dif: 
ferences  of  this  work  from  OUPS. The  simple  case of  no 
in  the  case of 
faults 
is  elementary  and  requires  no  error 
Byzantine 
is  achieved  us- 
correcting  codes.  The  error  correction 
ing  a  clever  scheme  of  zero  knowledge  proofs. 
‘I’llis 
has  two  consequences:  They  have  to  allow  an  ex- 
for  both  correct,- 
ponentially 
ness  and  privacy 
them  with  no  cr. 
(we  can  guarantee 
rors),  and  the  frequent  zero  knowledge  proofs  increase! 
In  the  solution  of 
the  complexity 
[CCD] 
is  of  Boolean  operations  while 
our  solution  allows  direct  simula.tion  of  arithmetic  op.. 
erations 
puting 
calls  for  O(log  n)  communication 
done  in  O(1)  rounds  using  our  solution. 

the  product  of  two  n  hit  numbers  using  [CCD: 

small  error  probability 

of  their  protocols. 

for  example,  corm 

rounds.  This  can  bc, 

the  simulation 

in  large  finite 

fields.  Thus, 

We  mention 

application 
rounds  protocol 
and  Micah 

[FM]. 

that 

the  above  results  already 
in  the  new,  constant  expected  number  01’ 

found 

for  Byzantine  agreement  of  Feldman 

alizations  aud  cxtc%nsions of  our  rrsulL+  t.o ol.llc>r Itasks 
fIiII(*~~iolls),  t,o 
(playing 
ratllcr 
panics 
other  model  param&rs 
,:.ollll~lultici~t  ion 
networks)  and  other  complexity  meitSnrrs  (nu~~hcr 
of 
rounds). 

than  comp~ll,inl; 
(synchrony, 

Definitions 

and  Results 

in  an  appendix. 

the 
For  this  abstract,  we  define  the  model  and  state 
results  on  an  intuitive 
level.  Since  even  the  formal 
definition  of  the  notions  of  privacy  and  resiliency  are 
nontrivial,  we  give  them  explicitly 
The  model  of  computation 

syn- 
chronous  network  of  n  processors.  The  pairwise  com- 
munication 
channels  between  players  are  secure,  i.e. 
they  cannot  be  rrad  or  t.empered  with  1~~ other  play- 
1 Iw  play- 
round  of 
crs. 
co~iiput~at~ioli 
(xrs ca.n tlo  an  arbitrary 
a1  ion. 
i~~llOlllll~ 
send  a  message  t.0  each  of  t.he  players,  and  rc>ad all 
messages  that  w(xrc scxnt, to  it,  at, this  round. 

is  a  complete 

cd”  local 

In  ow 

wllqwt 

cwch 

d 

We  shall  be  iilt.clrc&4 

imposing  privacy 

in  t.hc  coiilp\il.:ll.icwal 

p(\w\‘llr 
tol- 
For  simplicity,  we  restrict  our- 
functions 
of  (probabilistic) 
to  n, out,puts.  We  assume  t,liat  player 
input  at  the  start  of  computation, 
and 
the  i-th  output  at  the  end,  but  nothing 

of  this  model  when 
erance  requirements. 
selves  to  the  computation 
f  from  R inputs 
i  holds  the  i-th 
should  obtain 
else. 

fault. 

and 

A  protocol 

“Gossip”  and  “Byzan- 

two  kinds  of  faults: 
the  first, 
to  their  predetermined 

is  a specifica- 
for  computing  a function 
tion  of  12 programs,  one  for  each  of  the  players.  We 
distinguish 
tine”. 
In 
according 
to  learn  as much  as they  can  by  sharing 
tion  they  received. 
In  t,he scrond, 
different,  prograins,  collal~or:~ting 
formation  of  even  sabotage 
A  prot,ocol  is t-ptivnle 

faulty  processors  send  messages 
try 
the  informa- 
thry  can  WC 
t.obnlly 
to  :icqliirc>  morcx iri- 

if  any  set  of  at  most  1 players 

the  computa.tion. 

programs,  but 

cannot  compute  aft.cr  t,hc  protocol  more> l.lic~~ t.hy 
could  jointly 
from  their  set  of  privalc 
inputs  and  outputs. 

compute  solely 

is  t-resilienl 

if  no  set  of  f  or  less  play- 
A  protocol 
ers  can  influence 
the  correctness  of  the  output,s  of  t,he 
remaining  players.  For  this  to  make  sct~se, the  func- 
tion  definition 
it 
inpnts  or  are 
is  if  some  players  neglect 
caught  cheating 

should  be  extended 

to  specify  what 

(see  appendix). 

to  give  their 

We  can  now  state  the  main  results  of  this  paper. 

Theorem 

1:  For  every 
t  <  ?a/2  there  exists  a  t-private 

(probabilistic) 

ad 

fun.clion 

f 

prolocol. 

for  which 

there 

We  proceed 
and  prove  them. 

to  define 

the  model,  state  the  results 
In  the  full  paper  we  mention  gener- 

Thcorcm 

we  no  n/2-private 

2:  There  are  functions 
protocols. 



<!-- pdf-page: 3 -->
Theorem 
every  t  <  n/3 
resilient  and  t-private. 

3:  For  every  probabilistic 
there  exists  a  protocol 

function 

and 
is  both  t- 

that 

Theorem 

4:  There  are  functions 

for  which 

there 

is  no  n/3-resilient 

protocol. 

Proof 

of  Theorem 

1 

field  E,  with 

be  a set  of  players,  and  let  n  2  2t+  1. 
this  set  of  players  wants 
t-privately,  where  each  player  holds  some 
to  the  function  F.  Let  E  be some  fixed 
loss  of  general- 
from 
(in  the  input  vari- 

LetPo,...,P,-l 
Let  F  be  the  function  which 
to  compute 
input  variables 
finite 
ity  we  may  assume  that  all  inputs  are  elements 
E  and  that  F  is  some  polynomial 
ables)  over  E,  and  that  we  are  given  some  arithmetic 
circuit  computing 
constants 

IFI,  using  the  operations  +,  x  and 

[El  >  n.  Without 

from  E. 

To  simplify  our  explanation  we  divide 

the  compu- 

tation 

int.o  three  st.ages. 

Stage 

I:  ‘Hrc: input  stage,  whcrc  each  player  will  en- 
using 

t.0 the  computation 

t.cr  his  input,  variables 
a srcrcrl. sharing  procedure. 

Stage 

II:  The  coinput.ation 

stage,  where  the  players 
F,  gate  by 
the  circuit  computing 
will  simulate 
gat,e, keeping  the  value  of  each  computed  gate  as 
secret  shared  by  all  players. 

Stage 

III:  The  final  stage,  where  the  secret  shares 
to  one  or  all 

of  the  final  value  of  F  are  revealed 
of  the  players. 

Stages  I  and  III  are  very  simple  and  we  describe 

them  below,  and  delay  the  details  of  the  computation 
st,age t,o the  next  section. 

The 

input 

stage 

I,(4  (k(], . .  1 CY,,-1 be  some  n  disbinct,  non  zero  points 
[[:I  >  n.)  Each 
iu  our  lic,l(l  E.  (This 
playc>r holtliug  some  input  s  E  LS, iutroduccs 
l,he input 
t  random  elcment,s 
i,o  t,hc  corl~l~~rl.;~~.iotl by  selecting 
(li  E  E,  for 

is  why  we  urctl 

. . ,1,  setting 

i  =  l,, 

f(x)  =  s +  a12  +. 

. . +  a& 

and  sending 

to  each  player  Pi  the  value  Si  =  f(ai). 

[Sh]  secret  sharing  scheme,  the  se- 

As  in  Shamir’s 
qtience  (so,.  . . , s,,-~) 
dent  random  variables  uniformly 
thus  the  value  of  the  input 
the  shares  (si} 
from 
player 
that  does  not 
secret. 

is  a sequence  of  i-wise 
distributed 

indepen- 
over  E, 

is  completely 

that  are  given 
include 

the  player  holding 

independent 
to  any  set  of  t 
the 

The 

final 

stage 

to  some  s  E  E,  will  be  “evaluated” 

condition,  we  will  make  sure 
the  set  of  messages  received  by  any  set  oft  play- 
from  all  the  in- 
independent 
each  gate  which 
the  whole  computation 
by  the 
the  secret  value  of  8  using  a  com- 
random  poly- 
from  all  the  inputs, 
that 

To  keep  the  t-privacy 
that 
ers  will  be  completely 
pubs.  During 
evaluates 
players  by  sharing 
independent 
pletely 
f(t)  of  degree  t,  with 
nomial 
f(0)  =  s.  In  particular 
we  will  have  the  value  of  F  shared  among  the  play- 
ers  in  a  similar  manner. 
to  let  just  one 
the  players  send 
the  output 
player  know 
This  player 
to  that  particular 
their  shares 
can  compute 
f(z)  and 
the  interpolation 
use  its  free  coefficient  as the  result. 

the  only  restriction 
at  the  end  of  the  computation 

If  we  want 
value,  all 

player. 
polynomial 

Note  that 

there  is  a  one-to-one  correspondence  be- 
tween  the  set  of  all  shares  and  the  coefficients  of  the 
f(  2).  S ince  all  the  coefficients  of  f(z),  ex- 
polynomial 
random  vari- 
cept  for  its  free  coeffGent,  are  uniform 
the  set  of 
ables  lhat  are  independent 
of  the  inputs, 
the 
about 
all  shares  does  not  contain  any  information 
inputs 

from  the  value  of  J(0). 

that  does  not  follow 

The  Computation 

Stage 

Let  Q, b E  E  be  two  secrets  that  are  shared  using  the 
and  let  c  E  E, 
polynomials 
to  show  how 
c  #  0  be  some  constant. 
one  can  “compute” 

c.  a,  a +  6,  and  a.  b. 

respectively, 

is  enough 

f(x),g(r) 

It 

The  two  linear  operations  are  simple  and  for  their 
evaluation  we  do  not  need  any  communication 
be- 
tween  the  players.  This  is because  if  f(z)  and  g(z)  en- 
code  a and  6, then  the  polynomials 
and 
> x  encode  c.a,  a+  b respectively.  Thus 
k(l)  =  fb)+!J( 
to  compute 
for  example  a +b,  each  player  Pi  holding 
/(nil, 
Likowise,  since  c is  A known  constant  F’r can  compute 
if  only 
F ur th crmore,  h(z) 
h(tri)  =  c.f(cq). 
f(x)  was,  and  k(x) 
if  only  one  of  l(z)  or 
S(X)  Wm. 

can  c0mput.c  h(cYi)  =  f((Yi)  +  fJ(CYi). 

h(z)  =  c.f(t) 

is  random 

is random 

ad  dni) 

As  a corollary  we  immediately 

have 

Lemma: 
and  any  linear 

(Linear  Functional) 
functional 

For  any  t,  (t  5  n  - 

l), 

F(Xo,  . . . , X,-1)  =  aoX 

+ 

*. 

.  +  Qn-l&b-l 

where  each  Pi  has  input 
constants,  can  be  computed 

t-privately. 

xi  and 

the  ai  are  known 

From  the  lemma  we  have 

3 



<!-- pdf-page: 4 -->
(Matrix  Multiplication) 

Let  A  be  a  con-, 
CoroHary: 
stant  n  x  TI  matrix, 
in., 
put  variable  xi.  Let  X  =  (~0,  _ . . , zn,-l)  and  define 
Y  =  (~1,.-,vn> 

‘each  I\  have  an 

and 

by 

let 

Proof:  Let  H  be  the  n-vector 

H=(ho,...,ht 

,..., 

hzt,O  ,..., 

0) 

and  let  I<  be  the  n-vector 

Y  =X.A., 

IC  =  (ho,  1. . , ht , 0, . . - IO). 

then  for  any  t,  (t  5  n- 
the  vector  Y  such  that 
Piwillbethevalueof~,fori=O 

l),  we  can  t-privately 
information 
the  only 
,...,  n-l. 

compute 
given  tcl 

Let  B  =  (bij)  be  the  n  x  n  (Vandermonde)  matrix, 
where  bi,j  =  CX~ for  i,j  =  0,.  . . , n  -  1.  Furthermore, 
let  P  be  the  linear  projection 

Proof:  Matrix  multiplication 
n  linear 
functionals. 
each  linear 
the  outcome  only 

functional 

to  Pi. 

is  ,just  the  evaluation  01’ 

By  the  Lemma,  we  can  compute, 
and  revea’: 

independently, 

Yi 

The  multiplication 

step 

h(z)  =  f(z)g(r) 

is  2t  instead  of  t.  While 

step  is  only  a  bit  harder. 

interpolating 
it  is  clear  that 

first,  and  obvious  one,  is  that 

raise  the  degree,  and  once  the  degree  passes  n 

The  multiplication 
Let  o 
and  b be  encoded  by  f(z)  and  g(x)  as above.  We  nou’ 
assume  that  n  >  2t  +  1.  Note  thlat 
the  free  coefficienl, 
is  a.  b.  There  arc 
of  the  polynom%l 
to  encode  the  product 
two  problems  with  using  h(z) 
the 
of  a  times  b.  The 
degree  of  h(z) 
this  poser, 
11(z)  from  its  n  pieces 
no  problem  with 
since  n  >  2t+l, 
further  multiplications, 
will 
we  will  not  have  enough  points 
The  second  problem 
random  polynomial 
the  free  coefficient). 
of  two  polynomials, 
To  overcome 
step,  randomize 
degree  while  keeping 
We first  describe 
then  combine 
cients. 

is  not  a, 
of  degree  2t  (ignoring  of  course! 
For  example,  h(z),  as  a  product 
cannot  be  irreducible. 
these  two  problems  we  will, 
in  one! 
the  coefficients  of  h(z),  and  reduce  it:, 

the  degree  reduction  procedure  and 
of  the  coeffi- 

for  the  interpolation 
h(t) 

the  free  coefficient  unchanged 

the  randomization 

is  more  subtle. 

it  with 

The  degree 

reduction 

s.tep 

Let 

and  let 

h(x)  =  ho +  hlX  +. 

. . +  hztx2f 

Si 

= 

h(ai)= 

f(ai)g(ai), 

for  i=O,..., 
holds  an  si.  Define 

n  -  1 be  the  “shares”  of  h(z).  Each  Pi 

the  truncation 

of  h(z) 

to  be 

k(x)  =  hrJ +  hlX  +.  *. +  htxf, 

andr;=k(cri)fori=l,...,n--1. 

Chim: 

. . , rn-  1)  then 

(PO,. 
A  such  that 

Let  S  = 
there 

= 
, b-1  )  and 
(SO,... 
is  a  constant  n  x  n  matrix 

It 

qxo,..., 

xn-1)=(x0 

)...)  x*,0  )...)  0). 

We  have 

and 

H*B=S 

H.P=I’ 

Ii 

.  B  =  R. 

Since  B  is  not  singular 
we  have 

(because  the  ai-  are  distinct) 

S.  (B-‘PB) 

=  R 

is  some  fixed  constant  matrix,  prov- 

but  A  =  B-‘PB 
ing  our  claim. 

The 

randomization 

step 

truncation 

random,  and  likewise 

random.  To  randomize 

As  noted  above  the  coefficients  of  the  product  poly- 
nomial  are  not  completely 
the 
b(z)  may  not  be  com- 
coefficients  of  its 
the  coefficients,  each 
pletely 
player  Pi  randomly 
qi(z)  of  de- 
gree  22  with  a  zero  free  coefficient,  and  dist,ributes 
the  players.  By  a  simple  gencral- 
its  shares  among 
ization  of  the  argument,  in  Shamir’s 
it  is 
easy  to  see that  knowing 
gives  no  information 
the  monomials  of  t,  xz,  . . . , xt  of  qi(+). 

t  values  on  tl;is  polynomial 
on  the  vector  of  coefficients  of 

selects  a  polynomial 

[Shl  scheme. 

Thus 

instead  of  using  h(t) 

in  our  reduction  we  can 

use 

G) = h(x) + c f&(x) 

n-l 

j=O 

which  satisfies  h(O)  =  h(O)  but 
of  zi,  1 5  i  5  t,  are  completely 
player  can  evaluate 
apply  the  truncation 
tiplication 
polynomial 
and  k(O)  =  a  . b,  and  k(z) 
all  the  players. 

the  other  coefficients 
random.  Since  each 
his  point  &  =  h(cyi),  we  can  now 
procedure  using  the  matrix  mul- 
random 
I, 
= 
*,haretl  a.msng 

I(z)  which  satisfies  both  degi(3:) 

to  arrive  at  a  completely 

is  properly 

lemma 

Thus 

(omitting 
[GM  W])  we  hn.vc  proved 

many  well 

known 

tl<>bdls,  see 

R=S.A. 

Theorem 
1  <  n/2 

1:  For  every 

(probabilistic) 

function 

F  and 

lhere  exisls  a  t-private 

protocol. 

4 



<!-- pdf-page: 5 -->
Remarks: 

(1)  The  complexity 

bounded  by  a polynomial 
complexity  of  computing  F. 

of  computing 

F  i-privately 
is 
(in  n.)  factor  times  the 

(2)  If  F  can  be  computed  by  an  arithmetic 

over  some  field  using  unbounded 
operation  and  bounded 
depth  d,  then  F  can  be  computed 
O(d)  rounds  of  exchange  of  information. 

fan-in  multiplication, 
t-privately 

fan-in 

circuit 
linear 
in 
in 

only  when 

(3)  In  our  construction  we  have  to  reduce  the  degree 
its  degree  is  about 
of  our  polynomial 
to  pass  n-  1.  Thus  if  1=  O(nl-‘), 
for  some  fixed 
e >  0,  and  we  start  with  polynomials  of  degree  1, 
the  players  can  simulat#e  many  steps  of  the  com- 
putat.ion  before  the  degree  comes  close  to  n,  by 
doing  the  computation 
each  on  t,heir  own  shares, 
without  any  communication(!).  When  the  degree 
does  get  close  to  n,  we  reduce  the  degree  back  to 
t  in  one  radomizing,  degree  reducing  step. 

Two  simple  examples  are: 

a.  Any  Boolean 

+ 

function  F:  {O,l}” 

(0,  1) 
polyno- 
if  t  =  O(nlme) 
in  parallel,  all 
in  O(1)  number  of 

can  be  represented  as  a  multilinear 
mial  over  the  field  F.  Thus 
t-privately, 
we  can  compute 
the  monomials 
of  F 
rounds  and  then  use  a  big  fan-in  addition 
to  evaluate  F.  This  procedure  may  use  ex- 
ponentially 
long  messages but  only  constant 
number  of  rounds. 

b.  The  Boolean  Majorit,y 

f  =  O(n’-’ 

function  has  a  poly- 
nomial  siae  O(log  n)  dcpt.h  circuit,  and  thus 
for 
can  be 
computed 
ally 
rounds. 

long  messages  in  constant  number  of 

t-privat,ely  using  only  polynomi- 

funclion 

t,his 

), 

For  completeness  we  state  the  following  simple  re- 

sult 

Theorem 

2:  There  are functions 

for  which 

there 

are  no  n/2  -private 

protocols. 

Proof: 
It  is  easy  to  see  that 
ing  one  input  bit,  cannot  compute 
of  their  bits,  without 
one  of  them 
formation.  This 
theorem. 

immediately 

two  players,  each  hold- 
the  OR  function 
leaking  some  in- 
to  prove  the 

generalizes 

Sharing 

a  secret  with  Cheaters: 

Let  n  =  3t  f  1  and  let  PO,. . . , Pn-r  be  a  set  of  n 
players  among  which  we  want 
to  share  a secret  such 
that. 

(A)  Any  set  of  at  most  t  players  does  not  have  any 

information 

about 

the  secret  and 

(B) 

is  easy  to  compute 

It 
its 
shares  even  if  up  to  t  pieces  are  wrong  or  missing. 

the  secret 

from  all 

The  following  scheme  achieves  both  requirements: 
Let  E  be  a  (finite) 

of  unity,  w  E  E,  W”  =  1  and  for  all  1  < 
wj  #  1.  Without 
that  our  secret  s  is  in  E. 

n-th  root 
j  <  n, 
loss  of  generality  we  can  assume 

field  with  a  primitive 

Pick  a  random  polynomial 
f(0)  =  s.  That, 

t  such  that 
random  ai  E  E  for  i  =  1.  . . t  and  set 

f(z)  E  E[t],  of  degree 
is,  set  ac  =  s  and  pick 

f(x)  =  al) + 01z +  . . . + atd, 

the  share  of  9, 

Define 
f(d).  As  in  [Sh],  th e si-s  are  t-wise  independent 
dom  variables 
that  are  uniformly 
and  thus  our  first  requirement 

i  =  0.  ..n  --  1,  to  be  Si  = 
ran- 
over  E, 

distributed 
is  met. 

(A) 

Note  that  setting  oi  =  0  for  i  >  t  makes  our  secret 
shares  the  Discrete  Fourier  Transform  of  the  sequence 

,an-I). 
(ao,... 
By  the  well  known 

Let  f(z)  =  sg+s~z+~.++~,-i2”-~. 

formula 

for  the  inverse  transform 

and  in  particular 
Explicitly 

p(w-‘)  =  0  for  i  =  t+  1, . . . , n  -  1. 

the  si  satisfy 

the  linear  equations 

n-l 
c  W r.i  . Si =  0 
i=o 

for 

r=  1 , . . . ,2t. 

the 

the  polynomial 
the  polynomial 

g(z)  =  n~~~i,,(z 
in 
f(z),  which 

Thus 
-  w-“)  di- 
vides 
language 
of  Error  Correcting  Codes  says  that 
the  vector  s  = 
in  the  Cyclic  Code  of 
(so , . . . ,sn-1) 
length  n  generated  by  g(z).  By  our  choice  of  g(z), 
this  cyclic  code  is  the  well  known  Generalized  Reed- 
Miller  code.  Such  codes  have  a  simple  error  correc- 
to  correct  $ degg(z)  =  t  errors.  See 
tion  procedure 
for  example 

[PW,  page  283). 

is  a  codeword 

Verifying 

a  secret 

Assume  that  player  P  has  distributed 
manner  described  above.  Before  entering 
secret  into  a  computation  we  wish  to  verify 

a secret  in  the 
this  shared 
the 
that 



<!-- pdf-page: 6 -->
revealing  any  informat#ion  about 

secret  shares  we  are  holding  are  shares  of  a real  secret 
and  not  some  n  random  numbers.  We  want 
to  do  SC 
without 
or  any  of  its  shares.  This 
following  Zero  Knowledge  proof 
later  show  how 
technique 
We present  this  Zero  Knowledge 
is  simpler,  and  uses  fewer  roundls  of  communication. 

the  secret 
the 
technique,  We  &ill 
to  verify  a  secret  using  a  different 
that  has  absolutely  no  proba.bility  of  error. 
technique  because  it 

is  easily  done  using 

of  degree  1.  To  achieve  this  we  ask 
on  a  polynomial 
the  dealer  of  the  secret  to  make  public  all  t,he  values 
that  were  sent  to  each  player  who  filed  a  complaint. 
We  now  repeat  the  test,  using  new  random  C-Y-S. Each 
player  now  checks  at  his  point  and  at  all  t.hc  poiat,s 
that  were  made  public,  and  if  there  is  an  error  IIC files 
a  complaint. 
If  by  now  more  t,han  1 +  1  pla.yers  I~nvc 
complained  we  all  decide 
take  the  default  zero  polynomial.  Otherwise, 

the  sccrc4  is  bad  i11lci 

that 

Simple 

verification 

of  a  secret 

Claim:  With  very  high  probability, 
of  degree  t. 

ers  are  on  a  polynomial 

all  good  play- 

fi, 

Let 

fj(w’) 

the  values 

polynomial. 

fo  be  the  original 

. . . , fm, 
Let 
m  =  3n  be  random  polynomials  of  degree  t  generated 
by  P,  and  have  P  send  to  Pi 
for 
l,...,  m.  Each  Pi  selectes  a  random  a  #  0  from 
j= 
E  and  sends  it  to  all  the  other  players.  After 
reach- 
ing  agreement  on  the  set  of  Q-S ,the  dealer  broadcasts 
f”  =  cr=‘=o  ak fr;  to  all  play- 
the  set  of  polynomials 
the 
ers.  Each  player  Pi  checks  that  at  the  point  wi, 
shares  he  received  satisfy 
for 
the  required  equations, 
all  the  cr-s.  If  some  Pi  finds  an  error  he  broadcasts  his 
If  1+  1 or  more  player 
complaint. 
file  a  complaint,  we 
decide  that 
the  dealer  is  faulty  and  take  some  default 
value,  say  0,  to  be  the  dealers  secret,  (and  pick  0 for 
all  the  needed  shares). 

Cl&n: 

Let  7’  be  a set  of  good  players  that  did  nob 
the  interpolation 

complain.  Let  J*T be  the 
through 
Then  with  probability 

the  points 

in  T  of  the  original 

at  least 

polynomial 
fi. 

,polynomial 

1-  m2”/lEl 

all  the  polynomials 

f,T  are  of  degree  t. 

Proof  Omitted. 

Keeping 

in  mind 

the  (polynomial) 

complexity 

of 
IEl  2 

the  players  computation,  we can  certainly  allow 
22”.  This  makes  the  error  probability 
small. 
what 
rautlotn  polynomials, 

(The  case of small  IEJ  is similar:  Using  a some- 
sc?t of 
Inrgw 
asks  the  clealcr  to  reveal  c!it,llc?r 

exponentially 

each  player, 

a  diffcrcnt 

using 

in, 

li 

or 

Jo 

+ 

fi-) 

Note  that 

if  n  2  51 +  1,  then  our  srcrct,  sharing 
sclietnc  can  correc.t  2t  errors. 
If  a  secrcl,  is  ilCCPlIl.C’tl 
then  at  most  t  good  players  may  have  wrong  values. 
together  with  at  most  1 more  wrong  values  that 
This 
may  come  from 
the  bad  players,  gives  altogether  at 
most  2t  errors.  Thus  in  this  case the  secret  is uniquely 
defined  and  there  is  a simple  procedure 
value  using  the  error  correcting  procedure. 

to  recover  its 

To  handle 

the  case of  n  =  3t +  1 we  must  make  sure 
that  all  the  pieces  in  the  hands  of  the  good  players  lie 

Proof:  Omitted. 

that 

Note 

is  correct 

if  the  dealer 
player’s  value  will  become  public  during 
tion  process.  This 
that 
polynomials 
ification  procedure  are  completely 
the  secret  polynomial 
ers  will  not  gain  any  information 
secret.  (Detailed  proof  omitted). 

then  no  good 
the  verifica- 
the  fact  that  all  the 
this  ver- 
from 
the  bad  play- 
the  dealer’s 

together  with 
the  dealer  reveals  during 

fo,  ensures  that 

independent 

about 

Absolute 

verification 

of  a  secret 

procedure  describrd  above  lcnvcs  a11 
of  c?rror.  111 this  scc- 

pr0habilit.y 

snlall 

The  verification 
exponent,ially 
Lion  wc  dcscribc  a  srcrct.  vcrificntiou 
leaves  no  probability 
just 

of  errorsl. 
sending 

Instead 

of 

the  shares 

{si}, 

the 

proccdurc,  1.11;il. 

dealer  of  the  secret  selects  n  random  polynomials 
fo@), 

. . . , fn-l(x), 

with 

(l)s;=fi(O)fori=O,...,n-l,and 

(2)  c;:; 

w+  Ji(X)=Ofor 

T=  1,...,21 

In  other  words, 
the  dealer  selects  a  random  polyno- 
f(z,  y),  of  degree  t  in  both  variables  z  and  y, 
mial 
f(O,O)  =  s  (his  secret). 
the  only  restriction 
with 
and 
Then  he  sends  the  polynomials 
W) 
gi(v) 
is  jllst. 

t.0  playtar  Pi,  for  i  =  0,. 

fi(z)  =  f(zlwi) 

1 1) -  1.  TtlC 

I.tlcb  l)urlww 

that 

for 

Of 

f(W’, 

l>\lL 

= 

ITid 
stiarcl 
its  verification, 
j;(P)  and  !/i(u).  At.  (,liis  poitil, 

Lh 

/i(O), 

Si 

= 

(l(:ah’r  idSO  scntls 

C’ZlC11  plirycxr 

f{  Sc>IldS 

l.lIC 

I~oiyllc~nliids 

phycr 

Pj. 

= 

SiJ 

gj(Wi) 

f(Wj,W’) 

I80  C’ilCIl 

good 

fi(WJ) 
No1.t.  L11ilL 
Inlayer 

= 
if  t.h 
I> 
7 .  .  ..S.- 

= 
tltbnlcr 
is  looking 
= 
1 ,j),  then  all  these  points  should  be 
cit.11 coniI>are 
and 
it  is 

(SO,j  9 Slj 
on  his  polynomial 
the  incoming  values  with  his  own  computation 
find  out  which  values  are  wrong.  Furthermore 

is  corrccL, 
at  Lllo 

gj(2/).  Tl iereforc 

sc’qlrc~llcc’ 

WIICYI 

I.~IVII 

SSj 

Pj 

;z 

‘Our  original 

protocol  was  simpliied 

independently 
accomplished 

observed 
in  a  constant 

that 

the  verification 

number  of  communication 

by  Paul  Feldman  who 
can  be 
rounds. 

procedure 



<!-- pdf-page: 7 -->
ctea.r  that 
correct  any  vatlIe  coining 

in  this  case  no  good  player  will  have  to 

from  other  good  plnycrs. 

On  the  ot,her  hand  we  have 

If110 

COrreCt 

Lenknkn: 

phyfY 
given  by  a correct  player,  then  thcrc  is a polynomial  of 
dcgrc%c* 1. 1.11;11. pass(xs through 
points 
of  all  the  corrf~c’t  players. 

l,lic~ int~crpoliitioti 

t0  COrrCCt 

adue 

hS 

Proof:  Simple  algebra.  Omit.ted. 

lemma 

(i,j) 
than 

to  correct  public. 

To  make  sure  t,hat  the  condition  of  this 

is 
satisfied,  each  player  F’j  broadcasts  a request  to  make 
If 
he  had 
the  coordinates 
values,  or 
Pj  detects  more 
t  wrong 
is  clearly 
had  to  correct  his  own  value, 
faulty. 
to 
the 
make  both 
true)  values  si,j  at 
dealer  broadcasts 
all  these  points,  and  the  polynomials 
that  were  to 
fj  and  gj  public 
be  made  public.  Note  that  making 
makes  all  t.he  Sk,j  and  sj,k  public 
for  0  5  k  <  n,  for 
j. 
that.  part.iculat 

In  such  a  case  Pj  broadcasts  a  request 

) z  and  gj(y)  public.  At  this  point 

incoming 
the  dealer 

the  (supposedly 

fj( 

informal.ion 

Now  if  some  player  Pi  observes  that  some  new  pub- 
he  is  holding,  or 
the  polynomials 
lic  si,j 
tout  radicts 
finds  001. I.hr  t,lic  public 
already  contra- 
dicts  ibsclf,  ho  brondcasts  a rcqncsl.  t,o lnnke  all  his  in- 
Ibrmat.ion  public. 
llerc  once  more,  1.11~ dnalcr  mnkes 
public  all  t.llc, rcqucst,ed  inforniabion,  Fiiially,  each  I: 
chc~ks  aI1 t.hc  public  and  private 
he  re- 
ceived  front  the  dealer..  If  Pi  finds  any  inconsistencies 
he  br0adcast.s  a  complaint 
by  asking  all  his  private 
information 

to  be  made  public. 

inforlnntion 

public, 

Likewise, 

information 

If  at  this  point 

t  -+  1  or  more  players  have  asked 
the  dealer  is clearly 
to  make  their 
faulty  and  all  the  players  pick  the  default  zero  poly- 
if  the 
nomial  as  the  dealer’s  polynomial. 
requests  he 
dealer  did  not  answer  all  the  broadcasted 
if  t  or  less 
the  other  hand, 
faulty.  On 
is  declared 
then  there  are  at  least  t  +  1 
players  have  complaint, 
good  players  who  are  satisfied. 
These  uniquely  de- 
f(;c,  y)  and  they  conform  with  all 
fine  the  polynomial 
In  this  case 
the  information 
1.11~ complainilig 
information 
n.s I.hc*ir share>. 
Not.cb 1.11~1. 

of  il~fi~rl~iiJf.ic~ll 
f.llc,rl 
good 
rc975tl(*d tlrlring  1.lie vc~rification  process. 

if  (.lrc <lc>alcr has  disl.ribut.c~d  a correct  W- 
pIi1yc.r 
If  Iiow- 
w;is 
was  bad,  WV do  not  have  to  protect 
(‘v(ar  (.llc? Cif'illCr 
the*  privacy  of  his  informat.ion, 
and  the  vcrificat,ion 
procedure  ensllrcs  us  that  all  the  good  players  values 
lie  on  some  polynomial 

that  was  made  public. 
take  the  public 
players 

of  degree  2. 

(~iwc~ 

(*rv(. 

110 

ally 

cjf 

Some  more 

tools 

Before  going  into  the  computation 
mor(h tools 

stage,  we  need  two 

(1)  Generating 

(and  verifying)  a random  polynonlial 

of  degree  2t,  with  a  zero  free  coefficient. 

(II)  Allowing  a  dcalcr 

to  clistributc 

three  sccrcts,  fr, 

b,  and  c,  and  verifying 

that  c =  u  . b. 

Roth  of  these  are  not  needed  when  n  2  4t  +  1,  but 
are  required 

the  n  =  3t  +  1 case. 

to  handle 

(I)  Generating 

polynomials 

Let  each  player  Pi  distribute 
free  coefficient)  polynomials 
degree  t .  Define  fi  (z)  by 

of  degree  2t 
(including 

the 
t  random 
gi,k(CC), /z =  1,.  . . ,t,  of 

fj(z) 

= 

x2" 

.  Qi,b 

k=l 

and  let  the  players  evaluate 
gi,k-s  their  corresponding  point  on  fi(Z). 

from  their  points  on  the 

After  we  have  verified 

that 

indeed  deggi,k  5  t,  it 
is  also 

5  2t,  and  fi(O)  =  0.  (It 

i=  1,.  . , ,t,  in  /i(z)  are  uniformly 

is  clear  that  degfi(z) 
clear  that 
ofzi, 
and  are  completely 
held  by  any  set  of  at  most  1  players 
incltlde  Pi .) 

the  vector  of  coefficients  of  the  monomials 
distributed 
from  the  information 

indcpentlf~nt 

that  does  not 

Finally,  as our  random  polynomial  we  take 

(II)  Verifying 
Let 

the  player  P  distribute 

that  c =  a.  b 

polynomials  A(z)  and  B(r) 
P to  also  distribute 
c =  a A b, in  such  a way  that 
that 

indeed  c =  a.  b.  Let 

a  and  b  using 
the 
respectively.  We  want 
encoding 
the  players  can  all  verify 

a  random  polynomial 

D(t)  =  A(+).  B(z)  =  c +  clc  +  . . . -t  cZtz2* 

Ilc(2’) 
II,-,(x) 

rt,O +  r1,,2  + 

+  r‘l,t-~xr-l 
= 
=  Pf--1.0 +  ...  +  1’1-,,1--12 t--1+ 

+  CHAP:’ 

+[c2t- 

I  - 

r’(,t- 

*p 

L-h(z) =  l-1,0 f  . . . + q,+&-‘+ 
- 

+[ct - rt,l - rt-l,2 
the  ri,j  are  random  elements 

where 
lects  the  Di(Z)  and  distributes 

. . . -  f2,t--1lZ’ 

from  E.  P  se- 
their  shares  to  all  the 



<!-- pdf-page: 8 -->
players.  After  verifying 
D;(x)  are  of  degree  t,  define 

that  A(X),  B(Z)  and  all  the 

C(X)  =  D(X)  -  2  2’  . Di(X). 

i=l 

that  C(x) 
of  C(z) 

and  verify 
construction 
polynomial 
C(0)  =  a.  b. 

is  also  of  degree  1.  From 

it  is  clear  that  C(z) 

the 
is  a random 
that 

of  degree  t  with 

the  only  restriction 

Proof 

of  Theorem 

3 

to 

the  compubation 

Input, 
its 
We  separate  again 
the  input  stage, 
Computation 
and  Final  stages.  At 
we  let  each  player  enter  his  inputs 
to  the  computa- 
tion  using  our  secret  sharing  scheme,  while  verifying 
of 
that  each  secret  shared  is  indeed  some  polynomial 
degree  t.  The  secret  verification 
the  in- 
puts  of  any  Byzantine  player  is  well  defined,  but  does 
not  ensure 
For  example, 
input 
the  computation 

that 
is  0  or  1.  We  defer  this  type  of  verification 

it  is  in  the  domain  of  our  function. 

in  a  O-l  vote,  we  must  verify 

assures  that 

the 
to 

stage. 

that 

The  final  stage  is exactly 

the  satme as in  the  proof  of 
the  circuit,  and 
Theorem  1.  When  we  have  simulated 
the  pieces  of  a properly  shared 
the  players  are  holding 
secret,  encoding 
they  send  all  the 
pieces  to  one  or  all  the  players.  As  at  most  t  pieces 
are  wrong,  each  player  can  use  the  error  correcting 
procedure  and  recover  the  result. 

the  final  output, 

computation 

stage 

-  Byzantine 

The 
case 

j(a:)+g(z), 

and  c./(z), 

and  g(z) 
Let  u  and  b  be  properly  encoded  by  f(z) 
respectively,  where  by  “properly 
encoded”  we  mean 
that  all  the  pieces  of  the  good  players  are  on  some 
polynomial  of  degree  1.  Since  J(X)  and  g(z)  are  prop- 
erly  encoded  the  polynomials 
properly  encode  a+b,  and  c.a,  for  any  constant  c c  E. 
The  same  argument  of Theorem  1 implies 
that  we can 
of  any  linear  operation  with  no 
do  the  computation 
communication 
Bere  again, 
volved.  To  repeat 
the  degree  reduction 
tion  Lemma,  we  must  make  sure  the  all  the  players 
their  correct  point  on 
use,  as  input 
the  product  polynomial 
To  guaran- 
indeed  happens,  we  use  the  Error  Cor- 
this 
tee  that 
recting  Codes  again. 
Let  Uj  =  f(Ui), 

bi  =  g(W’)  and  Ci  =  h(U’)  =  ai  . bi 
be  the  points  of  Pi  on  these  polynomials.  We ask each 

at  all. 
the  multiplication 

step,  via  the  Matrix  Multiplica- 

the  procedure  of  theorem 

in- 
I,  using 

to  this  proce+re, 

h(z)  =  f(z)g(z). 

is  more 

step 

8 

and  use  this  polynoriiial 

of  dcgr,re  1,  ,~li(~), 
1.0 dis- 

Pi  to  pick  a  random  polynomial 
such  that  ni  =  Ai( 
tribute  aj  as  a  secret,  to  all 
Pi  distrihntcs 
/‘i  t#o tlis- 
tribute  ci  using  the  polynomial  Ci(Z),  wl~ilr  verifying 
Bi(l),  C’,(X)  are  all  of  degree  2, and  that 
that  Ai( 
Ci(O)  =  Ai(O)Bi(O). 

6;  using  Bi(z).  We  atso  ~:k 

the  players.  Similarly, 

that 

to  verify 

We  want 

the  free  coefficients  of  the 
polynomials  Ci(z)  are  all  points  on  the  product  poly- 
that  all  the  free 
nomial  h(z). 
coefficient  of  the  Ai( 
and 
g(z) 

respectively.  We  do  this  as follows. 

and  Bi(+)  are  on  f(z) 

It  is  enough 

to  verify 

The  free  coefficient  of  the  Ai( 

are  a  code  word 
the 
are  properly  distributed.  We  can  therefore  use 

with  at  most  t  errors.  By  our  assumption, 
Ai 
them  to  compute  any  linear 
using 
the  same  Ai(s 
mials 

functional. 
we  can  compute 

In  particular, 
the  polyno- 

all 

n-1 

i=O 

l,... 

that 

if  all 

,2t.  At 

to  recover 

the  Ai(0)  are  correct 

introduced 
this  implies 

by  the  Byzantine 
that 

this  point  all  the  players  reveal 
S?(Z),  enabling  all 
the  value  of  sp  :=  S,.(O),  for 

for  f= 
their  points  on  the  polynomials 
the  players 
r  =  1,...,2t. 
(i.e.  on  a 
Note 
polynomial 
of  degree  9  then  s,  =  Cl for  all  r.  Thus 
the  computed  value  of  the  s,  are  just  a  function  of 
the  errors 
In 
the  value  of  the  s,  does 
particular, 
not  reveal  any  information 
is  held  in  the  hands 
that 
of  the  good  players! 
Since  at  most 
value  of  the  s+, 
the  only 
procedure 
a wrong  Ai( 
if  some  s,  #  0,  all  the  players  compute 
the  correct  value  of  f(wi), 
coordinates, 
constant  polynomial  wit,11 this  value,  instead  of  Ai( 

needed  by  the  error  correction 
.4i(z)  encode 
and  give  the  correct  value.  Therefore, 
the  wrong 
and  use  the 

t  of  the  Ai(0) 
the  so  called  Syndrome  Vector, 

to  detect  which  coordinates 

can  be  wrong, 

information 

the 
is 

players. 

In  asimilar  way  we can  check  and  correct  the  B;(Z). 
the  Ci(z), 

We  can,  therefore,  also  check  (and  correct) 
to  the  linear  com- 
so  we  are  sure  that  all  the  inputs 
putation  we  have  to  do  in  the  degree  reduc6ion  pro- 
cedure  are  correct. 

Note 

that  much  of  this 

71  > 
4t  +  1, because  then  we  can  still  correct  up  to  t  errors 
on  polynomials 
In  this  case  we  can  do 
the  error  correction  on  the  points  of  h(r)  directly. 

of  degree  2t. 

is  not  needed  when 

As 

in  the  proof  of  Theorem  1,  we  have, 

Theorem 
every  t  <  n/3 
resilient 

and  t-pn’vate. 

3:  For  every  probabilistic 
there  exists  a  protocol 

function  and 
that  is  both  t  - 



<!-- pdf-page: 9 -->
For  completeness  we  state, 

[Yl]  A.  C.  Yao,  How  to  generate  and  exchange  se- 

Theorem 

4:  There  are  functions 

for  which 

there 

is  no  n/3  -  resilient 

protocol. 

from  the  lower  bound 
for 
in  this  model.  We  note  that 
operation, 

Proof.  Follows  immediately 
Byzantine  Agreement 
even  if  we  allow  broadcast  as  a  primitive 
theorem  4  remains 
hibit 
functions 
puted  tesilient,ly,  when  one  player 
alizc%s ir~~n~ctli;rt.cly  to  n/3. 

is  because  we  can  ex- 
for  three  players  that  cannot  be  com- 
is  bad.  This  gener- 

true.  This 

Remark: 

the  remarks  following 
of  theorem  1 apply  also  to  theorem  3. 

All 

the  statement 

References 

[BL]  M.  Ben-Or  and  N.  Linial,  Collective  coin  flip- 

crets,  STOC86. 

[Y2]  A.  C.  Yaq  On 

the  succession  problem 

for 

Byzantine  Generals,  manuscript, 

(1983). 

Appendix 

Formal  Not  at ion 

Let  F’  I)(: a  field.  Let  CJ =  P’”  denote  the  standard 
dimensional 
of  72 x  n  matrices  over  F. 

vector  space  over  1” and  M,,(F) 

7t- 
the  ring 

Let  R  be  a  random  variable  with  distribution 
over  F.  Then  Rk  (R*)  denotes  k  (finitely  many) 
dependent  draws  from  D. 
Comment: 
nite,  and  D  the  uniform  distribution 

Unless  otherwise  specified,  F  will  be  fi- 

over  F. 

D 
in- 

ping,  FOCS86. 

The  Basic  Model: 

[CCD]  D.  Chaum,  C.  Crepeau  and  I.  Damgard,  Mul- 
secure  protocols,  These 

unconditionally 

tiparty 
proceedings. 

[DH]  W.  Dime  and  M.  E.  Helman,  New  directions 
Inform.  Theory, 

IEEE  Trans. 

in  cryptography, 
Vol.IT-22,pp.644-654, 

1976. 

IDS]  D.  Dolev  and  R.  Strong,  Polynomial  algorithms 
for  multiple  processor  agreement.  STOC82. 

[Fhsl]  I’.  Fcldn~an  and  S.  Micali,  Opt.imaI  algorit,hms 
for  Byzantine  agreement,  These  proceedings. 

[GhlWl] 

0.  Gold  riech,  S.  Micali  and  A.  Wigderson, 
Proofs  that  yield  nothing  but  the  validity  of  the 
assertion,  and  a  methodology 
protocol  design,  FOCS86,  pp.  174-187. 

of  cryptographic 

Intuitively, 

Fix  n  >  0  and  a  field  F. 

is  a  complete  synchronous 

an  (n,  F)  - 
network 
network  of  n 
At 
probabilistic  machines 
every  round,  each  player  can  send  one  message  (el- 
receive  a  message 
ement  of  F)  to  each  other  player, 
from  each  other  player,  and  perform  arbitrary 
com- 
putation. 

(players)  PO, PI,  . . . . P,-l. 

If  we assume  for  convenience 

too,  a  round  of  communication 

that  players  send  mes- 
is 
sages to  themselves 
neatly  described  by  a  matrix  A4  E  M,(F), 
where 
each  Pi  sent  the  ith  row  of  M,  and  receives  the  ith 
column  of  M. 
the  security  of  private 
channels). 

formalizes 

(This 

Formally,  a  T  round 

(n,  F)  -  network 

is  a  set  of 

players  {PO, PI,  . . . . P,,-1).  Each  Pi  is  a  tuple 

Pi  =<  Qi,q!O)  Rig&  > 

t 

, 

[GMW2]  0.  G  Id o 
son,  How 
pp.  218-229. 

riech,  S.  Micah  and  A.  Wigder- 
to  play  any  mental  game,  STOC87, 

where  Qi  is  a  set  of  states,  qj (O) the  initial  state,  Ri  is 
a  random  variable  over  F  (distributed 

like  R)  and 

&:[!l’I  x&i 

x  F”  X  R:  -*Qi  X  F” 

[GMR]  S. G o Id wasser,  S. Micali  and  C.  Rackoff,  The 
proof  sys- 

of  interactive 

knowledge  complexity 
tems,  STOC85,  pp.  291-304. 

[PSL]  M.  Pease,  R.  Shostak  and  L.  Lamport,  Reach- 
in  the  presence  of  faults,  JACM 

ing  agreement 
Vol.  27,  pp.  228-234,  (1980). 

[PW]  W.  W.  Peterson  and  E.  J.  Weldon,  Error  cor- 
recting  codes,  Second  Ed.,  hll’l’  Press,  (1972). 

[Sh]  A.  Shamir,  How  to  share  a  secret,  CACM,  22, 

pp.  612-613,  (1979). 

9 

is  a  transition 
state,  previous 
computes 

A  protocol 

function 
round 

that  given  a  round  number, 
tosses 

input  and  private  coin 

the  next  state  and  this  round’s  output. 
>, 
is  simply  6  =<  60,61,.  . . , a,-, 

the 
to  each  player  what 

functions  prescribing 

transition 
to  do  in  each  round. 
run  M 

A 

the  communication 

(Ml,  M2, 
ing 
Note 
{qi’)}, 
dom  draws  from  D. 

that  M 

of  a  protocol 
. . , MT),  Mj  E  M,(F) 

in  rounds 

is  a  random  variable, 

6 
is  a  sequence 
of  matrices  describ- 
j  =  1,2,.  . . ,T. 
depending  on 
the  ran- 

(=  R’), 

the  initial  states,  and  {R?}, 



<!-- pdf-page: 10 -->
A  (probabilistic) 

function 

is. a  function 

f, 

f:F” 

x  R”’  +  F”. 

if 

exactly 

Intuitively, 

is  distributed 

a  protocol 
i’i 

cctmpute::  a  function  UT if 
Vi  E  F  be:bre 
is  given 
‘1’ it  knows  ui,  such  that 
like 
For  convenience  we  denote  a  vector 
let  qIj’  derote 

for  all  v  E  F”, 
round  1,  then  after  round 
7.4 =<  U(),Ul,.‘.,  u,-  1  > 
f(v  x  R”). 
<  ~0, ~1, . . . . ~“-1  >  by  <  oi  >.  Also, 
the  state  of  Pi  after  round 
define  what 
to  compute  a  function,  we  assume  fixed 
functions, 
output 
Now  6  computes 
we  have  <  Oi(qy’) 
variables). 

.Pnd 
Ii,  Oi:  Qi  .+  F  for  each  player  Pi. 
if  for  every  choice  of  <  qi”)  >, 
f, 
>= 
(as  ranc.om 
x  R”‘) 

it  means  for  a  protocol 

To  formally 

f(li(qiO’) 

input 

i. 

Some 

Intuition 

The  bad  players  in  our  model  can  completely  coor- 

the 

transition 

their  actions.  Hence,  for  a  bad  set  (coalition) 
l}, 
[n]  = 

dinate 
{0,1,2  )“.,  n  - 
c  c 
tions  6i,  i  E  C  are  replaced  by  arbitrary 
6:  that  compute 
from  the  joint 
viously 
(Pi), 
C  is  bad  (in  this  sense)  by  6~. 

func- 
functions 
the  next  state  and  messages  of  Pi 
of  the  current  states,  pre- 
received  messages  and  random  choices  01’ all 
in  which  a set 

i  E  C.  We  denote  any  protocol 

information 

two 

We  d&tinguish 

types  of  bad  behavior. 

benign  (gossip)  kind, 
sages  according 
learn  as  much  as  they  can  from 
forces.  The  malign 
tions  on  the  bad  players, 
arbitrary. 

to  the  original  protocol  6,  but 
it  by  joining 

The 
in  which  bad  players  send  mes- 
tr:r  to 
their 
kind  puts  no  restric- 
the  6:  can  really  be 

(Byzantine) 
i.e. 

To  formalize 

the  benign  kind  of  bad  behavior  we 

need  the  foliowing  definition: 
Two  protocols  6 and  6’ look  alike  if  their  runs  have  the 
i.e.  M  =  M’  as random  variables, 
same  distribution, 
state  c:  qi”)  >  of  all  players. 
for  every  fixed 

initial 

A  bad  coalition  C  is  called  gossip  if  the  protocol  6~ 

looks  like  6,  otherwise 

it  is  catted  ByranZine. 

f  -  this  follows 

In  the  case of  gossip,  we  don’t  have  to  worry  about 
from  the 
“took  alike”.  Here  all  we  shalt  have  to  pre- 

the  correctness  of  cotnputing 
definition 
vent,  is  leakage  of  information. 
In  case  of  Byzantine 
faults,  we  will  have  to  guarantee  also  the  correct:ress 
of  the  computation.  We  proceed  now  to  define 
the 
important 
Privacy 

notions  of  Privacy  and  Correctness. 

(preliminary): 

a  coalition  C  did  not 

Intuitively, 
f, 
from  a  protocol 
compute  after 
(from 
could  compute  only  from  its  inputs 
its  components  of  the  function 

for  computing 

the  protocol 

values. 

learn  anything 

it  can 
if  whatever 
its  final  states), 
it 
(initial  states)  and 

Let QC = ni,,  Qi and  A  be  an  arbitrary 

set.  Also, 
,...,  u,-  1 >,  UC  denotes  the  sub-vector 

in  a  protocol  6  (for  computing 

ifu=<ue,ur 
of  u  that  contains  ui, 
ignorant 
ery  set  of  initial 
that 
looks  like  d ,nd  every  fifnct,idn  g’:  Qc 
exists  a  funclion  d: Qc  x  Ftct  -+  A  rrnt,isfying 

i  E  C.  Formally,  a  set. C  is 
if  for  ev- 
states  <  Jo)  >  every  prot.ocot  6 
c 
.4 ttierc 

I)* 

+ 

s’(p) 

=  9(&f, 

(<  ZiG?j”))  >)c) 

(*) 

A  protocol  6  (for  computing 

f) 

is  t-private 

if  every 

coalition  C  with 
Correctness: 

ICI  5  t  is  ignorant. 

This 

inputs, 

issue  is  problematic, 
their 

since  some  of  the  bad 
the 
initial 
players  can  obliterate 
(a  simple  example 
value  is  not  well  defined 
function 
for 
is  Byzantine 
that 
every  set  B  C  [n],  we  need  a  (sub)function 
depends  on  the  input  coordinates  of  only 
[n]  \  B.  (a 
special  case  is  assigning  default  values  to  input  coor- 
dinates 

To  ignore  bad  inputs 

agreement). 

and 

off 

in  B). 
So  now  by 
{f~:  F n\B  x  RM 
the  original 
agreement) 
cinctly  described. 

f  we  mean  a  family 

-  F”}, 

I3  E 
f.  Typically, 

funct8ion 
this  exponemiat 

size  fanrity 

of 
[n.],  with 

funct,ions 
f+  being 
(as  in  13yza.ut,iuc, 
is  very  suc- 

So now,  a romput,ation 

is  correct,  if  all  good  ptaycrs 
fB,  where  L3 is a subset  of  the  bad 

compute  a function 
players. 

More  formally,  a coalition  C  is  harmless  if  for  every 

set  of  initial  states  <  *i(O) >  and  every  prot.ocol  6~, 

{<  Oi(PjT)) 

>)[n]\C 

= 

fB({< 

Ii(Q!‘)) 

>l[n]\B)[n]\C 

for  some  B  C  C. 
A  protocol 

is  l-resilient 

if 

every  coalition  C  with 

ICI  5  1 is  harmless. 
Revisited: 
Privacy 
For  the  case  of  Byzantine 
that  6~  looks  like  5 is  invalid. 
tion  C  we  can  remove  this  assumption 
inition  of  ignorance,  and  replace 
fB,  the  funct.ion 
the  good  players. 

f 
that  will  actually 

faults, 
the  assumption 
For  any  harmless  coali- 
from  the  def- 
in  (*)  above,  by 
be  computed  by 

Now  the  notion  of  a protocol 

ttrat  is both  t-resilient 

and  l-private 

is  well  defined. 

10 


