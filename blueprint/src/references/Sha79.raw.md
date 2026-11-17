<!-- generated-by: proofmatch local extraction -->
<!-- source-pdf-sha256: a76120fbec44ae3b8dd1fbc5ade85a0c032358f1c692c918d8fb5d586ed7f8b1 -->
<!-- extractor: pdfminer.six v20260107 -->

<!-- pdf-page: 1 -->
Programming 
Techniques 

R.  Rivest 
Editor 

H o w   to  Share  a  Secret 
Adi  Shamir 
Massachusetts  Institute of Technology 

In  this  paper  we  show  how  to  divide  data  D  into  n 

pieces  in  such  a  way  that  D  is  easily  reconstructable 
from  any  k  pieces,  but  even  complete  knowledge  of 
k -  1  pieces  reveals  absolutely  no  information  about  D. 
This  technique  enables  the  construction  of  robust  key 
management  schemes  for  cryptographic  systems  that 
can  function  securely  and  reliably  even  when  misfor- 
tunes  destroy  half  the  pieces  and  security  breaches  ex- 
pose  all  but  one  of  the  remaining  pieces. 

Key  Words  and  Phrases:  cryptography,  key  manage- 

ment,  interpolation 

CR  Categories:  5:39,  5.6 

1.  Introduction 

In  4,  Liu  considers  the  following  problem: 

Eleven scientists are working on a secret project. They wish to lock 
up  the  documents in  a  cabinet  so that  the  cabinet  can  be  opened  if 
and  only  if  six  or  more  of  the  scientists  are  present.  What  is  the 
smallest  number  of  locks  needed?  What  is  the  smallest  number of 
keys to  the  locks  each  scientist must  carry? 

It is not  hard  to  show  that  the  minimal  solution  uses 462 
locks  and  252  keys  per  scientist.  These  numbers  are 
clearly 
they  become  exponentially 
worse  when  the  number  of  scientists  increases. 

impractical,  and 

In  this  paper  we  generalize  the  problem  to  one  in 
which  the  secret  is  some  data  D  (e.g.,  the  safe  combina- 

Permission to copy without fee all  or part of this material  is granted 
provided that the copies are not made or distributed for direct commer- 
cial  advantage,  the ACM  copyright notice and  the title  of the publica- 
tion  and  its date  appear,  and  notice is given that copying is by permis- 
sion of the Association for Computing Machinery.  To copy otherwise, 
or  to  republish,  requires a  fee a n d / o r   specific permission. 

Author's  present  address:  A.  Shamir,  Laboratory  for  Computer 
Science,  Massachusetts  Institute  of  Technology,  Cambridge,  MA 
02139. 

This research was supported by the  Office of Naval Research under 

contract  no.  N00014-76-C-0366. 
@1979  ACM  0001-0782/79/1100-0612  $00.75. 

612 

tion)  and 
in  which  nonmechanical  solutions  (which 
manipulate  this  data)  are  also  allowed.  Our  goa !  is  to 
divide D  into  n  pieces  D, . . . . .   D n in  such  a  way that: 

(1)  knowledge  of  any  k  or  more  D i  pieces  makes  D 

easily computable; 

(2)  knowledge  of  any  k -   1 or  fewer  Di  pieces  leaves  D 
completely  undetermined  (in  the  sense  that  all  its 
possible values  are  equally likely). 

Such  a  scheme is called  a  (k,  n)  threshold  scheme. 

Efficient  threshold  schemes  can  be very helpful  in the 
management  of  cryptographic  keys.  In  order  to  protect 
data we can encrypt it,  but in order to protect the encryp- 
tion key we need a  different method  (further encryptions 
change  the  problem  rather  than  solve  it).  The  most 
secure key management  scheme keeps the key in a single, 
well-guarded  location  (a computer,  a  h u m a n   brain,  or  a 
safe).  This  scheme  is  highly  unreliable  since  a  single 
misfortune  (a  computer  breakdown,  sudden  death,  or 
sabotage) can make the information  inaccessible.  An ob- 
vious solution is to store multiple copies o f  the key at dif- 
ferent locations,  but  this increases  the  danger  of security 
breaches  (computer  penetration~  betrayal,  or  h u m a n   er- 
rors).  By using  a  (k,  n)  threshold  scheme  with  n  = 2 k -   1 
we  get  a  very  robust  key  management  scheme:  We  can 
recover  the  original  key even when  n/2J  =  k -   1 of the  n 
pieces  are  destroyed,  but  our  opponents  cannot 
reconstruct  the  key  even  when  security  breaches  expose 
n/21  = k -   1 of  the  remaining  k  pieces. 

In  other  applications  the  tradeoff  is  not  between 
secrecy  and  reliability,  but  between  safety  and  conve- 
nience  of  use.  Consider,  for  example,  a  c o m p a n y   that 
digitally  signs  all  its  checks  (see  RSA  5). 
If  each  ex- 
ecutive is given a  copy of the  c o m p a n y ' s  secret signature 
key,  the  system  is  convenient  but  easy  to  misuse.  If the 
cooperation  of all the  c o m p a n y ' s  executives  is necessary 
in  order  to  sign  each  check,  the  system  is  safe  but  in- 
convenient.  The  standard  solution  requires  at  least three 
signatures  per  check,  and  it  is  easy to  implement  with  a 
(3,  n)  threshold  scheme.  Each  executive  is  given  a  small 
magnetic  card  with  one  Di  piece,  and  the  c o m p a n y ' s  
signature  generating  device  accepts  any three  of them  in 
order to generate (and later destroy) a t e m p o r a r y  copy of 
the  actual  signature  key D.  The  device  does  not  contain 
any  secret information  and  thus  it need  not  be protected 
against  inspection.  An  unfaithful  executive must  have at 
least  two  accomplices  in  order  to  forge  the  c o m p a n y ' s  
signature  in  this  scheme. 

Threshold  schemes are ideally suited to applications in 
which  a  group  of  mutually  suspicious  individuals  with 
conflicting  interests  must  cooperate.  Ideally  we  would 
like the  cooperation  to  be based  on  mutual  consent,  but 
the veto power this mechanism gives to each m e m b e r  can 
paralyze  the  activities  of the  group.  By  properly  choos- 
ing  the  k  and  n  parameters  we  can  give  any  sufficiently 
large  majority  the  authority  to  take  some  action  while 
giving any sufficiently large minority the  power to block 
it. 

Communications 
of 
the  ACM 

November  1979 
Volume 22 
Number  11 



<!-- pdf-page: 2 -->
2.  A  Simple  (k,  n)  Threshold  Scheme 

Our  scheme  is  based  on  polynomial'  interpolation: 

given  k  points  in  the  2-dimensional  plane  (x,,  y,) . . . . .  
(xk,  Yk). with  distinct  xi's ,  there  is  one  and  only  one 
polynomial q(x)  of degree k -  1 such that  q(x)  =yi for all 
i.  Without  loss of generality,  we can assume that the data 
D  is  (or  can  be  made)  a  number.  To  divide  it  into  pieces 
degree  polynomial 
D~,  we  pick  a 
in  which  a o = D  ,  and 
q ( x ) = a o + a l x +  
evaluate: 

random  k - 1  
ak_ixk-~ 

. . .  

D~ = q(1) . . . . .   D i = q(i) . . . . .   D n = q(n). 

Given  any  subset  of  k  of  these  D~ values  (together  with 
their  identifying  indices),  we can  find  the  coefficients  of 
q(x)  by 
then  evaluate  D = q ( O ) .  
Knowledge  of  just  k -   1  of  these  values,  on  the  other 
hand,  does not  suffice in  order  to  calculate D. 

interpolation,  and 

To  make  this  claim  more  precise,  we  use  modular 
arithmetic  instead  of real  arithmetic.  The  set  of integers 
modulo  a  prime  number p  forms  a  field  in  which  inter- 
polation  is possible.  Given  an  integer  valued  data  D,  we 
pick  a  prime p  which  is  bigger  than  both  D  and  n.  The 
coefficients  a~ . . . . .  
ak_~ in  q(x)  are  randomly  chosen 
from  a  uniform  distribution  over  the  integers  in  0,  p), 
and  the  values D~ . . . . .   Dn are  computed  modulo p. 

Let  us  now  assume  that  k - 1   of  these  n  pieces  are 
revealed to  an opponent.  For each candidate  value D '   in 
0,  p)  he  can  construct  one  and  only  one  polynomial 
q  '(x)  of degree  k -   1 such  that  q  '(0) = D '   and  q  '(0 =D~ 
for  the  k -   1 given  arguments.  By  construction,  these p 
possible polynomials are equally likely,  and  thus  there  is 
abolutely  nothing  the  opponent  can  deduce  about  the 
real value  of D. 

Efficient  O(n  log 2 n) algorithms  for polynomial evalu- 
ation  and  interpolation  are  discussed  in  1  and  3,  but 
even  the  straightforward  quadratic  algorithms  are  fast 
enough  for  practical  key  management  schemes.  If  the 
number  D  is long,  it  is  advisable to  break  it  into  shorter 
blocks  of bits  (which  are  handled  separately) in  order  to 
avoid  multiprecision  arithmetic  operations.  The  blocks 
cannot  be  arbitrarily  short,  since  the  smallest  usable 
value  of p  is  n +  1  (there  must  be  at  least  n +  1 distinct 
arguments  in  0,  p)  to  evaluate q(x)  at).  However,  this  is 
not  a  severe  limitation  since  sixteen  bit  modulus  (which 
can  be  handled  by  a  cheap  sixteen  bit  arithmetic  unit) 
suffices  for  applications  with  up  to  64,000  D~ pieces. 

Some  of  the  useful  properties  of this  (k,  n)  threshold 
scheme  (when  compared  to  the  mechanical  locks  and 
keys solutions)  are: 

(1)  The  size of each  piece does  not  exceed the  size of the 

original  data. 

(2)  When  k  is  kept  fixed,  D~ pieces  can  be  dynamically 
added  or  deleted  (e.g.,  when  executives join  or  leave 

LThe polynomials can  be replaced by any  other collection of func- 

tions which are easy to evaluate and to  interpolate. 

613 

the  company)  without  affecting  the  other  D i pieces. 
(A  piece  is  deleted  only  when  a  leaving  executive 
makes  it completely inaccessible,  even to  himself.) 
(3)  It  is  easy  to  change  the  D i pieces  without  changing 
the  original data D - - a l l   we need  is a  new polynomial 
q(x)  with  the  same  free  term.  A  frequent  change  of 
this type can greatly enhance  security since the pieces 
exposed  by security breaches  cannot  be accumulated 
unless  all  of  them  are  values  of  the  same  edition  of 
the  q(x)  polynomial. 

(4)  By using tuples  of polynomial values as Di pieces,  we 
can get a  hierarchical  scheme in which  the  number of 
pieces  needed  to  determine  D  depends  on  their  im- 
portance.  For  example,  if  we  give  the  c o m p a n y ' s  
president  three  values  of  q(x),  each  vice-president 
two  values  of  q(x),  and  each  executive  one  value  of 
q(x),  then a  (3, n) threshold  scheme enables checks to 
be  signed  either  by  any  three  executives,  or  by  any 
two executives one of whom is a vice-president,  or by 
the  president  alone. 

A  different  (and  somewhat  less  efficient)  threshold 

scheme was  recently developed  by G.R.  Blakley  2. 

Received  April  1979; revised  September 1979 

References 
1.  Aho,  A.,  Hopcroft, J.,  and Ullman,  J.  The Design  and Analysis 
o f  Computer AIgorithms.  Addison-Wesley, Reading, Mass.,  1974. 
2.  Blakley,  G.R.  Safeguarding cryptographic keys.  Proc.  AFIPS 
1979 NCC,  Vol. 48,  Arlington, Va.,  June  1979, pp.  313-317. 
3.  Knuth,  D.  The Art o f  Computer Programming,  Vol.  2: 
SeminumericalAlgorithms.  Addison-Wesley, Reading, Mass.,  1969. 
4.  Liu,  C.L.  Introduction  to  Combinatorial  Mathematics.  McGraw- 
Hill,  New  York,  1968. 
5.  Rivest,  R.,  Shamir, A.,  and  Adleman, L.  A  method for obtaining 
digital  signatures and  public-key cryptosystems. Comm.  A CM 21,  2 
(Feb.  1978),  120-126. 

Communications 
of 
the ACM 

November 1979 
Volume 22 
Number  11 


