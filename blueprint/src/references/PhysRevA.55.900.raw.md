<!-- generated-by: proofmatch local extraction -->
<!-- source-pdf-sha256: bbdd8e5c39493ec02f6852ab4a6ac223d49a452f0b7d0bd31df5f1982f095a2d -->
<!-- extractor: pdfminer.six v20260107 -->

<!-- pdf-page: 1 -->
PHYSICAL REVIEW A

VOLUME 55, NUMBER 2

FEBRUARY 1997

Theory of quantum error-correcting codes

Emanuel Knill1,* and Raymond Laﬂamme2,†
1CIC-3, Mail Stop B265, Los Alamos National Laboratory, New Mexico 87545
2T-6, Mail Stop B288, Los Alamos National Laboratory, New Mexico 87545
(cid:126)Received 14 June 1996(cid:33)

Quantum error correction will be necessary for preserving coherent states against noise and other unwanted
interactions in quantum computation and communication. We develop a general theory of quantum error
correction based on encoding states into larger Hilbert spaces subject to known interactions. We obtain nec-
essary and sufﬁcient conditions for the perfect recovery of an encoded state after its degradation by an
interaction. The conditions depend only on the behavior of the logical states. We use them to give a recovery-
operator-independent deﬁnition of error-correcting codes. We relate this deﬁnition to four others: the existence
of a left inverse of the interaction, an explicit representation of the error syndrome using tensor products,
perfect recovery of the completely entangled state, and an information theoretic identity. Two notions of
ﬁdelity and error for imperfect recovery are introduced, one for pure and the other for entangled states. The
latter is more appropriate when using codes in a quantum memory or in applications of quantum teleportation
to communication. We show that the error for entangled states is bounded linearly by the error for pure states.
A formal deﬁnition of independent interactions for qubits is given. This leads to lower bounds on the number
of qubits required to correct e errors and a formal proof that the classical bounds on the probability of error of
e-error-correcting codes applies to e-error-correcting quantum codes, provided that the interaction is domi-
nated by an identity component. (cid:64)S1050-2947(cid:126)97(cid:33)07501-X(cid:35)

PACS number(cid:126)s(cid:33): 03.65.Bz, 89.70.(cid:49)c, 89.80.(cid:49)h, 02.70.(cid:50)c

I. INTRODUCTION

Within the past few years, quantum computation and
communication have undergone a dramatic evolution. From
being subjects of primarily academic interest, they have be-
come ﬁelds having an enormous potential for revolutionizing
computer science and cryptography, as well as an impact on
issues of national security, and even potentially commercial-
izable applications. This has resulted not only from the de-
velopment of new algorithms such as quantum factoring (cid:64)1(cid:35),
but also as a consequence of recent experimental work on
implementations of individual quantum gates (cid:64)2–4(cid:35) and of
quantum cryptography (cid:64)5(cid:35).

Unfortunately, the quantum states required to carry out a
computation are very sensitive to the imperfections of the
hardware, and above all, to the decoherence (cid:64)6(cid:35) caused by
interaction with the environment (cid:126)by environment we mean
all the degrees of freedom which can have unwanted inter-
actions with the computer(cid:33). This fragility of a quantum com-
puter (cid:64)7–9(cid:35) is closely tied to its function: it acts as a sophis-
ticated, nonlinear interferometer. The coherent interference
pattern between the multitude of superpositions is essential
for taking advantage of quantum parallelism, which is the
key feature allowing one to explore aspects of an exponen-
tially large number of possible solutions.

To ensure that the fragility of quantum states does not
destroy our ability to extract the desired interference pattern
requires techniques for correcting errors. It is interesting to
draw a parallel between the state of the art in quantum com-
putation today and that of classical computers in the 1940s.

*Electronic address: knill@lanl.gov
†Electronic address: laf@time.lanl.gov

At that time it was often said that classical computers would
not be very useful because errors in the computer itself
would render the result untrustworthy (cid:64)10(cid:35). These doubts dis-
appeared after the discovery of powerful error-correction
techniques. Similar doubts are being expressed about the fea-
sibility of the large scale application of quantum computers.
These doubts are partially based on the belief that to perform
an error-correction step, knowledge of the exact state of the
computer is required. Such knowledge would destroy the
quantum mechanical properties of the state. However, Shor
(cid:64)11(cid:35) has shown that in a restricted model of errors (cid:126)similar to
that which is assumed for classical error correction(cid:33) it is
possible to restore a state using only partial knowledge of the
state of the quantum computer. Many codes have since been
discovered which correct for speciﬁc interactions (cid:64)12–18(cid:35).
As a result, it may now be possible to implement practical
quantum memories and achieve very reliable quantum com-
munication. These ideas have opened the path to a general
theory of quantum error correction: the subject of this paper.
This manuscript is organized as follows: In Sec. II, we
give an intuitive approach to the theory of quantum error
correction and introduce some simple examples of the basic
concepts. These concepts are formalized in Sec. III, where
the notions of ﬁdelity and error of a code are introduced.
Instead of considering explicit encoding and decoding opera-
tors, we introduce recovery superoperators. These operators
allow us to study the most general physical processes which
can be used for error correction. Quantum error-correcting
codes which permit complete restoration of the encoded state
can then be characterized. We give necessary and sufﬁcient
conditions for being able to recover the state of a system
after it has evolved through a superoperator. These condi-
tions depend only on the subspace of the code. Several
equivalent characterizations are possible and we give four:

1050-2947/97/55(cid:126)2(cid:33)/900(cid:126)12(cid:33)/$10.00

55

900

© 1997 The American Physical Society



<!-- pdf-page: 2 -->
55

THEORY OF QUANTUM ERROR-CORRECTING CODES

901

one based on the existence of a left inverse of the interaction
superoperator, one using the explicit representation of the
coding space as a tensor product of the code with a quantum
error syndrome, one exploiting the effect of the operators on
a completely entangled state, and, ﬁnally, one using an in-
formation theoretic identity. In Sec. IV we discuss several
methods for implementing the recovery operator in practice
and point out that if certain additional properties hold, the
recovery operator can be substantially simpliﬁed. Next, in
Sec. V we discuss independent interactions for strings of
qubits (cid:126)or other systems(cid:33). These types of interactions are the
natural generalization of classical independent errors. After a
short discussion of the physical interpretation and relevance
we give a proof that it is not possible to obtain a one-error-
correcting code for one qubit using a coding space of only
four qubits. This is generalized in a theorem about correcting
e errors and a characterization of e-error-correcting codes.
Finally we address the important issue of the ﬁdelity of
codes with imperfect recovery operators. We observe that a
correct measure of ﬁdelity must take into account any en-
tanglements of the state. We show that the ﬁdelity of the
recovery of an entangled state can be bounded below in
terms of the pure state ﬁdelity. An example is provided to
show that our bound is best possible. We end this section by
proving a bound on the ﬁdelity of codes where one of the
interaction operators is proportional to the identity. In Sec.
VI we conclude the paper with a ﬁnal summary of the results
and their implications.

II. AN INTUITIVE APPROACH

Coherent quantum states are used in quantum communi-
cation and quantum computation. Both situations involve the
manipulation of states by unitary operations where some de-
sired information is eventually extracted from parts of the
state by measurement. Quantum communication involves
multiple parties with limited communication capabilities and
focuses more on the transmission of states over potentially
noisy channels, while quantum computation involves only
one party and focuses on the unitary transformations in-
volved in achieving the ﬁnal state. In both cases, loss of
coherence occurs while executing the necessary operations,
and when some of the systems are either transmitted or tem-
porarily preserved in memory. This loss of coherence results
in a reduction of the probability of getting the correct answer
after completion of the required operations. For short dis-
tance communication or small scale computations, the best
way to avoid errors is to minimize this loss by isolating the
state as well as possible and improving the accuracy of the
unitary transformation used. For larger distances and long
calculations errors in the state are inevitable and it is neces-
sary to devise a scheme for returning the state to the desired
one. Here we focus on the problem of preserving a coherent
state subject to unwanted interactions in a quantum memory
or channel.

In classical communication and computer memories, cor-
rupted information can be restored by introducing redun-
dancy, for example by copying all or part of the information
to be preserved (cid:64)19(cid:35). Unfortunately, it is not possible to use
a simple redundancy scheme for quantum states, primarily
because the ‘‘no-cloning’’ theorem (cid:64)20(cid:35) prevents the dupli-

cation of quantum information. However, it has recently
been realized (cid:64)11(cid:35) that it is possible to correct a state against
certain known errors by spreading the information over
many qubits through an encoding. The goal is to ﬁnd an
encoding which behaves in a speciﬁc way (cid:126)described below(cid:33)
under evolution by the interaction superoperator. The behav-
ior is such that it permits recovery of the original state. This
works only for speciﬁc types of superoperators. In practice,
error-correction schemes cannot correct all errors perfectly
but only a subset of them. The quality of a scheme can be
evaluated by its ﬁdelity, i.e., the overlap between the cor-
rected state with the wanted one.

An essential part of the error-correction scheme is the
encoding of the quantum information. Consider the simplest
nontrivial case of encoding a single qubit. In this case the
general state to be protected is of the form (cid:117)(cid:67)(cid:38)(cid:53)(cid:97)(cid:117)0(cid:38)(cid:49)(cid:98)(cid:117)1(cid:38).
The idea is to map (cid:117)(cid:67)(cid:38) into a higher dimensional Hilbert
space (cid:126)using ancilla qubits which are assumed to be in their
(cid:117)0(cid:38) states initially(cid:33):

(cid:126)(cid:97)(cid:117)0(cid:38)(cid:49)(cid:98)(cid:117)1(cid:38))(cid:117)000•••(cid:38)!(cid:97)(cid:117)0 L(cid:38)(cid:49)(cid:98)(cid:117)1 L(cid:38).

(cid:126)1(cid:33)

(cid:38) are called the logical zero
(cid:38) and (cid:117)1L
This deﬁnes the code. (cid:117)0L
and the logical one of the qubit which we want to preserve,
respectively. The new state in Eq. (cid:126)1(cid:33) should be such that any
error induced by an incorrect functioning of the computer
maps it into one of a family of two-dimensional subspaces
which preserve the relative coherence of the quantum infor-
mation (cid:126)i.e., in each subspace, the state of the computer
should be in a tensor product state with the environment(cid:33). A
measurement is then performed which projects the state into
one of these subspaces. The original state can be recovered
by a unitary transformation which depends on which of these
subspaces has been observed. A fact to be established in Sec.
IV is that for every error-correcting code, the original state
can be recovered by a measurement followed by a unitary
operation determined by the outcome of the measurement.

In order to ﬁnd good encodings, it is essential to under-
stand the types of error which can occur. We assume that the
initial state is (cid:67)
i , which undergoes interaction with an envi-
ronment. This leaves the computer in the reduced density
matrix

(cid:114)
f

(cid:53)$(cid:126)(cid:117)(cid:67)

ı(cid:38)),

(cid:126)2(cid:33)

where $ is the superoperator associated with the interaction.
In the case where the environment is not initially entangled
with the system (cid:114)

f can be written in the form (cid:64)21(cid:35)

(cid:114)
f

(cid:53)(cid:40)

a

A a

(cid:114)
† .
iA a

(cid:126)3(cid:33)

A choice of operators A a can be determined from an ortho-
normal basis (cid:117)(cid:109)
(cid:38) of the environment, the environment’s ini-
a
tial state (cid:117)e(cid:38), and the evolution operator U of the whole
system as follows:

A a

(cid:53)(cid:94)(cid:109)
a

(cid:117)U(cid:117)e(cid:38).

(cid:126)4(cid:33)

With A a written in this way, it can be seen that



<!-- pdf-page: 3 -->
902

EMANUEL KNILL AND RAYMOND LAFLAMME

55

(cid:40)

a

†A a

A a

(cid:53)I.

(cid:126)5(cid:33)

advance the state that will be used. We therefore use the
minimum ﬁdelity (cid:126)that is, the worst-case ﬁdelity(cid:33)

The A a are linear operators of the Hilbert space of the system
and describe the effect of the environment. The A a are called
interaction operators. Any family of operators A a which sat-
isﬁes Eq. (cid:126)5(cid:33) deﬁnes a superoperator. Note that the choice of
interaction operators is not unique;
they depend on the
choice of the basis (cid:117)(cid:109)
(cid:38) of the environment. Two sets of
a
interaction operators which differ only by this choice are
physically equivalent.

i

If there is no prior knowledge of the interaction operators
which corrupt an encoded state, it is not possible to recover
(cid:117)(cid:67)
(cid:38) consistently. However, in many physical systems the A a
are of a restricted form. For example, a reasonable approxi-
mation for systems of qubits is that the interaction with the
environment is independent for each qubit. In this case the
interaction operators are tensor products of one-qubit inter-
action operators. For small error rates, it might also be that
one of the one-qubit interaction operators, say A 0, is near the
identity. One can then deﬁne the number of errors of an
interaction by counting the number of operators in the tensor
product which are not A 0. If there is a sufﬁciently small
number of errors, it may be possible to retrieve the original
state just as for classical error correction.

Necessary and sufﬁcient conditions for recovery of the

state (cid:117)(cid:67)
i

(cid:38) are (cid:126)see Sec. III(cid:33)

(cid:94)0 L

(cid:117)A a

†A b

(cid:117)1 L(cid:38)(cid:53)0,

(cid:94)0 L

(cid:117)A a

†A b

(cid:117)0 L(cid:38)(cid:53)(cid:94)1 L

(cid:117)A a

†A b

(cid:117)1 L(cid:38).

(cid:126)6(cid:33)

(cid:126)7(cid:33)

The ﬁrst condition states that the logical zero and one must
go to orthogonal states under any error. The second one im-
plies that the length and inner products of the projections of
the corrupted logical zero and one should be the same.

A sufﬁcient but not necessary condition is that Eq. (cid:126)7(cid:33) is
zero if A a and A b are different. This implies that each error
maps the initial state to orthogonal subspaces. Obviously this
permits retrieval of the original state by projecting on these
subspaces. The more general Eq. (cid:126)7(cid:33) leaves room for two
different errors to be mapped on the same two-dimensional
subspace. This possibility is allowed by the superposition
principle of quantum mechanics but cannot occur in classical
error correction.

For realistic quantum computers only a subset of possible
errors can be corrected. An appropriate measure of the qual-
ity of a recovered code is the ﬁdelity (cid:64)22(cid:35). Fidelity is the
f of a system (cid:114) and the
overlap between the ﬁnal state (cid:114)
original state (cid:117)(cid:67)
(cid:38). If the combined superoperator consisting
of an interaction with the environment followed by a recov-
ery operation is given by A(cid:53)(cid:36)A 0, . . . (cid:37), then the ﬁdelity is

i

F(cid:126)(cid:117)(cid:67)

i(cid:38),A)(cid:53)(cid:94)(cid:67)

(cid:117)(cid:114)
f

i

(cid:117)(cid:67)

i(cid:38)(cid:53)(cid:40)

a

(cid:94)(cid:67)

(cid:117)A a

i

(cid:117)(cid:67)

i(cid:38)(cid:94)(cid:67)

†(cid:117)(cid:67)

(cid:117)A a

i

i(cid:38).

(cid:126)8(cid:33)

F min

(cid:53)min
(cid:117)(cid:67)(cid:38)

(cid:94)(cid:67)(cid:117)(cid:114)
f

(cid:117)(cid:67)(cid:38).

(cid:126)9(cid:33)

The best quantum code maximizes F min . Hereafter we will
drop the subscript min to denote the ﬁdelity of a code.

We now turn to a simple but important example to illus-
trate some of the points mentioned above. We investigate
decoherence (cid:64)6(cid:35), i.e., the randomization of the phase of the
(cid:38). The effect of decoherence is to decrease the
initial state (cid:117)(cid:67)
size of the diagonal element of the density matrix in a basis
determined by the interaction Hamiltonian with the environ-
ment. For one qubit, decoherence takes the form

i

i(cid:38)(cid:53)(cid:97)(cid:117)0(cid:38)(cid:49)(cid:98)(cid:117)1(cid:38)!(cid:114)(cid:83) (cid:97)(cid:97)*

(cid:117)(cid:67)

(cid:97)(cid:98)*e (cid:50)(cid:103)

(cid:68) ,

(cid:97)*(cid:98)e (cid:50)(cid:103) (cid:98)(cid:98)*

(cid:126)10(cid:33)

where e (cid:50)(cid:103) (cid:126)(cid:103)(cid:62)0(cid:33) parametrizes the amount of decoherence.
Decoherence can be understood in terms of the following
interaction with the environment:

(cid:117)e(cid:38)(cid:117)0(cid:38)!(cid:117)e 0(cid:38)(cid:117)0(cid:38),

with (cid:94)e 0
and (cid:117)(cid:109)
tion operators

(cid:126)11(cid:33)

(cid:117)e(cid:38)(cid:117)1(cid:38)!(cid:117)e 1(cid:38)(cid:117)1(cid:38),
(cid:117)e 1(cid:38)(cid:53)e (cid:50)(cid:103). Using the environment basis (cid:117)(cid:109)
(cid:38)(cid:53)(cid:117)e 0
(cid:38)
0
1(cid:38)(cid:53)((cid:117)e 1(cid:38)(cid:50)e (cid:50)(cid:103)(cid:117)e 0(cid:38))/(cid:65)1(cid:50)e (cid:50)2(cid:103) we obtain the interac-
0 (cid:65)1(cid:50)e (cid:50)2(cid:103)(cid:68) .
(cid:53)(cid:83) 0

e (cid:50)(cid:103)(cid:68) ; A 1

(cid:53)(cid:83) 1

(cid:126)12(cid:33)

A 0

0

0

0

For a single qubit which is corrupted by decoherence the

minimum ﬁdelity can be seen to be given by

F(cid:53)

1(cid:49)e (cid:50)(cid:103)
2

(cid:59)1(cid:50)

(cid:103)

2

(cid:49)••• ,

(cid:126)13(cid:33)

where the last approximation is valid for small (cid:103).

In what follows we assume that the different qubits have
independent environments (cid:126)a physically reasonable approxi-
mation(cid:33) so that the interaction operators are tensor products
of the ones given in Eq. (cid:126)12(cid:33).

A one-qubit code to correct this type of error by using
three qubits has been devised in Refs. (cid:64)11,12(cid:35). To understand
how it works, it is better to change the basis state of the
environment to (cid:117)(cid:109)(cid:49)(cid:38)(cid:53)((cid:117)e 0(cid:38)(cid:49)(cid:117)e 1(cid:38))/(cid:65)2(1(cid:49)e (cid:50)(cid:103)) and (cid:117)(cid:109)(cid:50)(cid:38)
(cid:53)((cid:117)e 0(cid:38)(cid:50)(cid:117)e 1(cid:38))/(cid:65)2(1(cid:50)e (cid:50)(cid:103)). This gives the one-qubit inter-
action operators
(cid:68) ; A (cid:50)(cid:53)a (cid:50)(cid:83) 1

A (cid:49)(cid:53)a (cid:49)(cid:83) 1

(cid:68) .

(cid:126)14(cid:33)

0

0
0 (cid:50)1

0

1

where a (cid:49)(cid:53)(cid:65)(1(cid:49)e (cid:50)(cid:103))/2 and a (cid:50)(cid:53)(cid:65)(1(cid:50)e (cid:50)(cid:103))/2. In this ba-
sis, the effect of the environment is either to leave the system
alone or ﬂip the sign if the qubit is in the state (cid:117)1(cid:38). The
encoding has the form

It gives the probability that the ﬁnal state would pass a test
checking whether it agrees with the initial state. As we are
thinking of encoding arbitrary states, we do not know in

(cid:117)0 L(cid:38)(cid:53)(cid:126)(cid:117)0(cid:38)(cid:49)(cid:117)1(cid:38))(cid:126)(cid:117)0(cid:38)(cid:49)(cid:117)1(cid:38))(cid:126)(cid:117)0(cid:38)(cid:49)(cid:117)1(cid:38)),

(cid:117)1 L(cid:38)(cid:53)(cid:126)(cid:117)0(cid:38)(cid:50)(cid:117)1(cid:38))(cid:126)(cid:117)0(cid:38)(cid:50)(cid:117)1(cid:38))(cid:126)(cid:117)0(cid:38)(cid:50)(cid:117)1(cid:38)).

(cid:126)15(cid:33)



<!-- pdf-page: 4 -->
55

THEORY OF QUANTUM ERROR-CORRECTING CODES

903

This code is such that if one qubit is corrupted by the envi-
ronment, then it is possible to detect it by using a majority
rule.

Assuming at most one incorrect qubit, the interaction with
the environment maps the initial state to one of the following
possibilities:

A (cid:49)(cid:117)0 L(cid:38)(cid:53)a (cid:49)

3/2(cid:126)(cid:117)0(cid:38)(cid:49)(cid:117)1(cid:38))(cid:126)(cid:117)0(cid:38)(cid:49)(cid:117)1(cid:38))(cid:126)(cid:117)0(cid:38)(cid:49)(cid:117)1(cid:38)),

1 (cid:117)0 L(cid:38)(cid:53)a (cid:49)
A (cid:50)

2 a (cid:50)

1/2(cid:126)(cid:117)0(cid:38)(cid:50)(cid:117)1(cid:38))(cid:126)(cid:117)0(cid:38)(cid:49)(cid:117)1(cid:38))(cid:126)(cid:117)0(cid:38)(cid:49)(cid:117)1(cid:38)),

2 (cid:117)0 L(cid:38)(cid:53)a (cid:49)
A (cid:50)

2 a (cid:50)

1/2(cid:126)(cid:117)0(cid:38)(cid:49)(cid:117)1(cid:38))(cid:126)(cid:117)0(cid:38)(cid:50)(cid:117)1(cid:38))(cid:126)(cid:117)0(cid:38)(cid:49)(cid:117)1(cid:38)),

3 (cid:117)0 L(cid:38)(cid:53)a (cid:49)
A (cid:50)

2 a (cid:50)

1/2(cid:126)(cid:117)0(cid:38)(cid:49)(cid:117)1(cid:38))(cid:126)(cid:117)0(cid:38)(cid:49)(cid:117)1(cid:38))(cid:126)(cid:117)0(cid:38)(cid:50)(cid:117)1(cid:38)),

(cid:126)16(cid:33)

where the superscripts on the operator A (cid:50) indicate which
(cid:38). The
qubit is being affected. A similar result applies to (cid:117)1L
recovery operator is the superoperator determined by the in-
teractions

R (cid:49)(cid:53)(cid:126)(cid:117)0 L(cid:38)(cid:94)0 L

(cid:117)(cid:49)(cid:117)1 L(cid:38)(cid:94)1 L

(cid:117)(cid:33),

1 (cid:53)(cid:126)(cid:117)0 L(cid:38)(cid:94)0 L
R (cid:50)

(cid:117)(cid:49)(cid:117)1 L(cid:38)(cid:94)1 L

(cid:117)(cid:33)(cid:115)
1,
z

2 (cid:53)(cid:126)(cid:117)0 L(cid:38)(cid:94)0 L
R (cid:50)

(cid:117)(cid:49)(cid:117)1 L(cid:38)(cid:94)1 L

(cid:117)(cid:33)(cid:115)
2,
z

3 (cid:53)(cid:126)(cid:117)0 L(cid:38)(cid:94)0 L
R (cid:50)

(cid:117)(cid:49)(cid:117)1 L(cid:38)(cid:94)1 L

(cid:117)(cid:33)(cid:115)
3,
z

(cid:126)17(cid:33)

where (cid:115)
r is the z Pauli matrix for the rth qubit. In practice
z
the recovery operator is implemented by ﬁrst performing a
measurement to determine which error has occurred. This
can be achieved by using a series of controlled-NOT gates
and measurements (cid:126)with the possible involvement of ancilla
qubits(cid:33) (cid:64)12(cid:35). The measurements establish the relative signs in
Eq. (cid:126)16(cid:33). Note that these relative signs are the same for the
logical zero and one after the same operator has acted and
therefore the measurements collapse the system to two-
dimensional subspaces. Once the measurements reveal which
subspace has actually occurred, it is straightforward to re-
cover the initial state with an appropriate unitary transforma-
tion.

It is important to realize that this code corrects perfectly
only if at most one error occurs. In general, however, deco-
herence can induce more than one error (cid:64)as can be deduced
from the fact that the A a in Eq. (cid:126)16(cid:33) do not form a superop-
erator(cid:35). As long as the decoherence is small (cid:126)i.e., (cid:103)is small(cid:33),
the probability of having two or more errors will be much
smaller than that of having one error. The minimum ﬁdelity
can be bounded below by

III. QUANTUM ERROR-CORRECTING CODES

A. Fundamentals of quantum error-correcting codes

let us deﬁne

It is now time to give a formal treatment of quantum
to preserve a 2k-dimensional subspace
codes. We want
against some known errors. This is accomplished by map-
ping the states into a larger, 2n-dimensional Hilbert space.
First,
a
an (n,k)
2k-dimensional subspace of an 2n-dimensional Hilbert space.
The latter is called the coding space and denoted by H. The
symbol C is used for the code. An encoding operator for C is
a unitary operator E from a k-dimensional Hilbert space Q
onto C. A decoding operator is a right inverse of an encoding
operator.

quantum code

as

The encoding operator can be implemented as a unitary
operator on Q (cid:94) k (cid:94) Q (cid:94) n(cid:50)k (cid:94) Q (cid:94) a, where the last factor has a
ancillary qubits whose state before and after the operation is
intended to be (cid:117)0(cid:38). The ancillas can be used as scratch pad
memory during the process of measurement needed to re-
cover C. In this case, the space Q to be encoded is a ‘‘stan-
dard’’ subspace of the coding space, and the encoding opera-
tor maps it to the intended code. Note that there are many
encoding operators which have the same effect on Q. This is
because the encoding deﬁnes only a part of the unitary trans-
formation needed. Which choice is actually used depends on
efﬁciency (cid:126)e.g., the number of gates in a physical situation(cid:33)
as well as the desired error-correcting properties.

For the purpose of discussing error-correcting properties
of codes, instead of focusing on encoding and decoding op-
erators, we introduce the recovery superoperator. A recovery
(cid:126)super(cid:33)operator R is a superoperator on the coding space. A
recovery operator is used to restore a state to the code after it
has been affected by an interaction with the environment.
Note that except for their intended use, recovery and inter-
action operators are the same type of object.

Use of a recovery operator instead of an explicit unitary
operator allows us to ignore many of the details of imple-
menting a code which are not relevant to its error-correcting
properties. It is general enough to represent potentially unin-
tended or unavoidable side effects of the more traditional
decode-encode operations. In practice, a recovery operator
may be implemented by a combination of unitary operations
and classical measurements or by unitary operations alone.
A quantum error-correcting code is a pair (cid:126)C,R(cid:33) consist-
ing of a quantum code and a recovery operator. The correct-
ing properties of an error-correcting code depend on the in-
teraction with the environment. Let A be a family of linear
operators as described in Eq. (cid:126)3(cid:33). The ﬁdelity of the code is
determined by the ﬁdelity of the composition RA restricted
to C. The ﬁdelity of the error-correcting code is thus deﬁned
as

F(cid:126)C,RA(cid:33)(cid:53) min
(cid:117)(cid:67)(cid:37)(cid:80)C

F(cid:126)(cid:117)(cid:67)(cid:38),RA)(cid:53) min
(cid:117)(cid:67)(cid:38)(cid:80)C

(cid:40)

r,a

(cid:122)(cid:94)(cid:67)(cid:117)R rA a

(cid:117)(cid:67)(cid:38)(cid:122)2,

F(cid:53)1(cid:50)(cid:126)a (cid:50)

3 (cid:49)3a (cid:50)

2 a (cid:49)(cid:33)(cid:39)1(cid:50) 3

4

(cid:103)2(cid:49)••• .

(cid:126)18(cid:33)

This scheme is thus an improvement over the single qubit
evolution for a small enough (cid:103). Using a 2n(cid:49)1 bit generali-
zation of the code in Eq. (cid:126)15(cid:33), it is possible to have ﬁdelity
be given by 1(cid:50)O((cid:103)n(cid:49)1) for small (cid:103), but with a potentially
large hidden constant.

where the R r are the interaction operators for the superop-
erator R. It is useful to consider families of linear operators
which do not necessarily satisfy the superoperator constraint
Eq. (cid:126)5(cid:33). In that case the ﬁdelity as deﬁned above is not cor-
rectly normalized and instead we consider the error of the
code. The error of the code is deﬁned as



<!-- pdf-page: 5 -->
904

EMANUEL KNILL AND RAYMOND LAFLAMME

55

of

the

consequences

B. Characterizations of A-correcting codes
So far we have deﬁned A-correcting codes both in terms
of the code and the recovery operator. One of the most im-
portant
of
A-correcting codes below is to allow deﬁning A-correcting
codes without reference to the recovery operator. Let (cid:117)i L(cid:38)
denote the elements of an orthonormal basis of the code C.
The ﬁrst characterization has proved the most useful so far
for ﬁnding good codes by systematic searches such as that in
(cid:64)15(cid:35) or by exploiting linear techniques from the classical
theory of error-correcting codes (cid:64)12,13(cid:35).

characterizations

Theorem III.2. The code C can be extended to an
A-correcting code iff for all basis elements (cid:117)i L(cid:38), (cid:117) j L(cid:38) (i(cid:222) j)
and operators A a , A b in A

and

(cid:94)i L

(cid:117)A a

†A b

(cid:117)i L(cid:38)(cid:53)(cid:94) j L

(cid:117)A a

†A b

(cid:117) j L(cid:38)

(cid:94)i L

(cid:117)A a

†A b

(cid:117) j L(cid:38)(cid:53)0.

(cid:126)19(cid:33)

(cid:126)20(cid:33)

These conditions are more general than the ones given in
(cid:64)23(cid:35), which are sufﬁcient but not necessary. Since they are
independent of a recovery operator, we can deﬁne an
A-correcting code as one which satisﬁes Eq. (cid:126)19(cid:33) and Eq.
(cid:126)20(cid:33) for any one (cid:126)and therefore every(cid:33) basis of the code.

Proof. Assume that (cid:126)C, R(cid:33) is an A-correcting code. We

compute (cid:94)i L

(cid:117)A a

†A b

(cid:117) j L(cid:38) explicitly.

(cid:94)i L

(cid:117)A a

†A b

(cid:117) j L(cid:38)(cid:53)(cid:94)i L

(cid:117)A a

†IA b

(cid:117) j L(cid:38)(cid:53)(cid:75) i L(cid:85)A a
†(cid:40)
(cid:117) j L(cid:38)(cid:53)(cid:40)

†R rA b

r

†R rA b(cid:85) j L(cid:76)

R r

(cid:94)i L

(cid:117)(cid:108)¯

ar

(cid:108)

(cid:117) j L(cid:38)

br

r

(cid:53)(cid:40)

r

(cid:94)i L

(cid:117)A a

†R r

(cid:53)(cid:97)

ab

(cid:100)

i j ,

where we have used the superoperator properties of R and
Theorem III.1. The forward direction of the theorem now
follows by inspection.

Let us now show how to construct a recovery operator
given that Eq. (cid:126)19(cid:33) and Eq. (cid:126)20(cid:33) hold. Call V i the subspace
(cid:117)i L(cid:38) (cid:126)for all a(cid:33). By Eq. (cid:126)20(cid:33), the V i are or-
spanned by A a
thogonal subspaces. Let (cid:117)(cid:110)
i (cid:38) be an orthonormal basis for V i.
r
We shall shortly impose additional conditions on the (cid:117)(cid:110)
i (cid:38).
r
the (cid:117)(cid:110)
i (cid:38) are mutually orthogonal.
For now, observe that
r
Hence there exist unitary V r which return (cid:117)(cid:110)
i (cid:38) to the corre-
r
sponding state (cid:117)i L(cid:38):

V r

(cid:117)(cid:110)
r

i (cid:38)(cid:53)(cid:117)i L(cid:38).

(cid:126)21(cid:33)

The recovery operator is given by the interaction operators

R(cid:53)(cid:36)O,R 1 ,...,R r ,...(cid:37),

(cid:126)22(cid:33)

where O is the projection onto the orthogonal complement of
V i, i.e., the part of the Hilbert space which is not reached
(cid:37)
by acting on the code with the A a , and

i

R r

(cid:53)V r(cid:40)

i

i (cid:38)(cid:94)(cid:110)
(cid:117)(cid:110)
i (cid:117).
r
r

(cid:126)23(cid:33)

FIG. 1. Geometric relation between ﬁdelity and error. The ﬁdel-
ity is the sum of the projections (cid:126)for each interaction operator(cid:33)
along the state. The error gives the ‘‘distance’’ from the original
state for each interaction operator.

E(cid:126)C,RA(cid:33)(cid:53) max
(cid:117)(cid:67)(cid:38)(cid:80)C

(cid:40)

r,a

(cid:122)(cid:126)R rA a

(cid:50)(cid:94)(cid:67)(cid:117)R rA a

(cid:117)(cid:67)(cid:38) (cid:33)(cid:117)(cid:67)(cid:38)(cid:122)2.

Figure 1 gives a geometric picture of the notion of ﬁdelity
and error of a code. The error of the code makes sense for
arbitrary families A. For superoperators,
is given by
1(cid:50)F(cid:126)C,RA(cid:33), which is the worst-case probability of not ob-
serving the desired state if we were to attempt to measure it
directly.

it

a

We ﬁrst focus on the ideal case where the code corrects
all errors, i.e., when the initial state is recovered perfectly for
all operators in A. The case of imperfect recovery will be
discussed later. The pair (cid:126)C,R(cid:33) is an A-correcting code if
E(cid:126)C,RA(cid:33)(cid:53)0. Note that this is equivalent to saying that for
(cid:33)(cid:53)0. Thus we can speak of A-correcting
each A a , E(cid:126)C,RA
codes even if A is not ﬁnite. In the next subsection we use
characterizations of A-correcting codes to slightly modify
this deﬁnition by omitting explicit mention of the recovery
operator.

Before we characterize A-correcting codes, let us turn the
problem around and ask what the family A(cid:126)C,R(cid:33) of operators
A for which (cid:126)C,R(cid:33) is A-correcting looks like. The next result
gives an answer.

Theorem III.1. The operator A a is in A(cid:126)C,R(cid:33) iff when
(cid:80)R. The family

restricted to C, R rA a
A(cid:126)C,R(cid:33) is linearly closed and (cid:126)C,R(cid:33) is A(cid:126)C,R(cid:33) correcting.
Proof. To be A a correcting requires that for (cid:117)(cid:67)(cid:38)(cid:80)C,

raI for each R r

(cid:53)(cid:108)

(cid:122)(cid:132)R rA a

(cid:50)(cid:126)(cid:94)(cid:67)(cid:117)R rA a

(cid:117)(cid:67)(cid:38) (cid:33)(cid:133)(cid:117)(cid:67)(cid:38)(cid:122)(cid:53)0.

(cid:126)(cid:117)(cid:67)(cid:38)(cid:33)(cid:117)(cid:67)(cid:38). By linearity of
(cid:126)(cid:117)(cid:67)(cid:38)(cid:33) cannot depend on (cid:117)(cid:67)(cid:38). The rest of the theo-

(cid:117)(cid:67)(cid:38)(cid:53)(cid:108)

ra

This implies that R rA a
R rA a , (cid:108)
ra
rem is immediate. QED.



<!-- pdf-page: 6 -->
55

THEORY OF QUANTUM ERROR-CORRECTING CODES

(cid:117)(cid:110)

That R is a superoperator follows from the observation that
it is a sum of orthogonal projections followed by unitary
operators where the projections span the Hilbert space.

0(cid:38)(cid:53)(cid:117)(cid:110)
r

(cid:117)0 L(cid:38)(cid:53)A a

To show that R recovers the state, we need unitary op-
i (cid:38)
such that U i
and for all A a ,
erators U i
r
(cid:117)i L(cid:38). The existence of unitary operators satis-
U iA a
fying the second condition follows from Eq. (cid:126)19(cid:33), according
(cid:117)0 L(cid:38)
to which the inner-product relationships between the A a
(cid:117)i L(cid:38) are identical (cid:64)24(cid:35). Given such U i , (cid:117)(cid:110)
i (cid:38) can be
and the A a
r
made to satisfy the remaining condition by choosing the ba-
0(cid:38) of V 0 and deﬁning (cid:117)(cid:110)
sis (cid:117)(cid:110)
r

r
We show that R does indeed recover the state, i.e., for
(cid:117)(cid:67)(cid:38) is proportional to (cid:67). We can write

i (cid:38)(cid:53)U i

(cid:67)(cid:80)C, R rA a

0(cid:38).
r

(cid:117)(cid:110)

A a

(cid:117)(cid:67)(cid:38)(cid:91)A a(cid:40)

i

(cid:97)
i

(cid:117)i L(cid:38)(cid:53)(cid:40)

i

(cid:97)

iA a

(cid:117)i L(cid:38)(cid:53)(cid:40)

i

(cid:97)

iU iA a

(cid:117)0 L(cid:38)

(cid:91)(cid:40)

i,r

(cid:97)

iU i

0 (cid:117)(cid:110)
(cid:98)
r
ar

0(cid:38)(cid:53)(cid:40)

i,r

(cid:97)
i

i (cid:38),
0 (cid:117)(cid:110)
(cid:98)
r
ar

(cid:126)24(cid:33)

where the identities deﬁne (cid:97)
i and (cid:98)
0 by expansion in terms
ar
of the corresponding basis elements. The introduction of the
operators U i is what allows us to obtain the expansion in the
last line where the (cid:98)’s show no dependence on i. We can
now compute R rA a

(cid:117)(cid:67)(cid:38) as

R rA a

(cid:117)(cid:67)(cid:38)(cid:53)(cid:40)

i

V r

i (cid:38)(cid:75) (cid:110)

i(cid:85)(cid:40)

r

(cid:117)(cid:110)
r

j,s

0 (cid:85)(cid:110)

j(cid:76) (cid:53)(cid:40)

s

(cid:97)
j

(cid:98)
as

i

(cid:53)(cid:40)

i

0 (cid:97)
(cid:98)
i
ar

(cid:117)i L(cid:38)(cid:53)(cid:98)

0 (cid:117)(cid:67)(cid:38).
ar

This implies that R rA a is a multiple of the identity operation
(cid:117) j L(cid:38), the fact that R is a
on C. Since O is null on all A a
recovery operator for A follows. QED.

An interesting observation about Eq. (cid:126)19(cid:33) is that it does
not require that the logical states have zero scalar products
when two different interactions are applied, but merely that
the scalar products are the same. For two-dimensional codes,
(cid:117)0 L(cid:38) and
this means that parts of the subspaces spanned by A a
(cid:117)1 L(cid:38) to which the states are mapped may overlap. If we
A a
identify each A a with a distinct error, then this possibility
allows the correction of more than one error per two-
dimensional subspace. This is a novel feature of quantum
error-correcting codes which does not exist in their classical
counterparts. The fact that nontrivial overlap is possible is
demonstrated by the following example.

Let us consider the code (cid:36)(cid:117)0L

(cid:38)(cid:53)(cid:117)00(cid:38), (cid:117)1L

(cid:38)(cid:53)(cid:117)11(cid:38)(cid:37) subject to

the interaction operators

A 0

1

0

0

0

0

(cid:53)(cid:83) (cid:65)1(cid:50)2q
(cid:53)(cid:83) (cid:65)q/2 0

0
0
(cid:65)q/2 0
0
0

A 1

0

0

(cid:68) ,

0

0

0

0

0

1
0 (cid:65)1(cid:50)2q

(cid:68) ,

0
0
0 (cid:65)q/2
0
0
0 (cid:65)q/2

(cid:126)26(cid:33)

(cid:53)(cid:83) (cid:65)q/2

0
(cid:50)(cid:65)q/2
0

A 2

905

(cid:68) ,

0

0

0

0

0

0

0
(cid:65)q/2
0
0
0 (cid:50)(cid:65)q/2

for some ﬁxed 0(cid:44)q(cid:44)1. It is easy to check that these opera-
tors form a superoperator. They are linearly independent and
therefore cannot be reduced to a smaller, equivalent interac-
tion. The A i map the logical states as follows:

(cid:117)0 L(cid:38)!(cid:65)1(cid:50)2q(cid:117)00(cid:38), (cid:65)q/2(cid:126)(cid:117)00(cid:38)(cid:49)(cid:117)10(cid:38)),
(cid:65)q/2(cid:126)(cid:117)00(cid:38)(cid:50)(cid:117)10(cid:38)),
(cid:117)1 L(cid:38)!(cid:65)1(cid:50)2q(cid:117)11(cid:38), (cid:65)q/2(cid:126)(cid:117)01(cid:38)(cid:49)(cid:117)11(cid:38)),
(cid:65)q/2(cid:126)(cid:117)01(cid:38)(cid:50)(cid:117)11(cid:38)).

(cid:126)27(cid:33)

Naively, one might expect that the states on the right hand
sides are linearly independent, but in fact, one of them is
linearly dependent on the other two in each case. We there-
fore need only two recovery operators to retrieve the initial
state. They are given by

We return to the problem of characterizing quantum error-
correcting codes. If A is a superoperator, then a simple char-
acterization of A-correcting codes is in terms of left invert-
ible superoperators.

Theorem III.3. Let A be a superoperator. C is an
A-correcting code iff the restriction of A to C has a left
superoperator inverse.

Proof. By Theorem III.1, C is an A-correcting code if and
only if there exists a superoperator R such that on C,
raI for all r and a. This means that RA is a super-
R rA a
operator equivalent to the identity (cid:126)by a change of basis on
the environment(cid:33). QED.

Interestingly, to check that an operator B(cid:53)RA has error 0
on any state, it sufﬁces to apply I (cid:94)B to a completely en-
tangled state. In other words, checking that the operator B
has zero error for all pure states of a system is equivalent to
checking only one state which is completely entangled with a
copy of the system.

(cid:53)(cid:108)

Theorem III.4. B has error 0 on C if and only if

I (cid:94)B(cid:40)

(cid:117)i L(cid:38)(cid:117)i L(cid:38)(cid:53)(cid:108) (cid:40)

i

(cid:117)i L(cid:38)(cid:117)i L

i

(cid:38).

The equality in the theorem is to be interpreted in terms of
state ensembles: Two state ensembles are equivalent iff they
induce the same density matrix.

Proof. Let B r be a member of B. Then I (cid:94) B r is a member

of I (cid:94)B. If B has error 0 on C, then

I (cid:94) B r(cid:40)

i

(cid:117)i L(cid:38)(cid:117)i L(cid:38)(cid:53)(cid:40)

i

(cid:117)i L(cid:38)B r

(cid:117)i L(cid:38)(cid:53)(cid:40)

i

(cid:117)i L(cid:38)(cid:108)

(cid:117)i L(cid:38)

r

(cid:53)(cid:108)

r(cid:40)

i

(cid:117)i L(cid:38)(cid:117)i L(cid:38).

(cid:97)
i

(cid:98)
0 V r
ar

i (cid:38)
(cid:117)(cid:110)
r

R 0

(cid:53)(cid:117)00(cid:38)(cid:94)00(cid:117)(cid:49)(cid:117)11(cid:38)(cid:94)11(cid:117); R 1

(cid:53)(cid:117)00(cid:38)(cid:94)10(cid:117)(cid:49)(cid:117)11(cid:38)(cid:94)01(cid:117).

(cid:126)28(cid:33)

(cid:126)25(cid:33)

Whether there are any such examples of practical signiﬁ-
cance is under investigation.



<!-- pdf-page: 7 -->
906

EMANUEL KNILL AND RAYMOND LAFLAMME

55

This implies that the ensemble I (cid:94)B(cid:40)
to a scalar multiple of (cid:40)
i

(cid:117)i L(cid:38)(cid:117)i L(cid:38).

(cid:117)i L(cid:38)(cid:117)i L(cid:38) is equivalent

i

Now suppose that the identity in the theorem holds. The
fact that the left hand side is equivalent (cid:126)as a set of states(cid:33) to
the right hand side implies that for each r,

I (cid:94) B r(cid:40)

ı

(cid:117)i L(cid:38)(cid:117)i L(cid:38)(cid:53)(cid:108)

r(cid:40)

i

(cid:117)i L(cid:38)(cid:117)i L(cid:38).

r

the (cid:117)i L(cid:38)(cid:117)i L(cid:38) are independent,

that
(cid:117)i L(cid:38). The result follows. QED.

By applying the operator I (cid:94) B r to each summand and using
this gives
the fact
(cid:117)i L(cid:38)(cid:53)(cid:108)
B r
An interesting and concise method of describing a code
which hides the recovery operator without removing it en-
tirely involves expressing the coding space as a sum of two
terms, the ﬁrst of which is a tensor product of the code with
another space. As we will see, this perspective has several
interesting consequences. One of these consequences is the
explicit distinction between correctable versus detectable er-
rors.

Theorem III.5. C is an A-correcting code if and only if
there is an isomorphism (cid:115):H!C(cid:94)E(cid:37)D such that for all
(cid:117)(cid:67)(cid:38)(cid:53)(cid:115)(cid:132)(cid:117)(cid:67)(cid:38)(cid:94)(cid:117)E(a)(cid:38)(cid:133) for some vector
A a
(cid:117)E(a)(cid:38) depending on A a alone.

(cid:80)A and (cid:117)(cid:67)(cid:38)(cid:80)C, A a

The idea is to ensure that under each interaction operators
the effect of the environment is clearly separated from the
state to be preserved. This is essential for the logical state to
keep their coherence. (cid:117)(cid:67)(cid:38) is the wave function of a collective
degree of freedom which represents the logical state and the
state of the remaining degrees of freedom is given by (cid:117)E(a)(cid:38).
E takes up all the information from the environment and ﬁnal
state in E encodes the environment’s effect on the code. The
ﬁnal state E is called the error syndrome. D is the summand
of H, which is normally never reached by A, but which can
be used for error detection if so desired. A perfect quantum
code is one for which D is empty and the (cid:117)E(a)(cid:38) span E. Note
that in many cases of interest, a multiple of the identity map
In this case,
is
C(cid:53)(cid:115)(cid:132)C(cid:94)(cid:117)E(cid:126)0(cid:33)(cid:38)(cid:133).

in A (cid:126)given by A 0

for example(cid:33).

Proof. Let C be an A-correcting code in H. We use the
notation from the proof of Theorem III.2. Let D be the or-
i (cid:38).
thogonal complement of the subspace spanned by the (cid:117)(cid:110)
r
0(cid:38)(cid:37)r . The isomor-
Let E be the Hilbert space spanned by (cid:36)(cid:117)(cid:110)
phism between H and C(cid:94)E(cid:37)D is established by letting
i (cid:38) and deﬁning (cid:115) to be the identity map on
0(cid:38))(cid:53)(cid:117)(cid:110)
(cid:115)((cid:117)i L(cid:38)(cid:117)(cid:110)
r
r
(cid:117) j L(cid:38)(cid:80)C. Write
D.
(cid:80)A
A a
Let
j
0(cid:38). Applying the properties discussed in
(cid:117)0 L(cid:38)(cid:53) (cid:40)
0 (cid:117)(cid:110)
A a
r
ra
the proof of Theorem III.2 gives

(cid:117)(cid:67)(cid:38)(cid:53)(cid:40)

and

(cid:97)
j

(cid:98)

r

r

(cid:117)(cid:67)(cid:38)(cid:53)(cid:40)

A a

jr

(cid:97)
j

0 (cid:117)(cid:110)
(cid:98)
r
ar

(cid:53)(cid:115)(cid:83) (cid:117)(cid:67)(cid:38) (cid:94) (cid:40)

r

j(cid:38)(cid:53)(cid:115)(cid:83) (cid:40)
0(cid:38)(cid:68) .

0 (cid:117)(cid:110)
(cid:98)
r
ra

j

0(cid:38)(cid:68)

0 (cid:117)(cid:110)
(cid:98)
r
ar

(cid:97)
j

(cid:117) j L(cid:38) (cid:94) (cid:40)

r

Thus we can let (cid:117)E(a)(cid:38)(cid:53)(cid:40)
r
part of the theorem.

(cid:98)

0 (cid:117)(cid:110)
ar

0(cid:38) to prove the ‘‘only if’’
r

For the other direction we show how to construct a recov-
ery operator which restores the code after action of A. Let
(cid:117)(cid:110)
0(cid:38) be a basis of E and let R r be the projection onto
r
0(cid:38)(cid:33)
(cid:115)(cid:126)C(cid:94)(cid:117)(cid:110)
followed by a unitary operator which maps
r

r

(cid:115)((cid:117)i L(cid:38) (cid:94) (cid:117)(cid:110)
0(cid:38)) to (cid:117)i L(cid:38). Let O be the projection onto (cid:115)(cid:126)D(cid:33).
Then the conditions on the A a imply that R rA a is a scalar
multiple of the identity, which gives the desired result. QED.
Finally, we mention that for superoperators A, there is a
simple information theoretic characterization of A-correcting
codes due to Nielsen and Schumacher (cid:64)25(cid:35). Let (cid:117)e(cid:38)
(cid:53)(1/(cid:65)k) (cid:40)
from which we can deﬁne the density matrices:

(cid:117)i L(cid:38)(cid:117)i L(cid:38) be the perfectly entangled state of the code

i

(cid:114)¯(cid:53)

1
k

(cid:40)

ai

A a

(cid:117)i L(cid:38)(cid:94)i L

†
(cid:117)A a

and (cid:114)(cid:53)(cid:40)

a

I (cid:94) A a

(cid:117)e(cid:38)(cid:94)e(cid:117)A a

† (cid:94) I.

(cid:126)29(cid:33)

The entropy of a density matrix (cid:115) is denoted by S(cid:126)(cid:115)(cid:33).

Theorem III.6. Let A be a superoperator. Then C is an

A-correcting code if and only if S((cid:114)¯)(cid:50)S((cid:114))(cid:53)log2 k.

The quantity S((cid:114)¯)(cid:50)S((cid:114)) is introduced as a natural notion
of mutual information in (cid:64)25(cid:35). The proof of the theorem can
be found there.

IV. IMPLEMENTING RECOVERY OPERATORS

Let us begin by observing that the recovery operator con-
structed in Theorem III.2 consists only of projections fol-
lowed by unitary operators conditional on the result of the
projections. Implementing such an operator is conceptually
straightforward: First you perform a measurement corre-
sponding to the set of projections, then, depending on the
outcome of the measurement, you perform an appropriate
unitary operation. However, in quantum computation, it is
customary to assume that direct measurements can only be
performed in a standard basis of each system. This means
that a suitable unitary transformations must be applied ﬁrst in
order to rotate the measurement subspaces.

To discuss various methods for implementing the recov-
ery operator we need the notion of a unitary extension. Let
W(cid:53) (cid:40)
iV iP i , where the P i are orthogonal projections, and
(cid:53)0 for i(cid:222) j. Then a unitary extension of W is any
†V j
P j
unitary W(cid:56) which agrees with W on the range of the P i . The
conditions ensure that W(cid:56) exists.

†V iP i

P rm

Let R be described by the

rP r
(cid:94) (cid:117)0 M(cid:38) goes to P

interaction operators
(U 0P 0 ,...,U rm
), where the P r are projections onto the
r , and the U r are unitary. Let M be
orthogonal subspaces P
a separate (cid:126)ancillary(cid:33) system with standard basis (cid:117)r M(cid:38). Let V r
be a unitary operator on M with the property that
(cid:117)0 M(cid:38)(cid:53)(cid:117)r M(cid:38) (cid:126)i.e., V r is a unitary extension of (cid:117)r M(cid:38)(cid:94)0 M
(cid:117)).
V r
The operator V(cid:53) (cid:40)
(cid:94) V r is unitary and has the property
(cid:94) (cid:117)r M(cid:38). (cid:126)This is a generalization of
that P
r
r
the standard controlled-NOT operations in quantum comput-
ing.(cid:33) If M starts in the state (cid:117)0M
(cid:38), then we can perform R by
ﬁrst applying V, then measuring M in the standard basis,
and ﬁnally applying U r to the coding space if the outcome of
the measurement is (cid:117)r M(cid:38). This is in fact the implementation
of the recovery operator suggested in (cid:64)11,12(cid:35). If it is neces-
sary to represent the recovery operator by unitary operators
without measurement, then the measurement and the ﬁnal
rotation step can be replaced by application of the unitary
(cid:117). However, note that with this pro-
operator (cid:40)
cedure, the information about the environment’s interaction
with the coding space is transferred completely to M. The
only effective way in which M can be reused for subsequent

(cid:94) (cid:117)r M(cid:38)(cid:94)r M

rU r



<!-- pdf-page: 8 -->
55

THEORY OF QUANTUM ERROR-CORRECTING CODES

907

operations is to dissipate that information by a measurement.
Usually when using a code, there will be a time when it is
desirable to decode the state into a separate system C(cid:56) of the
same dimension as C with standard basis (cid:117)i(cid:38). The purpose of
decoding the state in this fashion may be to measure it, or to
perform unitary operations which cannot easily be applied in
the coding space directly, or as the ﬁrst step in a recovery
operation where the second step is to reencode the state.
Given an implementation of the recovery operator, one can
perform this decoding by following the recovery operator
with the application of a unitary extension of the operator
(cid:117) (cid:94) (cid:117)i(cid:38)(cid:94)0(cid:117) to H(cid:94)(cid:117)0(cid:38). This in effect swaps the state
(cid:40)
from C to C(cid:56) after recovery.

(cid:117)0 L(cid:38)(cid:94)i L

i

iQ ı

(cid:94) (cid:117)i(cid:38)(cid:94)0(cid:117)

to (cid:117)(cid:99)(cid:38)(cid:94)(cid:117)0(cid:38) in H(cid:94)C(cid:56). Then apply (cid:40)

Here is a potentially useful method for decoding without
use of ancillas. We use the notation from Theorem III.2. Let
Q i be the projection onto V i. First apply a unitary extension
†
of (cid:40)
iU i
(cid:94) (cid:117)i(cid:38)(cid:94)i(cid:117). Finally (cid:126)if desired(cid:33) measure H to put the coding
system into a known state. As an alternative to the last uni-
tary transformation, one can measure H in a special basis
and follow the measurement by a unitary operation on C(cid:56).
One choice for such a basis is given by an arbitrary extension
of the set

(cid:117)e ir(cid:38)(cid:53)(cid:40)

j

j(cid:38),
(cid:118)i j(cid:117)(cid:110)
r

j

where (cid:118) is a kth root of unity (cid:126)we have neglected normal-
ization factors(cid:33). If the outcome of the measurement is (cid:117)e ir(cid:38),
(cid:118)(cid:50)i j(cid:117) j(cid:38)(cid:94) j(cid:117) needs to be ap-
then the unitary transformation (cid:40)
plied to C(cid:56) to complete the decoding step. If a k(cid:51)k Had-
amard matrix (cid:64)19(cid:35) exists, one can choose the coefﬁcients of
i (cid:38) and of (cid:117)i(cid:38)(cid:94)i(cid:117) to be 1 or (cid:50)1.
(cid:117)(cid:110)
r
In many applications, C(cid:56) is in fact a subsystem of H, that
is, H(cid:53)C(cid:56)(cid:94)E(cid:56). In that case we can decode a state by using the
isomorphism of Theorem III.5. First identify E with a sub-
space of E(cid:56) and apply a unitary extension D of the operator
which takes (cid:115)((cid:117)i L(cid:38)(cid:117)a(cid:38)) to (cid:117)i(cid:38)(cid:117)a(cid:38). This can be followed by a
measurement of E to dissipate the error. Note that in the case
where the identity map is corrected, such that C(cid:53)(cid:115)(cid:126)C(cid:94)(cid:117)a 0
(cid:38)(cid:33),
we can apply D (cid:50)1 to (cid:117)(cid:99)(cid:38)(cid:117)a 0
(cid:38) to perform the encoding opera-
tion. Now the same circuit can be used for both encoding and
decoding. Recovery can be accomplished by applying D, a
(cid:38), and ﬁnally re-
measurement of E, a restoration of E to (cid:117)a 0
encoding using D (cid:50)1. The ﬁrst example of such a conﬁgura-
tion was given in (cid:64)15(cid:35).

We end this section by making a comment on codes such
as the ones suggested by Steane (cid:64)12(cid:35) and Calderbank and
Shor (cid:64)13(cid:35). These codes have the property that H can be
represented as in Theorem III.5, with the additional property
that for a basis (cid:117)e ı(cid:38) of E and unitary operators U i j ,

(cid:115)(cid:126)(cid:117)(cid:99)(cid:38)(cid:117)e i(cid:38))(cid:53)(cid:115)(cid:83) (cid:40)

A a

(cid:117)e j(cid:38)(cid:68)

U i j

(cid:117)(cid:99)(cid:38)(cid:97)
a j

j

independent of (cid:99). This implies that each subspace (cid:115)(cid:126)C(cid:94)(cid:117)e i(cid:38)(cid:33)
is an A-correcting code. This property is particularly useful
in iterated applications of the code, where recovery operators
and interactions alternate. Effectively, it sufﬁces to project
the state after the interaction onto the subspaces (cid:115)(cid:126)C(cid:94)(cid:117)e i(cid:38))
by using a recovery operator consisting of these projections.

The result of the projection is a correct state in an alternative
code, so it is not necessary to follow up with a unitary op-
erator. It is, however, necessary to keep track of the sequence
of outcomes of the projections, since the U i j change the re-
quired interpretation of the logical basis of C.

V. PROPERTIES OF CODES CORRECTING
INDEPENDENT INTERACTIONS

A. Independent interactions

It is difﬁcult to discover quantum error-correcting codes
for general types of interactions. In the classical theory of
error correction, it is often assumed that errors occur inde-
pendently for each symbol. This assumption seems physi-
cally reasonable in many situations. In cases where it is not
strictly true it can still lead to a systematic approach for
ﬁnding high-ﬁdelity error-correcting codes. We now discuss
the implications of a similar assumption for the quantum
theory. In this case, the set of symbols is replaced by a ﬁxed
system such as the qubit. The coding space is a tensor prod-
uct of independent systems. To say that the interaction op-
erator acts independently on each component system means
that it is a tensor product of single system interactions. We
shall focus on the case where each system is a qubit to sim-
plify the discussion. Generalizations to larger systems are
straightforward. Let H(cid:53)Q(cid:94) r(cid:53)Q
r . Given a one-
qubit superoperator A, we say that A(cid:94) r acts independently
on each qubit with

(cid:94)•••(cid:94)Q

1

A(cid:94) r(cid:53)(cid:36)A i1

(cid:94) A i2

(cid:94) •••(cid:37)i1 ,i2 ,... .

The assumption of independent interaction is reasonable
for the case of spontaneous emission where we can take A to
consist of

0 (cid:65)1(cid:50) p 2(cid:68) ,
(cid:53)(cid:83) 1

0

S 0

(cid:53)(cid:83) 0

0

S 1

(cid:68) .

p

0

For phase randomization (cid:126)decoherence(cid:33) independence is a
good approximation when the effective wavelength of the
environment is smaller than the interspacing of the physical
system used as qubits. For example, if the environment is
modeled by a bath at ﬁnite temperature, the condition is that
the De Broglie wavelength is smaller than the qubit’s inter-
spacing. The one-qubit phase randomization interactions
were given in Eq. (cid:126)12(cid:33).

As in classical error correction with ﬁxed error rates, it is
in general not possible to correct A(cid:94) r with error 0. And just
as in the classical case, it is useful to consider codes which
correct well the ‘‘important’’ members of A(cid:94) r, that is, those
which strongly affect only a few of the qubits. This leads to
the study of e-error-correcting quantum codes.

An operator A acting on H is said to induce (cid:126)at most(cid:33) e
errors if it is an r-fold tensor product of one-qubit operators
where all but e of them are the identity. An e-error-
correcting code is one which can recover from all interaction
operators inducing at most e errors.

To discuss e error correction in more detail, we need a
linear basis for the one-qubit interactions. One such basis
with the additional property that each operator is unitary is
given by



<!-- pdf-page: 9 -->
908

EMANUEL KNILL AND RAYMOND LAFLAMME

0

(cid:53)(cid:83) 1
(cid:53)(cid:83) 0

1

A 0

A 2

(cid:68) ; A 1
(cid:68) ; A 3

0

1

1

0

0
0 (cid:50)1

(cid:53)(cid:83) 1
(cid:53)(cid:83) 0 (cid:50)1

1

0

(cid:68) ;
(cid:68) .

(cid:126)30(cid:33)

(cid:117)0 L(cid:38)(cid:53)(cid:40)

i jkl

(cid:97)

i jkl

(cid:117)i jkl(cid:38),

(cid:117)1 L(cid:38)(cid:53)(cid:40)

i jkl

(cid:98)

i jkl

(cid:117)i jkl(cid:38),

55

(cid:126)32(cid:33)

These A a operators physically correspond to: (cid:126)0(cid:33) leaving the
system unchanged, (cid:126)1(cid:33) changing the sign of the bit if it is in
the (cid:117)1(cid:38) state, (cid:126)2(cid:33) ﬂipping the bit, (cid:126)3(cid:33) ﬂipping the bit and
changing its sign if it was in the (cid:117)1(cid:38) state.

Another useful basis for the one qubit

interactions is

given by

0

(cid:53)(cid:83) 1
(cid:53)(cid:83) 0

0

A˜

0

A˜

2

(cid:68) ; A˜
(cid:68) ; A˜

1

3

0

0

1

0

0

(cid:53)(cid:83) 0
(cid:53)(cid:83) 0

1

(cid:68) ;
(cid:68) .

0

1

0

0

and use the interaction operators described in Eq. (cid:126)31(cid:33). Let
us deﬁne the reduced density matrices

0 (cid:53)(cid:40)
(cid:114)
i(cid:56) j(cid:56)i j

kl

1 (cid:53)(cid:40)
(cid:114)
i(cid:56) j(cid:56)i j

kl

(cid:97)

* (cid:97)
i(cid:56) j(cid:56)kl

i jkl ,

(cid:98)

* (cid:98)
i(cid:56) j(cid:56)kl

i jkl .

(cid:126)33(cid:33)

Using those operators which induce an error on the last

two qubits in Eq. (cid:126)20(cid:33) we get

(cid:126)31(cid:33)

The operators A˜
2 and A˜
the qubit. A˜
lowed by a bit ﬂip.

0 and A˜

1 implement an ideal measurement on
3 implement an ideal measurement fol-

The basis in Eq. (cid:126)30(cid:33) is the one used in (cid:64)15(cid:35) to ﬁnd the

one-error-correcting ﬁve-qubit code.

B. Simple lower bound

One of the simplest lower bounds on the number of clas-
sical code words given that at least e errors are to be cor-
rected is the Hamming bound. It is obtained by counting the
number b e of words within e errors of each code word. The
product of b e and the number of code words cannot exceed
the size of the coding space.

For quantum codes, one can attempt a similar argument.
Assume that we have written the superoperator A in a mini-
mal form so that each A a is independent. In the special case
where Eq. (cid:126)19(cid:33) is solved by setting both sides to 0, it is clear
(cid:38) are independent. This im-
(cid:117)i L
that all states of the form A a
plies that the total dimension of the space has to be at least
2k(cid:117)A(cid:117). This argument fails because no such independence is
implied by Eq. (cid:126)19(cid:33) and Eq. (cid:126)20(cid:33). One can, however, use
Theorem III.5 to see that the total dimension has to exceed
2 ke, where e is the dimension of E. If a lower bound on
dim(A 0
then this is a lower
is known,
bound on e.

(cid:117)(cid:67)(cid:38),...,A am

(cid:117)(cid:67)(cid:38))

As an example, consider the question of whether there are
(cid:126)2r,2(cid:33) codes with r(cid:60)4 qubits such that any operator which
induces at most one error can be corrected. A natural basis
for this family of operators can be derived from the basis in
Eq.
operators. Solving
2(1(cid:49)3r)(cid:60)2 r suggests that r must be at least 5. See (cid:64)15(cid:35) for
an example of a code with r(cid:53)5. As was pointed out in the
previous paragraph, this argument is incomplete.

and consists of 1(cid:49)3r

(cid:126)30(cid:33)

(cid:40)

i j

(cid:40)

i j

(cid:40)

i j

i j00* (cid:98)
(cid:97)

i j00

(cid:53)0,

i j10* (cid:98)
(cid:97)

i j00

(cid:53)0,

(cid:65)

i j11* (cid:98)
(cid:97)

i j11

(cid:53)0,

(cid:126)34(cid:33)

from which we conclude that the density matrices are or-
thogonal, i.e.,

On the other hand, Eq. (cid:126)19(cid:33) implies that these two density
matrices are equal: Using those operators which induce an
error in the ﬁrst two qubits, we get

(cid:126)35(cid:33)

(cid:40)

i j

(cid:40)

i j

00i j* (cid:97)
(cid:97)

00i j

10i j* (cid:97)
(cid:97)

10i j

(cid:53)(cid:40)

i j

(cid:53)(cid:40)

i j

(cid:65)

00i j* (cid:98)
(cid:98)

00i j ,

10i j* (cid:98)
(cid:98)

10i j ,

We present here a different argument which proves that
r(cid:53)5 is the minimum for one-error-correcting codes. Assume
a code with r(cid:53)4 exists. We use the necessary and sufﬁcient
conditions given in Eqs. (cid:126)19(cid:33) and (cid:126)20(cid:33) and expand the logical
zero and one as

(cid:40)

i j

11i j* (cid:97)
(cid:97)

11i j

(cid:53)(cid:40)

i j

11i j* (cid:98)
(cid:98)

11i j ,

(cid:126)36(cid:33)

from which we deduce



<!-- pdf-page: 10 -->
55

THEORY OF QUANTUM ERROR-CORRECTING CODES

909

0 (cid:53)(cid:40)
(cid:114)
i ji(cid:56) j(cid:56)

kl

i jkl* (cid:97)
(cid:97)

i(cid:56) j(cid:56)kl

(cid:53)(cid:40)

kl

i jkl* (cid:98)
(cid:98)

i(cid:56) j(cid:56)kl

1
(cid:53)(cid:114)
i ji(cid:56) j(cid:56)

.

(cid:126)37(cid:33)

Equation (cid:126)35(cid:33) and Eq. (cid:126)37(cid:33) are inconsistent and imply that no
such code exists.

The argument presented above can be generalized to the

following theorem.

Theorem V.1. A(n,k) e-error-correcting quantum code

must satisfy n(cid:62)4e(cid:49)k.

The task of proving this theorem is much simpliﬁed by
characterizing e-error correction in terms of the reduced den-
sity matrices of the code words. Let the qubits of the coding
space be labeled by 1, . . . ,r. For U(cid:35)(cid:36)1,...,r(cid:37), let (cid:114)((cid:117)x(cid:38),U)
be the reduced density matrix of (cid:117)x(cid:38) on the qubits labeled by
elements of U. The complement of U is denoted by U¯ .

Theorem V.2. C is an e-error-correcting code if and only if
for all U(cid:35)(cid:36)1,...,r(cid:37) with (cid:117)U(cid:117)(cid:53)2e: (cid:126)i(cid:33) for all i, j, (cid:114)((cid:117)i L(cid:38),U)
(cid:53)(cid:114)((cid:117) j L(cid:38),U) and (cid:126)ii(cid:33) for i(cid:222) j, (cid:114)((cid:117)i L(cid:38),U¯ )(cid:114)((cid:117) j L(cid:38),U¯ )(cid:53)0.

The proofs of Theorems V.1 and V. 2 will be given else-
where using a straightforward generalization of the tech-
niques in the earlier proof of the bound on one error correc-
tion.

i

e

(cid:65)p i

Here (cid:114) and (cid:114)
e are the ﬁnal density matrix after interaction
(cid:38), respectively.
and recovery if the initial state is (cid:117)(cid:67)(cid:38) and (cid:117)(cid:67)
e(cid:38)
Write the entangled state in the Schmidt basis as (cid:117)(cid:67)
H(cid:38) (cid:126)the label C characterizes the system on
C(cid:38)(cid:117)(cid:99)
(cid:53) (cid:40)
(cid:117)(cid:99)
i
i
which we want to do error correction and the label H the
system with which it is entangled(cid:33). We assume that only the
system C is affected by an interaction with the environment
and subsequent recovery and that the system H has trivial
dynamics. In this case the interaction operators are tensor
products of the identity operator for the system H and the
ones given by the interactions for the system C. We can
therefore rewrite Eq. (cid:126)39(cid:33) as

F e

(cid:53)(cid:40)

i j,a

p ip j(cid:94)(cid:99)

C(cid:117)A a

i

C(cid:38)(cid:94)(cid:99)
(cid:117)(cid:99)
j
i

C(cid:117)A a

C(cid:38).
†(cid:117)(cid:99)
j

(cid:126)40(cid:33)

To obtain the bound we calculate the pure state ﬁdelity for

a superposition of the form (cid:65)p 1

C(cid:49)e i(cid:117)(cid:65)p 2
(cid:99)
1

C
(cid:99)
2

. Thus

(cid:60)(cid:126)(cid:65)p 1

C(cid:49)e i(cid:117)(cid:65)p 2
(cid:99)
1

C(cid:33)
(cid:99)
2

F p

(cid:53)(cid:40)

a

(cid:94)(cid:65)p 1

C(cid:49)e i(cid:117)(cid:65)p 2
(cid:99)
1

C(cid:117)A a
(cid:99)
2

(cid:117)(cid:65)p 1

C(cid:49)e i(cid:117)(cid:65)p 2
(cid:99)
1

C(cid:38)
(cid:99)
2

(cid:51)(cid:94)(cid:65)p 1

C(cid:49)e i(cid:117)(cid:65)p 2
(cid:99)
1

C(cid:117)A a
(cid:99)
2

†(cid:117)(cid:65)p 1

C(cid:49)e i(cid:117)(cid:65)p 2
(cid:99)
1

C(cid:38). (cid:126)41(cid:33)
(cid:99)
2

We can now average uniformly the last equation over all
values of (cid:117)to get

C. Relationship between the pure state
and entangled state ﬁdelity

F p

(cid:60)F e

(cid:49) p 1p 2(cid:126)(cid:94)(cid:99)

C(cid:117)A a

1

C(cid:38)(cid:94)(cid:99)
(cid:117)(cid:99)
2
2

C(cid:117)A a

C(cid:38)
†(cid:117)(cid:99)
1

We have studied the recovery of corrupted states using
error-correction codes. It is anticipated that the states to be
protected involve only a subset of the entangled qubits of the
computer or communication channel. This means that in dis-
cussions of ﬁdelity and error, the whole state, not just the
component being protected, must be considered. Naturally
we can compute the ﬁdelity of a code taking into account any
part of the state not directly involved in the interaction and
recovery. The worst-case ﬁdelity for such states is referred to
as the entangled state ﬁdelity to distinguish it from the pure
state ﬁdelity introduced earlier.

If the pure state ﬁdelity after recovery of the coded sub-
system is one, then the entangled state ﬁdelity is one also; it
does not matter if the state is pure or if it is entangled with
other systems. This observation is invalid if we have imper-
fect ﬁdelity.

Theorem V.3. If the pure state ﬁdelity is F p

(cid:53)1(cid:50)(cid:101), then
(cid:62)1(cid:50)3(cid:101)/2. There are ex-

the entangled state ﬁdelity is F e
amples where this bound is achieved.

Proof. We give the proof for the case where the system is

two-dimensional. We have

F p

(cid:53) min
(cid:117)(cid:99)(cid:38)(cid:80)C

(cid:94)(cid:67)(cid:117)(cid:114)(cid:117)(cid:67)(cid:38)(cid:53)1(cid:50)(cid:101),

(cid:126)38(cid:33)

and we would like to put a bound on the entangled state
ﬁdelity

F e

(cid:53) min
(cid:117)(cid:67)

e(cid:38)(cid:80)H(cid:94) C

(cid:94)(cid:67)

(cid:117)(cid:114)
e

e

(cid:117)(cid:67)

e(cid:38).

(cid:126)39(cid:33)

(cid:126)42(cid:33)

(cid:126)43(cid:33)

(cid:49)(cid:94)(cid:99)
2

C(cid:117)A a

C(cid:38)(cid:94)(cid:99)
(cid:117)(cid:99)
1
1

C(cid:117)A a

C(cid:38)).
†(cid:117)(cid:99)
2

Finally, Eq. (cid:126)5(cid:33) puts a bound on the last term in Eq. (cid:126)43(cid:33)
using the normalization of the interaction operator, i.e.,

(cid:40)

i,a

(cid:94)(cid:99)
i

C(cid:117)A a

C(cid:38)(cid:94)(cid:99)
(cid:117)(cid:99)
1
1

C(cid:117)A a

C(cid:38)(cid:60)1.
†(cid:117)(cid:99)
i

(cid:126)44(cid:33)

(cid:126)Note that the expression is a partial trace of a density ma-
trix. The trace is partial because the interactions may take the
original state into a larger space containing C.(cid:33) By expanding
the sum over i and noting that (cid:126)1(cid:33) the term with i(cid:53)1 is at
least 1(cid:50)(cid:101)by the deﬁnition of pure state ﬁdelity and (cid:126)2(cid:33) all
the terms are positive, we conclude that the terms with i(cid:222)1
are bounded by (cid:101). The largest achievable value for p 1p 2 is
1/4. This gives

(cid:62)1(cid:50)

F e

3(cid:101)
.
2

(cid:126)45(cid:33)

For the example of decoherence in Sec. II, it is possible to
(cid:53)F p . The following example shows however
show that F e
that the bound in Eq. (cid:126)45(cid:33) can be achieved. Consider the
interaction consisting of scalar multiples of the Pauli spin
matrices,

A(cid:53)(cid:72) 1

)

(cid:115)

x ,

1
)

(cid:115)

y ,

1
)

z(cid:74) .

(cid:115)



<!-- pdf-page: 11 -->
910

EMANUEL KNILL AND RAYMOND LAFLAMME

55

We show that for this example, F(cid:126)A(cid:33)(cid:53)1/3 and F e
(cid:126)A(cid:33)(cid:53)0.
Let (cid:117)u(cid:38)(cid:53)(cid:97)(cid:117)0(cid:38)(cid:49)e i(cid:117)(cid:98)(cid:117)1(cid:38) with (cid:97) and (cid:98) real, and (cid:97)2(cid:49)(cid:98)2(cid:53)1.
The ﬁdelity of A is obtained by maximizing the expression

1
3

(cid:126)(cid:122)(cid:94)u(cid:117)(cid:115)
x

(cid:117)u(cid:38)(cid:122)2(cid:49)(cid:122)(cid:94)u(cid:117)(cid:115)
y

(cid:117)u(cid:38)(cid:122)2(cid:49)(cid:122)(cid:94)u(cid:117)(cid:115)
z

(cid:117)u(cid:38)(cid:122)2(cid:33)

(cid:53) 1

3 (cid:36)(cid:64)2(cid:97)(cid:98) cos(cid:126)(cid:117)(cid:33)(cid:35) 2(cid:49)(cid:64)2(cid:97)(cid:98) sin(cid:126)(cid:117)(cid:33)(cid:35) 2(cid:49)(cid:126)(cid:97)2(cid:50)(cid:98)2(cid:33)2(cid:37)

(cid:53) 1
3

(cid:64)(cid:126)(cid:97)2(cid:49)(cid:98)2(cid:33)2(cid:35)(cid:53)

1
3

.

Hence F(cid:126)A(cid:33)(cid:53)1/3. To show that F e
second system of
(cid:53)1/&(cid:126)(cid:117)0(cid:38)(cid:117)0(cid:38)(cid:49)(cid:117)1(cid:38)(cid:117)1(cid:38)(cid:33). We get

(cid:126)A(cid:33)(cid:53)0, apply A to the
the completely entangled state (cid:117)e(cid:38)

I (cid:94) (cid:115)
x

(cid:117)e(cid:38)(cid:53)

I (cid:94) (cid:115)
y

(cid:117)e(cid:38)(cid:53)

I (cid:94) (cid:115)
z

(cid:117)e(cid:38)(cid:53)

1
&

i
&

i
&

(cid:126)(cid:117)0(cid:38)(cid:117)1(cid:38)(cid:49)(cid:117)1(cid:38)(cid:117)0(cid:38)),

(cid:126)(cid:117)0(cid:38)(cid:117)1(cid:38)(cid:50)(cid:117)1(cid:38)(cid:117)0(cid:38)),

(cid:126)(cid:117)0(cid:38)(cid:117)0(cid:38)(cid:50)(cid:117)1(cid:38)(cid:117)1(cid:38)).

U

i(cid:80)U

(cid:53)( (cid:94)

i(cid:185)UI) (cid:94)(cid:126)(cid:94)

A(cid:56)(cid:33) refer to the ensemble of operators
A
obtained by letting I act on the qubits in U and A(cid:56) on the
qubits not in U. By the properties of the recovery operator,
for (cid:117)U(cid:117)(cid:60)e, the error due to RA
U is 0. Thus it sufﬁces to
bound the error of the remaining terms in the sum for the
interaction. We do this by assuming that the error in each
summand is maximal. That is, the contribution to the total
error by A
U given by the
maximum value of (cid:122)A
(cid:117)x(cid:38)(cid:122)2. The strength of the tensor prod-
uct of operator ensembles can be computed using the next
lemma.

U is bounded by the strength of A

U

(cid:117)B

(cid:53) (cid:40)

(cid:117)2(cid:117)B
1

(cid:117)2(cid:53)(cid:117)B
2

1 and B

2 be operator ensembles. Then

Lemma V.4. Let B
(cid:94)B
(cid:117)2.
1
2
The lemma can be proved by diagonalizing B
†B
† B 2i .
iB 1i
2
2
We deduce that the strength of A

† B 1i and B

U is p (cid:117)U(cid:117). By evaluating

†B
1

1

iB 2i

(cid:53) (cid:40)

the sums over the U’s we obtain the following result.

Theorem V.5. Let R be the recovery operator of an
and A
C

correcting

e-error
code
(cid:53)(cid:36)(cid:65)1(cid:50) pI,A(cid:56)(cid:37) a superoperator on one qubit. Then
(cid:68) p k(cid:126)1(cid:50) p (cid:33)r(cid:50)k.

F(cid:126)C,RA(cid:94) r(cid:33)(cid:62)1(cid:50) (cid:40)
k(cid:46)e

(cid:83) r

qubits

on

n

k

These states are all orthogonal to (cid:117)e(cid:38), whence F e
(cid:126)A(cid:33)(cid:53)0.
Thus this example achieves equality in Eq. (cid:126)45(cid:33) and our
bound is the best possible.

Note that for applications involving entanglements, the
bound needs to be modiﬁed in consideration of the relation-
ship between pure state and entangled state ﬁdelity.

D. Bounds on the ﬁdelity of error-correcting codes
for independent interactions

of

the

Let A be

one-qubit

interaction

form
A(cid:53)(cid:36)A 0 ,A 1 ,...(cid:37) with A 0 close to the identity in some sense.
In this case we would hope that an e-error-correcting code
on n qubits reduces the error after independent interactions
of each qubit with A. That this does indeed hold is an im-
these error-
portant observation for
correcting codes. We are about to show that in the case
(cid:53)(cid:65)1(cid:50)pI, the classical bounds on the probability
where A 0
of error in the corrected code do apply, as has been discussed
by Calderbank and Shor (cid:64)13(cid:35), Steane (cid:64)12(cid:35), and others. When
A 0 is not a scalar multiple of the identity, then additional
terms must be added to the bounds. We defer the discussion
of this case to future papers.

the application of

Assume

then

that A(cid:53)(cid:36)(cid:65)1(cid:50)pI,A 1 ,...(cid:37). Denote

A(cid:56)(cid:53)(cid:36)A 1,. . .(cid:37). and note that the strength of A(cid:56) is

(cid:117)A(cid:56)(cid:117)2(cid:53)sup
(cid:117)x(cid:38)

(cid:40)
i(cid:62)1

(cid:94)x(cid:117)A i

†A i

(cid:117)x(cid:38)(cid:53)p.

Let C(cid:35)Q(cid:94) r be an r-qubit e-error-correcting code with re-
covery operator R. To estimate the error after recovering
from A(cid:94) r, write
A(cid:94) r(cid:53)(cid:36)(cid:65)1(cid:50)pI,A(cid:56)(cid:37) (cid:94) r

(cid:53) (cid:40)
0(cid:60)k(cid:60)r

(cid:40)
U(cid:35)(cid:36)1,...,r(cid:37),(cid:117)U(cid:117)(cid:53)k

(cid:65)1(cid:50)p k(cid:126) (cid:94)

i(cid:185)UI (cid:33) (cid:94) (cid:126) (cid:94)

i(cid:80)U

A(cid:56)(cid:33),

with the obvious interpretation of the tensor products and
Let
factor
which

system each

acting

on.

is

VI. CONCLUSION AND FUTURE WORK

We have laid the foundations for a theory of quantum
error-correcting codes by providing a general deﬁnition of
quantum codes and by characterizing those which can correct
known interactions with zero error. The main features of our
approach include treating a code solely in terms of its sub-
space in a larger Hilbert space and deﬁning decoding opera-
tions in terms of general recovery superoperators. This al-
lows studying codes and their properties for arbitrary
interaction superoperator and avoids explicitly dealing with
decoding and encoding issues when studying the ﬁdelity of a
code given its recovery operator. The treatment in terms of
interaction operators directly leads to the characterizations of
error-correcting codes given in Sec. III. The characterization
in terms of how the operators map individual states (cid:126)Theo-
rem III.2(cid:33) has proved useful for ﬁnding new codes (cid:64)15(cid:35) but
also gives the quantum analog to the classical notion of dis-
tance between code words.

Our approach is not conﬁned to the study of codes which
allow perfect reconstruction of the encoded states. As an
example of what can be done, we deﬁned e-error-correcting
codes on strings of qubits and considered the effect of inde-
pendent interactions. We showed that for interactions with an
identity component, there is a natural way in which the clas-
sical bound on the error can be applied, as has been dis-
cussed informally by other authors. This justiﬁes the effort
that has been put into ﬁnding good e-error-correcting codes.
We observe that this classical bound may be more pessimis-
tic than necessary, but leave a careful study of the ﬁdelity of
various known codes to future work.

We brought up the important issue of how reliable a pre-
dictor the pure state ﬁdelity is for error propagation in en-



<!-- pdf-page: 12 -->
55

THEORY OF QUANTUM ERROR-CORRECTING CODES

911

tangled systems and showed that the entangled state ﬁdelity
is not much less than the pure state ﬁdelity. The fact that it
can be less is an important observation, lest one be deceived
into believing that a ﬁdelity of 1/3 might be adequate if not
compounded by other errors on the same system.

The study of imperfect ﬁdelity codes is far from complete.
Both the sources of introduced error, and its propagation
when recovery is attempted many times, require further
study. Ultimately, these issues determine the circumstances
when an advantage may be gained from using error-
correction schemes.

We would like to ﬁnish by commenting on a general is-
sue. The present work on quantum error correction assumes
that no errors are produced during operations. This is a rea-
sonable assumption if the coding, recovery, and decoding
operations take a small time compared to the rate at which
errors appear (cid:126)i.e., the interaction strengths(cid:33), and the error in
the operations themselves is small compared to the error cor-
rected by the code. We do not believe that this assumption

will remain valid in the context of large scale quantum cal-
culations. It is therefore important to take into account the
fact that operations are imperfect. A step in this direction has
already been taken in (cid:64)26(cid:35). There the particular case of cor-
recting for decoherence (cid:126)phase randomization(cid:33) using the
three-bit scheme presented in the Introduction has been in-
vestigated.

ACKNOWLEDGMENTS

We would like to thank I. Chuang, C. Miquel, J. Paz, B.
Schumacher, J. Smolin, and W. Zurek for useful conversa-
tions. R.L. is grateful to J. Gregson for insights on the intui-
tive approach to error correction. We have both beneﬁted
from interaction with the Quantum Computer group at Los
Alamos National Laboratory. This work was partially per-
formed under the auspices of the U.S. Department of Energy
under Contract No. W-7405-ENG-36.

(cid:64)1(cid:35) P. Shor, in Proceedings, 35th Annual Symposium on Founda-
tions of Computer Science (cid:126)IEEE Press, New York, 1994(cid:33).

(cid:64)2(cid:35) C. Monroe et al., Phys. Rev. Lett. 75, 4714 (cid:126)1995(cid:33).
(cid:64)3(cid:35) P. Domokos, J. M. Raimond, M. Brune, and S. Haroche, Phys.

Rev. Lett. 52, 3554 (cid:126)1995(cid:33).

(cid:64)15(cid:35) R. Laﬂamme, C. Miquel, J.-P. Paz, and W. H. Zurek, Phys.

Rev. Lett. 76, 198 (cid:126)1996(cid:33).

(cid:64)16(cid:35) S. L. Braunstein, Report No. quant-phys/9603024.
(cid:64)17(cid:35) C. H. Bennett, D. P. DiVincenzo, J. A. Smolin, and W. K.

Wootters, Phys. Rev. A 54, 3824 (cid:126)1996(cid:33).

(cid:64)4(cid:35) Q. A. Turchette, C. J. Hood, W. Lange, H. Mabuchi, and H. J.

(cid:64)18(cid:35) L. Vaidman, L. Goldenberg, and S. Wiesner, Phys. Rev. A 54,

Kimble, Phys. Rev. Lett. 75, 4710 (cid:126)1995(cid:33).

(cid:64)5(cid:35) Richard J. Hughes, D. M. Alde, P. Dyer, G. G. Luther, G. L.
Morgan, and M. Schauer, Contemp. Phys. 36, 149 (cid:126)1995(cid:33).

(cid:64)6(cid:35) W. H. Zurek, Phys. Today 40 (cid:126)10(cid:33), 36 (cid:126)1991(cid:33).
(cid:64)7(cid:35) R. Landauer (cid:126)unpublished(cid:33).
(cid:64)8(cid:35) W. G. Unruh (cid:126)unpublished(cid:33); Phys. Rev. A 51, 992 (cid:126)1995(cid:33).
(cid:64)9(cid:35) I. L. Chuang, R. Laﬂamme, P. Shor, and W. H. Zurek, Science

270, 1633 (cid:126)1995(cid:33).

(cid:64)10(cid:35) Comments by C. H. Bennet (cid:126)unpublished(cid:33).
(cid:64)11(cid:35) Peter Shor, Phys. Rev. A 52, 2493 (cid:126)1995(cid:33).
(cid:64)12(cid:35) A. Steane, Phys. Rev. Lett. 77, 793 (cid:126)1996(cid:33).
(cid:64)13(cid:35) A. R. Calderbank and P. W. Shor, Phys. Rev. A 54, 1098

(cid:126)1996(cid:33).

R1745 (cid:126)1996(cid:33).

(cid:64)19(cid:35) F. J. MacWilliams and N. J. Sloane, The Theory of Error-
Correcting Codes (cid:126)North-Holland Publishing Company, New
York, 1977(cid:33).

(cid:64)20(cid:35) W. K. Wootters and W. H. Zurek, Nature (cid:126)London(cid:33) 229, 802

(cid:126)1982(cid:33).

(cid:64)21(cid:35) K. Kraus, States, Effect, and Operations (cid:126)Springer-Verlag,

New York, 1983(cid:33).

(cid:64)22(cid:35) Benjamin Schumacher, Phys. Rev. A 51, 2738 (cid:126)1995(cid:33).
(cid:64)23(cid:35) A. Ekert and C. Macchiavello, Phys. Rev. Lett. 77, 2585

(cid:126)1996(cid:33).

(cid:64)24(cid:35) R. A. Horn and I. Olkin, Am. Math. M. 103, 470 (cid:126)1996(cid:33).
(cid:64)25(cid:35) M. A. Nielsen and B. Schumacher, Phys. Rev. A 54, 2629

(cid:64)14(cid:35) I. L. Chuang and R. Laﬂamme, Los Alamos National Labora-

(cid:126)1996(cid:33).

tory Report No. LA-UR-95-3641 (cid:126)unpublished(cid:33).

(cid:64)26(cid:35) I. Chuang and Y. Yamamoto, Phys. Rev. A 55, 114 (cid:126)1997(cid:33).


