<!-- generated-by: proofmatch local extraction -->
<!-- source-pdf-sha256: e658890bd7efd74e8042d47d6141825821ce4e0e28440509a52fca914282bbb7 -->
<!-- extractor: arxiv-tex-source Thesis.tex, SELECTIVE: chapters "Basics of Quantum Error Correction", "Stabilizer Coding", "Bounds on Quantum Error-Correcting Codes" only (long text; other chapters deliberately not converted) -->

<!-- pdf-page: 1 -->
\chapter{Basics of Quantum Error Correction}
\label{chap-basics}

\section{The Quantum Channel}

Now we turn to the quantum channel.  A noisy quantum channel can be a 
regular communications channel which we expect to preserve at least some 
degree of quantum coherence, or it can be the passage of time as a set of 
qubits sits around, interacting with its environment, or it can be the result 
of operating with a noisy gate on some qubits in a quantum computer.  
In any of these cases, the input of a pure quantum state can produce a 
mixed state as output as the data qubits become entangled with the 
environment.  Even when a pure state comes out, it might not be the same 
state as the one that went in.

At first it appears that trying to correct a mixed state back into the correct
pure state is going to be harder than correcting an erroneous pure state, but 
this is not the case.  The output mixed state can be considered as an ensemble 
of pure states.  If we can correct each of the pure states in the ensemble 
back to the original input state, we have corrected the full mixed state.  
Another way of phrasing this is to say the channel applies a 
superoperator to the input density matrix.  We can diagonalize 
this superoperator and write it as the direct sum of a number of 
different matrices acting directly on the possible input pure states with 
various probabilities.  If the code can correct any of the possible matrices, 
it can correct the full superoperator.  A key point is that the 
individual matrices need not be unitary.  From now on, I will only consider 
the effects of a (possibly non-unitary) matrix acting on a pure state.

\section{A Simple Code}

For the moment, let us consider only channels which cause an error on a 
single qubit at a time.  We wish to protect a single logical qubit against 
error.  We cannot send it through the channel as is, because the one qubit 
that is affected might be the one we want to keep.  Suppose we send through 
nine qubits after encoding the logical qubit as follows:
\begin{eqnarray}
\ket{0} & \rightarrow & \ket{\overline{0}} = (\ket{000} + \ket{111}) 
(\ket{000} + \ket{111}) (\ket{000} + \ket{111}) \\
\ket{1} & \rightarrow & \ket{\overline{1}} = (\ket{000} - \ket{111}) 
(\ket{000} - \ket{111}) (\ket{000} - \ket{111}).
\end{eqnarray}
The data is no longer stored in a single qubit, but instead spread out 
among nine of them.  Note that even if we know the nine qubits are in one 
of these two states, we cannot determine which one without making a 
measurement on at least three qubits.  This code is due to 
Shor~\cite{shor-9qubit}.

Suppose the channel flips a single qubit, say the first one, switching 
$\ket{0}$ and $\ket{1}$.  Then by comparing the first two qubits, we find 
they are different, which is not allowed for any valid codeword.  Therefore 
we know an error occurred, and furthermore, it flipped either the first or 
second qubit.  Note that we do not actually measure the first and second 
qubits, since this would destroy the superposition in the codeword; we just 
measure the difference between them.

Now we compare the first and third qubits.  Since the first qubit was 
flipped, it will disagree with the third; if the second qubit had been 
flipped, the first and third would have agreed.  Therefore, we have 
narrowed down the error to the first qubit and we can fix it simply by 
flipping it back.  To handle possible bit flips on the other blocks of three, 
we do the same comparisons inside the other blocks.

However, this is not the only sort of error that could have occurred.  The 
channel might have left the identity of the 0 and 1 alone, but altered their 
relative phase, introducing, for instance, a relative factor of $-1$ when 
the first qubit is $\ket{1}$.  Then the two basis states become
\begin{eqnarray}
\ket{\overline{0}} & \rightarrow & (\ket{000} - \ket{111}) (\ket{000} + 
\ket{111}) (\ket{000} + \ket{111}) \\
\ket{\overline{1}} & \rightarrow & (\ket{000} + \ket{111}) (\ket{000} - 
\ket{111}) (\ket{000} - \ket{111}).
\end{eqnarray}
By comparing the sign of the first block of three with the second block of 
three, we can see that a sign error has occurred in one of those blocks.  
Then by comparing the signs of the first and third blocks of three, we 
narrow the sign error down to the first block, and flip the sign back to 
what it should be.  Again, we do not want to actually measure the signs, 
only whether they agree.  In this case, measuring the signs would give us 
information about whether the state is $\ket{\overline{0}}$ or 
$\ket{\overline{1}}$, which would destroy any superposition between 
them.

This does not exhaust the list of possible one qubit errors.  For instance, we 
could have both a bit flip and a sign flip on the same qubit.  However, by 
going through both processes described above, we will fix first the bit flip, 
then the sign flip (in fact, this code will correct a bit flip and a sign flip 
even if they are on different qubits).  The original two errors can be 
described as the operation of
\begin{equation}
\X = \pmatrix{0 & 1 \cr 1 & 0} \ {\rm and}\ 
\Z = \pmatrix{1 & \ 0 \cr 0 & -1}.
\end{equation}
The simultaneous bit and sign flip is
\begin{equation}
\Y = i \X \Z = \pmatrix{0 & -i \cr i & \ 0}.
\end{equation}
Sometimes I will write $\Xs{i}$, $\Ys{i}$, or $\Zs{i}$ to represent $\X$, $\Y$,
or $\Z$ acting on the $i$th qubit.

The most general one-qubit error that can occur is some $2 \times 2$ 
matrix; but such a matrix can always be written as the (complex) linear 
combination of $\X$, $\Y$, $\Z$, and the $2 \times 2$ identity matrix $I$.  
Consider what happens to the code when such an error occurs:
\begin{equation}
\ket{\psi} = \alpha \ket{\overline{0}} + \beta \ket{\overline{1}}
\rightarrow a \Xs{i} \ket{\psi} + b \Ys{i} \ket{\psi} + c \Zs{i} \ket{\psi} +
d \ket{\psi}.
\end{equation}
Suppose we perform the process above, comparing bits within a block of 
three, and comparing the signs of blocks of three.  This acts as a 
measurement of which error (or the identity) has occurred, causing the 
state, originally in a superposition, to collapse to $\Xs{i} \ket{\psi}$ with 
probability $|a|^2$, to $\Ys{i} \ket{\psi}$ with probability $|b|^2$, to 
$\Zs{i} \ket{\psi}$ with probability $|c|^2$, and to $\ket{\psi}$ with
probability $|d|^2$.  In any of the four cases, we have determined which error
occurred and we can fix it.

<!-- pdf-page: 2 -->
\section{Properties of Any Quantum Code}
\label{sec-general-prop}

Now let us consider properties of more general codes.  A code to encode 
$k$ qubits in $n$ qubits will have $2^k$ basis codewords corresponding to 
the basis of the original states.  Any linear combination of these basis 
codewords is also a valid codeword, corresponding to the same linear 
combination of the unencoded basis states.  The space $T$ of valid 
codewords (the {\em coding space}) is therefore a Hilbert space in its own 
right, a subspace of the full $2^n$-dimensional Hilbert space.  As with 
Shor's nine-qubit code, if we can correct errors $E$ and $F$, we can correct 
$aE + bF$, so we only need to consider whether the code can correct a basis of 
errors.  One convenient basis to use is the set of tensor products of $\X$, 
$\Y$, $\Z$, and $I$.  The {\em weight} of an operator of this form is the 
number of qubits on which it differs from the identity.  The set of all these 
tensor products with a possible overall factor of $-1$ or $\pm i$ forms a 
group $\G$ under multiplication.  $\G$ will play a major role in the 
stabilizer formalism.  Sometimes I will write it $\G_n$ to distinguish the 
groups for different numbers of qubits.  $\G_1$ is just the quaternionic 
group; $\G_n$ is the direct product of $n$ copies of the quaternions 
modulo all but a global phase factor.

In order for the code to correct two errors $E_a$ and $E_b$, we must 
always be able to distinguish error $E_a$ acting on one basis codeword 
$\ket{\psi_i}$ from error $E_b$ acting on a different basis codeword 
$\ket{\psi_j}$.  We can only be sure of doing this if $E_a \ket{\psi_1}$ is 
orthogonal to $E_b \ket{\psi_2}$; otherwise there is some chance of 
confusing them.  Thus,
\begin{equation}
\bra{\psi_i} E_a^\dagger E_b \ket{\psi_j} = 0
\label{eq-cond-orthogonal}
\end{equation}
when $i \neq j$ for correctable errors $E_a$ and $E_b$.  Note that we 
normally include the identity in the set of possible ``errors,'' since we do
not want to confuse an error on one qubit with nothing happening to another.  
If we have a channel in which we are certain {\em some} error occurred, 
we do not need to include the identity as a possible error.  In any case,
the set of correctable errors is unlikely to be a group --- it does not
even need to be closed under multiplication.

However, (\ref{eq-cond-orthogonal}) is insufficient to guarantee a code will 
work as a quantum error-correcting code.  When we make a measurement to find 
out about the error, we must learn nothing about the actual state of the code 
within the coding space.  If we did learn something, we would be disturbing 
superpositions of the basis states, so while we might correct the basis 
states, we would not be correcting an arbitrary valid codeword.  We learn 
information about the error by measuring $\bra{\psi_i} E_a^\dagger E_b 
\ket{\psi_i}$ for all possible errors $E_a$ and $E_b$.  This quantity must 
therefore be the same for all the basis codewords:
\begin{equation}
\bra{\psi_i} E_a^\dagger E_b \ket{\psi_i} = \bra{\psi_j} E_a^\dagger E_b 
\ket{\psi_j}.
\label{eq-cond-structure}
\end{equation}
We can combine equations (\ref{eq-cond-orthogonal}) and 
(\ref{eq-cond-structure}) into a single equation:
\begin{equation}
\bra{\psi_i} E_a^\dagger E_b \ket{\psi_j} = C_{ab} \delta_{ij},
\label{eq-condition}
\end{equation}
where $\ket{\psi_i}$ and $\ket{\psi_j}$ run over all possible basis 
codewords, $E_a$ and $E_b$ run over all possible errors, and $C_{ab}$ is 
independent of $i$ and $j$.  This condition was found by Knill and 
Laflamme~\cite{knill-laflamme-theory} and Bennett {\it et 
al.}~\cite{bennett-tome}.

The above argument shows that (\ref{eq-condition}) is a necessary 
condition for the code to correct the errors $\{E_a\}$.  It is also a 
sufficient condition:  The matrix $C_{ab}$ is Hermitian, so it can be 
diagonalized.  If we do this and rescale the errors $\{E_a\}$ appropriately, we 
get a new basis $\{F_a\}$ for the space of possible errors, with either
\begin{equation}
\bra{\psi_i} F_a^\dagger F_b \ket{\psi_j} = \delta_{ab} \delta_{ij}
\end{equation}
or
\begin{equation}
\bra{\psi_i} F_a^\dagger F_b \ket{\psi_j} = 0,
\end{equation}
depending on $a$.  Note that this basis will not necessarily contain 
operators that are tensor products of one-qubit operators.  Errors of the 
second type actually annihilate any codeword, so the probability of one 
occuring is strictly zero and we need not consider them.  The other errors 
always produce orthogonal states, so we can make some measurement that 
will tell us exactly which error occurred, at which point it is a simple 
matter to correct it.  Therefore, a code satisfies equation 
(\ref{eq-condition}) for all $E_a$ and $E_b$ in some set ${\cal E}$ iff the
code can correct all errors in ${\cal E}$.

Another minor basis change allows us to find a basis where any two errors 
acting on a given codeword either produce orthogonal states or exactly the 
same state.  The errors $F_a$  that annihilate codewords correspond to two 
errors that act the same way on codewords.  For instance, in Shor's 
nine-qubit code, $\Zs{1}$ and $\Zs{2}$ act the same way on the code, so $\Zs{1} 
- \Zs{2}$ will annihilate codewords.  This phenomenon will occur iff $C_{ab}$ 
does not have maximum rank.  A code for which $C_{ab}$ is singular is 
called a {\em degenerate} code, while a code for which it is not is {\em 
nondegenerate}.  Shor's nine-qubit code is degenerate; we will see many 
examples of nondegenerate codes later.  Note that whether a code is 
degenerate or not depends on the set of errors it is intended to correct.  
For instance, a two-error-correcting degenerate code might be 
nondegenerate when considered as a one-error-correcting code.

In equation~(\ref{eq-condition}), $E = E_a^\dagger E_b$ is still in the group 
$\G$ when $E_a$ and $E_b$ are in $\G$.  The weight of the smallest $E$ in 
$\G$ for which (\ref{eq-condition}) does {\em not} hold is called the {\em 
distance} of the code.  A quantum code to correct up to $t$ errors must 
have distance at least $2t+1$.  Every code has distance at least one.  A
distance $d$ code encoding $k$ qubits in $n$ qubits is described as an
$[n, k, d]$ code.  Note that a quantum $[n,k,d]$ code is often written
in the literature as $[[n,k,d]]$ to distinguish it from a classical
$[n,k,d]$ code.  I have chosen the notation $[n,k,d]$ to emphasize the
similarities with the classical theory; when I need to distinguish, I
will do so using the words ``quantum'' and ``classical.''

<!-- pdf-page: 3 -->
We can also consider variations of the usual error-correction problem.  
For instance, suppose we only want to detect if an error has occurred, not 
to correct it.  This could, for instance, be used to prevent errors using the 
quantum Zeno effect~\cite{vaidman}.  In this case, we do not need to 
distinguish error $E_a$ from $E_b$, only from the identity.  We can use the 
same argument to find (\ref{eq-condition}), only now $E_b = I$ always.  
This means a code to detect $s$ errors must have distance at least $s+1$.  
Another variation is when we know in which qubit(s) an error has 
occurred, as in the quantum erasure channel~\cite{grassl}.  In this case, we 
only need distinguish $E_a$ from those $E_b$ affecting the same qubits.  
This means that $E_a^\dagger E_b$ has the same weight as $E_a$, and to correct 
$r$ such located errors, we need a code of distance at least $r+1$.  We can 
also imagine combining all of these tasks.  A code to correct $t$ arbitrary 
errors, $r$ additional located errors, and detect a further $s$ errors must 
have distance at least $r + s + 2t + 1$.

\section{Error Models}

In this thesis, I will mostly assume that errors occur independently on 
different qubits, and that when an error occurs on a qubit, it is equally 
likely to be a $\X$, $\Y$, or $\Z$ error.  If the probability $\epsilon$ of 
error per qubit is fairly small, it is often useful to simply ignore the 
possibility of more than $t$ errors, since this only occurs with probability 
$O(\epsilon^{t+1})$.  Thus, I will typically deal with codes that correct up 
to $t$ arbitrary errors.  Such a code will handle any error on up to $t$ qubits 
that leaves the data somewhere in the normal computational space (although 
moving it outside of the space of valid codewords).

In some systems, there will be errors that move the system outside of the
computational space.  For instance, if the data is stored as the ground or
metastable excited state of an ion, the electron might instead end up in a 
different excited state.  If the data is stored in the polarization of a
photon, the photon might escape.  In both of these cases, the normal error 
correction networks will not function properly, since they assume that the
qubit is either in the state $\ket{0}$ or $\ket{1}$.  However, by performing
some measurement that distinguishes between the computational Hilbert space
and other possible states, we can determine not only that this sort of
{\em leakage error} has occurred, but also on which qubit it has occurred.
Then we can cool the atom to the ground state or introduce a new photon with
random polarization, and the error becomes a located error, which was
discussed at the end of the previous section.  One possible network of gates 
to detect a leakage error is given in figure~\ref{fig-leakage} (see appendix
\ref{app-gates} for a description of the symbols used in this and later
figures).
\begin{figure}
\centering
\begin{picture}(120,60)

\put(0,34){\makebox(20,12){$\ket{\psi}$}}
\put(0,14){\makebox(20,12){$\ket{0}$}}

\put(20,20){\line(1,0){100}}
\put(20,40){\line(1,0){100}}

\put(40,40){\circle*{4}}
\put(40,40){\line(0,-1){24}}
\put(40,20){\circle{8}}

\put(60,40){\circle{8}}
\put(60,36){\line(0,1){8}}

\put(80,40){\circle*{4}}
\put(80,40){\line(0,-1){24}}
\put(80,20){\circle{8}}

\put(100,40){\circle{8}}
\put(100,36){\line(0,1){8}}

\end{picture}
\caption{Network to detect leakage errors.}
\label{fig-leakage}
\end{figure}
This network asssumes that states outside the normal computational space do
not interact at all with other qubits.  If the data state $\ket{\psi}$ is
either $\ket{0}$ or $\ket{1}$, the ancilla qubit will flip and become $\ket{1}$.
If the data state is neither $\ket{0}$ nor $\ket{1}$, the ancilla will remain
$\ket{0}$, thus signalling a leakage error on this data qubit.

Another possible difficulty arises when correlated errors on multiple qubits
can occur.  While this can in principle be a severe problem, it can be handled 
without a change in formalism as long as the chance of a correlated error drops
rapidly enough with the size of the blocks of errors.  Since a $t$-qubit
error will occur with probability $O(\epsilon^t)$ when the probability of
uncorrelated single-qubit errors is $\epsilon$, as long as the probability
of a $t$-qubit correlated error is $O(\epsilon^t)$, the correlated errors
cause no additional problems.

In real systems, the assumption that errors are equally likely to be $\X$,
$\Y$, and $\Z$ errors is a poor one.  In practice, some linear combinations
of $\X$, $\Y$, and $\Z$ are going to be more likely than others.  For instance,
when the qubits are ground or excited states of an ion, a likely source of
errors is spontaneous emission.  After some amount of time, the excited
state will either decay to the ground state, producing the error $\X + i\Y$
with probability $\epsilon$, or it will not, which changes the relative 
amplitudes of $\ket{0}$ and $\ket{1}$, resulting in the error $I - \Z$ with
probability $O (\epsilon^2)$.  A channel that performs this sort of time
evolution is known as an {\em amplitude damping} channel.  Since the only 
$O(1)$ effect of time evolution is the identity, this sort of error can be 
protected against to lowest order by a code to correct an arbitrary single 
error.  However, codes that take account of the restricted possibilities
for errors can be more efficient than codes that must correct a general
error~\cite{leung}, and understanding the physically likely sources of
error will certainly be an important part of engineering quantum computers.

<!-- pdf-page: 4 -->
\chapter{Stabilizer Coding}
\label{chap-stabilizers}

\section{The Nine-Qubit Code Revisited}

Let us look more closely at the procedure we used to correct errors for the 
nine-qubit code.  To detect a bit flip error on one of the first three qubits, 
we compared the first two qubits and the first and third qubits.  This is 
equivalent to measuring the eigenvalues of $\Zs{1} \Zs{2}$ and $\Zs{1} \Zs{3}$.
If the first two qubits are the same, the eigenvalue of $\Zs{1} \Zs{2}$ is 
$+1$; if they are different, the eigenvalue is $-1$.  Similarly, to detect a 
sign error, we compare the signs of the first and second blocks of three and 
the first and third blocks of three.  This is equivalent to measuring the 
eigenvalues of $\Xs{1} \Xs{2} \Xs{3} \Xs{4} \Xs{5} \Xs{6}$ and $\Xs{1} \Xs{2}
\Xs{3} \Xs{7} \Xs{8} \Xs{9}$.  Again, if the signs agree, the eigenvalues will 
be $+1$; if they disagree, the eigenvalues will be $-1$.  In order to totally 
correct the code, we must measure the eigenvalues of a total of eight operators.
They are listed in table~\ref{table-9qubit}.
\begin{table}
\centering
\begin{tabular}{c|ccccccccc}
$M_1$ & $\Z$ & $\Z$ & $I$ & $I$ & $I$ & $I$ & $I$ & $I$ & $I$ \\
$M_2$ & $\Z$ & $I$ & $\Z$ & $I$ & $I$ & $I$ & $I$ & $I$ & $I$ \\
$M_3$ & $I$ & $I$ & $I$ & $\Z$ & $\Z$ & $I$ & $I$ & $I$ & $I$ \\
$M_4$ & $I$ & $I$ & $I$ & $\Z$ & $I$ & $\Z$ & $I$ & $I$ & $I$ \\
$M_5$ & $I$ & $I$ & $I$ & $I$ & $I$ & $I$ & $\Z$ & $\Z$ & $I$ \\
$M_6$ & $I$ & $I$ & $I$ & $I$ & $I$ & $I$ & $\Z$ & $I$ & $\Z$ \\
$M_7$ & $\X$ & $\X$ & $\X$ & $\X$ & $\X$ & $\X$ & $I$ & $I$ & $I$ \\
$M_8$ & $\X$ & $\X$ & $\X$ & $I$ & $I$ & $I$ & $\X$ & $\X$ & $\X$
\end{tabular}
\caption{The stabilizer for Shor's nine-qubit code}
\label{table-9qubit}
\end{table}

The two valid codewords $\ket{\overline{0}}$ and $\ket{\overline{1}}$ in 
Shor's code are eigenvectors of all eight of these operators with eigenvalue 
$+1$.  All the operators in $\G$ that fix both $\ket{\overline{0}}$ and 
$\ket{\overline{1}}$ can be written as the product of these eight operators.  
The set of operators that fix $\ket{\overline{0}}$ and $\ket{\overline{1}}$ 
form a group $S$, called the {\em stabilizer} of the code, and $M_1$ 
through $M_8$ are the generators of this group.

When we measure the eigenvalue of $M_1$, we determine if a bit flip 
error has occurred on qubit one or two, i.e., if $\Xs{1}$ or $\Xs{2}$ has 
occurred.  Note that both of these errors anticommute with $M_1$, while 
$\Xs{3}$ through $\Xs{9}$, which cannot be detected by just $M_1$, commute 
with it.  Similarly, $M_2$ detects $\Xs{1}$ or $\Xs{3}$, which anticommute 
with it, and $M_7$ detects $\Zs{1}$ through $\Zs{6}$.  In general, if 
$M \in S$, $\{M, E\} = 0$, and $\ket{\psi} \in T$, then
\begin{equation}
M E \ket{\psi} = - E M \ket{\psi} = - E \ket{\psi},
\end{equation}
so $E \ket{\psi}$ is an eigenvector of $M$ with eigenvalue $-1$ instead of 
$+1$ and to detect $E$ we need only measure $M$.

The distance of this code is in fact three.  Even a cursory perusal reveals 
that any single-qubit operator $\Xs{i}$, $\Ys{i}$, or $\Zs{i}$ will anticommute 
with one or more of $M_1$ through $M_8$.  Since states with different 
eigenvalues are orthogonal, condition~(\ref{eq-condition}) is satisfied when 
$E_a$ has weight one and $E_b = I$.  We can also check that every two-qubit 
operator $E$ anticommutes with some element of $S$, except for those of 
the form $\Zs{a} \Zs{b}$ where $a$ and $b$ are in the same block of three.  
However, the operators of this form are actually in the stabilizer.  This means 
that $\Zs{a} \Zs{b} \ket{\psi} = \ket{\psi}$ for any codeword $\ket{\psi}$, and 
$\bra{\psi} \Zs{a} \Zs{b} \ket{\psi} = \langle \psi \ket{\psi} = 1$ for all 
codewords $\ket{\psi}$, and these operators also satisfy 
equation~(\ref{eq-condition}).  Since $\Zs{a} \Zs{b}$ is in the stabilizer,
both $\Zs{a}$ and $\Zs{b}$ act the same way on the codewords, and there is no 
need to distinguish them.  When we get to operators of weight three, we do 
find some for which (\ref{eq-condition}) fails.  For instance, $\Xs{1} \Xs{2} 
\Xs{3}$ commutes with everything in $S$, but
\begin{eqnarray}
\bra{\overline{0}} \Xs{1} \Xs{2} \Xs{3} \ket{\overline{0}} & = & +1 \\
\bra{\overline{1}} \Xs{1} \Xs{2} \Xs{3} \ket{\overline{1}} & = & -1.
\end{eqnarray}

\section{The General Stabilizer Code}

The stabilizer construction applies to many more codes than just the 
nine-qubit one~\cite{gottesman-stab,calderbank-stab}.  In general, the 
stabilizer $S$ is some Abelian subgroup of $\G$ and the coding space $T$ is 
the space of vectors fixed by $S$.  Since $\Y$ has imaginary components, 
while $\X$ and $\Z$ are real, with an even number of $\Y$'s in each element
of the stabilizer, all the coefficients in the basis codewords can be chosen
to be real; if there are an odd number of $\Y$'s, they may be imaginary.  
However, Rains has shown that whenever a (possibly complex) code exists, a 
real code exists with the same parameters~\cite{rains-shadow}.  Therefore, I 
will largely restrict my attention to real codes.

For a code to encode $k$ qubits in $n$, $T$ has $2^k$ dimensions and $S$ 
has $2^{n-k}$ elements.  $S$ must be an Abelian group, since only 
commuting operators can have simultaneous eigenvectors, but provided it 
is Abelian and neither $i$ nor $-1$ is in $S$, the space $T = \{ \ket{\psi}\ 
{\rm s.t.} \ M \ket{\psi} = \ket{\psi} \ \forall M \in S \}$ does have 
dimension $2^k$.  At this point it will be helpful to note a few properties of 
$\G$.  Since $\X^2 = \Y^2 = \Z^2 = +1$, every element in $\G$ squares to 
$\pm 1$.  Also, $\X$, $\Y$, and $\Z$ on the same qubit anticommute, while 
they commute on different qubits.  Therefore, any two elements of $\G$ 
either commute or they anticommute.  $\X$, $\Y$, and $\Z$ are all 
Hermitian, but of course $(iI)^\dagger = -i I$, so elements of $\G$ can be 
either Hermitian or anti-Hermitian.  In either case, if $A \in \G$, 
$A^\dagger \in G$ also.  Similarly, $\X$, $\Y$, and $\Z$ are all unitary, so 
every element of $\G$ is unitary.

<!-- pdf-page: 5 -->
As before, if $M \in S$, $\ket{\psi_i} \in T$, and $\{M, E \} = 0$, then
$M E \ket{\psi_i} =- E \ket{\psi_i}$, so
\begin{equation}
\bra{\psi_i} E \ket{\psi_j} = \bra{\psi_i} M E \ket{\psi_j} = - \bra{\psi_i} E 
\ket{\psi_j} = 0.
\end{equation}
Therefore the code satisfies~(\ref{eq-cond-orthogonal}) whenever $E = 
E_a^\dagger E_b = \pm E_a E_b$ anticommutes with $M$ for some $M \in 
S$.  In fact, in such a case it also satisfies~(\ref{eq-cond-structure}), since 
$\bra{\psi_i} E \ket{\psi_i} = \bra{\psi_j} E \ket{\psi_j} = 0$.  Therefore, if 
$E_a^\dagger E_b$ anticommutes with some element of $S$ for all errors 
$E_a$ and $E_b$ in some set, the code will correct that set of errors.

Of course, strictly speaking, this is unlikely to occur.  Generally, $I$ will 
be an allowed error, and $E = I^\dagger I$ commutes with everything.  
However, $S$ is a group, so $I \in S$.  In general, if $E \in S$,
\begin{equation}
\bra{\psi_i} E \ket{\psi_j} = \langle \psi_i \ket{\psi_j} = \delta_{ij}.
\end{equation}
This will satisfy equation~(\ref{eq-condition}) also.

Now, there generally are many elements of $\G$ that commute with 
everything in $S$ but are not actually in $S$.  The set of elements in $\G$ 
that commute with all of $S$ is defined as the centralizer $C(S)$ of $S$ in 
$\G$.  Because of the properties of $S$ and $\G$, the centralizer is actually 
equal to the normalizer $N(S)$ of $S$ in $\G$, which is defined as the set of 
elements of $\G$ that fix $S$ under conjugation.  To see this, note that for
any $A \in \G$, $M \in S$, 
\begin{equation}
A^\dagger M A = \pm A^\dagger A M = \pm M.
\end{equation}
Since $-1 \notin S$, $A \in N(S)$ iff $A \in C(S)$, so $N(S) = C(S)$.  Note 
that $S \subseteq N(S)$.  In fact, $S$ is a normal subgroup of $N(S)$.  
$N(S)$ contains $4 \cdot 2^{n+k}$ elements.  The factor of four is for the 
overall phase factor.  Since an overall phase has no effect on the physical
quantum state, often, when considering $N(S)$, I will only really 
consider $N(S)$ without this global phase factor.

If $E \in N(S)-S$, then $E$ rearranges elements of $T$ but does not take 
them out of $T$: if $M \in S$ and $\ket{\psi} \in T$, then
\begin{equation}
M E \ket{\psi} = EM \ket{\psi} = E \ket{\psi},
\end{equation}
so $E \ket{\psi} \in T$ also.  Since $E \notin S$, there is some state in $T$ 
that is not fixed by $E$.  Unless it differs from an element of $S$ by an 
overall phase, $E$ will therefore be undetectable by this code.

Putting these considerations together, we can say that a quantum code 
with stabilizer $S$ will detect all errors $E$ that are either in $S$ or 
anticommute with some element of $S$.  In other words, $E \in S \cup (\G - 
N(S))$.  This code will correct any set of errors $\{ E_i \}$ iff $E_a E_b \in 
S \cup (\G - N(S)) \ \forall E_a, E_b$ (note that $E_a^\dagger E_b$ commutes 
with $M \in \G$ iff $E_a E_b = \pm E_a^\dagger E_b$ does).  For instance, the 
code will have distance $d$ iff $N(S) - S$ contains no elements of weight less 
than $d$.  If $S$ has elements of weight less than $d$ (except the identity), 
it is a degenerate code; otherwise it is a nondegenerate code.  For instance, 
the nine-qubit code is degenerate, since it has distance three and $\Zs{1} 
\Zs{2} \in S$.  A nondegenerate stabilizer code satisfies
\begin{equation}
\bra{\psi_i} E_a^\dagger E_b \ket{\psi_j} = \delta_{ab} \delta_{ij}.
\end{equation}
By convention, an $[n, 0, d]$ code must be nondegenerate.  When $E_a E_b \in S$,
we say that the errors $E_a$ and $E_b$ are degenerate.  We cannot distinguish
between $E_a$ and $E_b$, but there is no need to, since they have the same
effect on the codewords.

It is sometimes useful to define the {\em error syndrome} for a stabilizer 
code.  Let $f_M : \G \rightarrow {\bf Z}_2$, 
\begin{equation}
f_M (E) = \left\{ \begin{array}{ll} 0 & \mbox{if $[M, E] = 0$} \\ 1 & 
\mbox{if $\{M, E\} = 0$} \end{array} \right.
\end{equation}
and $f (E) = (f_{M_1} (E), \ldots, f_{M_{n-k}} (E) )$, where $M_1, \ldots, 
M_{n-k}$ are the generators of $S$.  Then $f(E)$ is some $(n-k)$-bit binary 
number which is $0$ iff $E \in N(S)$.  $f(E_a) = f(E_b)$ iff $f(E_a E_b) = 0$, 
so for a nondegenerate code, $f(E)$ is different for each correctable error 
$E$.

In order to perform the error-correction operation for a stabilizer code, all 
we need to do is measure the eigenvalue of each generator of the 
stabilizer.  The eigenvalue of $M_i$ will be $(-1)^{f_{M_i} (E)}$, so this 
process will give us the error syndrome.  The error syndrome in turn tells 
us exactly what error occurred (for a nondegenerate code) or what set of 
degenerate errors occurred (for a degenerate code).  The error will always be 
in $\G$ since the code uses that error basis, and every operator in $\G$ is 
unitary, and therefore invertible.  Then we just apply the error operator (or 
one equivalent to it by multiplication by $S$) to fix the state.  Note that
even if the original error that occurred is a nontrivial linear combination of 
errors in $\G$, the process of syndrome measurement will project onto one
of the basis errors.  If the resulting error is not in the correctable set, 
we will end up in the wrong encoded state, but otherwise, we are in the 
correct state.  In chapter~\ref{chap-fault-tolerant}, I describe a few ways 
of measuring the error syndrome that are tolerant of imperfect component gates.

Since the elements of $N(S)$ move codewords around within $T$, they 
have a natural interpretation as encoded operations on the codewords.  
Since $S$ fixes $T$, actually only $N(S) / S$ will act on $T$ nontrivially.  If 
we pick a basis for $T$ consisting of eigenvectors of $n$ commuting elements 
of $N(S)$, we get an automorphism $N(S) / S \rightarrow \G_k$.  $N(S)/S$ can 
therefore be generated by $i$ (which we will by and large ignore) and $2k$ 
equivalence classes, which I will write $\Xbar_i$ and $\Zbar_i$ ($i=1 
\ldots k$), where $\Xbar_i$ maps to $\Xs{i}$ in $\G_k$ and $\Zbar_i$ 
maps to $\Zs{i}$ in $\G_k$.  They are encoded $\X$ and $\Z$ operators for 
the code.  If $k=1$, I will write $\Xbar_1 = \Xbar$ and $\Zbar_1 = \Zbar$.  
The $\Xbar$ and $\Zbar$ operators satisfy
\begin{eqnarray}
[\Xbar_i, \Xbar_j] & = & 0 \\
{[}\Zbar_i, \Zbar_j] & = & 0 \\
{[}\Xbar_i, \Zbar_j] & = & 0\ (i \neq j) \\
\{\Xbar_i, \Zbar_i \} & = & 0.
\end{eqnarray}

<!-- pdf-page: 6 -->
\section{Some Examples}
\label{sec-stab-examples}

I shall now present a few short codes to use as examples.  The first 
encodes one qubit in five qubits~\cite{bennett-tome,laflamme-5qubit} and is 
given in table~\ref{table-5qubit}.
\begin{table}
\centering
\begin{tabular}{c|ccccc}
$M_1$ & $\X$ & $\Z$ & $\Z$ & $\X$ & $I$ \\
$M_2$ & $I$ & $\X$ & $\Z$ & $\Z$ & $\X$ \\
$M_3$ & $\X$ & $I$ & $\X$ & $\Z$ & $\Z$ \\
$M_4$ & $\Z$ & $\X$ & $I$ & $\X$ & $\Z$ \\
\hline
\low{$\Xbar$} & \low{$\X$} & \low{$\X$} & \low{$\X$} & \low{$\X$} & \low{$\X$} 
\\
\low{$\Zbar$} & \low{$\Z$} & \low{$\Z$} & \low{$\Z$} & \low{$\Z$} & \low{$\Z$}
\end{tabular}
\caption{The stabilizer for the five-qubit code.}
\label{table-5qubit}
\end{table}
I have also included $\Xbar$ and $\Zbar$, which, along with $M_1$ 
through $M_4$, generate $N(S)$.  Note that this code is {\em cyclic} (i.e., 
the stabilizer and codewords are invariant under cyclic permutations of
the qubits).  It has distance three (for instance, $\Ys{1} \Zs{2} \Ys{3} \in 
N(S)-S$) and is nondegenerate.  We can take the basis codewords for this code 
to be
\begin{equation}
\ket{\overline{0}} = \Sum_{M \in S} M \ \ket{00000}
\end{equation}
and
\begin{equation}
\ket{\overline{1}} = \Xbar \ket{\overline{0}}.
\end{equation}
That is,
\begin{eqnarray}
\ket{\overline{0}} & = & \ket{00000} + M_1 \ket{00000} + M_2 \ket{00000} +
M_3 \ket{00000} + M_4 \ket{00000} \nonumber \\
& & \quad \mbox{} + M_1 M_2 \ket{00000} + M_1 M_3 \ket{00000} +
M_1 M_4 \ket{00000} \nonumber \\
& & \quad \mbox{} + M_2 M_3 \ket{00000} + M_2 M_4 \ket{00000} + 
M_3 M_4 \ket{00000} \\
& & \quad \mbox{} + M_1 M_2 M_3 \ket{00000} + M_1 M_2 M_4 \ket{00000} + 
M_1 M_3 M_4 \ket{00000} \nonumber \\
& & \quad \mbox{} + M_2 M_3 M_4 \ket{00000} + M_1 M_2 M_3 M_4 \ket{00000} 
\nonumber \\
& = & \ket{00000} + \ket{10010} + \ket{01001} + \ket{10100} \nonumber \\
& & \mbox{} + \ket{01010} - \ket{11011} - \ket{00110} - \ket{11000} \nonumber \\
& & \mbox{} - \ket{11101} - \ket{00011} - \ket{11110} - \ket{01111} \\
& & \mbox{} - \ket{10001} - \ket{01100} - \ket{10111} + \ket{00101}, \nonumber
\end{eqnarray}
and
\begin{eqnarray}
\ket{\overline{1}} & = & \Xbar \ket{\overline{0}} \nonumber \\
& = & \ket{11111} + \ket{01101} + \ket{10110} + \ket{01011} \nonumber \\
& & \mbox{} + \ket{10101} - \ket{00100} - \ket{11001} - \ket{00111} \nonumber \\
& & \mbox{} - \ket{00010} - \ket{11100} - \ket{00001} - \ket{10000} \\
& & \mbox{} - \ket{01110} - \ket{10011} - \ket{01000} + \ket{11010}. \nonumber
\end{eqnarray}
Since multiplying by an element of the stabilizer merely rearranges the 
sum $\Sum M$, these two states are in $T$.  When these are the encoded 
$0$ and $1$, $\Xbar$ is the encoded bit flip operator $\X$ and $\Zbar$ is 
the encoded $\Z$.  This code also has the property that every possible 
error syndrome is used by the single-qubit errors.  It is therefore a {\em 
perfect} code.  There are a number of other perfect 
codes~\cite{gottesman-pasting,calderbank-GF4}, which will be discussed in 
chapter~\ref{chap-examples}.

A code encoding three qubits in eight 
qubits~\cite{gottesman-stab,calderbank-stab,steane-8qubit} appears in 
table~\ref{table-8qubit}.
\begin{table}
\centering
\begin{tabular}{c|cccccccc}
$M_1$ & $\X$ & $\X$ & $\X$ & $\X$ & $\X$ & $\X$ & $\X$ & $\X$ \\
$M_2$ & $\Z$ & $\Z$ & $\Z$ & $\Z$ & $\Z$ & $\Z$ & $\Z$ & $\Z$ \\
$M_3$ & $I$ & $\X$ & $I$ & $\X$ & $\Y$ & $\Z$ & $\Y$ & $\Z$ \\
$M_4$ & $I$ & $\X$ & $\Z$ & $\Y$ & $I$ & $\X$ & $\Z$ & $\Y$ \\
$M_5$ & $I$ & $\Y$ & $\X$ & $\Z$ & $\X$ & $\Z$ & $I$ & $\Y$ \\
\hline
\low{$\Xbar_1$} & \low{$\X$} & \low{$\X$} & \low{$I$} & \low{$I$} & \low{$I$} & 
\low{$\Z$} & \low{$I$} & \low{$\Z$} \\
\low{$\Xbar_2$} & \low{$\X$} & \low{$I$} & \low{$\X$} & \low{$\Z$} & \low{$I$} 
& \low{$I$} & \low{$\Z$} & \low{$I$} \\
\low{$\Xbar_3$} & \low{$\X$} & \low{$I$} & \low{$I$} & \low{$\Z$} & \low{$\X$} 
& \low{$\Z$} & \low{$I$} & \low{$I$} \\
\low{$\Zbar_1$} & \low{$I$} & \low{$\Z$} & \low{$I$} & \low{$\Z$} & \low{$I$} & 
\low{$\Z$} & \low{$I$} & \low{$\Z$} \\
\low{$\Zbar_2$} & \low{$I$} & \low{$I$} & \low{$\Z$} & \low{$\Z$} & \low{$I$} & \low{$I$} & \low{$\Z$} & \low{$\Z$} \\
\low{$\Zbar_3$} & \low{$I$} & \low{$I$} & \low{$I$} & \low{$I$} & \low{$\Z$} & 
\low{$\Z$} & \low{$\Z$} & \low{$\Z$}
\end{tabular}
\caption{The stabilizer for the eight-qubit code.}
\label{table-8qubit}
\end{table}
Again, $M_1$ through $M_5$ generate the stabilizer, and generate $N(S)$ with 
$\Xbar_i$ and $\Zbar_i$.  This is also a nondegenerate distance three 
code.  The codewords are
\begin{equation}
\ket{\overline{c_1 c_2 c_3}} = \Xbar_1^{c_1} \Xbar_2^{c_2} \Xbar_3^{c_3} 
\Sum_{M \in S} M \ket{00000000}.
\end{equation}
The operators $\Xbar_i$ and $\Zbar_i$ are the encoded $\X$ and $\Z$ on 
the $i$th encoded qubit.  This code is one of an infinite family of 
codes~\cite{gottesman-stab,steane-RM}, which I present in 
chapter~\ref{chap-examples}.

A particularly useful class of codes with simple stabilizers is the 
Calderbank-Shor-Steane (or {\em CSS}) class of 
codes~\cite{calderbank-CSS,steane-CSS}.  Suppose we have a classical code 
with parity check matrix $P$.  We can make a quantum code to correct just 
$\X$ errors using a stabilizer with elements corresponding to the rows of 
$P$, with a $\Z$ wherever $P$ has a $1$ and $I$'s elsewhere.  The error 
syndrome $f(E)$ for a product of $\X$ errors $E$ is then equal to the 
classical error syndrome for the same set of classical bit flip errors.  Now 
add in stabilizer generators corresponding to the parity check matrix $Q$ 
of a second classical code, only now with $\X$'s instead of $\Z$'s.  These 
generators will identify $\Z$ errors.  Together, they can also identify $\Y$ 
errors, which will have a nontrivial error syndrome for both parts.  In
general, a code formed this way will correct as many $\X$ errors as the code 
for $P$ can correct, and as many $\Z$ errors as the code for $Q$ can correct; 
a $\Y$ error counts as one of each.

We can only combine $P$ and $Q$ into a single stabilizer in the CSS form if 
the generators derived from the two codes commute.  This will be true iff the 
rows of $P$ and $Q$ are orthogonal using the binary dot product.  This 
means that the dual code of each code must be a subset of the other code.  
The minimum distance of the quantum code will be the minimum of the 
distances of $P$ and $Q$.  An example of a code of this sort is given in 
table~\ref{table-7qubit}.  It is based on the classical $[7,4,3]$ Hamming 
code, which is self-dual.
\begin{table}
\centering
\begin{tabular}{c|ccccccc}
$M_1$ & $\X$ & $\X$ & $\X$ & $\X$ & $I$ & $I$ & $I$ \\
$M_2$ & $\X$ & $\X$ & $I$ & $I$ & $\X$ & $\X$ & $I$ \\
$M_3$ & $\X$ & $I$ & $\X$ & $I$ & $\X$ & $I$ & $\X$ \\
$M_4$ & $\Z$ & $\Z$ & $\Z$ & $\Z$ & $I$ & $I$ & $I$ \\
$M_5$ & $\Z$ & $\Z$ & $I$ & $I$ & $\Z$ & $\Z$ & $I$ \\
$M_6$ & $\Z$ & $I$ & $\Z$ & $I$ & $\Z$ & $I$ & $\Z$ \\
\hline
\low{$\Xbar$} & \low{$I$} & \low{$I$} & \low{$I$} & \low{$I$} & \low{$\X$} & 
\low{$\X$} & \low{$\X$} \\
\low{$\Zbar$} & \low{$I$} & \low{$I$} & \low{$I$} & \low{$I$} & \low{$\Z$} & 
\low{$\Z$} & \low{$\Z$}
\end{tabular}
\caption{The seven-qubit CSS code.}
\label{table-7qubit}
\end{table}
For this code, the codewords are
\begin{eqnarray}
\ket{\overline{0}} & = & \ket{0000000} + \ket{1111000} + \ket{1100110} +
\ket{1010101} \nonumber \\
& & \mbox{} + \ket{0011110} + \ket{0101101} + \ket{0110011} + \ket{1001011}
\end{eqnarray}
and
\begin{eqnarray}
\ket{\overline{1}} & = & \ket{0000111} + \ket{1111111} + \ket{1100001} +
\ket{1010010} \nonumber \\
& & \mbox{} + \ket{0011001} + \ket{0101010} + \ket{0110100} + \ket{1001100}.
\end{eqnarray}
The encoded $\ket{0}$ state is the superposition of the even codewords in
the Hamming code and the encoded $\ket{1}$ state is the superposition of
the odd codewords in the Hamming code.  This behavior is characteristic
of CSS codes; in general, the various quantum codewords are superpositions
of the words in subcodes of one of the classical codes.

<!-- pdf-page: 7 -->
CSS codes are not as efficient as the most general quantum 
code, but they are easy to derive from known classical codes and their 
simple form often makes them ideal for other purposes.  For instance, the 
seven-qubit code is particularly well suited for fault-tolerant computation 
(as I will discuss in chapter~\ref{chap-fault-tolerant}).

\section{Alternate Languages for Stabilizers}
\label{sec-alternate}

There are number of possible ways of describing the stabilizer of a 
quantum code.   They each have advantages and are useful in different 
circumstances.  The description I have used so far uses the language of 
finite group theory and is particularly useful for making contact with the 
usual language of quantum mechanics.  This is the form presented in 
\cite{gottesman-stab}.

We can instead write the stabilizer using binary vector spaces, as in 
\cite{calderbank-stab}, which emphasizes connections with the classical 
theory of error-correcting codes.  To do this, we write the stabilizer as a 
pair of $(n-k) \times n$ binary matrices (or often one $(n-k) \times 2n$ 
matrix with a line separating the two halves).  The rows correspond to the 
different generators of the stabilizer and the columns correspond to 
different qubits.  One matrix has a $1$ whenever the generator has a $\X$ 
or a $\Y$ in the appropriate place, the other has a $1$ whenever the 
generator has a $\Y$ or $\Z$.  Overall phase factors get dropped.  For 
instance, the five-qubit code in this form becomes
\begin{equation}
\left( \begin{array}{ccccc|ccccc}
1 & 0 & 0 & 1 & 0 & 0 & 1 & 1 & 0 & 0 \\
0 & 1 & 0 & 0 & 1 & 0 & 0 & 1 & 1 & 0 \\
1 & 0 & 1 & 0 & 0 & 0 & 0 & 0 & 1 & 1 \\
0 & 1 & 0 & 1 & 0 & 1 & 0 & 0 & 0 & 1
\end{array} \right).
\end{equation}
Other elements of $\G$ get converted to two $n$-dimensional vectors in the 
same way.  We can convert back to the group theory formalism by writing 
down operators with a $\X$ if the left vector or matrix has a $1$, a $\Z$ if 
the right vector or matrix has a $1$, and a $\Y$ if they are both $1$.  The 
generators formed this way will never have overall phase factors, although 
other elements of the group might.  Multiplication of group elements
corresponds to addition of the corresponding binary vectors.

In the binary formalism, the condition that two operators commute with 
each other becomes the condition that the following inner product is 0:
\begin{equation}
Q(a|b, c|d) = \Sum_{i=1}^n (a_{i} d_{i} + b_{i} c_{i}) = 0,
\label{eq-commute-bin}
\end{equation}
using binary arithmetic as usual.  $a_i$, $b_i$, $c_i$, and $d_i$ are the 
$i$th components of the corresponding vectors.    Therefore the condition 
that the stabilizer be Abelian converts to the condition that the stabilizer 
matrix $(A|B)$ satisfy
\begin{equation}
\Sum_{l=1}^n (A_{il} B_{jl} + B_{il} A_{jl}) = 0.
\end{equation}
We determine the vectors in $N(S)$ by evaluating the inner product 
(\ref{eq-commute-bin}) with the rows of $(A|B)$.  To get a real code (with 
an even number of $\Y$'s), the code should also satisfy
\begin{equation}
\Sum_{l=1}^n A_{il} B_{il} = 0.
\end{equation}

Another formalism highlights connections with the classical theory of codes 
over the field GF(4) \cite{calderbank-GF4}.  This is a field of characteristic 
two containing four elements, which can be written 
$\{0, 1, \omega, \omega^2\}$.  Since the field has characteristic two, 
\begin{equation}
1 + 1 = \omega + \omega = \omega^2 + \omega^2 = 0.
\end{equation}
Also, $\omega^3 = 1$ and $1 + \omega = \omega^2$.  We can rewrite the 
generators as an $n$-dimensional ``vector'' over GF(4) by substituting $1$ 
for $\X$, $\omega$ for $\Z$, and $\omega^2$ for $\Y$.  The multiplicative 
structure of $\G$ becomes the additive structure of GF(4).  I put vector in 
quotes because the code need not have the structure of a vector space over 
GF(4).  If it does (that is, the stabilizer is closed under multiplication by 
$\omega$), the code is a {\em linear} code, which is essentially a classical 
code over GF(4).  The most general quantum code is sometimes called an {\em 
additive} code, because the stabilizer is only closed under sums of its elements.  In this formalism, the five-qubit code appears as
\begin{equation}
\left( \begin{array}{ccccc}
1 & \omega & \omega & 1 & 0 \\
0 & 1 & \omega & \omega & 1 \\
1 & 0 & 1 & \omega & \omega \\
\omega & 1 & 0 & 1 & \omega
\end{array} \right).
\end{equation}
Note that the five-qubit code is a linear quantum code.

Again, there is an additional condition for a quantum code.  Define the 
``trace'' operator by ${\rm Tr}\ \omega = {\rm Tr}\ \omega^2 = 1$, ${\rm 
Tr}\ 1 = {\rm Tr}\ 0 = 0$.  Two operators in $\G$ commute iff their images, 
the vectors $u$ and $v$ over GF(4), satisfy
\begin{equation}
{\rm Tr}\ u \cdot \overline{v} = {\rm Tr}\left( \Sum_{j=1}^n u_j 
\overline{v}_j \right) = 0,
\end{equation}
where $\overline{v}_j$ is conjugation on the $j$th component of $v$, 
switching $\omega$ and $\omega^2$, and leaving $0$ and $1$ alone.

\section{Making New Codes From Old Codes}
\label{sec-construction}

Using old codes to find new ones can simplify the task of finding codes, 
which can otherwise be quite a difficult problem.  There are a number of simple 
modifications we can make to existing codes to produce new codes with 
different parameters~\cite{gottesman-pasting,calderbank-GF4}.

One trivial change is to perform a permutation of $\X$, $\Y$, and $\Z$ on 
each qubit.  This leaves the distance and size of the code the same, 
although it may be useful for codes that can correct different numbers of 
$\X$, $\Y$, and $\Z$ errors.  A slightly less trivial manipulation is to add a 
new qubit and a new generator which is $\X$ for the new qubit.  The other 
generators are tensored with the identity on the new qubit to form the
generators of the new code.  This makes an $[n, k, d]$ code (degenerate or 
nondegenerate) into an $[n+1, k, d]$ degenerate code:  Any operator acting as 
$\Y$ or $\Z$ on the new qubit will anticommute with the new generator, and any 
operator with the form $M \otimes \Xs{(n+1)}$ will be equivalent to the 
operator $M \otimes I$.  Therefore, an operator must have at least weight $d$ 
when restricted to the first $n$ qubits to be in $N(S)-S$.

<!-- pdf-page: 8 -->
A less trivial manipulation is to remove the last qubit, converting an $[n, k, 
d]$ code into an $[n-1, k+1, d-1]$ code.  To do this, we choose the $n-k$ 
generators of $S$ so that $M_1$ ends $\X$, $M_2$ ends $\Z$, and $M_3$ 
through $M_{n-k}$ end $I$.  We can always do this when $d>1$ by picking 
the first two and then multiplying by combinations of them to make the 
others end appropriately.\footnote{If the code has been formed by adding 
a single $\X$ (or $\Y$ or $\Z$) generator, as above, we may not be able to 
do this for a given qubit, but there will always be at least one qubit for 
which we can.}  Then the new code has a stabilizer formed from the last 
$n-k-2$ generators, dropping $M_1$ and $M_2$.  Suppose we have an 
operator $A$ on the first $n-1$ qubits of weight $w$ that commutes with 
$M_3$ through $M_{n-k}$.  There are four possibilities, all of which lead to 
an operator of weight at most $w+1$ that commutes with the original 
stabilizer:
\begin{enumerate}
\item $A$ commutes with both $M_1$ and $M_2$.  
\item $A$ commutes with $M_1$, but not $M_2$.  Then $A \otimes \Xs{n}$ 
commutes with $M_1$ and $M_2$.
\item $A$ commutes with $M_2$, but not $M_1$.  Then $A \otimes \Zs{n}$ 
commutes with $M_1$ and $M_2$.
\item $A$ anticommutes with both $M_1$ and $M_2$.  Then $A \otimes 
\Ys{n}$ commutes with $M_1$ and $M_2$.
\end{enumerate}
Since the original code had distance $d$, $w$ must be at least $d-1$, 
which is therefore the distance of the new code.  The stabilizer has $n-k-2$ 
generators, so the code encodes $(n-1)-(n-k-2) = k+1$ qubits.  The new $\Xbar$
and $\Zbar$ operators are $M_1$ and $M_2$ (in either order), restricted to
the first $n-1$ qubits.  An example of this construction is to remove the
last qubit from the $[5,1,3]$ code of figure~\ref{fig-5qubit} to produce
a $[4,2,2]$ code: the generators of the new code are $M_1$ and $M_3 M_4$,
both without the last qubit.  The new stabilizer is given in figure
\ref{fig-droplast}.  Note that the $\Zbar_1$ operator is equal to
$M_3 \Zbar$ for the five-qubit code.  I have multiplied by $M_3$ so that 
$\Zbar_1$ anticommutes with $\Xbar_1$.
\begin{table}
\centering
\begin{tabular}{c|cccc}
$M_1'$ & $\X$ & $\Z$ & $\Z$ & $\X$ \\
$M_2'$ & $\Y$ & $\X$ & $\X$ & $\Y$ \\
\hline
\low{$\Xbar_1$} & \low{$\X$} & \low{$\X$} & \low{$\X$} & \low{$\X$} \\
\low{$\Xbar_2$} & \low{$\X$} & \low{$I$} & \low{$\X$} & \low{$\Z$} \\
\low{$\Zbar_1$} & \low{$\Y$} & \low{$\Z$} & \low{$\Y$} & \low{$I$} \\
\low{$\Zbar_2$} & \low{$I$} & \low{$\X$} & \low{$\Z$} & \low{$\Z$}
\end{tabular}
\caption{A $[4,2,2]$ code derived from the $[5,1,3]$ code.}
\label{fig-droplast}
\end{table}

Another way to make new codes is by {\em pasting} together old codes.  Suppose 
we have four stabilizers $R_1$, $R_2$, $S_1$, and $S_2$, with $R_1 \subset 
S_1$ and $R_2 \subset S_2$.  Let $R_1$ define an $[n_1, l_1, c_1]$ code, 
$R_2$ be an $[n_2, l_2, c_2]$ code, $S_1$ be an $[n_1, k_1, d_1]$ code, and 
$S_2$ be an $[n_2, k_2, d_2]$ code.  Then $k_i < l_i$ and $c_i \leq d_i$.  We 
require $l_1-k_1 = l_2-k_2$ and for $S_1$ and $S_2$ to be 
nondegenerate.\footnote{We can actually allow $S_1$ and $S_2$ to be degenerate, 
as long as all the degenerate operators are confined to $R_1$ and $R_2$}  Let 
generators of $R_1$ be $\{M_1, \ldots, M_{n_1 - l_1}\}$, the generators of 
$S_1$ be $\{M_1, \ldots, M_{n_1-k_1}\}$, the generators of $R_2$ be $\{N_1, 
\ldots, N_{n_2-l_2}\}$, and the generators of $S_2$ be $\{N_1, \ldots, 
N_{n_2-k_2}\}$.  We form a new stabilizer $S$ on $n_1 + n_2$ qubits generated 
by 
\begin{eqnarray}
& & \{M_1 \otimes I, \ldots, M_{n_1-l_1} \otimes I, I \otimes N_1, \ldots, 
I \otimes N_{n_2-l_2}, \nonumber \\
& & \quad M_{n_1-l_1+1} \otimes N_{n_2-l_2+1}, \ldots,
M_{n_1-k_1} \otimes N_{n_2-k_2} \}.
\end{eqnarray}
The code has $(n_1-l_1) + (n_2-l_2) + (l_i-k_i)$ generators, and therefore 
encodes $l_1+k_2 = l_2+k_1$ qubits.  For instance, if $S_1$ is the eight-qubit 
code and $S_2$ is the five-qubit code, with $R_1$ generated by $\X \X \X \X 
\X \X \X \X$ and $\Z \Z \Z \Z \Z \Z \Z \Z$ and $R_2$ generated by $\X \Z 
\Z \X I$, we can make the $[13,7,3]$ code given in 
table~\ref{table-13qubit}.
\begin{table}
\centering
\begin{tabular}{c|cccccccc|ccccc}
$M_1$ & $\X$ & $\X$ & $\X$ & $\X$ & $\X$ & $\X$ & $\X$ & $\X$ & $I$ 
& $I$ & $I$ & $I$ & $I$ \\
$M_2$ & $\Z$ & $\Z$ & $\Z$ & $\Z$ & $\Z$ & $\Z$ & $\Z$ & $\Z$ & $I$ & 
$I$ & $I$ & $I$ & $I$ \\
\hline
$M_3$ & $I$ & $I$ & $I$ & $I$ & $I$ & $I$ & $I$ & $I$ & $\X$ & $\Z$ & 
$\Z$ & $\X$ & $I$ \\
\hline
$M_4$ & $I$ & $\X$ & $I$ & $\X$ & $\Y$ & $\Z$ & $\Y$ & $\Z$ & $I$ & 
$\X$ & $\Z$ & $\Z$ & $\X$ \\
$M_5$ & $I$ & $\X$ & $\Z$ & $\Y$ & $I$ & $\X$ & $\Z$ & $\Y$ & $\X$ & 
$I$ & $\X$ & $\Z$ & $\Z$ \\
$M_6$ & $I$ & $\Y$ & $\X$ & $\Z$ & $\X$ & $\Z$ & $I$ & $\Y$ & $\Z$ & 
$\X$ & $I$ & $\X$ & $\Z$
\end{tabular}
\caption{The thirteen-qubit code formed by pasting together the five- and 
eight-qubit codes.}
\label{table-13qubit}
\end{table}

In general, the distance of the new code will be ${\rm min}\{d_1, d_2, c_1 
+ c_2 \}$.  This is because an operator acting on just the first $n_1$ qubits 
can only commute with $S$ if it commutes with $S_1$, an operator acting 
on the last $n_2$ qubits can only commute with $S$ if it commutes with 
$S_2$, and an operator acting on both parts must commute with both $R_1 
\otimes I$ and $I \otimes R_2$.

Another very useful way of producing new codes is to {\em concatenate} 
two codes to produce a code of greater total distance.  Suppose we have an 
$[n_1, k, d_1]$ code (stabilizer $S_1$) and we encode each of its $n_1$ 
qubits again using an $[n_2, 1, d_2]$ code (stabilizer $S_2$).  The result is 
an $[n_1 n_2, k, d_1 d_2]$ code.  Its stabilizer $S$ is $n_1$ copies of $S_2$, 
acting on the physical qubits in blocks of size $n_2$, plus an additional 
$n_1 - k$ generators corresponding to the generators of $S_1$.  However, these 
generators are encoded to act on the second code.  That is, a $\X$ acting 
on the first code must be replaced by an $\Xbar$ for the second code.  For 
instance, the code resulting from concatenating the five-qubit code with itself 
has the stabilizer given in table~\ref{table-25qubit}.
\begin{table}
{\setlength{\tabcolsep}{0.1em}
\begin{tabular}{c|ccccc|ccccc|ccccc|ccccc|ccccc}
$M_1$ & $\X$ & $\Z$ & $\Z$ & $\X$ & $I$ & $I$ & $I$ & $I$ & $I$ & $I$ & 
$I$ & $I$ & $I$ & $I$ & $I$ & $I$ & $I$ & $I$ & $I$ & $I$ & $I$ & $I$ & 
$I$ & $I$ & $I$ \\
$M_2$ & $I$ & $\X$ & $\Z$ & $\Z$ & $\X$ & $I$ & $I$ & $I$ & $I$ & $I$ & 
$I$ & $I$ & $I$ & $I$ & $I$ & $I$ & $I$ & $I$ & $I$ & $I$ & $I$ & $I$ & 
$I$ & $I$ & $I$ \\
$M_3$ & $\X$ & $I$ & $\X$ & $\Z$ & $\Z$ & $I$ & $I$ & $I$ & $I$ & $I$ & 
$I$ & $I$ & $I$ & $I$ & $I$ & $I$ & $I$ & $I$ & $I$ & $I$ & $I$ & $I$ & 
$I$ & $I$ & $I$ \\
$M_4$ & $\Z$ & $\X$ & $I$ & $\X$ & $\Z$ & $I$ & $I$ & $I$ & $I$ & $I$ & 
$I$ & $I$ & $I$ & $I$ & $I$ & $I$ & $I$ & $I$ & $I$ & $I$ & $I$ & $I$ & 
$I$ & $I$ & $I$ \\
$M_5$ & $I$ & $I$ & $I$ & $I$ & $I$ & $\X$ & $\Z$ & $\Z$ & $\X$ & $I$ & 
$I$ & $I$ & $I$ & $I$ & $I$ & $I$ & $I$ & $I$ & $I$ & $I$ & $I$ & $I$ & 
$I$ & $I$ & $I$ \\
$M_6$ & $I$ & $I$ & $I$ & $I$ & $I$ & $I$ & $\X$ & $\Z$ & $\Z$ & $\X$ & 
$I$ & $I$ & $I$ & $I$ & $I$ & $I$ & $I$ & $I$ & $I$ & $I$ & $I$ & $I$ & 
$I$ & $I$ & $I$ \\
$M_7$ & $I$ & $I$ & $I$ & $I$ & $I$ & $\X$ & $I$ & $\X$ & $\Z$ & $\Z$ & 
$I$ & $I$ & $I$ & $I$ & $I$ & $I$ & $I$ & $I$ & $I$ & $I$ & $I$ & $I$ & 
$I$ & $I$ & $I$ \\
$M_8$ & $I$ & $I$ & $I$ & $I$ & $I$ & $\Z$ & $\X$ & $I$ & $\X$ & $\Z$ & 
$I$ & $I$ & $I$ & $I$ & $I$ & $I$ & $I$ & $I$ & $I$ & $I$ & $I$ & $I$ & 
$I$ & $I$ & $I$ \\
$M_9$ & $I$ & $I$ & $I$ & $I$ & $I$ & $I$ & $I$ & $I$ & $I$ & $I$ & $\X$ 
& $\Z$ & $\Z$ & $\X$ & $I$ & $I$ & $I$ & $I$ & $I$ & $I$ & $I$ & $I$ & 
$I$ & $I$ & $I$ \\
$M_{10}$ & $I$ & $I$ & $I$ & $I$ & $I$ & $I$ & $I$ & $I$ & $I$ & $I$ & $I$ 
& $\X$ & $\Z$ & $\Z$ & $\X$ & $I$ & $I$ & $I$ & $I$ & $I$ & $I$ & $I$ & 
$I$ & $I$ & $I$ \\
$M_{11}$ & $I$ & $I$ & $I$ & $I$ & $I$ & $I$ & $I$ & $I$ & $I$ & $I$ & 
$\X$ & $I$ & $\X$ & $\Z$ & $\Z$ & $I$ & $I$ & $I$ & $I$ & $I$ & $I$ & 
$I$ & $I$ & $I$ & $I$ \\
$M_{12}$ & $I$ & $I$ & $I$ & $I$ & $I$ & $I$ & $I$ & $I$ & $I$ & $I$ & 
$\Z$ & $\X$ & $I$ & $\X$ & $\Z$ & $I$ & $I$ & $I$ & $I$ & $I$ & $I$ & 
$I$ & $I$ & $I$ & $I$ \\
$M_{13}$ & $I$ & $I$ & $I$ & $I$ & $I$ & $I$ & $I$ & $I$ & $I$ & $I$ & $I$ 
& $I$ & $I$ & $I$ & $I$ & $\X$ & $\Z$ & $\Z$ & $\X$ & $I$ & $I$ & $I$ & 
$I$ & $I$ & $I$ \\
$M_{14}$ & $I$ & $I$ & $I$ & $I$ & $I$ & $I$ & $I$ & $I$ & $I$ & $I$ & $I$ 
& $I$ & $I$ & $I$ & $I$ & $I$ & $\X$ & $\Z$ & $\Z$ & $\X$ & $I$ & $I$ & 
$I$ & $I$ & $I$ \\
$M_{15}$ & $I$ & $I$ & $I$ & $I$ & $I$ & $I$ & $I$ & $I$ & $I$ & $I$ & $I$ 
& $I$ & $I$ & $I$ & $I$ & $\X$ & $I$ & $\X$ & $\Z$ & $\Z$ & $I$ & $I$ & 
$I$ & $I$ & $I$ \\
$M_{16}$ & $I$ & $I$ & $I$ & $I$ & $I$ & $I$ & $I$ & $I$ & $I$ & $I$ & $I$ 
& $I$ & $I$ & $I$ & $I$ & $\Z$ & $\X$ & $I$ & $\X$ & $\Z$ & $I$ & $I$ & 
$I$ & $I$ & $I$ \\
$M_{17}$ & $I$ & $I$ & $I$ & $I$ & $I$ & $I$ & $I$ & $I$ & $I$ & $I$ & $I$ 
& $I$ & $I$ & $I$ & $I$ & $I$ & $I$ & $I$ & $I$ & $I$ & $\X$ & $\Z$ & 
$\Z$ & $\X$ & $I$ \\
$M_{18}$ & $I$ & $I$ & $I$ & $I$ & $I$ & $I$ & $I$ & $I$ & $I$ & $I$ & $I$ 
& $I$ & $I$ & $I$ & $I$ & $I$ & $I$ & $I$ & $I$ & $I$ & $I$ & $\X$ & $\Z$ 
& $\Z$ & $\X$ \\
$M_{19}$ & $I$ & $I$ & $I$ & $I$ & $I$ & $I$ & $I$ & $I$ & $I$ & $I$ & $I$ 
& $I$ & $I$ & $I$ & $I$ & $I$ & $I$ & $I$ & $I$ & $I$ & $\X$ & $I$ & 
$\X$ & $\Z$ & $\Z$ \\
$M_{20}$ & $I$ & $I$ & $I$ & $I$ & $I$ & $I$ & $I$ & $I$ & $I$ & $I$ & $I$ 
& $I$ & $I$ & $I$ & $I$ & $I$ & $I$ & $I$ & $I$ & $I$ & $\Z$ & $\X$ & $I$ 
& $\X$ & $\Z$ \\
$M_{21}$ & $\X$ & $\X$ & $\X$ & $\X$ & $\X$ & $\Z$ & $\Z$ & $\Z$ & $\Z$ 
& $\Z$ & $\Z$ & $\Z$ & $\Z$ & $\Z$ & $\Z$ & $\X$ & $\X$ & $\X$ & $\X$ & 
$\X$ & $I$ & $I$ & $I$ & $I$ & $I$ \\
$M_{22}$ & $I$ & $I$ & $I$ & $I$ & $I$ & $\X$ & $\X$ & $\X$ & $\X$ & 
$\X$ & $\Z$ & $\Z$ & $\Z$ & $\Z$ & $\Z$ & $\Z$ & $\Z$ & $\Z$ & $\Z$ & 
$\Z$ & $\X$ & $\X$ & $\X$ & $\X$ & $\X$ \\
$M_{23}$ & $\X$ & $\X$ & $\X$ & $\X$ & $\X$ & $I$ & $I$ & $I$ & $I$ & 
$I$ & $\X$ & $\X$ & $\X$ & $\X$ & $\X$ & $\Z$ & $\Z$ & $\Z$ & $\Z$ & 
$\Z$ & $\Z$ & $\Z$ & $\Z$ & $\Z$ & $\Z$ \\
$M_{24}$ & $\Z$ & $\Z$ & $\Z$ & $\Z$ & $\Z$ & $\X$ & $\X$ & $\X$ & $\X$ 
& $\X$ & $I$ & $I$ & $I$ & $I$ & $I$ & $\X$ & $\X$ & $\X$ & $\X$ & $\X$ 
& $\Z$ & $\Z$ & $\Z$ & $\Z$ & $\Z$
\end{tabular}
\caption{Result of concatenating the five-qubit code with itself.}
\label{table-25qubit}}
\end{table}
The concatenated code has distance $d_1 d_2$ because operators in $N(S) - 
S$ must have distance at least $d_2$ on at least $d_1$ blocks of $n_2$ 
qubits, so have weight at least $d_1 d_2$.  Note that it is not strictly 
necessary to use the same code to encode each qubit of $S_1$.

<!-- pdf-page: 9 -->
There are two possible ways to concatenate when $S_2$ encodes multiple 
qubits.  Suppose $S_1$ is an $[n_1, k_1, d_1]$ code and $S_2$ is an $[n_2, 
k_2, d_2]$ code.  Further, suppose $n_1$ is a multiple of $k_2$.  Then we 
can encode blocks of $S_1$ of size $k_2$ using $S_2$.  This will result in a 
code using $n_1 n_2/k_2$ qubits to encode $k_1$ qubits.  It still takes an 
operator of distance at least $d_2$ to cause an error on an $n_2$-qubit 
block, but such an error can cause up to $k_2$ errors on $S_1$, so the 
resulting code need only have distance $\lceil d_1/k_2 \rceil d_2$.  
However, the $k_2$ errors that result are not a general set of $k_2$ errors, 
so the code may actually be better.  Suppose $S_1$ has distance $d_1'$ 
($d_1' \geq \lceil d_1/k_2 \rceil$) for blocks of $k_2$ errors, i.e., $d_1'$ 
such blocks must have errors before the code fails.  Then the concatenated 
code has distance $d_1' d_2$.

Another way to concatenate codes encoding multiple qubits is to add 
additional blocks of $S_1$ to fill the spaces in $S_2$.  That is, we actually 
encode $k_2$ copies of $S_1$, encoding the $i$th qubit of each copy in the 
same $S_2$ block.  This produces an $[n_1 n_2, k_1 k_2, d_1 d_2]$ code, 
since any failure of an $S_2$ block only produces one error in each $S_1$ 
block.

\section{Higher Dimensional States}
\label{sec-qudits}

So far, we have only considered systems for which the Hilbert space is the
tensor product of two-state systems.  However, it may turn out that a good
physical implementation of quantum computation uses three- or four-level
atoms, or spin-one particles, or some other system where it makes more sense
to consider it as the tensor product of $d$-dimensional systems, where
$d > 2$.  I will call the fundamental unit of such a system a {\em qudit}.
In such a case, we will want to consider error correcting codes where a
single qudit error can occur with reasonable probability.  For these systems,
the stabilizer code formalism needs to be modified to deal with the extra
dimensions.

Fundamental to the success of the stabilizer formalism was the use of the
Pauli spin matrix basis for possible errors.  The algebraic properties of
this basis allowed a straightforward characterization of errors depending
on whether they commuted or anticommuted with elements of an Abelian group.
Knill~\cite{knill-qudit} has codified the properties necessary for this 
construction to generalize to $d$-dimensional spaces.  Suppose we have a
set of $d^2$ unitary operators $E_1, \ldots, E_{n^2}$ (including the 
identity) acting on a single qudit such that the $E_i$'s form a basis for all
possible $d \times d$ complex matrices.  If $E_i E_j = w_{ij} E_{i*j}$ for all 
$i, j$ (where $*$ is some binary group operation), then the $E_i$'s are said to 
form a {\em nice} error basis.  The values $w_{ij}$ will then have modulus one. 
Given a nice error basis, we form the group $\G_n$ for this basis as the tensor
product of $n$ copies of the error basis, with possible overall phases
generated by the $w_{ij}$'s.  Then an Abelian subgroup $S$ of $\G_n$ that does
not contain any nontrivial phase times the identity will have a nontrivial
set $T$ of states in the Hilbert space in the $+1$ eigenspace of every operator
in $S$.  The code $T$ can detect any error $E$ for which $E M = c M E$ for some
$M \in \G_n$ and some $c \neq 1$.

One interesting complication of codes over $d$-dimensional spaces is that
when $S$ has $n-k$ generators, $T$ need not encode $k$ qudits.  This can
only occur when $d$ is composite and the order of a generator of $S$ is
a nontrivial factor of $d$.  It is still true that if $S$ has $r$ elements,
then $T$ will be $(d^n/r)$-dimensional.  If all the generators of $S$ have
order $d$, $T$ does encode $k$ qudits.

One particularly convenient error basis for any $d$ is generated by
$D_\omega$ and $C_n$, where $(D_\omega)_{ij} = \delta_{ij} \omega^i$ and
$(C_n)_{ij} = \delta_{j, (i+1 \bmod n)}$.  $\omega$ is a primitive $n$th
root of unity.  For $d=2$, this just reduces to the usual Pauli basis,
since $C_2 = \X$ and $D_{-1} = \Z$.  For higher $d$, $D_\omega$ maps
$\ket{i} \rightarrow \omega^i \ket{i}$ and $C_n$ adds one modulo $n$.
This is a nice error basis, with
\begin{equation}
C_n D_\omega = \omega D_\omega C_n.
\end{equation}
The elements of the basis can be written $C_n^a D_\omega^b$, and 
\begin{equation}
\left( C_n^a D_\omega^b \right) \left( C_n^c D_\omega^d \right) =
\omega^{ad-bc} \left( C_n^c D_\omega^d \right) \left( C_n^a D_\omega^b \right).
\end{equation}

Codes for higher-dimensional systems have not been as extensively studied as
those for two-dimensional systems, but some constructions are given in
\cite{knill-qudit, chau-d^2, chau-5qudit, aharonov, rains-orthogonal}.

<!-- pdf-page: 10 -->
\chapter{Bounds on Quantum Error-Correcting Codes}
\label{chap-bounds}
\markright{CHAPTER~\ref{chap-bounds}. \ BOUNDS ON QUANTUM CODES}

\section{General Bounds}
\label{sec-gen-bounds}
\pagestyle{headings}

The question of how efficient an error-correcting code of a given block size 
can be made in terms of both encoded qubits and distance is an interesting 
and important question in the theories of both classical and quantum error 
correction.  In the classical theory, only upper and lower bounds exist on 
the efficiency of codes that must have a given minimum distance between 
all codewords.  The true, achievable bounds on such codes are unknown.  
Better understood in the classical case is the asymptotic efficiency of coding 
(where we only require that the code correct all likely errors).  In the limit 
of infinite bits sent, we usually require the code to correct measure one of 
the errors occuring using some probability measure associated with the channel. 
Classically, Shannon's theorem tells us what the achievable capacity of a 
channel is.  No real quantum analogue of Shannon's theorem is known, despite
extensive work on the subject~\cite{lloyd, schumacher, barnum}.

One simple upper bound on the efficiency of quantum codes is the 
quantum Hamming bound~\cite{ekert}.  For a nondegenerate code with 
basis codewords $\ket{\psi_i}$ and possible errors $E_a$, all of the states 
$E_a \ket{\psi_i}$ are linearly independent for all $a$ and $i$.  If the code 
uses $n$ qubits, there can only be $2^n$ linearly indepedent vectors in the 
Hilbert space, so the number of errors times the number of codewords 
must be less than or equal to $2^n$.  If the code corrects all errors of 
weight $t$ or less and encodes $k$ qubits, this means
\begin{equation}
\Sum_{j=0}^{t} 3^j \pmatrix{n \cr j} 2^k \leq 2^n.
\label{eq-QHB-finite}
\end{equation}
There are \mbox{\tiny $\pmatrix{n \cr j}$} ways to choose $j$ qubits to be 
affected by $j$ errors and $3^j$ ways these errors can be tensor products of 
$\X$, $\Y$, and $\Z$.  This bound is completely analogous to the classical 
Hamming bound, with two differences: the quantum bound has a factor of $3^j$ 
reflecting the additional quantum-mechanical degrees of freedom; and the 
quantum bound only applies to nondegenerate codes.  The distinction 
between degenerate and nondegenerate codes is a purely
quantum-mechanical distinction; there are no classical degenerate codes.  
It is unknown whether there are any degenerate codes that exceed the 
quantum Hamming bound (\ref{eq-QHB-finite}).

If we let the block size $n$ grow arbitrarily large, we should also increase 
the expected number of errors.  Consider the depolarizing channel, which is 
equally likely to have $\X$, $\Y$, and $\Z$ errors.  Suppose there is a 
probability $p$ of having one of these errors on a given qubit and $1-p$ of 
having no error.  The expected number of errors on a block of size $n$ is $t 
= np$.  The number of likely errors will be about the number of errors of 
length $t$, so the quantum Hamming bound becomes
\begin{equation}
3^{np} \pmatrix{n \cr np} 2^k \leq 2^n.
\end{equation}
Taking the logarithm and rearranging gives us
\begin{equation}
\frac{k}{n} \leq 1 - p \log_2 3 - H(p).
\label{eq-QHB}
\end{equation}
Again, $H(x) = - x \log_2 x - (1 - x) \log_2 (1-x)$, as with the asymptotic 
form of the classical Hamming bound (\ref{eq-Hamming}).  As with the 
classical case, we can achieve the quantum Hamming bound by using 
random codes.  Unlike the classical case, this is not always the most 
efficient use of the channel, so (\ref{eq-QHB}) does not give the actual 
channel capacity of the quantum channel.  I will discuss this question in 
greater detail in section~\ref{depolarizing}.

For minimum distance codes, it is not in general possible to achieve the 
quantum Hamming bound.  We can set a lower bound, the quantum 
Gilbert-Varshamov bound.  Recall that
\begin{equation}
\bra{\psi_i} E_a^\dagger E_b \ket{\psi_j} = C_{ab} \delta_{ij}
\end{equation}
for a quantum code correcting errors $\{E_a\}$ with basis states 
$\ket{\psi_i}$.  The matrix $C_{ab}$ is Hermitian, but is further 
constrained by the algebraic relationships of the operators $E_a^\dagger 
E_b$.  It is better to consider $C_{ab}$ as a function of operators $O = 
E_a^\dagger E_b$.  When the possible errors are all operators of up to 
weight $t$, $O$ can be any operator of weight $\leq 2t$.  Slightly more 
generally, for a code of distance $d$, $O$ is any operator of weight less 
than $d$.  Therefore, the statement
\begin{equation}
\bra{\psi} E_a^\dagger E_b \ket{\psi} = C_{ab}
\label{eq-Cab}
\end{equation}
is actually 
\begin{equation}
N = \Sum_{j=0}^{d-1} 3^j \pmatrix{n \cr j}
\end{equation}
constraints on the state $\ket{\psi}$.  For generic $C_{ab}$ (satisfying the 
appropriate algebraic constraints) and generic linear subspace $V$ with 
dimension larger than $N$, there will be states $\ket{\psi}$ satisfying 
equation (\ref{eq-Cab}).

Suppose we choose generic $C_{ab}$ and a generic state $\ket{\psi_1}$ 
satisfying (\ref{eq-Cab}).  Now restrict attention to the subspace 
orthogonal to $\ket{\psi_1}$ and to all $O \ket{\psi_1}$ for operators $O$ of 
weight less than $d$.  For an $n$-qubit Hilbert space, this subspace has 
dimension $2^n - N$.  Choose a generic state $\ket{\psi_2}$ in this subspace 
satisfying (\ref{eq-Cab}).  Now restrict attention to the subspace 
orthogonal to both $O \ket{\psi_1}$ and $O \ket{\psi_2}$.  We can again 
pick $\ket{\psi_3}$ in this subspace satisfying (\ref{eq-Cab}), and so on.  
Choose $\ket{\psi_i}$ orthogonal to all $O \ket{\psi_j}$ ($j \leq i-1$) and 
satisfying (\ref{eq-Cab}).  We can continue doing this as long as
\begin{equation}
\Sum_{j=0}^{d-1} 3^j \pmatrix{n \cr j} i < 2^n.
\end{equation}
Therefore, we can always find a distance $d$ quantum code encoding $k$ 
qubits in $n$ qubits satisfying
\begin{equation}
\Sum_{j=0}^{d-1} 3^j \pmatrix{n \cr j} 2^k \geq 2^n.
\label{eq-QGV}
\end{equation}
This is the quantum Gilbert-Varshamov bound.  In the limit where $t = pn 
= d/2$, with $n$ large, this becomes
\begin{equation}
\frac{k}{n} \geq 1 - 2p \log_2 3 - H(2p).
\end{equation}

<!-- pdf-page: 11 -->
The quantum Hamming bound only limits the efficiency of nondegenerate 
codes.  For degenerate codes, we can still set a bound, but it will not be as 
restrictive.  For an $[n, k, d]$ code, we can choose any $d-1$ qubits and 
remove them.  The remaining $n-d+1$ qubits must contain enough 
information to reconstruct not only the $2^k$ possible codewords, but the state 
of the missing qubits as well.  Because the missing qubits can be any 
qubits, we can choose them to have maximum entropy.  Then
\begin{eqnarray}
n-d+1 & \geq & d-1+k \\
n & \geq & 2(d-1) + k.
\end{eqnarray}
This is the Knill-Laflamme bound~\cite{knill-laflamme-theory,cerf-cleve}. 
It is a quantum analog of the classical Singleton bound. 
A code to correct $t$ errors must have distance $d=2t+1$, so for such a 
code, $n \geq 4t + k$.  This bound holds for any code with a given 
minimum distance, whether it is degenerate or nondegenerate.  For 
instance, this bound demonstrates that the smallest one-error-correcting 
quantum code uses five qubits.

\section{Weight Enumerators and Linear Programming Bounds}
\label{sec-enumerators}

In the classical theory of error-correcting codes, the distribution of 
codeword weights contains a great deal of information about the code.  
This distribution is often encoded in the coefficients of a polynomial, and 
algebraic relationships between these polynomials, known as {\em weight 
enumerators}, can be very useful for setting bounds on classical codes.  
Many of the same ideas can be adapted for use with quantum 
error-correcting codes~\cite{rains-shadow, shor-laflamme-QMW, 
rains-enumerators, rains-poly-invariants}.

Let $A_d$ be the number of elements of the stabilizer $S$ with weight $d$, 
and let $B_d$ be the number of elements of $N(S)$ with weight $d$ (ignoring
overall phases).  Note that $B_d \geq A_d \geq 0$.  Define polynomials
\begin{eqnarray}
A (z) & = & \Sum_{d=0}^{n} A_d z^d \\
B (z) & = & \Sum_{d=0}^{n} B_d z^d.
\end{eqnarray}
$A_0 = B_0 = 1$ always.  For a code of distance $d$, $B_{d'} = A_{d'}$ for 
all $d' < d$.  For a nondegenerate code, $B_{d'} = A_{d'} = 0$ for $d' < d$.  A 
degenerate code has $B_{d'} = A_{d'} > 0$ for at least one $d' < d$.  $A(z)$ 
and $B(z)$ are the weight enumerators of $S$ and $N(S)$.

The polynomials $A(z)$ and $B(z)$ satisfy the quantum MacWilliams 
identity \cite{shor-laflamme-QMW}:
\begin{equation}
B(z) = \frac{1}{2^{n-k}} (1+3z)^n A \left( \frac{1-z}{1+3z} \right).
\label{eq-QMW}
\end{equation}
In other words,
\begin{equation}
\Sum_{d=0}^{n} B_d z^d = \frac{1}{2^{n-k}} \Sum_{d=0}^{n} A_d (1-z)^d 
(1+3z)^{n-d}.
\end{equation}
Matching coefficients of $z^d$, we find
\begin{equation}
B_d = \frac{1}{2^{n-k}} \Sum_{d'=0}^{n} \left[ \Sum_{s=0}^{d} (-1)^s 3^{d-s} 
\pmatrix{d' \cr s} \pmatrix{n-d' \cr d-s} \right] A_{d'}.
\end{equation}

To prove this, note that an operator $E \in \G$ of weight $d$ will either 
commute with every operator $M \in S$ or it will commute with exactly 
half of the operators in $S$.  Therefore, if we sum
\begin{equation}
\Sum_{M \in S} (-1)^{f_M (E)},
\end{equation}
we will get zero if $E \notin N(S)$ and $2^{n-k}$ if $E \in N(S)$ (recall that 
$f_M (E)$ is $0$ if $M$ and $E$ commute and $1$ if they do not).  
Therefore, we can write $B_d$ as follows:
\begin{equation}
B_d = \frac{1}{2^{n-k}} \Sum_{E} \Sum_{M \in S} (-1)^{f_M (E)},
\end{equation}
where the sum over $E$ is taken over all $E \in \G$ of weight $d$.  We 
reverse the order of summation and break up the sum over $M$ to the 
sum over $d'$ and the sum over $M \in S$ of weight $d'$ to get
\begin{equation}
B_d = \frac{1}{2^{n-k}} \Sum_{d'=0}^{n} \Sum_M \Sum_E (-1)^{f_M (E)}.
\end{equation}
Now, any given $M$ and $E$ will both act nontrivially on some set of $s$ 
qubits.  Of those $s$, they will act as different Pauli matrices on $t$ qubits 
and as the same Pauli matrix on $s-t$ qubits.  Now,
\begin{equation}
(-1)^{f_M (E)} = (-1)^t.
\end{equation}
The number of operators $E$ that agree with $M$ on $s-t$ qubits and 
disagree on $t$ qubits is
\begin{equation}
1^{s-t} 2^t 3^{d-s} \pmatrix{s \cr t} \pmatrix{d' \cr s} \pmatrix{n-d' \cr d-
s}.
\end{equation}
Note that this does not depend on $M$.  Thus,
\begin{eqnarray}
B_d & \!\! = & \!\! \frac{1}{2^{n-k}} \Sum_{d'=0}^{n} \Sum_M \Sum_{s=0}^{d} 
\Sum_{t=0}^{s} \left[1^{s-t} (-2)^t \pmatrix{s \cr t}\right] 3^{d-s} 
\pmatrix{d' \cr s} \pmatrix{n-d' \cr d-s} \\
& \!\! = & \!\! \frac{1}{2^{n-k}} \Sum_{d'=0}^{n} \Sum_M \Sum_{s=0}^{d} (1 - 
2)^s 3^{d-s} \pmatrix{d' \cr s} \pmatrix{n-d' \cr d-s} \\
& \!\! = & \!\! \frac{1}{2^{n-k}} \Sum_{d'=0}^{n} \Sum_M \Sum_{s=0}^{d} (-1)^s 
3^{d-s} \pmatrix{d' \cr s} \pmatrix{n-d' \cr d-s} \\
& \!\! = & \!\! \frac{1}{2^{n-k}} \Sum_{d'=0}^{n} \left[ \Sum_{s=0}^{d} (-1)^s 
3^{d-s} \pmatrix{d' \cr s} \pmatrix{n-d' \cr d-s} \right] A_{d'}.
\end{eqnarray}

This proves the quantum MacWilliams identity (\ref{eq-QMW}) for 
stabilizer codes.  The coefficients $A_d$ and $B_d$ can also be defined 
for non-stabilizer codes, and equation (\ref{eq-QMW}) will still hold, so 
any bounds derived strictly from the quantum MacWilliams identity will 
hold for any quantum code, not just stabilizer codes.  For any code of 
distance $d$, the coefficients $A_d$ and $B_d$ satisfy the additional 
constraints
\begin{eqnarray}
B_0 & = & A_0 = 1 \\
B_{d'} & = & A_{d'}\ (d' < d) \\
B_{d'} & \geq & A_{d'} \geq 0\ (\forall\,d').
\end{eqnarray}
For a nondegenerate code, $A_{d'} = B_{d'} = 0$ for $d' < d$.  These 
constraints along with equation (\ref{eq-QMW}) restrict the allowed values 
of $A_d$ and $B_d$.  The constraints are all linear, so standard linear 
programming techniques will find solutions.  If there are no possible 
integer values of $A_d$ and $B_d$ satisfying all of the constraints, there is 
no $[n, k, d]$ code.  Otherwise, the possible solutions will give us 
parameters of possible codes.  For instance, applying the constraints for a 
$[5, 1, 3]$ code produces the unique solution $A_i = (1, 0, 0, 0, 15, 0)$ and 
$B_i = (1, 0, 0, 30, 15, 18)$~\cite{shor-laflamme-QMW}.  Therefore, the 
usual five-qubit code is essentially the only $[5,1,3]$ code.  There are thus 
no degenerate five-qubit codes.

<!-- pdf-page: 12 -->
Even tighter linear programming bounds than those produced by the 
quantum MacWilliams identity are possible.  This can be done using the 
quantum shadow enumerator~\cite{rains-shadow}.  The {\em shadow} $Sh(S)$ of 
a code $S$ is defined as the set of $E \in \G$ satisfying
\begin{equation}
f_M (E) \equiv {\rm wt} (M) \pmod{2}
\end{equation}
for all $M \in S$ (where ${\rm wt} (M)$ is the weight of $M$).  Define 
$S_d$ to be the number of elements of $Sh(S)$ of weight $d$ (again, ignoring
overall phases), and
\begin{equation}
S (z) = \Sum_{d=0}^{n} S_d z^d.
\end{equation}
$S(z)$ is the {\em shadow enumerator} of $S$.  Then
\begin{equation}
S(z) = \frac{1}{2^{n-k}} (1+3z)^n A \left( \frac{z-1}{1+3z} \right).
\label{eq-shadow}
\end{equation}

If $S$ contains only operators of even weight, then $E \in Sh(S)$ iff $f_M (E) 
= 0$ for all $M \in S$, so $Sh(S) = N(S)$, and $S_d = B_d$.  Furthermore, in 
this case, $A(z)$ is an even function, so
\begin{eqnarray}
S(z) & = & B(z) = \frac{1}{2^{n-k}} (1+3z)^n A \left( \frac{1-z}{1+3z} \right) 
\\
& = & \frac{1}{2^{n-k}} (1+3z)^n A \left( \frac{z-1}{1+3z} \right).
\end{eqnarray}

If $S$ contains an element of odd weight, consider the subset $S' \subset 
S$ of even weight operators.  Then $S'$ has exactly $2^{n-k-1}$ elements.  
This is true because in order for $M, M' \in S$ to commute, they must overlap
and disagree only on an even number of qubits.  Thus, ${\rm wt}(MM') \equiv
{\rm wt}(M) + {\rm wt}(M') \pmod{2}$.
The shadow of $S$ is just $Sh(S) = N(S') - N(S)$.  Let $B'(z)$ and $A'(z)$ be 
the weight enumerators of $S'$ and $N(S')$.  Then
\begin{eqnarray}
S(z) & = & B' (z) - B(z) \\
& = & \frac{1}{2^{n-k-1}} (1+3z)^n A' \left( \frac{1-z}{1+3z} \right) - 
\frac{1}{2^{n-k}} (1+3z)^n A \left( \frac{1-z}{1+3z} \right) \nonumber \\ \\
& = & \frac{1}{2^{n-k}} (1+3z)^n \left[ 2 A' \left( \frac{1-z}{1+3z} \right) - 
A \left( \frac{1-z}{1+3z} \right) \right].
\end{eqnarray}
Now, $A'_d = A_d$ for even $d$ and $A'_d = 0$ for odd $d$, so $A(z) + A(-
z) = 2 A'(z)$, and
\begin{equation}
S(z) = \frac{1}{2^{n-k}} (1+3z)^n A \left( \frac{z-1}{1+3z} \right).
\end{equation}

Again, the shadow enumerator can be defined for non-stabilizer codes and 
satisfies the same relationship with $A(z)$ as for stabilizer codes.  In both 
the stabilizer and non-stabilizer case, $S_d \geq 0$.  Along with 
(\ref{eq-shadow}), this provides additional constraints for the linear 
programming bound restricting the parameters of any code.  These bounds 
have been applied to all possible codes with $n \leq 30$
\cite{rains-shadow,calderbank-GF4}.  Among other things, they show that 
the smallest possible distance five code is an $[11,1,5]$ code and that 
degenerate codes in this region all fall below the quantum Hamming 
bound.  The shadow enumerator can also be used to show that any nondegenerate
code on $n$ qubits can correct at most $\lfloor \frac{n+1}{6} \rfloor$
errors~\cite{rains-shadow}.

\section{Bounds on Degenerate Stabilizer Codes}

It is still unknown whether there are any degenerate codes that exceed the 
limits set by the quantum Hamming bound, but for certain restricted cases, 
we can show that there are not.  For codes using fewer than 30 qubits, the 
linear programming bounds of the previous section show this.  In this 
section, I will show that the statement also is true for all stabilizer codes 
that correct one or two errors.  The results can be extended slightly 
beyond stabilizer codes, but do not apply to the most general possible code.

For a one-error-correcting degenerate code, the stabilizer $S$ will contain 
one or more operators of weight one or two.  Weight one operators totally 
constrain a qubit and both the operator and the qubit can be eliminated, 
converting an $[n, k, d]$ code into an $[n-1, k, d]$.  If the latter satisfies 
the quantum Hamming bound, the former will as well.  Suppose there are $l$ 
independent weight two operators $M_1, \ldots, M_l$ in $S$.  Let $D$ be the 
group generated by $M_1, \ldots, M_l$.  Note that $S - D$ will contain no 
operators of weight less than three.  The weight two operators in $D$ tell us 
which errors produce the same states.  For instance, if $M_1 = \Zs{1} \Zs{2}$, 
$\Zs{1} \ket{\psi} = \Zs{2} \ket{\psi}$ for any codeword $\ket{\psi}$.

Any operator in $N(D)$ will take states fixed by $D$ to states fixed by $D$.  
The total dimensionality of the subspace fixed by $D$ is $2^{n-l}$.  Suppose 
that none of the operators in $D$ acts on some qubit $j$.  Then all of the 
three operators $\Xs{j}$, $\Ys{j}$, and $\Zs{j}$ are in $N(D)$, and they are
not degenerate.  Therefore, they must produce orthogonal states in the 
subspace fixed by $D$ for each basis codeword.  There are always at least 
$n-2l$ qubits not affected by $D$, since each generator of $D$ can add at 
most two qubits.  Therefore,
\begin{eqnarray}
\left[1 + 3(n-2l) \right] 2^k & \leq & 2^{n-l} \\
k & \leq & n - l - \log_2 [1+3(n-2l)]. \label{eq-QHB-deg1}
\end{eqnarray}
Recall that the quantum Hamming bound says that
\begin{equation}
k \leq n - \log_2 (1+3n),
\end{equation}
so (\ref{eq-QHB-deg1}) is more restrictive when
\begin{eqnarray}
l + \log_2 [1+3(n-2l)] & \geq & \log_2 (1+3n) \\
l & \geq & \log_2 \left[ \frac{1+3n}{1+3(n-2l)} \right] \\
& = & \log_2 \left[ 1 + \frac{6l}{1 + 3(n-2l)} \right]. \label{eq-QHB-deg1'}
\end{eqnarray}
Assuming $n \geq 2l$, we see that the quantum Hamming bound will still 
hold if $l \geq \log_2 (1+6l)$.  This is true for $l \geq 5$.  For $l=4$, 
(\ref{eq-QHB-deg1'}) holds for $n \geq 9$; for $l=3$, it holds for $n \geq 
7$.  For $l=2$, (\ref{eq-QHB-deg1'}) holds for $n \geq 5$, and for $l=1$, it 
holds for $n \geq 4$.  The remaining possibilities with $n \geq 2l$ are 
ruled out by the linear programming bounds of section
\ref{sec-enumerators}.  On the other hand, if $l > n/2$, then $k \leq n-l 
\leq n/2$.  For $n \geq 13$, the quantum Hamming bound is less 
restrictive than this, so in conjunction with the linear programming 
bounds, we can conclude that there are no distance three degenerate stabilizer 
codes that exceed the quantum Hamming bound.

<!-- pdf-page: 13 -->
We can make a similar argument for codes to correct two errors.  Now let $D$ 
be generated by the operators of weight four or less in $S$.  There must be 
at least $n-4l$ qubits that are unaffected by operators in $D$.  All the 
possible weight one and two errors on those qubits give orthogonal states, so
\begin{eqnarray}
\left[1 + 3(n-4l) + \frac{9}{2} (n-4l) (n-4l-1)\right] 2^k & \leq & 2^{n-l} \\
\left[1 - \frac{3}{2} n + \frac{9}{2} n^2 + 6 l (1 + 12 l - 6 n)\right] 2^l & \leq & 2^{n-k}.
\end{eqnarray}
The quantum Hamming bound will still hold if
\begin{eqnarray}
\left[1 - \frac{3}{2}n + \frac{9}{2} n^2 + 6 l (1 + 12 l - 6 n)\right] 2^l & 
\geq & 1 - \frac{3}{2}n + \frac{9}{2} n^2 \\
\left[ 1 - \frac{6l (6n - 12 l - 1)}{1 - 3n/2 + 9n^2/2} \right] 2^l & \geq & 1.
\label{eq-QHB-deg2}
\end{eqnarray}
Now, $l (6n - 12 l - 1) = -12 [l^2 - (6n-1) l /12]$ is maximized for $l = (6n-
1)/24$.  That means (\ref{eq-QHB-deg2}) will be satisfied when
\begin{eqnarray}
\left[ 1 - \frac{(6n - 1)^2}{8 - 12n + 36n^2} \right] 2^l & \geq & 1 \\
\frac{7}{8 - 12n + 36n^2}\,2^l & \geq & 1 \\
7 \cdot 2^{l-2} & \geq & 9n^2 - 3n + 2.
\end{eqnarray}
If this is true, the code will satisfy the quantum Hamming bound.  If it is 
{\em not} true, then
\begin{eqnarray}
l & \leq & 2 - \log_2 7 + \log_2 (9n^2 - 3n + 2) \\
& \leq & 3 + 2 \log_2 n.
\end{eqnarray}
Then $l (6n - 12l - 1) \leq 6 n l \leq 6 n (3 + 2 \log_2 n)$, so equation 
(\ref{eq-QHB-deg2}) will again be satisfied when
\begin{equation}
\left[ 1 - \frac{6 n (3 + 2 \log_2 n)}{1 - 3n/2 + 9n^2/2} \right] 2^l \geq 1.
\end{equation}
However, for $n \geq 30$,
\begin{equation}
\frac{6 n (3 + 2 \log_2 n)}{1 - 3n/2 + 9n^2/2} \leq 0.58,
\end{equation}
so (\ref{eq-QHB-deg2}) will be satisfied for any $l$ with $1 < l \leq n/4$ 
in the regime of interest.  When $l=1$, (\ref{eq-QHB-deg2}) becomes
\begin{equation}
1 - \frac{6 (6n - 13)}{1 - 3n/2 + 9n^2/2} \geq 1/2.
\end{equation}
However, for $n \geq 30$,
\begin{equation}
\frac{6 (6n - 13)}{1 - 3n/2 + 9n^2/2} \leq 0.26,
\end{equation}
so (\ref{eq-QHB-deg2}) is satisfied for $l=1$ as well.

Therefore, we are left with $l > n/4$.  Again, this implies that $k \leq n-l < 
3n/4$.  This is at least as restrictive than the quantum Hamming bound for $n 
\geq 52$.  For $n=31$, the quantum Hamming bound says $k \leq n-13$.  
Therefore, for $31 \leq n \leq 51$, the only remaining region of interest, 
the code must have $l \leq n/4 + 5$ to violate the quantum Hamming bound.  
The only possibility for $l > n/4 + 4$ is $l=12$, $n=31$.  Assume for the 
moment that $l \leq n/4 + 4$.  Then there are at least $n - 16$ qubits in 
the code that are affected by at most one of the generators of $D$.  This is 
more than $l+3$, so either at least two of the generators of $D$ must each
affect two qubits that are fixed by all of the other generators, or one generator fixes four qubits that are unaffected by all of the other generators. 
The second case will be more restrictive to the code than the first one, so I 
will assume the first case holds.  Assume without loss of generality that the 
two generators are $M_{l-1}$ and $M_l$.  Then errors on the four qubits 
affected only by these generators leave the codewords within the subspace fixed 
by $D'$, the group generated by $M_1, \ldots, M_{l-2}$.  There are 67 errors of 
weight zero, one and two on the four qubits, so
\begin{eqnarray}
67 \cdot 2^k & \leq & 2^{n-(l-2)} \\
k & \leq & n - l - 5.
\end{eqnarray}
This is at least as restrictive as the quantum Hamming bound for any $n$ 
between 31 and 51.

That leaves the case $l=12$, $n=31$.  Even in this case, there must be at 
least fourteen qubits that are affected by at most one of the generators of 
$D$.  As before, this is enough to ensure that we can pick two generators of 
$D$ that will together act on four qubits unaffected by any of the other 
generators.  Again, $k \leq n - l - 5$, which is more restrictive than the quantum Hamming bound.  Therefore, there are no two-error-correcting degenerate 
stabilizer codes exceeding the quantum Hamming bound.

The methods of this section could be adapted and perhaps applied to codes 
correcting three or more errors, but it gets more difficult for each 
additional error, since the cases with $l > n/(2t)$ must be treated on a 
special basis, and the range of $n$ for which this could violate the 
quantum Hamming bound grows rapidly with $t$.  Eventually, it might 
well be true that some code with enough degeneracies does violate the 
quantum Hamming bound.

Even though we cannot rule out the possibility of a sufficiently large 
degenerate code violating the quantum Hamming bound, we can still set
a less restrictive bound on degenerate stabilizer codes by constructing
a classical code from the quantum code~\cite{cleve-classical}.  Since bounds 
on the efficiencies of classical codes are known, we can therefore get
bounds on the possible parameters of quantum codes.

To produce a classical code from a quantum code, first put the code in
standard form, as per (\ref{eq-standard-form}).  In particular, note the
$r \times k$ matrix $A_2$.  $r \leq n-k$, but by performing single qubit
rotations from $N(\G)$, we can always convert one generator to the product of 
$\Z$'s, so we can ensure that $r \leq n-k-1$.  If we look at the classical code 
$C$ with $k \times (r+k)$ generator matrix $(A_2^T | I)$, then $C$ encodes
$k$ bits in at most $n-1$ bits.  If the original quantum code could correct
$t$ quantum errors, it turns out that the classical code $C$ can correct $t$
classical bit flip errors, whether the quantum code was degenerate or 
nondegenerate.  Therefore, the existence of an $[n, k, d]$ quantum code
implies that an $[n-1, k, d]$ classical code exists.

\section{Error-Correcting Codes and Entanglement Purification Protocols}

Before discussing bounds on the channel capacity, I will discuss another 
way of looking at quantum codes that is sometimes helpful for thinking 
about the channel capacity.  Consider the situation where Alice prepares a 
number of EPR pairs and sends one member of the pair to Bob.  In general, 
both the qubits that Alice keeps and the qubits she sends to Bob may be 
subject to errors and decoherence.  This means that Alice and Bob will 
share a number of imperfect pairs.  If Alice attempts to teleport a state 
using these imperfect EPR pairs, for instance, the state that Bob receives 
will be incorrect.  Alice and Bob wish to perform some local operations on 
their halves of the imperfect pairs so that they are left with a smaller 
number of perfect pairs (or at least better ones).  A protocol to do this is 
called an {\em entanglement purification protocol} (or EPP) 
\cite{bennett-tome,bennett-EPP}.

<!-- pdf-page: 14 -->
Depending on the situation, Bob and Alice may or may not be allowed to 
communicate with each other and perform operations conditioned on the 
results of measurements by the other one.  If both Bob and Alice can 
communicate with each other via classical communication channels, the 
possible protocols they can implement are called two-way error purification 
protocols (or 2-EPPs).  If Bob can only receive classical information (as well 
as qubits) from Alice, but not transmit, then Bob and Alice are restricted to 
using one-way error purification protocols (or 1-EPPs).  In principle, there is 
another possibility.  Bob and Alice might not be able to communicate 
classically at all.  However, it turns out that the protocols available for 
them in this case are equivalent to the 1-EPPs.  On the other hand, it is 
known that in some circumstances, 2-EPPs allow more good pairs to be 
purified than 1-EPPs do~\cite{bennett-tome}.

One remarkable fact about 1-EPPs is that they are equivalent to 
quantum error-correcting codes.  Suppose we have a quantum code.  We 
can make a 1-EPP out of it as follows: Alice encodes the qubits she is going 
to send to Bob using the code, then Bob corrects and decodes.  The encoded 
qubits that are thus preserved in the channel retain their entanglement 
with the qubits Alice kept, and thus form part of a good EPR pair.  The 
number of good pairs is just equal to the number of encoded qubits.

Conversely, suppose we have a 1-EPP that distills $k$ good pairs from $n$ 
noisy pairs and we wish to make a quantum code.  In this case Alice is the 
encoder and Bob is the decoder for the code.  Alice creates $n$ EPR pairs 
and sends them to Bob, then performs her half of the 1-EPP.  Since she 
cannot receive transmissions from Bob, she does not need to wait until Bob 
receives the qubits to do this.  This is why a quantum code is equivalent to 
a 1-EPP and not a 2-EPP.  After she has performed her half of the 
purification protocol, sending any necessary classical information, she 
takes the $k$ qubits she wishes to protect and performs her half of the 
teleportation protocol using her half of what will be the $k$ good pairs.  
Again, she sends the classical information about the measurement results 
to Bob.  Bob now receives the qubits, plus all the classical information.  He 
completes the purification protocol, purifying $k$ good pairs.  Since they 
are good EPR pairs, when he then completes the teleportation protocol, the 
resulting state is the correct one, and the whole process acts like a code 
encoding $k$ qubits in $n$ qubits.

\section{Capacity of the Erasure Channel}

Most quantum channels are very difficult to analyze.  However, the 
channel capacity is known for at least one simple channel of interest.  The 
{\em erasure channel} is the channel for which every qubit sent through the 
channel has some chance $p$ of being totally randomized.  However, when 
this happens, we always know on which qubit it occurred.  The capacity of 
the erasure channel for both quantum codes and 2-EPPs is straightforward 
to calculate~\cite{bennett-erasure}.

The capacity for 2-EPPs is particularly straightforward.  If Alice sends $n$ 
EPR pairs through the channel, $pn$ of them will be destroyed, but $(1-
p)n$ will remain intact.  Furthermore, Bob will know which pairs remain 
intact, so he tells Alice and they discard the useless pairs.  This achieves a 
rate of $1-p$.  Clearly, it is impossible to do better than this.  This means 
that the capacity for a 2-EPP is just $1-p$.

With a 1-EPP or quantum code, we cannot do as well, because Bob cannot 
tell Alice which pairs she should keep and which she should throw away.  In 
fact, we can set an upper bound on the capacity of $1-2p$.  Suppose the erasure 
rate of $p$ in the channel is actually caused by Charlie, who steals any 
given qubit with probability $p$, replaces any stolen qubits with random 
ones, and then tells Bob which qubits he stole.  When $p = 1/2$, Bob has 
exactly the same number of valid pairs as Charlie.  If there were any 
operations Alice could make without consulting Bob that enabled him to 
purify even a single valid pair, Charlie could do the same thing as Bob, also 
giving a valid pair.  Now when Alice attempts to teleport something to Bob, 
she is also teleporting it to Charlie.  This would allow the cloning of a 
quantum state.  Therefore, the rate for $p>1/2$ is zero.  For $p<1/2$, we 
can imagine Alice somehow knows $n(1-2p)$ of the pairs that will not be 
stolen by Charlie.  The remaining $2pn$ pairs she is uncertain about.  Of 
them, $pn$ will be stolen by Charlie, again leaving him with the same 
number of good pairs from this set as Bob has.  If Alice attempts to purify 
more than $n(1-2p)$ pairs with Bob, she will therefore also be purifying 
pairs with Charlie, again leading to state cloning.  Therefore, the capacity is 
bounded above by $1-2p$.

This is, in fact, the actual achievable capacity for this channel.  Suppose we 
take a random Abelian subgroup of $\G_n$ with $n-k$ generators.  This 
subgroup will act as the stabilizer $S$ of a code.  If we encode $k$ qubits 
using this code, and then send them through the erasure channel, for large 
$n$, with high probability, $pn$ known qubits will have been randomized.  
We need to distinguish between the $4^{pn}$ possible errors on these 
qubits.  Since the error operators are all on the same $pn$ qubits, there are 
again $4^{pn}$ products of these operators.  If measure one of these products
anticommute with some element of $S$, then we will be able to correct the 
errors and decode the $k$ qubits, with fidelity approaching one for large $n$.  
Since the generators are chosen randomly, each one will commute with half of 
the possible operators of weight $pn$ and anticommute with half of the possible 
operators.  The different generators commute and anticommute with operators 
independently, so the number of operators that commute with all $n-k$ 
generators is
\begin{equation}
4^{pn} / 2^{n-k} = 2^{k - (1-2p)n} = 2^{(r - 1 + 2p) n},
\end{equation}
where $r$ is the rate: $k = rn$.  As long as $r < 1 - 2p$, the chance of not 
being able to distinguish all the likely errors goes to zero as $n \rightarrow 
\infty$.  Therefore, a random stabilizer code can give us rate $1-2p$.  Since 
this coincides with the upper bound on the capacity, it is the actual 
capacity of the erasure channel.

<!-- pdf-page: 15 -->
\section{Capacity of the Depolarizing Channel}
\label{depolarizing}

The {\em depolarizing channel} is a very natural channel to consider.  In this 
channel, with probability $1-p$, each qubit is left alone.  In addition, there 
are equal probabilities $p/3$ that $\X$, $\Y$, or $\Z$ affects the qubit.  We 
can apply similar methods to the depolarizing channel as with the erasure 
channel to place upper and lower bounds on its capacity.  However, 
currently these bounds do not meet, so the actual capacity of the 
depolarizing channel is unknown.

The depolarizing channel can also simulated by imagining Charlie is 
randomly stealing some qubits from the channel.  If Charlie steals a qubit 
with probability $q$ and replaces it with a random qubit (not telling Bob 
which one was stolen), there is still a $1/4$ chance that Charlie happens to 
replace the stolen qubit with one in the same state.  There is only a chance 
$q/4$ of Charlie applying each of $\X$, $\Y$, and $\Z$.  Therefore, this 
situation corresponds to the depolarizing channel with $p = 3q/4$.  We can 
make a cloning argument just as with the erasure channel to set an upper 
bound on the capacity.  Again we find that the capacity is limited by $1-2q 
= 1- 8p/3$.  When $p > 3/8$, the rate of transmission is necessarily zero.

Actually, we can set a tighter upper bound than this.  Randomly stealing qubits 
is not the best eavesdropping method available to Charlie that will look like 
the depolarizing channel.  The best eavesdropping method actually allows 
him to produce the same state as Bob whenever $p > 1/4$~\cite{fuchs-KL}.  
This means that the rate is limited to $1-4p$.  This is the asymptotic form 
of the Knill-Laflamme bound, which was derived for codes with a fixed 
minimum distance in section~\ref{sec-gen-bounds}.

We can set a lower bound for the achievable rate by again considering the 
rate for a random stabilizer code.  If we encode $k$ qubits in $n$ qubits 
using a random stabilizer $S$, the expected number of errors is $pn$.  We 
need measure one of the errors to be distinguishable from each other.  The 
errors $E$ and $F$ are distinguishable if $E^\dagger F$ anticommutes with 
some elements of $S$, and are not if they do not.  The typical product 
$E^\dagger F$ actually does not have weight $2pn$.  There is a chance 
$p^2$ that $E$ and $F$ will both have nontrivial action on a given 
qubit.  If they act as different Pauli matrices, the product will still act on 
that qubit.  If they act as the same Pauli matrix, the product will not act on 
that qubit at all.  The probability of having both act as the same Pauli 
matrix is $p^2/3$.  Therefore, the expected length of the product 
$E^\dagger F$ is $(2p - 4p^2/3)n$.  Let $x = 2p - 4p^2/3$.

Let the number of errors of weight $w$ be $N(w)$.  Then the number of 
different products of weight $xn$ is $N(xn)$, and therefore the number of 
typical products that commute with everything in $S$ is $N(xn) / 2^{n-k}$.  
Now, there are $N(pn)$ likely errors, so the number of ways we can pair 
them into products is $N(pn) [N(pn) -1]/2$.  This means that the number of 
ways of getting any given operator $O$ of weight $xn$ is
\begin{equation}
\left. \pmatrix{ N(pn) \cr 2} \right/ N(xn).
\end{equation}
For each of the pairs that gives one of the $N(xn)/2^{n-k}$ products that 
commute with $S$, we must remove one of the errors in the pair from the 
group of likely errors.  Therefore, we must remove
\begin{equation}
\left. \pmatrix{ N(pn) \cr 2} \right/ 2^{n-k}
\end{equation}
errors.  We want to remove only measure zero of the errors, so we wish this 
number to be small compared to $N(pn)$ for large $n$.  Thus,
\begin{eqnarray}
N (pn) / 2^{n-k+1} & \ll & 1 \\
N (pn) & \ll & 2^{n-k+1} \\
k/n & < & 1 - \frac{1}{n} \log_2 N (pn) = 1 - p \log_2 3 - H(p).
\end{eqnarray}
This is just the quantum Hamming bound (\ref{eq-QHB}).  In other words, 
a random code saturates the quantum Hamming bound.

However, the quantum Hamming bound only limits the efficiency of 
nondegenerate codes.  The typical element of a random stabilizer will have 
weight $3n/4$, which is much larger than $pn$ for any $p$ where the rate 
could possibly be nonzero.  Therefore, a random code will have a 
negligable number of degenerate errors, and the quantum Hamming bound 
will still apply.  However, if we choose the stabilizer to be of a restricted 
form rather than totally random, we can choose it to have very many 
degeneracies, and the quantum Hamming bound may be exceeded
\cite{shor-smolin}, although existing codes only allow us to exceed the 
rate of a random code by a very small amount.  Shor and Smolin showed that
by concatenating a random code with a simple repetition code ($\ket{0}$
becomes the tensor product of $\ket{0}$'s and $\ket{1}$ becomes the tensor
product of $\ket{1}$'s), the rate of the code is improved slightly near the
zero-rate limit.  The optimum block size for repetition turns out to be five.

We can still set an upper bound on the efficiency of a degenerate stabilizer 
code using similar arguments to those that gave us the capacity of a 
random stabilizer code.  Note that this upper bound does not necessarily 
apply to all codes, so it may not be a strict upper bound on the capacity.  
However, non-stabilizer codes are very difficult to work with, so it does 
provide a practical upper bound on the capacity.

To give this bound, assume that every element of $S$ actually has weight 
$xn$.  This bound is unlikely to be achievable, since the product of two 
operators of weight $xn$ will only rarely have weight $xn$ again.  There 
are at least $N(xn)/2^{n-k}$ operators of weight $n$ that commute with $S$, 
but $2^{n-k}$ of them are in $S$.  Therefore, in the best case, there are only 
$N(xn)/2^{n-k} - 2^{n-k}$ operators that can potentially cause a problem.  In 
the limit where $n$ and $k = rn$ are both large, either $N(xn)/2^{n-k}$ will 
dominate the number of troublesome operators, or $N(xn)/2^{n-k} \ll 2^{n-
k}$.  In the first case, the calculation goes through as for a completely 
random stabilizer, giving us a capacity only at the quantum Hamming 
bound.  In the second case,
\begin{eqnarray}
N(xn) & \ll & 2^{2(n-k)} \\
r = k/n & < & 1 - \frac{1}{2n} \log_2 N(xn) = 1 - \frac{x}{2} \log_2 3 - 
\frac{1}{2} H(x).
\label{eq-deg-bound}
\end{eqnarray}
Since $x = 2p - 4p^2/3$, this is higher than the quantum Hamming bound.  
Equation (\ref{eq-deg-bound}) gives an upper bound on the capacity of the 
depolarizing channel achievable using stabilizer codes.  It is shown in
figure~\ref{CCBounds} along with the Knill-Laflamme bound and the quantum
Hamming bound.  Cleve has also proved a bound on the capacity achievable
using degenerate stabilizer codes \cite{cleve-classical}, but it is slightly
worse than (\ref{eq-deg-bound}) everywhere in the region of interest, so
it is not shown in the figure.
\begin{figure}
\epsfig{file=Capacity.eps}
\caption[The quantum Hamming bound, the Knill-Laflamme bound, and the bound
from equation~(\ref{eq-deg-bound})]{The quantum Hamming bound (dashed), the 
Knill-Laflamme bound (dotted), and the bound from equation~(\ref{eq-deg-bound}) 
(solid).}
\label{CCBounds}
\end{figure}
