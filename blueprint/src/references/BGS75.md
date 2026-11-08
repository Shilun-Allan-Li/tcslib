<!-- generated-by: proofmatch Claude repair -->
<!-- source-pdf-sha256: 2459e3840724ade8c7d3b9901042b49f88ed9c514b17e78cc7ee7fb8051b6e9f -->

<a id="pdf-2459e3840724-p001-b001"></a>
<!-- pdf-source: page=1; block=1; confidence=0.98 -->
# Relativizations of the \(\mathcal P =? \mathcal{NP}\) Question

<a id="pdf-2459e3840724-p001-b002"></a>
<!-- pdf-source: page=1; block=2; confidence=0.99 -->
**Abstract.** We investigate relativized versions of the open question of whether every language accepted nondeterministically in polynomial time can be recognized deterministically in polynomial time. For any set \(X\), let \(\mathcal P^X\) (resp. \(\mathcal{NP}^X\)) be the class of languages accepted in polynomial time by deterministic (resp. nondeterministic) query machines with oracle \(X\). We construct a recursive set \(A\) such that \(\mathcal P^A = \mathcal{NP}^A\). On the other hand, we construct a recursive set \(B\) such that \(\mathcal P^B \ne \mathcal{NP}^B\). Oracles \(X\) are constructed to realize all consistent set inclusion relations between the relativized classes \(\mathcal P^X\), \(\mathcal{NP}^X\), and co-\(\mathcal{NP}^X\), the family of complements of languages in \(\mathcal{NP}^X\). Several related open problems are described.

<a id="pdf-2459e3840724-p001-b003"></a>
<!-- pdf-source: page=1; block=3; confidence=0.99 -->
## 1. Introduction

<a id="pdf-2459e3840724-p001-b004"></a>
<!-- pdf-source: page=1; block=4; confidence=0.90 -->
P is the class of languages decidable in deterministic polynomial time; NP is the class accepted in nondeterministic polynomial time. The paper studies whether these classes remain equal when machines can query an oracle, and reports that some oracles yield equality while others yield inequality.

<a id="pdf-2459e3840724-p002-b001"></a>
<!-- pdf-source: page=2; block=1; confidence=0.93 -->
The authors argue that general simulations or diagonalization methods for resolving P versus NP would transfer to oracle settings, where the paper obtains conflicting answers. A query machine is a multitape Turing machine with a query tape and query, yes, and no states; an oracle for a set X sends the machine to yes exactly when the query string belongs to X.

<a id="pdf-2459e3840724-p002-b002"></a>
<!-- pdf-source: page=2; block=2; confidence=0.96 -->
**Definition.** A query machine is deterministic when each configuration permits at most one operation; otherwise it is nondeterministic. A deterministic machine with oracle X recognizes a language if it halts on every input and accepts exactly its members. A nondeterministic machine accepts an input when some computation halts in an accepting state.

<a id="pdf-2459e3840724-p002-b003"></a>
<!-- pdf-source: page=2; block=3; confidence=0.92 -->
**Definition.** A query machine is polynomial-bounded if one polynomial bounds the running time of every computation on inputs of length n, for every oracle. For oracle X, P^X consists of languages recognized by polynomial-bounded deterministic query machines, and NP^X consists of those accepted by polynomial-bounded nondeterministic query machines. coNP^X comprises complements of languages in NP^X.

<a id="pdf-2459e3840724-p002-b004"></a>
<!-- pdf-source: page=2; block=4; confidence=0.99 -->
A query machine is polynomial-bounded if there is a polynomial \(p(n)\) such that every computation of the machine on every input of length \(n\) halts within \(p(n)\) steps, whatever oracle \(X\) is used. For any oracle \(X\), we denote by \(\mathcal P^X\) the class of languages recognized by polynomial-bounded deterministic query machines with oracle \(X\), and we denote by \(\mathcal{NP}^X\) the class of languages accepted by polynomial-bounded nondeterministic query machines with oracle \(X\). The class of languages whose complements are in \(\mathcal{NP}^X\) is denoted by co-\(\mathcal{NP}^X\).

Every query machine can be converted to a polynomial-bounded machine by attaching a clock which terminates every computation of the machine that exceeds some predetermined polynomial time bound. We can thereby produce a list of polynomial-bounded query machines which perform all possible polynomial-bounded computations. We will denote by \(P_i\) the \(i\)th deterministic polynomial-bounded machine in this list and by \(NP_i\) the \(i\)th nondeterministic polynomial-bounded query machine. Without loss of generality, we can assume that \(p_i(n)\) is a strict upper bound on the length of any computation by \(P_i\) or \(NP_i\) with oracle \(X\) on an input of length \(n\), where \(p_i(n)=i+n\). We indicate by use of a superscript when an oracle has been specified for a query machine; thus \(NP_i^X\) and \(P_i^X\) denote query machines using oracle \(X\).

<a id="pdf-2459e3840724-p003-b001"></a>
<!-- pdf-source: page=3; block=1; confidence=0.80 -->
**Definition.** A finite sequence of binary strings is encoded over {0,1,*} by concatenation with separators, replacing 0, 1, and * respectively by 00, 01, and 11. Encoding and decoding take linear time in the encoded input length. Binary strings are enumerated by length and lexicographically within each length; x^n denotes n-fold concatenation of x.

<a id="pdf-2459e3840724-p003-b002"></a>
<!-- pdf-source: page=3; block=2; confidence=0.74 -->
Section 2 constructs a recursive oracle A with P^A ≠ NP^A and discusses polynomial-space-complete languages and finding accepting computations when P^A = NP^A. Section 3 constructs a contrasting oracle B; Section 4 lists open problems. Some results were independently obtained by other researchers.

<a id="pdf-2459e3840724-p003-b003"></a>
<!-- pdf-source: page=3; block=3; confidence=0.72 -->
## 2. P ≠ NP, relativized

<a id="pdf-2459e3840724-p003-b004"></a>
<!-- pdf-source: page=3; block=4; confidence=0.84 -->
**Definition.** For a language class C, K in C is Cook-complete if every language in C is recognized by a polynomial-bounded deterministic query machine using K as oracle. It is Karp-complete if every S in C has a polynomial-time computable many-one reduction f satisfying x ∈ S iff f(x) ∈ K. Karp-completeness implies Cook-completeness.

<a id="pdf-2459e3840724-p003-b005"></a>
<!-- pdf-source: page=3; block=5; confidence=0.99 -->
Every Karp-complete set is Cook-complete. Ladner, Lynch, and Selman [4] compare the polynomial-bounded reducibilities of Cook and Karp. Note that if \(K\) is Cook-complete in \(\mathcal F\), then \(\mathcal F \subseteq \mathcal P^K\).

<a id="pdf-2459e3840724-p003-b006"></a>
<!-- pdf-source: page=3; block=6; confidence=0.99 -->
**Lemma 1.** For any oracle \(X\), define the language \(K(X)\) to be \(\{\langle i,x,0^n\rangle : \text{some computation of } NP_i^X \text{ accepts } x \text{ in fewer than } n \text{ steps}\}\). Then \(K(X)\) is Karp-complete in \(\mathcal{NP}^X\). In particular, \(\mathcal P^X=\mathcal{NP}^X\) if and only if \(K(X)\in\mathcal P^X\).

<a id="pdf-2459e3840724-p003-b007"></a>
<!-- pdf-source: page=3; block=7; confidence=0.72 -->
**Proof.** K(X) ∈ NP^X. If S ∈ NP^X is accepted by NP_i^X and p_i bounds its running time, map x to (i,x,0^{p_i(|x|)}); this is a polynomial-time reduction, since x ∈ S iff NP_i^X accepts x within that bound iff the encoded triple belongs to K(X). Thus K(X) is Karp-complete. The lemma's final equivalence follows from completeness and the class inclusion; the proof continues beyond the supplied text.

<a id="pdf-2459e3840724-p003-b008"></a>
<!-- pdf-source: page=3; block=8; confidence=0.69 -->
The text remarks that {(i,x) : NP_i^X accepts x} is not in P^X because there is no uniform polynomial running-time bound across the indexed machines.

<a id="pdf-2459e3840724-p004-b001"></a>
<!-- pdf-source: page=4; block=1; confidence=0.90 -->
A language can be polynomial-time reducible to a language that is not polynomial-complete.

<a id="pdf-2459e3840724-p004-b002"></a>
<!-- pdf-source: page=4; block=2; confidence=0.99 -->
The result is attributed independently to Meyer and Fischer, and to Hunt.

<a id="pdf-2459e3840724-p004-b003"></a>
<!-- pdf-source: page=4; block=3; confidence=1.00 -->
**Theorem 1.** There is an oracle \(A\) such that \(\mathcal P^A=\mathcal{NP}^A\).

<a id="pdf-2459e3840724-p004-b004"></a>
<!-- pdf-source: page=4; block=4; confidence=0.98 -->
**Proof.** We construct an oracle \(A\) such that \(A=K(A)\). Let \(A=\{\langle i,x,0^n\rangle : NP_i^A\text{ accepts }x\text{ in }<n\text{ steps}\}\). This is a valid inductive definition of a set. In a computation of length \(<n\), no string of length \(\ge n\) can be queried. To simulate \(NP_i^A\) on input \(x\) for \(<n\) steps, we need know only which elements of length \(<n\le |\langle i,x,0^n\rangle|\) belong to \(A\). Therefore \(A\) is well-defined, and by definition \(A=K(A)\). Since \(K(A)=A\in\mathcal P^A\), we conclude \(\mathcal P^A=\mathcal{NP}^A\) by Lemma 1. Q.E.D.

<a id="pdf-2459e3840724-p004-b005"></a>
<!-- pdf-source: page=4; block=5; confidence=0.88 -->
The recursion theorem also gives a recursive oracle with the same separation; the constructed oracle can be recognized deterministically in exponential time.

<a id="pdf-2459e3840724-p004-b006"></a>
<!-- pdf-source: page=4; block=6; confidence=0.98 -->
A language is recognizable in polynomial space if a deterministic Turing machine decides it using at most \(p(n)\) work-tape squares on inputs of length \(n\), for some polynomial \(p\). The text uses \(\mathsf{PSPACE}\) for this class. Savitch's theorem makes the nondeterministic polynomial-space definition equivalent: space \(p(n)\) nondeterministically can be simulated deterministically in space \(p(n)^2\).

<a id="pdf-2459e3840724-p004-b007"></a>
<!-- pdf-source: page=4; block=7; confidence=0.99 -->
A language \(S\) is log-space reducible to \(A\) if there is a function \(f(x)\) computable in space \(\log(|x|)\) such that \(x\in S\iff f(x)\in A\). The language \(A\) is polynomial-space complete if every language in \(\mathcal{PS}\) is log-space reducible to \(A\). Since every function computable in log space is computable in polynomial time, every polynomial-space complete language is Karp-complete in \(\mathcal{PS}\). If \(A\) is polynomial-space complete, then \(\mathcal{PS}=\mathcal P^A\).

<a id="pdf-2459e3840724-p004-b008"></a>
<!-- pdf-source: page=4; block=8; confidence=0.94 -->
The validity problem for first-order sentences in equality is given as a natural polynomial-space-complete language; Stockmeyer and Meyer provide further word-problem examples. An artificial example encodes triples \((i,x,0^n)\) where deterministic machine \(P_i\) recognizes \(x\) using fewer than \(n\) space.

<a id="pdf-2459e3840724-p004-b009"></a>
<!-- pdf-source: page=4; block=9; confidence=0.93 -->
**Theorem 2.** If \(A\) is polynomial-space complete, then \(\mathsf{P}^A=\mathsf{PSPACE}\).

<a id="pdf-2459e3840724-p004-b010"></a>
<!-- pdf-source: page=4; block=10; confidence=0.86 -->
**Proof.** Since \(A\in\mathsf{PSPACE}\), oracle computations in polynomial time with oracle \(A\) can be simulated in polynomial space, so \(\mathsf{P}^A\subseteq\mathsf{PSPACE}\). Completeness gives a log-space reduction from every polynomial-space language to \(A\), hence \(\mathsf{PSPACE}\subseteq\mathsf{P}^A\). Therefore the classes are equal.

<a id="pdf-2459e3840724-p004-b011"></a>
<!-- pdf-source: page=4; block=11; confidence=0.80 -->
When the relativized deterministic and nondeterministic polynomial-time classes coincide, a deterministic oracle machine can simulate a nondeterministic polynomial-time computation by querying which branch leads to acceptance.

<a id="pdf-2459e3840724-p005-b001"></a>
<!-- pdf-source: page=5; block=1; confidence=0.86 -->
**Lemma 2.** Suppose oracle \(A\) satisfies \(\mathsf{P}^A=\mathsf{NP}^A\). For each nondeterministic query machine \(NP_i\), there is a deterministic query machine \(P_j\) that outputs an accepting computation of \(NP_i\) on input \(x\) whenever \(NP_i\) accepts \(x\).

<a id="pdf-2459e3840724-p005-b002"></a>
<!-- pdf-source: page=5; block=2; confidence=0.94 -->
**Proof.** Encode machine configurations as instantaneous descriptions. Let \(\mathsf{COMP}(X)\) contain encodings \((i,x,0^m,I_0,\ldots,I_m)\) of accepting computations of query machines with oracle \(X\), with \(m<p_i(|x|)\). Let \(\mathsf{INIT}(X)\) contain the prefixes of these accepting computations; the source states \(\mathsf{INIT}(X)\in\mathsf{NP}^X\). Under \(\mathsf{P}^A=\mathsf{NP}^A\), a deterministic polynomial-time oracle machine can recognize \(\mathsf{INIT}(A)\). Starting from the initial configuration, extend the prefix one step at a time by testing the finitely many possible next configurations for membership in \(\mathsf{INIT}(A)\). If \(NP_i\) accepts \(x\), some accepting computation exists, so this process finds one within polynomially many steps.

<a id="pdf-2459e3840724-p005-b003"></a>
<!-- pdf-source: page=5; block=3; confidence=0.99 -->
The proof technique of Lemma 2 will also be used in the proof of Theorem 6.

<a id="pdf-2459e3840724-p005-b004"></a>
<!-- pdf-source: page=5; block=4; confidence=0.80 -->
The section aims to construct recursive oracles realizing consistent inclusion relations among relativized complexity classes, including examples where the classes differ and where relativized nondeterministic polynomial time is not closed under complementation.

<a id="pdf-2459e3840724-p006-b001"></a>
<!-- pdf-source: page=6; block=1; confidence=0.90 -->
For an oracle \(X\), define \(L(X)=\{x:\exists y\in X,\ |y|=|x|\}\). Thus \(L(X)\in\mathsf{NP}^X\), by guessing a string \(y\) of input length and querying whether it belongs to \(X\).

<a id="pdf-2459e3840724-p006-b002"></a>
<!-- pdf-source: page=6; block=2; confidence=0.98 -->
The next theorem is credited independently to Richard Ladner; the text includes a direct proof to illustrate the construction method.

<a id="pdf-2459e3840724-p006-b003"></a>
<!-- pdf-source: page=6; block=3; confidence=0.98 -->
**Theorem 3.** There is an oracle \(B\) such that \(\mathcal P^B\ne\mathcal{NP}^B\).

**Proof.** We construct a set \(B\) such that \(L(B)\) does not belong to \(\mathcal P^B\). The construction of \(B\) proceeds in stages. We denote by \(B(i)\) the finite set of strings placed into \(B\) prior to stage \(i\). Recall that \(p_i(n)\) is an upper bound on the lengths of computations by \(P_i^X\) and \(NP_i^X\) for all oracles \(X\) and all inputs of length \(n\). Let \(n_0=0\).

**Stage \(i\).** Choose \(n>n_i\) so large that \(p_i(n)<2^n\). Run query machine \(P_i\) with oracle \(B(i)\) on input \(x_i=0^n\). If \(P_i^{B(i)}\) accepts \(0^n\), then place no strings into \(B\) at this stage. Otherwise, if \(P_i^{B(i)}\) rejects \(0^n\), then add to \(B\) the least string (that is, the earliest occurring string in the canonical enumeration of binary strings) of length \(n\) not queried during the computation of \(P_i^{B(i)}\) on \(0^n\). Such a string exists because not every string of length \(n\) can be queried by \(P_i^{B(i)}\) on \(0^n\): in \(p_i(n)\) steps, \(P_i^{B(i)}\) can ask at most \(p_i(n)\) questions, and we have chosen \(n\) so that \(p_i(n)<2^n\), the number of strings of length \(n\). Finally, let \(n_{i+1}=2^n\). (This will ensure that no string of length \(\le 2^n\) is added to \(B\) at a later stage.) Go to the next stage.

The computation of \(P_i\) on input \(x_i\) is the same whether \(B\) or \(B(i)\) is used as oracle, because no string queried by \(P_i^{B(i)}\) on input \(x_i\) is later added to or deleted from \(B\). At stage \(i\), we ensure that \(P_i^B\) does not recognize \(L(B)\): by construction, \(P_i^{B(i)}\), and hence \(P_i^B\), rejects \(x_i\) iff some string of length \(|x_i|\) belongs to \(B\), that is, iff \(x_i\in L(B)\). Therefore \(L(B)\) does not belong to \(\mathcal P^B\). Q.E.D.

<a id="pdf-2459e3840724-p006-b004"></a>
<!-- pdf-source: page=6; block=4; confidence=0.91 -->
**Proof.** Build \(B\) in stages, where \(B(i)\) is the finite set chosen before stage \(i\). At stage \(i\), choose \(n>n_i\) with \(p_i(n)<2^n\) and run deterministic oracle machine \(P_i\) on \(0^n\) using oracle \(B(i)\). If it accepts, add no strings; if it rejects, add the least length-\(n\) string not queried in that computation. Such a string exists because fewer than \(2^n\) queries are made. Choose \(n_{i+1}\) so later stages add no strings of length at most \(2^n\). The computation on \(0^n\) is unchanged when the final oracle \(B\) replaces \(B(i)\). Consequently \(P_i\) fails to decide \(L(B)\): its answer on \(0^n\) disagrees with whether a length-\(n\) string belongs to \(B\).

<a id="pdf-2459e3840724-p006-b005"></a>
<!-- pdf-source: page=6; block=5; confidence=0.99 -->
The set \(B\) constructed in the proof of Theorem 3 is sparse: for every \(n\), there is at most one string \(x\in B\) such that \(n\le |x|<2^n\). An obvious modification of the proof of Theorem 3 yields the following result: there are arbitrarily sparse recursive sets such that \(\mathcal P^B\ne\mathcal{NP}^B\).

<a id="pdf-2459e3840724-p006-b006"></a>
<!-- pdf-source: page=6; block=6; confidence=0.86 -->
The proof relies on querying an arbitrary length-\(n\) string in about \(n\) steps, yielding \(L(B)\in\mathsf{NP}^B\). Alternate oracle-tape models are described, and the text says the proofs of Theorems 1–3 do not directly carry over to those models.

<a id="pdf-2459e3840724-p006-b007"></a>
<!-- pdf-source: page=6; block=7; confidence=0.99 -->
Richard Ladner has shown that there are oracles \(B\) recognizable deterministically in exponential time such that \(\mathcal P^B\ne\mathcal{NP}^B\).

<a id="pdf-2459e3840724-p007-b001"></a>
<!-- pdf-source: page=7; block=1; confidence=0.99 -->
From Theorems 1 and 3 we see that the answer to the question \(\mathcal P^X=?\mathcal{NP}^X\) depends on the oracle \(X\). Kurt Mehlhorn [5] has shown that the family of oracles \(X\) for which \(\mathcal P^X=\mathcal{NP}^X\) is a “meagre” set in a space of recursive oracles. In this sense, “most” oracles satisfy \(\mathcal P^X\ne\mathcal{NP}^X\).

<a id="pdf-2459e3840724-p007-b002"></a>
<!-- pdf-source: page=7; block=2; confidence=0.72 -->
**Theorem 4.** There is an oracle $C$ such that the relativized class denoted in the source by $\mathcal{C}$ is not closed under complementation.

<a id="pdf-2459e3840724-p007-b003"></a>
<!-- pdf-source: page=7; block=3; confidence=0.99 -->
**Theorem 4.** There is an oracle \(C\) such that \(\mathcal{NP}^C\) is not closed under complementation.

**Proof.** By a construction very similar to that of Theorem 3, we generate an oracle \(C\) such that \(\mathcal{NP}^C\) does not contain \(\overline{L(C)}\), the complement of \(L(C)\). Let \(C(i)\) be the set of strings placed into \(C\) before stage \(i\), and let \(n_0=0\).

**Stage \(i\).** Choose \(n>n_i\) so that \(p_i(n)<2^n\). (That is, \(n\) is greater than the length of every string queried earlier in this construction.) Run nondeterministic query machine \(NP_i\) with oracle \(C(i)\) on input \(x_i=0^n\). If \(NP_i^{C(i)}\) accepts \(0^n\), then choose any accepting computation and place into \(C\) some string of length \(n\) not queried during this computation. Otherwise, place no string into \(C\) at this stage. Let \(n_{i+1}=2^n\), and go to the next stage.

By construction, \(NP_i^C\) accepts \(x_i\) iff some string of length \(|x_i|\) belongs to \(C\), that is, iff \(x_i\in L(C)\). Consequently, \(NP_i^C\) does not accept \(\overline{L(C)}\). Therefore \(\overline{L(C)}\) does not belong to \(\mathcal{NP}^C\). Q.E.D.

<a id="pdf-2459e3840724-p007-b004"></a>
<!-- pdf-source: page=7; block=4; confidence=1.00 -->
**Theorem 5.** There is an oracle \(D\) such that \(\mathcal P^D\ne\mathcal{NP}^D\) but \(\mathcal{NP}^D\) is closed under complementation.

<a id="pdf-2459e3840724-p007-b005"></a>
<!-- pdf-source: page=7; block=5; confidence=0.97 -->
**Proof.** It is easily seen that \(\mathcal{NP}^X\) is closed under complementation if and only if \(\overline{K(X)}\in\mathcal{NP}^X\), where \(K(X)\) is the complement of the Karp-complete language \(K(X)\). We shall construct an oracle \(D\) such that (i) \(\mathcal P^D\ne\mathcal{NP}^D\) and (ii) \(u\in\overline{K(D)}\) iff \(u\) is a prefix of some string \(v\in D\) such that \(|v|=2|u|\). Then \(\mathcal P^D\ne\mathcal{NP}^D\) from (i); and \(\overline{K(D)}\in\mathcal{NP}^D\) from (ii), and so \(\mathcal{NP}^D\) is closed under complementation.

At stage \(n\) in the construction, we decide the membership in \(D\) of all strings of length \(n\). In the course of the construction, some strings will be reserved for \(\overline D\), that is, designated as nonmembers of \(D\). An index \(i\) will be cancelled at some stage when we ensure that \(P_i^D\) does not recognize \(L(D)\). As usual, \(D(n)\) denotes those strings placed into \(D\) prior to stage \(n\).

**Stage \(n=2m\).** For every string \(z\) of length \(n=2m\) not reserved for \(\overline D\) at an earlier stage, determine the prefix \(u\) of \(z\) of length \(m\). If \(u\) encodes a triple \(\langle i,x,0^t\rangle\), then place \(z\) into \(D\) iff \(P_i^{D(n)}\) does not accept \(x\) in fewer than \(t\) steps.

**Stage \(n=2m+1\).** Let \(i\) be the least uncancelled index. If any string of length \(\ge n\) has been reserved for \(\overline D\), or if \(p_i(n)\ge 2^n\), then add no elements to \(D\) at this stage. Otherwise, run \(P_i\) with oracle \(D(n)\) on input \(0^n\) and reserve for \(\overline D\) all strings of length \(\ge n\) queried during this computation. If \(P_i^{D(n)}\) accepts \(0^n\), then add no elements to \(D\). But if \(P_i^{D(n)}\) rejects \(0^n\), then add to \(D\) the least string of length \(n\) not queried (and so not reserved for \(\overline D\)). Finally cancel index \(i\).

<a id="pdf-2459e3840724-p008-b001"></a>
<!-- pdf-source: page=8; block=1; confidence=0.97 -->
Every index is eventually cancelled, and when index \(i\) is cancelled at some stage, we have guaranteed that \(P_i^D\) does not recognize \(L(D)\). Therefore \(L(D)\in\mathcal{NP}^D-\mathcal P^D\).

At any odd stage \(2m+1\), at most \(p_i(n)<2^m\) strings are reserved for \(\overline D\), and so fewer than \(2^0+2^1+\cdots+2^{m-1}<2^m\) strings of length \(2m\) can be reserved for \(\overline D\) at odd stages before stage \(2m\). Therefore every string \(u\) of length \(m\) is the prefix of at least one string \(v\) of length \(2m\) which is never reserved for \(\overline D\). By construction, \(u\in\overline{K(D)}\) iff \(u\) prefixes a number \(v\in D\) of length \(2|u|\), and so \(\overline{K(D)}\in\mathcal{NP}^D\). Q.E.D.

<a id="pdf-2459e3840724-p008-b002"></a>
<!-- pdf-source: page=8; block=2; confidence=1.00 -->
**Theorem 6.** There is an oracle \(E\) such that \(\mathcal P^E\ne\mathcal{NP}^E\) and \(\mathcal P^E=\mathcal{NP}^E\cap\operatorname{co}\mathcal{NP}^E\).

<a id="pdf-2459e3840724-p008-b003"></a>
<!-- pdf-source: page=8; block=3; confidence=0.96 -->
Define \(e(n)\) inductively by \(e(0)=0\) and \(e(n+1)=2^{e(n)}\). Choose any oracle \(A\) such that \(\mathcal P^A=\mathcal{NP}^A\). Without any loss of generality, we can assume that \(A\) contains no elements of length \(e(n)\) for any \(n\ge0\). The oracle \(E\) is obtained by adding to \(A\) at stage \(n\) at most one string of length \(e(n)\). Let \(E(0)=A\) and let \(E(n)\) denote the set of strings placed into \(E\) before stage \(n\). There are two types of requirements to be satisfied in the construction of \(E\). An unsatisfied requirement \(\langle i,i\rangle\) is vulnerable at stage \(n\) if \(p_i(e(n))<2^{e(n)}\). An unsatisfied requirement \(\langle j,k\rangle\) with \(j\ne k\) is vulnerable at stage \(n\) if there is a string \(x\) such that \(e(n-1)<\log_2|x|\le e(n)\le\max\{p_j(|x|),p_k(|x|)\}<e(n+1)\) and neither \(NP_j\) nor \(NP_k\) with oracle \(E(n)\) accepts \(x\). We agree that requirement \(r_1\) has higher priority than requirement \(r_2\) just when \(r_1<r_2\).

<a id="pdf-2459e3840724-p008-b004"></a>
<!-- pdf-source: page=8; block=4; confidence=0.60 -->
**Proof.** The construction is designed both to make $L(E)$ fail to lie in the indicated class and to ensure that if a set and its complement are both accepted by nondeterministic query machines with oracle $E$, then the set is in the indicated deterministic class. At stage $n$, satisfy the highest-priority vulnerable requirement. For $(j,k)$ with $j\ne k$, add no string. For $(i,i)$, simulate machine $P_i$ on $0^{e(n)}$ with oracle $E(n)$; if it rejects, add the least unqueried string of length $e(n)$, and otherwise add none. Each diagonal requirement is eventually met: at its satisfying stage, $P_i$ accepts $0^{e(n)}$ iff $E$ has a string of that length, so it cannot recognize $L(E)$.

<a id="pdf-2459e3840724-p008-b005"></a>
<!-- pdf-source: page=8; block=5; confidence=0.99 -->
Now suppose \(S\) and \(\overline S\) belong to \(\mathcal{NP}^E\). We must show that \(S\in\mathcal P^E\). Assume \(NP_j^E\) accepts \(S\) and \(NP_k^E\) accepts \(\overline S\). Note that requirement \(\langle j,k\rangle\) is never satisfied, else there would be a string \(x\) accepted by neither \(NP_j^E\) nor \(NP_k^E\). Let \(m\) be so large that

(i) for every \(x\) such that \(|x|\ge e(m)\) there is at most one \(n\) such that \(\log_2|x|\le e(n)\le\max\{p_j(|x|),p_k(|x|)\}\);

(ii) if a requirement of higher priority than requirement \(\langle j,k\rangle\) is ever satisfied, then it is satisfied before stage \(m\).

<a id="pdf-2459e3840724-p009-b001"></a>
<!-- pdf-source: page=9; block=1; confidence=0.96 -->
We can decide \(S\) deterministically in polynomial time using oracle \(E\) by the following procedure. With input \(x\), if \(|x|<e(m)\), then use a finite table to decide if \(x\in S\). Otherwise \(|x|\ge e(m)\). Calculate the least \(n\) such that \(e(n)\ge\log_2|x|\). Determine which elements were added to \(E\) before stage \(n\) by querying the oracle \(E\) about all strings of lengths \(e(0),e(1),\ldots,e(n-1)\). Only \(O(|x|)\) strings need be queried here, since \(e(n-1)\le\log_2|x|\).

Now there are two cases. If \(e(n)>\max\{p_j(|x|),p_k(|x|)\}\), then no computation of either \(NP_j\) or \(NP_k\) can query oracle \(E\) about any string of length \(\ge e(n)\). Therefore the computation of \(NP_j\) on input \(x\) is the same with oracle \(E(n)\) as with oracle \(E\). Since we have already calculated \(E(n)-A\), we can produce a query machine \(NP_{i(n)}^{E(n)}\) which simulates \(NP_j^{E(n)}\) but makes no queries about strings of length \(e(m)\) for any \(m<n\); these queries are answered without recourse to the oracle \(E(n)\) by using the finite table of elements of \(E(n)-A\). Clearly \(NP_{i(n)}\) on input \(x\) gives the same result with oracle \(A\) as with oracle \(E(n)\). Therefore \(NP_j^E\) accepts \(x\) iff \(NP_{i(n)}^A\) accepts \(x\), that is, iff \(\langle i(n),x,0^{p_j(|x|)}\rangle\in K(A)\). (We can easily make sure that \(NP_{i(n)}\) has the same running time bound as \(NP_j\), and that the length of the index \(i(n)\) is at most a polynomial of \(|x|\).) Since \(K(A)\) belongs to \(\mathcal P^A\), we can now determine in polynomial time if \(NP_j^E\) accepts \(x\).

<a id="pdf-2459e3840724-p009-b002"></a>
<!-- pdf-source: page=9; block=2; confidence=0.53 -->
If $e(n)\le\max\{p_j(|x|),p_k(|x|)\}$, the unsatisfiability of requirement $(j,k)$ ensures at least one of the two machines accepts $x$ with oracle $E(n)$. The recovered $E(n)\setminus A$ lets the procedure determine which machine accepts.

<a id="pdf-2459e3840724-p009-b003"></a>
<!-- pdf-source: page=9; block=3; confidence=0.94 -->
Suppose, to be definite, \(NP_j^{E(n)}\) accepts \(x\). (In case \(NP_k^{E(n)}\) accepts \(x\), the argument is similar.) We must now determine if \(NP_j^E\) accepts \(x\), where \(E\) might contain a string of length \(e(n)\).

Since \(\mathcal P^A=\mathcal{NP}^A\) and since we have already calculated \(E(n)-A\), we can use the method of Lemma 2 to find an accepting computation of \(NP_j^{E(n)}\) on input \(x\). Now we examine this computation to see if it represents a valid computation when oracle \(E\) is used instead of \(E(n)\). Whenever a string \(y\) of length \(e(n)\) is queried by \(NP_j^{E(n)}\) on \(x\), we consult oracle \(E\) about \(y\). There are two subcases. If no such \(y\) belongs to \(E\), then the computation of \(NP_j^{E(n)}\) on \(x\) is the same as the computation of \(NP_j^E\) on \(x\). Now \(NP_j^{E(n)}\) accepts \(x\), and so \(NP_j^E\) also accepts \(x\). We conclude that \(x\in S\).

In the other subcase, \(NP_j^{E(n)}\) on input \(x\) queries some string \(y\) of length \(e(n)\) which belongs to \(E\). By construction, there is at most one number in \(E\) of length \(e(n)\). Thus we have correctly calculated \(E(n+1)-E(n)\). Earlier we found \(E(n)-A\), so we now know \(E(n+1)-A\). Using the method of the first case above, we can finally determine which machine, \(NP_j\) or \(NP_k\), with oracle \(E(n+1)\) accepts \(x\). Since \(e(n+1)>\max\{p_j(|x|),p_k(|x|)\}\), no number of length \(\ge e(n+1)\) can be queried by \(NP_j^E\) or \(NP_k^E\) on \(x\), so \(NP_j^E\) accepts \(x\) iff \(NP_j^{E(n+1)}\) accepts \(x\). Q.E.D.

<a id="pdf-2459e3840724-p010-b001"></a>
<!-- pdf-source: page=10; block=1; confidence=0.98 -->
**Theorem 7.** There is an oracle \(F\) such that \(\mathcal P^F\subseteq\mathcal{NP}^F\cap\operatorname{co}\mathcal{NP}^F\subseteq\mathcal{NP}\).

**Proof.** We outline the construction. Let \(L_1(F)=\{x: |x|\text{ is even and there is }y\in F\text{ with }|y|=|x|\}\), and let \(L_2(F)=\{x: |x|\text{ is odd and there is a string }0y\in F\text{ with }|0y|=|x|\}\). Modify the construction of Theorem 4 so that \(L_1(F)\in\mathcal{NP}^F-\operatorname{co}\mathcal{NP}^F\) and \(L_2(F)\in\mathcal{NP}^F\cap\operatorname{co}\mathcal{NP}^F-\mathcal P^F\). To force \(L_2(F)\in\mathcal{NP}^F\cap\operatorname{co}\mathcal{NP}^F\), we require that for every odd \(n\) there is a string \(0y\) of length \(n\) in \(F\) iff there is no string \(1y\) of length \(n\) in \(F\). We omit the details. Q.E.D.

<a id="pdf-2459e3840724-p010-b002"></a>
<!-- pdf-source: page=10; block=2; confidence=1.00 -->
**Theorem 7.** There is an oracle \(F\) such that \(\mathcal P^F\subseteq\mathcal{NP}^F\cap\operatorname{co}\mathcal{NP}^F\subseteq\mathcal{NP}\).

<a id="pdf-2459e3840724-p010-b003"></a>
<!-- pdf-source: page=10; block=3; confidence=0.73 -->
The section introduces questions about polynomial-time complexity hierarchies, recalling a characterization of the class denoted in the source by $\mathcal{A}$ and prior work of Meyer and Stockmeyer.

<a id="pdf-2459e3840724-p010-b004"></a>
<!-- pdf-source: page=10; block=4; confidence=1.00 -->
**Lemma 3.** A language \(L\) belongs to \(\mathcal{NP}\) iff there is a polynomial \(p(n)\) and a predicate \(R(x,y)\) in \(\mathcal P\) such that \(x\in L\iff(\exists y)[|y|\le p(|x|)\ \&\ R(x,y)]\).

<a id="pdf-2459e3840724-p010-b005"></a>
<!-- pdf-source: page=10; block=5; confidence=0.99 -->
**Proof.** (\(\Leftarrow\)) Suppose \(x\in L\iff(\exists y)[|y|\le p(|x|)\ \&\ R(x,y)]\). Then we can accept \(L\) in polynomial time by nondeterministically selecting a string \(y\) such that \(|y|\le p(|x|)\) and accepting \(x\) iff \(R(x,y)\) is true.

(\(\Rightarrow\)) If \(L\in\mathcal{NP}\), then \(L\) is accepted by some query machine \(NP_i\). Define predicate \(R(x,y)\) to hold iff \(y\) encodes an accepting computation of \(NP_i\) on input \(x\). Clearly \(R(x,y)\) belongs to \(\mathcal P\). We then choose a polynomial \(p(n)\) large enough that \(|y|<p(|x|)\) whenever \(y\) encodes a computation of length \(\le p_i(|x|)\). Q.E.D.

<a id="pdf-2459e3840724-p010-b006"></a>
<!-- pdf-source: page=10; block=6; confidence=0.98 -->
Meyer and Stockmeyer [6] have defined a polynomial-bounded analogue of the arithmetic hierarchy, the \(\mathcal P\)-hierarchy. They define \(\Sigma_0^{\mathcal P}=\Pi_0^{\mathcal P}=\Delta_0^{\mathcal P}\) to be the class \(\mathcal P\). Then \(\Sigma_{i+1}^{\mathcal P}\) is the class of languages definable by polynomial-bounded existential quantification over predicates in \(\Pi_i^{\mathcal P}\); that is, \(L\in\Sigma_{i+1}^{\mathcal P}\) iff there is a polynomial \(p(n)\) and a predicate \(R(x,y)\) in \(\Pi_i^{\mathcal P}\) such that \(x\in L\iff(\exists y)[|y|\le p(|x|)\ \&\ R(x,y)]\). Similarly, \(\Pi_{i+1}^{\mathcal P}\) contains exactly those languages definable by polynomial-bounded universal quantification over predicates in \(\Sigma_i^{\mathcal P}\). (Equivalently, \(L\in\Sigma_i^{\mathcal P}\) iff there is a polynomial \(p(n)\) and a predicate \(R(x,y_1,\ldots,y_i)\) in \(\mathcal P\) such that \(x\in L\iff(\exists y_1)(\forall y_2)\cdots(Qy_i)[|y_1|,|y_2|,\ldots,|y_i|\le p(|x|)\ \&\ R(x,y_1,\ldots,y_i)]\), where there are \(i\) alternations of polynomial-bounded quantifiers.) \(\Delta_{i+1}^{\mathcal P}\) is defined to be the class of languages recognizable in polynomial time with the aid of an oracle for some language in \(\Sigma_i^{\mathcal P}\); that is, \(L\in\Delta_{i+1}^{\mathcal P}\) iff \(L\in\mathcal P^S\) for some \(S\in\Sigma_i^{\mathcal P}\). The \(\mathcal P\)-hierarchy is \(\{\Sigma_i^{\mathcal P},\Pi_i^{\mathcal P},\Delta_i^{\mathcal P}:i\ge0\}\).

<a id="pdf-2459e3840724-p010-b007"></a>
<!-- pdf-source: page=10; block=7; confidence=0.99 -->
\(\Delta_{i+1}^{\mathcal P}\) is defined to be the class of languages recognizable in polynomial time with the aid of an oracle for some language in \(\Sigma_i^{\mathcal P}\); that is, \(L\in\Delta_{i+1}^{\mathcal P}\) iff \(L\in\mathcal P^S\) for some \(S\in\Sigma_i^{\mathcal P}\).

<a id="pdf-2459e3840724-p011-b001"></a>
<!-- pdf-source: page=11; block=1; confidence=0.99 -->
The \(\mathcal P\)-hierarchy shares several of the properties of the arithmetic hierarchy:

(i) \(L\in\Sigma_i^{\mathcal P}\iff\overline L\in\Pi_i^{\mathcal P}\);

(ii) \(\Sigma_i^{\mathcal P}\cup\Pi_i^{\mathcal P}\subseteq\Delta_{i+1}^{\mathcal P}\subseteq\Sigma_{i+1}^{\mathcal P}\cap\Pi_{i+1}^{\mathcal P}\).

However, it is not known if any of the inclusions in (ii) are proper; the \(\mathcal P\)-hierarchy may consist of only a single class, namely, \(\Sigma_0^{\mathcal P}=\Pi_0^{\mathcal P}=\Delta_0^{\mathcal P}=\mathcal P\). One of the results of [6] implies the following.

**Lemma 4 (Meyer–Stockmeyer).** If \(\Sigma_i^{\mathcal P}=\Pi_i^{\mathcal P}\) for any \(i\ge1\), then \(\Sigma_j^{\mathcal P}=\Pi_j^{\mathcal P}=\Sigma_i^{\mathcal P}\) for every \(j\ge i\). In particular, if \(\mathcal P=\mathcal{NP}\), then \(\Sigma_i^{\mathcal P}=\Pi_i^{\mathcal P}=\Delta_i^{\mathcal P}=\mathcal P\) for every \(i\).

<a id="pdf-2459e3840724-p011-b002"></a>
<!-- pdf-source: page=11; block=2; confidence=0.58 -->
The text says the hierarchy inclusions need not be known proper; if two adjacent levels coincide, the hierarchy collapses. It defines relativized versions by allowing predicates and the oracle-assisted class to use an oracle $X$, and states that the hierarchy properties and Lemma 4 also relativize.

<a id="pdf-2459e3840724-p011-b003"></a>
<!-- pdf-source: page=11; block=3; confidence=0.67 -->
For the oracle \(A\) of Theorem 1, \(\mathcal{NP}^A=\mathcal P^A\), hence the \(\mathcal P\), \(A\)-hierarchy collapses entirely. If \(D\) is the oracle of Theorem 5, then \(\Sigma_0^{\mathcal P,D}\subseteq\Sigma_1^{\mathcal P,D}=\Pi_1^{\mathcal P,D}\); the \(\mathcal P\), \(D\)-hierarchy consists of only two levels. If \(E\) is the oracle of Theorem 6, then \(\Sigma_1^{\mathcal P,E}\subseteq\Sigma_2^{\mathcal P,E}\subseteq\Sigma_2^{\mathcal P,E}\) (since \(\Pi_1^{\mathcal P,E}\ne\Sigma_1^{\mathcal P,E}\)) and \(\Sigma_2^{\mathcal P,E}=\Sigma_2^{\mathcal P,E}\cap\Pi_2^{\mathcal P,E}\).

<a id="pdf-2459e3840724-p011-b004"></a>
<!-- pdf-source: page=11; block=4; confidence=0.95 -->
Several questions can be asked about relativized \(\mathcal P\)-hierarchies.

(i) Does there exist an oracle \(X\) such that \(\Sigma_i^{\mathcal P,X}\subsetneq\Sigma_{i+1}^{\mathcal P,X}\) for all \(i\), that is, such that the \(\mathcal P\), \(X\)-hierarchy contains infinitely many distinct classes?

(ii) Does there exist an oracle \(X\) such that \(\Sigma_{i-1}^{\mathcal P,X}\subsetneq\Sigma_i^{\mathcal P,X}=\Sigma_{i+1}^{\mathcal P,X}\), that is, the \(\mathcal P\), \(X\)-hierarchy extends exactly \(i\) levels?

(iii) Does there exist an oracle \(X\) such that the \(\mathcal P\), \(X\)-hierarchy is not trivial but \(\Sigma_i^{\mathcal P,X}\subseteq\Delta_{i+1}^{\mathcal P,X}=\Sigma_{i+1}^{\mathcal P,X}\cap\Pi_{i+1}^{\mathcal P,X}\) for all \(i\)? (Only question (i) has an affirmative answer for the arithmetic hierarchy.) An interesting open question, less general than (i)–(iii) is

(iv) Does there exist an oracle \(X\) such that \(\Sigma_2^{\mathcal P,X}\ne\Pi_2^{\mathcal P,X}\)?

We were unable to settle (iv) by the methods of this paper.

<a id="pdf-2459e3840724-p011-b005"></a>
<!-- pdf-source: page=11; block=5; confidence=0.94 -->
The authors acknowledge colleagues for permission to report results, suggestions of a theorem and open problems, and referee corrections.

<a id="pdf-2459e3840724-p012-b001"></a>
<!-- pdf-source: page=12; block=1; confidence=0.96 -->
Bibliography entries [5]–[10] cite works by Mehlhorn, Meyer and Stockmeyer, Morris, Rogers, Savitch, and Stockmeyer and Meyer.
