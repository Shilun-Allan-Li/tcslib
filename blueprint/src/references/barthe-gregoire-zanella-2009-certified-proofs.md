<!-- generated-by: maintainer transcription of the passages used (DW-8) -->
<!-- source-pdf-sha256: 216f8cd86ce5e077730bcf9d5ed1a90131f0107d23e64f249c7df02690b4678a -->
<!-- validation-status: scoped transcription for DW-8; awaiting Codex source review -->

# Formal Certification of Code-Based Cryptographic Proofs

Gilles Barthe, Benjamin Grégoire and Santiago Zanella. *POPL 2009* (36th ACM
SIGPLAN-SIGACT Symposium on Principles of Programming Languages); tag `BGZ09`. Uploaded
copy: 12 PDF pages.

*Transcription note.* The byline of this version reads "Gilles Barthe, Benjamin Grégoire,
Santiago Zanella" (Microsoft Research – INRIA Joint Centre, France), without the third
author's later surname "Zanella Béguelin" used in the library's reference list.

**Scope.** Only the passages that the relational simulation lemma uses are transcribed
(DW-8; pairing ruling Q11): §3.4 (adversaries and the oracles they may call), the opening
of §4 (why a relational Hoare logic, and Shoup's three categories of proof step), §4.1
(the lifting of a relation to distributions, Definition 5 of pRHL judgments, the derived
rules of Figure 5, and the lemmas $(=_{[\![]\!]})$ and $(\le_{[\![]\!]})$ that move a pRHL
judgment to equalities of expectations), §4.2 (observational equivalence and its two
invariant-carrying variants $\vDash_\varphi$ and $\vDash_{\Psi,\Phi}$), and §5.2 (Lemma 1,
lazy/eager sampling, and the replacement of a lazy random oracle $O_l$ by an eager one
$O_e$ inside an arbitrary context). §§1–2, §3.1–§3.3, §5.1, §5.3, §6 and §§7–9 are not
transcribed. The PDF is not committed. Physical and printed pages coincide.

**On the raw extraction.** The paper is set in two columns. Poppler's reading order
interleaves the columns around figures and footnotes, so in
`barthe-gregoire-zanella-2009-certified-proofs.raw.md` a section heading can appear *after*
the text it heads (§3.4's heading on p. 6 is the clearest case). The raw file is the
mechanical extraction and is left as Poppler produced it; this transcription restores the
reading order, which was checked against the page images (rendered at 170 dpi).
Mathematics is set in LaTeX; the wording is the paper's. Notes marked *Transcription note*
are not part of the source.

<a id="pdf-216f8cd86ce5-p006-b001"></a>
<!-- pdf-source: page=6; block=1; confidence=0.95 -->

**Section 3.4, Adversaries (p. 6).** In order to reason formally about security, we make
explicit which variables and procedures are accessible to adversaries, and provide a simple
analysis to check whether an adversary respects its policy. Given a set of procedure
identifiers $\mathcal O$ (the procedures that may be called by the adversary), and sets of
global variables $\mathcal G_A$ (those that can be read and written by the adversary) and
$\mathcal G_{ro}$ (those that the adversary can only read), we say that an adversary
$\mathcal A$ is well-formed in an environment $E$ if the judgment
$\vdash_{\mathrm{wf}}\mathcal A$ can be derived using the rules in Fig. 4. These rules
guarantee that each time a variable is written by the adversary, the adversary has the
right to do so; and that each time a variable is read by the adversary, it is either a
global variable in $\mathcal G_A\cup\mathcal G_{ro}$ or a local variable previously
initialized. **A well-formed adversary is free to call oracles, but any other procedure it
calls must be a well-formed adversary itself.**

Additional constraints may be imposed on adversaries. For example, exact security proofs
usually impose an upper bound to the number of calls adversaries can make to a given
oracle, whereas for some properties such as IND-CCA2 there are some restrictions on the
parameters with which the oracles may be called. Likewise, some proofs impose extra
conditions such as forbidding repeated or malformed queries. These kinds of properties can
be formalized using lists that record the oracle calls, and verifying as postcondition that
the calls were legitimate.

*Transcription note.* Figure 4 ("Static analysis for well-formedness of adversaries", p. 6)
is a rule figure and is not transcribed; only the prose that states its guarantees is.

<a id="pdf-216f8cd86ce5-p006-b002"></a>
<!-- pdf-source: page=6; block=2; confidence=0.95 -->

**Section 4, Relational Hoare Logic, opening (pp. 6–7).** Shoup [31] classifies proof steps
into three categories: transitions based on indistinguishability—which typically involve
applying a security hypothesis, e.g. the DDH assumption—; transitions based on failure
events—which typically amount to bound the probability of bad, as in the Switching
Lemma—; and bridging steps—which correspond to replacing or reorganizing code in a way
that is not observable by adversaries. In some circumstances, a bridging transition from
$G_1$ to $G_2$ may replace a program fragment $P$ by another fragment $P'$ observationally
equivalent to $P$. In general, however, $P$ and $P'$ are only observationally equivalent in
the context where the replacement is done. Such transitions are supported through a
relational Hoare logic, that generalizes observational equivalence through preconditions
and postconditions which we use to characterize the context where the replacement is valid.
Besides, we use relational Hoare logic to establish (in)equalities between probabilities of
two events, as shown by the lemmas $(=_{[\![]\!]})$ and $(\le_{[\![]\!]})$ below, and to
establish program invariants, e.g. in the proof of the Switching Lemma in Sec. 2.2.

*Transcription note.* Reference "[31]" is Shoup's *Sequences of games* (tag `Sho04` in this
library); the three categories named here are the three transition types of
`shoup-2004-sequences-of-games.md`.

<a id="pdf-216f8cd86ce5-p007-b001"></a>
<!-- pdf-source: page=7; block=1; confidence=0.95 -->

**Section 4.1, Probabilistic Relational Hoare Logic (pRHL) (p. 7).** Our logic pRHL
elaborates on and extends to probabilistic programs Benton's Relational Hoare Logic [9].
Benton's logic uses judgments of the form $\vdash G_1\sim G_2:\Psi\Rightarrow\Phi$, and
relates the evaluation of a program $G_1$ to the evaluation of a program $G_2$ w.r.t. a
precondition $\Psi$ and a postcondition $\Phi$, both defined as relations on deterministic
states. Such a judgment states that for any initial memories $m_1$ and $m_2$ satisfying the
precondition $m_1\,\Psi\,m_2$, if the evaluations of $G_1$ in $m_1$ and $G_2$ in $m_2$
terminate with final memories $m_1'$ and $m_2'$ respectively, then $m_1'\,\Phi\,m_2'$
holds. In a probabilistic setting, the evaluation of a program w.r.t. an initial memory
yields a (sub-)distribution. In order to give a meaning to the above judgment, one
therefore needs to lift relations over memories into relations over distributions. We
follow early work on probabilistic bisimulations [21]. The lifting to distributions of a
unary predicate $P$ and of a binary relation $\Phi$ are respectively defined as

$$
\begin{aligned}
\mathsf{range}\ P\ \mu &\stackrel{\mathrm{def}}{=}
  \forall f.\ (\forall a.\ P\,a\Rightarrow f\,a=0)\Rightarrow \mu\,f=0\\
\mu_1\sim_\Phi\mu_2 &\stackrel{\mathrm{def}}{=}
  \exists\mu.\ \pi_1(\mu)=\mu_1\wedge\pi_2(\mu)=\mu_2\wedge\mathsf{range}\ \Phi\ \mu
\end{aligned}
$$

where the projections of $\mu$ are defined as

$$
\pi_1(\mu)\stackrel{\mathrm{def}}{=}\mathsf{bind}\ \mu\ (\lambda(x,y).\mathsf{unit}\ x)
\qquad
\pi_2(\mu)\stackrel{\mathrm{def}}{=}\mathsf{bind}\ \mu\ (\lambda(x,y).\mathsf{unit}\ y)
$$

This way of lifting relations over memories to relations over distributions is a
generalization to arbitrary relations of the definition of Sabelfeld and Sands [29]. Their
definition applies only to PERs, whereas our definition applies to arbitrary relations.
Nevertheless, both definitions coincide for PERs as established by Jonsson, Larsen and
Yi [21].

<a id="pdf-216f8cd86ce5-p007-b002"></a>
<!-- pdf-source: page=7; block=2; confidence=0.95 -->

**Definition 5 (pRHL judgments) (p. 7).** Programs $G_1$ and $G_2$ are equivalent w.r.t.
precondition $\Psi$ and postcondition $\Phi$ iff

$$
\vDash G_1\sim G_2:\Psi\Rightarrow\Phi\ \stackrel{\mathrm{def}}{=}\
\forall\,m_1\,m_2.\ m_1\,\Psi\,m_2\Rightarrow
[\![G_1]\!]\,m_1\sim_\Phi[\![G_2]\!]\,m_2
$$

Our approach slightly departs from Benton's: rather than defining the rules for pRHL and
proving them sound w.r.t. the meaning of judgments, we place ourselves in a semantic
setting and derive the rules as lemmas. This allows to easily extend the system by deriving
extra rules, or even to resort to the semantic definition if the system turns out to be
insufficient.

Figure 5 gathers some representative derived rules. To improve readability, in the figure
and in the remainder of the paper we let $e\langle i\rangle$ denote
$\lambda m_1\,m_2.\ [\![e]\!]\,m_i=\mathsf{true}$, where $e$ is a boolean expression. As
pRHL allows for arbitrary relations, we freely use higher-order logic; in particular,
$\mathsf{PER}$ and $\mathsf{SYM}$ are predicates over relations that stand for *partial
equivalence relation* and *symmetric relation* respectively.

<a id="pdf-216f8cd86ce5-p007-b003"></a>
<!-- pdf-source: page=7; block=3; confidence=0.95 -->

**Section 4.1, one-sided variants and the rules that are new in pRHL (p. 7).** There are
two points worth noting. First, most rules admit, in addition to their symmetrical version
of Fig. 5, one-sided (left and right) variants, e.g. for assignments

$$
\frac{m_1\,\Phi'\,m_2\stackrel{\mathrm{def}}{=}(m_1\{[\![e_1]\!]m_1/x_1\})\,\Phi\,m_2}
{\vDash E_1,x_1\leftarrow e_1\sim E_2,\mathsf{nil}:\Phi'\Rightarrow\Phi}
$$

Second, some rules of pRHL do not appear in RHL, or generalize existing rules. The rule
[R-Case] allows to do a case analysis on the evaluation of an arbitrary relation in the
initial memories. Together with simple rules in the spirit of

$$
\frac{\vDash E_1,c_1\sim E_2,c:\Psi\wedge e\langle1\rangle\Rightarrow\Phi}
{\vDash E_1,\mathsf{if}\ e\ \mathsf{then}\ c_1\ \mathsf{else}\ c_2\sim E_2,c:
 \Psi\wedge e\langle1\rangle\Rightarrow\Phi}
$$

it subsumes [R-Cond] and allows to prove judgments that would otherwise not be derivable,
such as the equivalence between $(\mathsf{if}\ e\ \mathsf{then}\ c_1\ \mathsf{else}\ c_2)$
and $(\mathsf{if}\ \neg e\ \mathsf{then}\ c_2\ \mathsf{else}\ c_1)$. We also use [R-Case]
to prove the correctness of dataflow analyses that exploit the information provided by
entering branches.

In addition, we often use the rule [R-Inv] that generalizes the rule [R-Sym] to inverse of
relations

$$
\frac{\vDash G_1\sim G_2:\Psi\Rightarrow\Phi}
{\vDash G_2\sim G_1:\Psi^{-1}\Rightarrow\Phi^{-1}}\ \text{[R-Inv]}
$$

and we make an extensive use of the rule [R-Comp] that generalizes the rule [R-Tr] to
composition of relations

$$
\frac{\vDash G_1\sim G:\Psi'\Rightarrow\Phi'\qquad\vDash G\sim G_2:\Psi''\Rightarrow\Phi''}
{\vDash G_1\sim G_2:\Psi'\circ\Psi''\Rightarrow\Phi'\circ\Phi''}\ \text{[R-Comp]}
$$

The benefits of the rule [R-Comp], as opposed to [R-Tr], are illustrated by considering
"independent" preconditions and postconditions of the form
$\Psi\stackrel{\mathrm{def}}{=}\lambda x\,y.\Psi_1\,x\wedge\Psi_2\,y$ and
$\Phi\stackrel{\mathrm{def}}{=}\lambda x\,y.\Phi_1\,x\wedge\Phi_2\,y$. In order to apply
the rule [R-Tr] to $G_1$ and $G_2$, we are essentially forced to have $\Psi_1=\Psi_2$ and
$\Phi_1=\Phi_2$, and furthermore we must also choose the same pre and postcondition for the
intermediate game $G$. This constraint makes the rule [R-Tr] impractical, we use instead
the rule [R-Comp] to introduce intermediate games that do not satisfy the same
specification as $G_1$ or $G_2$.

*Footnote 4 (p. 7).* The machine-checked rule requires that $\Phi,\Phi'$ are decidable, and
uses **Set**-valued existential quantification $\exists_{\mathbf{Set}}$ in the composition
for preconditions, i.e.
$x\,(\Psi\circ\Psi')\,z\stackrel{\mathrm{def}}{=}\exists_{\mathbf{Set}}y.\ x\,\Psi\,y\wedge y\,\Psi'z$.

<a id="pdf-216f8cd86ce5-p007-b004"></a>
<!-- pdf-source: page=7; block=4; confidence=0.95 -->

**Section 4.1, the rule [R-Rand] and its bijection premise (p. 7).** The rule [R-Rand] is
also (obviously) not present in RHL. Let
$\mathbb I_x\stackrel{\mathrm{def}}{=}(\lambda v.\mathsf{if}\ x=v\ \mathsf{then}\ 1\
\mathsf{else}\ 0)$, and define the support of a distribution,
$\mathsf{supp}([\![d]\!]\,m)$, by the clause

$$
v\in\mathsf{supp}([\![d]\!]\,m)\iff[\![d]\!]\,m\,\mathbb I_v\neq 0
$$

Finally, let $[\![d_1]\!]\,m_1=_g[\![d_2]\!]\,m_2$ iff there exists a set $X$ and a
bijection $g:X\to X$ such that
$\mathsf{supp}([\![d_1]\!]\,m_1)=\mathsf{supp}([\![d_2]\!]\,m_2)=X$ and
$[\![d_1]\!]\,m_1\,\mathbb I_a=[\![d_2]\!]\,m_2\,\mathbb I_{(g\,a)}$ for all $a$ in $X$. To
apply rule [R-Rand], it is necessary to exhibit a function $f$ such that for all memories
$m_1$ and $m_2$, $[\![d_1]\!]\,m_1=_{f\,m_1\,m_2}[\![d_2]\!]\,m_2$. Thus, if
$d_1=d_2=[0..n]$ for some constant $n$, and we take $f$ to be the identity function, the
premise simplifies to the expected,

$$
m_1\,\Psi\,m_2\stackrel{\mathrm{def}}{=}
\forall\,v\in[0..n].\ (m_1\{v/x_1\})\,\Phi\,(m_2\{v/x_2\})
$$

Section 5.3 shows that the generality of the rule is required for applications such as
optimistic sampling.

<a id="pdf-216f8cd86ce5-p007-b005"></a>
<!-- pdf-source: page=7; block=5; confidence=0.95 -->

**Section 4.1, pRHL judgments as equalities of expectations — the lemma
$(=_{[\![]\!]})$ (p. 7).** It is often fruitful to understand pRHL judgments in terms of
the inability of the postcondition to separate between the two commands of the judgment.
Define two functions $f$ and $g$ to be equivalent w.r.t. a predicate $\Phi$ iff

$$
f=_\Phi g\ \stackrel{\mathrm{def}}{=}\ \forall\,m_1\,m_2.\ m_1\,\Phi\,m_2\Rightarrow
f(m_1)=g(m_2)
$$

The definition of pRHL judgments entails

$$
\left.
\begin{array}{l}
\vDash G_1\sim G_2:\Psi\Rightarrow\Phi\\
f=_\Phi g\\
m_1\,\Psi\,m_2
\end{array}
\right\}
\Rightarrow\ [\![G_1]\!]\,m_1\,f=[\![G_2]\!]\,m_2\,g
\qquad (=_{[\![]\!]})
$$

*Transcription note.* $[\![G]\!]\,m\,f$ is the expectation of $f$ under the
(sub-)distribution that running $G$ from memory $m$ produces. The paper's semantics (§3.2,
not transcribed) is given in the **measure monad**
$\mathcal M(X)\stackrel{\mathrm{def}}{=}(X\to[0,1])\to[0,1]$, with
$[\![c]\!]\,m:\mathcal M(\mathcal M)$ (p. 5), so a distribution *is* a function on
functions and $[\![G]\!]\,m\,f$ is literally its application to $f$. The paper notes that
$\mathcal M(X)$ "was proposed by Audebaud and Paulin [4] as a variant of the expectation
monad used by Ramsey and Pfeffer [27]" (p. 5).

<a id="pdf-216f8cd86ce5-p008-b001"></a>
<!-- pdf-source: page=8; block=1; confidence=0.95 -->

**Figure 5, selection of derived rules of pRHL (p. 8).**

$$
\vDash E_1,\mathsf{nil}\sim E_2,\mathsf{nil}:\Phi\Rightarrow\Phi\quad\text{[R-Skip]}
$$

$$
\frac{\vDash E_1,c_1\sim E_2,c_2:\Phi\Rightarrow\Phi'\qquad
      \vDash E_1,c_1'\sim E_2,c_2':\Phi'\Rightarrow\Phi''}
{\vDash E_1,c_1;c_1'\sim E_2,c_2;c_2':\Phi\Rightarrow\Phi''}\ \text{[R-Seq]}
$$

$$
\vDash E_1,x_1\leftarrow e_1\sim E_2,x_2\leftarrow e_2:
(\lambda\,m_1\,m_2.\ (m_1\{[\![e_1]\!]m_1/x_1\})\,\Phi\,(m_2\{[\![e_2]\!]m_2/x_2\}))
\Rightarrow\Phi\quad\text{[R-Ass]}
$$

$$
\frac{m_1\,\Psi\,m_2\stackrel{\mathrm{def}}{=}
 [\![d_1]\!]m_1=_{f\,m_1\,m_2}[\![d_2]\!]m_2\wedge
 \forall\,v\in\mathsf{supp}([\![d_1]\!]m_1).\ (m_1\{v/x_1\})\,\Phi\,(m_2\{f\,m_1\,m_2\,v/x_2\})}
{\vDash E_1,x_1\xleftarrow{\$}d_1\sim E_2,x_2\xleftarrow{\$}d_2:\Psi\Rightarrow\Phi}
\ \text{[R-Rand]}
$$

$$
\frac{\forall m_1\,m_2.\ m_1\,\Psi\,m_2\Rightarrow[\![e_1]\!]\,m_1=[\![e_2]\!]\,m_2
 \qquad\vDash E_1,c_1\sim E_2,c_2:\Psi\wedge e_1\langle1\rangle\Rightarrow\Phi
 \qquad\vDash E_1,c_1'\sim E_2,c_2':\Psi\wedge\neg e_1\langle1\rangle\Rightarrow\Phi}
{\vDash E_1,\mathsf{if}\ e_1\ \mathsf{then}\ c_1\ \mathsf{else}\ c_1'\sim
 E_2,\mathsf{if}\ e_2\ \mathsf{then}\ c_2\ \mathsf{else}\ c_2':\Psi\Rightarrow\Phi}
\ \text{[R-Cond]}
$$

$$
\frac{\forall m_1\,m_2.\ m_1\,\Phi\,m_2\Rightarrow[\![e_1]\!]\,m_1=[\![e_2]\!]\,m_2
 \qquad\vDash E_1,c_1\sim E_2,c_2:\Phi\wedge e_1\langle1\rangle\Rightarrow\Phi}
{\vDash E_1,\mathsf{while}\ e_1\ \mathsf{do}\ c_1\sim
 E_2,\mathsf{while}\ e_2\ \mathsf{do}\ c_2:\Phi\Rightarrow\Phi\wedge\neg e_1\langle1\rangle}
\ \text{[R-Whl]}
$$

$$
\frac{\vDash G_1\sim G_2:\Psi'\Rightarrow\Phi'\quad
 \forall m_1\,m_2.\ m_1\,\Psi\,m_2\Rightarrow m_1\,\Psi'\,m_2\quad
 \forall m_1\,m_2.\ m_1\,\Phi'\,m_2\Rightarrow m_1\,\Phi\,m_2}
{\vDash G_1\sim G_2:\Psi\Rightarrow\Phi}\ \text{[R-Sub]}
$$

$$
\frac{\vDash G_1\sim G_2:\Psi\Rightarrow\Phi\quad\mathsf{SYM}(\Psi)\quad\mathsf{SYM}(\Phi)}
{\vDash G_2\sim G_1:\Psi\Rightarrow\Phi}\ \text{[R-Sym]}
\qquad
\frac{\vDash G_1\sim G:\Psi\Rightarrow\Phi\quad\vDash G\sim G_2:\Psi\Rightarrow\Phi
 \quad\mathsf{PER}(\Psi)\quad\mathsf{PER}(\Phi)}
{\vDash G_1\sim G_2:\Psi\Rightarrow\Phi}\ \text{[R-Tr]}
$$

$$
\frac{\vDash G_1\sim G_2:\Psi\wedge\Psi'\Rightarrow\Phi\quad
 \vDash G_1\sim G_2:\Psi\wedge\neg\,\Psi'\Rightarrow\Phi}
{\vDash G_1\sim G_2:\Psi\Rightarrow\Phi}\ \text{[R-Case]}
$$

<a id="pdf-216f8cd86ce5-p008-b002"></a>
<!-- pdf-source: page=8; block=2; confidence=0.95 -->

**Section 4.1, termination sensitivity and the lemma $(\le_{[\![]\!]})$ (p. 8).** By
instantiating $f$ and $g$ to $\mathbb 1$, one can observe that observational equivalence
enjoys some form of termination sensitivity

$$
(\vDash G_1\sim G_2:\Psi\Rightarrow\Phi)\wedge m_1\,\Psi\,m_2\Rightarrow
[\![G_1]\!]\,m_1\,\mathbb 1=[\![G_2]\!]\,m_2\,\mathbb 1
$$

This interpretation of pRHL judgments is strongly connected to the relation between
relational logics and information flow [3, 9]. We extensively use $(=_{[\![]\!]})$, and its
variant $(\le_{[\![]\!]})$ below, to fall back from the world of pRHL into the world of
probabilities, in which security statements are expressed;

$$
\left.
\begin{array}{l}
\vDash G_1\sim G_2:\Psi\Rightarrow\Phi\\
f\le_\Phi g\\
m_1\,\Psi\,m_2
\end{array}
\right\}
\Rightarrow\ [\![G_1]\!]\,m_1\,f\le[\![G_2]\!]\,m_2\,g
\qquad (\le_{[\![]\!]})
$$

where $f\le_\Phi g\stackrel{\mathrm{def}}{=}\forall\,m_1\,m_2.\ m_1\,\Phi\,m_2\Rightarrow
f(m_1)\le g(m_2)$.

<a id="pdf-216f8cd86ce5-p008-b003"></a>
<!-- pdf-source: page=8; block=3; confidence=0.95 -->

**Section 4.2, Observational equivalence (p. 8).** Observational equivalence is derived as
an instance of relational Hoare judgments in which pre and postconditions are restricted to
relations based on equality over a subset of variables. Given a set $X$ of variables, we
define $=_X$ as

$$
m_1=_X m_2\ \stackrel{\mathrm{def}}{=}\ \forall\,x\in X.\ m_1\,x=m_2\,x
$$

Then, the observational equivalence of $G_1$ and $G_2$ w.r.t. an input set $I$ and an
output set $O$ is defined as

$$
\vDash G_1\simeq^I_O G_2\ \stackrel{\mathrm{def}}{=}\
\vDash G_1\sim G_2:\ =_I\ \Rightarrow\ =_O
$$

All derived rules for pRHL can be specialized to the case of observational equivalence. For
example, we have

$$
\frac{\vDash e_1\simeq^I e_2\qquad\vDash E_1,c_1\simeq^I_O E_2,c_2
 \qquad\vDash E_1,c_1'\simeq^I_O E_2,c_2'}
{\vDash E_1,\mathsf{if}\ e_1\ \mathsf{then}\ c_1\ \mathsf{else}\ c_1'\simeq^I_O
 E_2,\mathsf{if}\ e_2\ \mathsf{then}\ c_2\ \mathsf{else}\ c_2'}
$$

where $\vDash e_1\simeq^I e_2$ iff for every memories $m_1$ and $m_2$, $m_1=_I m_2$ implies
$[\![e_1]\!]\,m_1=[\![e_2]\!]\,m_2$.

To support automation, CertiCrypt implements a calculus of variable dependencies and
provides two functions, $\mathsf{eqobsIn}$ and $\mathsf{eqobsOut}$, that given a command
$c$ and a set $O$ (respectively $I$) of output (input) variables compute a set $I$ ($O$) of
input (output) variables such that $\vDash E_1,c\simeq^I_O E_2,c$. **CertiCrypt also
provides tactics for two variants of observational equivalence that are widely used in
game-based proofs, namely**

$$
\begin{aligned}
\vDash_\varphi G_1\simeq^I_O G_2\ &\stackrel{\mathrm{def}}{=}\
  \vDash G_1\sim G_2:\ =_I\wedge\varphi\ \Rightarrow\ =_O\wedge\varphi\\
\vDash_{\Psi,\Phi} G_1\simeq^I_O G_2\ &\stackrel{\mathrm{def}}{=}\
  \vDash G_1\sim G_2:\ =_I\wedge\Psi\ \Rightarrow\ =_O\wedge\Phi
\end{aligned}
$$

These tactics use a (sound but incomplete) weakest precondition calculus for relational
judgments.

<a id="pdf-216f8cd86ce5-p008-b004"></a>
<!-- pdf-source: page=8; block=4; confidence=0.95 -->

**Section 5, Proof methods for bridging steps, opening (p. 8).** CertiCrypt provides a
powerful set of tactics and algebraic equivalences to automate bridging steps. Most tactics
rely on an implementation of a certified optimizer for pWHILE, with the exception of *lazy
sampling* which has an ad hoc implementation.

<a id="pdf-216f8cd86ce5-p009-b001"></a>
<!-- pdf-source: page=9; block=1; confidence=0.95 -->

**Section 5.2, Lazy sampling (p. 9).** It is sometimes convenient to defer random choices
in games until they are actually needed, or conversely, to make random choices as early as
possible. The lazy sampling technique, allows to delay the random sampling of a value until
the point in the program where it is first used. Conversely, eager sampling allows to
choose a random value, which would be otherwise sampled later, at the beginning of a game.
These techniques are presented in [8], where the authors discuss some of its subtleties. In
this section we present a syntax-oriented criterion for the correctness of lazy sampling
that can be applied provided the sampling is adequately guarded. **Here by context we mean
a program context with multiple holes that may appear either in the main program or any of
the procedures in the environment.**

<a id="pdf-216f8cd86ce5-p009-b002"></a>
<!-- pdf-source: page=9; block=2; confidence=0.95 -->

**Lemma 1 (Lazy/eager sampling) (p. 9).** Let $C[\cdot]$ be a context, $c_1$ and $c_2$
commands, $e$ a boolean expression, $d$ a distribution expression, and $z$ a variable, such
that $C[\cdot]$ does not modify $\mathrm{fv}(e)\cup\mathrm{fv}(d)$ and does not use $z$.
Assume

1. $\vDash z\xleftarrow{\$}d;c_1;\mathsf{if}\ e\ \mathsf{then}\ z\xleftarrow{\$}d\ \sim\
   z\xleftarrow{\$}d;c_1\ :\ (=\wedge\,e\langle1\rangle)\Rightarrow\ =$
2. $\vDash c_2\sim c_2\ :\ (=\wedge\,\neg e\langle1\rangle)\Rightarrow
   (=\wedge\,\neg e\langle1\rangle)$

Let $c=\mathsf{if}\ e\ \mathsf{then}\ z\xleftarrow{\$}d;c_1\ \mathsf{else}\ c_2$ and
$c'=\mathsf{if}\ e\ \mathsf{then}\ c_1\ \mathsf{else}\ c_2$. Then,

$$
\vDash C[c];\mathsf{if}\ e\ \mathsf{then}\ z\xleftarrow{\$}d\ \sim\
z\xleftarrow{\$}d;C[c']\ :\ (=\wedge\,e\langle1\rangle)\Rightarrow\ =
$$

Intuitively, in the above lemma $e$ indicates whether $z$ has not been used in the game
since it was last sampled. If it has not been used, then it is perfectly fine to resample
it. The first two hypotheses ensure that $e$ has exactly this meaning, $c_1$ must set it to
false if it has used the value sampled in $z$, and $c_2$ must not reset $e$ if it is false.
The first hypothesis is the one that allows to swap $c_1$ with $z\xleftarrow{\$}d$,
provided the value of $z$ is not used in $c_1$. Note that, for clarity, we have omitted
environments in the above lemma, and so the second hypothesis is not as trivial as it may
seem because both programs may have different environments.

<a id="pdf-216f8cd86ce5-p009-b003"></a>
<!-- pdf-source: page=9; block=3; confidence=0.95 -->

**Section 5.2, replacing a lazy random oracle by an eager one (pp. 9–10).** Suppose we want
to eagerly sample the answer that a random oracle

$$
O_l(x)\stackrel{\mathrm{def}}{=}
\mathsf{if}\ x\notin\mathrm{dom}(L)\ \mathsf{then}\ y\xleftarrow{\$}d;\
L\leftarrow(x,y)::L;\ \mathsf{return}\ L[x]
$$

gives to a particular query $x'$, i.e. we want to transform $O_l$ into

$$
\begin{aligned}
O_e(x)\stackrel{\mathrm{def}}{=}\ &\mathsf{if}\ x\notin\mathrm{dom}(L)\ \mathsf{then}\\
&\qquad\mathsf{if}\ x=x'\ \mathsf{then}\ y\leftarrow y'\ \mathsf{else}\ y\xleftarrow{\$}d;\\
&\qquad L\leftarrow(x,y)::L\\
&\mathsf{return}\ L[x]
\end{aligned}
$$

Define
$O_l'(x)\stackrel{\mathrm{def}}{=}\mathsf{if}\ x'\notin\mathrm{dom}(L)\ \mathsf{then}\
y'\xleftarrow{\$}d;O_e(x)\ \mathsf{else}\ O_l(x)$,
$O_e'(x)\stackrel{\mathrm{def}}{=}\mathsf{if}\ x'\notin\mathrm{dom}(L)\ \mathsf{then}\
O_e(x)\ \mathsf{else}\ O_l(x)$, both returning $L[x]$. **Oracles $O_l$ and $O_e$ result
semantically equivalent to $O_l'$ and $O_e'$, respectively.**

<a id="pdf-216f8cd86ce5-p010-b001"></a>
<!-- pdf-source: page=10; block=1; confidence=0.95 -->

**Section 5.2, the oracle replacement, conclusion (p. 10).** Lemma 1 can be applied taking
$e=x'\notin\mathrm{dom}(L)$, $z=y'$, and $c_1=O_e(x)$, $c_2=O_l(x)$ **to safely replace
oracle $O_l$ by oracle $O_e$ in the environment of a program**, sampling $y'$ at the
beginning. Whenever a bound for the number of queries to a random oracle is known in
advance, the above trick can be iteratively applied to completely remove randomness from
the oracle code, as it is done in the proof of the Switching Lemma in Sec. 2.2.
