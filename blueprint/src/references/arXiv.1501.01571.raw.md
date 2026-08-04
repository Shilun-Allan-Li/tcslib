<!-- generated-by: proofmatch local extraction -->
<!-- source-pdf-sha256: 7fbbda473d03c6486194e389ee98adb205a16dd05ad1717dc337ad8e69d348f4 -->
<!-- extractor: arxiv-tex-source tropp-ch4-wrapped.tex (PDF text layer unusable; pseudo-pages from TeX); SELECTIVE: Chapter 4 (Matrix Gaussian & Rademacher Series, containing Thm 4.1.1) only -->

<!-- pdf-page: 1 -->
\chapter[Matrix Gaussian \& Rademacher Series]{Matrix Gaussian Series \& \\ Matrix Rademacher Series} \label{chap:matrix-series}

In this chapter, we present our first set of matrix concentration inequalities.  These results provide spectral information about a sum of fixed matrices, each modulated by an independent scalar random variable.  This type of formulation is surprisingly versatile, and it captures a range of interesting examples.  Our main goal, however, is to introduce
matrix concentration in the simplest setting possible.

To be more precise about our scope, let us introduce the concept of a matrix Gaussian series.
Consider a finite sequence $\{ \mtx{B}_k \}$ of fixed matrices with the same dimension,
along with a finite sequence $\{ \gamma_k \}$ of independent standard normal random variables.
We will study the spectral norm of the random matrix
$$
\mtx{Z} = \sum\nolimits_k \gamma_k \mtx{B}_k.
$$
This expression looks abstract, but it has concrete modeling power.
For example, we can express a Gaussian Wigner matrix, one of the
classical random matrices, in this fashion.  But the real value of this
approach is that we can use matrix Gaussian series to represent
many kinds of random matrices built from Gaussian random variables.
This technique allows us to attack problems that classical methods
do not handle gracefully.  For instance, we can easily study a
Toeplitz matrix with Gaussian entries.

Similar ideas allow us to treat a \term{matrix Rademacher series}, a sum of fixed matrices modulated by random signs.
(Recall that a \term{Rademacher random variable} takes the values $\pm 1$ with equal probability.)
The results in this case are almost identical with the results for matrix Gaussian series,
but they allow us to consider new problems.
As an example, we can study the expected spectral norm of a fixed real matrix after flipping
the signs of the entries at random.

\subsubsection{Overview}

In \S\ref{sec:matrix-gauss-rect}, we begin
with an overview of our results for matrix Gaussian
series; very similar results also hold for matrix Rademacher series.
Afterward, we discuss the accuracy of the theoretical bounds.
The subsequent sections, \S\S\ref{sec:gauss-matrices}--\ref{sec:toeplitz},
describe what the matrix concentration inequalities
tell us about some classical and not-so-classical examples of random matrices.
Section~\ref{sec:maxqp} includes an overview of a more substantial
application in combinatorial optimization.  The final part \S\ref{sec:matrix-gauss-proof}
contains detailed proofs of the bounds.
We conclude with bibliographical notes.

\section{A Norm Bound for Random Series with Matrix Coefficients} \label{sec:matrix-gauss-rect}

Consider a finite sequence $\{ b_k \}$ of real numbers and a finite sequence $\{ \gamma_k \}$ of independent standard normal random variables.  Form the random series $Z = \sum_k \gamma_k b_k$.

A routine invocation of the scalar Laplace transform method demonstrates that
\begin{equation} \label{eqn:real-gauss}
\Prob{ \abs{Z} \geq t }
	\leq 2\, \exp\left( \frac{-t^2}{2v} \right)
\quad\text{where $v = \Var(Z) = \sum\nolimits_k b_k^2$.}
\end{equation}

It turns out that the inequality~\eqref{eqn:real-gauss} extends directly to the matrix setting.

\begin{thm}[Matrix Gaussian \& Rademacher Series] \label{thm:matrix-gauss-rect}
Consider a finite sequence $\{ \mtx{B}_k \}$ of fixed complex matrices with dimension $d_1 \times d_2$,
and let $\{\gamma_k\}$ be a finite sequence of independent standard normal variables.
Introduce the matrix Gaussian series
\begin{equation} \label{eqn:matrix-gauss-series}
\mtx{Z} = \sum\nolimits_k \gamma_k \mtx{B}_k.
\end{equation}
Let $v(\mtx{Z})$ be the matrix variance statistic of the sum:

\begin{align}
v(\mtx{Z}) &= \max\left\{ \norm{ \smash{\Expect ( \mtx{ZZ}^\adj )} }, \
	\norm{ \smash{\Expect ( \mtx{Z}^\adj \mtx{Z} )} } \right\}  \label{eqn:matrix-gauss-sigma2-rect} \\
	&= \max\left\{ \norm{ \sum\nolimits_k \mtx{B}_k \mtx{B}_k^\adj }, \
	\norm{ \sum\nolimits_k \mtx{B}_k^\adj \mtx{B}_k } \right\}. \label{eqn:matrix-gauss-rect-var-calc}
\end{align}
Then  
\begin{equation} \label{eqn:matrix-gauss-expect-rect}
\Expect \norm{ \mtx{Z} }
	\leq \sqrt{2 v(\mtx{Z}) \log (d_1 + d_2)}.
\end{equation}
Furthermore, for all $t \geq 0$,
\begin{equation} \label{eqn:matrix-gauss-tail-rect}
\Prob{ \norm{ \mtx{Z} } \geq t}
	\leq (d_1 + d_2) \, \exp\left( \frac{- t^2}{2v(\mtx{Z})} \right).
\end{equation}
The same bounds hold when we replace $\{\gamma_k\}$ by a finite sequence $\{\varrho_k\}$ of independent Rademacher random variables.
\end{thm}

\noindent
The proof of Theorem~\ref{thm:matrix-gauss-rect} appears below
in~\S\ref{sec:matrix-gauss-proof}.

\subsection{Discussion}

Let us take a moment to discuss the content of Theorem~\ref{thm:matrix-gauss-rect}.
The main message is that the expectation of $\norm{\mtx{Z}}$
is controlled by the matrix variance statistic $v(\mtx{Z})$.  Furthermore,
$\norm{\mtx{Z}}$ has a subgaussian tail whose decay rate depends on $v(\mtx{Z})$.

The matrix variance statistic $v(\mtx{Z})$ defined in~\eqref{eqn:matrix-gauss-sigma2-rect}
specializes the general formulation~\eqref{eqn:matrix-variance-rect}.  The second
expression~\eqref{eqn:matrix-gauss-rect-var-calc} follows from the additivity
property~\eqref{eqn:indep-sum-rect} for the variance of an independent sum.
When the summands are Hermitian, observe that the two terms in the maximum coincide.

The formulas~\eqref{eqn:matrix-gauss-sigma2-rect} and~\eqref{eqn:matrix-gauss-rect-var-calc}
are a direct extension of the variance that arises in the scalar bound~\eqref{eqn:real-gauss}.

As compared with~\eqref{eqn:real-gauss},
a new feature of the bound~\eqref{eqn:matrix-gauss-tail-rect} is the
dimensional factor $d_1 + d_2$.  When $d_1 = d_2 = 1$,
the matrix bound reduces to the scalar result~\eqref{eqn:real-gauss}.

In this case, at least, we have lost nothing by lifting the Laplace transform
method to matrices.

The behavior of the matrix tail bound~\eqref{eqn:matrix-gauss-tail-rect}
is more subtle than the behavior of the scalar tail bound~\eqref{eqn:real-gauss}.
See Figure~\ref{fig:gauss-tail-schema} for an illustration.

<!-- pdf-page: 2 -->
\begin{figure}
\begin{center}
\includegraphics[width=0.9\textwidth]{art/gauss-tail-schema-3.pdf}
\begin{caption}{
\textbf{Schematic of tail bound for matrix Gaussian series.}
Consider a matrix Gaussian series $\mtx{Z}$ with dimension $d_1 \times d_2$.
The tail probability $\Prob{ \norm{\mtx{Z}} \geq t }$ admits the upper bound
$(d_1 + d_2) \, \exp(-t^2/(2v(\mtx{Z})))$, marked as a dark blue curve.
This estimate provides no information below the level $t = \sqrt{2 v(\mtx{Z}) \log(d_1 + d_2)}$.
This value, the dark red vertical line,
coincides with the upper bound~\eqref{eqn:matrix-gauss-expect-rect} for $\Expect \norm{\mtx{Z}}$.
As $t$ increases beyond this point, the tail probability decreases at a subgaussian
rate with variance on the order of $v(\mtx{Z})$.}
\label{fig:gauss-tail-schema}
\end{caption}
\end{center}
\end{figure}

\subsection{Optimality of the Bounds for Matrix Gaussian Series} \label{sec:matrix-gauss-sharp}

One may wonder whether Theorem~\ref{thm:matrix-gauss-rect} provides accurate information about the behavior of a matrix Gaussian series.  The answer turns out to be complicated.  Here is the executive summary: the expectation bound~\eqref{eqn:matrix-gauss-expect-rect} is always quite good, but the tail bound~\eqref{eqn:matrix-gauss-tail-rect}
is sometimes quite bad.  The rest of this section expands on these claims.

\subsubsection{The Expectation Bound}

Let $\mtx{Z}$ be a matrix Gaussian series of the form~\eqref{eqn:matrix-gauss-series}.  We will argue that
\begin{equation} \label{eqn:matrix-gauss-expect-two-sided}
v(\mtx{Z})
	\quad\leq\quad
	\Expect \normsq{\mtx{Z}}
	\quad\leq\quad
	2 v(\mtx{Z}) (1 + \log(d_1 + d_2)).
\end{equation}
In other words, the matrix variance $v(\mtx{Z})$ is roughly the correct scale for $\normsq{\mtx{Z}}$.
This pair of estimates is a significant achievement because it is quite challenging to compute the
norm of a matrix Gaussian series in general.  Indeed, the literature contains very few examples
where explicit estimates are available, especially if one desires reasonable constants.

We begin with the lower bound in~\eqref{eqn:matrix-gauss-expect-two-sided},
which is elementary.  Indeed, since the spectral norm is convex,
Jensen's inequality ensures that
$$
\Expect \normsq{\mtx{Z}}
	= \Expect{} \max\big\{ \norm{\smash{\mtx{ZZ}^\adj}}, \ \norm{\smash{\mtx{Z}^\adj\mtx{Z}}} \big\}
	\geq \max\big\{ \norm{\smash{\Expect(\mtx{ZZ}^\adj)}}, \ \norm{\smash{\Expect(\mtx{Z}^\adj\mtx{Z})}} \big\}
	= v(\mtx{Z}).
$$
The first identity follows from~\eqref{eqn:spectral-norm-square}, and the last
is the definition~\eqref{eqn:matrix-variance-rect} of the matrix variance.

The upper bound in~\eqref{eqn:matrix-gauss-expect-two-sided} is
a consequence of the tail bound~\eqref{eqn:matrix-gauss-tail-rect}:
$$
\begin{aligned}
\Expect{} \normsq{\mtx{Z}}
	&= \int_0^\infty 2t \, \Prob{ \norm{\mtx{Z}} \geq t } \idiff{t} \\
	&\leq \int_0^E 2t \idiff{t} + 2 (d_1 + d_2) \int_E^\infty t \, \econst^{-t^2/(2v(\mtx{Z}))} \idiff{t}
	= E^2 + 2v(\mtx{Z}) \, (d_1 + d_2) \, \econst^{-E^2/(2v(\mtx{Z}))}. \phantom{\int_0^E}
\end{aligned}
$$
In the first step, rewrite the expectation using integration by parts, and then split the integral
at a positive number $E$.  In the first term, we bound the probability by one, while the second term
results from the tail bound~\eqref{eqn:matrix-gauss-tail-rect}.  Afterward, we compute the integrals
explicitly.  Finally, select $E^2 = 2v(\mtx{Z}) \log(d_1+d_2)$ to complete the proof
of~\eqref{eqn:matrix-gauss-expect-two-sided}.

\subsubsection{About the Dimensional Factor}

At this point, one may ask whether it is possible to improve either side of the inequality~\eqref{eqn:matrix-gauss-expect-two-sided}.  The answer is negative unless we have additional information about the Gaussian series
beyond the matrix variance statistic $v(\mtx{Z})$.

Indeed, for arbitrarily large dimensions $d_1$ and $d_2$, we can exhibit a matrix Gaussian series where
the left-hand inequality in~\eqref{eqn:matrix-gauss-expect-two-sided} is correct.
That is, $\Expect \normsq{\mtx{Z}} \approx v(\mtx{Z})$ with no additional dependence on the dimensions $d_1$ or $d_2$.
One such example appears below in~\S\ref{sec:marcenko-pastur}.

At the same time, for arbitrarily large dimensions $d_1$ and $d_2$,
we can construct a matrix Gaussian series where the right-hand
inequality in~\eqref{eqn:matrix-gauss-expect-two-sided} is correct.
That is, $\Expect \normsq{\mtx{Z}} \approx v(\mtx{Z}) \log(d_1 + d_2)$.
See~\S\ref{sec:toeplitz} for an example.

We can offer a rough intuition about how these two situations differ from each other.
The presence or absence of the dimensional factor $\log(d_1 + d_2)$

depends on how much the coefficients $\mtx{B}_k$ in the matrix Gaussian series $\mtx{Z}$ 
commute with each other.  More commutativity leads to a logarithm,
while less commutativity can sometimes result in cancelations that obliterate the logarithm.

It remains a major open question to find a simple quantity, computable from the coefficients $\mtx{B}_k$,
that decides whether $\Expect \normsq{\mtx{Z}}$ contains a dimensional factor or not.

In Chapter~\ref{chap:intrinsic}, we will describe a technique that allows us to moderate the dimensional factor in~\eqref{eqn:matrix-gauss-expect-two-sided} for some types of matrix series.  But we cannot remove the dimensional factor entirely with current technology.

\subsubsection{The Tail Bound}

What about the tail bound~\eqref{eqn:matrix-gauss-tail-rect} for the norm of the Gaussian series?  Here, our results are less impressive.  It turns out that the large-deviation behavior of the spectral norm of a matrix Gaussian series $\mtx{Z}$ is controlled by a
statistic $v_\star(\mtx{Z})$ called the \term{weak variance}:
$$
v_{\star}(\mtx{Z})
	= \sup_{\norm{\vct{u}}=\norm{\vct{w}}=1} \Expect{} \abssq{ \smash{\vct{u}^\adj \mtx{Z} \vct{w}} }
	= \sup_{\norm{\vct{u}}=\norm{\vct{w}}=1} \sum\nolimits_k \abssq{ \smash{\vct{u}^\adj \mtx{B}_k \vct{w}} }.
$$
The best general inequalities between the matrix variance statistic and the weak variance are
$$
v_{\star}(\mtx{Z}) \quad\leq\quad v(\mtx{Z}) \quad\leq\quad \min\{ d_1, d_2 \} \cdot v_{\star}(\mtx{Z})
$$
There are examples of matrix Gaussian series that saturate the lower or the upper inequality.

<!-- pdf-page: 3 -->
The classical concentration inequality~\cite[Thm.~5.6]{BLM13:Concentration-Inequalities}
for a function of independent Gaussian random variables implies that
\begin{equation} \label{eqn:gauss-concentration}
\Prob{ \norm{\mtx{Z}} \geq \Expect \norm{\mtx{Z}} + t }
	\leq \econst^{-t^2/(2v_{\star}(\mtx{Z}))}.
\end{equation}
Let us emphasize that the bound~\eqref{eqn:gauss-concentration} provides no information about $\Expect \norm{\mtx{Z}}$;
it only tells us about the probability that $\norm{\mtx{Z}}$ is larger than its mean.

Together, the last two displays indicate that the exponent in the
tail bound~\eqref{eqn:matrix-gauss-tail-rect} is sometimes too big by a factor $\min\{d_1,d_2\}$.
Therefore, a direct application of Theorem~\ref{thm:matrix-gauss-rect} can badly overestimate
the tail probability $\Prob{ \norm{\mtx{Z}} > t }$ when the level $t$ is large.

Fortunately, this problem is less pronounced with the matrix Chernoff inequalities of Chapter~\ref{chap:matrix-chernoff} and the matrix Bernstein inequalities of Chapter~\ref{chap:matrix-bernstein}.

\subsubsection{Expectations and Tails}

When studying concentration of random variables, it is quite common that we need to use one method
to assess the expected value of the random variable and a separate technique to determine the
probability of a large deviation.

\begin{quotation}
\noindent
\textbf{The primary value of matrix concentration inequalities inheres in the estimates
that they provide for the expectation of the spectral norm
(or maximum eigenvalue or minimum eigenvalue) of a random matrix.}
\end{quotation}

\noindent
In many cases, matrix concentration bounds provide reasonable information about
the tail decay, but there are other situations where the tail bounds are feeble.
In this event, we recommend applying a scalar concentration inequality to
control the tails.

\section{Example: Some Gaussian Matrices} \label{sec:gauss-matrices}

Let us try out our methods on two types of Gaussian matrices that have been studied extensively in the classical literature on random matrix theory.  In these cases, precise information about the spectral distribution is available, which provides a benchmark for assessing our results.  We find that bounds based on Theorem~\ref{thm:matrix-gauss-rect}
lead to very reasonable estimates, but they are not sharp.  The advantage of our approach is that it applies to every example, whereas we are making comparisons with specialized techniques that only illuminate individual cases.
Similar conclusions hold for matrices with independent Rademacher entries.

\subsection{Gaussian Wigner Matrices} \label{sec:wigner}

We begin with a family of Gaussian Wigner matrices.  A $d \times d$ matrix $\mtx{W}_d$ from this ensemble is real-symmetric with a zero diagonal; the entries above the diagonal are independent normal variables with mean zero and variance one:
$$
\mtx{W}_d = \begin{bmatrix}
	0 & \gamma_{12} & \gamma_{13} &  \dots & \gamma_{1d} \\
	\gamma_{12} & 0 & \gamma_{23} & \dots  & \gamma_{2d} \\
	\gamma_{13} & \gamma_{23} & 0 &  & \gamma_{3d} \\
	\vdots & \vdots && \ddots & \vdots \\
	\gamma_{1d} & \gamma_{2d} & \dots & \gamma_{d-1,d} & 0
\end{bmatrix}
$$
where $\{ \gamma_{jk} : 1 \leq j < k \leq d \}$ is an independent family of standard normal variables.  We can represent this matrix compactly as a Gaussian series:
\begin{equation} \label{eqn:gauss-wigner}
\mtx{W}_d =
\sum\limits_{1 \leq j < k \leq d} \gamma_{jk} (\mathbf{E}_{jk} + \mathbf{E}_{kj}).
\end{equation}
The norm of a Wigner matrix satisfies
\begin{equation} \label{eqn:gauss-wigner-true}
\frac{1}{\sqrt{d}} \, \norm{\mtx{W}_d} \longrightarrow 2
\quad\text{as $d \to \infty$, almost surely}.
\end{equation}
For example, see~\cite[Thm.~5.1]{BS10:Spectral-Analysis}.
To make~\eqref{eqn:gauss-wigner-true} precise,
we assume that $\{\mtx{W}_d\}$ is an independent sequence of Gaussian Wigner matrices, indexed by the dimension $d$.

Theorem~\ref{thm:matrix-gauss-herm} provides a simple way to bound the norm of a Gaussian Wigner matrix.  We just need to compute the matrix variance statistic $v(\mtx{W}_d)$.
The formula~\eqref{eqn:matrix-gauss-rect-var-calc} for $v(\mtx{W}_d)$ asks us to form the sum of the squared coefficients from the representation~\eqref{eqn:gauss-wigner}:
$$
\sum\limits_{1 \leq j < k \leq d} (\mathbf{E}_{jk} + \mathbf{E}_{kj})^2
	= \sum\limits_{1 \leq j < k \leq d} (\mathbf{E}_{jj} + \mathbf{E}_{kk})
	= (d-1) \, \Id_d.
$$
Since the terms in~\eqref{eqn:gauss-wigner} are Hermitian, we have only one sum of squares to consider.
We have also used the facts that $\mathbf{E}_{jk} \mathbf{E}_{kj} = \mathbf{E}_{jj}$ while $\mathbf{E}_{jk} \mathbf{E}_{jk} = \mtx{0}$ because of the condition $j < k$ in the limits of summation.

We see that
$$
v(\mtx{W}_d) 
	= \norm{ \sum\limits_{1 \leq j < k \leq d} (\mathbf{E}_{jk} + \mathbf{E}_{kj})^2 }
	= \norm{ (d-1) \, \Id_d } = d-1.
$$
The bound~\eqref{eqn:matrix-gauss-expect-rect} for the expectation of the norm gives
\begin{equation} \label{eqn:gauss-wigner-est}
\Expect \norm{\mtx{W}_d} \leq \sqrt{2 (d-1) \log(2d)}.
\end{equation}
In conclusion, our techniques overestimate $\norm{\mtx{W}_d}$ by a factor of about $\sqrt{0.5 \log d}$.
The result~\eqref{eqn:gauss-wigner-est} is not perfect, but it only takes two lines of work.
In contrast, the classical result~\eqref{eqn:gauss-wigner-true} depends on a long moment
calculation that involves challenging combinatorial arguments.

\subsection{Rectangular Gaussian Matrices} \label{sec:marcenko-pastur}

Next, we consider a $d_1 \times d_2$ rectangular matrix with independent standard normal entries:
$$
\mtx{G} = \begin{bmatrix}
	\gamma_{11} & \gamma_{12} & \gamma_{13} & \dots & \gamma_{1d_2} \\
	\gamma_{21} & \gamma_{22} & \gamma_{23} & \dots & \gamma_{2d_2} \\
	\vdots & \vdots &&\ddots & \vdots \\
	\gamma_{d_1 1} & \gamma_{d_1 2} & \gamma_{d_1 3} & \dots & \gamma_{d_1d_2} \\
\end{bmatrix}
$$
where $\{ \gamma_{jk} \}$

is an independent family of standard normal variables.  We can express this
matrix efficiently using a Gaussian series:
\begin{equation} \label{eqn:mp-gauss-series}
\mtx{G} = \sum_{j=1}^{d_1} \sum_{k=1}^{d_2} \gamma_{jk} \mathbf{E}_{jk},
\end{equation}

<!-- pdf-page: 4 -->
There is an elegant estimate~\cite[Thm.~2.13]{DS02:Local-Operator} for the norm of this matrix:
\begin{equation} \label{eqn:gauss-rect-true}
\Expect \norm{\mtx{G}} \leq \sqrt{d_1} + \sqrt{d_2}.
\end{equation}
The inequality~\eqref{eqn:gauss-rect-true} is sharp when $d_1$ and $d_2$ tend to infinity while the ratio $d_1/d_2 \to \mathrm{const}$.  See~\cite[Thm.~5.8]{BS10:Spectral-Analysis} for details.

Theorem~\ref{thm:matrix-gauss-rect} yields another bound on the expected norm of the matrix $\mtx{G}$.
In order to compute the matrix variance statistic $v(\mtx{G})$,
we calculate the sums of the squared coefficients
from the representation~\eqref{eqn:mp-gauss-series}:
$$
\begin{aligned}
\sum_{j=1}^{d_1} \sum_{k=1}^{d_2} \mathbf{E}_{jk} \mathbf{E}_{jk}^\adj
	&= \sum_{j=1}^{d_1} \sum_{k=1}^{d_2} \mathbf{E}_{jj}
	= d_2 \, \Id_{d_1}, \quad\text{and} \\
\sum_{j=1}^{d_1} \sum_{k=1}^{d_2} \mathbf{E}_{jk}^\adj \mathbf{E}_{jk}
	&= \sum_{j=1}^{d_1} \sum_{k=1}^{d_2} \mathbf{E}_{kk}
	= d_1 \, \Id_{d_2}.
\end{aligned}
$$
The matrix variance statistic~\eqref{eqn:matrix-gauss-sigma2-rect} satisfies
$$
v(\mtx{G}) = \max\big\{ \norm{ \smash{d_2 \, \Id_{d_1}} }, \ \norm{ \smash{d_1 \, \Id_{d_2}} } \big\}
	= \max\{ d_1, \ d_2 \}.
$$
We conclude that
\begin{equation} \label{eqn:gauss-rect-est}
\Expect \norm{ \mtx{G} } \leq \sqrt{2 \max\{d_1, \ d_2\} \log(d_1 + d_2)}.
\end{equation}
The leading term is roughly correct because
$$
\sqrt{d_1} + \sqrt{d_2}
\leq 2 \sqrt{\max\{d_1, \ d_2\}}
\leq 2 \left( \sqrt{d_1} + \sqrt{d_2} \right). 
$$
The logarithmic factor in~\eqref{eqn:gauss-rect-est} does not belong, but it is rather small in comparison with the leading terms.  Once again, we have produced a reasonable result with a short argument based on general principles.

\section{Example: Matrices with Randomly Signed Entries} \label{sec:rdm-sign-mtx}

Next, we turn to an example that is superficially similar with the matrix discussed in~\S\ref{sec:marcenko-pastur} but is less understood.  Consider a fixed $d_1 \times d_2$ matrix $\mtx{B}$ with real entries, and let $\{ \varrho_{jk} \}$ be an independent family of Rademacher random variables.  Consider the $d_1 \times d_2$ random matrix
$$
\mtx{B}_{\pm} = \sum_{j=1}^{d_1} \sum_{k=1}^{d_2} \varrho_{jk} b_{jk} \mathbf{E}_{jk}
$$
In other words, we obtain the random matrix $\mtx{B}_{\pm}$ by randomly flipping the sign of each entry of $\mtx{B}$.

The expected norm of this matrix satisfies the bound
\begin{equation} \label{eqn:rdm-sign-matrix-true}
\Expect \norm{\mtx{B}_{\pm}} \leq \textrm{Const} \cdot  v^{1/2} \cdot \log^{1/4} \min\{ d_1, \ d_2 \},
\end{equation}
where the leading factor $v^{1/2}$ satisfies
\begin{equation} \label{eqn:rdm-sign-matrix-var}
v = \max\left\{ \max\nolimits_j \normsq{ \smash{\vct{b}_{j:}} }, \ \max\nolimits_k \normsq{ \vct{b}_{:k} } \right\}.
\end{equation}
We have written $\mtx{b}_{j:}$ for the $j$th row of $\mtx{B}$ and $\mtx{b}_{:k}$ for the $k$th column of $\mtx{B}$.  In other words, the expected norm of a matrix with randomly signed entries is comparable with the maximum $\ell_2$ norm achieved by any row or column.  There are cases where the bound~\eqref{eqn:rdm-sign-matrix-true} admits a matching lower bound.
These results appear in~\cite[Thms.~3.1, 3.2]{Seg00:Expected-Norm} and~\cite[Cor.~4.7]{BV14:Sharp-Nonasymptotic}.

Theorem~\ref{thm:matrix-gauss-rect} leads to a quick proof of a slightly weaker result.  We simply need to compute the
matrix variance statistic $v(\mtx{B}_{\pm})$.  To that end, note that
$$
\sum_{j=1}^{d_1} \sum_{k=1}^{d_2} (b_{jk} \mathbf{E}_{jk})(b_{jk} \mathbf{E}_{jk})^\adj 
	= \sum_{j=1}^{d_1} \left(\sum_{k=1}^{d_2} \abssq{\smash{b_{jk}}}\right) \mathbf{E}_{jj}
	= \begin{bmatrix} \normsq{ \vct{b}_{1:}} && \\ & \ddots & \\ &&\norm{\smash{\vct{b}_{d_1:}}}^2
	\end{bmatrix}.
$$
Similarly,
$$
\sum_{j=1}^{d_1} \sum_{k=1}^{d_2} (b_{jk} \mathbf{E}_{jk})^{\adj}(b_{jk} \mathbf{E}_{jk}) 
	= \sum_{k=1}^{d_2} \left(\sum_{j=1}^{d_1} \abssq{\smash{b_{jk}}}\right) \mathbf{E}_{kk}
	= \begin{bmatrix} \normsq{ \vct{b}_{:1}} && \\ & \ddots & \\ &&\norm{\smash{\vct{b}_{:d_2}}}^2
	\end{bmatrix}.
$$
Therefore, using the formula~\eqref{eqn:matrix-gauss-rect-var-calc}, we find that
\begin{align*}
v( \mtx{B}_{\pm} ) &=
	\max\left\{ \norm{ \sum_{j=1}^{d_1} \sum_{k=1}^{d_2} (b_{jk} \mathbf{E}_{jk})(b_{jk} \mathbf{E}_{jk})^\adj }, \
	\norm{ \sum_{j=1}^{d_1} \sum_{k=1}^{d_2} (b_{jk} \mathbf{E}_{jk})^{\adj}(b_{jk} \mathbf{E}_{jk}) }
	\right\} \\

&= \max\left\{ \max\nolimits_j \norm{\smash{\vct{b}_{j:}}}^2, \
		\max\nolimits_k \norm{\smash{\vct{b}_{:k}}}^2 \right\}.
\end{align*}

We see that $v(\mtx{B}_{\pm})$ coincides with $v$, the leading term~\eqref{eqn:rdm-sign-matrix-var} in the established estimate~\eqref{eqn:rdm-sign-matrix-true}!  Now, Theorem~\ref{thm:matrix-gauss-rect} delivers the bound
\begin{equation} \label{eqn:rdm-sign-matrix-est}
\Expect \norm{\mtx{B}_{\pm}}
	\leq \sqrt{2 v(\mtx{B}_{\pm}) \log(d_1 + d_2)}.
\end{equation}
Observe that the estimate~\eqref{eqn:rdm-sign-matrix-est} for the norm matches the correct bound~\eqref{eqn:rdm-sign-matrix-true} up to the logarithmic factor. Yet again, we obtain a result that is respectably close to the optimal one, even though it is not quite sharp.

The main advantage of using results like Theorem~\ref{thm:matrix-gauss-rect} to analyze this random matrix is that we can obtain a good result with a minimal amount of arithmetic.  The  analysis that leads to~\eqref{eqn:rdm-sign-matrix-true} involves a specialized combinatorial argument.

\section{Example: Gaussian Toeplitz Matrices} \label{sec:toeplitz}

Matrix concentration inequalities offer an effective tool for analyzing random matrices whose dependency structures are more complicated than those of the classical ensembles.  In this section, we consider Gaussian Toeplitz matrices, which have applications in signal processing.

We construct an (unsymmetric) $d \times d$ Gaussian Toeplitz matrix $\mtx{\Gamma}_d$ by populating the first row and first column of the matrix with independent standard normal variables; the entries along each diagonal of the matrix take the same value:
$$
\mtx{\Gamma}_d = \begin{bmatrix}
	\gamma_0 & \gamma_1 & & \dots &&  \gamma_{d-1} \\
	\gamma_{-1} & \gamma_0 & \gamma_1 & &&  \\
	 & \gamma_{-1} & \gamma_0 & \gamma_1 && \vdots \\
	 \vdots & & \ddots & \ddots & \ddots & \\
	 & & & \gamma_{-1} & \gamma_0 & \gamma_1 \\
	\gamma_{-(d-1)} & & \dots & & \gamma_{-1} & \gamma_0
\end{bmatrix}
$$
where $\{ \gamma_k \}$

<!-- pdf-page: 5 -->
is an independent family of standard normal variables.
As usual, we represent the Gaussian Toeplitz matrix as a matrix Gaussian series:
\begin{equation} \label{eqn:gauss-toeplitz-cpt}
\mtx{\Gamma}_d = \gamma_0 \, \Id + \sum_{k=1}^{d-1} \gamma_k \mtx{C}^k
	+ \sum_{k=1}^{d-1} \gamma_{-k} \big(\mtx{C}^k \big)^\adj,
\end{equation}
where $\mtx{C} \in \mathbb{M}_d$ denotes the shift-up operator acting on $d$-dimensional column vectors:
$$
\mtx{C} = \begin{bmatrix} 0 & 1 \\ & 0 & 1 \\ && \ddots & \ddots \\ &&& 0 & 1 \\
&&&& 0 \end{bmatrix}.
$$

It follows that $\mtx{C}^k$ shifts a vector up by $k$ places, introducing zeros at the bottom,
while $(\mtx{C}^k)^\adj$ shifts a vector down by $k$ places, introducing zeros at the top.

We can analyze this example quickly using Theorem~\ref{thm:matrix-gauss-rect}.  First, note that
$$
\big(\mtx{C}^k\big)\big(\mtx{C}^k\big)^\adj = \sum_{j=1}^{d-k} \mathbf{E}_{jj}
\quad\text{and}\quad
\big(\mtx{C}^k\big)^\adj \big(\mtx{C}^k\big) = \sum_{j=k+1}^d \mathbf{E}_{jj}.
$$
To obtain the matrix variance statistic~\eqref{eqn:matrix-gauss-rect-var-calc}, we calculate the sum of the squares of the coefficient matrices that appear in~\eqref{eqn:gauss-toeplitz-cpt}.  In this instance, the two terms in the variance are the same.  We find that
\begin{multline}
\Id^2 + \sum_{k=1}^{d-1} \big(\mtx{C}^k\big)\big(\mtx{C}^k\big)^{\adj} + \sum_{k=1}^{d-1} \big(\mtx{C}^k\big)^\adj \big(\mtx{C}^k\big)
	= \Id + \sum_{k=1}^{d-1} \left[ \sum_{j=1}^{d-k} \mathbf{E}_{jj} + \sum_{j=k+1}^{d} \mathbf{E}_{jj} \right] \\
	= \sum_{j=1}^d \left[ 1 + \sum_{k=1}^{d-j} 1 + \sum_{k=1}^{j-1} 1 \right] \mathbf{E}_{jj}
	= \sum_{j=1}^d (1 + (d-j) + (j-1)) \, \mathbf{E}_{jj}
	= d \, \Id_d.
\end{multline}

In the second line, we (carefully) switch the order of summation and rewrite the identity matrix as a sum of diagonal standard basis matrices.  We reach
$$
v(\mtx{\Gamma}_d) = \norm{ d \, \Id_d } = d.
$$
An application of Theorem~\ref{thm:matrix-gauss-rect} leads us to conclude that
\begin{equation} \label{eqn:gauss-toeplitz-est}
\Expect \norm{ \mtx{\Gamma}_d } \leq \sqrt{2d\log(2d)}.
\end{equation}
It turns out that the inequality~\eqref{eqn:gauss-toeplitz-est} is correct up to the precise value of the constant, which does not seem to be known.  Nevertheless, the limiting value is available for the top eigenvalue of a (scaled) symmetric Toeplitz matrix whose first row contains independent standard normal variables~\cite[Thm.~1]{SV13:Top-Eigenvalue}.  From this
result, we may conclude that
$$
0.8288 \quad\leq\quad
	\frac{\Expect \norm{ \mtx{\Gamma}_d }}{ \sqrt{2d\log(2d)} }
	\quad\leq\quad 1
	\quad\text{as $d \to \infty$.}
$$
Here, we take $\{\mtx{\Gamma}_d\}$ to be a sequence of unsymmetric Gaussian Toeplitz matrices, indexed by the ambient dimension $d$.  Our simple argument gives the right scaling for this problem, and our estimate for the constant lies within 21\% of the optimal value!

\section{Application: Rounding for the MaxQP Relaxation} \label{sec:maxqp}

Our final application involves a more substantial question from combinatorial optimization.  One of the methods that has been proposed for solving a certain optimization problem leads to a matrix Rademacher series, and the analysis of this method requires the spectral norm bounds from Theorem~\ref{thm:matrix-gauss-rect}.  A detailed treatment would take us too far afield, so we just sketch the context and indicate how the random matrix arises.

There are many types of optimization problems that are computationally difficult to solve exactly.  One approach to solving these problems is to enlarge the constraint set in such a way that the problem becomes tractable, a process called ``relaxation.''  After solving the relaxed problem, we can use a randomized ``rounding'' procedure to map the solution back to the constraint set for the original problem.  If we can perform the rounding step without changing the value of the objective function substantially, then the rounded solution is also a decent solution to the original optimization problem.

One difficult class of optimization problems has a matrix decision variable, and it requires us to maximize a quadratic form in the matrix variable subject to a set of convex quadratic constraints and a spectral norm constraint~\cite{Nem07:Sums-Random}.  This problem is referred to as \textsc{MaxQP}.  The desired solution $\mtx{B}$ to this problem is a $d_1 \times d_2$ matrix.  The solution needs to satisfy several different requirements, but we focus on the condition that $\norm{\mtx{B}} \leq 1$.

There is a natural relaxation of the \textsc{MaxQP} problem.  When we solve the relaxation, we obtain a family $\{ \mtx{B}_k : k = 1, 2, \dots, n \}$ of $d_1 \times d_2$ matrices that satisfy the constraints
\begin{equation} \label{eqn:maxqp-constraint}
\sum_{k=1}^n \mtx{B}_k \mtx{B}_k^\adj \psdle \Id_{d_1}
\quad\text{and}\quad
\sum_{k=1}^n \mtx{B}_k^\adj \mtx{B}_k \psdle \Id_{d_2}.
\end{equation}
In fact, these two bounds are part of the specification of the relaxed problem.  To round the family of matrices back to a solution of the original problem, we form the random matrix
$$
\mtx{Z} = \alpha \sum_{k=1}^n \varrho_k \mtx{B}_k,
$$
where $\{ \varrho_k \}$ is an independent family of Rademacher random variables.  The scaling factor $\alpha > 0$ can be adjusted to guarantee that the norm constraint $\norm{\mtx{Z}} \leq 1$ holds with high probability.

What is the expected norm of $\mtx{Z}$?  Theorem~\ref{thm:matrix-gauss-rect} yields
$$
\Expect \norm{ \mtx{Z} }
	\leq \sqrt{ 2 v(\mtx{Z}) \log(d_1 + d_2) }.
$$
Here, the matrix variance statistic satisfies
$$
v(\mtx{Z}) = \alpha^2 \, \max\left\{ \norm{ \sum_{k=1}^n \mtx{B}_k \mtx{B}_k^\adj }, \
	\norm{ \sum_{k=1}^n \mtx{B}_k^\adj \mtx{B}_k } \right\}
	\leq \alpha^2,
$$
owing to the constraint~\eqref{eqn:maxqp-constraint} on the matrices $\mtx{B}_1, \dots, \mtx{B}_n$.  It follows that the scaling parameter $\alpha$ should satisfy
$$
\alpha^2 = \frac{1}{2 \log(d_1 + d_2)}
$$
to ensure that $\Expect \norm{\mtx{Z}} \leq 1$.  For this choice of $\alpha$, the rounded solution $\mtx{Z}$ obeys the spectral norm constraint on average.  By using the tail bound~\eqref{eqn:matrix-gauss-tail-rect}, we can even obtain high-probability estimates for the norm of the rounded solution $\mtx{Z}$.

<!-- pdf-page: 6 -->
The important fact here is that the scaling parameter $\alpha$ is usually small as compared with the other parameters of the problem ($d_1, d_2$, $n$, and so forth).  Therefore, the scaling does not have a massive effect on the value of the objective function.  Ultimately, this approach leads to a technique for solving the \textsc{MaxQP} problem that produces a feasible point whose objective value is within a factor of $\sqrt{2 \log(d_1+d_2)}$ of the maximum objective value possible.

\section{Analysis of Matrix Gaussian \& Rademacher Series}
\label{sec:matrix-gauss-proof}

We began this chapter with a concentration inequality,
Theorem~\ref{thm:matrix-gauss-rect},
for the norm of a matrix Gaussian series,
and we have explored a number of different applications of this result.
This section contains a proof of this theorem.

\subsection{Random Series with Hermitian Coefficients}

As the development in Chapter~\ref{chap:matrix-lt} suggests,
random Hermitian matrices provide the natural setting for
establishing matrix concentration inequalities.
Therefore, we begin our treatment with a detailed statement of the matrix concentration
inequality for a Gaussian series with Hermitian matrix coefficients.

\begin{thm}[Matrix Gaussian \& Rademacher Series: The Hermitian Case] \label{thm:matrix-gauss-herm}
Consider a finite sequence $\{ \mtx{A}_k \}$ of fixed Hermitian matrices with dimension $d$,
and let $\{ \gamma_k \}$ be a finite sequence of independent standard normal variables.
Introduce the matrix Gaussian series
$$
\mtx{Y} = \sum\nolimits_k \gamma_k \mtx{A}_k.
$$
Let $v(\mtx{Y})$ be the matrix variance statistic of the sum:
\begin{equation} \label{eqn:matrix-gauss-sigma2}
v(\mtx{Y})
= \norm{ \smash{\Expect{} \mtx{Y}^2} }
 = \norm{ \sum\nolimits_k \mtx{A}_k^2 }.
\end{equation}
Then 
\begin{align}
\Expect \lambda_{\max}\left( \mtx{Y} \right)
	&\leq \sqrt{2 v(\mtx{Y}) \log d}.

\label{eqn:matrix-gauss-upper-expect}

\end{align}
Furthermore, for all $t \geq 0$,
\begin{align}
\Prob{ \lambda_{\max}\left( \mtx{Y} \right) \geq t }
	&\leq d \, \exp\left( \frac{-t^2}{2 v(\mtx{Y})} \right).

\label{eqn:matrix-gauss-upper-tail}

\end{align}
The same bounds hold when we replace $\{\gamma_k\}$ by a finite sequence of independent Rademacher random variables.
\end{thm}

\noindent
The proof of this result occupies the rest of the section.

\subsection{Discussion}

Before we proceed to the analysis, let us take a moment to compare Theorem~\ref{thm:matrix-gauss-herm}
with the result for general matrix series, Theorem~\ref{thm:matrix-gauss-rect}.

First, we consider the matrix variance statistic $v(\mtx{Y})$ defined
in~\eqref{eqn:matrix-gauss-sigma2}.  Since $\mtx{Y}$ has zero mean,
this definition coincides with the general formula~\eqref{eqn:matrix-variance-herm}.
The second expression, in terms of the coefficient matrices, follows
from the additivity property~\eqref{eqn:indep-sum-herm}
for the variance of a sum of independent, random Hermitian matrices.

Next, bounds for the minimum eigenvalue $\lambda_{\min}(\mtx{Y})$
follow from the results for the maximum eigenvalue
because $-\mtx{Y}$ has the same distribution as $\mtx{Y}$.
Therefore, 
\begin{equation} \label{eqn:matrix-gauss-lower-expect}
\Expect \lambda_{\min}(\mtx{Y}) = \Expect \lambda_{\min}(-\mtx{Y})
	= - \Expect \lambda_{\max}(\mtx{Y})
	\geq - \sqrt{2 v(\mtx{Y}) \log d}.
\end{equation}
The second identity holds because of the relationship~\eqref{eqn:min-max-sign-eig}
between minimum and maximum eigenvalues.
Similar considerations lead to a lower tail bound for the minimum eigenvalue:
\begin{equation} \label{eqn:matrix-gauss-lower-tail}
\Prob{ \lambda_{\min}(\mtx{Y}) \leq -t }
	\leq d \, \exp\left( \frac{-t^2}{2v(\mtx{Y})} \right)
	\quad\text{for $t \geq 0$.}
\end{equation}
This result follows directly from the upper tail bound~\eqref{eqn:matrix-gauss-upper-tail}.

This observation points to the most important difference between the Hermitian case and the general
case. 
Indeed, Theorem~\ref{thm:matrix-gauss-herm} concerns the extreme eigenvalues
of the random series $\mtx{Y}$ instead of the norm.  This change amounts to producing
one-sided tail bounds instead of two-sided tail bounds.

For Gaussian and Rademacher series, this improvement is not really useful,
but there are random Hermitian
matrices whose minimum and maximum eigenvalues exhibit different types of behavior.
For these problems, it can be extremely valuable to examine the two tails separately.
See Chapter~\ref{chap:matrix-chernoff} and~\ref{chap:matrix-bernstein} for some results of this type.

\subsection{Analysis for Hermitian Gaussian Series}

We continue with the proof that matrix Gaussian series exhibit the behavior described in Theorem~\ref{thm:matrix-gauss-herm}.  Afterward, we show how to adapt the argument to address matrix Rademacher series.  Our main tool is Theorem~\ref{thm:master-ineq}, the set of master bounds for independent sums.  To use this result, we must identify the cgf of a fixed matrix modulated by a Gaussian random variable.

\begin{lemma}[Gaussian $\times$ Matrix: Mgf and Cgf] \label{lem:matrix-gauss-mgf}
Suppose that $\mtx{A}$ is a fixed Hermitian matrix, and  
let $\gamma$ be a standard normal random variable.  Then
$$
\Expect \econst^{\gamma \theta \mtx{A}}
	= \econst^{\theta^2 \mtx{A}^2/2}
\quad\text{and}\quad
\log{} \Expect \econst^{\gamma \theta \mtx{A}}
	= \frac{\theta^2}{2} \mtx{A}^2
\quad\text{for $\theta \in \mathbb{R}$.}
$$
\end{lemma}

\begin{proof}
We may assume $\theta = 1$ by absorbing $\theta$ into the matrix $\mtx{A}$.
It is well known that the moments of a standard normal variable satisfy
$$
\Expect\big( \gamma^{2q+1} \big) = 0
\quad\text{and}\quad
\Expect \big( \gamma^{2q} \big) = \frac{(2q)!}{2^q \, q!}
\quad\text{for $q = 0, 1, 2, \dots$}.
$$
The formula for the odd moments holds because a standard normal variable is symmetric.
One way to establish the formula for the even moments is to use integration by parts
to obtain a recursion for the $(2q)$th moment in terms of the $(2q-2)$th moment.

<!-- pdf-page: 7 -->
Therefore, the matrix mgf satisfies
$$
\Expect \econst^{\gamma \mtx{A}}

= \Id + \sum_{q=1}^\infty \frac{\Expect\big(\gamma^{2q}\big)}{(2q)!}\mtx{A}^{2q}
	= \Id + \sum_{q=1}^\infty \frac{1}{q!} \big(\mtx{A}^2/2 \big)^q
	= \econst^{ \mtx{A}^2 / 2 }.
$$
The first identity holds because the odd terms vanish from the series representation~\eqref{eqn:exp-series}
of the matrix exponential when we take the expectation.  To compute the cgf, we extract the logarithm of the mgf and recall~\eqref{eqn:log-defn}, which states that the matrix logarithm is the functional inverse of the matrix exponential.
\end{proof}

We quickly reach results on the maximum eigenvalue of a matrix Gaussian series with Hermitian coefficients.

\begin{proof}[Proof of Theorem~\ref{thm:matrix-gauss-herm}: Gaussian Case]
Consider a finite sequence $\{ \mtx{A}_k \}$ of Hermitian matrices with dimension $d$,
and let $\{ \gamma_k \}$ be a finite sequence of independent standard normal variables.
Define the matrix Gaussian series
$$
\mtx{Y} = \sum\nolimits_k \gamma_k \mtx{A}_k.
$$
We begin with the upper bound~\eqref{eqn:matrix-gauss-upper-expect} for $\Expect \lambda_{\max}(\mtx{Y})$.  The master expectation bound~\eqref{eqn:master-upper-expect} from Theorem~\ref{thm:master-ineq} implies that
\begin{align*}
\Expect \lambda_{\max}(\mtx{Y})
	&\leq \inf_{\theta > 0} \ \frac{1}{\theta} \log{} \trace \exp\left(
	\sum\nolimits_k \log{} \Expect \econst^{\gamma_k \theta \mtx{A}_k} \right) \\
	&= \inf_{\theta > 0} \ \frac{1}{\theta} \log{} \trace \exp\left(
	\frac{\theta^2}{2} \sum\nolimits_k \mtx{A}_k^2 \right) \\
	&\leq \inf_{\theta > 0} \ \frac{1}{\theta} \log{} \left[ d \, \lambda_{\max}\left(
	\exp\left( \frac{\theta^2}{2} \sum\nolimits_{k} \mtx{A}_k^2 \right) \right) \right] \\
	&= \inf_{\theta > 0} \ \frac{1}{\theta} \log{} \left[ d \, \exp\left(
	\frac{\theta^2}{2} \lambda_{\max}\left(\sum\nolimits_k \mtx{A}_k^2 \right) \right) \right] \\
	&= \inf_{\theta > 0} \ \frac{1}{\theta} \left[ \log d +
	\frac{\theta^2 v(\mtx{Y})}{2} \right]

\end{align*}
The second line follows when we introduce the cgf from Lemma~\ref{lem:matrix-gauss-mgf}.  To reach the third inequality, we bound the trace by the dimension times the maximum eigenvalue.  The fourth line is the Spectral Mapping Theorem, Proposition~\ref{prop:spectral-mapping}.  Use the formula~\eqref{eqn:matrix-gauss-sigma2} to identify the matrix variance statistic $v(\mtx{Y})$ in the exponent.

The infimum is attained at $\theta = \sqrt{2 v(\mtx{Y})^{-1} \log d}$.  This choice leads to~\eqref{eqn:matrix-gauss-upper-expect}.

Next, we turn to the proof of the upper tail bound~\eqref{eqn:matrix-gauss-upper-tail}
for $\lambda_{\max}(\mtx{Y})$.  Invoke the master tail bound~\eqref{eqn:master-upper-tail} from Theorem~\ref{thm:master-ineq}, and calculate that
\begin{align*}
\Prob{ \lambda_{\max}(\mtx{Y}) \geq t }
	&\leq \inf_{\theta > 0} \ \econst^{-\theta t} \,
	\trace \exp\left( \sum\nolimits_k \log{} \Expect \econst^{\gamma_k \theta \mtx{A}_k} \right)	\\
	&= \inf_{\theta > 0} \ \econst^{-\theta t} \,
	\trace \exp\left( \frac{\theta^2}{2} \sum\nolimits_k \mtx{A}_k^2 \right) \\

&\leq  \inf_{\theta > 0 } \ \econst^{-\theta t} \cdot d \,
	\exp\left( \frac{\theta^2}{2} \lambda_{\max}\left(\sum\nolimits_k \mtx{A}_k^2 \right) \right) \\
	&= d \, \inf_{\theta > 0} \ \econst^{-\theta t + \theta^2 v(\mtx{Y}) / 2}.

\end{align*}
The steps here are the same as in the previous calculation.

The infimum is achieved at $\theta = t/v(\mtx{Y})$, which yields~\eqref{eqn:matrix-gauss-upper-tail}.

\end{proof}

\subsection{Analysis for Hermitian Rademacher Series}

The inequalities for matrix Rademacher series involve arguments closely related to the proofs for matrix Gaussian series, but we require one additional piece of reasoning to obtain the simplest results.  First, let us compute bounds for the matrix mgf and cgf of a Hermitian matrix modulated by a Rademacher random variable.

\begin{lemma}[Rademacher $\times$ Matrix: Mgf and Cgf] \label{lem:matrix-rad-mgf}
Suppose that $\mtx{A}$ is a fixed Hermitian~matrix, and let $\varrho$ be a Rademacher random variable.  Then
$$
\Expect \econst^{\varrho \theta \mtx{A}}
\psdle \econst^{\theta^2\mtx{A}^2/2}
\quad\text{and}\quad
\log{} \Expect \econst^{\varrho \theta \mtx{A}}
\psdle \frac{\theta^2}{2} \mtx{A}^2
\quad\text{for $\theta \in \mathbb{R}$.}
$$ 
\end{lemma}

\begin{proof}
First, we establish a scalar inequality.  Comparing Taylor series,
\begin{equation} \label{eqn:cosh-exp}
\cosh(a) = \sum_{q=0}^\infty \frac{a^{2q}}{(2q)!}
	\leq \sum_{q=0}^\infty \frac{a^{2q}}{2^q q!}
	= \econst^{a^2/2}
	\quad\text{for $a \in \R$.}
\end{equation}
The inequality holds because $(2q)! \geq (2q)(2q-2)\cdots (4)(2) = 2^q q!$.

To compute the matrix mgf, we may assume $\theta = 1$.  By direct calculation,

$$
\Expect \econst^{\varrho \mtx{A}}
	= \tfrac{1}{2} \econst^{\mtx{A}} + \tfrac{1}{2} \econst^{-\mtx{A}}
	= \cosh(\mtx{A})
	\psdle \econst^{\mtx{A}^2/2}.
$$
The semidefinite bound follows when we apply the Transfer Rule~\eqref{eqn:transfer-rule} to the inequality~\eqref{eqn:cosh-exp}.

To determine the matrix cgf, observe that
$$
\log{} \Expect \econst^{\varrho \mtx{A}}
	= \log \cosh(\mtx{A})
	\psdle \tfrac{1}{2} \mtx{A}^2.
$$
The semidefinite bound follows when we apply the Transfer Rule~\eqref{eqn:transfer-rule} to the scalar inequality $\log \cosh(a) \leq a^2 / 2$ for $a \in \R$, which is a consequence of~\eqref{eqn:cosh-exp}.
\end{proof}

We are prepared to develop some probability inequalities for the maximum eigenvalue of a
Rademacher series with Hermitian coefficients.

\begin{proof}[Proof of Theorem~\ref{thm:matrix-gauss-herm}: Rademacher Case]
Consider a finite sequence $\{ \mtx{A}_k \}$ of Hermitian matrices, and let $\{ \varrho_k \}$ be a finite sequence of independent Rademacher variables.  Define the matrix Rademacher series
$$
\mtx{Y} = \sum\nolimits_k \varrho_k \mtx{A}_k.
$$
The bounds for the extreme eigenvalues of $\mtx{Y}$ follow from an argument almost identical with the proof in the Gaussian case.  The only point that requires justification is the inequality
$$
\trace \exp\left( \sum\nolimits_k \log{} \Expect \econst^{\varrho_k \theta \mtx{A}_k} \right)
	\leq \trace \exp\left( \frac{\theta^2}{2} \sum\nolimits_k \mtx{A}_k^2 \right).
$$
To obtain this result, we introduce the semidefinite bound, Lemma~\ref{lem:matrix-rad-mgf}, for the Rademacher cgf into the trace exponential.  The left-hand side increases after this substitution because of the fact~\eqref{eqn:exp-trace-monotone} that the trace exponential function is monotone with respect to the semidefinite order.
\end{proof}

<!-- pdf-page: 8 -->
\subsection{Analysis of Matrix Series with Rectangular  Coefficients} \label{sec:matrix-gauss-proof-rect}

Finally, we consider a series with non-Hermitian matrix coefficients modulated by independent Gaussian or Rademacher random variables.  The bounds for the norm of a rectangular series follow instantly from the bounds for the norm of an Hermitian series because of a formal device.  We simply apply the Hermitian results to the Hermitian dilation~\eqref{eqn:herm-dilation} of the series.

\begin{proof}[Proof of Theorem~\ref{thm:matrix-gauss-rect}]
Consider a finite sequence $\{ \mtx{B}_k \}$ of $d_1 \times d_2$ complex matrices, and let $\{\zeta_k\}$ be a finite sequence of independent random variables, either standard normal or Rademacher.

Recall from Definition~\ref{def:herm-dilation} that the Hermitian dilation is the map
$$
\coll{H} : \mtx{B} \longmapsto \begin{bmatrix} \mtx{0} & \mtx{B} \\ \mtx{B}^\adj & \mtx{0} \end{bmatrix}.
$$

This leads us to form the two series
$$
\mtx{Z} = \sum\nolimits_k \zeta_k \mtx{B}_k
\quad\text{and}\quad
\mtx{Y} = \coll{H}(\mtx{Z}) = \sum\nolimits_k \zeta_k \coll{H}(\mtx{B}_k).

$$
The second expression for $\mtx{Y}$ holds because the Hermitian dilation is real-linear.
Since we have written $\mtx{Y}$ as a matrix series with Hermitian coefficients,
we may analyze it using Theorem~\ref{thm:matrix-gauss-herm}.  We just need to express
the conclusions in terms of the random matrix $\mtx{Z}$.

First, we employ the fact~\eqref{eqn:herm-dilation-norm} that the Hermitian dilation preserves spectral information:
$$
\norm{ \mtx{Z} } = \lambda_{\max}(\coll{H}(\mtx{Z})) = \lambda_{\max}(\mtx{Y}).
$$
Therefore, bounds on $\lambda_{\max}(\mtx{Y})$ deliver bounds on $\norm{\mtx{Z}}$.

In view of the calculation~\eqref{eqn:var-stat-dilation} for the variance statistic
of a dilation, we have
$$
v(\mtx{Y}) = v( \coll{H}(\mtx{Z}) ) = v(\mtx{Z}).
$$
Recall that the matrix variance statistic $v(\mtx{Z})$ defined in~\eqref{eqn:matrix-gauss-sigma2-rect}
coincides with the general definition from~\eqref{eqn:matrix-variance-rect}.

Now, invoke Theorem~\ref{thm:matrix-gauss-herm} to obtain Theorem~\ref{thm:matrix-gauss-rect}.
\end{proof}

\section{Notes}

We give an overview of research related to matrix Gaussian series, along with references for the specific random matrices that we have analyzed.

\subsection{Matrix Gaussian and Rademacher Series}

The main results, Theorem~\ref{thm:matrix-gauss-rect} and Theorem~\ref{thm:matrix-gauss-herm}, have an interesting history.  In the precise form presented here, these two statements first appeared in~\cite{Tro11:User-Friendly-FOCM}, but we can trace them back more than two decades.

In his work~\cite[Thm.~1]{Oli10:Sums-Random}, Oliveira established the mgf bounds presented in Lemma~\ref{lem:matrix-gauss-mgf} and Lemma~\ref{lem:matrix-rad-mgf}.  He also developed an ingenious improvement on the arguments of Ahlswede \& Winter~\cite[App.]{AW02:Strong-Converse}, and he obtained a bound similar with Theorem~\ref{thm:matrix-gauss-herm}.  The constants in Oliveira's result are worse, but the dependence on the dimension is better because it depends on the number of summands.  We do not believe that the approach Ahlswede \& Winter describe in~\cite{AW02:Strong-Converse} can deliver any of these results.

Recently, there have been some minor improvements to the dimensional factor that appears in Theorem~\ref{thm:matrix-gauss-herm}.  We discuss these results and give citations in Chapter~\ref{chap:intrinsic}.

\subsection{The Noncommutative Khintchine Inequality}
\label{sec:nc-khintchine}

Our theory about matrix Rademacher and Gaussian series should be compared with
a classic result, called the \term{noncommutative Khintchine inequality},
that was originally due to Lust-Piquard~\cite{LP86:Inegalites-Khintchine};
see also the follow-up work~\cite{LPP91:Noncommutative-Khintchine}.
In its simplest form, this inequality concerns a matrix Rademacher series
with Hermitian coefficients:
$$
\mtx{Y} = \sum\nolimits_k \varrho_k \mtx{A}_k
$$
The noncommutative Khintchine inequality states that
\begin{equation} \label{eqn:nc-khintchine}
\Expect{} \trace\big[ \mtx{Y}^{2q} \big]
	\leq C_{2q} \trace\big[ \big(\Expect \mtx{Y}^2 \big)^{q} \big]
	\quad\text{for $q = 1,2,3, \dots$.}
\end{equation}
The minimum value of the constant $C_{2q} = (2q)!/(2^q \, q!)$
was obtained in the two papers~\cite{Buc01:Operator-Khintchine,Buc05:Optimal-Constants}.
Traditional proofs of the noncommutative Khintchine inequality are quite involved,
but there is now an elementary argument available~\cite[Cor.~7.3]{MJCFT12:Matrix-Concentration}.

Theorem~\ref{thm:matrix-gauss-herm} is the exponential moment analog
of the polynomial moment bound~\eqref{eqn:nc-khintchine}.  
The polynomial moment inequality is somewhat stronger than the exponential
moment inequality.  Nevertheless, the exponential results are often more
useful in practice.  For a more thorough exploration of the relationships
between Theorem~\ref{thm:matrix-gauss-herm} and noncommutative moment inequalities,
such as~\eqref{eqn:nc-khintchine}, see the discussion in~\cite[\S4]{Tro11:User-Friendly-FOCM}.

\subsection{Application to Random Matrices}

It has also been known for a long time that results such as Theorem~\ref{thm:matrix-gauss-herm} and inequality~\eqref{eqn:nc-khintchine} can be used to study random matrices.

We believe that the geometric functional analysis literature contains the earliest applications of matrix concentration results to analyze random matrices.  In a well-known paper~\cite{Rud99:Random-Vectors}, Mark Rudelson---acting on a suggestion of Gilles Pisier---showed how to use the noncommutative Khintchine inequality~\eqref{eqn:nc-khintchine} to study covariance estimation.  This work led to a significant amount of activity in which researchers used variants of Rudelson's argument to prove other types of results.  See, for example, the paper~\cite{RV07:Sampling-Large}.  This approach is powerful, but it tends to require some effort to use.

<!-- pdf-page: 9 -->
In parallel, other researchers in noncommutative probability theory also came to recognize the power of noncommutative moment inequalities in random matrix theory.  The paper~\cite{JX08:Noncommutative-Burkholder-II} contains a specific example.  Unfortunately, this literature is technically formidable, which makes it difficult for outsiders to appreciate its achievements.

The work~\cite{AW02:Strong-Converse} of Ahlswede \& Winter led to the first ``packaged'' matrix concentration inequalities
of the type that we describe in these lecture notes.  For the first few
years after this work, most of the applications concerned quantum information theory and random graph theory.  The paper~\cite{Gro11:Recovering-Low-Rank} introduced the method of Ahlswede \& Winter to researchers in mathematical signal processing and statistics, and it served to popularize matrix concentration bounds.

At this point, the available matrix concentration inequalities were still significantly suboptimal.  The main advances, in~\cite{Oli10:Concentration-Adjacency,Tro11:User-Friendly-FOCM}, led to optimal matrix concentration results of the kind that we present in these lecture notes.  These results allow researchers to obtain reasonably accurate analyses of a wide variety of random matrices with very little effort.

\subsection{Wigner and Mar{\v c}enko--Pastur}

Wigner matrices first emerged in the literature on nuclear physics, where they were used to model the Hamiltonians of reactions involving heavy atoms~\cite[\S1.1]{Meh04:Random-Matrices}.  Wigner~\cite{Wig55:Characteristic-Vectors} showed that the limiting spectral distribution of a certain type of Wigner matrix follows the semicircle law.  See the book~\cite[\S2.4]{Tao12:Topics-Random} of Tao for an overview and the book~\cite[Chap.~2]{BS10:Spectral-Analysis} of Bai \& Silverstein for a complete treatment.  The Bai--Yin law~\cite{BY93:Limit-Smallest} states that, up to scaling, the maximum eigenvalue of a Wigner matrix converges almost surely to two.  See~\cite[\S2.3]{Tao12:Topics-Random} or~\cite[Chap.~5]{BS10:Spectral-Analysis} for more information.  The analysis of the Gaussian Wigner matrix that we present here, using Theorem~\ref{thm:matrix-gauss-herm}, is drawn from~\cite[\S4]{Tro11:User-Friendly-FOCM}.

The first rigorous work on a rectangular Gaussian matrix is due to Mar{\v c}enko \& Pastur~\cite{MP67:Distribution-Eigenvalues}, who established that the limiting distribution of the squared singular values follows a distribution that now bears their names.  The Bai--Yin law~\cite{BY93:Limit-Smallest} gives an almost-sure limit for the largest singular value of a rectangular Gaussian matrix.  The expectation bound~\eqref{eqn:gauss-rect-true} appears in a survey article~\cite{DS02:Local-Operator} by Davidson \& Szarek.  The latter result is ultimately derived from a comparison theorem for Gaussian processes due to F{\'e}rnique~\cite{Fer75:Regularite-Trajectoires} and amplified by Gordon~\cite{Gor85:Some-Inequalities}.
Our approach, using Theorem~\ref{thm:matrix-gauss-rect}, is based on~\cite[\S4]{Tro11:User-Friendly-FOCM}.

\subsection{Randomly Signed Matrices}

Matrices with randomly signed entries have not received much attention in the literature.  The result~\eqref{eqn:rdm-sign-matrix-true} is due to Yoav Seginer~\cite{Seg00:Expected-Norm}.  There is also a well-known paper~\cite{Lat05:Some-Estimates} by Rafa{\l} Lata{\l}a that provides a bound for the expected norm of a Gaussian matrix whose entries have nonuniform variance.  Riemer \& Sch{\"u}tt~\cite{RS13:Expectation-Norm} have extended the earlier results.
The very recent paper~\cite{BV14:Sharp-Nonasymptotic} of Afonso Bandeira and Ramon Van Handel contains
an elegant new proof of Seginer's result based on a general theorem for random matrices with independent
entries.  The analysis here, using Theorem~\ref{thm:matrix-gauss-rect}, is drawn from~\cite[\S4]{Tro11:User-Friendly-FOCM}.

\subsection{Gaussian Toeplitz Matrices}

Research on random Toeplitz matrices is surprisingly recent, but there are now a number of papers available.  Bryc, Dembo, \& Jiang obtained the limiting spectral distribution of a symmetric Toeplitz matrix based on independent and identically distributed (iid) random variables~\cite{BDJ06:Spectral-Measure}.  Later, Mark Meckes established the first bound for the expected norm of a random Toeplitz matrix based on iid random variables~\cite{Mec07:Spectral-Norm}.  More recently, Sen \& Vir{\'a}g computed the limiting value of the expected norm of a random, symmetric Toeplitz matrix whose entries have identical second-order statistics~\cite{SV13:Top-Eigenvalue}. See the latter paper for additional references.  The analysis here, based on Theorem~\ref{thm:matrix-gauss-rect}, is new.
Our lower bound for the value of $\Expect \norm{\mtx{\Gamma}_d}$ follows from the results of Sen \& Vir{\'a}g.

We are not aware of any analysis for a random Toeplitz matrix whose entries have different variances,
but this type of result would follow from a simple modification of the argument in \S\ref{sec:toeplitz}.

\subsection{Relaxation and Rounding of \textsc{MaxQP}}

The idea of using semidefinite relaxation and rounding to solve the \textsc{MaxQP} problem is due to Arkadi Nemirovski~\cite{Nem07:Sums-Random}.  He obtained nontrivial results on the performance of his method using some matrix moment calculations, but he was unable to reach the sharpest possible bound.  Anthony So~\cite{So09:Moment-Inequalities} pointed out that matrix moment inequalities imply an optimal result; he also showed that matrix concentration inequalities have applications to robust optimization.  The presentation here, using Theorem~\ref{thm:matrix-gauss-rect}, is essentially equivalent with the approach in~\cite{So09:Moment-Inequalities}, but we have achieved slightly better bounds for the constants.

\makeatletter{}
