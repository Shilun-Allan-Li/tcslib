<!-- generated-by: proofmatch Claude repair -->
<!-- source-pdf-sha256: 5ada2eaf45a82e0deea73bcd5180a5dd3c8e1d125c5f65c4d4cce6458deea54a -->

<a id="pdf-5ada2eaf45a8-p001-b001"></a>
<!-- pdf-source: page=1; block=1; confidence=0.95 -->
**Adaptive Estimation of a Quadratic Functional by Model Selection.** By B. Laurent and P. Massart, Université Paris Sud. *The Annals of Statistics* 2000, Vol. 28, No. 5, 1302–1338.

<a id="pdf-5ada2eaf45a8-p001-b002"></a>
<!-- pdf-source: page=1; block=2; confidence=0.90 -->
Problem: estimate the quadratic functional $\|s\|^2$ where $s$ lies in a separable Hilbert space $H$, given the observed Gaussian process $Y(t)=\langle s,t\rangle+\sigma L(t)$ for all $t\in H$, with $L$ a Gaussian isonormal process. Special case: the Gaussian sequence model with $H=\ell_2(\mathbb{N}^*)$ and $L(t)=\sum_{\lambda\ge1}t_\lambda\varepsilon_\lambda$, $(\varepsilon_\lambda)$ i.i.d. standard normal. Method: choose at-most-countable families of finite-dimensional linear subspaces of $H$ (models) and perform model selection by a penalized least-squares criterion to build estimators of $\|s\|^2$. A general nonasymptotic risk bound is proved, yielding estimators adaptive over hyperrectangles, ellipsoids, $\ell_p$-bodies and Besov bodies (in the sequence model). Conditions for efficiency as $\sigma\to0$ are described. The construction is an alternative to Efroïmovich–Low for hyperrectangles and gives new results otherwise.

<a id="pdf-5ada2eaf45a8-p001-b003"></a>
<!-- pdf-source: page=1; block=3; confidence=0.85 -->
**Framework (Introduction).** For a separable Hilbert space $H$, one observes
$$Y(t)=\langle s,t\rangle+\sigma L(t),\quad t\in H,$$
where $L$ is a centered Gaussian isonormal process, i.e. $L$ maps $H$ isometrically onto a Gaussian subspace of $L^2(\Omega)$. Then $Y$ is called a Gaussian linear process with mean $s$ and variance $\sigma^2$; the goal is to estimate $\|s\|^2$. Instances covered: (i) the white noise model, $H=L^2([0,1])$ and $L(t)=\int t(x)\,dW(x)$ with $W$ standard Brownian motion; (ii) the finite-dimensional linear model, $H=\mathbb{R}^N$ and $L(t)=\langle\zeta,t\rangle$ with $\zeta$ a standard $N$-dimensional Gaussian vector. Given a Hilbertian basis $(\varphi_\lambda)_{\lambda\in\Lambda}$ of $H$ ($\Lambda$ finite or countable), the observation can be described equivalently in coordinates.

<a id="pdf-5ada2eaf45a8-p001-b004"></a>
<!-- pdf-source: page=1; block=4; confidence=0.95 -->
Received December 1998; revised April 2000. AMS 1991 subject classifications: primary 62G05; secondary 62G20, 62J02. Key words: adaptive estimation, quadratic functionals, model selection, Besov bodies, $\ell_p$-bodies, Gaussian sequence model, efficient estimation.

<a id="pdf-5ada2eaf45a8-p002-b001"></a>
<!-- pdf-source: page=2; block=1; confidence=0.88 -->
The observation $Y$ in the basis is described by
$$Y_\lambda=\beta_\lambda+\sigma\varepsilon_\lambda,\quad \lambda\in\Lambda,$$
where $(\varepsilon_\lambda)_{\lambda\in\Lambda}$ are i.i.d. standard normal and $(\beta_\lambda)_{\lambda\in\Lambda}$ are the coordinates of $s$. When $\Lambda=\mathbb{N}^*$ this is the **Gaussian sequence model** (discrete equivalent of the white noise model). To ease comparison with density estimation from $n$ i.i.d. observations, the noise level is written $\sigma=n^{-1/2}$.

<a id="pdf-5ada2eaf45a8-p002-b002"></a>
<!-- pdf-source: page=2; block=2; confidence=0.85 -->
**Question (Q).** For $s$ restricted to a set $\Theta$ and using the usual distance on the real line as loss, what is the order of the minimax risk over $\Theta$ when estimating $\|s\|^2$? (Stated as still unresolved in general.) Contrast: for estimating $s$ itself the minimax-risk order is governed by the metric dimension of $\Theta$ (Birgé 1983); for a linear functional it is determined by the functional's modulus of continuity w.r.t. Hellinger distance (Donoho and Liu 1991).

<a id="pdf-5ada2eaf45a8-p002-b003"></a>
<!-- pdf-source: page=2; block=3; confidence=0.95 -->
**Prior results (Bickel and Ritov 1988).** In density estimation from $n$ i.i.d. observations with density $s$ on $\mathbb{R}$, let $\theta=\|s\|^2$ and suppose $s$ lies in a Hölder ball $\Theta$ of radius $R$ and smoothness index $\alpha$. Then there is an estimator $\hat\theta_n$ (depending on $\Theta$) such that:
- if $\alpha>1/4$, $\hat\theta_n$ is asymptotically $\sqrt{n}$-efficient for $\theta$;
- if $\alpha\le1/4$, $\hat\theta_n$ attains the rate $n^{-4\alpha/(1+4\alpha)}$, which is the minimax-risk order over $\Theta$.

**Donoho and Nussbaum (1990)** give the Gaussian-sequence analog, replacing smoothness by a geometric (ellipsoid) assumption on $(\beta_\lambda)_{\lambda\ge1}$, namely $\sum_{\lambda\ge1}\lambda^{2\alpha}\beta_\lambda^2\le R^2$.

<a id="pdf-5ada2eaf45a8-p003-b001"></a>
<!-- pdf-source: page=3; block=1; confidence=0.95 -->
Estimating $\|s\|^2$ is a key step toward estimators of general integral functionals of $s$ (references: Laurent 1996; Birgé–Massart 1995 for lower bounds). For ellipsoids/hyperrectangles, question (Q) is solved by the cited results; a general answer should reflect both the functional's modulus of continuity and the "size" of $\Theta$ (metric dimension may not suffice). **New $\ell_p$-body result (proved in Section 3), $p<2$:** under
$$\sum_{\lambda\ge1}\lambda^{p(1/2+\alpha-1/p)}|\beta_\lambda|^p\le R^p,\quad \alpha>1/p-1/2,$$
a $\sqrt{n}$-convergent estimator exists provided $\alpha>1/p-1/4$ when $p\ge4/3$, and $\alpha>1/2$ when $p\le4/3$. Notably this condition depends on $p$, whereas the metric dimension of the $\ell_p$-body depends only on $\alpha$ (Birgé–Massart 2000a). Optimality is left open.

<a id="pdf-5ada2eaf45a8-p003-b002"></a>
<!-- pdf-source: page=3; block=2; confidence=0.90 -->
All the estimators above require prior knowledge that $s\in\Theta$ (a specific Hölder ball or ellipsoid). Efroïmovitch and Low (1996) removed this drawback in the Gaussian sequence model using a procedure close to Lepskii's method (Lepskii 1990, 1992).

<a id="pdf-5ada2eaf45a8-p003-b003"></a>
<!-- pdf-source: page=3; block=3; confidence=0.85 -->
**Efroïmovitch and Low (1996).** For any $R,\alpha>0$, if $(\beta_\lambda)_{\lambda\ge1}$ satisfies $\beta_\lambda^2\lambda^{2\alpha+1}\le R^2$ for all $\lambda$ (i.e. lies in a hyperrectangle), there is an estimator $\hat\theta_n$ of $\theta$ with:
1. $\hat\theta_n$ asymptotically efficient if $\alpha>1/4$;
2. $\mathbb{E}[(\hat\theta_n-\theta)^2]\le b_n/n$ with $b_n\to\infty$ arbitrarily slowly, if $\alpha=1/4$.

They also give a $\sqrt{n}$-consistent estimator over the whole range $\alpha\ge1/4$. For both, when $\alpha<1/4$,
$$\mathbb{E}[(\hat\theta_n-\theta)^2]\le C(R,\alpha)\,\big(n^{-2}\log n\big)^{4\alpha/(1+4\alpha)}.$$
Since the minimax quadratic risk over a hyperrectangle is of order $n^{-8\alpha/(1+4\alpha)}$ for $\alpha<1/4$, $\hat\theta_n$ misses the optimal rate by a factor $(\log n)^{4\alpha/(1+4\alpha)}$; this logarithmic factor is shown to be the unavoidable price of adaptation.

<a id="pdf-5ada2eaf45a8-p004-b001"></a>
<!-- pdf-source: page=4; block=1; confidence=0.90 -->
The parameter α used here differs from that of Efroïmovitch and Low (1996); this choice is convenient for connecting smoothness assumptions on functions with geometric constraints on the coefficients in a proper basis.

<a id="pdf-5ada2eaf45a8-p004-b002"></a>
<!-- pdf-source: page=4; block=2; confidence=0.98 -->
**Description of our method and results.**

<a id="pdf-5ada2eaf45a8-p004-b003"></a>
<!-- pdf-source: page=4; block=3; confidence=0.90 -->
Adaptive estimation via model selection by penalization (following Birgé–Massart 1997, Barron–Birgé–Massart 1999, Baraud 1997, Birgé–Massart 2000b), presented in the Gaussian sequence model. Given a collection $\mathcal{M}$ of subsets of $\mathbb{N}^*$ and a penalty function $\mathrm{pen}\colon\mathcal{M}\to\mathbb{R}_+$, the penalized estimator of $\theta=\sum_{\lambda\ge 1}\beta_\lambda^2$ is

$$\hat\theta=\sup_{m\in\mathcal{M}}\Big(\sum_{\lambda\in m}Y_\lambda^2-\mathrm{pen}(m)\Big).\tag{1.1}$$

<a id="pdf-5ada2eaf45a8-p004-b004"></a>
<!-- pdf-source: page=4; block=4; confidence=0.95 -->
Theorem 1 (Section 2) gives a nonasymptotic bound for $\mathbb{E}\big[(\hat\theta-\theta-\tfrac{2}{\sqrt n}\sum_{\lambda\ge1}\beta_\lambda\varepsilon_\lambda)^2\big]$ for a suitably chosen penalty (explicit form stated in Theorem 1), usable for asymptotics and for determining when $\hat\theta$ is asymptotically efficient. The penalty $\mathrm{pen}(m)$ depends on the cardinality of $m$ and on the complexity of the whole collection $\mathcal{M}$; an appropriate penalty for estimating $s$ need not suit estimating $\|s\|^2$ and vice versa.

<a id="pdf-5ada2eaf45a8-p004-b005"></a>
<!-- pdf-source: page=4; block=5; confidence=0.80 -->
For the nested family $\mathcal{C}_{\mathrm{nest}}$ of sets $\{1,\dots,D\}$, $D\in\mathbb{N}^*$, define

$$\hat\theta=\sup_{D\in\mathbb{N}^*}\Big(\sum_{\lambda\le D}Y_\lambda^2-\tfrac1n\big(D+1+2\sqrt{(D+1)x_D}+2x_D\big)\Big),\tag{1.2}$$

with $x_D=C\log D$ for a constant $C>2$. This $\hat\theta$ has the same adaptivity over hyperrectangles as the Efroïmovitch–Low estimator, and is $\sqrt n$-efficient (rather than $\sqrt n$-convergent) when the hyperrectangle index satisfies $\alpha>1/4$.

<a id="pdf-5ada2eaf45a8-p005-b001"></a>
<!-- pdf-source: page=5; block=1; confidence=0.78 -->
Analogous adaptivity holds over $l_p$-bodies $\sum_{\lambda\in\mathbb{N}^*}\lambda^{p(\alpha-1/p+1/2)}|\beta_\lambda|^p\le R^p$ for $p>2$. Taking $\mathcal{C}=\mathcal{C}_{\mathrm{all}}$, the collection of all finite subsets of $\mathbb{N}^*$, with adequate penalty, retains adaptivity over hyperrectangles and ellipsoids and gains adaptivity over $l_p$-bodies for $p<2$: under $\sum_{\lambda\ge1}\lambda^{p(1/2+\alpha-1/p)}|\beta_\lambda|^p\le R^p$ with $\alpha>1/p-1/2$, the estimator is $\sqrt n$-efficient provided $\alpha>1/p-1/4$ when $p\ge4/3$ and $\alpha>1/2$ when $p\le4/3$; otherwise nonparametric rates arise (optimality unknown for lack of lower bounds on minimax risk over $l_p$-bodies, $p<2$). Specially designed collections with $\mathcal{C}_{\mathrm{nest}}\subset\mathcal{C}\subset\mathcal{C}_{\mathrm{all}}$ improve adaptive convergence by a logarithmic factor.

<a id="pdf-5ada2eaf45a8-p005-b002"></a>
<!-- pdf-source: page=5; block=2; confidence=0.90 -->
Despite the optimization over $\mathcal{C}$ in (1.1) (potentially very large, e.g. $\mathcal{C}_{\mathrm{all}}$), for all examples considered the computation reduces to an optimization over the integers, as in (1.2), and can be done by computer.

<a id="pdf-5ada2eaf45a8-p005-b003"></a>
<!-- pdf-source: page=5; block=3; confidence=0.97 -->
**2. Estimation via model selection.**

**2.1. Description of the framework.**

<a id="pdf-5ada2eaf45a8-p005-b004"></a>
<!-- pdf-source: page=5; block=4; confidence=0.85 -->
One observes a Gaussian linear process $Y$ with mean $s$ and variance $1/n$ on a Hilbert space $\mathbb{H}$ with scalar product $\langle\cdot,\cdot\rangle$:

$$Y(t)=\langle s,t\rangle+\tfrac{1}{\sqrt n}L(t),\qquad t\in\mathbb{H},\tag{2.1}$$

where $s\in\mathbb{H}$ is unknown and $L$ is an isonormal Gaussian process (Dudley 1973), a linear isometry from $\mathbb{H}$ into a Gaussian subspace of $L_2(\Omega,P)$, with $\mathrm{Cov}(L(t),L(t'))=\langle t,t'\rangle$.

<a id="pdf-5ada2eaf45a8-p005-b005"></a>
<!-- pdf-source: page=5; block=5; confidence=0.90 -->
**Finite-dimensional Gaussian regression.** One observes

$$Y_i=s_i+\varepsilon_i,\qquad i=1,\dots,n,\tag{2.2}$$

with $\varepsilon_1,\dots,\varepsilon_n$ i.i.d. standard normal; take $\mathbb{H}=\mathbb{R}^n$ with $\langle x,y\rangle=(1/n)\sum_{i=1}^n x_iy_i$.

<a id="pdf-5ada2eaf45a8-p006-b001"></a>
<!-- pdf-source: page=6; block=1; confidence=0.82 -->
With $s=(s_1,\dots,s_n)$, model (2.1) arises by setting $Y(t)=(1/n)\sum_{i=1}^n t_iY_i$ and $L(t)=(1/\sqrt n)\sum_{i=1}^n t_i\varepsilon_i$ for $t\in\mathbb{R}^n$. Conversely, from (2.1) one recovers fixed-design Gaussian regression via an orthonormal basis $(e_1,\dots,e_n)$ of $\mathbb{H}$, setting $Y_i=Y(ne_i)$, $s_i=n\langle s,e_i\rangle$, $\varepsilon_i=\sqrt n\,L(e_i)$.

<a id="pdf-5ada2eaf45a8-p006-b002"></a>
<!-- pdf-source: page=6; block=2; confidence=0.85 -->
**The Gaussian sequence model.** One observes

$$Y_\lambda=\beta_\lambda+\tfrac{1}{\sqrt n}\varepsilon_\lambda,\qquad \lambda\in\mathbb{N}^*,\tag{2.3}$$

with $(\varepsilon_\lambda)$ i.i.d. standard normal. Take $\mathbb{H}=l_2(\mathbb{N}^*)$ with $\langle\beta,\gamma\rangle=\sum_\lambda\beta_\lambda\gamma_\lambda$ and $s=(\beta_\lambda)$; for $t=(\alpha_\lambda)$ set $Y(t)=\sum_\lambda\alpha_\lambda Y_\lambda$, $L(t)=\sum_\lambda\alpha_\lambda\varepsilon_\lambda$, so (2.3) implies (2.1). Conversely, from (2.1) recover (2.3) via the canonical basis $(\varphi_\lambda)$ by $Y_\lambda=Y(\varphi_\lambda)$, $\beta_\lambda=\langle s,\varphi_\lambda\rangle$, $\varepsilon_\lambda=L(\varphi_\lambda)$.

<a id="pdf-5ada2eaf45a8-p006-b003"></a>
<!-- pdf-source: page=6; block=3; confidence=0.83 -->
**The multivariate white noise model.** One observes, for $x=(x_1,\dots,x_d)\in[0,1]^d$,

$$Z(x)=\int_{[0,1]^d}\mathbf{1}_{[0,x_1]\times\cdots\times[0,x_d]}(u)\,s(u)\,du+\tfrac{1}{\sqrt n}W(x),$$

with $W$ the standard Wiener process on $[0,1]^d$; take $\mathbb{H}=L_2([0,1]^d)$ with its usual scalar product, $Y(t)=\int t\,dZ$, $L(t)=\int t\,dW$. This is a case of (2.1), and conversely $Z(x)=Y(\mathbf{1}_{[0,x_1]\times\cdots\times[0,x_d]})$ recovers the white noise model since $W(x)=L(\mathbf{1}_{[0,x_1]\times\cdots\times[0,x_d]})$ is a standard Wiener process.

<a id="pdf-5ada2eaf45a8-p006-b004"></a>
<!-- pdf-source: page=6; block=4; confidence=0.90 -->
**2.2. The estimation procedure.** Aim: estimate $\|s\|^2=\langle s,s\rangle$ from (2.1) by an adaptive model-selection method. First the minimax approach is recalled, using an estimator from a single finite-dimensional linear model.

<a id="pdf-5ada2eaf45a8-p006-b005"></a>
<!-- pdf-source: page=6; block=5; confidence=0.85 -->
**Minimax approach.** For a $D$-dimensional subspace $S\subset\mathbb{H}$ with orthonormal basis $(\varphi_\lambda,\lambda\in\Lambda)$, the orthogonal projection of $s$ is $\sum_{\lambda\in\Lambda}\langle s,\varphi_\lambda\rangle\varphi_\lambda$, motivating the projection estimator $\hat s=\sum_{\lambda\in\Lambda}Y(\varphi_\lambda)\varphi_\lambda$. One checks $\hat s=\arg\min_{v\in S}(\|v\|^2-2Y(v))$, so $\hat s$ is basis-independent. To study $\|\hat s\|^2$, write

$$\hat s=\sum_{\lambda\in\Lambda}\langle s,\varphi_\lambda\rangle\varphi_\lambda+\tfrac{1}{\sqrt n}\sum_{\lambda\in\Lambda}L(\varphi_\lambda)\varphi_\lambda.$$

<a id="pdf-5ada2eaf45a8-p007-b001"></a>
<!-- pdf-source: page=7; block=1; confidence=0.82 -->
**Derivation.** Expanding gives $\|\hat s\|^2 = \sum_{\lambda\in\Lambda}\langle s,\varphi_\lambda\rangle^2 + \tfrac{2}{\sqrt n}\sum_{\lambda\in\Lambda}\langle s,\varphi_\lambda\rangle L(\varphi_\lambda) + \tfrac{1}{n}\sum_{\lambda\in\Lambda}L^2(\varphi_\lambda).$ Hence $\hat\theta = \|\hat s\|^2 - D/n$ is an unbiased estimator of $\|\pi_S(s)\|^2$, where $\pi_S(s)=\sum_{\lambda\in\Lambda}\langle s,\varphi_\lambda\rangle\varphi_\lambda$ is the orthogonal projection of $s$ onto $S$.

<a id="pdf-5ada2eaf45a8-p007-b002"></a>
<!-- pdf-source: page=7; block=2; confidence=0.95 -->
**Equation (2.4).** For estimating $\theta=\|s\|^2$, $\tilde\theta - \theta - \tfrac{2L(s)}{\sqrt n} = -\|s-\pi_S(s)\|^2 + \tfrac{2}{\sqrt n}L(\pi_S(s)-s) + \tfrac{1}{n}\sum_{\lambda\in\Lambda}(L^2(\varphi_\lambda)-1).$ Since $L(\pi_S(s)-s)$ and $\sum_{\lambda\in\Lambda}L^2(\varphi_\lambda)$ are independent with distributions $\mathcal N(0,\|s-\pi_S(s)\|^2)$ and $\chi^2(D)$,
$$\mathbb E\Big[\big(\tilde\theta-\theta-\tfrac{2L(s)}{\sqrt n}\big)^2\Big] = \|s-\pi_S(s)\|^4 + \tfrac{4}{n}\|s-\pi_S(s)\|^2 + \tfrac{2D}{n^2} \le 3\|s-\pi_S(s)\|^4 + \tfrac{2(D+1)}{n^2}.$$

<a id="pdf-5ada2eaf45a8-p007-b003"></a>
<!-- pdf-source: page=7; block=3; confidence=0.83 -->
**Trade-off / minimax.** An ideal $S$ balances squared bias $\|s-\pi_S(s)\|^4$ against variance $D/n^2$. Taking $\Lambda=L^2([0,1])$ and $s$ in the Hölder class $\mathcal H_\alpha(L)=\{t\in L^2([0,1]): |t(x)-t(y)|\le L|x-y|^\alpha,\ \forall x,y\in[0,1]\}$, there is a subspace $S$ (e.g. histograms with $D$ regular pieces) with $\sup_{s\in\mathcal H_\alpha(L)}\|s-\pi_S(s)\|^2 \le C L^2 D^{-2\alpha}.$ Choosing $D$ so that $D/n^2 \sim L^4 D^{-4\alpha}$ gives, for a universal $C'$, $\ \mathbb E\big[\sup_{s\in\mathcal H_\alpha(L)}(\tilde\theta-\theta-\tfrac{2L(s)}{\sqrt n})^2\big] \le C' L^{4/(1+4\alpha)} n^{-8\alpha/(1+4\alpha)}.$ Then $\tilde\theta$ is asymptotically efficient with asymptotic variance $4\|s\|^2$ when $\alpha>1/4$.

<a id="pdf-5ada2eaf45a8-p007-b004"></a>
<!-- pdf-source: page=7; block=4; confidence=0.85 -->
The minimax choice of $S,D$ depends on the unknown smoothness class. Strategy: use a preliminary collection of models $(S_m)_{m\in\mathcal M}$, with $\mathcal M$ finite or countable possibly depending on $n$, define projection estimators $(\hat s_m)_{m\in\mathcal M}$, and select a model via a data-driven criterion.

<a id="pdf-5ada2eaf45a8-p008-b001"></a>
<!-- pdf-source: page=8; block=1; confidence=0.82 -->
**Heuristics.** For $m\in\mathcal M$, $S_m$ is a $D_m$-dimensional subspace, $s_m$ the projection of $s$ onto $S_m$, and $\tilde\theta_m=\|\hat s_m\|^2-D_m/n$ is unbiased for $\|s_m\|^2$. By (2.4) the best model minimizes $\|s-s_m\|^2 + C\sqrt{D_m}/n$, equivalently $-\|s_m\|^2 + C\sqrt{D_m}/n$. Replacing the unknown $\|s_m\|^2$ by $\tilde\theta_m$ suggests minimizing $-\|\hat s_m\|^2 + D_m/n + C\sqrt{D_m}/n$.

<a id="pdf-5ada2eaf45a8-p008-b002"></a>
<!-- pdf-source: page=8; block=2; confidence=0.85 -->
**Definition.** With a penalty $\mathrm{pen}:\mathcal M\to\mathbb R_+$, set $\hat m = \arg\min_{m\in\mathcal M}\big(-\|\hat s_m\|^2 + \mathrm{pen}(m)\big).$ Here $\mathrm{pen}(m)$ is taken larger than the heuristic $D_m/n + C\sqrt{D_m}/n$ to account for the collection's complexity. The penalized estimator of $\theta$ is $\hat\theta = \|\hat s_{\hat m}\|^2 - \mathrm{pen}(\hat m) = \sup_{m\in\mathcal M}\big(\|\hat s_m\|^2 - \mathrm{pen}(m)\big).$

<a id="pdf-5ada2eaf45a8-p008-b003"></a>
<!-- pdf-source: page=8; block=3; confidence=0.88 -->
**Section 2.3.** Risk bounds for penalized estimators depending on the penalty choice. The $n$ in (2.1) is fixed and the bounds' constants are numerical (independent of $n$), so the Hilbert space, the collection $(S_m)_{m\in\mathcal M}$, and $\mathrm{pen}(\cdot)$ may all depend on $n$.

<a id="pdf-5ada2eaf45a8-p008-b004"></a>
<!-- pdf-source: page=8; block=4; confidence=0.86 -->
**Theorem 1 (setup).** Let $\mathbb H$ be a Hilbert space with scalar product $\langle\cdot,\cdot\rangle$; observe the Gaussian process $\{Y(t),\,t\in\mathbb H\}$ given by (2.1). Let $\mathcal M^*$ be finite or countable and, for $m\in\mathcal M^*$, let $S_m$ be a subspace of finite dimension $D_m>0$. Let $(x_m)_{m\in\mathcal M^*}$ be nonnegative reals. Assume $\mathrm{pen}(m)$ satisfies
$$(2.5)\quad n\,\mathrm{pen}(m) \ge (D_m+1) + 2\sqrt{(D_m+1)x_m} + 2x_m.$$
Let $\mathcal M$ be $\mathcal M^*$ or $\mathcal M^*\cup\{0\}$ with $S_0=\{0\}$, $\mathrm{pen}(0)=0$. Let $\hat s_m$ be the projection estimator of $s$ over $S_m$. Define the collection $(\hat\theta_m)_{m\in\mathcal M}$ of estimators of $\theta=\|s\|^2$ by
$$(2.6)\quad \hat\theta_m = \|\hat s_m\|^2 - \mathrm{pen}(m),\qquad \hat\theta = \sup_{m\in\mathcal M}\hat\theta_m.$$

<a id="pdf-5ada2eaf45a8-p009-b001"></a>
<!-- pdf-source: page=9; block=1; confidence=0.95 -->
**Theorem 1 (conclusion).** Let $r>0$. If
$$(2.7)\quad \Sigma_r = \sum_{m\in\mathcal M} D_m^{r/2} e^{-x_m} < +\infty,$$
then $\hat\theta$ is almost surely finite and
$$(2.8)\quad \mathbb E_s\Big[\big|\hat\theta-\theta-\tfrac{2L(s)}{\sqrt n}\big|^r\Big] \le \inf_{m\in\mathcal M}\mathbb E_s\Big[\big(-\hat\theta_m+\theta+\tfrac{2L(s)}{\sqrt n}\big)_+^r\Big] + C_1(r)\frac{\Sigma_r+1}{n^r},$$
with $C_1(r)$ numerical. Moreover, for any $m\in\mathcal M$,
$$(2.9)\quad \mathbb E_s\Big[\big(-\hat\theta_m+\theta+\tfrac{2L(s)}{\sqrt n}\big)_+^r\Big] \le C_2(r)\Big[\|s-s_m\|^{2r} + \frac{D_m^{r/2}+1}{n^r} + \big(\mathrm{pen}(m)-\tfrac{D_m}{n}\big)^r\Big],$$
where $s_m$ is the orthogonal projection of $s$ over $S_m$ and $C_2(r)$ is numerical.

<a id="pdf-5ada2eaf45a8-p009-b002"></a>
<!-- pdf-source: page=9; block=2; confidence=0.83 -->
**Comment (i).** The isonormal process $\{L(t)\}$ is defined up to a negligible event depending on $t$; if $\mathbb H$ is infinite-dimensional, no single version is linear in $t$ for a.a. $\omega$. But the estimator only uses the countable collection $(S_m)$ and $\{Y(t),\,t\in\bigcup_m S_m\}$; a version of $L$ linear on the algebraic span $S$ of $\bigcup_m S_m$ exists and defines a linear $Y$ on $S$.

**Comment (ii).** If $\mathcal M$ is finite, any minimizer $\hat m$ of $-\|\hat s_m\|^2+\mathrm{pen}(m)$ yields the same value $\hat\theta_{\hat m}=\hat\theta=\sup_{m}\hat\theta_m$. If $\mathcal M$ is infinite the minimum need not be attained, but $\sup_m\hat\theta_m$ always makes sense; hence $\hat\theta=\sup_m\hat\theta_m$ is used, and Theorem 1 guarantees it is a.s. finite.

<a id="pdf-5ada2eaf45a8-p009-b003"></a>
<!-- pdf-source: page=9; block=3; confidence=0.84 -->
**Comment (iii).** Generally take $\mathrm{pen}(m)$ as small as (2.5) permits: $\mathrm{pen}(m) = \tfrac{D_m+1}{n} + 2\tfrac{\sqrt{(D_m+1)x_m}}{n} + 2\tfrac{x_m}{n}.$ The weights $(x_m)_{m\in\mathcal M}$ are essential; one possible choice is to pick them so that
$$(2.10)\quad \sum_{m\in\mathcal M} D_m^{r/2} e^{-x_m} \le C'(r).$$

<a id="pdf-5ada2eaf45a8-p010-b001"></a>
<!-- pdf-source: page=10; block=1; confidence=0.85 -->
Combining (2.8) and (2.9) yields, under the stated assumption, the moment bound (2.11):
$$\mathbb{E}_s\Big[\big|\hat\theta-\theta-\tfrac{2L(s)}{\sqrt n}\big|^{r}\Big]\le C''(r)\inf_{m\in\mathcal M}\Big\{\|s-s_m\|^{2r}+\frac{D_m^{r/2}+1}{n^{r}}+\Big(\mathrm{pen}(m)-\frac{D_m}{n}\Big)^{\,r}\Big\},$$
where $C''(r)$ is a numerical constant depending only on $r$.

<a id="pdf-5ada2eaf45a8-p010-b002"></a>
<!-- pdf-source: page=10; block=2; confidence=0.80 -->
(iv) Two consequences of (2.11). **Risk analysis:** (2.12) gives
$$\mathbb{E}_s\big[|\hat\theta-\theta|^{r}\big]\le 2^{(r-1)_+}\Big[C''(r)\inf_{m\in\mathcal M}\big\{\|s-s_m\|^{2r}+\tfrac{D_m^{r/2}+1}{n^{r}}+(\mathrm{pen}(m)-\tfrac{D_m}{n})^{\,r}\big\}+\mathbb{E}(|\xi|^{r})\frac{2^{r}\|s\|^{r}}{n^{r/2}}\Big],$$
with $\xi$ standard normal; this yields upper bounds for the maximal risk of $\hat\theta$ over parameter sets (studied next section). **Asymptotic analysis** ($n\to\infty$): taking $r=1$ with weights $(x_m)$ chosen so that (2.10) holds, if $\inf_{m\in\mathcal M}\{\|s-s_m\|^{2}+\tfrac{D_m^{1/2}}{n}+(\mathrm{pen}(m)-\tfrac{D_m}{n})\}=o(1/\sqrt n)$, then $\sqrt n(\hat\theta-\theta)-2L(s)\to0$ in probability. Since $L(s)$ is centered Gaussian with variance $\theta$, and when the Hilbert space $\mathbb H$ does not depend on $n$ so $\theta=\|s\|^2$ is fixed, $\sqrt n(\hat\theta-\theta)$ is asymptotically centered normal with variance $4\theta$. The estimator is to be shown adaptive (and often asymptotically efficient); henceforth $\mathbb H$ is taken infinite-dimensional. The correspondence between function classes in $L^2([0,1])$ (Hölder, Sobolev, Besov balls) and sequence classes in $l^2(\mathbb N^*)$ (hyperrectangles, ellipsoids, $l_p$, Besov bodies) motivates the Gaussian sequence model study of Section 3.

<a id="pdf-5ada2eaf45a8-p010-b003"></a>
<!-- pdf-source: page=10; block=3; confidence=0.90 -->
**2.4. Smoothness classes and bodies in $l^2(\mathbb N^*)$.** Aim: make precise the correspondence between classes of functions in $L^2([0,1])$ and sets of coefficients.

<a id="pdf-5ada2eaf45a8-p011-b001"></a>
<!-- pdf-source: page=11; block=1; confidence=0.85 -->
Following the Haar-basis setting (DeVore–Lorentz 1993), the $\ell_p$-modulus of continuity is defined by
$$(\omega(s,y)_p)^p=\sup_{0<h\le y}\int_0^{1-h}|s(x+h)-s(x)|^{p}\,dx,\quad 0<p<\infty,$$
and for $p=\infty$,
$$\omega(s,y)_\infty=\sup_{0<h\le y}\ \sup_{x\in[0,1-h]}|s(x+h)-s(x)|.$$

<a id="pdf-5ada2eaf45a8-p011-b002"></a>
<!-- pdf-source: page=11; block=2; confidence=0.85 -->
For $0<\alpha<1$, $0<p,q\le\infty$: $s\in B^\alpha_{p,q}([0,1])$ iff $s\in L^p([0,1])$ and
$$\|s\|_{\alpha,p,q}^{q}=\sum_{j\ge0}2^{j\alpha q}\,\omega^{q}(s,2^{-j})_p<+\infty\quad(0<q<\infty),$$
$$\|s\|_{\alpha,p,\infty}=\sup_{j\ge0}2^{j\alpha}\,\omega(s,2^{-j})_p<+\infty\quad(q=\infty).$$
The condition $\alpha>(1/p-1/2)_+$ ensures $B^\alpha_{p,q}([0,1])\subset L^2([0,1])$.

<a id="pdf-5ada2eaf45a8-p011-b003"></a>
<!-- pdf-source: page=11; block=3; confidence=0.85 -->
Let $\psi=\mathbf 1_{[0,1/2)}-\mathbf 1_{[1/2,1)}$ and $\psi_{j,k}(\cdot)=2^{j/2}\psi(2^j\cdot-k)$. Any $s\in L^2([0,1])$ expands as
$$s=\int_0^1 s(x)\,dx+\sum_{j\ge0}\sum_{k=1}^{2^j}\beta_{j,k}\psi_{j,k},\qquad \beta_{j,k}=\int_0^1 s(x)\psi_{j,k}(x)\,dx.$$
Set $\Lambda=\{(j,k):j\in\mathbb N,\ k\in\{1,\dots,2^j\}\}$, and $\|\beta\|_{j,p}=\big(\sum_{k=1}^{2^j}|\beta_{j,k}|^p\big)^{1/p}$ ($p<\infty$), $\|\beta\|_{j,\infty}=\sup_{k\in\{1,\dots,2^j\}}|\beta_{j,k}|$. Coefficient size relates to the modulus via the classical inequality (DeVore–Jawerth–Popov 1992), for $j\ge0$, $p\ge1$:
$$2^{j(1/2-1/p)}\|\beta\|_{j,p}\le C_p\,\omega(s,2^{-j})_p,\tag{2.13}$$
with $C_p$ depending only on $p$.

<a id="pdf-5ada2eaf45a8-p012-b001"></a>
<!-- pdf-source: page=12; block=1; confidence=0.82 -->
Assume $p\ge1$. By (2.13): if $\sum_{j\ge0}2^{j\alpha q}\omega^{q}(s,2^{-j})_p\le Q^{q}$ then
$$\sum_{j\ge0}2^{qj(1/2+(\alpha-1/p))}\|\beta\|_{j,p}^{q}\le R^{q},\qquad R=C_pQ.\tag{2.14}$$
Similarly, if $\sup_{j\ge0}2^{j\alpha}\omega(s,2^{-j})_p\le Q$ then
$$\forall j\in\mathbb N,\quad \|\beta\|_{j,p}\le R\,2^{-j(1/2+(\alpha-1/p))}.\tag{2.15}$$

<a id="pdf-5ada2eaf45a8-p012-b002"></a>
<!-- pdf-source: page=12; block=2; confidence=0.90 -->
More generally consider $s$ with $\sum_{j\ge0}\omega^{p}(s,2^{-j})_p/w^{p}(2^{-j})<+\infty$ ($p<\infty$), $w>0$ on $[0,1]$; the Besov space $B^\alpha_{p,p}$ corresponds to $w(x)=x^\alpha$. By (2.13), $\beta\in l^2(\Lambda)$ provided that $x\mapsto w(x)x^{1/2-1/p}$ is nondecreasing (hence bounded) if $p\le2$, and provided $\sum_{j\ge0}(w(2^{-j}))^{(1/2-1/p)^{-1}}<+\infty$ if $p>2$. Moreover, if $\sum_{j\ge0}\omega^{p}(s,2^{-j})_p/w^{p}(2^{-j})\le Q^{p}$ then
$$\sum_{j\ge0}\frac{\|\beta\|_{j,p}^{p}}{R^{p}\,2^{pj(1/p-1/2)}\,w^{p}(2^{-j})}\le1.\tag{2.16}$$
Similarly, if $\sup_{j\ge0}\big(\omega(s,2^{-j})_\infty/w(2^{-j})\big)\le Q$ then
$$\sup_{j\ge0}\frac{\|\beta\|_{j,\infty}}{R\,2^{-1/2}\,w(2^{-j})}\le1.\tag{2.17}$$

<a id="pdf-5ada2eaf45a8-p012-b003"></a>
<!-- pdf-source: page=12; block=3; confidence=0.83 -->
For $0<p<1$, (2.13) is unavailable; nonetheless the Besov ball for the seminorm $\|\cdot\|_{\alpha,p,q}$ is still included in a Besov body defined by (2.14) if $q<\infty$, or (2.15) if $q=\infty$, for an appropriate $R$ (DeVore–Kyriazis–Leviatan–Tikhomirov 1993). Ordering the countable set $\Lambda$ lexicographically identifies $\Lambda$ with $\mathbb N^*$; thus conditions on the moduli of continuity of $s$ transfer to conditions on the coefficient sequence $\beta$.

<a id="pdf-5ada2eaf45a8-p013-b001"></a>
<!-- pdf-source: page=13; block=1; confidence=0.80 -->
Motivates formal definitions of bodies in $l_2(\mathbb{N}^*)$ used to encode constraints on the coefficient sequence of $s$; begins with $l_p$-bodies.

<a id="pdf-5ada2eaf45a8-p013-b002"></a>
<!-- pdf-source: page=13; block=2; confidence=0.92 -->
**Definition 1.** For $0 < p \le \infty$ and $c$ a positive nonincreasing sequence, the $l_p$-body $\mathcal{E}_{p,c}$ is: for $p<\infty$, $\{\beta \in l_p(\mathbb{N}^*): \sum_{\lambda\in\mathbb{N}^*} |\beta_\lambda/c_\lambda|^p \le 1\}$; for $p=\infty$, $\{\beta \in l_\infty(\mathbb{N}^*): \sup_{\lambda\in\mathbb{N}^*} |\beta_\lambda/c_\lambda| \le 1\}$.

<a id="pdf-5ada2eaf45a8-p013-b003"></a>
<!-- pdf-source: page=13; block=3; confidence=0.85 -->
An $l_p$-body lies in $l_2(\mathbb{N}^*)$ for $p\le 2$. For $p>2$, Hölder's inequality gives $\mathcal{E}_{p,c}\subset l_2(\mathbb{N}^*)$ whenever (2.18) $\sum_{\lambda\in\mathbb{N}^*} c_\lambda^{(1/2-1/p)^{-1}} < \infty$. $\mathcal{E}_{p,c}$ is an ellipsoid for $p=2$ and a hyperrectangle for $p=\infty$. Besov bodies (Donoho–Johnstone 1998) are introduced next.

<a id="pdf-5ada2eaf45a8-p013-b004"></a>
<!-- pdf-source: page=13; block=4; confidence=0.88 -->
**Definition 2.** For $0 < p,q \le \infty$, $\alpha>0$, $R>0$, set $\alpha' = 1/2 + \alpha - 1/p > 0$. Partition $\mathbb{N}^* = \bigcup_{j\ge0}\Lambda(j)$ with $\Lambda(j)=\{2^j,\dots,2^{j+1}-1\}$. The Besov body: for $q<\infty$, $B_{\alpha,p,q}(R)=\{\beta\in l_2(\mathbb{N}^*): \sum_{j\ge0}\|\beta\|_{j,p}^q\,2^{qj\alpha'} \le R^q\}$; for $q=\infty$, $B_{\alpha,p,\infty}(R)=\{\beta\in l_2(\mathbb{N}^*): \sup_{j\ge0}\|\beta\|_{j,p}\,2^{j\alpha'} \le R\}$, where $\|\beta\|_{j,p}^p=\sum_{\lambda\in\Lambda(j)}\|\beta_\lambda\|^p$ for $p<\infty$ and $\|\beta\|_{j,\infty}=\sup_{\lambda\in\Lambda(j)}\|\beta_\lambda\|$. $B_{\alpha,p,p}(R)$ is essentially an $l_p$-body; $B_{\alpha,p,\infty}(R)$ contains it and is used later.

<a id="pdf-5ada2eaf45a8-p013-b005"></a>
<!-- pdf-source: page=13; block=5; confidence=0.82 -->
These bodies encode smoothness of $s$ via constraints on $\beta$: by (2.14)–(2.15), $s$ in a Besov ball for the seminorm $\|\cdot\|_{\alpha,p,q}$ implies $\beta$ in a Besov body $B_{\alpha,p,q}(R)$; by (2.16)–(2.17), general modulus-of-continuity conditions imply $\beta$ lies in an appropriate $l_p$-body.

<a id="pdf-5ada2eaf45a8-p013-b006"></a>
<!-- pdf-source: page=13; block=6; confidence=0.80 -->
**3. The Gaussian sequence model.** To estimate $\|s\|^2$ for $s$ in an infinite-dimensional separable Hilbert space observed via (2.1): take an orthonormal basis $(\varphi_\lambda)_{\lambda\in\Lambda}$ of $\mathbb{H}$, assuming $\Lambda = \Lambda_0 \cup \mathbb{N}^*$ with $\Lambda_0$ a finite subset independent of $n$ (e.g. the Haar basis on $L_2([0,1])$ with $\varphi_0=\mathbf{1}_{[0,1]}$ and $(\varphi_\lambda)_{\lambda\in\mathbb{N}^*}$ the ordered $(\psi_{j,k})$).

<a id="pdf-5ada2eaf45a8-p014-b001"></a>
<!-- pdf-source: page=14; block=1; confidence=0.85 -->
Decomposition $\|s\|^2 = \|s_0\|^2 + \sum_{\lambda\in\mathbb{N}^*}\beta_\lambda^2$, with $s_0$ the projection onto $\mathrm{span}(\varphi_\lambda)_{\lambda\in\Lambda_0}$. Estimate $\|s_0\|^2$ by $\|\hat s_0\|^2 - |\Lambda_0|/n$; this has risk of order $1/n$ and is efficient: $\sqrt{n}(\|\hat s_0\|^2 - |\Lambda_0|/n - \|s_0\|^2) \xrightarrow{\mathcal{L}} \mathcal{N}(0, 4\|s_0\|^2)$. So estimating $\|s\|^2$ reduces to estimating $\|\beta\|^2=\sum_{\lambda\in\mathbb{N}^*}\beta_\lambda^2$ from the Gaussian sequence model (2.3) with errors $\varepsilon_\lambda = L(\varphi_\lambda)$. Any estimator $T_n$ of $\|\beta\|^2$ from $(Y_\lambda)$ yields $T'_n = \|\hat s_0\|^2 - |\Lambda_0|/n + T_n$; since $|\Lambda_0|$ is independent of $n$, $T'_n$ keeps the same risk order, and if $T_n$ is efficient ($\sqrt{n}(T_n-\|\beta\|^2)\xrightarrow{\mathcal{L}}\mathcal{N}(0,4\|\beta\|^2)$) then, by independence of $\hat s_0$ and $T_n$, $\sqrt{n}(T'_n-\|s\|^2)\xrightarrow{\mathcal{L}}\mathcal{N}(0,4\|s\|^2)$. The section builds adaptive, efficient estimators of $\|\beta\|^2$ over collections of subsets $\{\Lambda_m, m\in\mathcal{M}\}$ of $\mathbb{N}^*$, with models $S_m=\{\beta\in l_2(\mathbb{N}^*): \beta_\lambda=0\ \forall \lambda\notin\Lambda_m\}$ and penalized estimators (2.6).

<a id="pdf-5ada2eaf45a8-p014-b002"></a>
<!-- pdf-source: page=14; block=2; confidence=0.90 -->
**3.1. $l_p$-bodies for $p\ge2$.** Defines the penalized estimator used throughout the section.

<a id="pdf-5ada2eaf45a8-p014-b003"></a>
<!-- pdf-source: page=14; block=3; confidence=0.95 -->
**Definition 3.** Let $\mathcal{M}=\mathbb{N}^*$ and $K>1$ real. For $m\in\mathcal{M}$, set $x_m = K\log(m+1)$ and $n\,\mathrm{pen}(m) = m + 1 + 2\sqrt{(m+1)x_m} + 2x_m$. Define $\hat\theta = \sup_{m\in\mathcal{M}}\Big(\sum_{\lambda=1}^{m} Y_\lambda^2 - \mathrm{pen}(m)\Big)$.

<a id="pdf-5ada2eaf45a8-p015-b001"></a>
<!-- pdf-source: page=15; block=1; confidence=0.90 -->
Introduces a body containing $l_p$-bodies for $p\ge2$. For $\gamma=(\gamma_m)_{m\in\mathbb{N}^*}$ nonincreasing and nonnegative, define (3.1) $\Gamma_\gamma = \{\beta\in l_2(\mathbb{N}^*): \forall m\in\mathbb{N}^*,\ \sum_{\lambda>m}\beta_\lambda^2 \le \gamma_m^2\}$.

<a id="pdf-5ada2eaf45a8-p015-b002"></a>
<!-- pdf-source: page=15; block=2; confidence=0.90 -->
**Theorem 2.** Observe $(Y_\lambda)_{\lambda\in\mathbb{N}^*}$ from the Gaussian sequence model (2.3); set $\beta=(\beta_\lambda)$, $\theta=\sum_{\lambda\in\mathbb{N}^*}\beta_\lambda^2$, $L(\beta)=\sum_{\lambda\in\mathbb{N}^*}\beta_\lambda\varepsilon_\lambda$. Let $K>1$, $\hat\theta$ the penalized estimator of Definition 3, and $\mathcal{S}_\gamma$ as in (3.1). For any $r < 2(K-1)$: $$\sup_{\beta\in\mathcal{S}_\gamma} \mathbb{E}_\beta\Big| \hat\theta - \theta - \frac{2L(\beta)}{\sqrt{n}} \Big|^r \le C(r)\, \inf_{m\in\mathbb{N}^*}\Big( \gamma_m^{2r} + \Big(\frac{m\log(m+1)}{n^2}\Big)^{r/2} \Big),$$ where $C(r)$ depends only on $r$.

<a id="pdf-5ada2eaf45a8-p015-b003"></a>
<!-- pdf-source: page=15; block=3; confidence=0.85 -->
**Comment (i).** Though nonasymptotic, the bound gives asymptotics: if $\inf_{m\in\mathbb{N}^*}\big(\gamma_m^{2r} + (m\log(m+1)/n^2)^{r/2}\big)$ is negligible relative to $n^{-r/2}$, then $\hat\theta$ is an efficient estimator of $\theta$; this depends on the structure of $\gamma$.

<a id="pdf-5ada2eaf45a8-p015-b004"></a>
<!-- pdf-source: page=15; block=4; confidence=0.82 -->
**Comment (ii).** An ellipsoid $\mathcal{E}_{2,c}\subset\Gamma_\gamma$ with $\gamma_m=c_m$; a hyperrectangle $\mathcal{E}_{\infty,c}\subset\Gamma_\gamma$ with $\gamma_m^2=\sum_{\lambda>m}c_\lambda^2$; an $l_p$-body $\mathcal{E}_{p,c}$ with $p>2$ and $\sum_{\lambda\in\mathbb{N}^*}c_\lambda^{(1/2-1/p)^{-1}}<\infty$ is contained with $\gamma_m=\big(\sum_{\lambda>m}c_\lambda^{(1/2-1/p)^{-1}}\big)^{1/2-1/p}$. Hence Theorem 2 applies to arbitrary $l_p$-bodies with $p\ge2$.

<a id="pdf-5ada2eaf45a8-p015-b005"></a>
<!-- pdf-source: page=15; block=5; confidence=0.83 -->
For the case $\gamma_m = R m^{-\alpha}$, write $\Gamma_\alpha(R)$ for the resulting $\Gamma_\gamma$. The following $l_p$-bodies are contained in $\Gamma_\alpha(R)$: (3.2) for $2\le p<\infty$, $B_{p,\alpha'}(R') = \{\gamma\in l_2(\mathbb{N}^*): \sum_{\lambda\in\mathbb{N}^*}\lambda^{p\alpha'}\|\gamma_\lambda\|^p \le (R')^p\}$; (3.3) for $p=\infty$, $B_{\infty,\alpha'}(R') = \{\gamma\in l_2(\mathbb{N}^*): \forall\lambda\in\mathbb{N}^*,\ \|\gamma_\lambda\|\le R'\lambda^{-\alpha'}\}$; where $\alpha'=1/2+\alpha-1/p$, $R'=R$ if $p=2$ and $R'=R\big(\alpha/(1/2-1/p)\big)^{1/2-1/p}$ otherwise.

<a id="pdf-5ada2eaf45a8-p016-b001"></a>
<!-- pdf-source: page=16; block=1; confidence=0.85 -->
Notes the inclusions 𝒮_α(R) ⊂ B_{α,2,∞}(R) ⊂ 𝒮_α(R·2^{2α}/√(2^α−1)), which yield a corollary of Theorem 2 giving risk bounds for the penalized estimator (Definition 3), uniform over the Besov body B_{α,2,∞}(R) and hence over the lp-body ℰ_{p,α'}(R') for p ≥ 2 with α' = 1/2 + (α − 1/p), where R' = R if p = 2 and R' = R(α/(1/2 − 1/p))^{1/2 − 1/p} otherwise.

<a id="pdf-5ada2eaf45a8-p016-b002"></a>
<!-- pdf-source: page=16; block=2; confidence=0.85 -->
**Corollary 1.** Under the Gaussian sequence model (2.3) with (Y_λ)_{λ∈ℕ*}, set β = (β_λ), θ = Σ_{λ∈ℕ*} β_λ². Let K > 1 be constant, θ̂ the corresponding penalized estimator (Definition 3), and r > 0 with r < 2(K − 1). For R > 0, α > 0 let the Besov body B_{α,2,∞}(R) be given by Definition 2. If nR² ≥ 1 then

sup_{s∈B_{α,2,∞}(R)} E_s |θ̂ − θ − 2L(s)/√n|^r ≤ C(r,α) [ R^{2r/(1+4α)} (log(1+nR²)/n²)^{2rα/(1+4α)} ],

with C(r,α) depending only on r, α. Consequently:

(3.4) if α ≤ 1/4: sup_{β∈B_{α,2,∞}(R)} E_β|θ̂ − θ|^r ≤ C'(r,α) R^{2r/(1+4α)} (log(1+nR²)/n²)^{2rα/(1+4α)};

(3.5) if α > 1/4: sup_{β∈B_{α,2,∞}(R)} E_β|θ̂ − θ|^r ≤ C'(r,α) R^r / n^{r/2},

with C'(r,α) depending only on r, α.

<a id="pdf-5ada2eaf45a8-p016-b003"></a>
<!-- pdf-source: page=16; block=3; confidence=0.82 -->
Continuation of **Corollary 1.** If β = (β_λ) ∈ B_{α,2,∞}(R) for some α > 1/4, then

(3.6) √n(θ̂ − θ) → 𝒩(0, 4θ) as n → ∞;

(3.7) n^{r/2} E_β‖θ̂ − θ‖^r → 2^r θ^{r/2} E‖ξ‖^r as n → ∞ if r ≥ 1, where ξ is a standard normal variable.

<a id="pdf-5ada2eaf45a8-p016-b004"></a>
<!-- pdf-source: page=16; block=4; confidence=0.80 -->
**Comments.** (i) When R is independent of n, the minimax convergence rate of θ̂ is (log n / n²)^{2α/(1+4α)} for α ≤ 1/4, while for α > 1/4 (3.6) shows θ̂ is efficient for θ. Cites Efroïmovich–Low (1996): the logarithmic factor is unavoidable for α < 1/4; via Lepskii's adaptation method they built an estimator adaptive on hyperrectangles ℓ_{∞,α'}(R) with α' = α + 1/2, achieving the optimal rate (log n / n²)^{2α/(1+4α)} for α < 1/4 and √n-consistent for α ≥ 1/4.

<a id="pdf-5ada2eaf45a8-p017-b001"></a>
<!-- pdf-source: page=17; block=1; confidence=0.90 -->
(i, cont.) The present estimator is additionally efficient for α > 1/4, with risk bounds valid simultaneously for all lp-bodies ℰ_{p,α'}(R) (not only hyperrectangles), and is easily computable; (3.4)–(3.5) are non-asymptotic and allow R to depend on n.

(ii) Replacing x_n = K log(n+1) by x_n = 1 in Definition 3 makes θ̂ attain rate 1/√n instead of log(n)/√n at α = 1/4, but θ̂ is then no longer efficient for α > 1/4, since the remainder R_n = (1/n^r) Σ_{m∈ℳ} D_m^{r/2} e^{−x_m} becomes of order n^{−r/2}.

<a id="pdf-5ada2eaf45a8-p017-b002"></a>
<!-- pdf-source: page=17; block=2; confidence=0.80 -->
**3.2. Arbitrary lp-bodies.** Proposes an estimator of θ adaptive over lp-bodies

ℓ_{p,c} = { γ ∈ l_p(ℕ*) : Σ_{λ∈ℕ*} |γ_λ / c_λ|^p ≤ 1 },

where (c_λ)_{λ∈ℕ*} is a positive nonincreasing unknown sequence satisfying (2.18) if p > 2. For p ≤ 2, ℓ_{p,c} ⊂ ℓ_{2,c} ⊂ ℰ_c (the set defined by (3.1)).

<a id="pdf-5ada2eaf45a8-p017-b003"></a>
<!-- pdf-source: page=17; block=3; confidence=0.80 -->
For m ∈ ℕ* set x_m = 3 log(m+1) and n·pen(m) = m + 1 + 2√((m+1)x_m) + 2x_m. Define

(3.8) θ̂(1) = sup_{m∈ℕ*} [ Σ_{λ=1}^m Y_λ² − pen(m) ].

By Theorem 1, for any p ≤ 2:

sup_{β∈ℓ_{p,c}} E_β |θ̂ − θ − 2L(β)/√n|^r ≤ C(r) inf_{m∈ℕ*} [ c_m^{2r} + (m log(m+1)/n²)^{r/2} ],

with C(r) depending only on r.

<a id="pdf-5ada2eaf45a8-p017-b004"></a>
<!-- pdf-source: page=17; block=4; confidence=0.82 -->
Notes the previous bound is too crude: for p < 2 nonlinear approximations outperform linear ones, motivating model collections where distinct models may share a dimension. For (N,D) ∈ (ℕ*)²:

(3.9) x_{N,D} = 3D(1 + log(N/D));

(3.10) n·w(N,D) = D + 1 + 2√((D+1)x_{N,D}) + 2x_{N,D}.

<a id="pdf-5ada2eaf45a8-p018-b001"></a>
<!-- pdf-source: page=18; block=1; confidence=0.80 -->
Let Γ̂_{N,D} be the set of indices of the D largest elements of { |Y_λ| : λ = 1, …, N }. Define

(3.11) θ̂(2) = sup_{N∈ℕ*} sup_{1≤D≤N} [ Σ_{λ∈Γ̂_{N,D}} Y_λ² − w(N,D) ].

<a id="pdf-5ada2eaf45a8-p018-b002"></a>
<!-- pdf-source: page=18; block=2; confidence=0.82 -->
θ̂(2) is a penalized estimator over the collection of all finite subsets of ℕ*; because infinitely many models share the same dimension, its penalty must be much larger than for θ̂(1) — improving bias control but worsening the variance term. Combining the two, θ̂ = θ̂(1) ∨ θ̂(2), performs as well as each.

<a id="pdf-5ada2eaf45a8-p018-b003"></a>
<!-- pdf-source: page=18; block=3; confidence=0.90 -->
**Theorem 3.** Under the Gaussian sequence model (2.3), set β = (β_λ), θ = Σ_{λ∈ℕ*} β_λ², L(β) = Σ_{λ∈ℕ*} β_λ ε_λ. Let θ̂(1), θ̂(2) be given by (3.8), (3.11) and θ̂ = θ̂(1) ∨ θ̂(2). For 0 < p ≤ ∞ and a nonincreasing nonnegative sequence c = (c_λ), there is an absolute constant C such that:

(i) if p < 2:
sup_{β∈Θ_{p,c}} E_β[(θ̂ − θ − 2L(β)/√n)²] ≤ C inf{ inf_{D∈ℕ*} [ c_D⁴ + D log(D+1)/n² ],  inf_{N∈ℕ*} inf_{1≤D≤N} [ (D^{1−2/p} c_D²)² + (D(1 + log(N/D))/n)² ] + c_N⁴ };

(ii) (3.12) if γ is nonincreasing:
sup_{β∈𝒮_γ} E_β[(θ̂ − θ − 2L(β)/√n)²] ≤ C inf_{D∈ℕ*} [ γ_D⁴ + D log(D+1)/n² ].

<a id="pdf-5ada2eaf45a8-p019-b001"></a>
<!-- pdf-source: page=19; block=1; confidence=0.90 -->
Continues a preceding result: $\Theta_{2,c} \subseteq \mathcal{S}_c$, and for $p > 2$, under condition (2.18), $\Theta_{p,c} \subseteq \mathcal{S}_\gamma$, where the sequence $\gamma = (\gamma_D)$ is given by $\gamma_D = \big(\sum_{\lambda>D} c_\lambda^{(1/2-1/p)^{-1}}\big)^{1/2-1/p}$.

<a id="pdf-5ada2eaf45a8-p019-b002"></a>
<!-- pdf-source: page=19; block=2; confidence=0.82 -->
**Definition (adaptive threshold estimator).** For (N,D) ∈ (ℕ*)², set x_{N,D} = 3D(1 + log N) and w(N,D) = 2D + 2√(2D·x_{N,D}) + 2x_{N,D}. Define

θ̃(2) = sup_{N∈ℕ*} sup_{A⊂{1,…,N}} ( Σ_{λ∈A} Y²_λ − w(N,|A|) ).

Since w(N,|A|) is proportional to |A|, θ̃(2) is an adaptive threshold estimator, explicitly

θ̃(2) = sup_{N∈ℕ*} Σ_{λ=1}^{N} ( Y²_λ − (2/n)[1 + √(6(1+log N)) + 3(1+log N)] ) · 1{ Y²_λ > (2/n)[1 + √(6(1+log N)) + 3(1+log N)] }.

<a id="pdf-5ada2eaf45a8-p019-b003"></a>
<!-- pdf-source: page=19; block=3; confidence=0.85 -->
Replacing θ̂(2) by θ̃(2) in the θ̂ of Theorem 3 degrades the quadratic-risk control: the factor log(N/D) becomes log(N). The compensating advantage of θ̃(2) is its more explicit expression.

<a id="pdf-5ada2eaf45a8-p019-b004"></a>
<!-- pdf-source: page=19; block=4; confidence=0.88 -->
**Definition (3.13).** For p > 0, α' > 0, R > 0, the lp-body is

Θ_{p,α'}(R) = { β ∈ lp(ℕ*) : Σ_{λ∈ℕ*} λ^{pα'} |β_λ|^p ≤ R^p }.

Θ_{p,α'}(R) ⊆ l2(ℕ*) when α' > 0 and α = α' − 1/2 + 1/p > 0.

<a id="pdf-5ada2eaf45a8-p019-b005"></a>
<!-- pdf-source: page=19; block=5; confidence=0.85 -->
**Corollary 2 (statement, setup).** Observe (Y_λ)_{λ∈ℕ*} from the Gaussian sequence model (2.3). Put β = (β_λ), θ = Σ_{λ} β²_λ, and L(β) = Σ_{λ} β_λ ε_λ. Let θ̂(1), θ̂(2) be given by (3.8) and (3.11), and set θ̂ = θ̂(1) ∨ θ̂(2). Uniform risk bounds for θ̂ over the lp-bodies Θ_{p,α'}(R) follow (stated on the next page).

<a id="pdf-5ada2eaf45a8-p020-b001"></a>
<!-- pdf-source: page=20; block=1; confidence=0.86 -->
**Corollary 2 (bounds).** Let p > 0, α' > 0, R > 0; set α = α' − 1/2 + 1/p and assume α > 0. If nR² ≥ 1:

(i) If p < 2, (3.14):
sup_{β∈Θ_{p,α'}(R)} E_β[ (θ̂ − θ − 2L(β)/√n)² ] ≤ C(p,α) · inf{ R^{4/(1+4α')} (log(1+nR²)/n²)^{4α'/(1+4α')} , R^{4/(1+2α)} (log(1+nR²)/n)^{4α/(1+2α)} }, with C(p,α) depending only on p, α.

(ii) (3.15): over the Besov body Θ_{α,2,∞}(R),
sup_{β∈Θ_{α,2,∞}(R)} E_β[ (θ̂ − θ − 2L(β)/√n)² ] ≤ C(α) R^{4/(1+4α)} (log(1+nR²)/n²)^{4α/(1+4α)}, with C(α) depending only on α.

<a id="pdf-5ada2eaf45a8-p020-b002"></a>
<!-- pdf-source: page=20; block=2; confidence=0.85 -->
(i) (3.15) yields the same bounds as Corollary 1. (ii) For 1 < p < 2 the rates are unusual and their optimality is unknown. (iii) Efficiency: comparing the RHS of (3.14) with 1/n, θ̂ is efficient when 4/3 ≤ p ≤ 2 provided α' > 1/4, and when p ≤ 4/3 provided α' > 1 − 1/p; in particular θ̂ is always efficient for p ≤ 1. (iv) Since ||β||² ≤ R² for β ∈ Θ_{p,α'}(R) with p < 2, (3.14) gives an upper bound for the uniform quadratic risk of θ̂, equal up to a constant to inf{ R^{4/(1+4α')}(log(1+nR²)/n²)^{4α'/(1+4α')}, R^{4/(1+2α)}(log(1+nR²)/n)^{4α/(1+2α)} } + R²/n.

<a id="pdf-5ada2eaf45a8-p021-b001"></a>
<!-- pdf-source: page=21; block=1; confidence=0.90 -->
Case where Theorem 3 applies but Corollary 2 does not: lp-bodies Θ_{p,c} with p < 2 and c_λ → 0 slowly. For c_λ = R(log λ)^{−η}, η > 0, (3.16):
sup_{β∈Θ_{p,c}} E_β[ (θ̂ − θ − 2L(β)/√n)² ] ≤ C(R,p,η) · inf{ (log(1+n))^{−4}, n^{(2−p)((1/η)(1/p−1/2)−1)} log²(1+n) }. The rate of θ̂(1) is always logarithmic, equal to (log(1+n))^{−2η}, whereas θ̂(2) (hence θ̂) attains a negative power of n as soon as η > 1/p − 1/2.

<a id="pdf-5ada2eaf45a8-p021-b002"></a>
<!-- pdf-source: page=21; block=2; confidence=0.82 -->
**§3.3 Special strategy for Besov bodies.** Goal: estimate Σ_λ β²_λ when (β_λ) lies in an unknown Besov body Θ_{α,p,∞}. Starts with p = 2 (adaptive estimators already given in §3.1, Corollary 1), aiming to show that Johnstone's (1999) level thresholding estimators are penalized estimators.

<a id="pdf-5ada2eaf45a8-p021-b003"></a>
<!-- pdf-source: page=21; block=3; confidence=0.85 -->
**§3.3.1 (definitions).** For $j \in \mathbb{N}^*$, $\Lambda(j) = \{2^j, \dots, 2^{j+1}-1\}$, so $\mathbb{N}^* = \cup_{j\ge0} \Lambda(j)$. Let $\overline{\mathcal{J}}$ be the family of all subsets of $\{0,\dots,J\}$ with $J = \lfloor\log_2(n^2)\rfloor$; for $\mathcal{J} \in \overline{\mathcal{J}}$ put $m_{\mathcal{J}} = \cup_{j\in\mathcal{J}} \Lambda(j)$, and $\mathcal{M} = \{ m_{\mathcal{J}} : \mathcal{J} \in \overline{\mathcal{J}} \}$. For $j \in \mathbb{N}$ define the weight via
$$n\,w(j) = (2^j + 1) + 2\sqrt{ (2^j+1)\cdot 2C \log(2^J) } + 4C \log(2^J),$$
$C > 1$ a numerical constant. Penalty (3.17): $\mathrm{pen}(m_{\mathcal{J}}) = \sum_{j\in\mathcal{J}} w(j)$. The penalized estimator is an explicit level thresholding estimator (analogue of Donoho–Johnstone 1999):
$$\sup_{\mathcal{J}\in\overline{\mathcal{J}}} \Big( \sum_{\lambda\in m_{\mathcal{J}}} Y^2_\lambda - \mathrm{pen}(m_{\mathcal{J}}) \Big) = \sup_{\mathcal{J}\subset\{0,\dots,J\}} \sum_{j\in\mathcal{J}} \Big( \sum_{\lambda\in\Lambda(j)} Y^2_\lambda - w(j) \Big) = \sum_{j=0}^{J} \Big( \sum_{\lambda\in\Lambda(j)} Y^2_\lambda - w(j) \Big) \mathbb{1}\{ \sum_{\lambda\in\Lambda(j)} Y^2_\lambda \ge w(j) \}.$$

<a id="pdf-5ada2eaf45a8-p022-b001"></a>
<!-- pdf-source: page=22; block=1; confidence=0.90 -->
The penalty (3.17) satisfies condition (2.5) by taking $x_m = 2C\log(2^J)$ for each $m$, and Corollary 1's results still hold for this level-thresholding estimator. A related estimator was introduced by Gayraud and Tribouley (1999), who use

$$(3.18)\quad \sum_{\lambda\in\hat m} Y_\lambda^2 - \tfrac{D_{\hat m}}{n},\qquad \hat m = \arg\max_{m}\Big(\sum_{\lambda\in m} Y_\lambda^2 - \mathrm{pen}(m)\Big),$$

instead of $\sum_{\lambda\in\hat m} Y_\lambda^2 - \mathrm{pen}(\hat m)$ used here and in Johnstone (1999). Their proof is asymptotic and specific to level thresholding; whether (3.18) enjoys the same properties as the present estimator under the generality of Theorem 1 is unknown.

<a id="pdf-5ada2eaf45a8-p022-b002"></a>
<!-- pdf-source: page=22; block=2; confidence=0.90 -->
**Section 3.3.2. The Birgé–Massart algorithm.** Aim: exploit that $\beta$ lies in an unknown Besov body to penalize over fewer models and improve the risk bound.

<a id="pdf-5ada2eaf45a8-p022-b003"></a>
<!-- pdf-source: page=22; block=3; confidence=0.85 -->
**Definition (Birgé–Massart procedure).** Using the compression algorithm of Birgé and Massart (2000a), for any $J\in\mathbb{N}$ there is a nonlinear approximation $\tilde\beta(J)$ of $\beta$ with

$$(3.19)\quad \|\beta - \tilde\beta(J)\| \le C(\alpha,p)\,R\,2^{-J\alpha},$$

provided $\beta\in\mathcal{B}_{\alpha,p,\infty}(R)$ with $\alpha > 1/p - 1/2$. Set $\Lambda(j)=\{2^j,\dots,2^{j+1}-1\}$. At each resolution level $j$ keep the $K_J(j)$ largest coefficients (in absolute value): $K_J(j)=2^j$ for $j\le J$ (all coefficients), and $K_J(j)=\lceil 2^J/(j-J)^3\rceil$ for $j>J$; the total number kept is of order $2^J$. Define

$$n\,w^{(1)}(J) = 2^{J+1} + 1 + 2\sqrt{2(2^{J+1}+1)\log(2^{J+1})} + 4\log(2^{J+1}),$$

and

$$(3.20)\quad \hat\theta^{(1)} = \sup_{J\in\mathbb{N}}\Big[\sum_{j=0}^{J}\sum_{\lambda\in\Lambda(j)} Y_\lambda^2 - w^{(1)}(J)\Big].$$

Let $\tilde\Lambda_J(j)\subset\Lambda(j)$ be the subset of the $K_J(j)$ indices with the largest values among $\{|Y_\lambda| : \lambda\in\Lambda(j)\}$.

<a id="pdf-5ada2eaf45a8-p023-b001"></a>
<!-- pdf-source: page=23; block=1; confidence=0.85 -->
**Definition (θ̂^(2)).** Set $D_J = \sum_{j=0}^{+\infty} K_J(j)$ and $n\,w^{(2)}(J) = 10.5\,(D_J + 1)$. Define

$$(3.21)\quad \hat\theta^{(2)} = \sup_{J\in\mathbb{N}}\Big[\sum_{j=0}^{+\infty}\sum_{\lambda\in\tilde\Lambda_J(j)} Y_\lambda^2 - w^{(2)}(J)\Big].$$

<a id="pdf-5ada2eaf45a8-p023-b002"></a>
<!-- pdf-source: page=23; block=2; confidence=0.82 -->
**Theorem 4.** Observe $(Y_\lambda)_{\lambda\in\Lambda^*}$ from the Gaussian sequence model (2.3); set $\beta=(\beta_\lambda)$, $\theta=\sum_\lambda \beta_\lambda^2$, and $L(\beta)=\sum_\lambda \beta_\lambda A_\lambda$. With $\hat\theta^{(1)},\hat\theta^{(2)}$ from (3.20),(3.21), define $\hat\theta = \hat\theta^{(1)}\vee\hat\theta^{(2)}$. Let $0<p\le+\infty$, $\alpha>0$, $R>0$, and $\alpha' = 1/2 + \alpha - 1/p > 0$. As soon as $nR^2\ge 1$:

(i) If $p<2$,
$$\sup_{\beta\in\Theta_{\alpha,p,\infty}(R)}\mathbb{E}_\beta\Big[\big(\hat\theta - \theta - \tfrac{2L(\beta)}{\sqrt n}\big)^2\Big] \le C(p,\alpha)\,\inf\Big\{ R^{4/(1+4\alpha')}\big(\tfrac{\log(1+nR^2)}{n^2}\big)^{4\alpha'/(1+4\alpha')},\; R^{4/(1+2\alpha)}n^{-4\alpha/(1+2\alpha)}\Big\},$$
with $C(p,\alpha)$ depending on $p,\alpha$.

(ii) If $p\ge 2$, then $\Theta_{\alpha,p,\infty}(R)\subseteq\Theta_{\alpha,2,\infty}(R)$ and
$$\sup_{\beta\in\Theta_{\alpha,2,\infty}(R)}\mathbb{E}_\beta\Big[\big(\hat\theta - \theta - \tfrac{2L(\beta)}{\sqrt n}\big)^2\Big] \le C(\alpha)\,R^{4/(1+4\alpha)}\big(\tfrac{\log(1+nR^2)}{n^2}\big)^{4\alpha/(1+4\alpha)},$$
with $C(\alpha)$ depending on $\alpha$.

<a id="pdf-5ada2eaf45a8-p023-b003"></a>
<!-- pdf-source: page=23; block=3; confidence=0.83 -->
**Comments.** (i) When $p=q$, the Besov body $\Theta_{\alpha,p,q}(R)$ coincides with the $l_p$-body $l_{p,c}$ for $c_\lambda = 2^{-j\alpha'}$ ($\lambda\in\Lambda(j)$), so Corollary 2 and Theorem 4 are comparable. Since $\Theta_{\alpha,p,p}(R)\subset\Theta_{\alpha,p,\infty}(R)$, Theorem 4 gives for $p<2$ the same bound as in (i). In Corollary 2 the factor $n^{-4\alpha/(1+2\alpha)}$ is replaced by $(n/\log(1+nR^2))^{-4\alpha/(1+2\alpha)}$, so Theorem 4's rate is slightly better…

<a id="pdf-5ada2eaf45a8-p024-b001"></a>
<!-- pdf-source: page=24; block=1; confidence=0.86 -->
…by saving a logarithmic factor. Nevertheless Corollary 2 is more general — e.g. it handles sequences $(c_\lambda)$ converging very slowly to $0$, as in (3.16). (ii) Because the estimator of Theorem 4 and that of the previous section behave similarly in risk, the earlier comments on Corollary 2 remain valid.

<a id="pdf-5ada2eaf45a8-p024-b002"></a>
<!-- pdf-source: page=24; block=2; confidence=0.92 -->
**Section 4. Proof of the main theorem.** The key tool for Theorem 1 is an exponential inequality for chi-square distributions.

<a id="pdf-5ada2eaf45a8-p024-b003"></a>
<!-- pdf-source: page=24; block=3; confidence=0.92 -->
**Section 4.1. An exponential inequality for chi-square distributions.** A slightly more general inequality than needed for Theorem 1 is proved.

<a id="pdf-5ada2eaf45a8-p024-b004"></a>
<!-- pdf-source: page=24; block=4; confidence=0.90 -->
**Lemma 1.** Let $Y_1,\dots,Y_D$ be i.i.d. Gaussian with mean $0$ and variance $1$, and $a_1,\dots,a_D\ge 0$. Set $\|a\|_\infty = \sup_{i=1,\dots,D}|a_i|$, $\|a\|_2^2 = \sum_{i=1}^D a_i^2$, and $Z = \sum_{i=1}^D a_i(Y_i^2 - 1)$. Then for any $x>0$:
$$(4.1)\quad \mathbb{P}\big(Z \ge 2\|a\|_2\sqrt{x} + 2\|a\|_\infty x\big) \le e^{-x},$$
$$(4.2)\quad \mathbb{P}\big(Z \le -2\|a\|_2\sqrt{x}\big) \le e^{-x}.$$

<a id="pdf-5ada2eaf45a8-p024-b005"></a>
<!-- pdf-source: page=24; block=5; confidence=0.90 -->
**Corollary (chi-square).** If $U$ is a $\chi^2$ statistic with $D$ degrees of freedom, then for any $x>0$:
$$(4.3)\quad \mathbb{P}\big(U - D \ge 2\sqrt{Dx} + 2x\big) \le e^{-x},$$
$$(4.4)\quad \mathbb{P}\big(D - U \ge 2\sqrt{Dx}\big) \le e^{-x}.$$

<a id="pdf-5ada2eaf45a8-p024-b006"></a>
<!-- pdf-source: page=24; block=6; confidence=0.88 -->
**Proof of Lemma 1.** For $Y\sim\mathcal{N}(0,1)$, let $\psi$ be the log-Laplace transform of $Y^2-1$:
$$\psi(u) = \log\mathbb{E}\big[\exp(u(Y^2-1))\big] = -u - \tfrac{1}{2}\log(1-2u).$$
Then for $0<u<1/2$,
$$\psi(u) \le \frac{u^2}{1-2u}.$$
[Proof continues beyond the supplied pages.]

<a id="pdf-5ada2eaf45a8-p025-b001"></a>
<!-- pdf-source: page=25; block=1; confidence=0.82 -->
**Proof (concluded).** Using the series identities $\psi(u)=2u^2\sum_{k\ge0}\frac{(2u)^k}{k+2}$ and $\frac{u^2}{1-2u}=u^2\sum_{k\ge0}(2u)^k$, the log-MGF is bounded by
$$\log\mathbb{E}[e^{uZ}]=\sum_{i=1}^{D}\log\mathbb{E}\big[\exp(a_i u(Y_i^2-1))\big]\le\sum_{i=1}^{D}\frac{a_i^2u^2}{1-2a_iu}\le\frac{\|a\|_2^2\,u^2}{1-2\|a\|_\infty u}.$$
Invoking Birgé and Massart (1998): if $\log\mathbb{E}[e^{uZ}]\le\frac{vu^2}{2(1-cu)}$ then for any $x>0$, $\mathbb{P}(Z\ge cx+\sqrt{2vx})\le e^{-x}$; hence (4.1) holds. For (4.2), note that for $-1/2<u<0$, $\psi(u)\le u^2$. This concludes the proof of Lemma 1. $\square$

<a id="pdf-5ada2eaf45a8-p025-b002"></a>
<!-- pdf-source: page=25; block=2; confidence=0.97 -->
**4.2. Proof of Theorem 1.**

<a id="pdf-5ada2eaf45a8-p025-b003"></a>
<!-- pdf-source: page=25; block=3; confidence=0.95 -->
**Proof of Theorem 1.** The goal is to establish inequality (2.8). Set $V_m=\hat\theta_m-\theta-2L(s)/\sqrt{n}$. By definition of $\hat\theta$,
$$\hat\theta-\theta-\frac{2L(s)}{\sqrt n}=\sup_{m\in\mathcal M}V_m.$$
Since $\big|\sup_{m}V_m\big|\le\big(\sup_{m}(V_m)_+\big)\vee\big(\inf_{m}(V_m)_-\big)$, one gets
$$(4.5)\qquad \mathbb{E}_s\Big[\big|\sup_{m\in\mathcal M}V_m\big|^r\Big]\le\sum_{m\in\mathcal M}\mathbb{E}_s\big[(V_m)_+^r\big]+\inf_{m\in\mathcal M}\mathbb{E}_s\big[(V_m)_-^r\big].$$
To control $\mathbb{E}_s[(V_m)_+^r]$ for $m\in\mathcal M^*$, take an orthonormal basis $(\varphi_\lambda,\lambda\in\Lambda_m)$ of $S_m$ with $|\Lambda_m|=D_m$, put $\beta_\lambda=\langle s,\varphi_\lambda\rangle$, and recall $s_m=\sum_{\lambda\in\Lambda_m}\beta_\lambda\varphi_\lambda$, $\hat s_m=\sum_{\lambda\in\Lambda_m}Y(\varphi_\lambda)\varphi_\lambda$.

<a id="pdf-5ada2eaf45a8-p026-b001"></a>
<!-- pdf-source: page=26; block=1; confidence=0.82 -->
**Proof (cont.).** By orthogonality,
$$V_m=\|\hat s_m-s_m\|^2-\mathrm{pen}(m)+2\langle s_m,\hat s_m-s_m\rangle-\tfrac{2}{\sqrt n}L(s)-\|s-s_m\|^2=\tfrac1n\sum_{\lambda\in\Lambda_m}L^2(\varphi_\lambda)-\mathrm{pen}(m)+\tfrac{2}{\sqrt n}L(s_m-s)-\|s-s_m\|^2.$$
Applying $2ab\le a^2+b^2$,
$$V_m\le\tfrac1n\sum_{\lambda\in\Lambda_m}L^2(\varphi_\lambda)-\mathrm{pen}(m)+\tfrac{L^2(s-s_m)}{n\|s-s_m\|^2}.$$
Here $Z_m=\sum_{\lambda\in\Lambda_m}L^2(\varphi_\lambda)$ is a $\chi^2$ statistic with $D_m$ degrees of freedom. Setting $W_m=\frac{L(s-s_m)}{\|s-s_m\|}$, $W_m\sim\mathcal N(0,1)$ is independent of $(L(\varphi_\lambda),\lambda\in\Lambda_m)$; hence $U_m=Z_m+W_m^2$ is $\chi^2$ with $D_m+1$ degrees of freedom and $V_m\le U_m/n-\mathrm{pen}(m)$. Using inequality (4.3) with condition (2.5),
$$\mathbb{P}\big(nV_m\ge h(\xi)\big)\le e^{-x_m}e^{-\xi},\qquad h(\xi)=2\sqrt{(D_m+1)\xi}+2\xi.$$

<a id="pdf-5ada2eaf45a8-p026-b002"></a>
<!-- pdf-source: page=26; block=2; confidence=0.90 -->
**Proof (cont.).** Via the identity $\mathbb{E}_s[(V_m)_+^r]=\frac{r}{n^r}\int_0^\infty t^{r-1}\mathbb{P}(nV_m\ge t)\,dt$ and the elementary bound $h^{-1}(t)\ge\frac{t^2}{4((D_m+1)+t)}\ge\frac{t^2}{8(D_m+1)}\wedge\frac{t}{8}$,
$$\int_0^{+\infty}t^{r-1}\mathbb{P}(nV_m\ge t)\,dt\le e^{-x_m}\Big[(D_m+1)^{r/2}\!\!\int_0^{+\infty}\! y^{r-1}e^{-y^2/8}dy+\int_0^{+\infty}\! y^{r-1}e^{-y/8}dy\Big].$$
Hence $\mathbb{E}_s[(V_m)_+^r]\le\frac{C(r)}{n^r}\,e^{-x_m}D_m^{r/2}$. For $m=0$, similarly $V_m\le W_0^2/n$ with $W_0$ standard Gaussian; defining $\Gamma_r=\frac{1}{\sqrt{2\pi}}\int_0^\infty x^r e^{-x^2/2}dx$, one gets $\mathbb{E}_s[(V_0)_+^r]\le\frac{\Gamma_{2r}}{n^r}$.

<a id="pdf-5ada2eaf45a8-p027-b001"></a>
<!-- pdf-source: page=27; block=1; confidence=0.80 -->
**Proof (concluded).** By (4.5) the preceding bounds establish (2.8). For (2.9), recall that for all $m\in\mathcal M$,
$$-V_m=-\tfrac{Z_m}{n}+\mathrm{pen}(m)+\|s-s_m\|^2+\tfrac{2}{\sqrt n}\big(L(s-s_m)\big).$$
By convexity/subadditivity of $x\mapsto x^r$ (according as $r\ge1$ or $r<1$),
$$(V_m)_-^r\le 4^{(r-1)_+}\Big[\tfrac{(D_m-Z_m)_+^r}{n^r}+\big(\mathrm{pen}(m)-\tfrac{D_m}{n}\big)^r\Big]+4^{(r-1)_+}\Big[\|s-s_m\|^{2r}+\mathbb{E}_s\big[\big(\tfrac{2}{\sqrt n}L(s-s_m)\big)_+^r\big]\Big].$$
Using (4.4), $\mathbb{E}_s[(D_m-Z_m)_+^r]\le\sqrt{2\pi}\,2^r D_m^{r/2}\,r D_{r-1}$; also $\mathbb{E}_s[(L(s-s_m))_+^r]=\|s-s_m\|^r D_r$; and by $2ab\le a^2+b^2$, $\mathbb{E}_s[(\tfrac{2}{\sqrt n}L(s-s_m))_+^r]\le 2^{r-1}D_r(n^{-r}+\|s-s_m\|^{2r})$. Then (2.9) follows. $\square$

<a id="pdf-5ada2eaf45a8-p027-b002"></a>
<!-- pdf-source: page=27; block=2; confidence=0.95 -->
**5. Proofs of the results about the Gaussian sequence model.** To prove Theorems 2, 3 and 4, apply Theorem 1, with the following notation. Work in the Hilbert space $\mathbb H=l^2(\mathbb N^*)$ with canonical basis $(\varphi_\lambda,\lambda\in\mathbb N^*)$. Observing $(Y_\lambda)_{\lambda\in\mathbb N^*}$ as in (2.3), define a Gaussian linear process $Y(\cdot)$ with mean $s=\beta=(\beta_\lambda)_{\lambda\in\mathbb N^*}$ and variance $1/n$ by $Y(t)=\sum_{\lambda\in\mathbb N^*}t_\lambda Y_\lambda$. Consider model collections $(S_m)_{m\in\mathcal M}$ where $S_m=\mathrm{span}(\varphi_\lambda,\lambda\in\Lambda_m)$ for $\Lambda_m\subset\mathbb N^*$, of dimension $D_m=|\Lambda_m|$ (the exact $(\Lambda_m)$ depends on the theorem). The orthogonal projection of $s$ onto $S_m$ and the projection estimator expand as $s_m=\sum_{\lambda\in\Lambda_m}\beta_\lambda\varphi_\lambda$, $\hat s_m=\sum_{\lambda\in\Lambda_m}Y_\lambda\varphi_\lambda$. $C$ denotes constants that may change line to line, with dependencies noted (e.g. $C(\alpha)$ depends only on $\alpha$).

<a id="pdf-5ada2eaf45a8-p028-b001"></a>
<!-- pdf-source: page=28; block=1; confidence=0.90 -->
**Proof of Theorem 2 (§5.1).** Take the model set $\mathcal{M}=\mathbb{N}^*$ with $\Lambda_m=\{1,2,\dots,m\}$, penalties $\mathrm{pen}(m)$ and weights $x_m$ from Definition 3, and apply Theorem 1 to the penalized estimator. Assumption (2.7) holds: $\Sigma_r=\sum_{m\ge1}m^{r/2}\exp(-K\log(m+1))\le\sum_{m\ge1}m^{-K+r/2}<\infty$ since $K>1+r/2$. By (2.8)–(2.9), for any $r>0$ and $s\in\mathcal{S}_\gamma$,
$$\mathbb{E}_s\big|\hat\theta-\theta-\tfrac{2L(s)}{\sqrt n}\big|^r\le C(r)\Big(T_n+\tfrac{\Sigma_r}{n^r}\Big),\quad T_n=\inf_{m\in\mathbb{N}^*}\Big\{\|s-s_m\|^{2r}+\big(\tfrac{m\log(m+1)}{n^2}\big)^{r/2}\Big\}.$$
For $s=(\beta_\lambda)_{\lambda\in\mathbb{N}^*}\in\mathcal{S}_\gamma$, $\|s-s_m\|^2=\sum_{\lambda>m}\beta_\lambda^2\le\gamma_m^2$, which concludes the proof (possibly enlarging $C(r)$). ∎

<a id="pdf-5ada2eaf45a8-p028-b002"></a>
<!-- pdf-source: page=28; block=2; confidence=0.82 -->
**Proof of Corollary 1 (§5.2).** If $s=(\beta_\lambda)_{\lambda\in\mathbb{N}^*}$ lies in the Besov body $\mathcal{B}_{\alpha,2,\infty}(R)$, then $\forall m\in\mathbb{N}^*$: $\sum_{\lambda>m}\beta_\lambda^2\le R^2m^{-2\alpha}\,\dfrac{2^{4\alpha}}{2^{2\alpha}-1}$. Hence by Theorem 2, for $r\le2(K-1)$,
$$\sup_{s\in\mathcal{B}_{\alpha,2,\infty}(R)}\mathbb{E}_s\big|\hat\theta-\theta-\tfrac{2L(s)}{\sqrt n}\big|^r\le C(r,\alpha)\inf_{m\in\mathbb{N}^*}\Big\{R^{2r}m^{-2r\alpha}+\big(\tfrac{m\log(m+1)}{n^2}\big)^{r/2}\Big\}.$$
Set $m_n=\big(\tfrac{n^2R^4}{\log(1+n^2R^4)}\big)^{1/(1+4\alpha)}$. Since $x\ge\log(1+x)$ for $x>0$, $m_n\ge1\vee\tfrac12\big(\tfrac{n^2R^4}{\log(1+n^2R^4)}\big)^{1/(1+4\alpha)}$; and since $nR^2\ge1$, $m_n\le2n^2R^4$ and $\log(m_n+1)\le\log(1+2n^2R^4)\le2\log(1+n^2R^4)$.

<a id="pdf-5ada2eaf45a8-p029-b001"></a>
<!-- pdf-source: page=29; block=1; confidence=0.90 -->
**Proof of Corollary 1 (continued).** Therefore
$$\sup_{s\in\mathcal{B}_{\alpha,2,\infty}(R)}\mathbb{E}_s\big|\hat\theta-\theta-\tfrac{2L(s)}{\sqrt n}\big|^r\le C(r,\alpha)R^{2r/(1+4\alpha)}\big(\tfrac{\log(1+n^2R^4)}{n^2}\big)^{2r\alpha/(1+4\alpha)}\le C(r,\alpha)R^{2r/(1+4\alpha)}\big(\tfrac{\log(1+nR^2)}{n^2}\big)^{2r\alpha/(1+4\alpha)},$$
proving (3.4). This gives $\sup_s\mathbb{E}_s|\hat\theta-\theta|^r\le C(r,\alpha)\big[R^{2r/(1+4\alpha)}(\tfrac{\log(1+nR^2)}{n^2})^{2r\alpha/(1+4\alpha)}+R^rn^{-r/2}\big]$, using $\mathbb{E}_s|2L(s)/\sqrt n|^r\le C(r,\alpha)R^rn^{-r/2}$. For $\alpha\le1/4$, $nR^2\ge1$: $R^rn^{-r/2}\le C(r,\alpha)R^{2r/(1+4\alpha)}(\tfrac{\log(1+nR^2)}{n^2})^{2r\alpha/(1+4\alpha)}$, so (3.4) holds. For $\alpha>1/4$: the reverse bound $\le C(r,\alpha)R^rn^{-r/2}$ holds, giving (3.5). For fixed $R>0,\ \alpha>1/4$ as $n\to\infty$, $(n^2/\log n)^{-2r\alpha/(1+4\alpha)}=o(n^{-r/2})$, hence $\mathbb{E}_s|\sqrt n(\hat\theta-\theta)-2L(s)|^r\to0$; since $L(s)\sim\mathcal{N}(0,\theta)$, $\sqrt n(\hat\theta-\theta)\xrightarrow{d}\mathcal{N}(0,4\theta)$. For $r\ge1$, by the triangle inequality $n^{r/2}\mathbb{E}_s|\hat\theta-\theta|^r\to2^r\mathbb{E}_s|L(s)|^r=2^r\theta^{r/2}\mathbb{E}|\xi|^r$, $\xi$ standard normal. ∎

<a id="pdf-5ada2eaf45a8-p029-b002"></a>
<!-- pdf-source: page=29; block=2; confidence=0.90 -->
**Proof of Theorem 3 (§5.3).** Define $\mathcal{M}^{(1)}=\mathbb{N}^*$ and $\mathcal{M}^{(2)}=\{m=(N,A_N):A_N\in\mathcal{P}(1,2,\dots,N),\ N\in\mathbb{N}^*\}$, where $\mathcal{P}(1,\dots,N)$ is the set of all nonempty subsets of $\{1,\dots,N\}$. Let $\mathcal{M}=\mathcal{M}^{(1)}\times\{1\}\oplus\mathcal{M}^{(2)}\times\{2\}$. For $m=m_1\times\{1\}$: $\Lambda_m=\Lambda_{m_1}=\{1,\dots,m_1\}$; for $m=m_2\times\{2\}$ with $m_2=(N,A_N)$: $\Lambda_m=\Lambda_{m_2}=A_N$. For $m=m_1\times\{1\}$ take $\mathrm{pen}(m)=\mathrm{pen}(m_1)$ and $x_m=x_{m_1}$ (Definition 3 with $K=3$); for $m=m_2\times\{2\}$ take $x_m=x_{N,|A_N|}$ [defined by (3.9)] and $\mathrm{pen}(m)=w(N,|A_N|)$ [given by (3.10)].

<a id="pdf-5ada2eaf45a8-p030-b001"></a>
<!-- pdf-source: page=30; block=1; confidence=0.83 -->
**Proof of Theorem 3 (continued).** Then $\hat\theta^{(1)}=\sup_{m_1\in\mathcal{M}^{(1)}}\big(\sum_{\lambda\in\Lambda_{m_1}}Y_\lambda^2-\mathrm{pen}(m_1)\big)$, and since for fixed $N$ the penalty of $m_2=(N,A_N)\in\mathcal{M}^{(2)}$ depends on $A_N$ only through its cardinality, $\hat\theta^{(2)}=\sup_{m_2\in\mathcal{M}^{(2)}}\big(\sum_{\lambda\in\Lambda_{m_2}}Y_\lambda^2-\mathrm{pen}(m_2)\big)$; hence $\hat\theta=\hat\theta^{(1)}\vee\hat\theta^{(2)}=\sup_{m\in\mathcal{M}}\big(\sum_{\lambda\in\Lambda_m}Y_\lambda^2-\mathrm{pen}(m)\big)$. Apply Theorem 1 with $r=2$: check (2.7) via $\Sigma_2=S^{(1)}+S^{(2)}$, $S^{(i)}=\sum_{m\in\mathcal{M}^{(i)}}D_m e^{-x_m}$. Then $S^{(1)}=\sum_{m\ge2}m^{-2}\le1$. Also $S^{(2)}\le\sum_{N\in\mathbb{N}^*}\sum_{1\le D\le N}\binom{N}{D}D\exp\!\big(-3D(1+\log(N/D))\big)$. Using $\binom{N}{D}\le(eN/D)^D$, $S^{(2)}\le\sum_{N}\sum_{1\le D\le N}De^{-2D}(N/D)^{-2D}$. Since $De^{-2D}\le1$ for $D\le N^{1/4}$ and $(N/D)^{-D}\le1$ for $N^{1/4}<D\le N$,
$$\sum_{1\le D\le N}De^{-2D}(N/D)^{-2D}\le\sum_{1\le D\le N^{1/4}}(N/D)^{-2D}+\sum_{N^{1/4}<D\le N}De^{-2D}\le\frac{N^{-3/2}}{1-N^{-3/2}}+N^2e^{-N/2}.$$
Therefore $S^{(2)}$ converges. ∎

<a id="pdf-5ada2eaf45a8-p031-b001"></a>
<!-- pdf-source: page=31; block=1; confidence=0.90 -->
**Proof (continued, Theorem 3).** By Theorem 1, for any $s\in\Theta_{p,c}$,
$$\mathbb{E}_s\Big[\big(\hat\theta-\theta-\tfrac{2L(s)}{\sqrt n}\big)^2\Big]\le C\Big(T_n^{(1)}\wedge T_n^{(2)}+\tfrac{\Sigma_2}{n^2}\Big),\tag{5.1}$$
where for $i=1,2$,
$$T_n^{(i)}=\inf_{m\in\mathcal M^{(i)}}\Big\{\big(\sum_{\lambda\notin\Lambda_m}\beta_\lambda^2\big)^2+\tfrac{D_m}{n^2}+\big(\operatorname{pen}(m)-\tfrac{D_m}{n}\big)^2\Big\}.$$

<a id="pdf-5ada2eaf45a8-p031-b002"></a>
<!-- pdf-source: page=31; block=2; confidence=0.85 -->
(5.1) shows $\hat\theta$ performs as well as $\hat\theta^{(1)}$, so (3.12) follows from Theorem 2 and Comment (ii) after Theorem 2.

<a id="pdf-5ada2eaf45a8-p031-b003"></a>
<!-- pdf-source: page=31; block=3; confidence=0.60 -->
**Bounding $T_n^{(1)}$.** For $p<2$, $s=\beta$ lies in the $\ell_p$-body $\ell_{p,c}$, i.e. $\sum_{\lambda>D}\|\beta_\lambda\|^p\le c_D^p$. By subadditivity of $x\mapsto x^{p/2}$ ($p\le2$),
$$\sum_{\lambda>D}\beta_\lambda^2\le\Big(\sum_{\lambda>D}\|\beta_\lambda\|^p\Big)^{2/p}\le c_D^2.$$
Hence $T_n^{(1)}\le\inf_{D\in\mathbb N^*}\big\{c_D^4+\tfrac{D\log(D)}{n^2}\big\}.$

<a id="pdf-5ada2eaf45a8-p031-b004"></a>
<!-- pdf-source: page=31; block=4; confidence=0.90 -->
**Bounding $T_n^{(2)}$.** For $D\in\mathbb N^*$ set $\varepsilon_D=D^{-1/p}c_D$ and $G_D=\{\lambda\in\{1,\dots,N\}:|\beta_\lambda|\ge\varepsilon_D\}$. Then
$$\sum_{\lambda\notin G_D}\beta_\lambda^2=\!\!\sum_{\lambda\notin G_D,\lambda\le D}\!\!\beta_\lambda^2+\!\!\sum_{\lambda\notin G_D,D<\lambda\le N}\!\!\beta_\lambda^2+\sum_{\lambda>N}\beta_\lambda^2\le D\varepsilon_D^2+\varepsilon_D^{2-p}\!\sum_{\lambda>D}|\beta_\lambda|^p+c_N^2\le D\varepsilon_D^2+\varepsilon_D^{2-p}c_D^p+c_N^2\le 2D^{1-2/p}c_D^2+c_N^2,$$
by definition of $\varepsilon_D$. For the cardinality, $c_D^p\ge\sum_{\lambda\in G_D,\lambda>D}|\beta_\lambda|^p\ge\varepsilon_D^p\,|G_D\cap\{\lambda>D\}|$, so $|G_D\cap\{\lambda>D\}|\le c_D^p\varepsilon_D^{-p}=D$, giving $|G_D|\le 2D$. Hence
$$T_n^{(2)}\le C\inf_{N\in\mathbb N^*}\inf_{1\le D\le N}\Big\{\big(D^{1-2/p}c_D^2\big)^2+\Big(\tfrac{D(1+\log(N/D))}{n}\Big)^2+c_N^4\Big\}.$$
This concludes the proof of Theorem 3. $\square$

<a id="pdf-5ada2eaf45a8-p032-b001"></a>
<!-- pdf-source: page=32; block=1; confidence=0.90 -->
**5.4. Proof of Corollary 2.** By (3.12) $\hat\theta$ behaves as well as the estimator of Corollary 1, so (3.15) follows from (3.4). For (3.14), with $p\le2$, Theorem 3 gives
$$\sup_{s\in\mathcal{E}_{p,\alpha'}(R)}\mathbb{E}_s\Big[\big(\hat\theta-\theta-\tfrac{2L(s)}{\sqrt n}\big)^2\Big]\le C\inf\{v_1(n),v_2(n)\},$$
where $c_\lambda=R\lambda^{-\alpha'}$ and
$$v_1(n)=\inf_{N\in\mathbb N^*}\Big\{\inf_{D\in\mathbb N^*}\big[\big(D^{1-2/p}c_D^2\big)^2+\big(\tfrac{D(1+\log(N/D))}{n}\big)^2\big]+c_N^4\Big\},\qquad v_2(n)=\inf_{D\in\mathbb N^*}\Big\{c_D^4+\tfrac{D\log(D+1)}{n^2}\Big\}.$$

<a id="pdf-5ada2eaf45a8-p032-b002"></a>
<!-- pdf-source: page=32; block=2; confidence=0.65 -->
Set $D_1(n)=\big\lceil(\tfrac{nR^2}{\log(1+nR^2)})^{1/(1+2\alpha)}\big\rceil$ and $N(n)=\lceil(nR^2)^{\alpha/(\alpha'(1+2\alpha))}\rceil$; both $\ge1$. Since for $p\le2$, $\alpha>\alpha'$, $\log(N(n)/D_1(n))\le C(p,\alpha)\log(1+nR^2)$, whence
$$v_1(n)\le C(p,\alpha)\,R^{4/(1+2\alpha)}\Big(\tfrac{\log(1+nR^2)}{n}\Big)^{4\alpha/(1+2\alpha)}.$$

<a id="pdf-5ada2eaf45a8-p032-b003"></a>
<!-- pdf-source: page=32; block=3; confidence=0.65 -->
Set $D_2(n)=\big\lceil(\tfrac{n^2R^4}{\log(1+n^2R^4)})^{1/(1+4\alpha')}\big\rceil\ge1$. By computations as in Corollary 1,
$$v_2(n)\le C(p,\alpha)\,R^{4/(1+4\alpha')}\Big(\tfrac{\log(1+nR^2)}{n^2}\Big)^{4\alpha'/(1+4\alpha')}.$$
This concludes the proof of Corollary 2. $\square$

<a id="pdf-5ada2eaf45a8-p032-b004"></a>
<!-- pdf-source: page=32; block=4; confidence=0.70 -->
**Proof of (3.16).** With $c_\lambda=R(\log\lambda)^{-\alpha'}$, pick $N\in\mathbb N^*$ with $c\,n\,(n^{1/\alpha'})^{1/p-1/2}\le N\le C\,n\,(n^{1/\alpha'})^{1/p-1/2}$. Taking $D_1(n)=\lceil n^{(p/2-p/2\alpha')(1/p-1/2)}\rceil$ gives $v_1(n)\le C(R,p,\alpha)\,n^{(2-p)((1/\alpha')(1/p-1/2)-1)}\log^2(1+n)$. Taking $D_2(n)=\lceil n^2/(\log(1+n))^{1+4\alpha'}\rceil$ gives $v_2(n)\le C(R,\alpha)(\log(1+n))^{-4\alpha'}$.

<a id="pdf-5ada2eaf45a8-p033-b001"></a>
<!-- pdf-source: page=33; block=1; confidence=0.90 -->
**5.5. Proof of Theorem 4.** Set $\mathcal M^{(1)}=\mathbb N$ and, for $J\in\mathbb N$,
$$\mathcal M^{(2)}_J=\big\{m\subset\mathbb N^*:\ \forall j\ge0,\ |m\cap\Lambda(j)|=K_J(j)\big\},\qquad \mathcal M^{(2)}=\bigcup_{J\in\mathbb N}\mathcal M^{(2)}_J.$$
Let $\mathcal M=\mathcal M^{(1)}\times\{1\}\ \oplus\ \mathcal M^{(2)}\times\{2\}$, and let $m\in\mathcal M$.

<a id="pdf-5ada2eaf45a8-p033-b002"></a>
<!-- pdf-source: page=33; block=2; confidence=0.70 -->
(i) If $m=J\times\{1\}$, $J\in\mathbb N$: $\Lambda_m=\Lambda_J=\bigcup_{j=0}^{J}\Lambda^{(j)}$, $x_m=x_J=2\log(D_m)$, $\operatorname{pen}(m)=\operatorname{pen}(J)=w^{(1)}(J)$.

(ii) If $m=m_2\times\{2\}$ with $m_2\in\mathcal M^{(2)}_J$: $\Lambda_m=\Lambda_{m_2}=m_2$, $x_m=x_{m_2}=3D_m$, $\operatorname{pen}(m)=\operatorname{pen}(m_2)=w^{(2)}(J)$.

<a id="pdf-5ada2eaf45a8-p033-b003"></a>
<!-- pdf-source: page=33; block=3; confidence=0.60 -->
These penalties/weights satisfy, for all $m\in\mathcal M$,
$$n\,\operatorname{pen}(m)\ge D_m+1+2\sqrt{(D_m+1)x_m}+2x_m,$$
the penalty assumption of Theorem 1. By definition $\hat\theta^{(1)}=\sup_{m_1\in\mathcal M^{(1)}}\big(\sum_{\lambda\in m_1}Y_\lambda^2-\operatorname{pen}(m_1)\big)$. For fixed $J$, $\sum_{\lambda\in m_2}Y_\lambda^2$ over $m_2\in\mathcal M^{(2)}_J$ is maximized at $m_2=\bigcup_{j=0}^{\infty}\Lambda_J(j)$, so
$$\hat\theta^{(2)}=\sup_{J\ge0}\big(\sum_{\lambda\in m_2}Y_\lambda^2-w^{(2)}(J)\big)=\sup_{m_2\in\mathcal M^{(2)}}\big(\sum_{\lambda\in m_2}Y_\lambda^2-\operatorname{pen}(m_2)\big),$$
hence $\hat\theta=\sup_{m\in\mathcal M}\big(\sum_{\lambda\in m}Y_\lambda^2-\operatorname{pen}(m)\big).$

<a id="pdf-5ada2eaf45a8-p034-b001"></a>
<!-- pdf-source: page=34; block=1; confidence=0.90 -->
**Proof (continued).** Theorem 1 applies to $\hat\theta$ provided assumption (2.7) holds with $r=2$. To verify it, split the series $\Sigma_2 = S^{(1)} + S^{(2)}$, where by (5.2) $S^{(i)} = \sum_{m\in\mathcal{M}^{(i)}} D_m e^{-x_m}$, with $S^{(1)} = \sum_{J\ge0}(2^{J+1}-1)^{-1} \le 2$ and $S^{(2)} = \sum_{J\ge0} \Delta_J\,|\mathcal{M}^{(2)}_J|\,e^{-3\Delta_J}$, where $\Delta_J = \sum_{j=0}^{\infty} K_J(j)$.

<a id="pdf-5ada2eaf45a8-p034-b002"></a>
<!-- pdf-source: page=34; block=2; confidence=0.85 -->
**Proof (continued).** Here $|\mathcal{M}^{(2)}_J| = \prod_{j>J}\binom{2^j}{K_J(j)}$, a finite product since $\binom{2^j}{K_J(j)} = 1$ for $j$ large enough. Using $\log\binom{k}{[kx]} \le kx\,(1+\log(1/x))$, valid for $x\in(0,1]$ and $k\in\mathbb{N}^*$, one gets $\log|\mathcal{M}^{(2)}_J| \le \sum_{j>J} \tfrac{2^J}{(j-J)^3}\big(1+\log\tfrac{(j-J)^3}{2^{J-j}}\big) \le 2^J\big(\sum_{l\ge1}\tfrac1{l^3} + \log 2\sum_{l\ge1}\tfrac1{l^2} + 3\sum_{l\ge1}\tfrac{\log l}{l^3}\big) \le C_3\,2^J$, with $C_3 = \sum_{l\ge1}\tfrac1{l^3} + \log2\sum_{l\ge1}\tfrac1{l^2} + 3\sum_{l\ge1}\tfrac{\log l}{l^3} < 3$. Hence (5.3): $|\mathcal{M}^{(2)}_J| \le \exp(C_3 2^J)$.

<a id="pdf-5ada2eaf45a8-p034-b003"></a>
<!-- pdf-source: page=34; block=3; confidence=0.70 -->
**Proof (continued).** Since $\Theta_J \ge 2^J$ and $x\mapsto x e^{-3x}$ is decreasing on $[1,\infty)$, combining (5.2) and (5.3) gives $S^{(2)} \le \sum_{J\ge0} 2^J\exp(C_3 2^J)\exp(-3\cdot2^J) < \infty$. Thus the series $\Sigma_2$ converges, and Theorem 1 yields the risk bound $\mathbb{E}_s\big[\big(\hat\theta - \theta - \tfrac{2L(s)}{\sqrt n}\big)^2\big] \le C\big(T^{(1)}_n \wedge T^{(2)}_n + \tfrac{\Sigma_2}{n^2}\big).$

<a id="pdf-5ada2eaf45a8-p035-b001"></a>
<!-- pdf-source: page=35; block=1; confidence=0.90 -->
**Definitions.** $T^{(1)}_n = \inf_{J\ge0}\big[\big(\sum_{\lambda\notin\Lambda_J}\beta_\lambda^2\big)^2 + \big(w^{(1)}(J) - \tfrac{|\Lambda_J|}{n}\big)^2\big]$ and $T^{(2)}_n = \inf_{J\ge0}\inf_{m\in\mathcal{M}^{(2)}_J}\big[\big(\sum_{\lambda\notin m}\beta_\lambda^2\big)^2 + \big(w^{(2)}(J) - \tfrac{\Delta_J}{n}\big)^2\big]$.

<a id="pdf-5ada2eaf45a8-p035-b002"></a>
<!-- pdf-source: page=35; block=2; confidence=0.90 -->
**Proof (continued).** Let $\beta \in \mathcal{B}_{\alpha,p,\infty}(R)$. (1) If $p\ge2$, convexity of $x\mapsto x^{p/2}$ gives $\sum_{\lambda\in\Lambda(j)}\beta_\lambda^2 \le \big(|\Lambda(j)|^{p/2-1}\sum_{\lambda\in\Lambda(j)}|\beta_\lambda|^p\big)^{2/p} \le R^2 2^{-2j\alpha}$, so $\mathcal{B}_{\alpha,p,\infty}(R)\subseteq\mathcal{B}_{\alpha,2,\infty}(R)$. (2) If $p<2$, subadditivity of $x\mapsto x^{p/2}$ gives $\sum_{\lambda\in\Lambda(j)}\beta_\lambda^2 \le \big(\sum_{\lambda\in\Lambda(j)}|\beta_\lambda|^p\big)^{2/p} \le R^2 2^{-2j\alpha'}$, where $\alpha' = 1/2 + \alpha - 1/p$.

<a id="pdf-5ada2eaf45a8-p035-b003"></a>
<!-- pdf-source: page=35; block=3; confidence=0.66 -->
**Proof (continued).** For every $J\in\mathcal{M}^{(1)}=\mathbb{N}$ and any $p>0$, $\sum_{\lambda\notin\Lambda_J}\beta_\lambda^2 = \sum_{j>J}\sum_{\lambda\in\Lambda(j)}\beta_\lambda^2 \le C(\alpha')R^2 2^{-2J\alpha''}$, with $\alpha'' = \inf(\alpha,\alpha')$; and since $|\Lambda_J|\le 2^{J+1}$, $\big(w^{(1)}(J)-\tfrac{|\Lambda_J|}{n}\big)^2 \le C\,\tfrac{2^J(J+1)}{n^2}$. Hence $T^{(1)}_n \le C\inf_{J\ge0}\big[R^4 2^{-4J\alpha''} + \tfrac{2^J(J+1)}{n^2}\big]$. Choosing $J^{(1)}_n = \big[\tfrac{1}{1+4\alpha''}\log_2\tfrac{n^2R^4}{\log(1+n^2R^4)}\big]$ gives $T^{(1)}_n \le C(p,\alpha)\,R^{4/(1+4\alpha'')}\big(\tfrac{\log(1+nR^2)}{n^2}\big)^{4\alpha''/(1+4\alpha'')}$. The control of $T^{(2)}_n$ (for $p<2$) follows.

<a id="pdf-5ada2eaf45a8-p036-b001"></a>
<!-- pdf-source: page=36; block=1; confidence=0.70 -->
**Proof (continued).** By Birgé and Massart (2000a), for any $J\in\mathbb{N}$ there exists $m\in\mathcal{M}^{(2)}_J$ with $\sum_{\lambda\notin m}\beta_\lambda^2 \le C(p,\alpha)R^2 2^{-2J\alpha}$. Since $\Theta_J \le \kappa 2^J$ ($\kappa$ an absolute constant), $T^{(2)}_n \le C(p,\alpha)\inf_{J\ge0}\big[R^4 2^{-4J\alpha} + \tfrac{2^{2J}}{n^2}\big]$. Choosing $J^{(2)}_n = \big[\tfrac{1}{1+2\alpha}\log_2(nR^2)\big]$ gives $T^{(2)}_n \le C(p,\alpha)\,R^{4/(1+2\alpha)}\,n^{-4\alpha/(1+2\alpha)}$. This concludes the proof of Theorem 4. $\square$

<a id="pdf-5ada2eaf45a8-p036-b002"></a>
<!-- pdf-source: page=36; block=2; confidence=0.80 -->
**References.** Bibliography section (~20 entries), including Baraud (2000); Barron, Birgé & Massart (1999); Bickel & Ritov (1988); Birgé (1983); Birgé & Massart (1995, 1997, 1998, 2000a, 2000b); DeVore, Jawerth & Popov (1992); DeVore & Lorentz (1993); DeVore, Kyriazis, Leviatan & Tikhomirov (1993); Johnstone (1999); Donoho & Johnstone (1998); Donoho & Liu (1991); Donoho & Nussbaum (1990); Dudley (1973); Efroïmovich & Low (1996); Gayraud & Tribouley (1999).

<a id="pdf-5ada2eaf45a8-p037-b001"></a>
<!-- pdf-source: page=37; block=1; confidence=0.95 -->
Page 1338; article by B. Laurent and P. Massart (running head).

<a id="pdf-5ada2eaf45a8-p037-b002"></a>
<!-- pdf-source: page=37; block=2; confidence=0.95 -->
Bibliography entries: Laurent, B. (1996), "Efficient estimation of integral functionals of a density," *Ann. Statist.* 24, 659–681; Lepskii, O. V. (1990), "On a problem of adaptive estimation in Gaussian white noise," *Theory Probab. Appl.* 35, 454–466; Lepskii, O. V. (1992), "On problems of adaptive estimation in Gaussian white noise," *Adv. Soviet Math.* 12, 87–106.

<a id="pdf-5ada2eaf45a8-p037-b003"></a>
<!-- pdf-source: page=37; block=3; confidence=0.95 -->
Author affiliation and contact: Laboratoire de mathématiques, Bât. 425, Université Paris Sud, F-91405 Orsay Cédex, France; emails Beatrice.Laurent@math.u-psud.fr and Pascal.Massart@math.u-psud.fr.
