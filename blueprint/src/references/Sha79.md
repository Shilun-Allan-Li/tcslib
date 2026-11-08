<!-- generated-by: proofmatch Claude repair -->
<!-- source-pdf-sha256: a76120fbec44ae3b8dd1fbc5ade85a0c032358f1c692c918d8fb5d586ed7f8b1 -->

<a id="pdf-a76120fbec44-p001-b001"></a>
<!-- pdf-source: page=1; block=1; confidence=1.00 -->
## How to Share a Secret — Adi Shamir

<a id="pdf-a76120fbec44-p001-b002"></a>
<!-- pdf-source: page=1; block=2; confidence=1.00 -->
The paper proposes splitting data into $n$ pieces so any $k$ recover the data, while any $k-1$ reveal no information; the method supports reliable key management.

<a id="pdf-a76120fbec44-p001-b003"></a>
<!-- pdf-source: page=1; block=3; confidence=1.00 -->
## 1. Introduction

<a id="pdf-a76120fbec44-p001-b004"></a>
<!-- pdf-source: page=1; block=4; confidence=0.94 -->
A lock-and-key solution to the eleven-scientist, six-person access problem requires 462 locks and 252 keys per scientist, and its resource demands grow exponentially with group size.

<a id="pdf-a76120fbec44-p001-b005"></a>
<!-- pdf-source: page=1; block=5; confidence=0.99 -->
**Definition.** A $(k,n)$ threshold scheme divides data $D$ into pieces $D_1,\ldots,D_n$ such that (1) any $k$ or more pieces determine $D$; and (2) any $k-1$ or fewer leave all possible values of $D$ equally likely.

<a id="pdf-a76120fbec44-p001-b006"></a>
<!-- pdf-source: page=1; block=6; confidence=0.99 -->
With $n=2k-1$, the scheme recovers the key when $\lfloor n/2\rfloor=k-1$ of the $n$ pieces are destroyed, while opponents cannot reconstruct it when a security breach exposes $\lfloor n/2\rfloor=k-1$ of the remaining $k$ pieces. A $(3,n)$ scheme also supports joint company signatures, and suitable $k,n$ can balance group authorization and veto power.

<a id="pdf-a76120fbec44-p002-b001"></a>
<!-- pdf-source: page=2; block=1; confidence=1.00 -->
## 2. A Simple $(k,n)$ Threshold Scheme

<a id="pdf-a76120fbec44-p002-b002"></a>
<!-- pdf-source: page=2; block=2; confidence=0.99 -->
Any $k$ plane points with distinct first coordinates determine a unique polynomial of degree at most $k-1$ interpolating their values.

<a id="pdf-a76120fbec44-p002-b003"></a>
<!-- pdf-source: page=2; block=3; confidence=0.99 -->
Represent $D$ as a number and choose a degree-$(k-1)$ polynomial $q(x)=a_0+a_1x+\cdots+a_{k-1}x^{k-1}$ with $a_0=D$ and the other coefficients random. Set $D_i=q(i)$ for $i=1,\ldots,n$. Any $k$ indexed shares interpolate $q$, and then $D=q(0)$.

<a id="pdf-a76120fbec44-p002-b004"></a>
<!-- pdf-source: page=2; block=4; confidence=0.95 -->
Choose a prime $p>\max(D,n)$ and sample $a_1,\ldots,a_{k-1}$ uniformly modulo $p$; compute shares modulo $p$. Given $k-1$ shares $D_i=q(i)$, for each candidate $D'\in[0,p)$ there is a unique polynomial $q'(x)$ of degree $k-1$ such that $q'(0)=D'$ and $q'(i)=D_i$ for the given indices. The text states that these $p$ candidate polynomials are equally likely, so the shares reveal no information about the real value of $D$.

<a id="pdf-a76120fbec44-p002-b005"></a>
<!-- pdf-source: page=2; block=5; confidence=0.91 -->
Polynomial evaluation and interpolation have cited $O(n\log^2 n)$ algorithms; quadratic methods are also considered practical. Long data may be split into blocks, but $p\ge n+1$ is needed for $n$ distinct evaluation arguments together with zero; a 16-bit modulus is said to support up to 64,000 shares.

<a id="pdf-a76120fbec44-p002-b006"></a>
<!-- pdf-source: page=2; block=6; confidence=0.96 -->
The listed properties are: (1) each share is no larger than the original data; (2) with $k$ fixed, shares can be added or removed independently; (3) resampling a polynomial with the same constant term refreshes shares without changing $D$, limiting accumulation across editions; and (4) tuples of polynomial values allow weighted access. For example, president/vice-president/executive share counts of three/two/one yield access by three executives, a vice-president and another executive, or the president alone.

<a id="pdf-a76120fbec44-p002-b007"></a>
<!-- pdf-source: page=2; block=7; confidence=0.99 -->
A different, somewhat less efficient threshold scheme is attributed to G. R. Blakley.
