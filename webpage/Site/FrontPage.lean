import VersoBlog

open Verso Genre
open Blog hiding lean
open Site

#doc (Page) "TCSlib" =>

::::::htmlDiv (class := "hero")

:::::htmlDiv (class := "hero-text")

TCSlib

A Lean 4 Formalization of

Theoretical Computer Science

TCSlib is an open-source library formalizing results in Boolean Function Analysis
and Error-Correcting Codes using [Lean 4](https://lean-lang.org) and
[Mathlib](https://leanprover-community.github.io/mathlib4_docs/).
Every theorem is machine-checked.

::::html a (class := "hero-btn primary") (href := "https://github.com/Shilun-Allan-Li/tcslib")
:::html img (src := "/tcslib/static/arrow.svg") (alt := "") (width := "20") (height := "20")
:::
View on GitHub
::::

::::html a (class := "hero-btn secondary") (href := "#get-started")
Get Started
::::

:::::

::::::

::::::html div (class := "pillars") (id := "boolean-analysis")

*Boolean Function Analysis*

::::htmlDiv (class := "pillar")

*Fourier Analysis on the Hypercube*

Foundations of Boolean function analysis over $`\{-1,1\}^n`,
including the Fourier expansion, Parseval's identity, and spectral norms.

::::

::::htmlDiv (class := "pillar")

*Arrow's Impossibility Theorem*

A formal proof of Arrow's Theorem via Boolean function analysis:
no ranked voting system satisfies independence of irrelevant alternatives,
unanimity, and non-dictatorship simultaneously.

::::

::::htmlDiv (class := "pillar")

*Hypercontractivity*

The Bonami Lemma and $(2,4)$-Hypercontractivity inequality,
with applications to the structure of Boolean functions with small Fourier support.

::::

::::::

::::::html div (class := "pillars") (id := "coding-theory")

*Error-Correcting Codes*

::::htmlDiv (class := "pillar")

*Classical Bounds*

The Singleton, Hamming, Gilbert–Varshamov, and Johnson bounds
on the parameters of error-correcting codes over arbitrary alphabets.

::::

::::htmlDiv (class := "pillar")

*Linear Codes*

Formal treatment of linear codes: generator and parity-check matrices,
dual codes, and the MacWilliams identity.

::::

::::htmlDiv (class := "pillar")

*Quantum Codes*

Quantum Singleton and Quantum Hamming bounds,
formalizing the fundamental limits of quantum error correction.

::::

::::::

::::::html div (id := "get-started") (class := "get-started")

*Get Started*

TCSlib uses Lean 4 and Mathlib. Install Lean via
[lean-lang.org/install](https://lean-lang.org/install/), then:

:::::htmlDiv (class := "cta-buttons")

::::html a (class := "cta-btn primary") (href := "https://github.com/Shilun-Allan-Li/tcslib")
:::html img (src := "/tcslib/static/arrow.svg") (alt := "") (width := "20") (height := "20")
:::
Clone on GitHub
::::

::::html a (class := "cta-btn secondary") (href := "https://lean-lang.org/install/")
Install Lean
::::

:::::

::::::
