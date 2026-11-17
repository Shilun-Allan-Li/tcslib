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

TCSlib is an open-source library formalizing results across theoretical
computer science using [Lean 4](https://lean-lang.org) and
[Mathlib](https://leanprover-community.github.io/mathlib4_docs/).

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

::::::html div (class := "pillars") (id := "formalization-tools")

*Scripts and Tools for Lean Formalization*

::::htmlDiv (class := "pillar")

*Have-to-Lemma*

Extract local proof steps into reusable lemmas and clean up unnecessary
intermediate facts. The tool uses Lean’s elaborated proof information and
rechecks each rewrite before writing changes.

[Use the have-to-lemma tool](https://github.com/Shilun-Allan-Li/tcslib/blob/main/scripts/haves.py).

::::

::::htmlDiv (class := "pillar")

*Proofmatch*

Match reference statements and proofs from PDFs or validated Markdown to
Lean declarations. Proofmatch supports source extraction, search, and comparison
to help maintain auditable links between informal mathematics and formal proofs.

[Explore Proofmatch](https://github.com/Shilun-Allan-Li/tcslib/tree/main/proofmatch).

::::

::::htmlDiv (class := "pillar")

*Blueprints and Dependency Tools*

Scripts extract declaration dependencies, generate and validate blueprint
entries, and check style and attribution, keeping the informal exposition
connected to the evolving library.

[Browse the scripts](https://github.com/Shilun-Allan-Li/tcslib/tree/main/scripts).

::::

::::::

::::::html div (class := "pillars") (id := "autoformalization-dataset")

*Mathematics Dataset and Autoformalization Pipeline*

::::htmlDiv (class := "pillar")

*Paired Informal and Formal Mathematics*

Our dataset brings together TCSlib and attributed FABL material, pairing
informal statements and proof accounts with extracted Lean statements,
flattened proofs, dependency information, and source provenance.
It is designed to support training and evaluation for autoformalization.

::::

::::htmlDiv (class := "pillar")

*From Sources to Dataset*

An incremental pipeline ingests references, matches citations, maintains
blueprints, and generates statement prose and proof accounts where sources
are unmatched. Cached stages support resuming work as the library grows.

[Follow the pipeline guide](https://github.com/Shilun-Allan-Li/tcslib/blob/main/dataset/INSTRUCTIONS.md).

::::

::::htmlDiv (class := "pillar")

*Provenance and Validation*

Published gzip shards and a manifest make the dataset accessible with
checksums and project provenance. Structural checks and optional sampled
Lean checks track quality; the proof-completeness flag records the absence
of placeholders in extracted text and is separate from kernel validation.

[Explore the dataset and schema](https://github.com/Shilun-Allan-Li/tcslib/blob/main/dataset/README.md).

::::

::::::

::::::html div (class := "pillars") (id := "boolean-analysis")

*Boolean Function Analysis*

::::htmlDiv (class := "pillar")

*Fourier Analysis on the Hypercube*

Foundations of Boolean function analysis over $`\{-1,1\}^n`,
including the Fourier expansion, Parseval's identity, and spectral norms.

::::

::::htmlDiv (class := "pillar")

*Hypercontractivity Beyond the Cube*

General forward and reverse noise inequalities,
finite-product hypercontractivity, tensorization, and random-variable moment bounds.

::::

::::htmlDiv (class := "pillar")

*Structure and Applications*

Hypercontractive methods connect small-set expansion, low-degree concentration
and anticoncentration, influences, and KKL. The library also includes
Arrow’s impossibility theorem via Boolean function analysis.

[Explore the development](https://github.com/Shilun-Allan-Li/tcslib/tree/main/TCSlib/BooleanAnalysis/Hypercontractivity).

::::

::::::

::::::html div (class := "pillars") (id := "complexity-theory")

*Complexity Theory*

::::htmlDiv (class := "pillar")

*Models of Computation*

An ongoing formalization of Arora and Barak’s textbook, built on reusable
Turing-machine constructions, circuits, formulas, and simulations.

::::

::::htmlDiv (class := "pillar")

*Complexity Classes and Reductions*

Developments cover P, NP, PSPACE, NP-completeness and Cook–Levin,
as well as space complexity, diagonalization, and hierarchy theorems.

::::

::::htmlDiv (class := "pillar")

*An Active Formalization*

Work continues across oracle computation, randomized complexity, circuit
complexity, and expanders, with both completed proofs and open obligations.

[Read the progress notes](https://github.com/Shilun-Allan-Li/tcslib/blob/main/TCSlib/Complexity/README.md).

::::

::::::

::::::html div (class := "pillars") (id := "cryptography")

*Cryptography*

::::htmlDiv (class := "pillar")

*Secret Sharing*

Shamir’s threshold scheme, reconstruction, and perfect privacy,
with reusable foundations for access structures and shared secrets.

::::

::::htmlDiv (class := "pillar")

*Identification and Public-Key Cryptography*

Our cryptography work includes RSA and the Schnorr identification protocol,
with completeness, witness extraction, and honest-verifier zero-knowledge results.

::::

::::htmlDiv (class := "pillar")

*Secure Multiparty Computation*

Ongoing work on arithmetic circuits and the BGW protocol over Shamir sharings
connects secret sharing to secure distributed computation.

[Explore cryptography](https://github.com/Shilun-Allan-Li/tcslib/tree/main/TCSlib/Cryptography).

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
