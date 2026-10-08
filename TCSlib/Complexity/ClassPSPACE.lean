/-
Copyright (c) 2026 Seyoon Ragavan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Seyoon Ragavan
-/
import TCSlib.Complexity.ClassPSPACE.TQBF
import TCSlib.Complexity.ClassPSPACE.Games

/-!
# `PSPACE`-completeness

[AB09, §4.2]: `PSPACE`-hardness and -completeness, the `TQBF` language and
the Stockmeyer-Meyer theorem, and the game-playing face of the class. The
headline statements (phase P4.3 of `AroraBarakChapters3-4Plan.md`) are
`Complexity.TQBF_PSPACEComplete` ([AB09, Theorem 4.13]) with its two halves,
the packaged adjacency-formula interface of Claim 4.4(2), and Zermelo
determinacy for finite perfect-information games ([AB09, Exercise 4.10]).

## Contents

- `ClassPSPACE.TQBF`: Definition 4.9, the collapse corollary, Claim 4.4(2)
  in packaged form, `TQBF`, and Theorem 4.13
- `ClassPSPACE.Games`: finite two-person perfect-information games and
  Zermelo determinacy

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009. (§4.2.)
-/
