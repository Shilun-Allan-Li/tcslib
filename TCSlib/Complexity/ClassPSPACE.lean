/-
Copyright (c) 2026 Seyoon Ragavan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Seyoon Ragavan
-/
import TCSlib.Complexity.ClassPSPACE.TQBF
import TCSlib.Complexity.ClassPSPACE.Games
import TCSlib.Complexity.ClassPSPACE.TQBFARM.Semantics
import TCSlib.Complexity.ClassPSPACE.TQBFARM.Machine
import TCSlib.Complexity.ClassPSPACE.TQBFARM.Leaf
import TCSlib.Complexity.ClassPSPACE.TQBFARM.Walk
import TCSlib.Complexity.ClassPSPACE.TQBFARM.Correct
import TCSlib.Complexity.ClassPSPACE.TQBFHardSemantics
import TCSlib.Complexity.ClassPSPACE.TQBFHardMachine
import TCSlib.Complexity.ClassPSPACE.TQBFHardTseitin
import TCSlib.Complexity.ClassPSPACE.TQBFHardVerifier
import TCSlib.Complexity.ClassPSPACE.TQBFHardBridge
import TCSlib.Complexity.ClassPSPACE.TQBFHardParams
import TCSlib.Complexity.ClassPSPACE.TQBFHard

/-!
# `PSPACE`-completeness

[AB09, §4.2]: `PSPACE`-hardness and -completeness, the `TQBF` language and
the Stockmeyer-Meyer theorem, and the game-playing face of the class. The
headline statements (phase P4.3 of `AroraBarakChapters3-4Plan.md`) are
`Complexity.TQBF_PSPACEComplete` ([AB09, Theorem 4.13]) with its two halves,
the closed-form configuration codec of Claim 4.4(2) (`Complexity.ConfigCodec`,
restated by RD-2), and Zermelo determinacy for finite perfect-information games
([AB09, Exercise 4.10]).

## Contents

- `ClassPSPACE.TQBF`: Definition 4.9, the collapse corollary, Claim 4.4(2)
  as the closed-form codec `Complexity.ConfigCodec` and its uniform emitters,
  `TQBF`, and Theorem 4.13
- `ClassPSPACE.Games`: finite two-person perfect-information games and
  Zermelo determinacy
- `ClassPSPACE.TQBFARM.Semantics`: the pure side of the polynomial-width register machine
  deciding `TQBF`: the syntax automaton of the encodings and the stack semantics `Val`
- `ClassPSPACE.TQBFARM.Machine`: the register machine itself, its register file and its
  loop sites
- `ClassPSPACE.TQBFARM.Leaf`: the machine's evaluation of the CNF matrix at a leaf
- `ClassPSPACE.TQBFARM.Walk`: the syntax check and the depth-first assignment walk; the walk
  is correct at a leaf
- `ClassPSPACE.TQBFARM.Correct`: the walk is correct at every depth; the true quantified
  formulas are in `PSPACE`, behind `Complexity.TQBF_mem_PSPACE`
- `ClassPSPACE.TQBFHardSemantics`: the `ψᵢ` prefix of the hardness reduction: blocks of
  quantifiers and the midpoint recursion `Mid`
- `ClassPSPACE.TQBFHardMachine`: acceptance as a path of blocks carrying code words
- `ClassPSPACE.TQBFHardTseitin`: Tseitin's transformation after the prefix, for circuits
- `ClassPSPACE.TQBFHardVerifier`: the polynomial-time verifier `predB` of the matrix
- `ClassPSPACE.TQBFHardBridge`: the verifier on an assignment is the flat matrix
- `ClassPSPACE.TQBFHardParams`: the block width and the bits of the quantifier prefix
- `ClassPSPACE.TQBFHard`: the reduction of every `PSPACE` language to the true quantified
  formulas, behind `Complexity.TQBF_PSPACEHard`

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009. (§4.2.)
-/
