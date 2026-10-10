/-
Copyright (c) 2026 The TCSlib Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TCSlib Contributors
-/
import TCSlib.Complexity.Expanders.Basic
import TCSlib.Complexity.Expanders.Mixing
import TCSlib.Complexity.Expanders.Walks
import TCSlib.Complexity.Expanders.Chernoff

/-!
# Expander Graphs

The spectral theory of expander graphs from Arora–Barak's appendices 7.A and
7.B, developed model-free over symmetric stochastic matrices (the normalized
adjacency matrices of regular multigraphs).

## Contents

- `Expanders.Basic`: symmetric stochastic matrices, the uniform distribution,
  and the parameter `λ(A)` ([AB09, Def 7.25]), with its basic bounds
  `0 ≤ λ ≤ 1` ([AB09, Rmk 7.26]).
- `Expanders.Mixing`: the Expander Mixing Lemma ([AB09, Lem 7.37]), in the
  normalized form `|⟨𝐬, A𝐭⟩ − |S||T|/n| ≤ λ√(|S||T|)`.
- `Expanders.Walks`: the operator-norm decomposition `A = (1−λ)J + λC`
  ([AB09, Lem 7.40]), the random-walk distribution `walkPMF`, and the
  expander-walk escape bound ([AB09, Thm 7.38]).
- `Expanders.Chernoff`: the Expander Chernoff Bound ([AB09, Thm 7.41], with
  the draft's sign erratum corrected).

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009.
-/
