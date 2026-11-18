# Exactly one next proof: Layered.forward_root

Candidate file: Layered.forward_root.proof.lean.inc. It preserves the exact current public
docstring/header from PartialGarbling/Layered.lean and replaces only its sorry body.
No live edit, Lean/lake/build/proof-check command, Git command or additional agent was used.
The body is a PURE TERM: zero tactic blocks, helpers, imports or new assumptions.

## Existing context

Namespace:
TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.PartialGarbling.Layered.
Variables: {p : ℕ+} {l n d : ℕ}; argument x : Fin l → ZMod (p : ℕ).

The proof first transports the root through published root_eq. It then reads forward_eq
at the explicit depth-zero node and applies the existing Fin.prod_univ_zero theorem.
No root/forward/xhat definition is unfolded. Core Sigma/Fin constructor projections and
empty-index elimination normalize definitionally; no Mathlib/TCSlib definition is passed
to simp/rw/unfold. The empty-product theorem is REUSED, not re-proved.

This proves the reconstruction vector's distinguished SOURCE coordinate equals1 for the
layered instance, matching the selected path-sum realization of AGW AppendixA Algorithm rec.
It does not claim to prove the full forward-action/reconstruction identity yet.
No mathematical obstruction: the statement holds for all positive moduli (including1),
all l,d, and in particular d=0 or l=0. It depends on no admitted algebra/garbling theorem.
Actual parent elaboration/Rule10/axiom checking remains pending; no Lean success is claimed.

## Reuse and search evidence

Read exact current declarations:
- Layered.lean:74 root, :77 root_eq; :229 forward, :233 forward_eq, :239 forward_root.
- Layered.lean:176 declares {p : ℕ+} {l n d : ℕ}; candidate uses the actual implicit d name.
- Mathlib/Algebra/BigOperators/Fin.lean:57 Fin.prod_univ_zero, signature
  `(f : Fin 0 → M) : (∏ i,f i)=1`, requiring only CommMonoid M.
- Existing import closure: Layered→Classes→Mathlib.Algebra.BigOperators.Fin, so no new
  Mathlib root/import is required.

Name and conclusion-shape rg across TCSlib, pinned BigOperators and core Init:
`forward_root|forward.*root.*=.*1|prod_univ_zero|prod_empty` found only the target wrapper;
nearest generic facts are Fin.prod_univ_zero and Fintype.prod_empty. The candidate directly
applies the former. It does not create an alternative finite-product lemma.

Pairing.Linear dlinMatrix_mulVec was also inspected as an alternative; it needs Fin2/Fin3
coordinate cases. The distinguished forward-coordinate identity is the simpler existing
admission, so EXACTLY this one was drafted.

Root-only exact?/apply? probe statement, if required by the overlap suite:

    {p : ℕ+} {l d : ℕ} (x : Fin l → ZMod (p : ℕ)) :
      forward x (root l d) = 1

No probe was run under this delegation. No new helper needs a frozen-header repair.
