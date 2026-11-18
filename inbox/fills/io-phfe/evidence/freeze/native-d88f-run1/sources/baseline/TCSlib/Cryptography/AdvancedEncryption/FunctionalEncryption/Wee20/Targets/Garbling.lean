/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.PartialGarbling.Layered

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Layered-garbling efficiency targets

The layered raw instance is total over every positive modulus. Its two deterministic
uniform-efficiency obligations are separated from raw reconstruction and exact privacy.

## Main definitions

* `PGTargets`: uniform matrix-generation and reconstruction targets.

## Main results

* `pgTargets_iff`: the conjunction reader.

## References

* [AGW20] M. Abdalla, J. Gong, H. Wee, *Functional Encryption for Attribute-Weighted
  Sums from k-Lin*, 2020, Lemma 2, p.12, Appendix A, pp.37-38, (28)-(32).
* [IW14] Y. Ishai, H. Wee, *Partial Garbling Schemes and Their Applications*, 2014,
  Definition 1, pp.6-7, and Section 4.2, pp.9-11.

-/

namespace TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.Wee20

open Complexity Turing TCSlib.Cryptography.Pairing

section

variable (ℓ n : PolyExpr) (d : ℕ)

local notation "PG" => layeredPG_raw ℓ n d

/-- Layered matrix generation and reconstruction satisfy the deterministic efficiency
clauses [AGW20, Lemma 2, p.12; IW14, Definition 1 continuation, p.7].
Phase B obligation; not proved in this development.

Each witness precedes κ and the arbitrary positive modulus, which is part of the input.
The definition imposes no sampling contract and no per-parameter modulus computation. -/
structure PGTargets : Prop where
  /-- One uniform map computes both matrices from the supplied modulus and tensor. -/
  lgen_eff : ∃ a : List Bool → List Bool, PolyTimeComputable a ∧
    ∀ κ (p : ℕ+) (f : PolyTensor p (ℓ.eval κ) (n.eval κ) d),
      a ((PG).lgenInput κ p f) = (PG).encLgen κ p f
  /-- One uniform map computes reconstruction from the supplied modulus and public input. -/
  rec_eff : ∃ a : List Bool → List Bool, PolyTimeComputable a ∧
    ∀ κ (p : ℕ+) (f : PolyTensor p (ℓ.eval κ) (n.eval κ) d)
      (x : Fin (ℓ.eval κ) → ZMod (p : ℕ)),
      a ((PG).recInput κ p f x) = (PG).encRec κ p f x

/-- The target is exactly the conjunction of its displayed algorithm obligations. -/
theorem pgTargets_iff :
    PGTargets ℓ n d ↔
      (∃ a : List Bool → List Bool, PolyTimeComputable a ∧
        ∀ κ (p : ℕ+) (f : PolyTensor p (ℓ.eval κ) (n.eval κ) d),
          a ((PG).lgenInput κ p f) = (PG).encLgen κ p f) ∧
      (∃ a : List Bool → List Bool, PolyTimeComputable a ∧
        ∀ κ (p : ℕ+) (f : PolyTensor p (ℓ.eval κ) (n.eval κ) d)
          (x : Fin (ℓ.eval κ) → ZMod (p : ℕ)),
          a ((PG).recInput κ p f x) = (PG).encRec κ p f x) :=
  ⟨fun h => ⟨h.lgen_eff, h.rec_eff⟩,
    fun h => ⟨h.1, h.2⟩⟩

end

end TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.Wee20
