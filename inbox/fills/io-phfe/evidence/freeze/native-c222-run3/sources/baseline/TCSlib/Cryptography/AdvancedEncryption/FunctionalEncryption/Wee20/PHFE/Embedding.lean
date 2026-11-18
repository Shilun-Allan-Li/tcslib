/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.Wee20.PHFE.Data

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Faithfulness of the PHFE value embedding

## Main definitions

No algorithm or representation is introduced here.

## Main results

* `Wee20.PHFE.embedValue_injective`: distinct scalar class values have distinct target values.

The proof uses only injectivity from the existing prime-order exponent theorem. It chooses
no exponent, defines no map from group elements to scalars, and belongs to the proof layer.

## References

* [GJLS21] R. Gay, A. Jain, H. Lin, A. Sahai, *Indistinguishability Obfuscation from
  Simple-to-State Hard Problems: New Assumptions, New Techniques, and Simplification*,
  EUROCRYPT 2021; full version, Cryptology ePrint Archive, Report 2020/764,
  revision of 3 January 2025, Definition 4.2 and Section 9.
-/

namespace TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.Wee20.PHFE

open Complexity TCSlib.Cryptography.Pairing

/-- The target-group embedding preserves distinct class values at every public parameter.
This is the prime-order injectivity property, used only as a proof about supplied scalars. -/
theorem embedValue_injective (G : BilinearGen) (ℓ n : PolyExpr) (d κ : ℕ)
    (pp : PublicParams G κ) : Function.Injective (embedValue G ℓ n d κ pp) :=
  fun a b h => (valueEquiv G ℓ n d κ pp).injective
    ((pp.group.pow_val_bijective pp.generator_ne_one).injective
      ((embedValue_eq G ℓ n d κ pp a).symm.trans
        (h.trans (embedValue_eq G ℓ n d κ pp b))))

end TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.Wee20.PHFE
