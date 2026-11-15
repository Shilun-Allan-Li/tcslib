import TCSlib.Cryptography.SecureComputation.ObliviousTransfer

/-! Negative control: exactly one unfolding of a helper `def` of this fill (`OT.mask`, of
`ObliviousTransfer/Shape.lean`, read by the owned file only through `OT.mask_eq`) by `rfl`. The
helpers are foreign to every other module: passes unsealed; must fail exactly once under every
seal. -/

open TCSlib.Cryptography.SecureComputation in
theorem ctl_unfold_mask (T : TCSlib.Cryptography.TrapdoorCollection) (H : List Bool → List Bool)
    (n : ℕ) (i t yj : List Bool) (a : Bool) :
    OT.mask T H n i t yj a =
      List.zipWith xor (H (Turing.pairEncode i (T.inv.runAtL n (Turing.pairEncode t yj)
        (List.replicate (T.inv.coins.eval n) true)))) [a] :=
  rfl
