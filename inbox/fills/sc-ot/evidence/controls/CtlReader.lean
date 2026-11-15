import TCSlib.Cryptography.SecureComputation.ObliviousTransfer

/-! Positive control: the same facts through published readers (`NUPPT.layout_eq`, `OT.mask_eq`,
`PolyExpr.eval_const`). Passes unsealed and under every seal. -/

theorem ctl_reader_layout (u y α r : List Bool) :
    Complexity.NUPPT.layout u y α r = Turing.pairEncode (Turing.pairEncode (Turing.pairEncode u y) α) r :=
  Complexity.NUPPT.layout_eq u y α r

open TCSlib.Cryptography.SecureComputation in
theorem ctl_reader_mask (T : TCSlib.Cryptography.TrapdoorCollection) (H : List Bool → List Bool)
    (n : ℕ) (i t yj : List Bool) (a : Bool) :
    OT.mask T H n i t yj a =
      List.zipWith xor (H (Turing.pairEncode i (T.inv.runAtL n (Turing.pairEncode t yj)
        (List.replicate (T.inv.coins.eval n) true)))) [a] :=
  OT.mask_eq T H n i t yj a

theorem ctl_reader_eval : (Complexity.PolyExpr.const 5).eval 3 = 5 :=
  Complexity.PolyExpr.eval_const 5 3
