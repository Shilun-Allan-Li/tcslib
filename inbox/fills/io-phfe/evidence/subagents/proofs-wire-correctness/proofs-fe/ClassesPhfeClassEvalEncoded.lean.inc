/-- Canonical encoded inputs realize the intended typed PHFE evaluation whenever
every residue fits in the public word width. [GJLS21, §9, pp.57–58].

**Proof sketch.** Read phfeClass_eval, apply the tensor encoding round trip and
the two total vector-decoding round trips, then identify the typed evaluation.
The width assumption is needed for representation completeness, not for totality. -/
theorem phfeClass_eval_encoded (l n w : PolyExpr) (d kappa : ℕ) (p : ℕ+)
    (hwidth : (p : ℕ) ≤ 2 ^ w.eval kappa)
    (C : PolyTensor p (l.eval kappa) (n.eval kappa * n.eval kappa) d)
    (x : Fin (l.eval kappa) → ZMod (p : ℕ))
    (y : Fin (n.eval kappa) → ZMod (p : ℕ))
    (xword : Fin (l.eval kappa * w.eval kappa) → Bool)
    (yword : Fin (n.eval kappa * w.eval kappa) → Bool)
    (hx : List.ofFn xword = Encoding.Modular.encodeVector (w.eval kappa) x)
    (hy : List.ofFn yword = Encoding.Modular.encodeVector (w.eval kappa) y) :
    (phfeClass l n w d).eval kappa p (encodeTensorBits (w.eval kappa) C) xword yword =
      phfeEval C x y := by
  rw [phfeClass_eval, decodeTensor_encodeTensorBits (w.eval kappa) hwidth C,
    decodeResidues_encodeVector p (l.eval kappa) (w.eval kappa) hwidth x xword hx,
    decodeResidues_encodeVector p (n.eval kappa) (w.eval kappa) hwidth y yword hy]
