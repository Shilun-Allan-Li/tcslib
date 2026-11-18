theorem encodeTensorBits_injective {p : ℕ+} {l n d : ℕ} (width : ℕ)
    (hwidth : (p : ℕ) ≤ 2 ^ width) :
    Function.Injective (encodeTensorBits (p := p) (l := l) (n := n) (d := d) width) :=
  fun C D h => (decodeTensor_encodeTensorBits width hwidth C).symm.trans
    ((congrArg (decodeTensor p l n d width) h).trans
      (decodeTensor_encodeTensorBits width hwidth D))
