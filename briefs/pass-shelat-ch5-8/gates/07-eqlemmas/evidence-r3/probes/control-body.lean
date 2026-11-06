
/-! ## Controls: the old reading (product domain and permutation read directly) -/

-- C1 (domain read as a product): the first component of an element of the padded domain.
example (z : (P.glPad m henc).D i) : P.D i := z.1

-- C2 (domain read as a product): an element of the padded domain built as a pair.
example (x : P.D i) (r : Fin (P.encD i default).length → Bool) : (P.glPad m henc).D i := (x, r)

-- C3 (permutation read directly): `perm'` is `perm_i × id` applied to the padded element
-- read as a pair, by unfolding.
example (z : (P.glPad m henc).D i) :
    (P.glPad m henc).perm i z = (P.perm i).prodCongr (Equiv.refl _) z :=
  rfl

-- C4 (permutation equation by unfolding): the conjugation equation of P3, proved by `rfl`.
example : (P.glPad m henc).perm i = ((P.glPad_domEquiv m henc i).trans
    ((P.perm i).prodCongr (Equiv.refl _))).trans (P.glPad_domEquiv m henc i).symm :=
  rfl

-- C5 (`glPad_domEquiv_apply`, the identity on the definition): `e z = z` is well typed only by
-- reading `(P.glPad m henc).D i` as the product.
example (z : (P.glPad m henc).D i) : P.glPad_domEquiv m henc i z = z :=
  P.glPad_domEquiv_apply m henc i z
