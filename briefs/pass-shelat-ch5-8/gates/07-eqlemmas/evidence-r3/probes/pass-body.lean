
/-! ## Pass: a consumer of the padded permutation collection's domain/permutation interface -/

-- P1 (domain): the published domain of `(P.glPad m henc).D i` is `D_i × {0,1}^L`.
example : (P.glPad m henc).D i ≃ P.D i × (Fin (P.encD i default).length → Bool) :=
  P.glPad_domEquiv m henc i

-- P2 (domain, round trip): elements of the padded domain are read and rebuilt through `e`.
example (z : (P.glPad m henc).D i) :
    (P.glPad_domEquiv m henc i).symm (P.glPad_domEquiv m henc i z) = z :=
  (P.glPad_domEquiv m henc i).symm_apply_apply z

-- P3 (permutation): the conjugated permutation equation `perm' = e⁻¹ ∘ (perm_i × id) ∘ e`.
example : (P.glPad m henc).perm i = ((P.glPad_domEquiv m henc i).trans
    ((P.perm i).prodCongr (Equiv.refl _))).trans (P.glPad_domEquiv m henc i).symm :=
  P.glPad_perm m henc i

-- P4 (application, forward): read through `e`, `perm'` is `perm_i` on the first component and
-- the identity on the padding.
example (z : (P.glPad m henc).D i) :
    P.glPad_domEquiv m henc i ((P.glPad m henc).perm i z) =
      (P.perm i (P.glPad_domEquiv m henc i z).1, (P.glPad_domEquiv m henc i z).2) := by
  rw [P.glPad_perm m henc i, Equiv.trans_apply, Equiv.apply_symm_apply, Equiv.trans_apply,
    Equiv.prodCongr_apply, Prod.map_apply, Equiv.refl_apply]

-- P5 (application, backward): on an element built from `(x, r)` through `e⁻¹`.
example (x : P.D i) (r : Fin (P.encD i default).length → Bool) :
    (P.glPad m henc).perm i ((P.glPad_domEquiv m henc i).symm (x, r)) =
      (P.glPad_domEquiv m henc i).symm (P.perm i x, r) := by
  rw [P.glPad_perm m henc i, Equiv.trans_apply, Equiv.trans_apply, Equiv.apply_symm_apply,
    Equiv.prodCongr_apply, Prod.map_apply, Equiv.refl_apply]

-- P6 (application, inverse permutation): `perm'⁻¹ = e⁻¹ ∘ (perm_i⁻¹ × id) ∘ e`.
example (x : P.D i) (r : Fin (P.encD i default).length → Bool) :
    ((P.glPad m henc).perm i).symm ((P.glPad_domEquiv m henc i).symm (x, r)) =
      (P.glPad_domEquiv m henc i).symm ((P.perm i).symm x, r) := by
  rw [P.glPad_perm m henc i, Equiv.symm_trans_apply, Equiv.symm_symm, Equiv.apply_symm_apply,
    Equiv.symm_trans_apply, Equiv.prodCongr_symm, Equiv.prodCongr_apply, Prod.map_apply,
    Equiv.refl_symm, Equiv.refl_apply]

-- P7 (field): the padded collection's function is its encoding after its permutation
-- (`PermCollection.f_perm` of `P.glPad m henc`), with the permutation read as in P4.
example (z : (P.glPad m henc).D i) :
    (P.glPad m henc).f i z = (P.glPad m henc).encD i ((P.glPad m henc).perm i z) :=
  (P.glPad m henc).f_perm i z
