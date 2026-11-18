theorem decodeResidues_modulus (p q : ℕ+) (hpq : (p : ℕ) = (q : ℕ)) (count width : ℕ)
    (word : Fin (count * width) → Bool) :
    (fun i => ((decodeResidues p count width word i).val : ZMod (q : ℕ))) =
      decodeResidues q count width word := by
  cases PNat.coe_injective hpq
  exact funext fun i => ZMod.natCast_zmod_val (decodeResidues p count width word i)
