
/-! ### Every-input equations (scope request EF-H1, `ef-h1-arith`) -/

/-- The defining equation of `mulStr` on every word: `mulStr z = ⟦⟦a⟧ · ⟦b⟧⟧_{|a| + |b|}` for
`a = pairFstD z`, `b = pairSndD z`. -/
theorem mulStr_eq (z : List Bool) :
    mulStr z = natToList ((pairFstD z).length + (pairSndD z).length)
      (listToNat (pairFstD z) * listToNat (pairSndD z)) := rfl

/-- The defining equation of `addStr` on every word: `addStr z = ⟦⟦a⟧ + ⟦b⟧⟧_{|a| + |b|}`. -/
theorem addStr_eq (z : List Bool) :
    addStr z = natToList ((pairFstD z).length + (pairSndD z).length)
      (listToNat (pairFstD z) + listToNat (pairSndD z)) := rfl

/-- The defining equation of `subStr` on every word: `subStr z = ⟦⟦a⟧ ∸ ⟦b⟧⟧_{|a|}`. -/
theorem subStr_eq (z : List Bool) :
    subStr z = natToList (pairFstD z).length (listToNat (pairFstD z) - listToNat (pairSndD z)) :=
  rfl

/-- The defining equation of `divModStr` on every word:
`divModStr z = ⟨⟦⟦a⟧ / ⟦b⟧⟧_{|a|}, ⟦⟦a⟧ mod ⟦b⟧⟧_{|b|}⟩`. -/
theorem divModStr_eq (z : List Bool) :
    divModStr z = pairEncode
      (natToList (pairFstD z).length (listToNat (pairFstD z) / listToNat (pairSndD z)))
      (natToList (pairSndD z).length (listToNat (pairFstD z) % listToNat (pairSndD z))) := rfl

/-- The defining equation of `xgcdStr` on every word:
`xgcdStr z = ⟨⟦gcd(⟦a⟧, ⟦b⟧)⟧_{|b|}, ⟦(⟦a⟧ : Z_{⟦b⟧})⁻¹⟧_{|b|}⟩`. -/
theorem xgcdStr_eq (z : List Bool) :
    xgcdStr z = pairEncode
      (natToList (pairSndD z).length (Nat.gcd (listToNat (pairFstD z)) (listToNat (pairSndD z))))
      (natToList (pairSndD z).length
        ((listToNat (pairFstD z) : ZMod (listToNat (pairSndD z)))⁻¹).val) := rfl

/-- The defining equation of `modExpStr` on every word:
`modExpStr z = ⟦⟦a⟧^{⟦x⟧} mod ⟦N⟧⟧_{|N|}` for `z = ⟨a, ⟨x, N⟩⟩` read by the total projections. -/
theorem modExpStr_eq (z : List Bool) :
    modExpStr z = natToList (pairSndD (pairSndD z)).length
      (listToNat (pairFstD z) ^ listToNat (pairFstD (pairSndD z)) %
        listToNat (pairSndD (pairSndD z))) := rfl

/-- The defining equation of `leStr` on every word: `leStr z = [⟦a⟧ ≤ ⟦b⟧]`. -/
theorem leStr_eq (z : List Bool) :
    leStr z = [decide (listToNat (pairFstD z) ≤ listToNat (pairSndD z))] := rfl
