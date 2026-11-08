# Current unchanged Hardness live-stop members

Source final79; all five full chunks are exact versus3023 BASE.

## clBank_first

```lean
/-- Cut the simultaneous bank at its observed first all-returned state.
This duration may be zero when no displacement needs a counter update;
the surrounding source-step/dispatch controller supplies positivity.
**Proof sketch.** Minimize the all-returned occurrence before the common
proved deadline. Absorption implies that its first occurrence already has
the exact endpoint and restored heads. -/
private lemma clBank_first {l : ℕ} (x : List Bool) (p : Fin (x.length + 2))
    (a : Fin l → Bool) (n : Fin l → ℕ) (W : ℕ)
    (hW : ∀ i, (n i).bits.length ≤ W) :
    ∃ t ≤ 2 * W + 2,
      (∀ j, j < t → ((clBankTM l).tm.runFrom
        (clBankCfg p (fun i => clCountCfg x (clBankStart (a i)) p 0 (n i).bits [])) j).state ≠
          some (fun _ => some (0 : Fin 4))) ∧
      (clBankTM l).tm.runFrom
        (clBankCfg p (fun i => clCountCfg x (clBankStart (a i)) p 0 (n i).bits [])) t =
        clBankCfg p (fun i => clCountCfg x 0 p 0 (n i + if a i then 1 else 0).bits []) := by
  let start := clBankCfg p (fun i => clCountCfg x (clBankStart (a i)) p 0 (n i).bits [])
  have finish := clBank_finish x p a n W hW
  have hex : ∃ t, t ≤ 2 * W + 2 ∧
      ((clBankTM l).tm.runFrom start t).state = some (fun _ => some (0 : Fin 4)) :=
    ⟨2 * W + 2, le_rfl, by rw [finish]; rfl⟩
  let t := Nat.find hex
  have ht := Nat.find_spec hex
  refine ⟨t, ht.1, ?_, ?_⟩
  · intro j hj hs
    have := Nat.find_min' hex (show j ≤ 2 * W + 2 ∧
      ((clBankTM l).tm.runFrom start j).state = some (fun _ => some (0 : Fin 4)) from
        ⟨by omega, hs⟩)
    omega
  · have hstay := Function.iterate_fixed (clBank_idle _ ht.2) (2 * W + 2 - t)
    change (clBankTM l).tm.runFrom ((clBankTM l).tm.runFrom start t)
      (2 * W + 2 - t) = (clBankTM l).tm.runFrom start t at hstay
    rw [← MultiTapeTM.runFrom_add, Nat.add_sub_of_le ht.1] at hstay
    exact hstay.symm.trans finish
```

## clCmp_first

```lean
/-- The native comparator returns at its first observed completion, within
its scan bound, with the correct arithmetic verdict and all four heads restored.
**Proof sketch.** Cut the exact completed run at its first completed-state
occurrence. Whole-configuration absorption preserves both the verdict and
all read-only words. The disjoint initial phase excludes zero duration. -/
private lemma clCmp_first (x : List Bool) (p : Fin (x.length + 2))
    (w : Fin 4 → List Bool) (W : ℕ) (hW : ∀ i, (w i).length ≤ W) :
    ∃ t ≤ 2 * W + 2, 0 < t ∧ ∃ b,
      (b = true ↔ clNum (w 0) + clNum (w 1) = clNum (w 2) + clNum (w 3)) ∧
      (∀ j, j < t → ∀ d, (clCmpTM.tm.runFrom
        (clCmpCfg x p (.inl (false, false, true)) w 0) j).state ≠ some (.inr (.inr d))) ∧
      clCmpTM.tm.runFrom (clCmpCfg x p (.inl (false, false, true)) w 0) t =
        clCmpCfg x p (.inr (.inr b)) w 0 := by
  let b := clCmpVerdict (clCmpOrbit w (clCmpSize w))
  have finish := clCmp_run x p w
  have hex : ∃ t, t ≤ 2 * clCmpSize w + 2 ∧
      (clCmpTM.tm.runFrom (clCmpCfg x p (.inl (false, false, true)) w 0) t).state =
        some (.inr (.inr b)) := ⟨2 * clCmpSize w + 2, le_rfl, by rw [finish]; rfl⟩
  let t := Nat.find hex
  have ht := Nat.find_spec hex
  have hw : clCmpSize w ≤ W := Finset.sup_le (fun i _ => hW i)
  have hp : 0 < t := by
    by_contra hn
    have hz : t = 0 := by omega
    have hh := ht.2
    change (clCmpTM.tm.runFrom (clCmpCfg x p (.inl (false, false, true)) w 0) t).state =
      some (.inr (.inr b)) at hh
    rw [hz, MultiTapeTM.runFrom_zero] at hh
    cases hh
  refine ⟨t, by omega, hp, b, clCmpVerdict_spec w, ?_, ?_⟩
  · intro j hj d hd
    have hstay := Function.iterate_fixed (clCmp_idle _ d hd) (2 * clCmpSize w + 2 - j)
    change clCmpTM.tm.runFrom
      (clCmpTM.tm.runFrom (clCmpCfg x p (.inl (false, false, true)) w 0) j)
      (2 * clCmpSize w + 2 - j) =
        clCmpTM.tm.runFrom (clCmpCfg x p (.inl (false, false, true)) w 0) j at hstay
    rw [← MultiTapeTM.runFrom_add, Nat.add_sub_of_le (by omega)] at hstay
    have hh := congrArg Cfg.state (finish.symm.trans hstay)
    rw [hd] at hh
    have hbd : b = d := Sum.inr.inj (Sum.inr.inj (Option.some.inj hh))
    have hs : (clCmpTM.tm.runFrom (clCmpCfg x p (.inl (false, false, true)) w 0) j).state =
        some (.inr (.inr b)) := by rw [hbd]; exact hd
    have := Nat.find_min' hex (show j ≤ 2 * clCmpSize w + 2 ∧
      (clCmpTM.tm.runFrom (clCmpCfg x p (.inl (false, false, true)) w 0) j).state =
        some (.inr (.inr b)) from ⟨by omega, hs⟩)
    omega
  · have hstay := Function.iterate_fixed (clCmp_idle _ b ht.2) (2 * clCmpSize w + 2 - t)
    change clCmpTM.tm.runFrom
      (clCmpTM.tm.runFrom (clCmpCfg x p (.inl (false, false, true)) w 0) t)
      (2 * clCmpSize w + 2 - t) =
        clCmpTM.tm.runFrom (clCmpCfg x p (.inl (false, false, true)) w 0) t at hstay
    rw [← MultiTapeTM.runFrom_add, Nat.add_sub_of_le ht.1] at hstay
    exact hstay.symm.trans finish
```

## clCopy_first

```lean
/-- The exact recorded field is available at the copier's observed first
positive return, with both the untouched source and the new record head
specified. This permits a host to dispatch without knowing field length.
**Proof sketch.** Choose the first completed-control occurrence below the exact copying bound. Since completion is absorbing on the whole configuration, its first occurrence already has the final record and restored source head. Initial and completed controls are distinct. -/
private lemma clCopy_first (x : List Bool) (p : Fin (x.length + 2))
    (w record : List Bool) :
    ∃ t ≤ 3 * w.length + 3, 0 < t ∧
      (∀ j, j < t → (clCopyTM.tm.runFrom (clCopyCfg x 0 p 0 w record) j).state ≠ some (4 : Fin 5)) ∧
      clCopyTM.tm.runFrom (clCopyCfg x 0 p 0 w record) t =
        clCopyCfg x 4 p 0 w (record ++ pairEncode w []) := by
  have finish := clCopy_run x p w record
  have hex : ∃ t, t ≤ 3 * w.length + 3 ∧
      (clCopyTM.tm.runFrom (clCopyCfg x 0 p 0 w record) t).state = some (4 : Fin 5) :=
    ⟨3 * w.length + 3, le_rfl, by rw [finish]; rfl⟩
  let t := Nat.find hex
  have ht := Nat.find_spec hex
  have hp : 0 < t := by
    by_contra h
    have hz : t = 0 := by omega
    have hs := ht.2
    change (clCopyTM.tm.runFrom (clCopyCfg x 0 p 0 w record) t).state = some (4 : Fin 5) at hs
    rw [hz, MultiTapeTM.runFrom_zero] at hs
    have hh := congrArg (fun z => z.map Fin.val) hs
    norm_num [clCopyCfg] at hh
  refine ⟨t, ht.1, hp, ?_, ?_⟩
  · intro j hj hs
    have := Nat.find_min' hex (show j ≤ 3 * w.length + 3 ∧
      (clCopyTM.tm.runFrom (clCopyCfg x 0 p 0 w record) j).state = some (4 : Fin 5) from ⟨by omega, hs⟩)
    omega
  · have hstay := Function.iterate_fixed (clCopy_idle _ ht.2) (3 * w.length + 3 - t)
    change clCopyTM.tm.runFrom (clCopyTM.tm.runFrom (clCopyCfg x 0 p 0 w record) t)
      (3 * w.length + 3 - t) = clCopyTM.tm.runFrom (clCopyCfg x 0 p 0 w record) t at hstay
    rw [← MultiTapeTM.runFrom_add, Nat.add_sub_of_le ht.1] at hstay
    exact hstay.symm.trans finish
```

## clFirst

```lean
/-- Cut a proved bounded run to its first visit to a fresh absorbing return.
**Proof sketch.** Minimize the return-control occurrence. Absorption makes
its whole configuration identical to the known endpoint, not just its state. -/
private lemma clFirst {k : ℕ} {S : Type} [DecidableEq S] {x : List Bool}
    (tm : MultiTapeTM k Bool S) (start finish : Cfg k Bool S x) (ret : S) (B : ℕ)
    (hrun : tm.runFrom start B = finish) (hret : finish.state = some ret)
    (hstart : start.state ≠ some ret)
    (hidle : ∀ c : Cfg k Bool S x, c.state = some ret → tm.step c = c) :
    ∃ t ≤ B, 0 < t ∧ (∀ j < t, (tm.runFrom start j).state ≠ some ret) ∧
      tm.runFrom start t = finish := by
  have hex : ∃ t, t ≤ B ∧ (tm.runFrom start t).state = some ret :=
    ⟨B, le_rfl, by rw [hrun]; exact hret⟩
  let t := Nat.find hex
  have ht := Nat.find_spec hex
  have hp : 0 < t := by
    by_contra hn
    have hz : t = 0 := by omega
    have hh := ht.2
    change (tm.runFrom start t).state = some ret at hh
    rw [hz, MultiTapeTM.runFrom_zero] at hh
    exact hstart hh
  refine ⟨t, ht.1, hp, ?_, ?_⟩
  · intro j hj hs
    have := Nat.find_min' hex (show j ≤ B ∧ (tm.runFrom start j).state = some ret
      from ⟨by omega, hs⟩)
    omega
  · have stay := Function.iterate_fixed (hidle _ ht.2) (B - t)
    change tm.runFrom (tm.runFrom start t) (B - t) = tm.runFrom start t at stay
    rw [← MultiTapeTM.runFrom_add, Nat.add_sub_of_le ht.1, hrun] at stay
    exact stay.symm
```

## clRow_first

```lean
/-- A row is completely stored at the actual first end-of-row return.
The fixed positive field count makes that return strictly positive.
**Proof sketch.** Minimize the completed-control occurrence below the
proved copying bound. The completed controller is absorbing, so its
first occurrence has the exact word and all the restored counter heads. -/
private lemma clRow_first {l : ℕ} (hl : 0 < l) (x : List Bool) (p : Fin (x.length + 2))
    (w : Fin l → List Bool) (record : List Bool) (W : ℕ)
    (hW : ∀ i, (w i).length ≤ W) :
    ∃ t ≤ l * (3 * W + 4), 0 < t ∧
      (∀ j, j < t → ((clRowTM l).tm.runFrom (clRowCfg x p 0 0 w record) j).state ≠
        some (Fin.last l, (0 : Fin 5))) ∧
      (clRowTM l).tm.runFrom (clRowCfg x p 0 0 w record) t =
        clRowCfg x p (Fin.last l) 0 w (record ++ clRowPrefix w l) := by
  obtain ⟨B, hB, he⟩ := clRow_stored x p w record W hW
  have hex : ∃ t, t ≤ B ∧ ((clRowTM l).tm.runFrom (clRowCfg x p 0 0 w record) t).state =
      some (Fin.last l, (0 : Fin 5)) := ⟨B, le_rfl, by rw [he]; rfl⟩
  let t := Nat.find hex
  have ht := Nat.find_spec hex
  have hp : 0 < t := by
    by_contra hn
    have hz : t = 0 := by omega
    have hs := ht.2
    change ((clRowTM l).tm.runFrom (clRowCfg x p 0 0 w record) t).state =
      some (Fin.last l, (0 : Fin 5)) at hs
    rw [hz, MultiTapeTM.runFrom_zero] at hs
    have hh := congrArg (fun z => z.map (fun q => q.1.val)) hs
    simp [clRowCfg] at hh
    omega
  refine ⟨t, ht.1.trans hB, hp, ?_, ?_⟩
  · intro j hj hs
    have := Nat.find_min' hex (show j ≤ B ∧
      ((clRowTM l).tm.runFrom (clRowCfg x p 0 0 w record) j).state =
        some (Fin.last l, (0 : Fin 5)) from ⟨by omega, hs⟩)
    omega
  · have hstay := Function.iterate_fixed (clRow_idle _ ht.2) (B - t)
    change (clRowTM l).tm.runFrom ((clRowTM l).tm.runFrom (clRowCfg x p 0 0 w record) t)
      (B - t) = (clRowTM l).tm.runFrom (clRowCfg x p 0 0 w record) t at hstay
    rw [← MultiTapeTM.runFrom_add, Nat.add_sub_of_le ht.1] at hstay
    exact hstay.symm.trans he
```
