## TCSlib/Complexity/TuringMachine/Finite.lean:236 exists_first_entry_of_fixed

```lean
theorem exists_first_entry_of_fixed {k : ℕ} {Symbol State : Type*}
    {input : List Symbol} (tm : MultiTapeTM k Symbol State)
    (stop : State → Prop) (c d : Cfg k Symbol State input) (T : ℕ)
    (hfix : ∀ z : Cfg k Symbol State input,
      (∃ q, z.state = some q ∧ stop q) → tm.step z = z)
    (hd : ∃ q, d.state = some q ∧ stop q) (hT : tm.runFrom c T = d) :
    ∃ t ≤ T, (∀ j < t, ¬∃ q, (tm.runFrom c j).state = some q ∧ stop q) ∧
      tm.runFrom c t = d := by
  classical
  have hh : ∃ t, ∃ q, (tm.runFrom c t).state = some q ∧ stop q :=
    ⟨T, by rw [hT]; exact hd⟩
  let t := Nat.find hh
  have ht : t ≤ T := Nat.find_min' hh (by rw [hT]; exact hd)
  have hs : ∃ q, (tm.runFrom c t).state = some q ∧ stop q := Nat.find_spec hh
  have hfixed : tm.step (tm.runFrom c t) = tm.runFrom c t := hfix _ hs
  have hconst (n : ℕ) : tm.runFrom (tm.runFrom c t) n = tm.runFrom c t := by
    induction n with
    | zero => exact runFrom_zero
    | succ n ih => rw [runFrom_succ_eq_step, hfixed]; exact ih
  refine ⟨t, ht, fun j hj => Nat.find_min hh hj, ?_⟩
  have he := tm.runFrom_add c t (T - t)
  rw [Nat.add_sub_of_le ht, hT, hconst] at he
  exact he.symm
```

## TCSlib/Complexity/TuringMachine/Build/Loop.lean:3496 emCall_first_entry

```lean
private lemma emCall_first_entry {k : ℕ} {S : Type} {w : List Bool}
    (tm : MultiTapeTM k Bool S) (stop : S → Prop) [DecidablePred stop]
    (c d : Cfg k Bool S w) (T : ℕ)
    (hfix : ∀ z : Cfg k Bool S w, (∃ q, z.state = some q ∧ stop q) → tm.step z = z)
    (hd : ∃ q, d.state = some q ∧ stop q) (hT : tm.runFrom c T = d) :
    ∃ t ≤ T, (∀ j < t, ¬∃ q, (tm.runFrom c j).state = some q ∧ stop q) ∧
      tm.runFrom c t = d := by
  classical
  have hh : ∃ t, ∃ q, (tm.runFrom c t).state = some q ∧ stop q := ⟨T, by rw [hT]; exact hd⟩
  let t := Nat.find hh
  have ht : t ≤ T := Nat.find_min' hh (by rw [hT]; exact hd)
  have hs : ∃ q, (tm.runFrom c t).state = some q ∧ stop q := Nat.find_spec hh
  refine ⟨t, ht, fun j hj => Nat.find_min hh hj, ?_⟩
  have hconst : tm.runFrom (tm.runFrom c t) (T - t) = tm.runFrom c t :=
    Function.iterate_fixed (hfix _ hs) _
  have he := tm.runFrom_add c t (T - t)
  rw [Nat.add_sub_of_le ht, hT, hconst] at he
  exact he.symm
```

## TCSlib/Complexity/TuringMachine/Build/Primitives.lean:5167 emitter_first_entry

```lean
private lemma emitter_first_entry {k : ℕ} {S : Type} {w : List Bool}
    (tm : MultiTapeTM k Bool S) (stop : S → Prop) [DecidablePred stop]
    (c d : Cfg k Bool S w) (T : ℕ)
    (hfix : ∀ z : Cfg k Bool S w, (∃ q, z.state = some q ∧ stop q) → tm.step z = z)
    (hd : ∃ q, d.state = some q ∧ stop q) (hT : tm.runFrom c T = d) :
    ∃ t ≤ T, (∀ j < t, ¬∃ q, (tm.runFrom c j).state = some q ∧ stop q) ∧
      tm.runFrom c t = d := by
  classical
  have hh : ∃ t, ∃ q, (tm.runFrom c t).state = some q ∧ stop q := ⟨T, by rw [hT]; exact hd⟩
  let t := Nat.find hh
  have ht : t ≤ T := Nat.find_min' hh (by rw [hT]; exact hd)
  have hs : ∃ q, (tm.runFrom c t).state = some q ∧ stop q := Nat.find_spec hh
  refine ⟨t, ht, fun j hj => Nat.find_min hh hj, ?_⟩
  have hconst : tm.runFrom (tm.runFrom c t) (T - t) = tm.runFrom c t :=
    Function.iterate_fixed (hfix _ hs) _
  have he := tm.runFrom_add c t (T - t)
  rw [Nat.add_sub_of_le ht, hT, hconst] at he
  exact he.symm
```

## TCSlib/Complexity/TuringMachine/Build/Primitives.lean:3752 catalogFirstEntry

```lean
private lemma catalogFirstEntry {k : ℕ} {S : Type} {w : List Bool}
    (tm : MultiTapeTM k Bool S) (q : S) (c d : Cfg k Bool S w) (T : ℕ)
    (hfix : ∀ z : Cfg k Bool S w, z.state = some q → tm.step z = z)
    (hd : d.state = some q) (hT : tm.runFrom c T = d) :
    ∃ t ≤ T, (∀ j < t, (tm.runFrom c j).state ≠ some q) ∧ tm.runFrom c t = d := by
  classical
  have hh : ∃ t, (tm.runFrom c t).state = some q := ⟨T, by rw [hT, hd]⟩
  let t := Nat.find hh
  have ht : t ≤ T := Nat.find_min' hh (by rw [hT, hd])
  have hs : (tm.runFrom c t).state = some q := Nat.find_spec hh
  refine ⟨t, ht, fun j hj => Nat.find_min hh hj, ?_⟩
  have hconst : tm.runFrom (tm.runFrom c t) (T - t) = tm.runFrom c t :=
    Function.iterate_fixed (hfix _ hs) _
  have he := tm.runFrom_add c t (T - t)
  rw [Nat.add_sub_of_le ht, hT, hconst] at he
  exact he.symm
```

## TCSlib/Complexity/TuringMachine/Build/Primitives.lean:3959 splitEmbed_cut

```lean
private lemma splitEmbed_cut {k : ℕ} {S H : Type} {w : List Bool}
    (tm : MultiTapeTM k Bool S) (host : MultiTapeTM k Bool H)
    (emb : S → H) (anchor : H) (stop : S → Prop) [DecidablePred stop]
    (haway : ∀ q, emb q ≠ anchor)
    (hfix : ∀ c : Cfg k Bool S w, (∃ q, c.state = some q ∧ stop q) → tm.step c = c)
    (hagree : ∀ q, ¬stop q → ∀ inp work,
      host.tr (emb q) inp work = (tm.tr q inp work).mapState emb)
    (c d : Cfg k Bool S w) (T : ℕ)
    (hd : ∃ q, d.state = some q ∧ stop q) (hT : tm.runFrom c T = d) :
    ∃ t ≤ T, host.runFrom (c.mapState emb) t = d.mapState emb ∧
      splitSafe host anchor (c.mapState emb) t := by
  classical
  have hex : ∃ t, ∃ q, (tm.runFrom c t).state = some q ∧ stop q :=
    ⟨T, by rw [hT]; exact hd⟩
  let t := Nat.find hex
  have ht : t ≤ T := Nat.find_min' hex (by rw [hT]; exact hd)
  have he : tm.runFrom c t = d := by
    have hh := tm.runFrom_add c t (T - t)
    have hconst : tm.runFrom (tm.runFrom c t) (T - t) = tm.runFrom c t :=
      Function.iterate_fixed (hfix _ (Nat.find_spec hex)) _
    rw [Nat.add_sub_of_le ht, hT, hconst] at hh
    exact hh.symm
  have hp : ∀ j ≤ t, host.runFrom (c.mapState emb) j = (tm.runFrom c j).mapState emb := by
    intro j
    induction j with
    | zero => intro hj; rfl
    | succ j ih =>
      intro hj
      rw [MultiTapeTM.runFrom_succ_eq_step', ih (by omega),
        MultiTapeTM.runFrom_succ_eq_step']
      let z := tm.runFrom c j
      change host.step (z.mapState emb) = (tm.step z).mapState emb
      cases hz : z.state with
      | none => simp [MultiTapeTM.step, Cfg.mapState, hz]
      | some q =>
        have hn : ¬stop q := fun hq => Nat.find_min hex (by omega) ⟨q, hz, hq⟩
        simp only [MultiTapeTM.step, Cfg.mapState, hz, Option.map_some]
        rw [hagree q hn]
        rfl
  refine ⟨t, ht, by rw [hp t (le_refl _), he], ?_⟩
  intro j hj
  rw [hp j hj]
  cases hs : (tm.runFrom c j).state with
  | none => simp [Cfg.mapState, hs]
  | some q => simpa [Cfg.mapState, hs] using haway q
```

## TCSlib/Complexity/TuringMachine/Build/Catalog.lean:9334 f2_catalogFirstEntry

```lean
private lemma f2_catalogFirstEntry {k : ℕ} {S : Type} {w : List Bool}
    (tm : MultiTapeTM k Bool S) (q : S) (c d : Cfg k Bool S w) (T : ℕ)
    (hfix : ∀ z : Cfg k Bool S w, z.state = some q → tm.step z = z)
    (hd : d.state = some q) (hT : tm.runFrom c T = d) :
    ∃ t ≤ T, (∀ j < t, (tm.runFrom c j).state ≠ some q) ∧ tm.runFrom c t = d := by
  classical
  have hh : ∃ t, (tm.runFrom c t).state = some q := ⟨T, by rw [hT, hd]⟩
  let t := Nat.find hh
  have ht : t ≤ T := Nat.find_min' hh (by rw [hT, hd])
  have hs : (tm.runFrom c t).state = some q := Nat.find_spec hh
  refine ⟨t, ht, fun j hj => Nat.find_min hh hj, ?_⟩
  have hconst : tm.runFrom (tm.runFrom c t) (T - t) = tm.runFrom c t :=
    Function.iterate_fixed (hfix _ hs) _
  have he := tm.runFrom_add c t (T - t)
  rw [Nat.add_sub_of_le ht, hT, hconst] at he
  exact he.symm
```

## TCSlib/Complexity/TuringMachine/Build/Catalog.lean:9583 f2_splitEmbed_cut

```lean
private lemma f2_splitEmbed_cut {k : ℕ} {S H : Type} {w : List Bool}
    (tm : MultiTapeTM k Bool S) (host : MultiTapeTM k Bool H)
    (emb : S → H) (anchor : H) (stop : S → Prop) [DecidablePred stop]
    (haway : ∀ q, emb q ≠ anchor)
    (hfix : ∀ c : Cfg k Bool S w, (∃ q, c.state = some q ∧ stop q) → tm.step c = c)
    (hagree : ∀ q, ¬stop q → ∀ inp work,
      host.tr (emb q) inp work = (tm.tr q inp work).mapState emb)
    (c d : Cfg k Bool S w) (T : ℕ)
    (hd : ∃ q, d.state = some q ∧ stop q) (hT : tm.runFrom c T = d) :
    ∃ t ≤ T, host.runFrom (c.mapState emb) t = d.mapState emb ∧
      f2_splitSafe host anchor (c.mapState emb) t := by
  classical
  have hex : ∃ t, ∃ q, (tm.runFrom c t).state = some q ∧ stop q :=
    ⟨T, by rw [hT]; exact hd⟩
  let t := Nat.find hex
  have ht : t ≤ T := Nat.find_min' hex (by rw [hT]; exact hd)
  have he : tm.runFrom c t = d := by
    have hh := tm.runFrom_add c t (T - t)
    have hconst : tm.runFrom (tm.runFrom c t) (T - t) = tm.runFrom c t :=
      Function.iterate_fixed (hfix _ (Nat.find_spec hex)) _
    rw [Nat.add_sub_of_le ht, hT, hconst] at hh
    exact hh.symm
  have hp : ∀ j ≤ t, host.runFrom (c.mapState emb) j = (tm.runFrom c j).mapState emb := by
    intro j
    induction j with
    | zero => intro hj; rfl
    | succ j ih =>
      intro hj
      rw [MultiTapeTM.runFrom_succ_eq_step', ih (by omega),
        MultiTapeTM.runFrom_succ_eq_step']
      let z := tm.runFrom c j
      change host.step (z.mapState emb) = (tm.step z).mapState emb
      cases hz : z.state with
      | none => simp [MultiTapeTM.step, Cfg.mapState, hz]
      | some q =>
        have hn : ¬stop q := fun hq => Nat.find_min hex (by omega) ⟨q, hz, hq⟩
        simp only [MultiTapeTM.step, Cfg.mapState, hz, Option.map_some]
        rw [hagree q hn]
        rfl
  refine ⟨t, ht, by rw [hp t (le_refl _), he], ?_⟩
  intro j hj
  rw [hp j hj]
  cases hs : (tm.runFrom c j).state with
  | none => simp [Cfg.mapState, hs]
  | some q => simpa [Cfg.mapState, hs] using haway q
```

## TCSlib/Complexity/CookLevin/Hardness.lean:3311 clFirst

```lean
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

## TCSlib/Complexity/CookLevin/Hardness.lean:1274 clBank_first

```lean
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

## TCSlib/Complexity/CookLevin/Hardness.lean:1748 clCopy_first

```lean
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

## TCSlib/Complexity/CookLevin/Hardness.lean:2174 clRow_first

```lean
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

## TCSlib/Complexity/CookLevin/Hardness.lean:3020 clCmp_first

```lean
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

## TCSlib/Complexity/ClassNP/ExhaustiveReplay.lean:272 xr_firstArrival

```lean
private theorem xr_firstArrival {k : ℕ} {S : Type} {x : List Bool} (tm : MultiTapeTM k Bool S)
    (a : S) (hstat : ∀ d : Cfg k Bool S x, d.state = some a → tm.step d = d)
    {c c' : Cfg k Bool S x} {T : ℕ} (h : tm.runFrom c T = c') (hc' : c'.state = some a) :
    ∃ T' ≤ T, tm.runFrom c T' = c' ∧ ∀ u < T', (tm.runFrom c u).state ≠ some a := by
  classical
  have hT' : (tm.runFrom c T).state = some a := by rw [h]; exact hc'
  have hex : ∃ u, (tm.runFrom c u).state = some a := ⟨T, hT'⟩
  refine ⟨Nat.find hex, Nat.find_min' hex hT', ?_, fun u hu => Nat.find_min hex hu⟩
  have hsplit : tm.runFrom c T = tm.runFrom (tm.runFrom c (Nat.find hex)) (T - Nat.find hex) := by
    rw [← MultiTapeTM.runFrom_add, Nat.add_sub_cancel' (Nat.find_min' hex hT')]
  rw [xr_runFrom_fixed tm _ (hstat _ (Nat.find_spec hex))] at hsplit
  exact hsplit.symm.trans h
/-! #### The leaf rows

This file's own rows, on `Bool` tapes, each exiting at a stationary anchor `done b`: the
ruler-driven pass (the window clear's engine), the head rewind to a word's origin, the extension
of a word by one `false`, the capture test (which also clears the captured output), the input
rewind and the answer. Their run lemmas give exact times and exact configurations; the phase
host's guard comes from `xr_firstArrival`. -/
```

## TCSlib/Complexity/ClassNP/ExhaustiveReplay.lean:1590 xr_firstArrival'

```lean
private theorem xr_firstArrival' {k : ℕ} {S : Type} {x : List Bool} (tm : MultiTapeTM k Bool S)
    (A : S → Prop)
    (hstat : ∀ d : Cfg k Bool S x, ∀ a, d.state = some a → A a → tm.step d = d)
    {c c' : Cfg k Bool S x} {T : ℕ} (h : tm.runFrom c T = c') {a : S} (hc' : c'.state = some a)
    (ha : A a) :
    ∃ T' ≤ T, tm.runFrom c T' = c' ∧
      ∀ u < T', ∀ a', (tm.runFrom c u).state = some a' → ¬ A a' := by
  classical
  have hT' : ∃ a', (tm.runFrom c T).state = some a' ∧ A a' := ⟨a, by rw [h]; exact hc', ha⟩
  have hex : ∃ u, ∃ a', (tm.runFrom c u).state = some a' ∧ A a' := ⟨T, hT'⟩
  refine ⟨Nat.find hex, Nat.find_min' hex hT', ?_,
    fun u hu a' ha' hA => Nat.find_min hex hu ⟨a', ha', hA⟩⟩
  obtain ⟨a'', ha'', hA''⟩ := Nat.find_spec hex
  have hsplit : tm.runFrom c T = tm.runFrom (tm.runFrom c (Nat.find hex)) (T - Nat.find hex) := by
    rw [← MultiTapeTM.runFrom_add, Nat.add_sub_cancel' (Nat.find_min' hex hT')]
  rw [xr_runFrom_fixed tm _ (hstat _ a'' ha'' hA'')] at hsplit
  exact hsplit.symm.trans h
```
