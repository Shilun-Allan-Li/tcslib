# Reviewed candidate endpoints

## Catalog.lean::f2_catalogFirstEntry

Exact captured head lines 9334–9349:

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

## Finite.lean::exists_first_entry_of_fixed

Exact captured head lines 236–258:

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

## Loop.lean::emCall_first_entry

Exact captured head lines 3496–3513:

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

## Primitives.lean::catalogFirstEntry

Exact captured head lines 3752–3767:

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

## Primitives.lean::emitter_first_entry

Exact captured head lines 5167–5184:

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
