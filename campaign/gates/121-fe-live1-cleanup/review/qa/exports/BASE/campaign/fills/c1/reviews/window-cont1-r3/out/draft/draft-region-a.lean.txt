/-- The one-cell copy body returns to `false` after copying a symbol and escapes to `true`
at a blank. No catalog row provides this cyclic native-input copy with an end-marker escape. -/
private def iw_body : MultiTapeTM 1 Bool Bool where
  q₀ := false
  tr := fun q inp _ =>
    if q then FinTM.controlAction 0 (some true)
    else match inp with
      | none => FinTM.controlAction 0 (some true)
      | some b => ⟨1, fun _ => (some (some b), 1), none, some false⟩

/-- One live step of a leaf is its selected action, expressed through the model's equations. -/
private theorem iw_one {k : ℕ} {S : Type} {z : List Bool} (M : MultiTapeTM k Bool S)
    (c : Cfg k Bool S z) (q : S) (hc : c.state = some q) :
    M.runFrom c 1 = (M.tr q c.inputSymbol c.workTapeSymbols).apply c := by
  calc
    _ = M.step (M.runFrom c 0) := MultiTapeTM.runFrom_succ_eq_step'
    _ = _ := by rw [MultiTapeTM.runFrom_zero, MultiTapeTM.step_of_some hc]

/-- One successful copy step writes the scanned bit, advances both heads and emits nothing. -/
private theorem iw_body_copy {z : List Bool} (c : Cfg 1 Bool Bool z) (b : Bool)
    (hc : c.state = some false) (hb : c.inputSymbol = some b) :
    iw_body.runFrom c 1 =
      { c with state := some false, inputPos := moveInputPos c.inputPos 1,
        workTapes := fun i => Function.update (c.workTapes i) (c.workTapePos i) (some b),
        workTapePos := fun i => c.workTapePos i + 1 } := by
  rw [iw_one iw_body c false hc]
  simp only [iw_body, Bool.false_eq_true, if_false, hb]
  apply Cfg.ext
  · rw [Action.apply_state]
  · rw [Action.apply_inputPos]
  · funext i
    simp only [Action.apply_workTapes, Option.getD_some]
  · funext i
    simp only [Action.apply_workTapePos, SignType.coe_one]
  · rw [Action.apply_output]
    exact List.append_nil _

/-- On a blank input cell, the body escapes in one step without changing any data. -/
private theorem iw_body_blank {z : List Bool} (c : Cfg 1 Bool Bool z)
    (hc : c.state = some false) (hb : c.inputSymbol = none) :
    iw_body.runFrom c 1 = { c with state := some true } := by
  rw [iw_one iw_body c false hc]
  simp only [iw_body, Bool.false_eq_true, if_false, hb,
    FinTM.controlAction_apply, moveInputPos_zero]

/-- Overwrite a finite interval of a tape, leaving its exterior intact. -/
private def iw_patch (tape : ℤ → Option Bool) (head : ℤ) (v : List Bool) :
    ℤ → Option Bool := fun q =>
  if head ≤ q ∧ q < head + (v.length : ℤ)
    then FinTM.bufferTape v (q - head) else tape q

/-- Appending a bit to the copied interval changes exactly its next cell.

**Proof sketch.** At the next cell use the buffer's append equation. Inside the old interval
that equation preserves the old symbol; outside the enlarged interval both tapes are framed. -/
private theorem iw_patch_append (tape : ℤ → Option Bool) (head : ℤ)
    (v : List Bool) (b : Bool) :
    iw_patch tape head (v ++ [b]) =
      Function.update (iw_patch tape head v) (head + (v.length : ℤ)) (some b) := by
  funext q
  by_cases he : q = head + (v.length : ℤ)
  · subst q
    rw [Function.update_same]
    simp only [iw_patch, List.length_append, List.length_singleton, Nat.cast_add,
      Nat.cast_one]
    rw [if_pos (by omega), FinTM.bufferTape_append]
    simp
  · rw [Function.update_noteq he]
    by_cases hi : head ≤ q ∧ q < head + (v.length : ℤ)
    · simp only [iw_patch, List.length_append, List.length_singleton, Nat.cast_add,
        Nat.cast_one]
      rw [if_pos hi, if_pos (by omega), FinTM.bufferTape_append,
        Function.update_noteq (by omega)]
    · simp only [iw_patch, List.length_append, List.length_singleton, Nat.cast_add,
        Nat.cast_one]
      rw [if_neg hi, if_neg (by omega)]

/-- The body configuration after copying `r` input cells starting at input index `p`. -/
private def iw_prefix {z : List Bool} (c : Cfg 1 Bool Bool z) (p r : ℕ)
    (hr : p + r ≤ z.length) : Cfg 1 Bool Bool z where
  state := some false
  inputPos := ⟨p + 1 + r, by omega⟩
  workTapes := fun _ => iw_patch (c.workTapes 0) (c.workTapePos 0) ((z.drop p).take r)
  workTapePos := fun _ => c.workTapePos 0 + (r : ℤ)
  output := c.output

/-- The zero-length copied prefix is the initial configuration. -/
private theorem iw_prefix_zero {z : List Bool} (c : Cfg 1 Bool Bool z) (p : ℕ)
    (hp : p ≤ z.length) (hc : c.state = some false) (hi : c.inputPos.val = p + 1) :
    iw_prefix c p 0 (by omega) = c := by
  apply Cfg.ext hc.symm
  · apply Fin.ext
    simpa only [iw_prefix, Nat.add_zero] using hi.symm
  · funext i q
    have hz : i = 0 := Subsingleton.elim _ _
    subst i
    simp [iw_prefix, iw_patch]
  · funext i
    have hz : i = 0 := Subsingleton.elim _ _
    subst i
    simp only [iw_prefix, Nat.cast_zero, add_zero]
  · rfl

/-- A successful body round extends the copied input prefix by exactly one cell.

**Proof sketch.** The next input bit has index `p + r`. The one-step leaf writes it at the
next free destination cell, which is exactly the interval append equation. -/
private theorem iw_prefix_step {z : List Bool} (c : Cfg 1 Bool Bool z) (p r : ℕ)
    (hr : p + r < z.length) :
    iw_body.runFrom (iw_prefix c p r (by omega)) 1 =
      iw_prefix c p (r + 1) (by omega) := by
  have hdrop : r < (z.drop p).length := by rw [List.length_drop]; omega
  have hlen : ((z.drop p).take r).length = r := List.length_take_of_le hdrop.le
  have hbit : (iw_prefix c p r (by omega)).inputSymbol = some z[p + r] :=
    inputSymbolInner (p + r) (by simp only [iw_prefix]; omega) hr
  rw [iw_body_copy _ _ rfl hbit]
  apply Cfg.ext rfl
  · apply Fin.ext
    rw [moveInputPos_pos_of_ne_right _ (by simp only [iw_prefix]; omega)]
    simp only [iw_prefix]
    omega
  · funext i
    simp only [iw_prefix]
    rw [List.take_succ_eq_append_getElem hdrop, List.getElem_drop, iw_patch_append, hlen]
  · funext i
    simp only [iw_prefix, Nat.cast_add, Nat.cast_one]
    omega
  · rfl

/-- The one-step round orbit is the explicitly copied prefix while input cells remain.

**Proof sketch.** Induct on the number of rounds using the public round-orbit equations and
the one-cell extension lemma. -/
private theorem iw_orbit {z : List Bool} (c : Cfg 1 Bool Bool z) (p : ℕ)
    (hc : c.state = some false) (hi : c.inputPos.val = p + 1) (r : ℕ)
    (hr : p + r ≤ z.length) :
    counterLoopOrbit iw_body (fun _ => 1) c r = iw_prefix c p r hr := by
  induction r with
  | zero =>
    simpa only [roundOrbit_zero] using (iw_prefix_zero c p (by omega) hc hi).symm
  | succ r ih =>
    simp only [roundOrbit_succ]
    rw [ih (by omega)]
    exact iw_prefix_step c p r (by omega)

/-- The counter loop's escape anchor takes one silent stationary step to its done anchor.
Every other transition is delegated to the public counter loop. -/
private def iw_machine : MultiTapeTM 2 Bool (CounterLoopState Bool) where
  q₀ := .dec .run
  tr := fun q inp work => match q with
    | .escape => FinTM.controlAction 0 (some .done)
    | _ => (counterLoopTM iw_body false (some true)).tr q inp work

/-- Before the escape anchor is visited, adding the exit join does not change the run.

**Proof sketch.** The transition tables agree off the escape anchor. Apply the public
agreement transport on that set of states. -/
private theorem iw_join_prefix {z : List Bool} (c : Cfg 2 Bool (CounterLoopState Bool) z)
    (t : ℕ) (hcut : ∀ u < t,
      ((counterLoopTM iw_body false (some true)).runFrom c u).state ≠ some .escape) :
    iw_machine.runFrom c t = (counterLoopTM iw_body false (some true)).runFrom c t := by
  apply MultiTapeTM.runFrom_eq_of_agreeOn (Q := {q | q ≠ .escape})
  · apply (MultiTapeTM.agreeOn_iff _ _ _).mpr
    intro q hq inp work
    cases q with
    | escape => exact (hq rfl).elim
    | body _ => rfl
    | dec _ => rfl
    | done => rfl
  · intro u hu q hs he
    exact hcut u hu (hs.trans (congrArg some he))

/-- The join changes only the control state at the escape anchor. -/
private theorem iw_join_step {z : List Bool} (c : Cfg 2 Bool (CounterLoopState Bool) z)
    (hc : c.state = some .escape) :
    iw_machine.runFrom c 1 = { c with state := some .done } := by
  rw [iw_one iw_machine c .escape hc]
  simp only [iw_machine, FinTM.controlAction_apply, moveInputPos_zero]

/-- The all-true underflow word has exactly the counter loop's reported tape contents. -/
private theorem iw_patch_true (ct : ℤ → Option Bool) (cp : ℤ) (width : ℕ) :
    iw_patch ct cp (List.replicate width true) =
      fun q => if cp ≤ q ∧ q < cp + (width : ℤ) then some true else ct q := by
  funext q
  simp only [iw_patch, List.length_replicate]
  split_ifs with h
  · rw [FinTM.bufferTape_eq, if_pos (by omega), List.getElem?_replicate_of_lt (by omega)]
  · rfl

/-- The two-tape copier stops after the available window, with its counter width preserved.

**Proof sketch.** If the counter value fits in the remaining input, use the returning loop
contract and its whole-run underflow bound. Otherwise use the escape contract after one
additional blank-reading round, then the stationary exit join. Both contracts exclude an
earlier exit; their ledgers give the common coefficient six. -/
private theorem iw_local {z : List Bool} (c : Cfg 1 Bool Bool z) (p : ℕ)
    (hc : c.state = some false) (hi : c.inputPos.val = p + 1) (hp : p ≤ z.length)
    (w : List Bool) (ct : ℤ → Option Bool) (cp : ℤ)
    (hw : ∀ q : ℤ, -1 ≤ q → q ≤ (w.length : ℤ) → ct (cp + q) = FinTM.bufferTape w q)
    (n : ℕ) (hn : n = min (Nat.ofDigits 2 (w.map Bool.toNat)) (z.length - p)) :
    ∃ T ≤ 6 * (n + 1) + 2 * w.length, ∃ v : List Bool, v.length = w.length ∧
      iw_machine.runFrom (counterLoopCfg (some (.dec .run)) c ct cp) T =
        counterLoopCfg (some .done)
          (iw_prefix c p n (by have := Nat.min_le_right
            (Nat.ofDigits 2 (w.map Bool.toNat)) (z.length - p); omega)) (iw_patch ct cp v) cp ∧
      ∀ u < T,
        (iw_machine.runFrom (counterLoopCfg (some (.dec .run)) c ct cp) u).state ≠ some .done := by
  let d := Nat.ofDigits 2 (w.map Bool.toNat)
  let start := counterLoopCfg (some (.dec .run)) c ct cp
  have horbit (r : ℕ) (hr : p + r ≤ z.length) := iw_orbit c p hc hi r hr
  by_cases hd : d ≤ z.length - p
  · have hnd : n = d := hn.trans (Nat.min_eq_left hd)
    subst n
    let t := d + counterOverhead w (d + 1)
    obtain ⟨hend, hcut, _, _⟩ := counterLoopTM_run_done iw_body false (some true)
      (fun _ => 1) c w ct cp hw d rfl (fun r hr => by
        refine ⟨?_, by decide, (fun u hu hu' => by omega), ?_⟩
        · rw [horbit r (by omega)]; rfl
        · rw [horbit (r + 1) (by omega)]; rfl) t (by simp [t])
    have hsame : iw_machine.runFrom start t =
        (counterLoopTM iw_body false (some true)).runFrom start t :=
      iw_join_prefix start t (fun u hu => (hcut u hu).2)
    refine ⟨t, ?_, List.replicate w.length true, List.length_replicate, ?_, ?_⟩
    · have hover := counterOverhead_le w
      change counterOverhead w (d + 1) ≤ 4 * d + 2 * w.length + 2 at hover
      dsimp only [t]
      omega
    · rw [hsame, hend, horbit d (by omega), iw_patch_true]
    · intro u hu
      rw [iw_join_prefix start u (fun s hs => (hcut s (by omega)).2)]
      exact (hcut u hu).1
  · have hnd : n = z.length - p := hn.trans (Nat.min_eq_right (by omega))
    have hpn : p + n = z.length := by omega
    have hnd' : n < d := by omega
    let t := n + 1 + counterOverhead w (n + 1)
    have hfinal : counterLoopOrbit iw_body (fun _ => 1) c (n + 1) =
        { iw_prefix c p n (by omega) with state := some true } := by
      simp only [roundOrbit_succ]
      rw [horbit n (by omega)]
      exact iw_body_blank _ rfl (Cfg.inputSymbol_of_end (by simp only [iw_prefix]; omega))
    obtain ⟨hend, hcut, _, _⟩ := counterLoopTM_run_escape iw_body false true (by decide)
      (fun _ => 1) c w ct cp hw n hnd' (fun r hr => by
        refine ⟨?_, by decide, (fun u hu hu' => by omega)⟩
        rw [horbit r (by omega)]; rfl) (by rw [hfinal]) t (by simp [t])
    have hsame (u : ℕ) (hu : u ≤ t) : iw_machine.runFrom start u =
        (counterLoopTM iw_body false (some true)).runFrom start u :=
      iw_join_prefix start u (fun s hs => (hcut s (by omega)).2)
    have hex : (iw_machine.runFrom start t).state = some .escape := by
      rw [hsame t le_rfl, hend, counter_cfg_eq]
    refine ⟨t + 1, ?_, counterWord w (n + 1), counterWord_length _ _, ?_, ?_⟩
    · have hover := counterOverhead_le_of_le w (n + 1) hnd'
      dsimp only [t]
      omega
    · rw [MultiTapeTM.runFrom_add, iw_join_step _ hex, hsame t le_rfl, hend, hfinal]
      simp only [counter_cfg_eq, iw_patch]
    · intro u hu
      by_cases hut : u < t
      · rw [hsame u (by omega)]
        exact (hcut u hut).1
      · have hut' : u = t := by omega
        subst u
        rw [hex]
        decide

/-- Select the destination as tape zero and the distinct counter as tape one. -/
private def iw_select {k : ℕ} (j dst : Fin k) (hjd : j ≠ dst) : Fin 2 ↪ Fin k :=
  ⟨fun i => if i = 0 then dst else j, by
    intro a b h
    fin_cases a <;> fin_cases b <;> simp_all⟩

