# Relevant final-source quotations (data only)

## TCSlib/Complexity/TuringMachine/Build/Primitives.lean:1778 — Turing.FinTM.catalogRewind

```lean
private lemma catalogRewind {k : ℕ} {S : Type} {x : List Bool}
    (tm : MultiTapeTM k Bool S) (start scan : S) (dest : Option S)
    (hstart : ∀ inp work, tm.tr start inp work = controlAction .neg (some scan))
    (hscan : ∀ inp work, tm.tr scan inp work = match inp with
      | some _ => controlAction .neg (some scan)
      | none => controlAction .pos dest)
    (c : Cfg k Bool S x) (hs : c.state = some start) :
    ∃ r ≤ c.inputPos.val + 2,
      tm.runFrom c r = {c with state := dest, inputPos := 1} := by
  have hstep : tm.step c =
      {c with state := some scan, inputPos := moveInputPos c.inputPos .neg} := by
    unfold MultiTapeTM.step
    rw [hs]
    dsimp only
    rw [hstart, controlAction_apply]
  have hp : (moveInputPos c.inputPos .neg).val ≤ x.length := by
    rw [moveInputPos_neg_val]
    have := c.inputPos.isLt
    omega
  refine ⟨1 + ((moveInputPos c.inputPos .neg).val + 1), ?_, ?_⟩
  · rw [moveInputPos_neg_val]; omega
  · rw [MultiTapeTM.runFrom_add]
    change tm.runFrom (tm.step c) _ = _
    rw [hstep, rewind_scan tm scan dest hscan _ rfl hp]
```

## TCSlib/Complexity/TuringMachine/Build/Primitives.lean:705 — Turing.FinTM.extract_replay

```lean
private lemma extract_replay (first second : Bool) (x a : List Bool)
    (i : ℕ) (hi : i ≤ x.length) : ∀ j (_hj : j ≤ a.length),
    (pairExtractTM first second).tm.runFrom
      (extractCfg x (some (.inr 1)) i hi a 0 []) j =
      extractCfg x (some (.inr 1)) i hi a j (if first then a.take j else []) := by
  intro j
  induction j with
  | zero => intro hj; cases first <;> rfl
  | succ j ih =>
    intro hj
    rw [MultiTapeTM.runFrom_succ_eq_step', ih (by omega)]
    unfold MultiTapeTM.step
    simp only [pairExtractTM, extractCfg, Cfg.workTapeSymbols, bufferTape_nat,
      List.getElem?_eq_getElem (by omega : j < a.length)]
    refine Cfg.ext rfl (moveInputPos_zero _) rfl ?_ ?_
    · funext k; simp [Action.apply]
    · change (if first then a.take j else []) ++
        (if first then some (a[j]'(by omega)) else none).toList =
          (if first then a.take (j + 1) else [])
      have ht : a.take j ++ [a[j]'(by omega)] = a.take (j + 1) := by
        rw [List.take_succ, List.getElem?_eq_getElem (by omega)]
        rfl
      cases first with
      | false => rfl
      | true => exact ht
```

## TCSlib/Complexity/TuringMachine/Build/Primitives.lean:1980 — Turing.FinTM.rawStrip_replay

```lean
private lemma rawStrip_replay (x a : List Bool) (i : ℕ) (hi : i ≤ x.length) :
    ∀ j (_hj : j ≤ a.length),
    rawStripTM.tm.runFrom (stripCfg x (some 3) i hi a 0 []) j =
      stripCfg x (some 3) i hi a j (a.take j) := by
  intro j
  induction j with
  | zero => intro hj; rfl
  | succ j ih =>
    intro hj
    rw [MultiTapeTM.runFrom_succ_eq_step', ih (by omega)]
    unfold MultiTapeTM.step
    simp only [rawStripTM, stripCfg, Cfg.workTapeSymbols, bufferTape_nat,
      List.getElem?_eq_getElem (by omega : j < a.length)]
    refine Cfg.ext rfl (moveInputPos_zero _) rfl ?_ ?_
    · funext k; simp [Action.apply]
    · change a.take j ++ [a[j]'(by omega)] = a.take (j + 1)
      rw [List.take_succ, List.getElem?_eq_getElem (by omega)]
      rfl
```

## TCSlib/Complexity/TuringMachine/Build/Primitives.lean:5723 — Turing.FinTM.emitter_first_entry

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

## TCSlib/Complexity/TuringMachine/Build/Primitives.lean:6754 — Turing.FinTM.emitterP2_body_erase_left

```lean
private lemma emitterP2_body_erase_left (C D : FinTM Bool) (hk : 0 < C.k) (hl : 0 < D.k)
    (ce cx : C.State) (de dx : D.State) (w s u v : List Bool) (ok : Bool) :
    let B := emitterP2BodyTM C D hk hl ce cx de dx
    ∃ t ≤ 2 * (u.length + 1),
      B.tm.runFrom (Cfg.ofWords (input := w) (.eraseLeft ok 0)
        (emitterP2Words C.k D.k s u v)) t =
        Cfg.ofWords (.eraseLeft ok 2) (emitterP2Words C.k D.k s [] v) ∧
      splitSafe B.tm .anchor (Cfg.ofWords (input := w) (.eraseLeft ok 0)
        (emitterP2Words C.k D.k s u v)) t := by
  dsimp only
  let slot := emitterP2LeftIndex C.k D.k ⟨0, hk⟩
  let emb : Fin 3 ↪ EmitterP2State C.State D.State :=
    ⟨.eraseLeft ok, by intro a b h; exact (EmitterP2State.eraseLeft.inj h).2⟩
  let tapes := fun i => bufferTape (emitterP2Words C.k D.k s [] v i)
  have hframe (q : Fin 3) (a : List Bool) :
      (embedEmitCfg (emitterP2OneIndex slot) tapes (fun _ => 0) []
        (emitterP2EraseCfg w a q 0)).mapState emb =
          Cfg.ofWords (emb q) (emitterP2Words C.k D.k s a v) := by
    change (embedEmitCfg _ _ _ [] (Cfg.ofWords q (fun _ : Fin 1 => a))).mapState emb = _
    rw [emitterP2_one_frame, emitterP2_update_left]
  obtain ⟨t, _, ht, hf, hr⟩ := emitterP2_erase_first w u
  have h := emitterP2_phase emitterP2EraseTM.tm (emitterP2BodyTM C D hk hl ce cx de dx).tm
    (emitterP2OneIndex slot) emb .anchor
    (by intro q; simp [emb]) (fun q : Fin 3 => q ≠ 2)
    (by intro q hq inp work; simp [emb, slot, emitterP2BodyTM, hq])
    tapes (fun _ => 0) (emitterP2EraseCfg w u 0 0) (emitterP2EraseCfg w [] 2 0) t
    (by intro j hj q hq he; subst q; exact hf j hj hq) hr
  erw [hframe, hframe] at h
  exact ⟨t, ht, h⟩
```

## TCSlib/Complexity/TuringMachine/Build/Primitives.lean:6787 — Turing.FinTM.emitterP2_body_erase_right

```lean
private lemma emitterP2_body_erase_right (C D : FinTM Bool) (hk : 0 < C.k) (hl : 0 < D.k)
    (ce cx : C.State) (de dx : D.State) (w s u v : List Bool) (ok : Bool) :
    let B := emitterP2BodyTM C D hk hl ce cx de dx
    ∃ t ≤ 2 * (v.length + 1),
      B.tm.runFrom (Cfg.ofWords (input := w) (.eraseRight ok 0)
        (emitterP2Words C.k D.k s u v)) t =
        Cfg.ofWords (.eraseRight ok 2) (emitterP2Words C.k D.k s u []) ∧
      splitSafe B.tm .anchor (Cfg.ofWords (input := w) (.eraseRight ok 0)
        (emitterP2Words C.k D.k s u v)) t := by
  dsimp only
  let slot := emitterP2RightIndex C.k D.k ⟨0, hl⟩
  let emb : Fin 3 ↪ EmitterP2State C.State D.State :=
    ⟨.eraseRight ok, by intro a b h; exact (EmitterP2State.eraseRight.inj h).2⟩
  let tapes := fun i => bufferTape (emitterP2Words C.k D.k s u [] i)
  have hframe (q : Fin 3) (a : List Bool) :
      (embedEmitCfg (emitterP2OneIndex slot) tapes (fun _ => 0) []
        (emitterP2EraseCfg w a q 0)).mapState emb =
          Cfg.ofWords (emb q) (emitterP2Words C.k D.k s u a) := by
    change (embedEmitCfg _ _ _ [] (Cfg.ofWords q (fun _ : Fin 1 => a))).mapState emb = _
    rw [emitterP2_one_frame, emitterP2_update_right]
  obtain ⟨t, _, ht, hf, hr⟩ := emitterP2_erase_first w v
  have h := emitterP2_phase emitterP2EraseTM.tm (emitterP2BodyTM C D hk hl ce cx de dx).tm
    (emitterP2OneIndex slot) emb .anchor
    (by intro q; simp [emb]) (fun q : Fin 3 => q ≠ 2)
    (by intro q hq inp work; simp [emb, slot, emitterP2BodyTM, hq])
    tapes (fun _ => 0) (emitterP2EraseCfg w v 0 0) (emitterP2EraseCfg w [] 2 0) t
    (by intro j hj q hq he; subst q; exact hf j hj hq) hr
  erw [hframe, hframe] at h
  exact ⟨t, ht, h⟩
```

## TCSlib/Complexity/TuringMachine/Build/Primitives.lean:1667 — Turing.FinTM.lenParse_first

```lean
private lemma lenParse_first (M : FinTM Bool) {x : List Bool}
    (c : Cfg M.k Bool M.State x) (pre rest : List Bool) (b : Bool) (r : ℕ)
    (hx : x = pre ++ b :: rest) :
    (pairCountTM M).tm.step
      (lenCfg M c (some (.inr (.inr none))) pre.length (by simp [hx]) r) =
      lenCfg M c (some (.inr (.inr (some b)))) (pre.length + 1) (by simp [hx]) r := by
  unfold MultiTapeTM.step
  change ((pairCountTM M).tm.tr (.inr (.inr none)) _ _).apply _ = _
  rw [lenCfg_read]
  have hin : x[pre.length]? = some b := by simp [hx]
  simp only [pairCountTM, hin]
  exact lenAction_apply M c _ _ pre.length (pre.length + 1) r r
    (by simp [hx]) (by simp [hx]) .pos 0 none
    (moveInputPos_pos_of_ne_right _ (by simp [hx])) (by simp [SignType.cast])
```

## TCSlib/Complexity/TuringMachine/Build/Primitives.lean:1611 — Turing.FinTM.lenSuffix_run

```lean
private lemma lenSuffix_run (M : FinTM Bool) {x : List Bool}
    (c : Cfg M.k Bool M.State x) (rest : List Bool) :
    ∀ pre (hx : x = pre ++ rest) r, r ≤ c.output.length →
    ∃ t ≤ rest.length + 1,
      ((pairCountTM M).tm.runFrom
        (lenCfg M c (some (.inr (.inl 3))) pre.length (by simp [hx]) r) t).state = none ∧
      ((pairCountTM M).tm.runFrom
        (lenCfg M c (some (.inr (.inl 3))) pre.length (by simp [hx]) r) t).output =
          [decide (rest.length ≤ r)] := by
  induction rest with
  | nil =>
    intro pre hx r hr
    refine ⟨1, by simp, ?_⟩
    simp only [MultiTapeTM.runFrom_succ_eq_step, MultiTapeTM.runFrom_zero]
    unfold MultiTapeTM.step
    change (((pairCountTM M).tm.tr (.inr (.inl 3)) _ _).apply _).state = none ∧ _
    rw [lenCfg_read]
    simp [hx, pairCountTM, lenAction, lenCfg, captureCfg, Action.apply]
  | cons b rest ih =>
    intro pre hx r hr
    cases r with
    | zero =>
      refine ⟨1, by simp, ?_⟩
      simp only [MultiTapeTM.runFrom_succ_eq_step, MultiTapeTM.runFrom_zero]
      unfold MultiTapeTM.step
      change (((pairCountTM M).tm.tr (.inr (.inl 3)) _ _).apply _).state = none ∧ _
      rw [lenCfg_read]
      simp [hx, pairCountTM, lenAction, lenCfg, captureCfg, Cfg.workTapeSymbols,
        bufferTape_left, Action.apply]
    | succ r =>
      have hs : (pairCountTM M).tm.step
          (lenCfg M c (some (.inr (.inl 3))) pre.length (by simp [hx]) (r + 1)) =
          lenCfg M c (some (.inr (.inl 3))) (pre.length + 1) (by simp [hx]) r := by
        unfold MultiTapeTM.step
        change ((pairCountTM M).tm.tr (.inr (.inl 3)) _ _).apply _ = _
        rw [lenCfg_read]
        have hin : x[pre.length]? = some b := by simp [hx]
        have hw : (lenCfg M c (some (.inr (.inl 3))) pre.length
            (by simp [hx]) (r + 1)).workTapeSymbols (Fin.last M.k) =
              some (c.output[r]'(by omega)) := by
          simp [lenCfg, captureCfg, Cfg.workTapeSymbols, bufferTape,
            List.getElem?_eq_getElem (by omega : r < c.output.length)]
        simp only [pairCountTM, hin, hw]
        exact lenAction_apply M c _ _ pre.length (pre.length + 1) (r + 1) r
          (by simp [hx]) (by simp [hx]) .pos .neg none
          (moveInputPos_pos_of_ne_right _ (by simp [hx])) (by simp [SignType.cast]; omega)
      obtain ⟨t, ht, hh, ho⟩ := ih (pre ++ [b]) (by simpa [List.append_assoc] using hx)
        r (by omega)
      refine ⟨1 + t, by simp only [List.length_cons]; omega, ?_⟩
      rw [MultiTapeTM.runFrom_add]
      simp only [MultiTapeTM.runFrom_succ_eq_step, MultiTapeTM.runFrom_zero]
      rw [hs]
      simpa using And.intro hh ho
```

## TCSlib/Complexity/TuringMachine/Build/Primitives.lean:7370 — Turing.FinTM.emitterToken_double

```lean
private lemma emitterToken_double (x pre rest out : List Bool) (b : Bool)
    (hx : x = pre ++ b :: rest) :
    unaryTokenTM.tm.runFrom
      (scanCfg x (some (0 : Fin 6)) pre.length (by simp [hx]) out) 2 =
      scanCfg x (some (if b then (0 : Fin 6) else 3)) (pre ++ [b]).length
        (by simp [hx]) (out ++ [b, b]) := by
  have hlen : pre.length < x.length := by simp [hx]
  have hread : x[pre.length]? = some b := by simp [hx]
  have hfirst : unaryTokenTM.tm.step
      (scanCfg x (some (0 : Fin 6)) pre.length (by omega) out) =
      scanCfg x (some (if b then (1 : Fin 6) else 2)) pre.length (by omega)
        (out ++ [b]) := by
    unfold MultiTapeTM.step
    change (unaryTokenTM.tm.tr (0 : Fin 6) _ _).apply _ = _
    rw [scanCfg_read, hread]
    apply Cfg.ext_zero_tapes <;> simp [unaryTokenTM, Action.apply, scanCfg]
  rw [show 2 = 1 + 1 by omega, MultiTapeTM.runFrom_succ_eq_step',
    MultiTapeTM.runFrom_succ_eq_step', MultiTapeTM.runFrom_zero, hfirst]
  cases b <;>
    apply Cfg.ext_zero_tapes
  all_goals first
    | rfl
    | simpa [MultiTapeTM.step, unaryTokenTM, Action.apply, scanCfg] using
        moveInputPos_pos_of_ne_right
          (⟨pre.length + 1, by omega⟩ : Fin (x.length + 2)) (by simp; omega)
    | simp [MultiTapeTM.step, unaryTokenTM, Action.apply, scanCfg, List.append_assoc]
```

## TCSlib/Complexity/TuringMachine/Build/Primitives.lean:7399 — Turing.FinTM.emitterToken_separator

```lean
private lemma emitterToken_separator (x out : List Bool) (i : ℕ) (hi : i ≤ x.length) :
    unaryTokenTM.tm.runFrom (scanCfg x (some (3 : Fin 6)) i hi out) 2 =
      scanCfg x (some (5 : Fin 6)) i hi (out ++ [false, true]) := by
  rw [show 2 = 1 + 1 by omega, MultiTapeTM.runFrom_succ_eq_step',
    MultiTapeTM.runFrom_succ_eq_step', MultiTapeTM.runFrom_zero]
  apply Cfg.ext_zero_tapes <;>
    simp [MultiTapeTM.step, unaryTokenTM, Action.apply, scanCfg, List.append_assoc]
```

## TCSlib/Complexity/TuringMachine/Build/Loop.lean:3641 — Turing.FinTM.emCall_first_entry

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

## TCSlib/Complexity/TuringMachine/Build/Loop.lean:4436 — Turing.FinTM.emCall_bank_initial

```lean
private lemma emCall_bank_initial (M : FinTM Bool) (emit : Bool)
    (x arg cap : List Bool) (T : ℕ) (i : Fin M.k) :
    let frame := emCallBankFrame M emit x arg cap T i.val (.inr (.inl (i.castSucc, 0)))
    emCallEmbeddedCfg (emCallTripleEmbedding M i) (fun q => .inr (.inl (i.castSucc, q)))
      frame.workTapes frame.workTapePos
      (emCallClearCfg x 1 0 ((M.tm.runFrom (M.tm.initCfg arg) T).workTapes i)
        (emCallSpan (emCallLo M arg T i) (emCallHi M arg T i)) (bufferTape [true])
        ((M.tm.runFrom (M.tm.initCfg arg) T).workTapePos i)) = frame := by
  dsimp only
  refine Cfg.ext rfl rfl ?_ ?_ rfl
  · funext j
    simp only [emCallEmbeddedCfg, Cfg.mapState]
    rcases emCall_layout_cases M j with h | h | ⟨l, r, h⟩
    · subst j
      trans (emCallBankFrame M emit x arg cap T i.val (.inr (.inl (i.castSucc, 0)))).workTapes (emCallPairIndex M 0)
      · exact ((embedEmitTM_frame (emCallTripleEmbedding M i) emCallClearTM.tm _ _ [] _ 0).1 (emCallPairIndex M 0)
          (by rintro ⟨r', hr⟩
              have h := congrArg (emCallTripleSelect M i) hr
              change emCallTripleSelect M i (emCallTripleIndex M i r') = _ at h
              simp only [emCall_triple_inverse, emCall_triple_pair] at h
              cases h)).1
      · rfl
    · subst j
      trans (emCallBankFrame M emit x arg cap T i.val (.inr (.inl (i.castSucc, 0)))).workTapes (emCallPairIndex M 1)
      · exact ((embedEmitTM_frame (emCallTripleEmbedding M i) emCallClearTM.tm _ _ [] _ 0).1 (emCallPairIndex M 1)
          (by rintro ⟨r', hr⟩
              have h := congrArg (emCallTripleSelect M i) hr
              change emCallTripleSelect M i (emCallTripleIndex M i r') = _ at h
              simp only [emCall_triple_inverse, emCall_triple_pair] at h
              cases h)).1
      · rfl
    · subst j
      by_cases he : l = i
      · subst l
        change (embedEmitCfg _ _ _ [] _).workTapes ((emCallTripleEmbedding M i) r) = _
        rw [embedEmitCfg_selected_tape]
        simp only [emCallBankFrame, emCallFrame, emCall_layout_triple, emCallClearCfg]
        fin_cases r <;> simp
      · trans (emCallBankFrame M emit x arg cap T i.val (.inr (.inl (i.castSucc, 0)))).workTapes (emCallTripleIndex M l r)
        · exact ((embedEmitTM_frame (emCallTripleEmbedding M i) emCallClearTM.tm _ _ [] _ 0).1 (emCallTripleIndex M l r)
            (by rintro ⟨r', hr⟩
                have h := congrArg (emCallTripleSelect M i) hr
                change emCallTripleSelect M i (emCallTripleIndex M i r') = _ at h
                simp only [emCall_triple_inverse, emCall_triple_other, if_neg he] at h
                cases h)).1
        · rfl
  · funext j
    simp only [emCallEmbeddedCfg, Cfg.mapState]
    rcases emCall_layout_cases M j with h | h | ⟨l, r, h⟩
    · subst j
      trans (emCallBankFrame M emit x arg cap T i.val (.inr (.inl (i.castSucc, 0)))).workTapePos (emCallPairIndex M 0)
      · exact ((embedEmitTM_frame (emCallTripleEmbedding M i) emCallClearTM.tm _ _ [] _ 0).1 (emCallPairIndex M 0)
          (by rintro ⟨r', hr⟩
              have h := congrArg (emCallTripleSelect M i) hr
              change emCallTripleSelect M i (emCallTripleIndex M i r') = _ at h
              simp only [emCall_triple_inverse, emCall_triple_pair] at h
              cases h)).2
      · rfl
    · subst j
      trans (emCallBankFrame M emit x arg cap T i.val (.inr (.inl (i.castSucc, 0)))).workTapePos (emCallPairIndex M 1)
      · exact ((embedEmitTM_frame (emCallTripleEmbedding M i) emCallClearTM.tm _ _ [] _ 0).1 (emCallPairIndex M 1)
          (by rintro ⟨r', hr⟩
              have h := congrArg (emCallTripleSelect M i) hr
              change emCallTripleSelect M i (emCallTripleIndex M i r') = _ at h
              simp only [emCall_triple_inverse, emCall_triple_pair] at h
              cases h)).2
      · rfl
    · subst j
      by_cases he : l = i
      · subst l
        change (embedEmitCfg _ _ _ [] _).workTapePos ((emCallTripleEmbedding M i) r) = _
        rw [embedEmitCfg_selected_pos]
        simp only [emCallBankFrame, emCallFrame, emCall_layout_triple, emCallClearCfg]
        fin_cases r <;> simp
      · trans (emCallBankFrame M emit x arg cap T i.val (.inr (.inl (i.castSucc, 0)))).workTapePos (emCallTripleIndex M l r)
        · exact ((embedEmitTM_frame (emCallTripleEmbedding M i) emCallClearTM.tm _ _ [] _ 0).1 (emCallTripleIndex M l r)
            (by rintro ⟨r', hr⟩
                have h := congrArg (emCallTripleSelect M i) hr
                change emCallTripleSelect M i (emCallTripleIndex M i r') = _ at h
                simp only [emCall_triple_inverse, emCall_triple_other, if_neg he] at h
                cases h)).2
        · rfl
```

## TCSlib/Complexity/TuringMachine/Build/Loop.lean:4524 — Turing.FinTM.emCall_bank_final

```lean
private lemma emCall_bank_final (M : FinTM Bool) (emit : Bool)
    (x arg cap : List Bool) (T : ℕ) (i : Fin M.k) :
    let frame := emCallBankFrame M emit x arg cap T i.val (.inr (.inl (i.castSucc, 0)))
    emCallEmbeddedCfg (emCallTripleEmbedding M i) (fun q => .inr (.inl (i.castSucc, q)))
      frame.workTapes frame.workTapePos
      (emCallClearCfg x 1 3 (fun _ => none) (fun _ => none) (fun _ => none) 0) =
      emCallBankFrame M emit x arg cap T (i.val + 1) (.inr (.inl (i.castSucc, 3))) := by
  dsimp only
  refine Cfg.ext rfl rfl ?_ ?_ rfl
  · funext j
    simp only [emCallEmbeddedCfg, Cfg.mapState]
    rcases emCall_layout_cases M j with h | h | ⟨l, r, h⟩
    · subst j
      trans (emCallBankFrame M emit x arg cap T i.val (.inr (.inl (i.castSucc, 0)))).workTapes (emCallPairIndex M 0)
      · exact ((embedEmitTM_frame (emCallTripleEmbedding M i) emCallClearTM.tm _ _ [] _ 0).1 (emCallPairIndex M 0)
          (by rintro ⟨r', hr⟩
              have h := congrArg (emCallTripleSelect M i) hr
              change emCallTripleSelect M i (emCallTripleIndex M i r') = _ at h
              simp only [emCall_triple_inverse, emCall_triple_pair] at h
              cases h)).1
      · simp [emCallBankFrame, emCallFrame, emCall_layout_pair]
    · subst j
      trans (emCallBankFrame M emit x arg cap T i.val (.inr (.inl (i.castSucc, 0)))).workTapes (emCallPairIndex M 1)
      · exact ((embedEmitTM_frame (emCallTripleEmbedding M i) emCallClearTM.tm _ _ [] _ 0).1 (emCallPairIndex M 1)
          (by rintro ⟨r', hr⟩
              have h := congrArg (emCallTripleSelect M i) hr
              change emCallTripleSelect M i (emCallTripleIndex M i r') = _ at h
              simp only [emCall_triple_inverse, emCall_triple_pair] at h
              cases h)).1
      · simp [emCallBankFrame, emCallFrame, emCall_layout_pair]
    · subst j
      by_cases he : l = i
      · subst l
        change (embedEmitCfg _ _ _ [] _).workTapes ((emCallTripleEmbedding M i) r) = _
        rw [embedEmitCfg_selected_tape]
        simp only [emCallBankFrame, emCallFrame, emCall_layout_triple, emCallClearCfg]
        fin_cases r <;> simp
      · trans (emCallBankFrame M emit x arg cap T i.val (.inr (.inl (i.castSucc, 0)))).workTapes (emCallTripleIndex M l r)
        · exact ((embedEmitTM_frame (emCallTripleEmbedding M i) emCallClearTM.tm _ _ [] _ 0).1 (emCallTripleIndex M l r)
            (by rintro ⟨r', hr⟩
                have h := congrArg (emCallTripleSelect M i) hr
                change emCallTripleSelect M i (emCallTripleIndex M i r') = _ at h
                simp only [emCall_triple_inverse, emCall_triple_other, if_neg he] at h
                cases h)).1
        · have hi : l.val ≠ i.val := fun h => he (Fin.ext h)
          have hiff : l.val < i.val + 1 ↔ l.val < i.val := by omega
          simp only [emCallBankFrame, emCallFrame, emCall_layout_triple, hiff]
  · funext j
    simp only [emCallEmbeddedCfg, Cfg.mapState]
    rcases emCall_layout_cases M j with h | h | ⟨l, r, h⟩
    · subst j
      trans (emCallBankFrame M emit x arg cap T i.val (.inr (.inl (i.castSucc, 0)))).workTapePos (emCallPairIndex M 0)
      · exact ((embedEmitTM_frame (emCallTripleEmbedding M i) emCallClearTM.tm _ _ [] _ 0).1 (emCallPairIndex M 0)
          (by rintro ⟨r', hr⟩
              have h := congrArg (emCallTripleSelect M i) hr
              change emCallTripleSelect M i (emCallTripleIndex M i r') = _ at h
              simp only [emCall_triple_inverse, emCall_triple_pair] at h
              cases h)).2
      · simp [emCallBankFrame, emCallFrame, emCall_layout_pair]
    · subst j
      trans (emCallBankFrame M emit x arg cap T i.val (.inr (.inl (i.castSucc, 0)))).workTapePos (emCallPairIndex M 1)
      · exact ((embedEmitTM_frame (emCallTripleEmbedding M i) emCallClearTM.tm _ _ [] _ 0).1 (emCallPairIndex M 1)
          (by rintro ⟨r', hr⟩
              have h := congrArg (emCallTripleSelect M i) hr
              change emCallTripleSelect M i (emCallTripleIndex M i r') = _ at h
              simp only [emCall_triple_inverse, emCall_triple_pair] at h
              cases h)).2
      · simp [emCallBankFrame, emCallFrame, emCall_layout_pair]
    · subst j
      by_cases he : l = i
      · subst l
        change (embedEmitCfg _ _ _ [] _).workTapePos ((emCallTripleEmbedding M i) r) = _
        rw [embedEmitCfg_selected_pos]
        simp only [emCallBankFrame, emCallFrame, emCall_layout_triple, emCallClearCfg]
        fin_cases r <;> simp
      · trans (emCallBankFrame M emit x arg cap T i.val (.inr (.inl (i.castSucc, 0)))).workTapePos (emCallTripleIndex M l r)
        · exact ((embedEmitTM_frame (emCallTripleEmbedding M i) emCallClearTM.tm _ _ [] _ 0).1 (emCallTripleIndex M l r)
            (by rintro ⟨r', hr⟩
                have h := congrArg (emCallTripleSelect M i) hr
                change emCallTripleSelect M i (emCallTripleIndex M i r') = _ at h
                simp only [emCall_triple_inverse, emCall_triple_other, if_neg he] at h
                cases h)).2
        · have hi : l.val ≠ i.val := fun h => he (Fin.ext h)
          have hiff : l.val < i.val + 1 ↔ l.val < i.val := by omega
          simp only [emCallBankFrame, emCallFrame, emCall_layout_triple, hiff]
```

## TCSlib/Complexity/TuringMachine/Build/Catalog.lean:218 — Turing.copyMapTM

```lean
def copyMapTM {Symbol : Type*} {Δ : Type*} (k : ℕ) (src dst : Fin k) (extract : Symbol → Δ)
    (merge : Option Symbol → Δ → Symbol) : MultiTapeTM k Symbol SweepPhase where
  q₀ := .sweep
  tr := fun q _ w =>
    match q with
    | .sweep =>
      match w src with
      | some b =>
        ⟨0, fun j => if j = dst then (some (some (merge (w dst) (extract b))), SignType.pos)
            else if j = src then (none, SignType.pos) else (none, 0),
          none, some .sweep⟩
      | none =>
        ⟨0, fun j => if j = src ∨ j = dst then (none, SignType.neg)
            else (none, 0), none, some .rewind⟩
    | .rewind =>
      match w src with
      | some _ =>
        ⟨0, fun j => if j = src ∨ j = dst then (none, SignType.neg)
            else (none, 0), none, some .rewind⟩
      | none =>
        ⟨0, fun j => if j = src ∨ j = dst then (none, SignType.pos)
            else (none, 0), none, some .done⟩
    | .done => ⟨0, fun _ => (none, 0), none, some .done⟩
```

## TCSlib/Complexity/TuringMachine/Build/Catalog.lean:247 — Turing.transferMapTM

```lean
def transferMapTM {Symbol : Type*} {Δ : Type*} (k : ℕ) (src dst : Fin k) (extract : Symbol → Δ)
    (merge : Option Symbol → Δ → Symbol) (rest : Symbol → Option Symbol) :
    MultiTapeTM k Symbol SweepPhase where
  q₀ := .sweep
  tr := fun q _ w =>
    match q with
    | .sweep =>
      match w src with
      | some b =>
        ⟨0, fun j => if j = dst then (some (some (merge (w dst) (extract b))), SignType.pos)
            else if j = src then (none, SignType.pos) else (none, 0),
          none, some .sweep⟩
      | none =>
        ⟨0, fun j => if j = src ∨ j = dst then (none, SignType.neg)
            else (none, 0), none, some .rewind⟩
    | .rewind =>
      match w src with
      | some b =>
        ⟨0, fun j => if j = src then (some (rest b), SignType.neg)
            else if j = dst then (none, SignType.neg) else (none, 0),
          none, some .rewind⟩
      | none =>
        ⟨0, fun j => if j = src ∨ j = dst then (none, SignType.pos)
            else (none, 0), none, some .done⟩
    | .done => ⟨0, fun _ => (none, 0), none, some .done⟩
```

## TCSlib/Complexity/TuringMachine/Build/Catalog.lean:1491 — Turing.Cfg.ofWords_copy_endpoint

```lean
theorem Cfg.ofWords_copy_endpoint {k : ℕ} {S : Type*} {x : List Bool} (q q' : S)
    (w : Fin k → List Bool) (src dst : Fin k) (hdst : w dst = []) :
    ({ (Cfg.ofWords (input := x) q w) with
        state := some q'
        workTapes := fun j p =>
          if j = dst ∧ (Cfg.ofWords (input := x) q w).workTapePos j ≤ p ∧
              p < (Cfg.ofWords (input := x) q w).workTapePos j + ((w src).length : ℤ)
            then FinTM.bufferTape (w src) (p - (Cfg.ofWords (input := x) q w).workTapePos j)
          else (Cfg.ofWords (input := x) q w).workTapes j p } : Cfg k Bool S x) =
      Cfg.ofWords q' (Function.update w dst (w src)) := by
  apply Cfg.ext <;> simp [Cfg.ofWords]
  funext j q
  by_cases hj : j = dst
  · subst j
    simp only [Function.update_self, hdst, FinTM.bufferTape_nil, true_and]
    split_ifs with hq
    · rfl
    · by_cases h0 : 0 ≤ q
      · simp [FinTM.bufferTape, h0]
        omega
      · simp [FinTM.bufferTape, h0]
  · simp [hj]
```

## TCSlib/Complexity/TuringMachine/Build/Catalog.lean:1412 — Turing.Cfg.ofWords_transfer_endpoint

```lean
theorem Cfg.ofWords_transfer_endpoint {k : ℕ} {S : Type*} {x : List Bool} (q q' : S)
    (w : Fin k → List Bool) (src dst : Fin k) (hne : src ≠ dst) (hdst : w dst = []) :
    ({ (Cfg.ofWords (input := x) q w) with
        state := some q'
        workTapes := fun j p =>
          if j = src ∧ (Cfg.ofWords (input := x) q w).workTapePos j ≤ p ∧
              p < (Cfg.ofWords (input := x) q w).workTapePos j + ((w src).length : ℤ)
            then none
          else if j = dst ∧ (Cfg.ofWords (input := x) q w).workTapePos j ≤ p ∧
              p < (Cfg.ofWords (input := x) q w).workTapePos j + ((w src).length : ℤ)
            then FinTM.bufferTape (w src) (p - (Cfg.ofWords (input := x) q w).workTapePos j)
          else (Cfg.ofWords (input := x) q w).workTapes j p } : Cfg k Bool S x) =
      Cfg.ofWords q' (Function.update (Function.update w src []) dst (w src)) := by
  apply Cfg.ext <;> simp [Cfg.ofWords]
  funext j q
  by_cases hs : j = src
  · subst j
    simp only [Function.update_of_ne hne, Function.update_self,
      FinTM.bufferTape_nil, hne, false_and, ite_false, true_and]
    split_ifs with hq
    · rfl
    · by_cases h0 : 0 ≤ q
      · simp [FinTM.bufferTape, h0]
        omega
      · simp [FinTM.bufferTape, h0]
  · by_cases hd : j = dst
    · subst j
      simp only [Function.update_self, hdst, FinTM.bufferTape_nil,
        hs, false_and, ite_false, true_and]
      split_ifs with hq
      · rfl
      · by_cases h0 : 0 ≤ q
        · simp [FinTM.bufferTape, h0]
          omega
        · simp [FinTM.bufferTape, h0]
    · simp [hs, hd]
```

## TCSlib/Complexity/TuringMachine/Build/Catalog.lean:1562 — Turing.incrementTM_run_succ_ofCfg

```lean
theorem incrementTM_run_succ_ofCfg {k : ℕ} {x : List Bool} (i : Fin k)
    (w v : List Bool) (hv : incFixed w = some v) (d : Cfg k Bool FlagPhase x)
    (hstate : d.state = some FlagPhase.run)
    (hw : ∀ p : ℤ, -1 ≤ p → p ≤ (w.length : ℤ) →
      d.workTapes i (d.workTapePos i + p) = FinTM.bufferTape w p) :
    (incrementTM k i).runFrom d (2 * (w.takeWhile id).length + 2) =
        { d with
          state := some (FlagPhase.done true)
          workTapes := fun j q =>
            if j = i ∧ d.workTapePos j ≤ q ∧ q < d.workTapePos j + (w.length : ℤ)
              then FinTM.bufferTape v (q - d.workTapePos j)
            else d.workTapes j q } ∧
      (∀ t < 2 * (w.takeWhile id).length + 2, ∀ b : Bool,
        ((incrementTM k i).runFrom d t).state ≠ some (FlagPhase.done b)) ∧
      (∀ (j : Fin k) (t : ℕ), t ≤ 2 * (w.takeWhile id).length + 2 →
        if j = i then
          ((incrementTM k i).runFrom d t).workTapePos j ∈
            Finset.Icc (d.workTapePos j - 1)
              (d.workTapePos j + ((w.takeWhile id).length : ℤ))
        else ((incrementTM k i).runFrom d t).workTapePos j = d.workTapePos j) := by
  obtain ⟨p, tail, hsplit⟩ := catalog_increment_split w
  rw [hsplit, catalog_increment_value] at hv
  cases tail with
  | none => simp at hv
  | some tail =>
    have hv' : v = List.replicate p false ++ true :: tail := by simpa using hv.symm
    have hp : (w.takeWhile id).length = p := by
      simp [hsplit, List.takeWhile_append, List.takeWhile_replicate]
    rw [hp]
    constructor
    · rw [catalog_increment_trace i w d hstate hw p (some tail) hsplit]
      simp only [catalogTrace, show ¬2 * p + 2 ≤ p by omega,
        show ¬2 * p + 2 ≤ 2 * p + 1 by omega, ite_false]
      apply Cfg.ext <;> simp [catalogIncR, catalogTape, hv', hsplit]
      funext j q
      by_cases hj : j = i <;> simp [hj, catalogTape]
    · constructor
      · intro t ht b
        rw [catalog_increment_trace i w d hstate hw p (some tail) hsplit]
        simp only [catalogTrace]
        split_ifs <;> simp_all [catalogIncF, catalogIncR] <;> omega
      · intro j t ht
        rw [catalog_increment_trace i w d hstate hw p (some tail) hsplit]
        simp only [catalogTrace]
        split_ifs <;> simp_all [catalogIncF, catalogIncR, Finset.mem_Icc] <;> omega
```

## TCSlib/Complexity/TuringMachine/Build/Catalog.lean:1619 — Turing.incrementTM_run_overflow_ofCfg

```lean
theorem incrementTM_run_overflow_ofCfg {k : ℕ} {x : List Bool} (i : Fin k)
    (w : List Bool) (hv : incFixed w = none) (d : Cfg k Bool FlagPhase x)
    (hstate : d.state = some FlagPhase.run)
    (hw : ∀ p : ℤ, -1 ≤ p → p ≤ (w.length : ℤ) →
      d.workTapes i (d.workTapePos i + p) = FinTM.bufferTape w p) :
    (incrementTM k i).runFrom d (2 * w.length + 2) =
        { d with
          state := some (FlagPhase.done false)
          workTapes := fun j q =>
            if j = i ∧ d.workTapePos j ≤ q ∧ q < d.workTapePos j + (w.length : ℤ)
              then FinTM.bufferTape (List.replicate w.length false) (q - d.workTapePos j)
            else d.workTapes j q } ∧
      (∀ t < 2 * w.length + 2, ∀ b : Bool,
        ((incrementTM k i).runFrom d t).state ≠ some (FlagPhase.done b)) ∧
      (∀ (j : Fin k) (t : ℕ), t ≤ 2 * w.length + 2 →
        if j = i then
          ((incrementTM k i).runFrom d t).workTapePos j ∈
            Finset.Icc (d.workTapePos j - 1) (d.workTapePos j + (w.length : ℤ))
        else ((incrementTM k i).runFrom d t).workTapePos j = d.workTapePos j) := by
  obtain ⟨p, tail, hsplit⟩ := catalog_increment_split w
  rw [hsplit, catalog_increment_value] at hv
  cases tail with
  | some tail => simp at hv
  | none =>
    have hp : w.length = p := by simp [hsplit]
    rw [hp]
    constructor
    · rw [catalog_increment_trace i w d hstate hw p none hsplit]
      simp only [catalogTrace, show ¬2 * p + 2 ≤ p by omega,
        show ¬2 * p + 2 ≤ 2 * p + 1 by omega, ite_false]
      apply Cfg.ext <;> simp [catalogIncR, catalogTape]
      funext j q
      by_cases hj : j = i <;> simp [hj, catalogTape]
    · constructor
      · intro t ht b
        rw [catalog_increment_trace i w d hstate hw p none hsplit]
        simp only [catalogTrace]
        split_ifs <;> simp_all [catalogIncF, catalogIncR] <;> omega
      · intro j t ht
        rw [catalog_increment_trace i w d hstate hw p none hsplit]
        simp only [catalogTrace]
        split_ifs <;> simp_all [catalogIncF, catalogIncR, Finset.mem_Icc] <;> omega
```
