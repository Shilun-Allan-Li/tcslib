## TCSlib/Complexity/ClassNP/SAT.lean:3980–3982

```lean
3980: /-- Six finite modules form the streaming body: startup append and install,
3981: then the recurring pack, append, emit, and install calls. -/
3982: private abbrev SatHostState (M : Fin 6 → FinTM Bool) := Unit ⊕ (Σ i, (M i).State)
```

## TCSlib/Complexity/CookLevin/Hardness.lean:6319–6321

```lean
6319: /-- Five finite modules form the body: native input copy, full packed-record
6320: installation and cursor installation, then recurring emission and cursor update. -/
6321: private abbrev CLA5HostState (M : Fin 5 → FinTM Bool) := Unit ⊕ (Σ i, (M i).State)
```

## TCSlib/Complexity/ClassNP/SAT.lean:3990–3992

```lean
3990: /-- A named entry state inside the finite body. -/
3991: private def satHostEntry (M : Fin 6 → FinTM Bool) (i : Fin 6) : SatHostState M :=
3992:   .inr ⟨i, (M i).tm.q₀⟩
```

## TCSlib/Complexity/CookLevin/Hardness.lean:6328–6330

```lean
6328: /-- A named entry state inside the finite body. -/
6329: private def clA5HostEntry (M : Fin 5 → FinTM Bool) (i : Fin 5) : CLA5HostState M :=
6330:   .inr ⟨i, (M i).tm.q₀⟩
```

## TCSlib/Complexity/ClassNP/SAT.lean:3994–3998

```lean
3994: /-- Resolve a finite module's return, with no additional tape operation. -/
3995: private def satHostRet (M : Fin 6 → FinTM Bool) (i : Fin 6) : SatHostState M :=
3996:   match satHostNext i with
3997:   | some j => satHostEntry M j
3998:   | none => .inl ()
```

## TCSlib/Complexity/CookLevin/Hardness.lean:6332–6336

```lean
6332: /-- Resolve a finite module's return, with no additional tape operation. -/
6333: private def clA5HostRet (M : Fin 5 → FinTM Bool) (i : Fin 5) : CLA5HostState M :=
6334:   match clA5HostNext i with
6335:   | some j => clA5HostEntry M j
6336:   | none => .inl ()
```

## TCSlib/Complexity/ClassNP/SAT.lean:4000–4011

```lean
4000: /-- The actual finite controller. All modules use the same padded work bank,
4001: so the clean-call contracts restore scratch before each next call. `emitAction`
4002: forwards the halting transition as well as ordinary transitions. -/
4003: private def satHostTM (M : Fin 6 → FinTM Bool) (K : ℕ) (hk : ∀ i, (M i).k ≤ K) : FinTM Bool where
4004:   k := K
4005:   State := SatHostState M
4006:   tm := {
4007:     q₀ := satHostEntry M 0
4008:     tr := fun q inp work => match q with
4009:       | .inl _ => FinTM.controlAction 0 (some (satHostEntry M 2))
4010:       | .inr ⟨i, s⟩ => emitAction (fun s => .inr ⟨i, s⟩) (satHostRet M i)
4011:           ((satPadTM (M i) K (hk i)).tm.tr s inp work) }
```

## TCSlib/Complexity/CookLevin/Hardness.lean:6338–6349

```lean
6338: /-- The actual finite controller. All modules use the same padded work bank,
6339: so the clean-call contracts restore scratch before each next call. `emitAction`
6340: forwards the halting transition as well as ordinary transitions. -/
6341: private def clA5HostTM (M : Fin 5 → FinTM Bool) (K : ℕ) (hk : ∀ i, (M i).k ≤ K) : FinTM Bool where
6342:   k := K
6343:   State := CLA5HostState M
6344:   tm := {
6345:     q₀ := clA5HostEntry M 0
6346:     tr := fun q inp work => match q with
6347:       | .inl _ => FinTM.controlAction 0 (some (clA5HostEntry M 3))
6348:       | .inr ⟨i, s⟩ => emitAction (fun s => .inr ⟨i, s⟩) (clA5HostRet M i)
6349:           ((clA5PadTM (M i) K (hk i)).tm.tr s inp work) }
```

## TCSlib/Complexity/ClassNP/SAT.lean:4013–4027

```lean
4013: /-- Forwarding a padded clean configuration produces the host's canonical
4014: seam with precisely the supplied output prefix. Positive tape count is used
4015: only to identify the real tape-zero word. -/
4016: private lemma satHost_seam (M : Fin 6 → FinTM Bool) (K : ℕ) (i : Fin 6)
4017:     (hp : 0 < (M i).k) (x w pre out : List Bool) (q : (M i).State)
4018:     (state : Option (M i).State) :
4019:     emitCfg (fun s => (Sum.inr ⟨i, s⟩ : SatHostState M)) (satHostRet M i) pre
4020:       (satPadCfg (K := K) {Cfg.ofWords (input := x) q (stateWord (M i).k w)
4021:         with state := state, output := out}) =
4022:       {Cfg.ofWords (((state.map (fun s => (Sum.inr ⟨i, s⟩ : SatHostState M))).getD (satHostRet M i)))
4023:         (stateWord K w) with output := pre ++ out} := by
4024:   have h := satPad_seam (K := K) (x := x) hp q w out
4025:   refine Cfg.ext rfl rfl ?_ ?_ rfl
4026:   · exact congrArg (fun c : Cfg K Bool (M i).State x => c.workTapes) h
4027:   · exact congrArg (fun c : Cfg K Bool (M i).State x => c.workTapePos) h
```

## TCSlib/Complexity/CookLevin/Hardness.lean:6351–6365

```lean
6351: /-- Forwarding a padded clean configuration produces the host's canonical
6352: seam with precisely the supplied output prefix. Positive tape count is used
6353: only to identify the real tape-zero word. -/
6354: private lemma clA5Host_seam (M : Fin 5 → FinTM Bool) (K : ℕ) (i : Fin 5)
6355:     (hp : 0 < (M i).k) (x w pre out : List Bool) (q : (M i).State)
6356:     (state : Option (M i).State) :
6357:     emitCfg (fun s => (Sum.inr ⟨i, s⟩ : CLA5HostState M)) (clA5HostRet M i) pre
6358:       (clA5PadCfg (K := K) {Cfg.ofWords (input := x) q (stateWord (M i).k w)
6359:         with state := state, output := out}) =
6360:       {Cfg.ofWords (((state.map (fun s => (Sum.inr ⟨i, s⟩ : CLA5HostState M))).getD (clA5HostRet M i)))
6361:         (stateWord K w) with output := pre ++ out} := by
6362:   have h := clA5Pad_seam (K := K) (x := x) hp q w out
6363:   refine Cfg.ext rfl rfl ?_ ?_ rfl
6364:   · exact congrArg (fun c : Cfg K Bool (M i).State x => c.workTapes) h
6365:   · exact congrArg (fun c : Cfg K Bool (M i).State x => c.workTapePos) h
```

## TCSlib/Complexity/ClassNP/SAT.lean:4029–4072

```lean
4029: /-- Run one clean module inside the body, forwarding exactly its output.
4030: **Proof sketch.** Padding preserves the source run. The audited `emit_run`
4031: then transfers every live prefix and the halting endpoint; live prefixes
4032: always remain in that module's state summand, hence cannot hit the anchor. -/
4033: private lemma satHost_call (M : Fin 6 → FinTM Bool) (K : ℕ) (hk : ∀ i, (M i).k ≤ K)
4034:     (i : Fin 6) (hp : 0 < (M i).k) (x arg result out pre : List Bool)
4035:     (q : (M i).State) (t : ℕ)
4036:     (hg : ∀ v < t, ¬((M i).tm.runFrom
4037:       (Cfg.ofWords (input := x) (M i).tm.q₀ (stateWord (M i).k arg)) v).Halted)
4038:     (he : (M i).tm.runFrom
4039:       (Cfg.ofWords (input := x) (M i).tm.q₀ (stateWord (M i).k arg)) t =
4040:       {Cfg.ofWords q (stateWord (M i).k result) with state := none, output := out}) :
4041:     (∀ v < t, ((satHostTM M K hk).tm.runFrom
4042:       {Cfg.ofWords (input := x) (satHostEntry M i) (stateWord K arg) with output := pre} v).state
4043:         ≠ some (.inl ())) ∧
4044:     (satHostTM M K hk).tm.runFrom
4045:       {Cfg.ofWords (input := x) (satHostEntry M i) (stateWord K arg) with output := pre} t =
4046:       {Cfg.ofWords (satHostRet M i) (stateWord K result) with output := pre ++ out} := by
4047:   let c := Cfg.ofWords (input := x) (M i).tm.q₀ (stateWord (M i).k arg)
4048:   let emb : (M i).State → SatHostState M := fun s => .inr ⟨i, s⟩
4049:   have hinit : emitCfg emb (satHostRet M i) pre (satPadCfg (K := K) c) =
4050:       {Cfg.ofWords (input := x) (satHostEntry M i) (stateWord K arg) with output := pre} := by
4051:     simpa [emb, c, satHostEntry] using
4052:       satHost_seam M K i hp x arg pre [] (M i).tm.q₀ (some (M i).tm.q₀)
4053:   have hrun (v : ℕ) (hv : v ≤ t) :
4054:       (satHostTM M K hk).tm.runFrom
4055:         {Cfg.ofWords (input := x) (satHostEntry M i) (stateWord K arg) with output := pre} v =
4056:         emitCfg emb (satHostRet M i) pre (satPadCfg ((M i).tm.runFrom c v)) := by
4057:     rw [← hinit]
4058:     rw [emit_run (satPadTM (M i) K (hk i)).tm (satHostTM M K hk).tm emb (satHostRet M i)
4059:       (by intros; rfl) pre _ v (by
4060:         intro u hu
4061:         rw [satPad_run]
4062:         exact hg u (by omega))]
4063:     rw [satPad_run]
4064:   constructor
4065:   · intro v hv
4066:     rw [hrun v (Nat.le_of_lt hv)]
4067:     have hl := hg v hv
4068:     cases hs : ((M i).tm.runFrom c v).state with
4069:     | none => exact False.elim (hl hs)
4070:     | some s => simp [emitCfg, satPadCfg, hs, emb]
4071:   · rw [hrun t (Nat.le_refl _), show (M i).tm.runFrom c t = _ from he]
4072:     exact satHost_seam M K i hp x result pre out q none
```

## TCSlib/Complexity/CookLevin/Hardness.lean:6367–6410

```lean
6367: /-- Run one clean module inside the body, forwarding exactly its output.
6368: **Proof sketch.** Padding preserves the source run. The audited `emit_run`
6369: then transfers every live prefix and the halting endpoint; live prefixes
6370: always remain in that module's state summand, hence cannot hit the anchor. -/
6371: private lemma clA5Host_call (M : Fin 5 → FinTM Bool) (K : ℕ) (hk : ∀ i, (M i).k ≤ K)
6372:     (i : Fin 5) (hp : 0 < (M i).k) (x arg result out pre : List Bool)
6373:     (q : (M i).State) (t : ℕ)
6374:     (hg : ∀ v < t, ¬((M i).tm.runFrom
6375:       (Cfg.ofWords (input := x) (M i).tm.q₀ (stateWord (M i).k arg)) v).Halted)
6376:     (he : (M i).tm.runFrom
6377:       (Cfg.ofWords (input := x) (M i).tm.q₀ (stateWord (M i).k arg)) t =
6378:       {Cfg.ofWords q (stateWord (M i).k result) with state := none, output := out}) :
6379:     (∀ v < t, ((clA5HostTM M K hk).tm.runFrom
6380:       {Cfg.ofWords (input := x) (clA5HostEntry M i) (stateWord K arg) with output := pre} v).state
6381:         ≠ some (.inl ())) ∧
6382:     (clA5HostTM M K hk).tm.runFrom
6383:       {Cfg.ofWords (input := x) (clA5HostEntry M i) (stateWord K arg) with output := pre} t =
6384:       {Cfg.ofWords (clA5HostRet M i) (stateWord K result) with output := pre ++ out} := by
6385:   let c := Cfg.ofWords (input := x) (M i).tm.q₀ (stateWord (M i).k arg)
6386:   let emb : (M i).State → CLA5HostState M := fun s => .inr ⟨i, s⟩
6387:   have hinit : emitCfg emb (clA5HostRet M i) pre (clA5PadCfg (K := K) c) =
6388:       {Cfg.ofWords (input := x) (clA5HostEntry M i) (stateWord K arg) with output := pre} := by
6389:     simpa [emb, c, clA5HostEntry] using
6390:       clA5Host_seam M K i hp x arg pre [] (M i).tm.q₀ (some (M i).tm.q₀)
6391:   have hrun (v : ℕ) (hv : v ≤ t) :
6392:       (clA5HostTM M K hk).tm.runFrom
6393:         {Cfg.ofWords (input := x) (clA5HostEntry M i) (stateWord K arg) with output := pre} v =
6394:         emitCfg emb (clA5HostRet M i) pre (clA5PadCfg ((M i).tm.runFrom c v)) := by
6395:     rw [← hinit]
6396:     rw [emit_run (clA5PadTM (M i) K (hk i)).tm (clA5HostTM M K hk).tm emb (clA5HostRet M i)
6397:       (by intros; rfl) pre _ v (by
6398:         intro u hu
6399:         rw [clA5Pad_run]
6400:         exact hg u (by omega))]
6401:     rw [clA5Pad_run]
6402:   constructor
6403:   · intro v hv
6404:     rw [hrun v (Nat.le_of_lt hv)]
6405:     have hl := hg v hv
6406:     cases hs : ((M i).tm.runFrom c v).state with
6407:     | none => exact False.elim (hl hs)
6408:     | some s => simp [emitCfg, clA5PadCfg, hs, emb]
6409:   · rw [hrun t (Nat.le_refl _), show (M i).tm.runFrom c t = _ from he]
6410:     exact clA5Host_seam M K i hp x result pre out q none
```

## TCSlib/Complexity/ClassNP/SAT.lean:4190–4203

```lean
4190: /-- Specialize a clean module to one call site in the finite host. -/
4191: private lemma satHost_clean (M : Fin 6 → FinTM Bool) (K : ℕ) (hk : ∀ i, (M i).k ≤ K)
4192:     (i : Fin 6) (f g : List Bool → List Bool) (B : ℕ → ℕ)
4193:     (h : SatClean (M i) f g B) (x arg pre : List Bool) :
4194:     ∃ t, 0 < t ∧ t ≤ B arg.length ∧
4195:       (∀ v < t, ((satHostTM M K hk).tm.runFrom
4196:         {Cfg.ofWords (input := x) (satHostEntry M i) (stateWord K arg) with output := pre} v).state
4197:           ≠ some (.inl ())) ∧
4198:       (satHostTM M K hk).tm.runFrom
4199:         {Cfg.ofWords (input := x) (satHostEntry M i) (stateWord K arg) with output := pre} t =
4200:         {Cfg.ofWords (satHostRet M i) (stateWord K (f arg)) with output := pre ++ g arg} := by
4201:   obtain ⟨t, hp, ht, hg, he⟩ := h.2 x arg
4202:   obtain ⟨hguard, hend⟩ := satHost_call M K hk i h.1 x arg (f arg) (g arg) pre (M i).tm.q₀ t hg he
4203:   exact ⟨t, hp, ht, hguard, hend⟩
```

## TCSlib/Complexity/CookLevin/Hardness.lean:6515–6528

```lean
6515: /-- Specialize a clean module to one call site in the finite host. -/
6516: private lemma clA5Host_clean (M : Fin 5 → FinTM Bool) (K : ℕ) (hk : ∀ i, (M i).k ≤ K)
6517:     (i : Fin 5) (f g : List Bool → List Bool) (B : ℕ → ℕ)
6518:     (h : CLA5Clean (M i) f g B) (x arg pre : List Bool) :
6519:     ∃ t, 0 < t ∧ t ≤ B arg.length ∧
6520:       (∀ v < t, ((clA5HostTM M K hk).tm.runFrom
6521:         {Cfg.ofWords (input := x) (clA5HostEntry M i) (stateWord K arg) with output := pre} v).state
6522:           ≠ some (.inl ())) ∧
6523:       (clA5HostTM M K hk).tm.runFrom
6524:         {Cfg.ofWords (input := x) (clA5HostEntry M i) (stateWord K arg) with output := pre} t =
6525:         {Cfg.ofWords (clA5HostRet M i) (stateWord K (f arg)) with output := pre ++ g arg} := by
6526:   obtain ⟨t, hp, ht, hg, he⟩ := h.2 x arg
6527:   obtain ⟨hguard, hend⟩ := clA5Host_call M K hk i h.1 x arg (f arg) (g arg) pre (M i).tm.q₀ t hg he
6528:   exact ⟨t, hp, ht, hguard, hend⟩
```
