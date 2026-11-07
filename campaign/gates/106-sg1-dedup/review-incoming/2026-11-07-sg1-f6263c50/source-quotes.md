## TCSlib/Complexity/ClassNP/SAT.lean:4074–4087

```lean
4074: /-- Joining two guarded segments preserves the first-return guard when the
4075: intermediate seam is also outside the anchor. -/
4076: private lemma sat_guard_add {k : ℕ} {S : Type} {x : List Bool}
4077:     (tm : MultiTapeTM k Bool S) (anchor : S) (c d : Cfg k Bool S x) (a b : ℕ)
4078:     (ha : ∀ v < a, (tm.runFrom c v).state ≠ some anchor)
4079:     (he : tm.runFrom c a = d)
4080:     (hb : ∀ v < b, (tm.runFrom d v).state ≠ some anchor) :
4081:     ∀ v < a + b, (tm.runFrom c v).state ≠ some anchor := by
4082:   intro v hv
4083:   by_cases h : v < a
4084:   · exact ha v h
4085:   · have hva : a ≤ v := by omega
4086:     rw [← Nat.add_sub_of_le hva, MultiTapeTM.runFrom_add, he]
4087:     exact hb (v - a) (by omega)
```

## TCSlib/Complexity/ClassNP/SAT.lean:4089–4095

```lean
4089: /-- Uniform clean-module contract: a first halt with a prescribed replacement
4090: word and emitted chunk, over every untouched native input. -/
4091: private def SatClean (M : FinTM Bool) (result emit : List Bool → List Bool) (B : ℕ → ℕ) : Prop :=
4092:   0 < M.k ∧ ∀ x arg : List Bool, ∃ t, 0 < t ∧ t ≤ B arg.length ∧
4093:     (∀ v < t, ¬(M.tm.runFrom (Cfg.ofWords (input := x) M.tm.q₀ (stateWord M.k arg)) v).Halted) ∧
4094:     M.tm.runFrom (Cfg.ofWords (input := x) M.tm.q₀ (stateWord M.k arg)) t =
4095:       {Cfg.ofWords M.tm.q₀ (stateWord M.k (result arg)) with state := none, output := emit arg}
```

## TCSlib/Complexity/ClassNP/SAT.lean:3906–3914

```lean
3906: /-- Convert a first-positive-exit module into a halting source for `emit_run`.
3907: The Boolean release flag ensures even an entry equal to exit executes once. -/
3908: private def satStopTM (C : FinTM Bool) (entry exit : C.State) : FinTM Bool where
3909:   k := C.k
3910:   State := Bool × C.State
3911:   tm := { q₀ := (false, entry)
3912:           tr := fun q inp work =>
3913:             if q.1 = true ∧ q.2 = exit then FinTM.controlAction 0 none
3914:             else {C.tm.tr q.2 inp work with state := (C.tm.tr q.2 inp work).state.map (true, ·)} }
```

## TCSlib/Complexity/ClassNP/SAT.lean:3855–3860

```lean
3855: /-- Configuration embedding for the shared bank; the padding is genuinely blank. -/
3856: private def satPadCfg {k K : ℕ} {S : Type} {x : List Bool}
3857:     (c : Cfg k Bool S x) : Cfg K Bool S x :=
3858:   ⟨c.state, c.inputPos,
3859:     fun i => if h : i.val < k then c.workTapes ⟨i.val, h⟩ else fun _ => none,
3860:     fun i => if h : i.val < k then c.workTapePos ⟨i.val, h⟩ else 0, c.output⟩
```

## TCSlib/Complexity/ClassNP/SAT.lean:2774–2785

```lean
2774: /-- Finite one-way transducer for local word operations used by round-field
2775: assembly. It uses no work tapes and always halts at the right boundary. -/
2776: private def satMapTM {S : Type} [Fintype S] [DecidableEq S]
2777:     (next : S → Bool → S) (emit : S → Bool → Option Bool)
2778:     (finish : S → Option Bool) (start : S) : FinTM Bool where
2779:   k := 0
2780:   State := S
2781:   tm := {
2782:     q₀ := start
2783:     tr := fun q inp _ => match inp with
2784:       | some b => ⟨.pos, Fin.elim0, emit q b, some (next q b)⟩
2785:       | none => ⟨0, Fin.elim0, finish q, none⟩ }
```

## TCSlib/Complexity/ClassNP/SAT.lean:3842–3845

```lean
3842: /-- Pad a callable module into a shared bank, keeping unused tapes stationary. -/
3843: private def satPadAction {k K : ℕ} {S : Type} (a : Action k Bool S) : Action K Bool S :=
3844:   ⟨a.inputTape, fun i => if h : i.val < k then a.workTapes ⟨i.val, h⟩ else (none, 0),
3845:     a.output, a.state⟩
```

## TCSlib/Complexity/ClassNP/SAT.lean:3916–3919

```lean
3916: /-- Release-flag embedding preserves all physical fields of a call. -/
3917: private def satStopCfg {k : ℕ} {S : Type} {x : List Bool}
3918:     (b : Bool) (c : Cfg k Bool S x) : Cfg k Bool (Bool × S) x :=
3919:   ⟨c.state.map (b, ·), c.inputPos, c.workTapes, c.workTapePos, c.output⟩
```

## TCSlib/Complexity/ClassNP/SAT.lean:4117–4136

```lean
4117: /-- The bridge overhead is bounded by one monomial of degree one higher.
4118: **Proof sketch.** Output length is bounded by source time; `n+1` and both
4119: source-time terms fit the larger power. The last unit pays for stopping. -/
4120: private lemma sat_bridge_bound (c A d n len : ℕ) (hlen : len ≤ A * (n + 1) ^ d) :
4121:     c * (A * (n + 1) ^ d + n + len + 1) + 1 ≤
4122:       (c * (2 * A + 1) + 1) * (n + 1) ^ (d + 1) := by
4123:   have hd := Nat.mul_le_mul_left A
4124:     (Nat.pow_le_pow_right (Nat.succ_pos n) (show d ≤ d + 1 by omega))
4125:   simp only [Nat.succ_eq_add_one] at hd
4126:   have hn : n + 1 ≤ (n + 1) ^ (d + 1) := by
4127:     simpa using Nat.pow_le_pow_right (Nat.succ_pos n) (show 1 ≤ d + 1 by omega)
4128:   have h1 : 1 ≤ (n + 1) ^ (d + 1) := by omega
4129:   calc
4130:     _ ≤ c * ((2 * A + 1) * (n + 1) ^ (d + 1)) + 1 := by
4131:       apply Nat.add_le_add_right
4132:       apply Nat.mul_le_mul_left
4133:       simp only [Nat.add_mul, Nat.one_mul, Nat.mul_assoc, two_mul]
4134:       omega
4135:     _ ≤ c * ((2 * A + 1) * (n + 1) ^ (d + 1)) + (n + 1) ^ (d + 1) := Nat.add_le_add_left h1 _
4136:     _ = _ := by ring
```

## TCSlib/Complexity/CookLevin/Hardness.lean:6412–6425

```lean
6412: /-- Joining two guarded segments preserves the first-return guard when the
6413: intermediate seam is also outside the anchor. -/
6414: private lemma clA5_guard_add {k : ℕ} {S : Type} {x : List Bool}
6415:     (tm : MultiTapeTM k Bool S) (anchor : S) (c d : Cfg k Bool S x) (a b : ℕ)
6416:     (ha : ∀ v < a, (tm.runFrom c v).state ≠ some anchor)
6417:     (he : tm.runFrom c a = d)
6418:     (hb : ∀ v < b, (tm.runFrom d v).state ≠ some anchor) :
6419:     ∀ v < a + b, (tm.runFrom c v).state ≠ some anchor := by
6420:   intro v hv
6421:   by_cases h : v < a
6422:   · exact ha v h
6423:   · have hva : a ≤ v := by omega
6424:     rw [← Nat.add_sub_of_le hva, MultiTapeTM.runFrom_add, he]
6425:     exact hb (v - a) (by omega)
```

## TCSlib/Complexity/CookLevin/Hardness.lean:6427–6433

```lean
6427: /-- Uniform clean-module contract: a first halt with a prescribed replacement
6428: word and emitted chunk, over every untouched native input. -/
6429: private def CLA5Clean (M : FinTM Bool) (result emit : List Bool → List Bool) (B : ℕ → ℕ) : Prop :=
6430:   0 < M.k ∧ ∀ x arg : List Bool, ∃ t, 0 < t ∧ t ≤ B arg.length ∧
6431:     (∀ v < t, ¬(M.tm.runFrom (Cfg.ofWords (input := x) M.tm.q₀ (stateWord M.k arg)) v).Halted) ∧
6432:     M.tm.runFrom (Cfg.ofWords (input := x) M.tm.q₀ (stateWord M.k arg)) t =
6433:       {Cfg.ofWords M.tm.q₀ (stateWord M.k (result arg)) with state := none, output := emit arg}
```

## TCSlib/Complexity/CookLevin/Hardness.lean:6245–6253

```lean
6245: /-- Convert a first-positive-exit module into a halting source for `emit_run`.
6246: The Boolean release flag ensures even an entry equal to exit executes once. -/
6247: private def clA5StopTM (C : FinTM Bool) (entry exit : C.State) : FinTM Bool where
6248:   k := C.k
6249:   State := Bool × C.State
6250:   tm := { q₀ := (false, entry)
6251:           tr := fun q inp work =>
6252:             if q.1 = true ∧ q.2 = exit then FinTM.controlAction 0 none
6253:             else {C.tm.tr q.2 inp work with state := (C.tm.tr q.2 inp work).state.map (true, ·)} }
```

## TCSlib/Complexity/CookLevin/Hardness.lean:6194–6199

```lean
6194: /-- Configuration embedding for the shared bank; the padding is genuinely blank. -/
6195: private def clA5PadCfg {k K : ℕ} {S : Type} {x : List Bool}
6196:     (c : Cfg k Bool S x) : Cfg K Bool S x :=
6197:   ⟨c.state, c.inputPos,
6198:     fun i => if h : i.val < k then c.workTapes ⟨i.val, h⟩ else fun _ => none,
6199:     fun i => if h : i.val < k then c.workTapePos ⟨i.val, h⟩ else 0, c.output⟩
```

## TCSlib/Complexity/CookLevin/Hardness.lean:6719–6730

```lean
6719: /-- Finite one-way transducer for local word operations used by round-field
6720: assembly. It uses no work tapes and always halts at the right boundary. -/
6721: private def clA5MapTM {S : Type} [Fintype S] [DecidableEq S]
6722:     (next : S → Bool → S) (emit : S → Bool → Option Bool)
6723:     (finish : S → Option Bool) (start : S) : FinTM Bool where
6724:   k := 0
6725:   State := S
6726:   tm := {
6727:     q₀ := start
6728:     tr := fun q inp _ => match inp with
6729:       | some b => ⟨.pos, Fin.elim0, emit q b, some (next q b)⟩
6730:       | none => ⟨0, Fin.elim0, finish q, none⟩ }
```

## TCSlib/Complexity/CookLevin/Hardness.lean:6181–6184

```lean
6181: /-- Pad a callable module into a shared bank, keeping unused tapes stationary. -/
6182: private def clA5PadAction {k K : ℕ} {S : Type} (a : Action k Bool S) : Action K Bool S :=
6183:   ⟨a.inputTape, fun i => if h : i.val < k then a.workTapes ⟨i.val, h⟩ else (none, 0),
6184:     a.output, a.state⟩
```

## TCSlib/Complexity/CookLevin/Hardness.lean:6255–6258

```lean
6255: /-- Release-flag embedding preserves all physical fields of a call. -/
6256: private def clA5StopCfg {k : ℕ} {S : Type} {x : List Bool}
6257:     (b : Bool) (c : Cfg k Bool S x) : Cfg k Bool (Bool × S) x :=
6258:   ⟨c.state.map (b, ·), c.inputPos, c.workTapes, c.workTapePos, c.output⟩
```

## TCSlib/Complexity/CookLevin/Hardness.lean:6455–6474

```lean
6455: /-- The bridge overhead is bounded by one monomial of degree one higher.
6456: **Proof sketch.** Output length is bounded by source time; `n+1` and both
6457: source-time terms fit the larger power. The last unit pays for stopping. -/
6458: private lemma clA5_bridge_bound (c A d n len : ℕ) (hlen : len ≤ A * (n + 1) ^ d) :
6459:     c * (A * (n + 1) ^ d + n + len + 1) + 1 ≤
6460:       (c * (2 * A + 1) + 1) * (n + 1) ^ (d + 1) := by
6461:   have hd := Nat.mul_le_mul_left A
6462:     (Nat.pow_le_pow_right (Nat.succ_pos n) (show d ≤ d + 1 by omega))
6463:   simp only [Nat.succ_eq_add_one] at hd
6464:   have hn : n + 1 ≤ (n + 1) ^ (d + 1) := by
6465:     simpa using Nat.pow_le_pow_right (Nat.succ_pos n) (show 1 ≤ d + 1 by omega)
6466:   have h1 : 1 ≤ (n + 1) ^ (d + 1) := by omega
6467:   calc
6468:     _ ≤ c * ((2 * A + 1) * (n + 1) ^ (d + 1)) + 1 := by
6469:       apply Nat.add_le_add_right
6470:       apply Nat.mul_le_mul_left
6471:       simp only [Nat.add_mul, Nat.one_mul, Nat.mul_assoc, two_mul]
6472:       omega
6473:     _ ≤ c * ((2 * A + 1) * (n + 1) ^ (d + 1)) + (n + 1) ^ (d + 1) := Nat.add_le_add_left h1 _
6474:     _ = _ := by ring
```

## TCSlib/Complexity/TuringMachine/Build/Contract/Basic.lean:459–478

```lean
459: /-- **Same-machine concatenation** (the `recordRun_trans` pattern): segments sharing the forbidden
460: set and the relation concatenate, with lengths adding and **no dispatch step**.
461: 
462: **Proof sketch.** Split a time at the first length `t`. Before it, use the first segment; after
463: it, the run is the second segment's from `b` (`Turing.MultiTapeTM.runFrom_add`). -/
464: theorem trans {a b c : Cfg k Γ S x} {t v : ℕ} (h : Segment M F P a b t)
465:     (g : Segment M F P b c v) : Segment M F P a c (t + v) := by
466:   refine ⟨by rw [MultiTapeTM.runFrom_add, h.1, g.1], ?_, ?_⟩
467:   · intro u hu
468:     by_cases hut : u < t
469:     · exact h.2.1 u hut
470:     · have he : u = t + (u - t) := by omega
471:       rw [he, MultiTapeTM.runFrom_add, h.1]
472:       exact g.2.1 _ (by omega)
473:   · intro u hu
474:     by_cases hut : u ≤ t
475:     · exact h.2.2 u hut
476:     · have he : u = t + (u - t) := by omega
477:       rw [he, MultiTapeTM.runFrom_add, h.1]
478:       exact g.2.2 _ (by omega)
```

## TCSlib/Complexity/TuringMachine/Build/Contract/Basic.lean:443–447

```lean
443: /-- The empty segment: zero steps, with the start's head vector satisfying the relation. -/
444: theorem zero {a : Cfg k Γ S x} (h : P a.workTapePos) : Segment M F P a a 0 :=
445:   ⟨rfl, fun _ hu => absurd hu (Nat.not_lt_zero _), fun u hu => by
446:     obtain rfl : u = 0 := Nat.le_zero.mp hu
447:     exact h⟩
```

## TCSlib/Complexity/TuringMachine/Build/Contract/Basic.lean:497–500

```lean
497: /-- Weakening: a smaller forbidden set and a weaker relation. -/
498: theorem mono {F' : Set (Option S)} {P' : (Fin k → ℤ) → Prop} {a b : Cfg k Γ S x} {t : ℕ}
499:     (h : Segment M F P a b t) (hF : F' ⊆ F) (hP : ∀ p, P p → P' p) : Segment M F' P' a b t :=
500:   ⟨h.1, fun u hu hm => h.2.1 u hu (hF hm), fun u hu => hP _ (h.2.2 u hu)⟩
```

## TCSlib/Complexity/TuringMachine/Build/Contract/Basic.lean:429–436

```lean
429: /-- `Turing.Segment M F P a b t` holds exactly when `M.runFrom a t = b`, no state at a time
430: `u < t` lies in `F`, and the head vector satisfies `P` at every time `u ≤ t` (the definition as
431: a lemma). -/
432: theorem segment_iff {S : Type} {x : List Γ} (M : MultiTapeTM k Γ S) (F : Set (Option S))
433:     (P : (Fin k → ℤ) → Prop) (a b : Cfg k Γ S x) (t : ℕ) :
434:     Segment M F P a b t ↔ M.runFrom a t = b ∧ (∀ u < t, (M.runFrom a u).state ∉ F) ∧
435:       ∀ u ≤ t, P (M.runFrom a u).workTapePos :=
436:   Iff.rfl
```

## TCSlib/Complexity/TuringMachine/Build/Contract/Basic.lean:421–427

```lean
421: /-- **A segment**: the run of `M` from `a` reaches `b` after exactly `t` steps, no state at a
422: time before `t` lies in the forbidden set `F`, and the head vector satisfies `P` at every time up
423: to `t`. Nothing is said about the endpoint's state. -/
424: def Segment {S : Type} {x : List Γ} (M : MultiTapeTM k Γ S) (F : Set (Option S))
425:     (P : (Fin k → ℤ) → Prop) (a b : Cfg k Γ S x) (t : ℕ) : Prop :=
426:   M.runFrom a t = b ∧ (∀ u < t, (M.runFrom a u).state ∉ F) ∧
427:     ∀ u ≤ t, P (M.runFrom a u).workTapePos
```

## TCSlib/Complexity/ClassNP/Tautology.lean:1281–1286

```lean
1281: /-- A segment records its exact endpoint and excludes the anchor strictly
1282: before that endpoint. It is used only after the initial release transition. -/
1283: private def tautDualSegment {x : List Bool}
1284:     (c d : Cfg 0 Bool TautDualControl x) (t : ℕ) : Prop :=
1285:   tautDualTM.tm.runFrom c t = d ∧
1286:     ∀ j < t, (tautDualTM.tm.runFrom c j).state ≠ some .anchor
```

## TCSlib/Complexity/ClassNP/Tautology.lean:1288–1296

```lean
1288: /-- `tautDualSegment` is the segment layer at the transducer's parameters: the segment
1289: (`Turing.Segment`) of `tautDualTM.tm` with the anchor forbidden and no head relation.
1290: Consecutive segments compose, without hiding an earlier anchor visit, by
1291: `Turing.Segment.trans` through this bridge. -/
1292: private lemma tautDualSegment_iff_segment {x : List Bool}
1293:     (c d : Cfg 0 Bool TautDualControl x) (t : ℕ) :
1294:     tautDualSegment c d t ↔ Segment tautDualTM.tm {some .anchor} (fun _ => True) c d t := by
1295:   rw [Turing.segment_iff]
1296:   exact ⟨fun h => ⟨h.1, h.2, fun _ _ => trivial⟩, fun h => ⟨h.1, h.2.1⟩⟩
```

## TCSlib/Complexity/TuringMachine/Build/CounterLoop.lean:818–828

```lean
818: /-- Common trajectory data for a finite host segment, with a chosen set of
819: permitted body-head vectors. -/
820: private def counterSpan {k : ℕ} {Γ S : Type} {x : List Γ}
821:     (H : MultiTapeTM (k + 1) Γ (CounterLoopState S))
822:     (z : Cfg (k + 1) Γ (CounterLoopState S) x) (t : ℕ) (cp : ℤ) (width : ℕ)
823:     (R : (Fin k → ℤ) → Prop) : Prop :=
824:   (∀ u < t, (H.runFrom z u).state ≠ some .done ∧
825:     (H.runFrom z u).state ≠ some .escape) ∧
826:   (∀ u ≤ t, (H.runFrom z u).workTapePos (Fin.last k) ∈
827:     Finset.Icc (cp - 1) (cp + (width : ℤ))) ∧
828:   (∀ u ≤ t, R (fun j => (H.runFrom z u).workTapePos j.castSucc))
```

## TCSlib/Complexity/TuringMachine/Build/CounterLoop.lean:830–848

```lean
830: /-- `counterSpan` is the segment layer at the counter loop's parameters: the segment
831: (`Turing.Segment`) from `z` to its run endpoint over both exits, whose head relation puts the
832: counter head in its interval and the body heads in `R`. Concatenation and weakening are
833: `Turing.Segment.trans` and `Turing.Segment.mono` through this bridge. -/
834: private lemma counterSpan_iff_segment {k : ℕ} {Γ S : Type} {x : List Γ}
835:     (H : MultiTapeTM (k + 1) Γ (CounterLoopState S))
836:     (z : Cfg (k + 1) Γ (CounterLoopState S) x) (t : ℕ) (cp : ℤ) (width : ℕ)
837:     (R : (Fin k → ℤ) → Prop) :
838:     counterSpan H z t cp width R ↔
839:       Segment H {some .done, some .escape}
840:         (fun p => p (Fin.last k) ∈ Finset.Icc (cp - 1) (cp + (width : ℤ)) ∧
841:           R fun j => p j.castSucc)
842:         z (H.runFrom z t) t := by
843:   rw [Turing.segment_iff]
844:   exact ⟨fun ⟨hc, hh, hr⟩ => ⟨rfl, fun u hu hm => Or.elim hm (hc u hu).1 (hc u hu).2,
845:       fun u hu => ⟨hh u hu, hr u hu⟩⟩,
846:     fun ⟨_, hc, hp⟩ =>
847:       ⟨fun u hu => ⟨fun h => hc u hu (Or.inl h), fun h => hc u hu (Or.inr h)⟩,
848:         fun u hu => (hp u hu).1, fun u hu => (hp u hu).2⟩⟩
```

## TCSlib/Complexity/TuringMachine/Robustness/SingleTape.lean:1181–1186

```lean
1181: /-- A finite run together with containment at all its prefixes. The endpoints
1182: are physical coordinates, and both are counted. -/
1183: private def DGSpan {A Q : Type} {x : List A} (tm : MultiTapeTM 1 A Q)
1184:     (c d : Cfg 1 A Q x) (t : ℕ) (lo hi : ℤ) : Prop :=
1185:   tm.runFrom c t = d ∧ ∀ u ≤ t,
1186:     lo ≤ (tm.runFrom c u).workTapePos 0 ∧ (tm.runFrom c u).workTapePos 0 ≤ hi
```

## TCSlib/Complexity/TuringMachine/Robustness/SingleTape.lean:1188–1196

```lean
1188: /-- `DGSpan` is the segment layer with nothing forbidden: the segment (`Turing.Segment`) of
1189: `tm` whose head relation keeps the one work head in `[lo, hi]`. Concatenating contained runs,
1190: which preserves containment at every physical time, is `Turing.Segment.trans` through this
1191: bridge. -/
1192: private lemma dgSpan_iff_segment {A Q : Type} {x : List A} (tm : MultiTapeTM 1 A Q)
1193:     (c d : Cfg 1 A Q x) (t : ℕ) (lo hi : ℤ) :
1194:     DGSpan tm c d t lo hi ↔ Segment tm ∅ (fun p => lo ≤ p 0 ∧ p 0 ≤ hi) c d t := by
1195:   rw [Turing.segment_iff]
1196:   exact ⟨fun h => ⟨h.1, fun _ _ hm => hm, h.2⟩, fun h => ⟨h.1, h.2.2⟩⟩
```
