# The rfl controls for the 82 sealed definitions (one per definition), and the [-simp] control.
CTL = {
'Turing.Action.apply': '''example {k : ℕ} {S Γ : Type} {x : List Γ} (a : Action k Γ S) (c : Cfg k Γ S x) :
    (a.apply c).state = a.state := rfl''',
'Turing.Action.mapState': '''example {k : ℕ} {Γ S S' : Type} (f : S → S') (a : Action k Γ S) :
    (a.mapState f).output = a.output := rfl''',
'Turing.Cfg.SameOutside': '''example {k : ℕ} {Γ S S' : Type} {x : List Γ} (fp : Fin k → Set ℤ) (d : Cfg k Γ S x)
    (d' : Cfg k Γ S' x) :
    Cfg.SameOutside fp d d' = ∀ j, ∀ q ∉ fp j, d'.workTapes j q = d.workTapes j q := rfl''',
'Turing.Cfg.bindState': '''example {k : ℕ} {Γ S S' : Type} {x : List Γ} (d : Cfg k Γ S x) (f : S → Option S') :
    (d.bindState f).output = d.output := rfl''',
'Turing.Cfg.inputSymbol': '''example : Cfg.inputSymbol
    (⟨none, 0, fun _ _ => none, fun _ => 0, []⟩ : Cfg 0 Bool Unit [true]) = none := rfl''',
'Turing.Cfg.mapState': '''example {k : ℕ} {Γ S S' : Type} {x : List Γ} (f : S → S') (c : Cfg k Γ S x) :
    (c.mapState f).workTapes = c.workTapes := rfl''',
'Turing.Cfg.workTapeSymbols': '''example {k : ℕ} {S Γ : Type} {x : List Γ} (c : Cfg k Γ S x) (i : Fin k) :
    c.workTapeSymbols i = c.workTapes i (c.workTapePos i) := rfl''',
'Turing.Contract._sizeOf_inst': '''example {k : ℕ} {Γ S ι : Type} {x : List Γ} [SizeOf Γ] [SizeOf S] [SizeOf ι]
    {M : MultiTapeTM k Γ S} {e : S} {X : Set (Option S)} [∀ a, SizeOf (X a)]
    (C : Contract M e X ι x) :
    @SizeOf.sizeOf _ (Contract._sizeOf_inst M e X ι x) C = C._sizeOf_1 := rfl''',
'Turing.Contract._sizeOf_1': '''example {k : ℕ} {Γ S ι : Type} {x : List Γ} [SizeOf Γ] [SizeOf S] [SizeOf ι]
    {M : MultiTapeTM k Γ S} {e : S} {X : Set (Option S)} [∀ a, SizeOf (X a)]
    (C : Contract M e X ι x) : C._sizeOf_1 = 1 := by
  cases C
  rfl''',
'Turing.Contract.branch': '''example {k : ℕ} {Γ S₀ S₁ S₂ ι κ₁ κ₂ : Type} [DecidableEq S₀] [DecidableEq S₁] {x : List Γ}
    {M₀ : MultiTapeTM k Γ S₀} {M₁ : MultiTapeTM k Γ S₁} {M₂ : MultiTapeTM k Γ S₂}
    {entry₀ e₁ e₂ : S₀} {entry₁ : S₁} {entry₂ : S₂} {X₁ : Set (Option S₁)} {X₂ : Set (Option S₂)}
    (he : e₁ ≠ e₂) (C₀ : Contract M₀ entry₀ {some e₁, some e₂} ι x) (C₁ : Contract M₁ entry₁ X₁ κ₁ x)
    (C₂ : Contract M₂ entry₂ X₂ κ₂ x) (l₁ : ι → κ₁) (l₂ : ι → κ₂)
    (h₁ : ∀ i (d : Cfg k Γ S₀ x), d.state = some entry₀ → C₀.pre i d →
      (C₀.post i d).state = some e₁ → C₁.pre (l₁ i) ((C₀.post i d).mapState fun _ => entry₁))
    (h₂ : ∀ i (d : Cfg k Γ S₀ x), d.state = some entry₀ → C₀.pre i d →
      (C₀.post i d).state = some e₂ → C₂.pre (l₂ i) ((C₀.post i d).mapState fun _ => entry₂)) :
    (Contract.branch he C₀ C₁ C₂ l₁ l₂ h₁ h₂).pre =
      fun i d => C₀.pre i (d.mapState fun _ => entry₀) := rfl''',
'Turing.Contract.inPhase': '''example {k : ℕ} {Γ I ι : Type} {Ph : I → Type} {x : List Γ}
    (Mf : (i : I) → MultiTapeTM k Γ (Ph i)) (q0 : (i : I) × Ph i)
    (red : (i : I) → Ph i → Option ((i : I) × Ph i)) (p : I) {s₀ : Ph p} {X : Set (Option (Ph p))}
    (C : Contract (Mf p) s₀ X ι x) (hnone : none ∉ X)
    (hred : ∀ s : Ph p, some s ∉ X → red p s = none)
    (hsome : ∀ s : Ph p, some s ∈ X → ∃ q, red p s = some q ∧ q.fst ≠ p) :
    (Contract.inPhase Mf q0 red p C hnone hred hsome).time =
      fun i d => C.time i (d.mapState fun _ => s₀) + 1 := rfl''',
'Turing.Contract.lockstep': '''example {k k' : ℕ} {Γ Γ' S S' ι : Type} {x : List Γ} {x' : List Γ'}
    {M : MultiTapeTM k Γ S} {N : MultiTapeTM k' Γ' S'} {enc : Cfg k Γ S x → Cfg k' Γ' S' x'}
    {cost : Cfg k Γ S x → ℕ} {entry : S} {X : Set (Option S)} {X' : Set (Option S')}
    (C : Contract M entry X ι x) (L : Lockstep M N enc cost X X') (entry' : S')
    (blo bhi : Cfg k Γ S x → Fin k' → ℤ)
    (hbox : ∀ (c : Cfg k Γ S x) (v : ℕ), (v = 0 ∨ (c.state ∉ X ∧ v ≤ cost c)) → ∀ j,
      (N.runFrom (enc c) v).workTapePos j ∈ Finset.Icc (blo c j) (bhi c j)) :
    (C.lockstep L entry' blo bhi hbox).post = fun p _ => enc (C.post p.1 p.2) := rfl''',
'Turing.Contract.ofSegment': '''example {k : ℕ} {Γ S ι : Type} {x : List Γ} {M : MultiTapeTM k Γ S} {entry : S}
    {exits : Set (Option S)} (pre : ι → Cfg k Γ S x → Prop) (time : ι → Cfg k Γ S x → ℕ)
    (post : ι → Cfg k Γ S x → Cfg k Γ S x) (lo hi : ι → Cfg k Γ S x → Fin k → ℤ)
    (seg : ∀ i (d : Cfg k Γ S x), d.state = some entry → pre i d →
      Segment M exits (HeadBox (lo i d) (hi i d)) d (post i d) (time i d))
    (em : ∀ i (d : Cfg k Γ S x), d.state = some entry → pre i d → (post i d).state ∈ exits) :
    (Contract.ofSegment pre time post lo hi seg em).time = time := rfl''',
'Turing.Contract.seq': '''example {k : ℕ} {Γ S₁ S₂ ι κ : Type} [DecidableEq S₁] {x : List Γ}
    {M₁ : MultiTapeTM k Γ S₁} {M₂ : MultiTapeTM k Γ S₂} {entry₁ exit₁ : S₁} {entry₂ : S₂}
    {X₂ : Set (Option S₂)} (C₁ : Contract M₁ entry₁ {some exit₁} ι x) (C₂ : Contract M₂ entry₂ X₂ κ x)
    (link : ι → κ)
    (hlink : ∀ i (d : Cfg k Γ S₁ x), d.state = some entry₁ → C₁.pre i d →
      C₂.pre (link i) ((C₁.post i d).mapState fun _ => entry₂)) :
    (C₁.seq C₂ link hlink).pre = fun i d => C₁.pre i (d.mapState fun _ => entry₁) := rfl''',
'Turing.FinTM.bufferTape': '''example : FinTM.bufferTape [true] 0 = some true := rfl''',
'Turing.HeadBox': '''example {k : ℕ} (lo hi p : Fin k → ℤ) :
    HeadBox lo hi p = ∀ j, p j ∈ Finset.Icc (lo j) (hi j) := rfl''',
'Turing.MultiTapeTM.runFrom': '''example {k : ℕ} {S Γ : Type} {x : List Γ} (tm : MultiTapeTM k Γ S) (c : Cfg k Γ S x) :
    tm.runFrom c 1 = tm.step c := rfl''',
'Turing.MultiTapeTM.step': '''example {k : ℕ} {S Γ : Type} {x : List Γ} (tm : MultiTapeTM k Γ S) (c : Cfg k Γ S x) :
    tm.step { c with state := none } = { c with state := none } := rfl''',
'Turing.Round': '''example {k : ℕ} {Γ S : Type} {x : List Γ} (M : MultiTapeTM k Γ S) (a : S) (E : Set (Option S))
    (P : (Fin k → ℤ) → Prop) (c c' : Cfg k Γ S x) (t : ℕ) :
    Round M a E P c c' t = (c.state = some a ∧ 0 < t ∧ M.runFrom c t = c' ∧
      c'.state ∈ insert (some a) E ∧
      (∀ u, 0 < u → u < t → (M.runFrom c u).state ∉ roundStop a E) ∧
      ∀ u ≤ t, P (M.runFrom c u).workTapePos) := rfl''',
'Turing.Segment': '''example {k : ℕ} {S : Type} {x : List Bool} (M : MultiTapeTM k Bool S) (F : Set (Option S))
    (P : (Fin k → ℤ) → Prop) (a b : Cfg k Bool S x) (t : ℕ) : Segment M F P a b t =
      (M.runFrom a t = b ∧ (∀ u < t, (M.runFrom a u).state ∉ F) ∧
        ∀ u ≤ t, P (M.runFrom a u).workTapePos) := rfl''',
'Turing.ZoneContents.extend': '''example {ℓ : ℕ} (z : ZoneContents ℓ) : z.extend.home = z.home := rfl''',
'Turing.ZoneContents.swap': '''example {ℓ : ℕ} (z : ZoneContents ℓ) : z.swap.left = z.right := rfl''',
'Turing.ZoneContents.words': '''example {ℓ : ℕ} (z : ZoneContents ℓ) : z.words true = z.right := rfl''',
'Turing.clearTM': '''example {k : ℕ} (i : Fin k) : (clearTM (Symbol := Bool) k i).q₀ = .sweep := rfl''',
'Turing.clearTM_contract': '''example {k : ℕ} {Γ : Type} (i : Fin k) (x : List Γ) :
    (clearTM_contract i x).time = fun w _ => 2 * w.length + 2 := rfl''',
'Turing.copyMapTM': '''example {k : ℕ} (src dst : Fin k) :
    (copyMapTM (Symbol := Bool) k src dst (fun _ => ()) (fun _ _ => true)).q₀ = .sweep := rfl''',
'Turing.copyMapTM_contract': '''example {k : ℕ} {Γ Δ : Type} (src dst : Fin k) (hne : src ≠ dst) (extract : Γ → Δ)
    (merge : Option Γ → Δ → Γ) (x : List Γ) :
    (copyMapTM_contract src dst hne extract merge x).time = fun w _ => 2 * w.length + 2 := rfl''',
'Turing.fieldOffset': '''example : fieldOffset ([[true], [false, true]] : List (List Bool)) 1 = 2 := rfl''',
'Turing.fieldsTape': '''example (fs : List (List Bool)) (z : ℤ) :
    fieldsTape fs z = if 0 ≤ z then ((joinFields fs)[z.toNat]?).join else none := rfl''',
'Turing.framedContract': '''example {k : ℕ} {Γ S ι : Type} (M : MultiTapeTM k Γ S) (entry done : S) (x : List Γ)
    (pre : ι → Cfg k Γ S x → Prop) (time : ι → Cfg k Γ S x → ℕ)
    (post : ι → Cfg k Γ S x → Cfg k Γ S x) (touched : Fin k → Prop) [DecidablePred touched]
    (lo hi : ι → Cfg k Γ S x → Fin k → ℤ) (hpost : ∀ i d, (post i d).state = some done)
    (hrun : ∀ i (d : Cfg k Γ S x), d.state = some entry → pre i d →
      M.runFrom d (time i d) = post i d ∧ (∀ t < time i d, (M.runFrom d t).state ≠ some done) ∧
        ∀ j, ∀ t ≤ time i d, if touched j then
          (M.runFrom d t).workTapePos j ∈ Finset.Icc (lo i d j) (hi i d j)
        else (M.runFrom d t).workTapePos j = d.workTapePos j) :
    (framedContract M entry done x pre time post touched lo hi hpost hrun).time = time := rfl''',
'Turing.inputMoveAction': '''example {k : ℕ} {Γ S : Type} (inp : SignType) (q : S) :
    (inputMoveAction (k := k) (Symbol := Γ) inp q).state = some q := rfl''',
'Turing.instDecidableEqSeekPhase': '''example : (if SeekPhase.run = SeekPhase.done then 1 else 0) = 0 := rfl''',
'Turing.instDecidableEqSweepPhase': '''example : (if SweepPhase.sweep = SweepPhase.done then 1 else 0) = 0 := rfl''',
'Turing.instFintypeSeekPhase': '''example : (Finset.univ : Finset SeekPhase).card = 4 := rfl''',
'Turing.instFintypeSweepPhase': '''example : (Finset.univ : Finset SweepPhase).card = 3 := rfl''',
'Turing.SeekPhase.enumList': '''example : SeekPhase.enumList.length = 4 := rfl''',
'Turing.SweepPhase.enumList': '''example : SweepPhase.enumList.length = 3 := rfl''',
'Turing.joinFields': '''example (fs : List (List Bool)) :
    joinFields fs = List.intercalate [none] (fs.map (List.map some)) := rfl''',
'Turing.moveInputPos': '''example : (moveInputPos (0 : Fin 3) .pos).val = 1 := rfl''',
'Turing.phaseHostTM': '''example {k : ℕ} {I : Type} {Ph : I → Type} (M : (i : I) → MultiTapeTM k Bool (Ph i))
    (q0 : Σ i, Ph i) (red : (i : I) → Ph i → Option (Σ i, Ph i)) :
    (phaseHostTM M q0 red).q₀ = q0 := rfl''',
'Turing.roundOrbit': '''example {k : ℕ} {Γ S : Type} {x : List Γ} (M : MultiTapeTM k Γ S) (τ : Cfg k Γ S x → ℕ)
    (c : Cfg k Γ S x) : roundOrbit M τ c 0 = c := rfl''',
'Turing.roundStop': '''example {S : Type} (a : S) (E : Set (Option S)) :
    roundStop a E = insert none (insert (some a) E) := rfl''',
'Turing.seamCompTM': '''example {k : ℕ} {S₁ S₂ : Type} [DecidableEq S₁] (M₁ : MultiTapeTM k Bool S₁) (e : S₁)
    (M₂ : MultiTapeTM k Bool S₂) (e₂ : S₂) : (seamCompTM M₁ e M₂ e₂).q₀ = Sum.inl M₁.q₀ := rfl''',
'Turing.seamCompTM₂': '''example {k : ℕ} {S₀ S₁ S₂ : Type} [DecidableEq S₀] [DecidableEq S₁]
    (M₀ : MultiTapeTM k Bool S₀) (e₁ e₂ : S₀) (M₁ : MultiTapeTM k Bool S₁) (n₁ : S₁)
    (M₂ : MultiTapeTM k Bool S₂) (n₂ : S₂) :
    seamCompTM₂ M₀ e₁ e₂ M₁ n₁ M₂ n₂ = seamCompTM (seamCompTM M₀ e₁ M₁ n₁) (Sum.inl e₂) M₂ n₂ :=
  rfl''',
'Turing.seekEndTM': '''example {k : ℕ} (i : Fin k) : (seekEndTM (Symbol := Bool) k i).q₀ = .run := rfl''',
'Turing.seekEndTM_contract': '''example {k : ℕ} {Γ : Type} (i : Fin k) (x : List Γ) :
    (seekEndTM_contract i x).time = fun ws _ => fieldOffset ws ws.length + 1 := rfl''',
'Turing.seekPost': '''example {k : ℕ} {Γ S : Type} {x : List Γ} (done : S) (i : Fin k) (p : ℤ) (d : Cfg k Γ S x) :
    (seekPost done i p d).state = some done := rfl''',
'Turing.seekStartTM': '''example {k : ℕ} (i : Fin k) : (seekStartTM (Symbol := Bool) k i).q₀ = .run := rfl''',
'Turing.seekStartTM_contract': '''example {k : ℕ} {Γ : Type} (i : Fin k) (x : List Γ) :
    (seekStartTM_contract i x).time = fun ws _ => fieldOffset ws ws.length + 4 := rfl''',
'Turing.skipBackTM': '''example {k : ℕ} (i : Fin k) : (skipBackTM (Symbol := Bool) k i).q₀ = .run := rfl''',
'Turing.skipBackTM_contract': '''example {k : ℕ} {Γ : Type} (i : Fin k) (x : List Γ) :
    (skipBackTM_contract i x).time = fun u _ => u.length + 3 := rfl''',
'Turing.skipTM': '''example {k : ℕ} (i : Fin k) : (skipTM (Symbol := Bool) k i).q₀ = .run := rfl''',
'Turing.skipTM_contract': '''example {k : ℕ} {Γ : Type} (i : Fin k) (x : List Γ) :
    (skipTM_contract i x).time = fun w _ => w.length + 1 := rfl''',
'Turing.sweepContract': '''example {k : ℕ} {Γ S : Type} (M : MultiTapeTM k Γ S) (entry done : S) (src : Fin k)
    (touched : Fin k → Prop) [DecidablePred touched] (x : List Γ)
    (post : List Γ → Cfg k Γ S x → Cfg k Γ S x) (hpost : ∀ w d, (post w d).state = some done)
    (hrun : ∀ (w : List Γ) (d : Cfg k Γ S x), d.state = some entry →
      (∀ p : ℤ, -1 ≤ p → p ≤ w.length → d.workTapes src (d.workTapePos src + p) =
        FinTM.bufferTape w p) →
      M.runFrom d (2 * w.length + 2) = post w d ∧
        (∀ t < 2 * w.length + 2, (M.runFrom d t).state ≠ some done) ∧
        ∀ j, ∀ t ≤ 2 * w.length + 2, if touched j then
          (M.runFrom d t).workTapePos j ∈
            Finset.Icc (d.workTapePos j - 1) (d.workTapePos j + w.length)
        else (M.runFrom d t).workTapePos j = d.workTapePos j) :
    (sweepContract M entry done src touched x post hpost hrun).time =
      fun w _ => 2 * w.length + 2 := rfl''',
'Turing.sweepMapWrite': '''example {k : ℕ} {Γ S Δ : Type} {x : List Γ} (extract : Γ → Δ) (merge : Option Γ → Δ → Γ)
    (w : List Γ) (d : Cfg k Γ S x) (j : Fin k) (q : ℤ) :
    sweepMapWrite extract merge w d j q =
      (FinTM.bufferTape w (q - d.workTapePos j)).map fun γ => merge (d.workTapes j q) (extract γ) :=
  rfl''',
'Turing.sweepPost': '''example {k : ℕ} {Γ S : Type} {x : List Γ} (done : S) (a : Fin k)
    (v : List Γ → Cfg k Γ S x → Fin k → ℤ → Option Γ) (w : List Γ) (d : Cfg k Γ S x) :
    (sweepPost done a v w d).state = some done := rfl''',
'Turing.tapeAction': '''example {k : ℕ} {Γ S : Type} (i : Fin k) (inp : SignType) (wr : Option (Option Γ)) (m : SignType)
    (q : S) : (tapeAction (k := k) (Symbol := Γ) i inp wr m q).state = some q := rfl''',
'Turing.walkTM': '''example {k : ℕ} (src : Fin k) (moved : Fin k → Prop) [DecidablePred moved] (dir : SignType) :
    (walkTM (Symbol := Bool) k src moved dir).q₀ = .run := rfl''',
'Turing.walkTM_contract': '''example {k : ℕ} {Γ : Type} (src : Fin k) (moved : Fin k → Prop) [DecidablePred moved]
    (hsrc : moved src) (dir : SignType) (x : List Γ) :
    (walkTM_contract src moved hsrc dir x).time = fun w _ => w.length + 1 := rfl''',
'Turing.zoneBase': '''example : zoneBase 1 = 2 := rfl''',
'Turing.zoneCapacity': '''example : zoneCapacity 0 = 2 := rfl''',
'Turing.zoneCascade': '''example {ℓ : ℕ} (j : ℕ) (z : ZoneContents ℓ) : zoneCascade true j z = zoneCascadeRight j z :=
  rfl''',
'Turing.zoneCascadeLeft': '''example {ℓ : ℕ} (j : ℕ) (z : ZoneContents ℓ) :
    zoneCascadeLeft j z = (zoneCascadeRight j z.swap).swap := rfl''',
'Turing.zoneCascadeRight': '''example {ℓ : ℕ} (z : ZoneContents ℓ) : zoneCascadeRight 0 z = zoneMove true z := rfl''',
'Turing.zoneCellAt': '''example {k ℓ : ℕ} (side : Bool) (z : Fin k → ZoneContents ℓ) (n : ℕ) :
    zoneCellAt side z n = (zoneOwner ℓ n).map fun i =>
      Sum.inr fun t => ((z t).words side i)[n - zoneStart i]? := rfl''',
'Turing.zoneCellOfCell': '''example {k : ℕ} : zoneCellOfCell (k := k) none = fun _ => none := rfl''',
'Turing.zoneCells': '''example {k ℓ : ℕ} (side : Bool) (z : Fin k → ZoneContents ℓ) (i : Fin ℓ) :
    zoneCells side z i = (List.range (zoneCapacity i)).map fun p =>
      Sum.inr fun t => ((z t).words side i)[p]? := rfl''',
'Turing.zoneMove': '''example (dir : Bool) (z : ZoneContents 0) : zoneMove dir z = z := rfl''',
'Turing.zoneMoveLeft': '''example {ℓ : ℕ} (hℓ : 0 < ℓ) (z : ZoneContents ℓ)
    (hroom : (z.right ⟨0, hℓ⟩).length + 1 ≤ zoneCapacity 0) :
    (zoneMoveLeft hℓ z hroom).home = (z.left ⟨0, hℓ⟩).headI := rfl''',
'Turing.zoneMoveRight': '''example {ℓ : ℕ} (hℓ : 0 < ℓ) (z : ZoneContents ℓ)
    (hroom : (z.left ⟨0, hℓ⟩).length + 1 ≤ zoneCapacity 0) :
    (zoneMoveRight hℓ z hroom).home = (z.right ⟨0, hℓ⟩).headI := rfl''',
'Turing.zoneOwner': '''example (ℓ n : ℕ) : zoneOwner ℓ n =
    Fin.find fun i : Fin ℓ => zoneStart i ≤ n ∧ n < zoneStart i + zoneCapacity i := rfl''',
'Turing.zoneRebalance': '''example {ℓ : ℕ} (dir : Bool) (z : ZoneContents ℓ) : zoneRebalance dir z =
    if zoneShiftIndex dir z < ℓ then zoneCascade dir (zoneShiftIndex dir z) z else z := rfl''',
'Turing.zoneShiftIn': '''example {ℓ : ℕ} (side : Bool) (i : ℕ) (z : ZoneContents ℓ) :
    (zoneShiftIn side i z).home = z.home := rfl''',
'Turing.zoneShiftInW': '''example {ℓ : ℕ} (w : Fin ℓ → List (Option Bool)) (j : Fin ℓ) : zoneShiftInW 0 w j = w j :=
  rfl''',
'Turing.zoneShiftIndex': '''example {ℓ : ℕ} (dir : Bool) (z : ZoneContents ℓ) : zoneShiftIndex dir z =
    (List.finRange ℓ).findIdx fun i => !(z.words dir i).isEmpty := rfl''',
'Turing.zoneShiftOut': '''example {ℓ : ℕ} (side : Bool) (i : ℕ) (z : ZoneContents ℓ) :
    (zoneShiftOut side i z).home = z.home := rfl''',
'Turing.zoneShiftOutW': '''example {ℓ : ℕ} (w : Fin ℓ → List (Option Bool)) (j : Fin ℓ) : zoneShiftOutW 0 w j = w j :=
  rfl''',
'Turing.zoneSlotOf': '''example {k : ℕ} (t : Fin k) (b : Bool) : zoneSlotOf t (.inl b) = none := rfl''',
'Turing.zoneSlotSet': '''example {k : ℕ} (t : Fin k) (cell : Option (ZoneSym k)) (s : Option (Option Bool)) :
    zoneSlotSet t cell s = .inr (Function.update (zoneCellOfCell cell) t s) := rfl''',
'Turing.zoneStart': '''example : zoneStart 0 = 2 := rfl''',
'Turing.zoneStepPair': '''example {ℓ : ℕ} (i : ℕ) (z : ZoneContents ℓ) :
    zoneStepPair i z = zoneShiftOut false i (zoneShiftIn true i z) := rfl''',
'Turing.zonedTape': '''example {k ℓ : ℕ} (z : Fin k → ZoneContents ℓ) :
    zonedTape z 0 = some (.inr fun t => some (z t).home) := rfl''',
}
SIMPCTL = '''example {k : ℕ} {S Γ : Type} {x : List Γ} (a : Action k Γ S) (c : Cfg k Γ S x) :
    (a.apply c).state = a.state := by simp'''
