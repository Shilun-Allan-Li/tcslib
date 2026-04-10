import TCSlib.BooleanAnalysis.Switching.RoundTrip

/-!
# Switching Lemma — Main Theorem

The main switching lemma statement, counting bounds, combinatorial inequalities,
and the corollary converting to CNF representation.
-/

open Classical

namespace SwitchingLemma2

variable {n : ℕ}

/-! ### Counting bounds -/

/-- Parse an aux list into triples `(pos, dir, hasMarker)` where
    `hasMarker = true` means the `(idx, dir)` entry is immediately followed
    by a `(w, false)` termination marker. Entries with `idx ≥ w` that are not
    immediately preceded by a real entry are dropped. -/
private def parseAux (w : ℕ) (hw_pos : 0 < w) :
    List (ℕ × Bool) → List (Fin w × Bool × Bool)
  | [] => []
  | (idx, dir) :: rest =>
    if h : idx < w then
      match rest with
      | [] => [(⟨idx, h⟩, dir, false)]
      | (idx', dir') :: rest' =>
        if idx' ≥ w then
          (⟨idx, h⟩, dir, true) :: parseAux w hw_pos rest'
        else
          (⟨idx, h⟩, dir, false) :: parseAux w hw_pos ((idx', dir') :: rest')
    else
      parseAux w hw_pos rest
termination_by l => l.length

/-- Convert a triple list back to an aux list. -/
private def triplesToAux (w : ℕ) :
    List (Fin w × Bool × Bool) → List (ℕ × Bool)
  | [] => []
  | (pos, dir, true) :: rest =>
    (pos.val, dir) :: (w, false) :: triplesToAux w rest
  | (pos, dir, false) :: rest =>
    (pos.val, dir) :: triplesToAux w rest

/-- Equational lemma: `parseAux` on an entry followed by a marker. -/
private lemma parseAux_cons_marker (w : ℕ) (hw_pos : 0 < w)
    (idx : ℕ) (h : idx < w) (dir : Bool) (rest : List (ℕ × Bool)) :
    parseAux w hw_pos ((idx, dir) :: (w, false) :: rest) =
      (⟨idx, h⟩, dir, true) :: parseAux w hw_pos rest := by
  rw [parseAux]
  simp only [h, ↓reduceDIte, ge_iff_le, le_refl, ↓reduceIte]

/-- Equational lemma: `parseAux` on an entry followed by a non-marker. -/
private lemma parseAux_cons_nonmarker (w : ℕ) (hw_pos : 0 < w)
    (idx : ℕ) (h : idx < w) (dir : Bool)
    (idx' : ℕ) (h' : idx' < w) (dir' : Bool) (rest : List (ℕ × Bool)) :
    parseAux w hw_pos ((idx, dir) :: (idx', dir') :: rest) =
      (⟨idx, h⟩, dir, false) :: parseAux w hw_pos ((idx', dir') :: rest) := by
  rw [parseAux]
  have hnge : ¬ idx' ≥ w := not_le.mpr h'
  simp only [h, ↓reduceDIte, ge_iff_le, hnge, ↓reduceIte]

/-- Equational lemma: `parseAux` on a single entry. -/
private lemma parseAux_singleton (w : ℕ) (hw_pos : 0 < w)
    (idx : ℕ) (h : idx < w) (dir : Bool) :
    parseAux w hw_pos [(idx, dir)] = [(⟨idx, h⟩, dir, false)] := by
  rw [parseAux]
  simp only [h, ↓reduceDIte]

/-- Equational lemma: `parseAux` on `[]`. -/
private lemma parseAux_nil (w : ℕ) (hw_pos : 0 < w) :
    parseAux w hw_pos [] = [] := by
  rw [parseAux]

/-- Round-trip: `parseAux` inverts `triplesToAux`. -/
private lemma parseAux_triplesToAux (w : ℕ) (hw_pos : 0 < w) :
    ∀ (ts : List (Fin w × Bool × Bool)),
      parseAux w hw_pos (triplesToAux w ts) = ts := by
  intro ts
  induction ts with
  | nil => rw [triplesToAux, parseAux_nil]
  | cons hd rest ih =>
    obtain ⟨pos, dir, mark⟩ := hd
    have hlt : pos.val < w := pos.isLt
    have hfin : (⟨pos.val, hlt⟩ : Fin w) = pos := Fin.ext rfl
    cases mark with
    | true =>
      show parseAux w hw_pos ((pos.val, dir) :: (w, false) :: triplesToAux w rest) =
        (pos, dir, true) :: rest
      rw [parseAux_cons_marker w hw_pos pos.val hlt dir (triplesToAux w rest), ih, hfin]
    | false =>
      show parseAux w hw_pos ((pos.val, dir) :: triplesToAux w rest) =
        (pos, dir, false) :: rest
      cases rest with
      | nil =>
        show parseAux w hw_pos [(pos.val, dir)] = [(pos, dir, false)]
        rw [parseAux_singleton w hw_pos pos.val hlt dir, hfin]
      | cons hd2 rest2 =>
        obtain ⟨pos2, dir2, mark2⟩ := hd2
        have hpos2 : pos2.val < w := pos2.isLt
        cases mark2 with
        | true =>
          show parseAux w hw_pos ((pos.val, dir) ::
              (pos2.val, dir2) :: (w, false) :: triplesToAux w rest2) =
            (pos, dir, false) :: (pos2, dir2, true) :: rest2
          rw [parseAux_cons_nonmarker w hw_pos pos.val hlt dir pos2.val hpos2 dir2
                ((w, false) :: triplesToAux w rest2)]
          have hih : parseAux w hw_pos ((pos2.val, dir2) :: (w, false) :: triplesToAux w rest2)
              = (pos2, dir2, true) :: rest2 := by
            have hexp : triplesToAux w ((pos2, dir2, true) :: rest2) =
                (pos2.val, dir2) :: (w, false) :: triplesToAux w rest2 := rfl
            rw [← hexp]; exact ih
          rw [hih, hfin]
        | false =>
          show parseAux w hw_pos ((pos.val, dir) ::
              (pos2.val, dir2) :: triplesToAux w rest2) =
            (pos, dir, false) :: (pos2, dir2, false) :: rest2
          rw [parseAux_cons_nonmarker w hw_pos pos.val hlt dir pos2.val hpos2 dir2
                (triplesToAux w rest2)]
          have hih : parseAux w hw_pos ((pos2.val, dir2) :: triplesToAux w rest2)
              = (pos2, dir2, false) :: rest2 := by
            have hexp : triplesToAux w ((pos2, dir2, false) :: rest2) =
                (pos2.val, dir2) :: triplesToAux w rest2 := rfl
            rw [← hexp]; exact ih
          rw [hih, hfin]

/-- `triplesToAux` distributes over append. -/
private lemma triplesToAux_append (w : ℕ)
    (ts₁ ts₂ : List (Fin w × Bool × Bool)) :
    triplesToAux w (ts₁ ++ ts₂) = triplesToAux w ts₁ ++ triplesToAux w ts₂ := by
  induction ts₁ with
  | nil => simp [triplesToAux]
  | cons hd rest ih =>
    obtain ⟨pos, dir, mark⟩ := hd
    cases mark with
    | true =>
      show triplesToAux w ((pos, dir, true) :: (rest ++ ts₂)) =
        triplesToAux w ((pos, dir, true) :: rest) ++ triplesToAux w ts₂
      simp [triplesToAux, ih]
    | false =>
      show triplesToAux w ((pos, dir, false) :: (rest ++ ts₂)) =
        triplesToAux w ((pos, dir, false) :: rest) ++ triplesToAux w ts₂
      simp [triplesToAux, ih]

/-- Combined length bound: the total aux output of `processClauseLits` plus
    remaining path length never exceeds the initial path length. -/
private lemma processClauseLits_len_add {n : ℕ}
    (lits : List (Literal n × ℕ)) (path : List (Fin n × Bool))
    (ρ₀ σ : Restriction n) :
    (processClauseLits lits path ρ₀ σ).2.2.2.length +
    (processClauseLits lits path ρ₀ σ).1.length ≤ path.length := by
  induction lits generalizing path ρ₀ σ with
  | nil => simp [processClauseLits]
  | cons hd tl ih =>
    cases path with
    | nil => simp [processClauseLits]
    | cons p ps =>
      simp only [processClauseLits, List.length_cons]
      have := ih ps (Function.update ρ₀ hd.1.var (some p.2))
                    (Function.update σ hd.1.var (some (!hd.1.neg)))
      omega

/-- Build a triple list from a `Fin w × Bool` block by marking the last entry. -/
private def markLast {w : ℕ} :
    List (Fin w × Bool) → List (Fin w × Bool × Bool)
  | [] => []
  | hd :: [] => [(hd.1, hd.2, true)]
  | hd :: (hd2 :: rest) => (hd.1, hd.2, false) :: markLast (hd2 :: rest)

/-- `triplesToAux` of `markLast` on a nonempty block produces the block followed
    by a termination marker. -/
private lemma triplesToAux_markLast (w : ℕ)
    (block : List (Fin w × Bool)) (hne : block ≠ []) :
    triplesToAux w (markLast block) =
      block.map (fun p => (p.1.val, p.2)) ++ [(w, false)] := by
  induction block with
  | nil => exact absurd rfl hne
  | cons hd rest ih =>
    obtain ⟨p, d⟩ := hd
    cases rest with
    | nil =>
      simp [markLast, triplesToAux]
    | cons hd2 rest2 =>
      have hML : markLast ((p, d) :: hd2 :: rest2) =
          (p, d, false) :: markLast (hd2 :: rest2) := by
        show markLast (((p, d) : Fin w × Bool) :: hd2 :: rest2) =
          (((p, d) : Fin w × Bool).1, ((p, d) : Fin w × Bool).2, false) ::
            markLast (hd2 :: rest2)
        rfl
      rw [hML]
      rw [show triplesToAux w ((p, d, false) :: markLast (hd2 :: rest2)) =
            (p.val, d) :: triplesToAux w (markLast (hd2 :: rest2)) from rfl]
      rw [ih (List.cons_ne_nil _ _)]
      simp

/-- `markLast` of a nonempty list is nonempty. -/
private lemma markLast_ne_nil {w : ℕ} (block : List (Fin w × Bool))
    (hne : block ≠ []) : markLast block ≠ [] := by
  match block, hne with
  | [hd], _ => simp [markLast]
  | hd :: hd2 :: rest, _ => simp [markLast]

/-- `markLast` preserves length. -/
private lemma markLast_length {w : ℕ} :
    ∀ (block : List (Fin w × Bool)), (markLast block).length = block.length
  | [] => rfl
  | [_] => rfl
  | hd :: hd2 :: rest => by
      show ((hd.1, hd.2, false) :: markLast (hd2 :: rest)).length =
        (hd :: hd2 :: rest).length
      have ih := markLast_length (hd2 :: rest)
      simp [ih]

/-- `getLast` of `markLast` on a nonempty block has `.2.2 = true`. -/
private lemma markLast_getLast_true {w : ℕ} :
    ∀ (block : List (Fin w × Bool)) (hne : markLast block ≠ []),
      ((markLast block).getLast hne).2.2 = true
  | [], hne => by simp [markLast] at hne
  | [hd], _ => by
      show (((hd.1, hd.2, true) : Fin w × Bool × Bool)).2.2 = true
      rfl
  | hd :: hd2 :: rest, hne => by
      have hne' : markLast (hd2 :: rest) ≠ [] :=
        markLast_ne_nil _ (List.cons_ne_nil _ _)
      have ih := markLast_getLast_true (hd2 :: rest) hne'
      show (((hd.1, hd.2, false) :: markLast (hd2 :: rest)).getLast hne).2.2 = true
      rw [List.getLast_cons hne']
      exact ih

/-- Cast a list of `(ℕ × Bool)` entries all with first coordinate `< w` into
    `List (Fin w × Bool)`. -/
private def toFinBlock (w : ℕ) :
    ∀ (l : List (ℕ × Bool)) (_ : ∀ e ∈ l, e.1 < w), List (Fin w × Bool)
  | [], _ => []
  | (idx, dir) :: rest, h =>
    (⟨idx, h (idx, dir) (List.mem_cons_self)⟩, dir) ::
      toFinBlock w rest (fun e he => h e (List.mem_cons_of_mem _ he))

/-- `toFinBlock` preserves the length. -/
private lemma toFinBlock_length (w : ℕ) (l : List (ℕ × Bool))
    (h : ∀ e ∈ l, e.1 < w) :
    (toFinBlock w l h).length = l.length := by
  induction l with
  | nil => rfl
  | cons hd rest ih =>
    obtain ⟨idx, dir⟩ := hd
    simp [toFinBlock, ih]

/-- Mapping `toFinBlock` back recovers the original list. -/
private lemma toFinBlock_map (w : ℕ) (l : List (ℕ × Bool))
    (h : ∀ e ∈ l, e.1 < w) :
    (toFinBlock w l h).map (fun p => (p.1.val, p.2)) = l := by
  induction l with
  | nil => rfl
  | cons hd rest ih =>
    obtain ⟨idx, dir⟩ := hd
    simp [toFinBlock, ih]

/-- `toFinBlock` is nonempty iff input is nonempty. -/
private lemma toFinBlock_ne_nil (w : ℕ) (l : List (ℕ × Bool))
    (h : ∀ e ∈ l, e.1 < w) (hne : l ≠ []) :
    toFinBlock w l h ≠ [] := by
  cases l with
  | nil => exact absurd rfl hne
  | cons hd rest =>
    obtain ⟨idx, dir⟩ := hd
    simp [toFinBlock]

/-- Every entry in `processClauseLits`'s aux output has first coordinate bounded
    by the term length. -/
private lemma processClauseLits_aux_idx_lt {n : ℕ} (t : Term n)
    (lits : List (Literal n × ℕ)) (path : List (Fin n × Bool))
    (ρ₀ σ : Restriction n)
    (hmem : ∀ p ∈ lits, p ∈ t.zipIdx) :
    ∀ e ∈ (processClauseLits lits path ρ₀ σ).2.2.2, e.1 < t.length := by
  intro e he
  obtain ⟨li, hli, hidx⟩ := processClauseLits_aux_entries_from_lits lits path ρ₀ σ e he
  obtain ⟨_, hlt_len, _⟩ := List.mem_zipIdx (hmem li hli)
  rw [hidx]; omega

/-- **Main encoder well-formedness invariant**.  The aux output of
    `razborovEncode.go` (with empty initial accumulator) can be expressed as
    `triplesToAux w ts` for some triple list `ts` whose length is bounded by
    the path length, and whose last element (if any) has `hasMarker = true`. -/
private lemma encode_go_wellformed {n : ℕ} (f : DNF n) (w : ℕ)
    (hw : f.width ≤ w) (hw_pos : 0 < w)
    (fuel : ℕ) (path : List (Fin n × Bool)) (ρ₀ σ : Restriction n) :
    ∃ ts : List (Fin w × Bool × Bool),
      (razborovEncode.go f w fuel path ρ₀ σ []).2 = triplesToAux w ts ∧
      ts.length ≤ path.length ∧
      (∀ (hne : ts ≠ []), (ts.getLast hne).2.2 = true) := by
  induction fuel generalizing path ρ₀ σ with
  | zero =>
    refine ⟨[], ?_, by simp, by intro hne; exact absurd rfl hne⟩
    cases path <;> simp [razborovEncode.go, triplesToAux]
  | succ fuel ih =>
    cases path with
    | nil =>
      refine ⟨[], ?_, by simp, by intro hne; exact absurd rfl hne⟩
      simp [razborovEncode.go, triplesToAux]
    | cons step rest =>
      simp only [razborovEncode.go]
      -- Case split on find?
      cases hfind : f.find? (fun t => decide (¬Term.killedBy t ρ₀)) with
      | none =>
        refine ⟨[], ?_, by simp, by intro hne; exact absurd rfl hne⟩
        simp [hfind, triplesToAux]
      | some t_clause =>
        simp only [hfind]
        -- Filter free literals
        set fli := (t_clause.zipIdx).filter
          (fun ⟨l, _⟩ => decide (l.var ∈ ρ₀.freeVars)) with hfli_def
        cases hflicase : fli with
        | nil =>
          refine ⟨[], ?_, by simp, by intro hne; exact absurd rfl hne⟩
          simp [hflicase, triplesToAux]
        | cons fl fls =>
          simp only [hflicase]
          set pcl := processClauseLits (fl :: fls) (step :: rest) ρ₀ σ with hpcl_def
          -- Extract the "new block" of aux data from pcl
          have ht_mem : t_clause ∈ f := List.mem_of_find?_eq_some hfind
          have ht_len : t_clause.length ≤ w :=
            le_trans (term_length_le_width f t_clause ht_mem) hw
          have hfli_mem_zip : ∀ p ∈ fl :: fls, p ∈ t_clause.zipIdx := by
            intro p hp
            rw [← hflicase] at hp
            rw [hfli_def] at hp
            exact (List.mem_filter.mp hp).1
          have hpcl_idx_lt : ∀ e ∈ pcl.2.2.2, e.1 < w := by
            intro e he
            exact lt_of_lt_of_le
              (processClauseLits_aux_idx_lt t_clause (fl :: fls) (step :: rest)
                ρ₀ σ hfli_mem_zip e he) ht_len
          -- The new block is nonempty
          have hpcl_ne : pcl.2.2.2 ≠ [] := by
            simp only [hpcl_def, processClauseLits]
            exact List.cons_ne_nil _ _
          -- Convert to Fin w × Bool list
          set block := toFinBlock w pcl.2.2.2 hpcl_idx_lt with hblock_def
          have hblock_ne : block ≠ [] := toFinBlock_ne_nil w _ _ hpcl_ne
          -- Apply the accumulator lemma and IH
          simp only [List.nil_append]
          rw [encode_go_acc f w fuel pcl.1 pcl.2.1 pcl.2.2.1 (pcl.2.2.2 ++ [(w, false)])]
          obtain ⟨ts_rec, hts_eq, hts_len, hts_last⟩ :=
            ih pcl.1 pcl.2.1 pcl.2.2.1
          refine ⟨markLast block ++ ts_rec, ?_, ?_, ?_⟩
          · -- Show the combined aux list matches triplesToAux
            simp only
            rw [triplesToAux_append, triplesToAux_markLast w block hblock_ne,
                hblock_def, toFinBlock_map, hts_eq]
          · -- Length bound
            rw [List.length_append]
            have hml_len : (markLast block).length = pcl.2.2.2.length := by
              rw [markLast_length]
              exact toFinBlock_length w pcl.2.2.2 hpcl_idx_lt
            have hpcl_len : pcl.2.2.2.length + pcl.1.length ≤ (step :: rest).length :=
              processClauseLits_len_add (fl :: fls) (step :: rest) ρ₀ σ
            omega
          · intro _
            -- The last of markLast block ++ ts_rec is either ts_rec's last
            -- or markLast block's last (if ts_rec = []).
            by_cases hts_rec_ne : ts_rec = []
            · subst hts_rec_ne
              simp only [List.append_nil]
              exact markLast_getLast_true block (markLast_ne_nil block hblock_ne)
            · rw [List.getLast_append_of_ne_nil _ hts_rec_ne]
              exact hts_last hts_rec_ne

/-- Combinatorial bound on the number of distinct aux lists that can arise
    from the Razborov encoder on bad restrictions.  Each of the `d` path steps
    contributes a `(position, direction, hasMarker)` triple with `position < w`
    and two booleans, giving `(4w)^d` possibilities.

    The proof (in the main case `w ≥ 1`) reduces to producing an injection
    from the image into `Fin d → Fin w × Bool × Bool`, which has cardinality
    exactly `(4 * w) ^ d`.  Constructing this injection is isolated into the
    helper `exists_aux_injection` below. -/
private lemma exists_aux_injection {n : ℕ} (f : DNF n) (w d : ℕ)
    (hw : f.width ≤ w) (hw_pos : 0 < w) (γ : Restriction n) :
    ∃ g : List (ℕ × Bool) → (Fin d → Fin w × Bool × Bool),
      Set.InjOn g
        (((Finset.univ.filter fun ρ : Restriction n =>
          IsBadRestriction f.eval d ρ ∧
          (razborovEncode f w d ρ).1 = γ).image
          (fun ρ => (razborovEncode f w d ρ).2) : Finset _) :
            Set (List (ℕ × Bool))) := by
  -- Strategy: parse aux into triples (pos : Fin w, dir : Bool, hasMarker : Bool)
  -- where `hasMarker = true` means the `(idx, dir)` entry is immediately
  -- followed by a `(w, false)` termination marker.  Pad to length d with a
  -- default triple to get a function `Fin d → Fin w × Bool × Bool`.
  -- For injectivity we use the round-trip `triplesToAux ∘ parseAux = id` on
  -- the encoder image; this is proved as a separate invariant of the encoder
  -- combined with `parseAux_triplesToAux`.
  classical
  refine ⟨fun aux =>
    fun i => ((parseAux w hw_pos aux)[i.val]?).getD (⟨0, hw_pos⟩, false, false),
    ?_⟩
  intro aux₁ haux₁ aux₂ haux₂ hg_eq
  -- Unified encoder well-formedness: every aux in the image is of the form
  -- `triplesToAux w ts` for some `ts` of length ≤ d whose last element (if any)
  -- has `hasMarker = true`.
  have hwf : ∀ aux : List (ℕ × Bool),
      aux ∈ ((Finset.univ.filter fun ρ : Restriction n =>
          IsBadRestriction f.eval d ρ ∧
          (razborovEncode f w d ρ).1 = γ).image
          (fun ρ => (razborovEncode f w d ρ).2) : Finset _) →
      ∃ ts : List (Fin w × Bool × Bool),
        aux = triplesToAux w ts ∧ ts.length ≤ d ∧
        (∀ (hne : ts ≠ []), (ts.getLast hne).2.2 = true) := by
    intro aux haux
    rw [Finset.mem_image] at haux
    obtain ⟨ρ, _, hρ_eq⟩ := haux
    rw [← hρ_eq]
    unfold razborovEncode
    obtain ⟨ts, hts_eq, hts_len, hts_last⟩ :=
      encode_go_wellformed f w hw hw_pos
        (((canonicalDTree f ρ).deepPath.take d).length + 1)
        ((canonicalDTree f ρ).deepPath.take d) ρ ρ
    refine ⟨ts, hts_eq, ?_, hts_last⟩
    have : ((canonicalDTree f ρ).deepPath.take d).length ≤ d :=
      List.length_take_le d _
    omega
  -- Derive the three local facts from hwf.
  have hround : ∀ aux : List (ℕ × Bool),
      aux ∈ ((Finset.univ.filter fun ρ : Restriction n =>
          IsBadRestriction f.eval d ρ ∧
          (razborovEncode f w d ρ).1 = γ).image
          (fun ρ => (razborovEncode f w d ρ).2) : Finset _) →
      triplesToAux w (parseAux w hw_pos aux) = aux := by
    intro aux haux
    obtain ⟨ts, hts_eq, _, _⟩ := hwf aux haux
    rw [hts_eq, parseAux_triplesToAux]
  have hlen : ∀ aux : List (ℕ × Bool),
      aux ∈ ((Finset.univ.filter fun ρ : Restriction n =>
          IsBadRestriction f.eval d ρ ∧
          (razborovEncode f w d ρ).1 = γ).image
          (fun ρ => (razborovEncode f w d ρ).2) : Finset _) →
      (parseAux w hw_pos aux).length ≤ d := by
    intro aux haux
    obtain ⟨ts, hts_eq, hts_len, _⟩ := hwf aux haux
    rw [hts_eq, parseAux_triplesToAux]
    exact hts_len
  have hlast : ∀ aux : List (ℕ × Bool),
      aux ∈ ((Finset.univ.filter fun ρ : Restriction n =>
          IsBadRestriction f.eval d ρ ∧
          (razborovEncode f w d ρ).1 = γ).image
          (fun ρ => (razborovEncode f w d ρ).2) : Finset _) →
      ∀ (hlen_pos : 0 < (parseAux w hw_pos aux).length),
        ((parseAux w hw_pos aux)[(parseAux w hw_pos aux).length - 1]'
          (Nat.sub_lt hlen_pos (by norm_num))).2.2 = true := by
    intro aux haux hlen_pos
    obtain ⟨ts, hts_eq, _, hts_last⟩ := hwf aux haux
    have hparse : parseAux w hw_pos aux = ts := by
      rw [hts_eq, parseAux_triplesToAux]
    -- Translate the goal to ts
    have hts_ne : ts ≠ [] := by
      intro h
      rw [hparse, h] at hlen_pos
      exact absurd hlen_pos (by simp)
    have hlast_val := hts_last hts_ne
    -- `ts.getLast hts_ne = ts[ts.length - 1]`
    have hgetLast_eq :
        ts.getLast hts_ne = ts[ts.length - 1]'(Nat.sub_lt
          (List.length_pos_iff.mpr hts_ne) (by norm_num)) := by
      rw [List.getLast_eq_getElem]
    rw [hgetLast_eq] at hlast_val
    -- And the parseAux version = ts version
    conv_lhs =>
      rw [show (parseAux w hw_pos aux)[(parseAux w hw_pos aux).length - 1]'
              (Nat.sub_lt hlen_pos (by norm_num)) =
            ts[ts.length - 1]'(Nat.sub_lt (List.length_pos_iff.mpr hts_ne) (by norm_num))
          from by congr 1 <;> rw [hparse]]
    exact hlast_val
  have hparse_eq : parseAux w hw_pos aux₁ = parseAux w hw_pos aux₂ := by
    have h1 := hlen aux₁ haux₁
    have h2 := hlen aux₂ haux₂
    have hpt : ∀ i : Fin d,
        (parseAux w hw_pos aux₁)[i.val]?.getD (⟨0, hw_pos⟩, false, false) =
        (parseAux w hw_pos aux₂)[i.val]?.getD (⟨0, hw_pos⟩, false, false) := by
      intro i
      have := congrFun hg_eq i
      simpa using this
    -- Step 1: lengths are equal.
    have hlen_eq : (parseAux w hw_pos aux₁).length = (parseAux w hw_pos aux₂).length := by
      by_contra hne
      -- Symmetric helper handling the case L1.length < L2.length.
      have key : ∀ (a b : List (ℕ × Bool)),
          a ∈ ((Finset.univ.filter fun ρ : Restriction n =>
              IsBadRestriction f.eval d ρ ∧
              (razborovEncode f w d ρ).1 = γ).image
              (fun ρ => (razborovEncode f w d ρ).2) : Finset _) →
          b ∈ ((Finset.univ.filter fun ρ : Restriction n =>
              IsBadRestriction f.eval d ρ ∧
              (razborovEncode f w d ρ).1 = γ).image
              (fun ρ => (razborovEncode f w d ρ).2) : Finset _) →
          (parseAux w hw_pos a).length ≤ d → (parseAux w hw_pos b).length ≤ d →
          (parseAux w hw_pos a).length < (parseAux w hw_pos b).length →
          (∀ i : Fin d,
            (parseAux w hw_pos a)[i.val]?.getD (⟨0, hw_pos⟩, false, false) =
            (parseAux w hw_pos b)[i.val]?.getD (⟨0, hw_pos⟩, false, false)) →
          False := by
        intro a b ha hb ha_d hb_d hlt hpt_ab
        set La := parseAux w hw_pos a
        set Lb := parseAux w hw_pos b
        have hb_pos : 0 < Lb.length := lt_of_le_of_lt (Nat.zero_le _) hlt
        set j := Lb.length - 1 with hj_def
        have hjlt : j < Lb.length := Nat.sub_lt hb_pos (by norm_num)
        have hjd : j < d := lt_of_lt_of_le hjlt hb_d
        have hjLa : La.length ≤ j := by omega
        have hja : La[j]? = none := List.getElem?_eq_none hjLa
        have hjb : Lb[j]? = some (Lb[j]) := List.getElem?_eq_getElem hjlt
        have hval := hpt_ab ⟨j, hjd⟩
        rw [hja, hjb] at hval
        simp only [Option.getD_none, Option.getD_some] at hval
        have hmark : (Lb[j]).2.2 = true := hlast b hb hb_pos
        rw [← hval] at hmark
        simp at hmark
      rcases lt_or_gt_of_ne hne with hlt | hgt
      · exact key aux₁ aux₂ haux₁ haux₂ h1 h2 hlt hpt
      · exact key aux₂ aux₁ haux₂ haux₁ h2 h1 hgt (fun i => (hpt i).symm)
    -- Step 2: equal lengths + pointwise equality gives list equality.
    apply List.ext_getElem hlen_eq
    intro i hi1 hi2
    have hid : i < d := lt_of_lt_of_le hi1 h1
    have hval := hpt ⟨i, hid⟩
    rw [List.getElem?_eq_getElem hi1, List.getElem?_eq_getElem hi2] at hval
    simpa using hval
  -- Now apply triplesToAux to both sides.
  have := congrArg (triplesToAux w) hparse_eq
  rw [hround aux₁ haux₁, hround aux₂ haux₂] at this
  exact this

private lemma aux_image_card_bound {n : ℕ} (f : DNF n) (w d : ℕ)
    (hw : f.width ≤ w) (γ : Restriction n) :
    (((Finset.univ.filter fun ρ : Restriction n =>
        IsBadRestriction f.eval d ρ ∧
        (razborovEncode f w d ρ).1 = γ).image
        (fun ρ => (razborovEncode f w d ρ).2)).card) ≤ (4 * w) ^ d := by
  by_cases hw0 : w = 0
  · -- Edge case w = 0: `f.width ≤ 0` forces every term in `f` to be empty,
    -- and empty terms are trivially `fixedBy` any restriction, so
    -- `dtDepth (restrictFn f.eval ρ) = 0` and there are no bad restrictions.
    subst hw0
    have hall_empty : ∀ t ∈ f, t = [] := by
      intro t ht
      have ht_len : t.length ≤ 0 := le_trans (term_length_le_width f t ht) hw
      exact List.length_eq_zero_iff.mp (Nat.le_zero.mp ht_len)
    have hno_bad : ∀ ρ : Restriction n, ¬ IsBadRestriction f.eval d ρ := by
      intro ρ hbad
      unfold IsBadRestriction at hbad
      -- If f has any term, that term is empty hence fixedBy ρ → dtDepth 0
      -- If f is empty, restrictFn is constant false → dtDepth 0
      by_cases hf : f = []
      · have hdtd : dtDepth (restrictFn f.eval ρ) = 0 := by
          apply killedAll_implies_dtDepth_zero
          intro t ht
          rw [hf] at ht; exact absurd ht (List.not_mem_nil)
        omega
      · obtain ⟨t, ht_mem⟩ := List.exists_mem_of_ne_nil f hf
        have ht_empty : t = [] := hall_empty t ht_mem
        have hdtd : dtDepth (restrictFn f.eval ρ) = 0 := by
          apply fixedTerm_implies_dtDepth_zero
          exact ⟨t, ht_mem, by rw [ht_empty]; intro l hl; exact absurd hl (List.not_mem_nil)⟩
        omega
    have hfilter_empty : (Finset.univ.filter fun ρ : Restriction n =>
        IsBadRestriction f.eval d ρ ∧ (razborovEncode f 0 d ρ).1 = γ) = ∅ := by
      rw [Finset.eq_empty_iff_forall_notMem]
      intro ρ hρ
      rw [Finset.mem_filter] at hρ
      exact hno_bad ρ hρ.2.1
    rw [hfilter_empty, Finset.image_empty, Finset.card_empty]
    exact Nat.zero_le _
  · have hw_pos : 0 < w := Nat.pos_of_ne_zero hw0
    obtain ⟨g, hginj⟩ := exists_aux_injection f w d hw hw_pos γ
    set S := ((Finset.univ.filter fun ρ : Restriction n =>
        IsBadRestriction f.eval d ρ ∧
        (razborovEncode f w d ρ).1 = γ).image
        (fun ρ => (razborovEncode f w d ρ).2)) with hS_def
    have hcard_eq : Fintype.card (Fin d → Fin w × Bool × Bool) = (4 * w) ^ d := by
      simp only [Fintype.card_fun, Fintype.card_prod, Fintype.card_fin,
                 Fintype.card_bool]
      ring
    calc S.card
        = (S.image g).card := (Finset.card_image_of_injOn hginj).symm
      _ ≤ (Finset.univ : Finset (Fin d → Fin w × Bool × Bool)).card :=
          Finset.card_le_card (Finset.subset_univ _)
      _ = Fintype.card (Fin d → Fin w × Bool × Bool) := Finset.card_univ
      _ = (4 * w) ^ d := hcard_eq

/-- Each aux data entry is a `(position, direction)` pair plus an implicit
    "is last free-lit of clause" flag (since the encoder inserts a `(w, false)`
    marker after each clause block). Thus each of the `d` path steps has
    `w · 2 · 2 = 4w` possibilities, giving `(4w)^d` fibers. -/
private lemma fiber_bound {n : ℕ} (f : DNF n) (w s d : ℕ)
    (hw : f.width ≤ w) (hd : d ≤ s)
    (hnd : ∀ t ∈ f, ∀ l₁ ∈ t, ∀ l₂ ∈ t, l₁.var = l₂.var → l₁ = l₂)
    (γ : Restriction n) :
    (Finset.univ.filter fun ρ : Restriction n =>
        IsRestriction s ρ ∧ IsBadRestriction f.eval d ρ ∧
        (razborovEncode f w d ρ).1 = γ).card ≤ (4 * w) ^ d := by
  -- Step 1: drop the `IsRestriction` hypothesis (monotone in the filter).
  set S := (Finset.univ.filter fun ρ : Restriction n =>
      IsRestriction s ρ ∧ IsBadRestriction f.eval d ρ ∧
      (razborovEncode f w d ρ).1 = γ)
  set T := (Finset.univ.filter fun ρ : Restriction n =>
      IsBadRestriction f.eval d ρ ∧ (razborovEncode f w d ρ).1 = γ)
  have hST : S ⊆ T := by
    intro ρ hρ
    simp only [S, T, Finset.mem_filter, Finset.mem_univ, true_and] at hρ ⊢
    exact ⟨hρ.2.1, hρ.2.2⟩
  refine le_trans (Finset.card_le_card hST) ?_
  -- Step 2: the map `ρ ↦ (razborovEncode f w d ρ).2` is injective on T.
  have hinj : Set.InjOn (fun ρ : Restriction n => (razborovEncode f w d ρ).2)
      (T : Set (Restriction n)) := by
    intro ρ₁ hρ₁ ρ₂ hρ₂ heq
    simp only [T, Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq] at hρ₁ hρ₂
    obtain ⟨hbad₁, hγ₁⟩ := hρ₁
    obtain ⟨hbad₂, hγ₂⟩ := hρ₂
    have henc : razborovEncode f w d ρ₁ = razborovEncode f w d ρ₂ := by
      apply Prod.ext
      · rw [hγ₁, hγ₂]
      · exact heq
    exact razborovEncode_injective f w d ρ₁ ρ₂ hbad₁ hbad₂ hw hnd henc
  rw [← Finset.card_image_of_injOn hinj]
  exact aux_image_card_bound f w d hw γ

/-- **Razborov counting bound**. -/
private lemma bad_count_bound {n : ℕ} (f : DNF n) (w s d : ℕ)
    (hw : f.width ≤ w) (hd : d ≤ s)
    (hnd : ∀ t ∈ f, ∀ l₁ ∈ t, ∀ l₂ ∈ t, l₁.var = l₂.var → l₁ = l₂) :
    (Finset.univ.filter fun ρ : Restriction n =>
        IsRestriction s ρ ∧ IsBadRestriction f.eval d ρ).card ≤
    n.choose (s - d) * 2 ^ (n - (s - d)) * (4 * w) ^ d := by
  sorry

/-! ## Combinatorial inequalities -/

private lemma bad_filter_empty_of_d_ge_s {n : ℕ} (f : DNF n) (d s : ℕ) (hds : s ≤ d) :
    (Finset.univ.filter fun ρ : Restriction n =>
        IsRestriction s ρ ∧ IsBadRestriction f.eval d ρ) = ∅ := by
  simp +zetaDelta at *
  exact fun ρ hρ => not_lt.mpr (le_trans (dtDepth_restrictFn_le_numFree _ _)
    (by linarith [hρ.symm]))

private lemma choose_mul_pow_bound {n s d : ℕ} (hs : 5 * s ≤ n) (hd : d ≤ s) :
    n.choose (s - d) * (4 * n) ^ d ≤ n.choose s * (5 * s) ^ d := by
  induction d with
  | zero => norm_num
  | succ d hd_ih =>
    have h_simp : (Nat.choose n (s - d - 1)) * (4 * n) ≤ (Nat.choose n (s - d)) * (5 * s) := by
      set m := s - d - 1 with hm_def
      have hm_succ : s - d = m + 1 := by omega
      rw [hm_succ]
      have h_eq := Nat.choose_succ_right_eq n m
      have h_mn : m ≤ n := by omega
      have h_pos : 0 < Nat.choose n m := Nat.choose_pos h_mn
      have h_sub_add : (n - m) + m = n := Nat.sub_add_cancel h_mn
      suffices h : 4 * n * (m + 1) ≤ (n - m) * (5 * s) by nlinarith [h_eq]
      have hms : m + 1 + d = s := by omega
      zify [h_mn] at h_sub_add hs ⊢
      nlinarith [hms]
    have := hd_ih ( Nat.le_of_succ_le hd )
    rw [ Nat.sub_sub ] at *
    rw [ pow_succ', pow_succ' ]
    nlinarith [ pow_pos ( show 0 < 4 * n by linarith ) d ]

/-! ## Main theorem -/

theorem switching_lemma {n : ℕ} (hn : 0 < n) (f : DNF n) (w s d : ℕ)
    (hw : f.width ≤ w) (hs : 5 * s ≤ n)
    (hnd : ∀ t ∈ f, ∀ l₁ ∈ t, ∀ l₂ ∈ t, l₁.var = l₂.var → l₁ = l₂) :
    (Finset.univ.filter fun ρ : Restriction n =>
        IsRestriction s ρ ∧ IsBadRestriction f.eval d ρ).card * n ^ d ≤
    numSRestrictions n s * (10 * s * w) ^ d := by
  by_cases hds : d ≤ s
  · refine le_trans (Nat.mul_le_mul_right _ (bad_count_bound f w s d hw hds hnd)) ?_
    convert Nat.mul_le_mul_right _ (choose_mul_pow_bound hs hds) |> le_trans <| ?_ using 1; ring
    rotate_left
    exact 2 ^ (n - s) * (2 * w) ^ d
    · unfold numSRestrictions; ring_nf
      norm_num [mul_assoc, mul_left_comm, ← mul_pow]
      ring_nf; norm_num [mul_assoc, mul_comm, mul_left_comm]
    · rw [show n - (s - d) = n - s + d by omega]; ring
  · rw [bad_filter_empty_of_d_ge_s f d s (by linarith)]; norm_num

/-! ## Decision tree to DNF/CNF conversion -/

private def toDNF {n : ℕ} : DecisionTree n → DNF n
  | .leaf true  => [[]   ]
  | .leaf false => []
  | .branch v lo hi =>
    ((toDNF lo).map fun t => ⟨v, true⟩ :: t) ++
    ((toDNF hi).map fun t => ⟨v, false⟩ :: t)

private def toCNF {n : ℕ} : DecisionTree n → CNF n
  | .leaf true  => []
  | .leaf false => [[]   ]
  | .branch v lo hi =>
    ((toCNF lo).map fun c => ⟨v, false⟩ :: c) ++
    ((toCNF hi).map fun c => ⟨v, true⟩ :: c)

private lemma dtDepth_witness {n : ℕ} (f : (Fin n → Bool) → Bool) :
    ∃ T : DecisionTree n, T.depth ≤ dtDepth f ∧ ∀ x, T.eval x = f x := by
  classical
  let p := fun d => ∃ T : DecisionTree n, T.depth ≤ d ∧ ∀ x, T.eval x = f x
  have hexists : ∃ d, p d := ⟨n, buildFullDTree f 0 (fun _ => false),
    buildFullDTree_depth f 0 (Nat.zero_le n) _,
    fun x => buildFullDTree_eval f 0 (Nat.zero_le n) _ x (fun _ hi => by omega)⟩
  have hspec := Nat.find_spec hexists
  show p (dtDepth f)
  unfold dtDepth
  convert hspec using 1

lemma dtDepth_le_implies_small_dnf_cnf {n : ℕ} (f : (Fin n → Bool) → Bool) (d : ℕ)
    (h : dtDepth f ≤ d) :
    (∃ φ : DNF n, φ.width ≤ d ∧ ∀ x, φ.eval x = f x) ∧
    (∃ ψ : CNF n, ψ.width ≤ d ∧ ∀ x, ψ.eval x = f x) := by
  obtain ⟨T, hTd, hTeval⟩ := dtDepth_witness f
  have hTd' : T.depth ≤ d := le_trans hTd h
  constructor
  · use SwitchingLemma2.toDNF T, by
      have h_width_le_depth : ∀ T : DecisionTree n, (toDNF T).width ≤ T.depth := by
        intro T;
        have h_width_induction : ∀ T : DecisionTree n, ∀ t ∈ toDNF T, t.length ≤ T.depth := by
          intro T
          induction' T with v lo hi hlo hhi;
          · cases v <;> simp +decide [ toDNF ];
          · intro t ht; unfold toDNF at ht; simp_all +decide [ DecisionTree.depth ] ;
            grind;
        have h_width_induction : ∀ {l : List ℕ}, (∀ x ∈ l, x ≤ T.depth) → List.foldr max 0 l ≤ T.depth := by
          intros l hl; induction l <;> aesop;
        exact h_width_induction fun x hx => by aesop;
      exact le_trans ( h_width_le_depth T ) hTd', by
      intro x;
      convert hTeval x using 1;
      clear hTd hTeval hTd' h;
      induction' T with v lo hi ihlo ihhi;
      · cases v <;> simp +decide [ toDNF ];
        · rfl;
        · rfl;
      · unfold DNF.eval at *; simp_all +decide [ DecisionTree.eval ] ;
        unfold toDNF; simp +decide [ *, List.any_append ] ;
        split_ifs <;> simp_all +decide [ Function.comp, Term.eval ];
        · simp_all +decide [ Function.comp, Literal.eval ];
          simp_all +decide [ Function.comp, List.any_eq, List.all_eq ];
        · simp_all +decide [ Function.comp, List.any_eq, Literal.eval ]
  · use toCNF T;
    refine' ⟨ le_trans _ hTd', fun x => _ ⟩;
    · have h_clause_length : ∀ T : DecisionTree n, ∀ c ∈ toCNF T, c.length ≤ T.depth := by
        intro T c hc
        induction' T with v lo hi ih_lo ih_hi generalizing c;
        · cases v <;> cases hc ; trivial;
          contradiction;
        · have h_clauses : ∀ c ∈ toCNF (DecisionTree.branch lo hi ih_lo), ∃ c' ∈ toCNF hi ∪ toCNF ih_lo, c = ⟨lo, false⟩ :: c' ∨ c = ⟨lo, true⟩ :: c' := by
            intro c hc; rw [ show toCNF ( DecisionTree.branch lo hi ih_lo ) = ( toCNF hi |> List.map fun c' => ⟨ lo, false ⟩ :: c' ) ++ ( toCNF ih_lo |> List.map fun c' => ⟨ lo, true ⟩ :: c' ) from rfl ] at hc; aesop;
          obtain ⟨ c', hc', rfl | rfl ⟩ := h_clauses c hc <;> simp +arith +decide [ *, DecisionTree.depth ];
          · grind;
          · grind;
      have h_foldr_le : ∀ {l : List ℕ}, (∀ x ∈ l, x ≤ T.depth) → List.foldr Max.max 0 l ≤ T.depth := by
        intros l hl; induction l <;> aesop;
      exact h_foldr_le fun x hx => by aesop;
    · rw [ ← hTeval, eq_comm ];
      have h_equiv : ∀ T : DecisionTree n, ∀ x : Fin n → Bool, T.eval x = (toCNF T).eval x := by
        intros T x; induction' T with v lo hi ih_lo ih_hi generalizing x; simp +decide [ *, CNF.eval ] ;
        · cases v <;> simp +decide [ DecisionTree.eval ];
          · exact ⟨ [ ], by tauto, by tauto ⟩;
          · exact fun t ht => by cases ht;
        · simp +decide [ *, DecisionTree.eval, CNF.eval ];
          rw [ show toCNF ( DecisionTree.branch lo hi ih_lo ) = ( toCNF hi |> List.map fun c => ⟨ lo, false ⟩ :: c ) ++ ( toCNF ih_lo |> List.map fun c => ⟨ lo, true ⟩ :: c ) by rfl ];
          split_ifs <;> simp_all +decide [ CNF.evalClause ];
          · simp +decide [ *, Function.comp, Literal.eval ];
            grind +splitIndPred;
          · simp +decide [ *, Function.comp, Literal.eval ];
            grind;
      exact h_equiv T x

theorem switching_corollary {n : ℕ} (hn : 0 < n) (f : DNF n) (w s : ℕ)
    (hw : f.width ≤ w) (hs : 5 * s ≤ n)
    (hnd : ∀ t ∈ f, ∀ l₁ ∈ t, ∀ l₂ ∈ t, l₁.var = l₂.var → l₁ = l₂) :
    (Finset.univ.filter fun ρ : Restriction n =>
        IsRestriction s ρ ∧
        ¬ ∃ ψ : CNF n, ψ.width ≤ w ∧
          ∀ x, ψ.eval x = restrictFn f.eval ρ x).card * n ^ w ≤
    numSRestrictions n s * (10 * s * w) ^ w := by
  apply le_trans _ (switching_lemma hn f w s w hw hs hnd)
  apply Nat.mul_le_mul_right
  apply Finset.card_le_card
  intro ρ hρ
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hρ ⊢
  refine ⟨hρ.1, ?_⟩
  show dtDepth (restrictFn f.eval ρ) > w
  by_contra hgood; push_neg at hgood
  exact hρ.2 (dtDepth_le_implies_small_dnf_cnf _ w hgood).2

end SwitchingLemma2
