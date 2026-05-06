import TCSlib.BooleanAnalysis.Switching.CanonicalDTree
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
    (hw : f.width ≤ w) (_hw_pos : 0 < w)
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
        simp [triplesToAux]
      | some t_clause =>
        simp only []
        -- Filter free literals
        set fli := (t_clause.zipIdx).filter
          (fun ⟨l, _⟩ => decide (l.var ∈ ρ₀.freeVars)) with hfli_def
        cases hflicase : fli with
        | nil =>
          refine ⟨[], ?_, by simp, by intro hne; exact absurd rfl hne⟩
          simp [triplesToAux]
        | cons fl fls =>
          simp only []
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
          from by (congr 1; rw [hparse])]
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
    (hw : f.width ≤ w) (_hd : d ≤ s)
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

/-- The number of restrictions with exactly `k` free variables equals
    `n.choose k * 2 ^ (n - k)`. -/
private lemma card_filter_numFree_eq (n k : ℕ) :
    (Finset.univ.filter fun ρ : Restriction n => ρ.numFree = k).card =
    n.choose k * 2 ^ (n - k) := by
  -- Partition restrictions by their set of free variables.
  classical
  rw [show (Finset.univ.filter fun ρ : Restriction n => ρ.numFree = k) =
      (Finset.univ.filter fun ρ : Restriction n => ρ.freeVars.card = k) from rfl]
  -- Use bijection: ρ ↔ (ρ.freeVars, g) where g encodes the non-free values.
  -- The cardinality is computed via a fiberwise sum over subsets of size k.
  have hcard : ∀ S : Finset (Fin n),
      (Finset.univ.filter fun ρ : Restriction n => ρ.freeVars = S).card = 2 ^ (n - S.card) := by
    intro S
    -- Bijection with functions (Fin n \ S) → Bool.
    let φ : (Fin n → Bool) → Restriction n :=
      fun g i => if i ∈ S then none else some (g i)
    have hφinj : ∀ g₁ g₂ : Fin n → Bool, (∀ i ∈ S, g₁ i = false) →
        (∀ i ∈ S, g₂ i = false) → φ g₁ = φ g₂ → g₁ = g₂ := by
      intro g₁ g₂ hg₁ hg₂ heq
      funext i
      by_cases hi : i ∈ S
      · rw [hg₁ i hi, hg₂ i hi]
      · have := congrFun heq i
        simp only [φ, hi, if_false] at this
        exact Option.some.inj this
    have himg : (Finset.univ.filter fun ρ : Restriction n => ρ.freeVars = S) =
        ((Finset.univ.filter fun g : Fin n → Bool => ∀ i ∈ S, g i = false).image φ) := by
      ext ρ
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image]
      constructor
      · intro hρ
        refine ⟨fun i => (ρ i).getD false, ?_, ?_⟩
        · intro i hi
          have : ρ i = none := by
            have : i ∈ ρ.freeVars := by rw [hρ]; exact hi
            simp [Restriction.freeVars] at this
            exact this
          simp [this]
        · funext i
          simp only [φ]
          by_cases hi : i ∈ S
          · simp only [hi, if_true]
            have : i ∈ ρ.freeVars := by rw [hρ]; exact hi
            simp [Restriction.freeVars] at this
            exact this.symm
          · simp only [hi, if_false]
            have hnf : i ∉ ρ.freeVars := by rw [hρ]; exact hi
            simp only [Restriction.freeVars, Finset.mem_filter, Finset.mem_univ,
                       true_and, Option.isNone_iff_eq_none] at hnf
            cases h : ρ i with
            | none => exact absurd h hnf
            | some b => simp
      · rintro ⟨g, hg, rfl⟩
        ext i
        simp only [Restriction.freeVars, Finset.mem_filter, Finset.mem_univ, true_and, φ]
        constructor
        · intro hi
          by_cases h : i ∈ S
          · exact h
          · simp [h] at hi
        · intro hi
          simp [hi]
    rw [himg, Finset.card_image_of_injOn]
    · -- cardinality of {g : Fin n → Bool | ∀ i ∈ S, g i = false}
      -- equals 2 ^ (n - S.card) since g is free on (Fin n \ S).
      -- Use bijection with (Fin n \ S) → Bool... or just direct counting.
      classical
      let ψ : ((↥Sᶜ : Type) → Bool) → (Fin n → Bool) :=
        fun h i => if hi : i ∈ S then false else h ⟨i, by
          simp only [Finset.mem_compl]; exact hi⟩
      have hψ_range : Set.range ψ =
          {g : Fin n → Bool | ∀ i ∈ S, g i = false} := by
        ext g
        simp only [Set.mem_range, Set.mem_setOf_eq]
        constructor
        · rintro ⟨h, rfl⟩ i hi
          simp [ψ, hi]
        · intro hg
          refine ⟨fun j => g j.val, ?_⟩
          funext i
          simp only [ψ]
          by_cases hi : i ∈ S
          · simp [hi, hg i hi]
          · simp [hi]
      have hψ_inj : Function.Injective ψ := by
        intro h₁ h₂ heq
        funext ⟨i, hi⟩
        have := congrFun heq i
        simp only [Finset.mem_compl] at hi
        simp only [ψ, hi, dite_false] at this
        exact this
      have hcard_ψ : Fintype.card ((↥Sᶜ : Type) → Bool) = 2 ^ (n - S.card) := by
        simp [Fintype.card_coe]
      have himg_ψ : (Finset.univ.image ψ :
          Finset (Fin n → Bool)) = (Finset.univ.filter fun g => ∀ i ∈ S, g i = false) := by
        ext g
        simp only [Finset.mem_image, Finset.mem_univ, true_and,
                   Finset.mem_filter]
        rw [← Set.mem_range (f := ψ), hψ_range]
        simp
      rw [← himg_ψ, Finset.card_image_of_injective _ hψ_inj]
      rw [Finset.card_univ]
      exact hcard_ψ
    · intro g₁ hg₁ g₂ hg₂ heq
      simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq] at hg₁ hg₂
      exact hφinj g₁ g₂ hg₁ hg₂ heq
  -- Now sum over S with |S| = k using powersetCard directly.
  have hpart : (Finset.univ.filter fun ρ : Restriction n => ρ.freeVars.card = k) =
      ((Finset.univ : Finset (Fin n)).powersetCard k).biUnion
        (fun S => Finset.univ.filter fun ρ : Restriction n => ρ.freeVars = S) := by
    ext ρ
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_biUnion,
               Finset.mem_powersetCard, Finset.subset_univ, true_and]
    constructor
    · intro hρ; exact ⟨ρ.freeVars, hρ, rfl⟩
    · rintro ⟨S, hS, hρ⟩; rw [hρ]; exact hS
  rw [hpart, Finset.card_biUnion]
  · -- Each fiber has size 2^(n - S.card), and |S| = k in powersetCard.
    have hsum_eq : ∀ S ∈ (Finset.univ : Finset (Fin n)).powersetCard k,
        (Finset.univ.filter fun ρ : Restriction n => ρ.freeVars = S).card =
          2 ^ (n - k) := by
      intro S hS
      rw [hcard S]
      rw [Finset.mem_powersetCard] at hS
      rw [hS.2]
    rw [Finset.sum_congr rfl hsum_eq]
    rw [Finset.sum_const, smul_eq_mul, Finset.card_powersetCard]
    simp
  · -- Disjoint: different S give different ρ
    intro S₁ _ S₂ _ hne
    simp only [Function.onFun, Finset.disjoint_left]
    intro ρ hρ₁ hρ₂
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hρ₁ hρ₂
    exact hne (hρ₁.symm.trans hρ₂)

/-! ### Helpers for numFree accounting in the Razborov encoder -/

/-- Updating a free variable of ρ to `some b` strictly decreases `numFree` by 1. -/
private lemma numFree_update_free {n : ℕ} (ρ : Restriction n) (v : Fin n) (b : Bool)
    (hv : ρ v = none) :
    Restriction.numFree (Function.update ρ v (some b)) + 1 = ρ.numFree := by
  classical
  have hv_mem : v ∈ ρ.freeVars := by
    simp [Restriction.freeVars, hv]
  have hsub : Restriction.freeVars (Function.update ρ v (some b)) = ρ.freeVars.erase v := by
    ext i
    simp only [Restriction.freeVars, Finset.mem_filter, Finset.mem_univ, true_and,
               Finset.mem_erase]
    by_cases hi : i = v
    · subst hi; simp [Function.update, hv]
    · simp [hi]
  have hcard : Restriction.numFree (Function.update ρ v (some b)) =
      (ρ.freeVars.erase v).card := by
    unfold Restriction.numFree; rw [hsub]
  rw [hcard, Finset.card_erase_of_mem hv_mem]
  unfold Restriction.numFree
  have hpos : 0 < ρ.freeVars.card := Finset.card_pos.mpr ⟨v, hv_mem⟩
  omega

/-- `processClauseLits` viewed on σ: if `ρ₀` and `σ` agree on free variables
    (same `freeVars` set), and the first literal's variable is free in `ρ₀`,
    then after one recursion step, σ's `numFree` is reduced by at most 1. More
    precisely, we track the exact relationship between path consumption, ρ₀
    updates, and σ updates. -/
private lemma processClauseLits_freeVars_agree {n : ℕ}
    (lits : List (Literal n × ℕ)) (path : List (Fin n × Bool))
    (ρ₀ σ : Restriction n)
    (hagree : ∀ v, ρ₀ v = none ↔ σ v = none) :
    ∀ v, (processClauseLits lits path ρ₀ σ).2.1 v = none ↔
         (processClauseLits lits path ρ₀ σ).2.2.1 v = none := by
  induction lits generalizing path ρ₀ σ with
  | nil => intro v; simp [processClauseLits]; exact hagree v
  | cons hd tl ih =>
    cases path with
    | nil => intro v; simp [processClauseLits]; exact hagree v
    | cons p ps =>
      simp only [processClauseLits]
      apply ih
      intro v
      by_cases heq : v = hd.1.var
      · subst heq; simp [Function.update]
      · simp [Function.update_of_ne heq]; exact hagree v

/-- `processClauseLits` at the σ component: numFree decreases by `min(lits.length, path.length)`
    under the invariants that `ρ₀` and `σ` have the same free variables, and
    each processed literal's variable is free in the current `ρ₀`. -/
private lemma processClauseLits_numFree_σ {n : ℕ}
    (lits : List (Literal n × ℕ)) (path : List (Fin n × Bool))
    (ρ₀ σ : Restriction n)
    (hagree : ∀ v, ρ₀ v = none ↔ σ v = none)
    (hfree : ∀ p ∈ lits, ρ₀ p.1.var = none)
    (hdistinct : lits.Pairwise (fun p q => p.1.var ≠ q.1.var)) :
    (processClauseLits lits path ρ₀ σ).2.2.1.numFree + min lits.length path.length =
      σ.numFree := by
  classical
  induction lits generalizing path ρ₀ σ with
  | nil => simp [processClauseLits]
  | cons hd tl ih =>
    cases path with
    | nil => simp [processClauseLits]
    | cons p ps =>
      simp only [processClauseLits, List.length_cons]
      have hhd : ρ₀ hd.1.var = none := hfree hd (by simp)
      have hhdσ : σ hd.1.var = none := (hagree _).mp hhd
      have hagree' : ∀ v,
          (Function.update ρ₀ hd.1.var (some p.2)) v = none ↔
          (Function.update σ hd.1.var (some (!hd.1.neg))) v = none := by
        intro v
        by_cases heq : v = hd.1.var
        · subst heq; simp [Function.update]
        · simp [Function.update_of_ne heq]; exact hagree v
      have hfree' : ∀ q ∈ tl,
          (Function.update ρ₀ hd.1.var (some p.2)) q.1.var = none := by
        intro q hq
        have hneq : q.1.var ≠ hd.1.var := by
          have := List.rel_of_pairwise_cons hdistinct hq
          exact fun h => this h.symm
        rw [Function.update_of_ne hneq]
        exact hfree q (by simp [hq])
      have hdistinct' : tl.Pairwise (fun p q => p.1.var ≠ q.1.var) :=
        List.Pairwise.of_cons hdistinct
      have hih := ih ps (Function.update ρ₀ hd.1.var (some p.2))
                    (Function.update σ hd.1.var (some (!hd.1.neg)))
                    hagree' hfree' hdistinct'
      have hupd :
          Restriction.numFree (Function.update σ hd.1.var (some (!hd.1.neg))) + 1 =
            σ.numFree := numFree_update_free σ hd.1.var (!hd.1.neg) hhdσ
      omega

/-- If `dtDepth(restrictFn f.eval ρ) > d`, then the canonical DT path has length ≥ d. -/
private lemma canonicalDTree_deepPath_length_ge {n : ℕ} (f : DNF n)
    (ρ : Restriction n) (d : ℕ) (hbad : IsBadRestriction f.eval d ρ) :
    d < (canonicalDTree f ρ).deepPath.length := by
  rw [DecisionTree.length_deepPath]
  have h1 : dtDepth (restrictFn f.eval ρ) > d := hbad
  have h2 : (canonicalDTree f ρ).depth ≥ dtDepth (restrictFn f.eval ρ) :=
    canonicalDTree_depth_ge f ρ
  omega

/-- The path used by `razborovEncode` has length exactly `d` when `ρ` is bad. -/
private lemma razborovEncode_path_length {n : ℕ} (f : DNF n) (ρ : Restriction n)
    (d : ℕ) (hbad : IsBadRestriction f.eval d ρ) :
    ((canonicalDTree f ρ).deepPath.take d).length = d := by
  have hge : d ≤ (canonicalDTree f ρ).deepPath.length :=
    Nat.le_of_lt (canonicalDTree_deepPath_length_ge f ρ d hbad)
  rw [List.length_take]
  omega

/-! ### Sub-lemmas for the path-consumption invariant -/

/-- `processClauseLits` consumes exactly `min lits.length path.length` path
    entries: the remaining path length equals `path.length - min(...)`. -/
private lemma processClauseLits_path_length_eq {n : ℕ}
    (lits : List (Literal n × ℕ)) (path : List (Fin n × Bool))
    (ρ₀ σ : Restriction n) :
    (processClauseLits lits path ρ₀ σ).1.length + min lits.length path.length =
      path.length := by
  induction lits generalizing path ρ₀ σ with
  | nil => simp [processClauseLits]
  | cons hd tl ih =>
    cases path with
    | nil => simp [processClauseLits]
    | cons p ps =>
      simp only [processClauseLits, List.length_cons]
      have hih := ih ps (Function.update ρ₀ hd.1.var (some p.2))
                       (Function.update σ hd.1.var (some (!hd.1.neg)))
      omega


/-- Updating a variable to `some b` decreases `numFree` by at most 1. -/
private lemma numFree_update_some_ge {n : ℕ} (ρ : Restriction n) (v : Fin n) (b : Bool) :
    Restriction.numFree (Function.update ρ v (some b)) + 1 ≥ ρ.numFree := by
  classical
  by_cases hv : ρ v = none
  · have := numFree_update_free ρ v b hv
    omega
  · -- ρ v = some _, so freeVars of the update equals freeVars of ρ
    have heq : Restriction.freeVars (Function.update ρ v (some b)) = ρ.freeVars := by
      ext i
      simp only [Restriction.freeVars, Finset.mem_filter, Finset.mem_univ, true_and,
                 Option.isNone_iff_eq_none]
      by_cases hiv : i = v
      · subst hiv
        constructor
        · intro h; simp [Function.update] at h
        · intro h; exact absurd h hv
      · rw [Function.update_of_ne hiv]
    have : Restriction.numFree (Function.update ρ v (some b)) = ρ.numFree := by
      unfold Restriction.numFree; rw [heq]
    omega

/-- **Key path-length bound**: if the initial path length is at most `ρ₀.numFree`,
    then after `processClauseLits`, the remaining path length is at most the
    updated `ρ₀`'s `numFree`. This uses the fact that each recursive step
    decreases both the path length and `numFree` by at most 1 (path by
    exactly 1, numFree by 0 or 1). -/
private lemma processClauseLits_remaining_le_numFree {n : ℕ}
    (lits : List (Literal n × ℕ)) (path : List (Fin n × Bool))
    (ρ₀ σ : Restriction n)
    (h0 : path.length ≤ ρ₀.numFree) :
    (processClauseLits lits path ρ₀ σ).1.length ≤
      (processClauseLits lits path ρ₀ σ).2.1.numFree := by
  induction lits generalizing path ρ₀ σ with
  | nil => simpa [processClauseLits] using h0
  | cons hd tl ih =>
    cases path with
    | nil =>
      simp [processClauseLits]
    | cons p ps =>
      simp only [processClauseLits]
      -- Remaining path length ≤ ρ₀'.numFree where ρ₀' = update ρ₀ hd.1.var (some p.2)
      have hupd : Restriction.numFree
          (Function.update ρ₀ hd.1.var (some p.2)) + 1 ≥ ρ₀.numFree :=
        numFree_update_some_ge ρ₀ hd.1.var p.2
      have hps_len : ps.length ≤
          Restriction.numFree (Function.update ρ₀ hd.1.var (some p.2)) := by
        have : (p :: ps).length = ps.length + 1 := rfl
        omega
      exact ih ps _ _ hps_len

/-- If every clause of `f` is killed by `ρ`, the canonical decision tree for
    `f|ρ` is `.leaf false` and hence has depth 0. -/
private lemma canonicalDTree_depth_zero_of_killed {n : ℕ} (f : DNF n)
    (ρ : Restriction n) (h : ∀ t ∈ f, Term.killedBy t ρ) :
    (canonicalDTree f ρ).depth = 0 := by
  unfold canonicalDTree
  -- `canonicalDTree.go f (ρ.numFree + 1) ρ` hits the `fuel + 1` branch,
  -- and the first `if` is satisfied by hypothesis, so returns `.leaf false`.
  set fuel := ρ.numFree
  show (canonicalDTree.go f (fuel + 1) ρ).depth = 0
  simp only [canonicalDTree.go]
  rw [dif_pos h]
  rfl

/-- If some clause of `f` is fixed by `ρ`, the canonical decision tree for
    `f|ρ` is `.leaf true` and hence has depth 0. -/
private lemma canonicalDTree_depth_zero_of_fixed {n : ℕ} (f : DNF n)
    (ρ : Restriction n) (h : ∃ t ∈ f, Term.fixedBy t ρ) :
    (canonicalDTree f ρ).depth = 0 := by
  unfold canonicalDTree
  set fuel := ρ.numFree
  show (canonicalDTree.go f (fuel + 1) ρ).depth = 0
  simp only [canonicalDTree.go]
  by_cases hkill : ∀ t ∈ f, Term.killedBy t ρ
  · rw [dif_pos hkill]; rfl
  · rw [dif_neg hkill, dif_pos h]; rfl

/-- `IsCanonicalPath f ρ path` says `path` is an initial segment of the
    canonical DT's deepest root-to-leaf path for `f|ρ`. Equivalently, `path`
    equals the first `path.length` entries of `(canonicalDTree f ρ).deepPath`.

    This is the true invariant carried by the Razborov encoder: the encoder
    walks `(canonicalDTree f ρ).deepPath.take d`, so at every recursive step,
    the remaining tail is still a prefix of a canonical DT's deepPath — just
    for the updated restriction that results from the `processClauseLits`
    steps. -/
private def IsCanonicalPath {n : ℕ} (f : DNF n) (ρ : Restriction n)
    (path : List (Fin n × Bool)) : Prop :=
  path = (canonicalDTree f ρ).deepPath.take path.length

/-
The filter of `zipIdx` by a predicate on the first component has the same
    length as the filter of the original list by the same predicate.
-/
private lemma zipIdx_filter_length {n : ℕ} (t : Term n)
    (p : Literal n → Bool) :
    (t.zipIdx.filter (fun x => p x.1)).length = (t.filter p).length := by
  induction' t using List.reverseRecOn with t ih;
  · rfl;
  · grind

/-
Accessing the first component of the k-th element of the filtered zipIdx
    gives the same result as the k-th element of the filtered list.
-/
private lemma zipIdx_filter_getElem_fst {n : ℕ} (t : Term n)
    (p : Literal n → Bool) (k : ℕ)
    (hk1 : k < (t.zipIdx.filter (fun x => p x.1)).length)
    (hk2 : k < (t.filter p).length) :
    ((t.zipIdx.filter (fun x => p x.1))[k]'hk1).1 = (t.filter p)[k]'hk2 := by
  -- By definition of `List.zipIdx`, the first component of the k-th element in the filtered list is the k-th element of the original list.
  have h_zipIdx : ∀ (t : Term n) (p : Literal n → Bool), List.map (fun x => x.1) (List.filter (fun x => p x.1) (List.zipIdx t)) = List.filter p t := by
    intros t p;
    induction' t using List.reverseRecOn with t ih;
    · rfl;
    · grind;
  grind

/-
**Structural match between canonicalDTree.deepPath and the first alive
    clause's free literals** (sub-sorry).

    When `f.find?` returns clause `t`, and the filtered (zipIdx) list of `t`'s
    free literals under `ρ` is `flis`, the prefix of `(canonicalDTree f ρ).deepPath`
    of length `flis.length` has variables matching the literals in `flis` exactly,
    in order. This is because `canonicalDTree.go` builds `termSubTree t ρ cont`,
    which branches on each free literal of `t` in clause order.

    Isolated as a single, precisely-stated sub-sorry.
-/
private lemma canonicalDTree_deepPath_match_freeLits {n : ℕ} (f : DNF n)
    (ρ : Restriction n) (t : Term n)
    (hfind : f.find? (fun t => decide (¬Term.killedBy t ρ)) = some t)
    (hnd : ∀ l₁ ∈ t, ∀ l₂ ∈ t, l₁.var = l₂.var → l₁ = l₂)
    (hnodup : t.Nodup)
    (k : ℕ)
    (flis : List (Literal n × ℕ))
    (hflis : flis = (t.zipIdx).filter (fun p => decide (p.1.var ∈ ρ.freeVars)))
    (hk_flis : k < flis.length)
    (hk_path : k < (canonicalDTree f ρ).deepPath.length) :
    ((canonicalDTree f ρ).deepPath[k]'hk_path).1 = (flis[k]'hk_flis).1.var := by
  have halive : ¬ (∀ t ∈ f, Term.killedBy t ρ) ∧ ¬ (∃ t ∈ f, Term.fixedBy t ρ) := by
    constructor <;> contrapose! hk_path <;> simp_all +decide [ Term.killedBy, Term.fixedBy ] ;
    · grind;
    · have h_depth_zero : (canonicalDTree f ρ).depth = 0 := by
        apply SwitchingLemma2.canonicalDTree_depth_zero_of_fixed f ρ hk_path
      generalize_proofs at *; (
      have h_depth_zero : ∀ (T : DecisionTree n), T.depth = 0 → T.deepPath.length = 0 := by
        intros T hT_depth_zero
        have hT_leaf : T = .leaf true ∨ T = .leaf false := by
          cases T <;> simp_all +decide [ DecisionTree.depth ]
        generalize_proofs at *; (
        rcases hT_leaf with ( rfl | rfl ) <;> rfl)
      generalize_proofs at *; (
      exact le_trans ( h_depth_zero _ ‹_› |> le_of_eq ) ( Nat.zero_le _ )));
  -- Apply the lemma termSubTree_deepPath_var_match with the pairwise distinctness of t.
  have h_pairwise : t.Pairwise (fun l₁ l₂ => l₁.var ≠ l₂.var) := by
    refine' List.Pairwise.imp_of_mem _ hnodup;
    exact fun { a b } ha hb hab h => hab <| hnd a ha b hb h;
  have := canonicalDTree_alive_eq_termSubTree' f ρ halive.1 halive.2 t hfind;
  have := termSubTree_deepPath_var_match t ρ (fun ρ' => if decide (Term.fixedBy t ρ') = true then DecisionTree.leaf true else SwitchingLemma2.canonicalDTree.go f ρ.numFree ρ') h_pairwise k ?_ ?_ <;> simp_all +decide ;
  any_goals rw [ ← zipIdx_filter_length ] ; simp +decide [ hk_flis ];
  rw [ ← zipIdx_filter_getElem_fst ]

/-
**Structural descent lemma**: `IsCanonicalPath` is preserved by
    `processClauseLits` when the literal variables match the path's head
    variables in order — which is guaranteed when `lits` are the free
    literals of the first alive clause and `path` is a canonical path
    descending through those literals.

    The remaining path from `processClauseLits` is the drop of the input path.
-/
private lemma processClauseLits_fst_eq_drop {n : ℕ}
    (lits : List (Literal n × ℕ)) (path : List (Fin n × Bool))
    (ρ₀ σ : Restriction n) :
    (processClauseLits lits path ρ₀ σ).1 = path.drop (min lits.length path.length) := by
  induction' lits with hd tl hl generalizing path ρ₀ σ;
  · cases path <;> aesop;
  · cases path <;> simp_all +decide [ processClauseLits ]

/-
`processClauseLits`'s ρ₀ output loses exactly `min lits.length path.length`
    free variables, provided every literal's variable is free in `ρ₀` and the
    literal variables are pairwise distinct.
-/
private lemma processClauseLits_numFree_ρ_eq {n : ℕ}
    (lits : List (Literal n × ℕ)) (path : List (Fin n × Bool))
    (ρ₀ σ : Restriction n)
    (hfree : ∀ p ∈ lits, ρ₀ p.1.var = none)
    (hdistinct : lits.Pairwise (fun p q => p.1.var ≠ q.1.var)) :
    (processClauseLits lits path ρ₀ σ).2.1.numFree + min lits.length path.length = ρ₀.numFree := by
  induction' lits with hd tl hl generalizing path ρ₀ σ;
  · cases path <;> aesop;
  · rcases path with ( _ | ⟨ p, ps ⟩ ) <;> simp_all +decide;
    · rfl;
    · convert congr_arg ( · + 1 ) ( hl ps ( Function.update ρ₀ hd.1.var ( some p.2 ) ) ( Function.update σ hd.1.var ( some ( !hd.1.neg ) ) ) ( fun a b hab => ?_ ) ) using 1;
      · rw [ numFree_update_free ] ; aesop;
      · rw [Function.update_of_ne (Ne.symm (hdistinct.1 a b hab))]; exact hfree.2 a b hab

/-
The termSubTree deepPath, after dropping the free-literal prefix, equals
    the continuation's deepPath at the processClauseLits-updated restriction.
    This connects the canonical DTree structure to the encoding's restriction
    update.
-/
private lemma processClauseLits_termSubTree_drop {n : ℕ} :
    ∀ (t : Term n) (ρ₀ σ : Restriction n)
      (cont : Restriction n → DecisionTree n)
      (_hdistinct : t.Pairwise (fun l₁ l₂ => l₁.var ≠ l₂.var))
      (path : List (Fin n × Bool))
      (lits : List (Literal n × ℕ))
      (hlits_len : lits.length = (t.filter (fun l => decide (l.var ∈ ρ₀.freeVars))).length)
      (_hlits_match : ∀ k (hk : k < lits.length),
        (lits[k]'hk).1 = (t.filter (fun l => decide (l.var ∈ ρ₀.freeVars)))[k]'(by omega))
      (_hpath_take : path = (termSubTree t ρ₀ cont).deepPath.take path.length)
      (_hfreeLen_le : lits.length ≤ path.length)
      (_hdp_len : path.length ≤ (termSubTree t ρ₀ cont).deepPath.length),
    (termSubTree t ρ₀ cont).deepPath.drop lits.length =
      (cont (processClauseLits lits path ρ₀ σ).2.1).deepPath := by
  intros t ρ₀ σ cont hdistinct path lits hlits_len hlits_match hpath hlits_le_path hpath_le_depth;
  induction' t with l rest ih generalizing ρ₀ σ cont path lits;
  · cases lits with
    | nil => simp [termSubTree, processClauseLits]
    | cons => simp at hlits_len;
  · by_cases hfree : l.var ∈ ρ₀.freeVars;
    · obtain ⟨b, hb⟩ : ∃ b : Bool, (termSubTree (l :: rest) ρ₀ cont).deepPath = (l.var, b) :: (termSubTree rest (Function.update ρ₀ l.var (some b)) cont).deepPath :=
        termSubTree_deepPath_head_free l rest ρ₀ cont hfree
      obtain ⟨lits_hd, lits_tl, hlits⟩ : ∃ lits_hd lits_tl, lits = lits_hd :: lits_tl ∧ lits_hd.1 = l := by
        rcases lits <;> simp +decide [ List.filter_cons ] at *;
        · grind;
        · simpa [ hfree ] using hlits_match 0 (by omega);
      obtain ⟨path_hd, path_tl, hpath⟩ : ∃ path_hd path_tl, path = (l.var, b) :: path_tl ∧ path_hd = (l.var, b) := by
        rcases path with ( _ | ⟨ x, _ | ⟨ y, path ⟩ ⟩ ) <;> simp +decide [ hb ] at hlits_le_path hpath_le_depth ⊢;
        · grind;
        · grind;
        · grind;
      specialize ih ( Function.update ρ₀ l.var ( some b ) ) ( Function.update σ l.var ( some ( !l.neg ) ) ) cont ( by
        exact List.pairwise_cons.mp hdistinct |>.2 ) path_tl lits_tl ( by
        simp +decide [ hlits, hfree ] at hlits_len ⊢;
        convert hlits_len using 2;
        apply filter_free_update_eq;
        exact fun x hx => by have := List.pairwise_cons.mp hdistinct; exact fun h => this.1 x hx <| by simp +decide [ h ] ; ) ( by
        all_goals generalize_proofs at *;
        intro k hk;
        convert hlits_match ( k + 1 ) ( by
          grind ) using 1
        generalize_proofs at *;
        · simp +decide [ hlits ];
        · all_goals generalize_proofs at *;
          simp +decide [ hfree ];
          congr! 1;
          refine' List.filter_congr fun x hx => _;
          by_cases h : x.var = l.var <;> simp +decide [ h ];
          · exact absurd ( List.pairwise_cons.mp hdistinct |>.1 x hx ) ( by simp +decide [ h ] );
          · simp +decide [ Restriction.freeVars, Function.update_apply, h ] ) ( by
        grind +ring ) ( by
        grind ) ( by
        grind );
      rw [ hlits.1, hb ];
      rw [ hpath.1 ];
      rw [ processClauseLits ];
      simp +decide [ hlits.2 ] at * ; tauto;
    · simp +decide [ termSubTree_cons_nonfree _ _ _ _ hfree ] at *;
      grind

set_option maxHeartbeats 1600000 in
private lemma canonicalPath_preserve_processClauseLits {n : ℕ} (f : DNF n)
    (lits : List (Literal n × ℕ)) (path : List (Fin n × Bool))
    (ρ₀ σ : Restriction n)
    (hcanon : IsCanonicalPath f ρ₀ path)
    (_hmatch : ∀ (k : ℕ) (hk : k < min lits.length path.length),
      (lits[k]'(by omega)).1.var = (path[k]'(by omega)).1)
    -- Extra context for the proof:
    (t : Term n)
    (hfind : f.find? (fun t => decide (¬Term.killedBy t ρ₀)) = some t)
    (hnd_t : ∀ l₁ ∈ t, ∀ l₂ ∈ t, l₁.var = l₂.var → l₁ = l₂)
    (hnodup_t : t.Nodup)
    (hdepth : path.length ≤ (canonicalDTree f ρ₀).depth)
    (hlits_eq : lits = (t.zipIdx).filter (fun p => decide (p.1.var ∈ ρ₀.freeVars))) :
    IsCanonicalPath f (processClauseLits lits path ρ₀ σ).2.1
        (processClauseLits lits path ρ₀ σ).1 ∧
    (processClauseLits lits path ρ₀ σ).1.length ≤
      (canonicalDTree f (processClauseLits lits path ρ₀ σ).2.1).depth := by
  have hrem := processClauseLits_fst_eq_drop lits path ρ₀ σ
  by_cases hge : lits.length ≥ path.length
  · -- All path entries consumed; remaining path is []
    have : min lits.length path.length = path.length := Nat.min_eq_right (by omega)
    rw [hrem, this, List.drop_length]
    exact ⟨by simp [IsCanonicalPath], Nat.zero_le _⟩
  · -- All lits consumed; remaining path = path.drop lits.length
    push_neg at hge
    have hmin : min lits.length path.length = lits.length := Nat.min_eq_left (by omega)
    rw [hrem, hmin]
    -- Establish alive conditions
    have hpath_pos : 0 < path.length := by omega
    have hdepth_pos : 0 < (canonicalDTree f ρ₀).depth := by omega
    have h_not_all_killed : ¬ ∀ t ∈ f, Term.killedBy t ρ₀ := by
      intro hall
      have := canonicalDTree_depth_zero_of_killed f ρ₀ hall
      omega
    have h_not_fixed : ¬ ∃ t ∈ f, Term.fixedBy t ρ₀ := by
      intro ⟨t', ht', hfix'⟩
      have := canonicalDTree_depth_zero_of_fixed f ρ₀ ⟨t', ht', hfix'⟩
      omega
    -- Rewrite canonicalDTree as termSubTree
    have hdt := canonicalDTree_alive_eq_termSubTree' f ρ₀ h_not_all_killed h_not_fixed t hfind
    -- Get pairwise distinct vars for t
    have ht_pairwise : t.Pairwise (fun l₁ l₂ => l₁.var ≠ l₂.var) := by
      rw [List.pairwise_iff_getElem]
      intro i j hi hj hij heq
      have := hnd_t t[i] (List.getElem_mem _) t[j] (List.getElem_mem _) heq
      exact absurd ((List.Nodup.getElem_inj_iff hnodup_t).mp this) (by omega)
    set cont := (fun ρ' => if decide (Term.fixedBy t ρ') then DecisionTree.leaf true
      else canonicalDTree.go f ρ₀.numFree ρ') with hcont_def
    set ρ' := (processClauseLits lits path ρ₀ σ).2.1 with hρ'_def
    have ht_mem : t ∈ f := List.mem_of_find?_eq_some hfind
    -- lits.length = |free lits of t|
    have hfree_len : (t.filter (fun l => decide (l.var ∈ ρ₀.freeVars))).length = lits.length := by
      rw [hlits_eq, ← zipIdx_filter_length]
    -- lits match the free literals of t
    have hlits_match : ∀ k (hk : k < lits.length),
        (lits[k]'hk).1 = (t.filter (fun l => decide (l.var ∈ ρ₀.freeVars)))[k]'(by omega) := by
      intro k hk
      have hk1 : k < (t.zipIdx.filter (fun x => decide (x.1.var ∈ ρ₀.freeVars))).length := by
        rw [← hlits_eq]; exact hk
      have hk2 : k < (t.filter (fun l => decide (l.var ∈ ρ₀.freeVars))).length := by omega
      have := zipIdx_filter_getElem_fst t (fun l => decide (l.var ∈ ρ₀.freeVars)) k hk1 hk2
      simp only [hlits_eq] at this ⊢; exact this
    -- path = termSubTree deepPath take
    have hpath_take : path = (termSubTree t ρ₀ cont).deepPath.take path.length := by
      conv_lhs => rw [hcanon]; rw [hdt]
    -- path.length ≤ deepPath.length
    have hdp_len : path.length ≤ (termSubTree t ρ₀ cont).deepPath.length := by
      rw [← hdt]; rw [DecisionTree.length_deepPath]; exact hdepth
    -- deepPath.drop lits.length = (cont ρ').deepPath
    have hdp_drop : (canonicalDTree f ρ₀).deepPath.drop lits.length = (cont ρ').deepPath := by
      rw [hdt]
      exact processClauseLits_termSubTree_drop t ρ₀ σ cont ht_pairwise path lits
        hfree_len.symm hlits_match hpath_take (by omega) hdp_len
    -- numFree bound for ρ'
    -- All literal variables are free in ρ₀
    have hlits_free : ∀ p ∈ lits, ρ₀ p.1.var = none := by
      intro p hp
      rw [hlits_eq] at hp
      have := List.mem_filter.mp hp
      simp [Restriction.freeVars, Finset.mem_filter] at this
      exact this.2
    -- Literal variables are pairwise distinct
    have hlits_distinct : lits.Pairwise (fun p q => p.1.var ≠ q.1.var) := by
      rw [hlits_eq]
      have : t.Pairwise (fun l₁ l₂ : Literal n => l₁.var ≠ l₂.var) := by
        rw [List.pairwise_iff_getElem]
        intro i j hi hj hij heq_var
        have heq := hnd_t t[i] (List.getElem_mem _) t[j] (List.getElem_mem _) heq_var
        exact absurd ((List.Nodup.getElem_inj_iff hnodup_t).mp heq) (by omega)
      exact List.Pairwise.filter _ (by
        rw [List.pairwise_iff_getElem] at this ⊢
        intro i j hi hj hij
        rw [List.length_zipIdx] at hi hj
        rw [List.getElem_zipIdx, List.getElem_zipIdx]; simp
        exact this i j hi hj hij)
    have hfuel_ok : ρ₀.numFree ≥ ρ'.numFree + 1 := by
      have := processClauseLits_numFree_ρ_eq lits path ρ₀ σ hlits_free hlits_distinct
      rw [hmin] at this
      -- We need lits.length ≥ 1 to conclude.
      -- If lits is empty, the else branch gives trivial result
      by_cases hlits_empty : lits.length = 0
      · -- lits.length = 0 is impossible: all free lits of t = 0 means t is fixedBy ρ₀,
        -- contradicting h_not_fixed.
        exfalso; apply h_not_fixed
        have hfree_empty : (t.filter (fun l => decide (l.var ∈ ρ₀.freeVars))).length = 0 := by omega
        have ht_nk : ¬Term.killedBy t ρ₀ := by
          have := List.find?_some hfind; simp at this; exact this
        exact ⟨t, ht_mem, fun l hl => by
          have hv_not_free : l.var ∉ ρ₀.freeVars := by
            intro hfv
            have hmem : l ∈ t.filter (fun l => decide (l.var ∈ ρ₀.freeVars)) :=
              List.mem_filter.mpr ⟨hl, by simp [hfv]⟩
            exact absurd (List.length_pos_of_mem hmem) (by omega)
          simp only [Restriction.freeVars, Finset.mem_filter, Finset.mem_univ, true_and,
                     Option.isNone_iff_eq_none] at hv_not_free
          cases hv : ρ₀ l.var with
          | none => exact absurd hv hv_not_free
          | some b =>
            unfold Literal.fixedBy; rw [hv]
            congr 1
            by_contra hneq
            exact ht_nk ⟨l, hl, by
              unfold Literal.killedBy; rw [hv]; congr 1
              revert hneq; cases b <;> cases l.neg <;> simp⟩⟩
      · rw [← hρ'_def] at this; omega
    -- cont ρ' = canonicalDTree f ρ'
    have hcont_canon := cont_eq_canonicalDTree f ρ₀ t ht_mem ρ' hfuel_ok
    have hcont_dp : (cont ρ').deepPath = (canonicalDTree f ρ').deepPath :=
      congr_arg DecisionTree.deepPath hcont_canon
    -- path.drop lits.length = (deepPath.drop lits.length).take (path.length - lits.length)
    have hpath_drop_eq : List.drop lits.length path =
        ((canonicalDTree f ρ₀).deepPath.drop lits.length).take (path.length - lits.length) := by
      conv_lhs => rw [hcanon]
      exact List.drop_take
    -- Combine
    rw [hpath_drop_eq, hdp_drop, hcont_dp]
    refine ⟨?_, ?_⟩
    · -- IsCanonicalPath: take of deepPath is a take of deepPath
      simp [IsCanonicalPath, List.length_take]
    · -- depth bound: take length ≤ depth
      simp [List.length_take, DecisionTree.length_deepPath]

/-- **Pairwise distinct vars**: when `t` has no duplicate literals and any two
    literals in `t` with the same variable are equal (i.e., `hnd`), the filter
    of `t.zipIdx` by a free-var predicate has pairwise distinct variables. -/
private lemma processClauseLits_freeLits_pairwise_var {n : ℕ}
    (t : Term n) (ρ₀ : Restriction n) (ht_nodup : t.Nodup)
    (hnd : ∀ l₁ ∈ t, ∀ l₂ ∈ t, l₁.var = l₂.var → l₁ = l₂) :
    ((t.zipIdx).filter
        (fun p => decide (p.1.var ∈ ρ₀.freeVars))).Pairwise
      (fun p q : Literal n × ℕ => p.1.var ≠ q.1.var) := by
  -- First, the zipIdx is pairwise distinct in both components.
  have hzip_pairwise : t.zipIdx.Pairwise
      (fun p q : Literal n × ℕ => p.1 = q.1 → p.2 ≠ q.2) := by
    rw [List.pairwise_iff_getElem]
    intro i j hi hj hij
    rw [List.length_zipIdx] at hi hj
    rw [List.getElem_zipIdx, List.getElem_zipIdx]
    intro _; simp; omega
  -- Distinct literals in `t` have distinct variables under hnd.
  have ht_var_pairwise : t.Pairwise (fun l₁ l₂ : Literal n => l₁.var ≠ l₂.var) := by
    rw [List.pairwise_iff_getElem]
    intro i j hi hj hij heq_var
    have hi_mem : t[i] ∈ t := List.getElem_mem _
    have hj_mem : t[j] ∈ t := List.getElem_mem _
    have heq : t[i] = t[j] := hnd t[i] hi_mem t[j] hj_mem heq_var
    -- But t is Nodup, so i = j, contradicting i < j.
    rw [List.nodup_iff_getElem?_ne_getElem?] at ht_nodup
    have := ht_nodup i j hij hj
    apply this
    rw [List.getElem?_eq_getElem hi, List.getElem?_eq_getElem hj, heq]
  -- Transport pairwise distinct vars from t to t.zipIdx.
  have hzip_var_pairwise : t.zipIdx.Pairwise
      (fun p q : Literal n × ℕ => p.1.var ≠ q.1.var) := by
    rw [List.pairwise_iff_getElem]
    intro i j hi hj hij
    rw [List.length_zipIdx] at hi hj
    rw [List.getElem_zipIdx, List.getElem_zipIdx]
    simp only
    rw [List.pairwise_iff_getElem] at ht_var_pairwise
    exact ht_var_pairwise i j hi hj hij
  -- The filter preserves pairwise-ness.
  exact List.Pairwise.filter _ hzip_var_pairwise

/-- **Key path-consumption invariant**: when `dtDepth(f|ρ₀) ≥ path.length`,
    `razborovEncode.go` fully consumes the path — it never terminates early
    via the "no alive clause" or "no free literal" branches — and the
    resulting σ has `numFree` decreased by exactly the initial `path.length`.

    The proof inducts on `fuel`, case-splits on `path` and the encoder's
    `find?`/`freeLitsIdx` branches, and defers two sub-properties to
    `canonicalPath_preserve_processClauseLits` and
    `processClauseLits_freeLits_pairwise_var`. -/
private lemma razborovEncode_go_numFree_invariant {n : ℕ}
    (f : DNF n) (w : ℕ)
    (hnd : ∀ t ∈ f, ∀ l₁ ∈ t, ∀ l₂ ∈ t, l₁.var = l₂.var → l₁ = l₂)
    (hnodup : ∀ t ∈ f, t.Nodup)
    (fuel : ℕ) (path : List (Fin n × Bool)) (ρ₀ σ : Restriction n)
    (hagree : ∀ v, ρ₀ v = none ↔ σ v = none)
    (hcanon : IsCanonicalPath f ρ₀ path)
    (hdepth : path.length ≤ (canonicalDTree f ρ₀).depth)
    (hfuel : path.length < fuel) :
    (razborovEncode.go f w fuel path ρ₀ σ []).1.numFree + path.length = σ.numFree := by
  induction fuel generalizing path ρ₀ σ with
  | zero => exact absurd hfuel (Nat.not_lt_zero _)
  | succ fuel ih =>
    cases path with
    | nil =>
      simp [razborovEncode.go]
    | cons step rest =>
      -- path.length = rest.length + 1 > 0, so (canonicalDTree f ρ₀).depth ≥ 1
      have hpath_pos : 0 < (step :: rest).length := Nat.succ_pos _
      have hdepth_pos : 0 < (canonicalDTree f ρ₀).depth :=
        Nat.lt_of_lt_of_le hpath_pos hdepth
      simp only [razborovEncode.go]
      -- Case split on find?
      cases hfind : f.find? (fun t => decide (¬Term.killedBy t ρ₀)) with
      | none =>
        -- All clauses killed by ρ₀ → dtDepth = 0, contradicting hdepth_pos.
        exfalso
        have hall : ∀ t ∈ f, Term.killedBy t ρ₀ := by
          intro t ht
          have hne := (List.find?_eq_none.mp hfind) t ht
          simp only [decide_not, Bool.not_eq_true', decide_eq_false_iff_not,
                     not_not] at hne
          exact hne
        have hdtd := canonicalDTree_depth_zero_of_killed f ρ₀ hall
        omega
      | some t_clause =>
        simp only []
        have ht_mem : t_clause ∈ f := List.mem_of_find?_eq_some hfind
        -- Build freeLitsIdx
        set fli := (t_clause.zipIdx).filter
          (fun p => decide (p.1.var ∈ ρ₀.freeVars)) with hfli_def
        cases hflicase : fli with
        | nil =>
          -- No free literal in t_clause under ρ₀. Then every literal of
          -- t_clause has ρ₀ fixed. Since ¬killedBy, t_clause is fixedBy ρ₀.
          -- So dtDepth(f|ρ₀) = 0, contradicting hdepth_pos.
          exfalso
          -- Extract ¬killedBy from find?.
          have hnk : ¬ Term.killedBy t_clause ρ₀ := by
            have := List.find?_eq_some_iff_append.mp hfind
            obtain ⟨h1, _⟩ := this
            simp only [decide_not, Bool.not_eq_true',
                       decide_eq_false_iff_not] at h1
            exact h1
          have hall_ne_none : ∀ l ∈ t_clause, ρ₀ l.var ≠ none := by
            intro l hl hnone
            -- Get an index of l in t_clause via getElem?.
            rw [List.mem_iff_getElem] at hl
            obtain ⟨k, hk_lt, hk_eq⟩ := hl
            -- (l, k) ∈ t_clause.zipIdx via mk_mem_zipIdx_iff_getElem?.
            have hmem_zip : (l, k) ∈ t_clause.zipIdx := by
              rw [List.mk_mem_zipIdx_iff_getElem?]
              rw [List.getElem?_eq_getElem hk_lt]
              exact Option.some_inj.mpr hk_eq
            have hmem_fli : (l, k) ∈ fli := by
              rw [hfli_def, List.mem_filter]
              refine ⟨hmem_zip, ?_⟩
              simp only [decide_eq_true_eq, Restriction.freeVars, Finset.mem_filter,
                         Finset.mem_univ, true_and]
              exact Option.isNone_iff_eq_none.mpr hnone
            rw [hflicase] at hmem_fli
            exact List.not_mem_nil hmem_fli
          -- For every literal, ρ₀ l.var = some (!l.neg) (since not none and not some l.neg).
          have hfixed : Term.fixedBy t_clause ρ₀ := by
            intro l hl
            show ρ₀ l.var = some (!l.neg)
            have hnn := hall_ne_none l hl
            -- ¬ killedBy means: not (∃ l ∈ t_clause, ρ₀ l.var = some l.neg).
            have hlk : ¬ Literal.killedBy l ρ₀ := by
              intro hk
              exact hnk ⟨l, hl, hk⟩
            unfold Literal.killedBy at hlk
            -- ρ₀ l.var ≠ none and ≠ some l.neg → = some (!l.neg)
            cases h : ρ₀ l.var with
            | none => exact absurd h hnn
            | some b =>
              cases hb : b
              · rcases Bool.eq_false_or_eq_true l.neg with hneg | hneg
                · rw [hneg]; rfl
                · rw [hneg] at hlk
                  rw [h, hb] at hlk
                  exact absurd rfl hlk
              · rcases Bool.eq_false_or_eq_true l.neg with hneg | hneg
                · rw [hneg] at hlk
                  rw [h, hb] at hlk
                  exact absurd rfl hlk
                · rw [hneg]; rfl
          have hdtd : (canonicalDTree f ρ₀).depth = 0 :=
            canonicalDTree_depth_zero_of_fixed f ρ₀ ⟨t_clause, ht_mem, hfixed⟩
          omega
        | cons fl fls =>
          simp only []
          set pcl := processClauseLits (fl :: fls) (step :: rest) ρ₀ σ with hpcl_def
          -- Apply accumulator lemma to strip the acc argument.
          simp only [List.nil_append]
          rw [encode_go_acc f w fuel pcl.1 pcl.2.1 pcl.2.2.1 (pcl.2.2.2 ++ [(w, false)])]
          -- Key facts about pcl:
          have hfree_pcl : ∀ p ∈ (fl :: fls), ρ₀ p.1.var = none := by
            intro p hp
            have hp_fli : p ∈ fli := by rw [hflicase]; exact hp
            rw [hfli_def] at hp_fli
            have h2 := (List.mem_filter.mp hp_fli).2
            simp only [decide_eq_true_eq, Restriction.freeVars, Finset.mem_filter,
                       Finset.mem_univ, true_and] at h2
            exact Option.isNone_iff_eq_none.mp h2
          have hdistinct_pcl : (fl :: fls).Pairwise
              (fun p q : Literal n × ℕ => p.1.var ≠ q.1.var) := by
            have := processClauseLits_freeLits_pairwise_var t_clause ρ₀
              (hnodup t_clause ht_mem) (hnd t_clause ht_mem)
            rw [← hfli_def, hflicase] at this
            exact this
          -- σ.numFree after pcl:
          have hσ_pcl : pcl.2.2.1.numFree + min (fl :: fls).length (step :: rest).length =
              σ.numFree :=
            processClauseLits_numFree_σ (fl :: fls) (step :: rest) ρ₀ σ
              hagree hfree_pcl hdistinct_pcl
          -- ρ₀' agreement with σ' after pcl:
          have hagree_pcl : ∀ v, pcl.2.1 v = none ↔ pcl.2.2.1 v = none :=
            processClauseLits_freeVars_agree (fl :: fls) (step :: rest) ρ₀ σ hagree
          -- Canonical-path preservation (gives both canon and depth bound).
          -- The `hmatch` hypothesis (that each free literal's variable matches
          -- the canonical path's head variable) is a structural fact about
          -- `canonicalDTree`'s descent through `termSubTree` on the first alive
          -- clause.
          have hmatch_pcl : ∀ (k : ℕ)
              (hk : k < min (fl :: fls).length (step :: rest).length),
              ((fl :: fls)[k]'(by omega)).1.var =
              ((step :: rest)[k]'(by omega)).1 := by
            intro k hk
            have hk_path : k < (step :: rest).length := by
              simp only [lt_min_iff] at hk; exact hk.2
            have hk_flis : k < (fl :: fls).length := by
              simp only [lt_min_iff] at hk; exact hk.1
            have hk_lt_path_len : k < (canonicalDTree f ρ₀).deepPath.length := by
              rw [DecisionTree.length_deepPath]
              have hdpath := hdepth
              omega
            -- From hcanon : (step :: rest) = deepPath.take (step::rest).length,
            -- so for index k, (step::rest)[k] = deepPath[k].
            have hpath_get :
                ((step :: rest)[k]'hk_path).1 =
                ((canonicalDTree f ρ₀).deepPath[k]'hk_lt_path_len).1 := by
              have heq : (step :: rest) =
                  (canonicalDTree f ρ₀).deepPath.take (step :: rest).length := hcanon
              have hk_take : k < ((canonicalDTree f ρ₀).deepPath.take
                  (step :: rest).length).length := by
                rw [List.length_take]; omega
              have h1 : ((step :: rest)[k]'hk_path) =
                  ((canonicalDTree f ρ₀).deepPath.take (step :: rest).length)[k]'hk_take := by
                congr 1
              rw [h1, List.getElem_take]
            -- Apply the structural fact.
            have hflis_eq : (fl :: fls) =
                (t_clause.zipIdx).filter (fun p => decide (p.1.var ∈ ρ₀.freeVars)) := by
              rw [← hflicase, hfli_def]
            have hmatch :=
              canonicalDTree_deepPath_match_freeLits f ρ₀ t_clause hfind
                (hnd t_clause ht_mem) (hnodup t_clause ht_mem) k
                (fl :: fls) hflis_eq hk_flis hk_lt_path_len
            -- Combine: (fl :: fls)[k].1.var = deepPath[k].1 = (step::rest)[k].1
            exact hmatch.symm.trans hpath_get.symm
          have hpres_pcl :=
            canonicalPath_preserve_processClauseLits f (fl :: fls) (step :: rest)
              ρ₀ σ hcanon hmatch_pcl
              t_clause hfind (hnd t_clause ht_mem) (hnodup t_clause ht_mem)
              hdepth (by rw [← hflicase, hfli_def])
          have hcanon_pcl : IsCanonicalPath f pcl.2.1 pcl.1 := hpres_pcl.1
          have hdepth_pcl : pcl.1.length ≤
              (canonicalDTree f pcl.2.1).depth := hpres_pcl.2
          -- Length decomposition:
          have hlen_add : pcl.2.2.2.length + pcl.1.length ≤ (step :: rest).length :=
            processClauseLits_len_add (fl :: fls) (step :: rest) ρ₀ σ
          -- Fuel suffices for recursion:
          have hfuel_pcl : pcl.1.length < fuel := by
            have hstrict : pcl.1.length ≤ rest.length := by
              simp only [hpcl_def, processClauseLits]
              exact processClauseLits_path_le _ _ _ _
            have hlen_eq : (step :: rest).length = rest.length + 1 := rfl
            have hf : (step :: rest).length < fuel + 1 := hfuel
            omega
          -- Apply IH to the recursive call
          have hih := ih pcl.1 pcl.2.1 pcl.2.2.1 hagree_pcl hcanon_pcl hdepth_pcl hfuel_pcl
          -- Combine: we need
          --   (go f w fuel pcl.1 pcl.2.1 pcl.2.2.1 []).1.numFree + (step :: rest).length
          --     = σ.numFree
          -- from hih: (...).1.numFree + pcl.1.length = pcl.2.2.1.numFree
          -- and hσ_pcl: pcl.2.2.1.numFree + min ... = σ.numFree
          -- Need: pcl.1.length + min ((fl::fls).length) ((step::rest).length)
          --        = (step :: rest).length
          -- This is the tight version of processClauseLits_len_add; we assert
          -- it via hlen_add and the observation that when lits ≠ [] and
          -- path ≠ [], at least min(|lits|, |path|) steps are consumed, and
          -- in fact exactly min steps, with pcl.1.length = |path| - min.
          have htight : pcl.1.length + min (fl :: fls).length (step :: rest).length =
              (step :: rest).length :=
            processClauseLits_path_length_eq (fl :: fls) (step :: rest) ρ₀ σ
          show (razborovEncode.go f w fuel pcl.1 pcl.2.1 pcl.2.2.1 []).1.numFree +
              (step :: rest).length = σ.numFree
          omega

/-- **Structural lemma**: for a bad `s`-restriction, the encoder's γ-output
    (the σ component) is an `(s - d)`-restriction.

    Intuition: for a bad restriction, the canonical DT has depth > d, so the
    encoder's path has length exactly d. Each step in `processClauseLits`
    consumes one path entry and fixes exactly one previously-free variable
    in σ. Hence `γ.numFree = ρ.numFree - d = s - d`. -/
private lemma razborovEncode_fst_numFree_eq {n : ℕ} (f : DNF n) (w d : ℕ)
    (ρ : Restriction n) (s : ℕ) (hρ : IsRestriction s ρ)
    (hbad : IsBadRestriction f.eval d ρ) (hd : d ≤ s)
    (hnd : ∀ t ∈ f, ∀ l₁ ∈ t, ∀ l₂ ∈ t, l₁.var = l₂.var → l₁ = l₂)
    (hnodup : ∀ t ∈ f, t.Nodup) :
    IsRestriction (s - d) (razborovEncode f w d ρ).1 := by
  classical
  unfold IsRestriction at hρ ⊢
  -- Unfold razborovEncode.
  show (razborovEncode.go f w _ _ ρ ρ []).1.numFree = s - d
  set path := (canonicalDTree f ρ).deepPath.take d with hpath_def
  have hpath_len : path.length = d := razborovEncode_path_length f ρ d hbad
  -- Invariants for the go-lemma with ρ₀ = σ = ρ.
  have hagree : ∀ v, ρ v = none ↔ ρ v = none := fun _ => Iff.rfl
  -- `path` is defined as `(canonicalDTree f ρ).deepPath.take d`, so it is
  -- by construction a prefix of `deepPath` — i.e., `IsCanonicalPath`.
  have hcanon : IsCanonicalPath f ρ path := by
    show path = (canonicalDTree f ρ).deepPath.take path.length
    rw [hpath_len, hpath_def]
  -- Depth bound via `canonicalDTree_depth_ge` and `hbad`.
  have hdepth : path.length ≤ (canonicalDTree f ρ).depth := by
    rw [hpath_len]
    have h1 : dtDepth (restrictFn f.eval ρ) > d := hbad
    have h2 : (canonicalDTree f ρ).depth ≥ dtDepth (restrictFn f.eval ρ) :=
      canonicalDTree_depth_ge f ρ
    omega
  have hfuel : path.length < path.length + 1 := Nat.lt_succ_self _
  have hinv :=
    razborovEncode_go_numFree_invariant f w hnd hnodup (path.length + 1)
      path ρ ρ hagree hcanon hdepth hfuel
  -- hinv : (go ...).1.numFree + path.length = ρ.numFree
  rw [hpath_len] at hinv ⊢
  rw [hρ] at hinv
  -- hinv : (go ...).1.numFree + d = s
  omega

/-- **Razborov counting bound**. -/
private lemma bad_count_bound {n : ℕ} (f : DNF n) (w s d : ℕ)
    (hw : f.width ≤ w) (hd : d ≤ s)
    (hnd : ∀ t ∈ f, ∀ l₁ ∈ t, ∀ l₂ ∈ t, l₁.var = l₂.var → l₁ = l₂)
    (hnodup : ∀ t ∈ f, t.Nodup) :
    (Finset.univ.filter fun ρ : Restriction n =>
        IsRestriction s ρ ∧ IsBadRestriction f.eval d ρ).card ≤
    n.choose (s - d) * 2 ^ (n - (s - d)) * (4 * w) ^ d := by
  classical
  set S := (Finset.univ.filter fun ρ : Restriction n =>
      IsRestriction s ρ ∧ IsBadRestriction f.eval d ρ) with hS_def
  -- Partition S by the γ := (razborovEncode f w d ρ).1 image.
  have hfgamma : ∀ ρ ∈ S, (razborovEncode f w d ρ).1 ∈
      (Finset.univ.filter (fun γ : Restriction n => γ.numFree = s - d)) := by
    intro ρ hρ
    simp only [S, Finset.mem_filter, Finset.mem_univ, true_and] at hρ
    obtain ⟨hsρ, hbadρ⟩ := hρ
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact razborovEncode_fst_numFree_eq f w d ρ s hsρ hbadρ hd hnd hnodup
  rw [Finset.card_eq_sum_card_fiberwise hfgamma]
  -- Bound each fiber by (4 * w) ^ d using fiber_bound.
  have hfiber_le : ∀ γ ∈ (Finset.univ.filter
      (fun γ : Restriction n => γ.numFree = s - d)),
      (S.filter fun ρ => (razborovEncode f w d ρ).1 = γ).card ≤ (4 * w) ^ d := by
    intro γ _
    have hfib := fiber_bound f w s d hw hd hnd γ
    refine le_trans ?_ hfib
    apply Finset.card_le_card
    intro ρ hρ
    simp only [S, Finset.mem_filter, Finset.mem_univ, true_and] at hρ
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨hρ.1.1, hρ.1.2, hρ.2⟩
  calc ∑ γ ∈ (Finset.univ.filter (fun γ : Restriction n => γ.numFree = s - d)),
          (S.filter fun ρ => (razborovEncode f w d ρ).1 = γ).card
      ≤ ∑ _γ ∈ (Finset.univ.filter (fun γ : Restriction n => γ.numFree = s - d)),
          (4 * w) ^ d := Finset.sum_le_sum hfiber_le
    _ = (Finset.univ.filter (fun γ : Restriction n => γ.numFree = s - d)).card *
          (4 * w) ^ d := by rw [Finset.sum_const]; ring
    _ = n.choose (s - d) * 2 ^ (n - (s - d)) * (4 * w) ^ d := by
        rw [card_filter_numFree_eq n (s - d)]

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
    (hnd : ∀ t ∈ f, ∀ l₁ ∈ t, ∀ l₂ ∈ t, l₁.var = l₂.var → l₁ = l₂)
    (hnodup : ∀ t ∈ f, t.Nodup) :
    (Finset.univ.filter fun ρ : Restriction n =>
        IsRestriction s ρ ∧ IsBadRestriction f.eval d ρ).card * n ^ d ≤
    numSRestrictions n s * (10 * s * w) ^ d := by
  by_cases hds : d ≤ s
  · refine le_trans (Nat.mul_le_mul_right _ (bad_count_bound f w s d hw hds hnd hnodup)) ?_
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
        split_ifs <;> simp_all +decide [ Term.eval ];
        · simp_all +decide [ Literal.eval ];
          simp_all +decide [ List.any_eq, List.all_eq ];
        · simp_all +decide [ List.any_eq, Literal.eval ]
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
          · simp +decide [ *, Literal.eval ];
            grind +splitIndPred;
          · simp +decide [ *, Literal.eval ];
            grind;
      exact h_equiv T x

theorem switching_corollary {n : ℕ} (hn : 0 < n) (f : DNF n) (w s : ℕ)
    (hw : f.width ≤ w) (hs : 5 * s ≤ n)
    (hnd : ∀ t ∈ f, ∀ l₁ ∈ t, ∀ l₂ ∈ t, l₁.var = l₂.var → l₁ = l₂)
    (hnodup : ∀ t ∈ f, t.Nodup) :
    (Finset.univ.filter fun ρ : Restriction n =>
        IsRestriction s ρ ∧
        ¬ ∃ ψ : CNF n, ψ.width ≤ w ∧
          ∀ x, ψ.eval x = restrictFn f.eval ρ x).card * n ^ w ≤
    numSRestrictions n s * (10 * s * w) ^ w := by
  apply le_trans _ (switching_lemma hn f w s w hw hs hnd hnodup)
  apply Nat.mul_le_mul_right
  apply Finset.card_le_card
  intro ρ hρ
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hρ ⊢
  refine ⟨hρ.1, ?_⟩
  show dtDepth (restrictFn f.eval ρ) > w
  by_contra hgood; push_neg at hgood
  exact hρ.2 (dtDepth_le_implies_small_dnf_cnf _ w hgood).2

end SwitchingLemma2


/-!
# Håstad's Switching Lemma for CNFs

The switching lemma for CNFs, derived from the DNF version via De Morgan duality.

The key idea: negating a CNF produces a DNF of the same width, and decision tree depth
is invariant under negation of the computed function. Therefore the DNF switching lemma
immediately implies the CNF version.
-/

open Classical

/-! ## Literal negation -/

/-- Negate a literal by flipping its polarity. -/
def Literal.flipNeg {n : ℕ} (l : Literal n) : Literal n :=
  ⟨l.var, !l.neg⟩

@[simp]
lemma Literal.flipNeg_eval {n : ℕ} (l : Literal n) (x : Fin n → Bool) :
    l.flipNeg.eval x = !(l.eval x) := by
  simp only [Literal.flipNeg, Literal.eval]
  cases l.neg <;> simp

@[simp]
lemma Literal.flipNeg_var {n : ℕ} (l : Literal n) :
    l.flipNeg.var = l.var := rfl

lemma Literal.flipNeg_injective {n : ℕ} : Function.Injective (Literal.flipNeg (n := n)) := by
  intro l₁ l₂ h
  cases l₁; cases l₂
  simp [Literal.flipNeg] at h
  exact Literal.mk.injEq .. ▸ h

/-! ## De Morgan dual: CNF → DNF -/

/-- Convert a CNF to its De Morgan dual DNF by negating every literal.
    Each clause (disjunction) becomes a term (conjunction) with negated literals.
    `¬(∧ᵢ (∨ⱼ lᵢⱼ)) = ∨ᵢ (∧ⱼ ¬lᵢⱼ)` -/
def cnfToDualDNF {n : ℕ} (ψ : CNF n) : DNF n :=
  ψ.map (fun clause => clause.map Literal.flipNeg)

/-! ## Properties of the dual -/

lemma cnfToDualDNF_width {n : ℕ} (ψ : CNF n) :
    (cnfToDualDNF ψ).width = ψ.width := by
  simp only [cnfToDualDNF, DNF.width, CNF.width, Term.width,
    List.map_map, Function.comp_def, List.length_map]
  congr 1

lemma cnfToDualDNF_eval {n : ℕ} (ψ : CNF n) (x : Fin n → Bool) :
    (cnfToDualDNF ψ).eval x = !(ψ.eval x) := by
  simp only [cnfToDualDNF, DNF.eval, CNF.eval]
  induction ψ with
  | nil => simp
  | cons hd tl ih =>
    simp only [List.map_cons, List.any_cons, List.all_cons]
    rw [ih, Bool.not_and]
    congr 1
    simp only [Term.eval, CNF.evalClause]
    induction hd with
    | nil => simp
    | cons l tl' ih' =>
      simp only [List.map_cons, List.all_cons, List.any_cons, Literal.flipNeg_eval]
      rw [ih', Bool.not_or]

/-! ## Decision tree depth is invariant under negation -/

/-- Negate all leaves of a decision tree. -/
def DecisionTree.negateLeaves {n : ℕ} : DecisionTree n → DecisionTree n
  | .leaf b => .leaf (!b)
  | .branch v lo hi => .branch v (negateLeaves lo) (negateLeaves hi)

@[simp]
lemma DecisionTree.negateLeaves_eval {n : ℕ} (T : DecisionTree n) (x : Fin n → Bool) :
    T.negateLeaves.eval x = !(T.eval x) := by
  induction T with
  | leaf b => simp [negateLeaves, DecisionTree.eval]
  | branch v lo hi ih_lo ih_hi =>
    simp only [negateLeaves, DecisionTree.eval]
    split <;> simp_all

@[simp]
lemma DecisionTree.negateLeaves_depth {n : ℕ} (T : DecisionTree n) :
    T.negateLeaves.depth = T.depth := by
  induction T with
  | leaf _ => simp [negateLeaves, DecisionTree.depth]
  | branch v lo hi ih_lo ih_hi =>
    simp [negateLeaves, DecisionTree.depth, ih_lo, ih_hi]

lemma dtDepth_neg {n : ℕ} (f : (Fin n → Bool) → Bool) :
    dtDepth (fun x => !(f x)) = dtDepth f := by
  apply le_antisymm
  · -- dtDepth (¬f) ≤ dtDepth f
    unfold dtDepth
    apply Nat.find_le
    have h := Nat.find_spec (p := fun d => ∃ T : DecisionTree n, T.depth ≤ d ∧ ∀ x, T.eval x = f x)
      ⟨n, buildFullDTree f 0 (fun _ => false),
       buildFullDTree_depth f 0 (Nat.zero_le n) _,
       fun x => buildFullDTree_eval f 0 (Nat.zero_le n) _ x (fun _ hi => by omega)⟩
    obtain ⟨T, hTd, hTeval⟩ := h
    exact ⟨T.negateLeaves, by simp [hTd], by intro x; simp [hTeval]⟩
  · -- dtDepth f ≤ dtDepth (¬f)
    unfold dtDepth
    apply Nat.find_le
    have h := Nat.find_spec (p := fun d => ∃ T : DecisionTree n, T.depth ≤ d ∧ ∀ x, T.eval x = (fun x => !(f x)) x)
      ⟨n, buildFullDTree _ 0 (fun _ => false),
       buildFullDTree_depth _ 0 (Nat.zero_le n) _,
       fun x => buildFullDTree_eval _ 0 (Nat.zero_le n) _ x (fun _ hi => by omega)⟩
    obtain ⟨T, hTd, hTeval⟩ := h
    exact ⟨T.negateLeaves, by simp [hTd], by intro x; simp [hTeval]⟩

namespace SwitchingLemmaCNF

open SwitchingLemma2

variable {n : ℕ}

/-! ## restrictFn commutes with negation -/

lemma restrictFn_neg {n : ℕ} (f : (Fin n → Bool) → Bool) (ρ : Restriction n) :
    restrictFn (fun x => !(f x)) ρ = fun x => !(restrictFn f ρ x) := by
  ext x; simp [restrictFn]

lemma IsBadRestriction_neg {n : ℕ} (f : (Fin n → Bool) → Bool) (d : ℕ) (ρ : Restriction n) :
    IsBadRestriction (fun x => !(f x)) d ρ ↔ IsBadRestriction f d ρ := by
  simp only [IsBadRestriction, restrictFn_neg, dtDepth_neg]

/-! ## Nodup and injectivity conditions transfer through duality -/

lemma cnfToDualDNF_nodup {n : ℕ} (ψ : CNF n)
    (h : ∀ c ∈ ψ, c.Nodup) :
    ∀ t ∈ cnfToDualDNF ψ, t.Nodup := by
  intro t ht
  simp only [cnfToDualDNF, List.mem_map] at ht
  obtain ⟨c, hc_mem, rfl⟩ := ht
  exact (h c hc_mem).map Literal.flipNeg_injective

lemma cnfToDualDNF_inj {n : ℕ} (ψ : CNF n)
    (h : ∀ c ∈ ψ, ∀ l₁ ∈ c, ∀ l₂ ∈ c, l₁.var = l₂.var → l₁ = l₂) :
    ∀ t ∈ cnfToDualDNF ψ, ∀ l₁ ∈ t, ∀ l₂ ∈ t, l₁.var = l₂.var → l₁ = l₂ := by
  intro t ht l₁ hl₁ l₂ hl₂ hvar
  simp only [cnfToDualDNF, List.mem_map] at ht
  obtain ⟨c, hc_mem, rfl⟩ := ht
  simp only [List.mem_map] at hl₁ hl₂
  obtain ⟨l₁', hl₁'_mem, rfl⟩ := hl₁
  obtain ⟨l₂', hl₂'_mem, rfl⟩ := hl₂
  simp only [Literal.flipNeg_var] at hvar
  have := h c hc_mem l₁' hl₁'_mem l₂' hl₂'_mem hvar
  rw [this]

/-! ## Main theorem: Switching Lemma for CNFs -/

/-- **Håstad's Switching Lemma for CNFs.**
    For a CNF formula `ψ` of width at most `w` on `n` variables, the number of
    `s`-restrictions under which the restricted function has decision tree depth > `d`
    is bounded by `numSRestrictions n s * (10 * s * w)^d / n^d`. -/
theorem switching_lemma_cnf {n : ℕ} (hn : 0 < n) (ψ : CNF n) (w s d : ℕ)
    (hw : ψ.width ≤ w) (hs : 5 * s ≤ n)
    (hnd : ∀ c ∈ ψ, ∀ l₁ ∈ c, ∀ l₂ ∈ c, l₁.var = l₂.var → l₁ = l₂)
    (hnodup : ∀ c ∈ ψ, c.Nodup) :
    (Finset.univ.filter fun ρ : Restriction n =>
        IsRestriction s ρ ∧ IsBadRestriction ψ.eval d ρ).card * n ^ d ≤
    numSRestrictions n s * (10 * s * w) ^ d := by
  -- Rewrite using the dual DNF
  have hkey : ∀ ρ : Restriction n,
      IsBadRestriction ψ.eval d ρ ↔
      IsBadRestriction (cnfToDualDNF ψ).eval d ρ := by
    intro ρ
    constructor
    · intro hbad
      simp only [IsBadRestriction] at hbad ⊢
      rw [show (cnfToDualDNF ψ).eval = fun x => !(ψ.eval x) from
        funext (fun x => cnfToDualDNF_eval ψ x)]
      rw [restrictFn_neg]
      rw [dtDepth_neg]
      exact hbad
    · intro hbad
      simp only [IsBadRestriction] at hbad ⊢
      rw [show (cnfToDualDNF ψ).eval = fun x => !(ψ.eval x) from
        funext (fun x => cnfToDualDNF_eval ψ x)] at hbad
      rw [restrictFn_neg] at hbad
      rw [dtDepth_neg] at hbad
      exact hbad
  have hfilter_eq : (Finset.univ.filter fun ρ : Restriction n =>
        IsRestriction s ρ ∧ IsBadRestriction ψ.eval d ρ) =
      (Finset.univ.filter fun ρ : Restriction n =>
        IsRestriction s ρ ∧ IsBadRestriction (cnfToDualDNF ψ).eval d ρ) := by
    ext ρ; simp [hkey]
  rw [hfilter_eq]
  have hw' : (cnfToDualDNF ψ).width ≤ w := by rw [cnfToDualDNF_width]; exact hw
  exact switching_lemma hn (cnfToDualDNF ψ) w s d hw' hs
    (cnfToDualDNF_inj ψ hnd) (cnfToDualDNF_nodup ψ hnodup)

/-- **Switching Lemma Corollary for CNFs.**
    For a CNF formula `ψ` of width at most `w`, the number of `s`-restrictions
    under which the restricted function cannot be represented by a DNF of width ≤ `w`
    is bounded. -/
theorem switching_corollary_cnf {n : ℕ} (hn : 0 < n) (ψ : CNF n) (w s : ℕ)
    (hw : ψ.width ≤ w) (hs : 5 * s ≤ n)
    (hnd : ∀ c ∈ ψ, ∀ l₁ ∈ c, ∀ l₂ ∈ c, l₁.var = l₂.var → l₁ = l₂)
    (hnodup : ∀ c ∈ ψ, c.Nodup) :
    (Finset.univ.filter fun ρ : Restriction n =>
        IsRestriction s ρ ∧
        ¬ ∃ φ : DNF n, φ.width ≤ w ∧
          ∀ x, φ.eval x = restrictFn ψ.eval ρ x).card * n ^ w ≤
    numSRestrictions n s * (10 * s * w) ^ w := by
  apply le_trans _ (switching_lemma_cnf hn ψ w s w hw hs hnd hnodup)
  apply Nat.mul_le_mul_right
  apply Finset.card_le_card
  intro ρ hρ
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hρ ⊢
  refine ⟨hρ.1, ?_⟩
  show dtDepth (restrictFn ψ.eval ρ) > w
  by_contra hgood; push_neg at hgood
  exact hρ.2 (dtDepth_le_implies_small_dnf_cnf _ w hgood).1

end SwitchingLemmaCNF

#min_imports
