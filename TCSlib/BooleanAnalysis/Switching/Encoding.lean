import TCSlib.BooleanAnalysis.Switching.CanonicalDTree

/-!
# Razborov Encoding and Decoding

Definitions for the Razborov encoding that maps a bad restriction ρ to (γ, aux),
and the corresponding decoder that recovers ρ from (γ, aux).

## Encoding strategy

The encoding extracts the deepest path from the canonical decision tree for f|ρ,
takes the first d steps, and fixes the corresponding variables to their
satisfying directions.

The simulation maintains two restrictions: ρ₀ follows the path directions
(to match canonical DT branching), while σ (= γ) follows satisfying directions.
-/

open Classical

namespace SwitchingLemma2

variable {n : ℕ}

/-- Find the free literals in a term under restriction ρ. -/
noncomputable def Term.freeLiterals {n : ℕ} (t : Term n) (ρ : Restriction n) :
    List (Literal n) :=
  t.filter (fun l => decide (l.var ∈ ρ.freeVars))

/-! ## processClauseLits -/

/-- Process one clause's free literals against the canonical DT path.
    For each free literal (in clause order), consume one path entry:
    - Fix the literal's variable to its satisfying direction in σ (building γ)
    - Track the path direction in ρ₀ (simulating canonical DT branching)
    - Record `(literal_position_in_clause, path_direction)` in aux

    Returns `(remaining_path, updated_ρ₀, updated_σ, clause_aux_data)`. -/
noncomputable def processClauseLits {n : ℕ} :
    List (Literal n × ℕ) → List (Fin n × Bool) → Restriction n → Restriction n →
    List (Fin n × Bool) × Restriction n × Restriction n × List (ℕ × Bool)
  | [], path, ρ₀, σ => (path, ρ₀, σ, [])
  | _, [], ρ₀, σ => ([], ρ₀, σ, [])
  | (l, idx) :: restLits, (_, dir) :: restPath, ρ₀, σ =>
    let r := processClauseLits restLits restPath
      (Function.update ρ₀ l.var (some dir))
      (Function.update σ l.var (some (!l.neg)))
    (r.1, r.2.1, r.2.2.1, (idx, dir) :: r.2.2.2)

/-! ## Razborov encoding -/

/-- The Razborov encoding: follow the deepest path in the canonical decision
    tree for f|ρ, processing one clause at a time.

    Returns `(γ, aux)` where:
    - `γ` extends `ρ` by fixing d variables to their satisfying directions
    - `aux` has clause blocks separated by termination markers `(w, false)` -/
noncomputable def razborovEncode {n : ℕ} (f : DNF n) (w d : ℕ)
    (ρ : Restriction n) : Restriction n × List (ℕ × Bool) :=
  let path := (canonicalDTree f ρ).deepPath.take d
  razborovEncode.go f w (path.length + 1) path ρ ρ []
where
  /-- Main encoding loop: find the first non-killed clause, process ALL of its
      free literals against the path, emit a termination marker, and repeat. -/
  go (f : DNF n) (w : ℕ) :
      ℕ → List (Fin n × Bool) → Restriction n → Restriction n →
      List (ℕ × Bool) → Restriction n × List (ℕ × Bool)
    | _, [], _, σ, acc => (σ, acc)
    | 0, _, _, σ, acc => (σ, acc)
    | fuel + 1, step :: rest, ρ₀, σ, acc =>
      let path := step :: rest
      match f.find? (fun t => decide (¬Term.killedBy t ρ₀)) with
      | none => (σ, acc)
      | some t =>
        let freeLitsIdx := (t.zipIdx).filter (fun ⟨l, _⟩ => decide (l.var ∈ ρ₀.freeVars))
        match freeLitsIdx with
        | [] => (σ, acc)
        | fl :: fls =>
          let r := processClauseLits (fl :: fls) path ρ₀ σ
          go f w fuel r.1 r.2.1 r.2.2.1 (acc ++ r.2.2.2 ++ [(w, false)])

/-! ## Razborov decoding -/

/-- Decode: given `(γ, aux)` from the Razborov encoding, recover the original
    restriction ρ. -/
noncomputable def razborovDecode {n : ℕ} (f : DNF n) (w : ℕ)
    (γ : Restriction n) (aux : List (ℕ × Bool)) : Restriction n :=
  (razborovDecode.go f w (aux.length + 1) γ γ aux).1
where
  /-- Process aux entries for one clause until termination marker. -/
  processEntries (t : Term n) (w : ℕ) :
      Restriction n → Restriction n → List (ℕ × Bool) →
      Restriction n × Restriction n × List (ℕ × Bool)
    | σ, ρ₀, [] => (σ, ρ₀, [])
    | σ, ρ₀, (idx, dir) :: rest =>
      if idx ≥ w then
        (σ, ρ₀, rest)
      else
        match t.drop idx with
        | [] => (σ, ρ₀, rest)
        | l :: _ =>
          processEntries t w
            (Function.update σ l.var none)
            (Function.update ρ₀ l.var (some dir))
            rest
  /-- Main decoding loop: find the clause, process its aux block, repeat. -/
  go (f : DNF n) (w : ℕ) :
      ℕ → Restriction n → Restriction n → List (ℕ × Bool) →
      Restriction n × Restriction n
    | _, σ, ρ₀, [] => (σ, ρ₀)
    | 0, σ, ρ₀, _ => (σ, ρ₀)
    | fuel + 1, σ, ρ₀, entry :: restAux =>
      let aux := entry :: restAux
      match f.find? (fun t => decide (¬Term.killedBy t ρ₀)) with
      | none => (σ, ρ₀)
      | some t =>
        let (σ', ρ₀', aux') := processEntries t w σ ρ₀ aux
        go f w fuel σ' ρ₀' aux'

/-! ## Basic processClauseLits properties -/

lemma processClauseLits_path_le {n : ℕ}
    (lits : List (Literal n × ℕ)) (path : List (Fin n × Bool))
    (ρ₀ σ : Restriction n) :
    (processClauseLits lits path ρ₀ σ).1.length ≤ path.length := by
  induction lits generalizing path ρ₀ σ with
  | nil => simp [processClauseLits]
  | cons hd tl ih =>
    cases path with
    | nil => simp [processClauseLits]
    | cons p ps =>
      simp only [processClauseLits]
      exact le_trans (ih _ _ _) (Nat.le_succ _)

end SwitchingLemma2
