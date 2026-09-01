-- `lemma` is a MATHLIB macro, not core Lean. The extractor emits
-- `private lemma <name> …`; without this import every assembled lemma fails to
-- parse at `private ▸lemma` and the extractor silently falls back to let-swap,
-- making the whole corpus inert. Keep this import.
import Mathlib.Tactic.Lemma

/-
Shape regression corpus for `#extract_haves_iter_decl` (ExtractHavesFile.lean).

WHY THIS EXISTS
  A real grind is a ~50-minute feedback loop (LinearCodes `uniformity_lemma`,
  89 haves). Class #69 was a PARSE bug in the have-header split that could have
  been caught in seconds. Every decl below runs in seconds and is Mathlib-free,
  so a metaprogram edit can be regressed against every have-HEADER shape that
  occurs in TCSlib before committing a window to it.

SCOPE — READ BEFORE TRUSTING A GREEN RUN
  * Covers PARSE/ASSEMBLY behaviour: header splitting, binder handling,
    callsite rewriting, naming, nesting. Class #69 lived entirely here.
  * Does NOT reproduce SEMANTIC failures (`grind` failed, typeclass stuck,
    ladder blowup, probe-text blowup). Those need real Mathlib context that a
    small fixture by construction lacks. A green corpus is NECESSARY, NOT
    SUFFICIENT — it does not replace a real window.

SHAPE CENSUS of TCSlib when this was written (151 files, 4711 have headers):
  colon-newline-wrapped 551 | untyped `h :=` 433 | anonymous `have :` 310
  bullet-attached 266 | explicit-paren binder 18 | destructuring 4
  implicit-brace binder 2 | inst-implicit 0 | strict-implicit 0
  (the last two do not occur yet; covered here as forward-coverage since
   `scanBinderGroups` claims to handle them)

USAGE
  zsh scripts/shape_regress.sh           # rebuild olean + run whole corpus
-/

namespace ExtractShapes

/-- S1 — PARAMETERIZED HAVES (class #69). Explicit, implicit, multi-group, and
    a binder with NO type ascription. Each is APPLIED, so a callsite rewrite
    that drops the binders breaks the decl rather than passing silently. -/
theorem s1_parameterized (n : Nat) : n ≤ n + 3 := by
  have h_expl (k : Nat) (hk : k ≤ n) : k ≤ n + 1 := by omega
  have h_impl {k : Nat} (hk : k ≤ n) : k ≤ n + 2 := by omega
  have h_multi (a : Nat) (b : Nat) (hab : a ≤ b) : a ≤ b + 1 := by omega
  have h_noasc (k) : k + 0 = k := by omega
  have u1 : n ≤ n + 1 := h_expl n (Nat.le_refl n)
  have u2 : n ≤ n + 2 := h_impl (Nat.le_refl n)
  have u3 : n ≤ n + 1 := h_multi n n (Nat.le_refl n)
  have u4 : n + 0 = n := h_noasc n
  omega

/-- S1b — remaining BINDER KINDS: instance-implicit and strict-implicit.
    Forward-coverage: absent from TCSlib today, accepted by `scanBinderGroups`. -/
theorem s1b_binderkinds (n : Nat) : n = n := by
  have h_inst [Inhabited Nat] : (0 : Nat) ≤ 1 := by omega
  have h_strict ⦃k : Nat⦄ : k + 0 = k := by omega
  have u1 : (0 : Nat) ≤ 1 := h_inst
  have u2 : n + 0 = n := @h_strict n
  rfl

/-- S2 — COLON-NEWLINE WRAPPED headers (551 in TCSlib, the most common shape).
    The colon sits at end-of-line, so a raw `splitOn " : "` finds no separator;
    `collapseToOneLine` must run BEFORE the name/type split. Combined here with
    a parameterized header, which is where #69 and this class intersect. -/
theorem s2_colon_newline (n : Nat) : n ≤ n + 2 := by
  have h_wrapped :
      n ≤ n + 1 := by
    omega
  have h_wrapped_param (k : Nat) (hk : k ≤ n) :
      k ≤ n + 2 := by
    omega
  have u1 : n ≤ n + 2 := h_wrapped_param n (Nat.le_refl n)
  omega

/-- S3 — BULLET-ATTACHED haves (266), including a parameterized one inside a
    bullet block, plus nesting: the callsite rewrite must stay inside the
    bullet's indentation. -/
theorem s3_bullet (n : Nat) (hn : 0 < n ∨ n = 0) : n = n := by
  rcases hn with h | h
  · have h_in_bullet (k : Nat) (hk : k ≤ n) : k ≤ n + 1 := by omega
    have u1 : n ≤ n + 1 := h_in_bullet n (Nat.le_refl n)
    rfl
  · have h_plain : n = 0 := h
    rfl

/-- S4 — UNTYPED (`have h := term`, 433) and ANONYMOUS (`have : T`, 310).
    Untyped haves must yield `("", "")` from the header split — no type, no
    binders — rather than a guess. -/
theorem s4_untyped_anonymous (n : Nat) : n + 0 = n := by
  have h_untyped := Nat.le_refl n
  have : n + 0 = n := by omega
  have h_after_anon : n + 0 = n := this
  exact h_after_anon

/-- S5 — DESTRUCTURING haves (class #57, 4 in TCSlib): rewritten to a named
    have + `obtain` by the pre-pass; the raw `⟨` must never reach a lemma name. -/
theorem s5_destructuring (n : Nat) : n ≤ n + 1 := by
  have ⟨a, ha⟩ : ∃ a : Nat, a = n := ⟨n, rfl⟩
  have h_use : a = n := ha
  omega

/-- S6 — NESTED parameterized haves: the leaf-first climb must extract the
    inner one, rewrite its callsite, then see the outer one as a leaf. This is
    the shape that produced the original #69 instance (`h_child_eval` wrapping
    `h_lits`). -/
theorem s6_nested (n : Nat) : n ≤ n + 2 := by
  have h_outer (k : Nat) (hk : k ≤ n) : k ≤ n + 2 := by
    have h_inner (j : Nat) (hj : j ≤ n) : j ≤ n + 1 := by omega
    have u : k ≤ n + 1 := h_inner k hk
    omega
  have u1 : n ≤ n + 2 := h_outer n (Nat.le_refl n)
  omega

/-- S8 — BINDER TYPES CONTAINING BRACKETS. Real shape, surfaced by window 14:
    TVDistance `hset_le (S : {S : Set Ω // MeasurableSet S})`. The binder group's
    own TYPE carries `{…}` / `[…]`, so the header split must count bracket DEPTH
    across all kinds rather than stopping at the first closer. The corpus lacked
    this until a real window produced it. -/
theorem s8_bracketed_binder_types (n : Nat) : n = n := by
  have h_subtype (s : {k : Nat // k ≤ n}) : (s : Nat) ≤ n := s.property
  have h_listlit (l : List Nat) (hl : l = [1, 2]) : l.length = 2 := by simp [hl]
  have h_nested (p : {k : Nat // k ≤ n} × Nat) : (p.1 : Nat) ≤ n := p.1.property
  have u1 : ∀ s : {k : Nat // k ≤ n}, (s : Nat) ≤ n := fun s => h_subtype s
  rfl

end ExtractShapes
