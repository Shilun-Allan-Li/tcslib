"""Build the A1 PR as this review recommends it: overlays of the four home files (copies of the
tip's files with the lemmas inserted beside their definitions and the module headers' result lists
updated), written to <out>/<Module>.lean, plus <out>/a1.patch (a unified diff against the tip).
Every edit is anchored on text that must occur exactly once; the script asserts that, and that the
result differs from the source only by insertions.

Usage: mka1overlays.py <worktree at the tip> <out dir> [--with-basic-classes]
  --with-basic-classes also adds the optional Basic.lean characterizations of DecidesInSpace,
  SPACE and LOGSPACE (the review's option for H's later inventory)."""
import difflib, os, sys

wt, out = sys.argv[1], sys.argv[2]
extra = "--with-basic-classes" in sys.argv[3:]
os.makedirs(out, exist_ok=True)

def edit(src, anchor, new, where="after"):
    assert src.count(anchor) == 1, f"anchor occurs {src.count(anchor)} times: {anchor[:60]!r}"
    i = src.index(anchor)
    j = i + len(anchor) if where == "after" else i
    return src[:j] + new + src[j:]

files = {}

# 1. ClassP/TimeConstructible.lean
p = "TCSlib/Complexity/ClassP/TimeConstructible.lean"
s = open(os.path.join(wt, p), encoding="utf-8").read()
s = edit(s, """def TimeConstructible (T : ℕ → ℕ) : Prop :=
  (∀ n, n ≤ T n) ∧
  ∃ c : ℕ, 0 < c ∧ ∃ M : FinTM Bool, ∀ x : List Bool,
    M.ComputesInTime x (T x.length).bits (c * (T x.length + 1))
""", """
/-- **Time constructibility, unfolded**: `T` is time constructible exactly when `n ≤ T n` for
every `n` and, for some constant `c > 0`, some machine computes `(T |x|).bits` on every input `x`
within `c · (T |x| + 1)` steps. -/
theorem timeConstructible_iff (T : ℕ → ℕ) :
    TimeConstructible T ↔
      (∀ n, n ≤ T n) ∧ ∃ c : ℕ, 0 < c ∧ ∃ M : FinTM Bool, ∀ x : List Bool,
        M.ComputesInTime x (T x.length).bits (c * (T x.length + 1)) :=
  Iff.rfl
""")
s = edit(s, "* `Complexity.timeConstructible_id` — the identity function is time constructible,",
         "* `Complexity.timeConstructible_iff` — the definition as an equivalence.\n", where="before")
files[p] = s

# 2. SpaceComplexity/Constructible.lean
p = "TCSlib/Complexity/SpaceComplexity/Constructible.lean"
s = open(os.path.join(wt, p), encoding="utf-8").read()
s = edit(s, """def SpaceConstructible (S : ℕ → ℕ) : Prop :=
  (∀ n, logSpace n ≤ S n) ∧
  ∃ c : ℕ, 0 < c ∧ ∃ M : FinTM Bool,
    M.ComputesInSpace (fun x => (S x.length).bits) fun n => c * S n
""", """
/-- **Space constructibility, unfolded**: `S` is space constructible exactly when
`logSpace n ≤ S n` for every `n` and, for some constant `c > 0`, some machine computes
`x ↦ (S |x|).bits` in space `c · S` (`Turing.FinTM.ComputesInSpace`). -/
theorem spaceConstructible_iff (S : ℕ → ℕ) :
    SpaceConstructible S ↔
      (∀ n, logSpace n ≤ S n) ∧ ∃ c : ℕ, 0 < c ∧ ∃ M : FinTM Bool,
        M.ComputesInSpace (fun x => (S x.length).bits) fun n => c * S n :=
  Iff.rfl
""")
s = edit(s, "* `Complexity.spaceConstructible_logSpace` — `log` is space-constructible.",
         "* `Complexity.spaceConstructible_iff` — the definition as an equivalence.\n", where="before")
files[p] = s

# 3. SpaceComplexity/Basic.lean
p = "TCSlib/Complexity/SpaceComplexity/Basic.lean"
s = open(os.path.join(wt, p), encoding="utf-8").read()
s = edit(s, """def ComputesInSpace (M : FinTM Bool) (f : List Bool → List Bool) (s : ℕ → ℕ) : Prop :=
  ∀ x : List Bool, ∃ t, M.ComputesInTime x (f x) t ∧
    M.tm.spaceUsed (M.tm.initCfg x) t ≤ s x.length
""", """
/-- **Computing in space, unfolded**: `M` computes `f` in space `s` exactly when on every input
`x` there is a time `t` at which `M` has halted with output `f x`
(`Turing.FinTM.ComputesInTime`), having visited at most `s |x|` work-tape cells by then. -/
theorem computesInSpace_iff (M : FinTM Bool) (f : List Bool → List Bool) (s : ℕ → ℕ) :
    M.ComputesInSpace f s ↔
      ∀ x : List Bool, ∃ t, M.ComputesInTime x (f x) t ∧
        M.tm.spaceUsed (M.tm.initCfg x) t ≤ s x.length :=
  Iff.rfl
""")
if extra:
    s = edit(s, """def DecidesInSpace (M : FinTM Bool) (L : Language Bool) (s : ℕ → ℕ) : Prop :=
  M.ComputesInSpace (fun x => [MultiTapeTM.indicator (L : Set (List Bool)) x]) s
""", """
/-- **Deciding in space, unfolded**: `M` decides `L` in space `s` exactly when it computes the
one-bit indicator `x ↦ [x ∈ L]` in space `s`. -/
theorem decidesInSpace_iff (M : FinTM Bool) (L : Language Bool) (s : ℕ → ℕ) :
    M.DecidesInSpace L s ↔
      M.ComputesInSpace (fun x => [MultiTapeTM.indicator (L : Set (List Bool)) x]) s :=
  Iff.rfl
""")
    s = edit(s, """def SPACE (s : ℕ → ℕ) : Set (Language Bool) :=
  {L | ∃ (c : ℕ) (M : FinTM Bool), M.DecidesInSpace L fun n => c * s n}
""", """
/-- **Membership in `SPACE`, unfolded**: `L ∈ SPACE s` exactly when some machine decides `L` in
space `c · s` for some constant `c`. -/
theorem mem_SPACE_iff {s : ℕ → ℕ} {L : Language Bool} :
    L ∈ SPACE s ↔ ∃ (c : ℕ) (M : FinTM Bool), M.DecidesInSpace L fun n => c * s n :=
  Iff.rfl
""")
    s = edit(s, "def LOGSPACE : Set (Language Bool) := SPACE logSpace\n", """
/-- `LOGSPACE` is `SPACE logSpace`. -/
theorem LOGSPACE_eq : LOGSPACE = SPACE logSpace := rfl
""")
s = edit(s, "def logSpace (n : ℕ) : ℕ := Nat.log 2 n + 1\n", """
/-- The logarithmic bound's formula: `logSpace n = Nat.log 2 n + 1`. -/
theorem logSpace_eq (n : ℕ) : logSpace n = Nat.log 2 n + 1 := rfl
""")
s = edit(s, "* `Complexity.SPACE.mono` — `SPACE` is monotone in the space bound.",
         "* `Turing.FinTM.computesInSpace_iff`, `Complexity.logSpace_eq` — the definitions of\n"
         "  `ComputesInSpace` and `logSpace` as an equivalence and an equation.\n"
         + ("* `Turing.FinTM.decidesInSpace_iff`, `Complexity.mem_SPACE_iff`, `Complexity.LOGSPACE_eq` —\n"
            "  the definitions of `DecidesInSpace`, `SPACE` and `LOGSPACE`, unfolded.\n" if extra else ""),
         where="before")
files[p] = s

# 4. ClassNP/Transducer.lean
p = "TCSlib/Complexity/ClassNP/Transducer.lean"
s = open(os.path.join(wt, p), encoding="utf-8").read()
s = edit(s, """def transduce (δ : σ → Bool → σ) (o : σ → Bool → Option Bool) : σ → List Bool → List Bool
  | _, [] => []
  | q, b :: l => (o q b).toList ++ transduce δ o (δ q b) l
""", """
/-- A transducer emits nothing on the empty word: `transduce δ o q [] = []`. -/
theorem transduce_nil (δ : σ → Bool → σ) (o : σ → Bool → Option Bool) (q : σ) :
    transduce δ o q [] = [] := rfl

/-- On `b :: l` a transducer emits `o q b` and continues from `δ q b`:
`transduce δ o q (b :: l) = (o q b).toList ++ transduce δ o (δ q b) l`. -/
theorem transduce_cons (δ : σ → Bool → σ) (o : σ → Bool → Option Bool) (q : σ) (b : Bool)
    (l : List Bool) :
    transduce δ o q (b :: l) = (o q b).toList ++ transduce δ o (δ q b) l := rfl
""")
s = edit(s, """    transduce δ o q (l₁ ++ l₂) =
      transduce δ o q l₁ ++ transduce δ o (l₁.foldl δ q) l₂ := by
  induction l₁ generalizing q with
  | nil => rfl
  | cons b l ih => simp [transduce, ih]
""", """
/-- **A copying state copies**: if from the state `q` every bit is emitted unchanged
(`o q b = some b`) and `q` is kept (`δ q b = q`), then the transducer started in `q` is the
identity, `transduce δ o q l = l`.

**Proof sketch.** Induction on `l`, by `Complexity.transduce_nil` and
`Complexity.transduce_cons`. -/
theorem transduce_of_copy (δ : σ → Bool → σ) (o : σ → Bool → Option Bool) (q : σ)
    (hδ : ∀ b, δ q b = q) (ho : ∀ b, o q b = some b) (l : List Bool) :
    transduce δ o q l = l := by
  induction l with
  | nil => exact transduce_nil δ o q
  | cons b l ih =>
    rw [transduce_cons, hδ, ho, ih]
    rfl
""")
s = edit(s, "* `Complexity.transducerTM_computes` — the machine computes the transducer's function",
         "* `Complexity.transduce_nil`, `Complexity.transduce_cons` — the function's case lemmas;\n"
         "  `Complexity.transduce_of_copy` — a state that copies and is kept gives the identity.\n",
         where="before")
files[p] = s

patch = []
for p, new in files.items():
    old = open(os.path.join(wt, p), encoding="utf-8").read()
    ol, nl = old.splitlines(keepends=True), new.splitlines(keepends=True)
    sm = difflib.SequenceMatcher(a=ol, b=nl, autojunk=False)
    for tag, i1, i2, j1, j2 in sm.get_opcodes():
        assert tag in ("equal", "insert"), (p, tag, i1, i2)
    assert all(len(l.rstrip("\n")) <= 100 for l in nl if l not in ol), p
    patch += difflib.unified_diff(ol, nl, "a/" + p, "b/" + p)
    name = p.rsplit("/", 1)[1]
    open(os.path.join(out, name), "w", encoding="utf-8").write(new)
    print(f"{p}: +{len(nl) - len(ol)} lines")
open(os.path.join(out, "a1.patch"), "w", encoding="utf-8").write("".join(patch))
print("wrote", os.path.join(out, "a1.patch"))
