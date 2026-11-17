/-! ### De Morgan negation and substitution (F1–F2) -/

mutual

/-- The De Morgan negation of a formula: every literal flips its sign and every gate flips its
kind, `(lit ⟨i, s⟩).neg = lit ⟨i, !s⟩` and `(node b cs).neg = node (!b) (cs.map neg)`, so
that `c.neg` computes `!c.eval x` with the same shape, depth and fan-in
(`TreeCircuit.neg_eval`, `depth_neg`, `maxFanin_neg`).  Structural recursion over the nested
child list, through the private list helper `negList`.  Glue. -/
def TreeCircuit.neg : TreeCircuit n → TreeCircuit n
  | .lit l => .lit ⟨l.idx, !l.sign⟩
  | .node b cs => .node (!b) (negList cs)

/-- `TreeCircuit.neg` on every member of a child list: `negList cs = cs.map neg`. -/
private def negList : List (TreeCircuit n) → List (TreeCircuit n)
  | [] => []
  | c :: cs => c.neg :: negList cs

end

/-- The negation of a literal flips its sign:
`(TreeCircuit.lit l).neg = TreeCircuit.lit ⟨l.idx, !l.sign⟩`. -/
theorem TreeCircuit.neg_lit (l : Lit n) :
    (TreeCircuit.lit l).neg = TreeCircuit.lit ⟨l.idx, !l.sign⟩ := rfl

/-- The list helper of `neg` is `List.map`: `negList cs = cs.map TreeCircuit.neg`. -/
private theorem negList_eq_map : ∀ cs : List (TreeCircuit n), negList cs = cs.map TreeCircuit.neg
  | [] => rfl
  | c :: cs => congrArg (c.neg :: ·) (negList_eq_map cs)

/-- The negation of a gate flips its kind and negates every child:
`(TreeCircuit.node b cs).neg = TreeCircuit.node (!b) (cs.map TreeCircuit.neg)`. -/
theorem TreeCircuit.neg_node (b : Bool) (cs : List (TreeCircuit n)) :
    (TreeCircuit.node b cs).neg = TreeCircuit.node (!b) (cs.map TreeCircuit.neg) :=
  congrArg (TreeCircuit.node (!b)) (negList_eq_map cs)

/-- **F1, value.** The De Morgan negation computes the negation:
`c.neg.eval x = !c.eval x`.  Glue (r3 §H5.7, F1).

**Proof sketch.** Induction on `c` (`TreeCircuit.ind`).  A literal: `neg_lit`, then
`eval_lit` and the value of a literal (`Lit.eval`, whose reader is missing; see the census)
with the sign flipped.  A gate `node b cs`: `neg_node`; for `b = true` the negated gate is an
`∨`-gate, so `eval_node_false` gives `(cs.map neg).any (·.eval x)`, which by the induction
hypothesis is `cs.any (! ·.eval x) = !(cs.all (·.eval x))`, that is `!` of `eval_node_true`;
`b = false` is symmetric. -/
theorem TreeCircuit.neg_eval (c : TreeCircuit n) (x : Fin n → Bool) :
    c.neg.eval x = !c.eval x := by
  sorry

/-- **F1, depth.** De Morgan negation preserves the depth: `c.neg.depth = c.depth`.  Glue.

**Proof sketch.** Induction on `c` (`TreeCircuit.ind`).  A literal stays a literal (depth `0`
on both sides; the reader `depth_lit` is missing, see the census).  A gate: `neg_node` and
`depth_node` reduce the claim to `maxDepth (cs.map neg) = maxDepth cs`, an induction on the
list with `maxDepth_nil`/`maxDepth_cons` and the induction hypothesis on each child. -/
theorem TreeCircuit.depth_neg (c : TreeCircuit n) : c.neg.depth = c.depth := by
  sorry

/-- **F1, fan-in.** De Morgan negation preserves the fan-in: `c.neg.maxFanin = c.maxFanin`.
Glue.

**Proof sketch.** As for `depth_neg`: induction on `c`; a gate keeps its arity
(`List.length_map`), and `maxFanin_node` with `maxFaninL_nil`/`maxFaninL_cons` and the
induction hypothesis gives `maxFaninL (cs.map neg) = maxFaninL cs`. -/
theorem TreeCircuit.maxFanin_neg (c : TreeCircuit n) : c.neg.maxFanin = c.maxFanin := by
  sorry

mutual

/-- Substitution of formulas for variables: `c.subst f` replaces every positive literal
`x_i` of `c` by `f i` and every negative literal `¬x_i` by `(f i).neg`, keeping the gates,
`(lit l).subst f = if l.sign then f l.idx else (f l.idx).neg` and
`(node b cs).subst f = node b (cs.map (·.subst f))`.  It computes `c` on the values of the
`f i` (`TreeCircuit.subst_eval`).  Structural recursion over the nested child list, through
the private list helper `substList`.  Glue. -/
def TreeCircuit.subst {m : ℕ} : TreeCircuit n → (Fin n → TreeCircuit m) → TreeCircuit m
  | .lit l, f => if l.sign then f l.idx else (f l.idx).neg
  | .node b cs, f => .node b (substList cs f)

/-- `TreeCircuit.subst` on every member of a child list:
`substList cs f = cs.map (·.subst f)`. -/
private def substList {m : ℕ} :
    List (TreeCircuit n) → (Fin n → TreeCircuit m) → List (TreeCircuit m)
  | [], _ => []
  | c :: cs, f => c.subst f :: substList cs f

end

/-- Substitution into a literal: the positive literal `x_i` becomes `f i` and the negative
literal `¬x_i` becomes `(f i).neg`,
`(TreeCircuit.lit l).subst f = if l.sign then f l.idx else (f l.idx).neg`. -/
theorem TreeCircuit.subst_lit {m : ℕ} (l : Lit n) (f : Fin n → TreeCircuit m) :
    (TreeCircuit.lit l).subst f = if l.sign then f l.idx else (f l.idx).neg := rfl

/-- The list helper of `subst` is `List.map`: `substList cs f = cs.map (·.subst f)`. -/
private theorem substList_eq_map {m : ℕ} (f : Fin n → TreeCircuit m) :
    ∀ cs : List (TreeCircuit n), substList cs f = cs.map fun c => c.subst f
  | [] => rfl
  | c :: cs => congrArg (c.subst f :: ·) (substList_eq_map f cs)

/-- Substitution into a gate substitutes into every child:
`(TreeCircuit.node b cs).subst f = TreeCircuit.node b (cs.map fun c => c.subst f)`. -/
theorem TreeCircuit.subst_node {m : ℕ} (b : Bool) (cs : List (TreeCircuit n))
    (f : Fin n → TreeCircuit m) :
    (TreeCircuit.node b cs).subst f = TreeCircuit.node b (cs.map fun c => c.subst f) :=
  congrArg (TreeCircuit.node b) (substList_eq_map f cs)

/-- Renaming the variables of a formula along `e : Fin n → Fin m`, the literal case of
substitution: `c.rename e = c.subst fun i => lit ⟨e i, true⟩`, so `x_i` becomes `x_{e i}` and
`¬x_i` becomes `¬x_{e i}`.  Glue. -/
def TreeCircuit.rename {m : ℕ} (c : TreeCircuit n) (e : Fin n → Fin m) : TreeCircuit m :=
  c.subst fun i => TreeCircuit.lit ⟨e i, true⟩

/-- Renaming is substitution of positive literals:
`c.rename e = c.subst fun i => TreeCircuit.lit ⟨e i, true⟩`. -/
theorem TreeCircuit.rename_eq {m : ℕ} (c : TreeCircuit n) (e : Fin n → Fin m) :
    c.rename e = c.subst fun i => TreeCircuit.lit ⟨e i, true⟩ := rfl

/-- **F2, value.** Substitution computes the formula on the substituted values:
`(c.subst f).eval x = c.eval fun i => (f i).eval x`.  Glue (r3 §H5.7, F2).

**Proof sketch.** Induction on `c` (`TreeCircuit.ind`).  A positive literal: `subst_lit`, and
both sides are `(f i).eval x` (`eval_lit` and the literal's value).  A negative literal: the
left side is `(f i).neg.eval x = !(f i).eval x` by `neg_eval`, which is the value of `¬x_i`
under `fun i => (f i).eval x`.  A gate: `subst_node`, then `eval_node_true`/`eval_node_false`
on both sides, `List.all_map`/`List.any_map` and the induction hypothesis on each child. -/
theorem TreeCircuit.subst_eval {m : ℕ} (c : TreeCircuit n) (f : Fin n → TreeCircuit m)
    (x : Fin m → Bool) : (c.subst f).eval x = c.eval fun i => (f i).eval x := by
  sorry

/-- **F2, depth.** Substitution adds at most the depth of the deepest substituted formula:
`(c.subst f).depth ≤ c.depth + Finset.univ.sup fun i => (f i).depth`.  Glue (r3 §H5.7, F2).

*Deviation from r3's sketch:* r3 writes `⨆ i, (f i).depth`; `SupSet ℕ` is not in this file's
(frozen) import closure, so the supremum over the finite index type is the equal
`Finset.univ.sup`.

**Proof sketch.** Induction on `c`, with `D = Finset.univ.sup fun i => (f i).depth`.  A
literal: the result is `f i` or `(f i).neg`, of depth `(f i).depth ≤ D`
(`depth_neg`, `Finset.le_sup`), and `c.depth = 0`.  A gate: `subst_node` and `depth_node` give
`1 + maxDepth (cs.map (·.subst f))`; each child is bounded by `child.depth + D` (induction
hypothesis) `≤ maxDepth cs + D` (`depth_le_maxDepth`), so the list maximum is too
(`maxDepth_nil`/`maxDepth_cons`), and `depth_node` on `c` closes it. -/
theorem TreeCircuit.depth_subst_le {m : ℕ} (c : TreeCircuit n) (f : Fin n → TreeCircuit m) :
    (c.subst f).depth ≤ c.depth + Finset.univ.sup fun i => (f i).depth := by
  sorry

/-- **F2, fan-in.** Substitution has the fan-in of the formula or of a substituted formula:
`(c.subst f).maxFanin ≤ max c.maxFanin (Finset.univ.sup fun i => (f i).maxFanin)`.  Glue
(r3 §H5.7, F2; r3 names the lemma without a formula, and `⨆` is written `Finset.univ.sup` as
in `depth_subst_le`).

**Proof sketch.** Induction on `c` as in `depth_subst_le`.  A literal becomes `f i` or
`(f i).neg`, of fan-in `(f i).maxFanin` (`maxFanin_neg`, `Finset.le_sup`).  A gate keeps its
arity (`subst_node`, `List.length_map`), and `maxFanin_node`, `maxFaninL_cons` and the
induction hypothesis bound the children. -/
theorem TreeCircuit.maxFanin_subst_le {m : ℕ} (c : TreeCircuit n) (f : Fin n → TreeCircuit m) :
    (c.subst f).maxFanin ≤ max c.maxFanin (Finset.univ.sup fun i => (f i).maxFanin) := by
  sorry

/-- **F2, renaming: value.** A renamed formula reads the renamed variables:
`(c.rename e).eval x = c.eval (x ∘ e)`.  Glue (r3 §H5.7, F2).

**Proof sketch.** `rename_eq` and `subst_eval`: the substituted value of variable `i` is
`(lit ⟨e i, true⟩).eval x = x (e i)` (`eval_lit` and the literal's value), which is
`(x ∘ e) i`. -/
theorem TreeCircuit.rename_eval {m : ℕ} (c : TreeCircuit n) (e : Fin n → Fin m)
    (x : Fin m → Bool) : (c.rename e).eval x = c.eval (x ∘ e) := by
  sorry

/-- **F2, renaming: depth.** Renaming preserves the depth: `(c.rename e).depth = c.depth`.
Glue (r3 §H5.7, F2).

**Proof sketch.** Induction on `c` (`TreeCircuit.ind`) after `rename_eq`: a literal becomes a
literal (`subst_lit`, `neg_lit`; depth `0`), and a gate keeps its children's depths
(`subst_node`, `depth_node`, `maxDepth_cons`).  (`depth_subst_le` alone gives only `≤`.) -/
theorem TreeCircuit.depth_rename {m : ℕ} (c : TreeCircuit n) (e : Fin n → Fin m) :
    (c.rename e).depth = c.depth := by
  sorry

/-! ### Constants and the fan-in-2 gadgets (F3) -/

/-- The constant formula with value `b`: the empty gate, `TreeCircuit.const b = node b []`
(an empty `∧` is `true`, an empty `∨` is `false`).  Depth `1`, fan-in `0`.  Glue. -/
def TreeCircuit.const (b : Bool) : TreeCircuit n :=
  .node b []

/-- The constant formula is the empty gate:
`(TreeCircuit.const b : TreeCircuit n) = TreeCircuit.node b []`. -/
theorem TreeCircuit.const_eq (b : Bool) :
    (TreeCircuit.const b : TreeCircuit n) = TreeCircuit.node b [] := rfl

/-- **F3, constant: value.** The constant formula evaluates to its constant:
`(TreeCircuit.const b).eval x = b`.  Glue.

**Proof sketch.** `const_eq`, then `eval_node_true` (`[].all _ = true`) for `b = true` and
`eval_node_false` (`[].any _ = false`) for `b = false`. -/
theorem TreeCircuit.const_eval (b : Bool) (x : Fin n → Bool) :
    (TreeCircuit.const b : TreeCircuit n).eval x = b := by
  sorry

/-- **F3, constant: depth.** The constant formula has depth one:
`(TreeCircuit.const b : TreeCircuit n).depth = 1`.  Glue.

**Proof sketch.** `const_eq`, `depth_node` and `maxDepth_nil`. -/
theorem TreeCircuit.depth_const (b : Bool) : (TreeCircuit.const b : TreeCircuit n).depth = 1 := by
  sorry

/-- **F3, constant: fan-in.** The constant formula has fan-in zero:
`(TreeCircuit.const b : TreeCircuit n).maxFanin = 0`.  Glue.

**Proof sketch.** `const_eq`, `maxFanin_node`, `List.length_nil` and `maxFaninL_nil`. -/
theorem TreeCircuit.maxFanin_const (b : Bool) :
    (TreeCircuit.const b : TreeCircuit n).maxFanin = 0 := by
  sorry

/-- The binary conjunction `TreeCircuit.and2 a b = node true [a, b]`.  Glue. -/
def TreeCircuit.and2 (a b : TreeCircuit n) : TreeCircuit n :=
  .node true [a, b]

/-- The binary conjunction is a two-child `∧`-gate:
`TreeCircuit.and2 a b = TreeCircuit.node true [a, b]`. -/
theorem TreeCircuit.and2_eq (a b : TreeCircuit n) :
    TreeCircuit.and2 a b = TreeCircuit.node true [a, b] := rfl

/-- The binary disjunction `TreeCircuit.or2 a b = node false [a, b]`.  Glue. -/
def TreeCircuit.or2 (a b : TreeCircuit n) : TreeCircuit n :=
  .node false [a, b]

/-- The binary disjunction is a two-child `∨`-gate:
`TreeCircuit.or2 a b = TreeCircuit.node false [a, b]`. -/
theorem TreeCircuit.or2_eq (a b : TreeCircuit n) :
    TreeCircuit.or2 a b = TreeCircuit.node false [a, b] := rfl

/-- The binary exclusive or `TreeCircuit.xor2 a b = or2 (and2 a b.neg) (and2 a.neg b)`, that
is `(a ∧ ¬b) ∨ (¬a ∧ b)` with the negations by De Morgan (`neg`).  Two levels above its
arguments.  Glue. -/
def TreeCircuit.xor2 (a b : TreeCircuit n) : TreeCircuit n :=
  TreeCircuit.or2 (TreeCircuit.and2 a b.neg) (TreeCircuit.and2 a.neg b)

/-- The exclusive or as a formula:
`TreeCircuit.xor2 a b = TreeCircuit.or2 (TreeCircuit.and2 a b.neg) (TreeCircuit.and2 a.neg b)`.
-/
theorem TreeCircuit.xor2_eq (a b : TreeCircuit n) :
    TreeCircuit.xor2 a b = TreeCircuit.or2 (TreeCircuit.and2 a b.neg) (TreeCircuit.and2 a.neg b) :=
  rfl

/-- The three-input exclusive or (the full adder's sum bit)
`TreeCircuit.xor3 a b c = xor2 (xor2 a b) c`.  Four levels above its arguments.  Glue. -/
def TreeCircuit.xor3 (a b c : TreeCircuit n) : TreeCircuit n :=
  TreeCircuit.xor2 (TreeCircuit.xor2 a b) c

/-- The three-input exclusive or as nested binary ones:
`TreeCircuit.xor3 a b c = TreeCircuit.xor2 (TreeCircuit.xor2 a b) c`. -/
theorem TreeCircuit.xor3_eq (a b c : TreeCircuit n) :
    TreeCircuit.xor3 a b c = TreeCircuit.xor2 (TreeCircuit.xor2 a b) c := rfl

/-- The three-input majority (the full adder's carry bit)
`TreeCircuit.maj3 a b c = or2 (and2 a b) (and2 c (or2 a b))`, that is
`(a ∧ b) ∨ (c ∧ (a ∨ b))`.  Three levels above its arguments.  Glue. -/
def TreeCircuit.maj3 (a b c : TreeCircuit n) : TreeCircuit n :=
  TreeCircuit.or2 (TreeCircuit.and2 a b) (TreeCircuit.and2 c (TreeCircuit.or2 a b))

/-- The majority as a formula: `TreeCircuit.maj3 a b c =
TreeCircuit.or2 (TreeCircuit.and2 a b) (TreeCircuit.and2 c (TreeCircuit.or2 a b))`. -/
theorem TreeCircuit.maj3_eq (a b c : TreeCircuit n) :
    TreeCircuit.maj3 a b c =
      TreeCircuit.or2 (TreeCircuit.and2 a b) (TreeCircuit.and2 c (TreeCircuit.or2 a b)) := rfl

/-- **F3, `and2`: value.** `(TreeCircuit.and2 a b).eval x = (a.eval x && b.eval x)`.  Glue.

**Proof sketch.** `and2_eq`, `eval_node_true`, and `List.all_cons`/`List.all_nil`. -/
theorem TreeCircuit.and2_eval (a b : TreeCircuit n) (x : Fin n → Bool) :
    (TreeCircuit.and2 a b).eval x = (a.eval x && b.eval x) := by
  sorry

/-- **F3, `and2`: depth `+1`.** `(TreeCircuit.and2 a b).depth ≤ max a.depth b.depth + 1`.
Glue.

**Proof sketch.** `and2_eq`, `depth_node`, `maxDepth_cons` twice and `maxDepth_nil`; then
`omega` (it is an equality). -/
theorem TreeCircuit.depth_and2_le (a b : TreeCircuit n) :
    (TreeCircuit.and2 a b).depth ≤ max a.depth b.depth + 1 := by
  sorry

/-- **F3, `and2`: fan-in two.**
`(TreeCircuit.and2 a b).maxFanin ≤ max 2 (max a.maxFanin b.maxFanin)`.  Glue.

**Proof sketch.** `and2_eq`, `maxFanin_node` (arity `2`), `maxFaninL_cons` twice and
`maxFaninL_nil`; then `omega`. -/
theorem TreeCircuit.maxFanin_and2_le (a b : TreeCircuit n) :
    (TreeCircuit.and2 a b).maxFanin ≤ max 2 (max a.maxFanin b.maxFanin) := by
  sorry

/-- **F3, `or2`: value.** `(TreeCircuit.or2 a b).eval x = (a.eval x || b.eval x)`.  Glue.

**Proof sketch.** `or2_eq`, `eval_node_false`, and `List.any_cons`/`List.any_nil`. -/
theorem TreeCircuit.or2_eval (a b : TreeCircuit n) (x : Fin n → Bool) :
    (TreeCircuit.or2 a b).eval x = (a.eval x || b.eval x) := by
  sorry

/-- **F3, `or2`: depth `+1`.** `(TreeCircuit.or2 a b).depth ≤ max a.depth b.depth + 1`.
Glue.

**Proof sketch.** As `depth_and2_le`, through `or2_eq`. -/
theorem TreeCircuit.depth_or2_le (a b : TreeCircuit n) :
    (TreeCircuit.or2 a b).depth ≤ max a.depth b.depth + 1 := by
  sorry

/-- **F3, `or2`: fan-in two.**
`(TreeCircuit.or2 a b).maxFanin ≤ max 2 (max a.maxFanin b.maxFanin)`.  Glue.

**Proof sketch.** As `maxFanin_and2_le`, through `or2_eq`. -/
theorem TreeCircuit.maxFanin_or2_le (a b : TreeCircuit n) :
    (TreeCircuit.or2 a b).maxFanin ≤ max 2 (max a.maxFanin b.maxFanin) := by
  sorry

/-- **F3, `xor2`: value.** `(TreeCircuit.xor2 a b).eval x = (a.eval x ^^ b.eval x)`.  Glue.

**Proof sketch.** `xor2_eq`, `or2_eval`, `and2_eval` and `neg_eval`; then a case split on the
two Booleans. -/
theorem TreeCircuit.xor2_eval (a b : TreeCircuit n) (x : Fin n → Bool) :
    (TreeCircuit.xor2 a b).eval x = (a.eval x ^^ b.eval x) := by
  sorry

/-- **F3, `xor2`: depth `+2`.** `(TreeCircuit.xor2 a b).depth ≤ max a.depth b.depth + 2`.
Glue; the constant `2` is settled by the construction (one `∧` level, one `∨` level, and the
depth-preserving `neg`).

**Proof sketch.** `xor2_eq`, `depth_or2_le`, `depth_and2_le` twice, and `depth_neg` for
`a.neg`, `b.neg`; then `omega`. -/
theorem TreeCircuit.depth_xor2_le (a b : TreeCircuit n) :
    (TreeCircuit.xor2 a b).depth ≤ max a.depth b.depth + 2 := by
  sorry

/-- **F3, `xor2`: fan-in two.**
`(TreeCircuit.xor2 a b).maxFanin ≤ max 2 (max a.maxFanin b.maxFanin)`.  Glue.

**Proof sketch.** `xor2_eq`, `maxFanin_or2_le`, `maxFanin_and2_le` and `maxFanin_neg`; then
`omega`. -/
theorem TreeCircuit.maxFanin_xor2_le (a b : TreeCircuit n) :
    (TreeCircuit.xor2 a b).maxFanin ≤ max 2 (max a.maxFanin b.maxFanin) := by
  sorry

/-- **F3, `xor3`: value** (the full adder's sum bit).
`(TreeCircuit.xor3 a b c).eval x = (a.eval x ^^ b.eval x ^^ c.eval x)`.  Glue (r3 §H5.7, F3).

**Proof sketch.** `xor3_eq` and `xor2_eval` twice. -/
theorem TreeCircuit.xor3_eval (a b c : TreeCircuit n) (x : Fin n → Bool) :
    (TreeCircuit.xor3 a b c).eval x = (a.eval x ^^ b.eval x ^^ c.eval x) := by
  sorry

/-- **F3, `xor3`: depth `+4`.**
`(TreeCircuit.xor3 a b c).depth ≤ max a.depth (max b.depth c.depth) + 4`.  Glue; r3's `+4`
*(fix)*, settled by the construction: two nested `xor2`, each `+2`.

**Proof sketch.** `xor3_eq`, `depth_xor2_le` twice; then `omega`. -/
theorem TreeCircuit.depth_xor3_le (a b c : TreeCircuit n) :
    (TreeCircuit.xor3 a b c).depth ≤ max a.depth (max b.depth c.depth) + 4 := by
  sorry

/-- **F3, `xor3`: fan-in two.**
`(TreeCircuit.xor3 a b c).maxFanin ≤ max 2 (max a.maxFanin (max b.maxFanin c.maxFanin))`.
Glue.

**Proof sketch.** `xor3_eq` and `maxFanin_xor2_le` twice; then `omega`. -/
theorem TreeCircuit.maxFanin_xor3_le (a b c : TreeCircuit n) :
    (TreeCircuit.xor3 a b c).maxFanin ≤ max 2 (max a.maxFanin (max b.maxFanin c.maxFanin)) := by
  sorry

/-- **F3, `maj3`: value** (the full adder's carry bit, in the form of `carryBit`'s step).
`(TreeCircuit.maj3 a b c).eval x = (a.eval x && b.eval x || c.eval x && (a.eval x ^^ b.eval x))`.
Glue (r3 §H5.7, F3).  The formula computes `(a ∧ b) ∨ (c ∧ (a ∨ b))`, which is the same
Boolean function.

**Proof sketch.** `maj3_eq`, `or2_eval`, `and2_eval` twice and `or2_eval` again; then a case
split on the three Booleans. -/
theorem TreeCircuit.maj3_eval (a b c : TreeCircuit n) (x : Fin n → Bool) :
    (TreeCircuit.maj3 a b c).eval x =
      (a.eval x && b.eval x || c.eval x && (a.eval x ^^ b.eval x)) := by
  sorry

/-- **F3, `maj3`: depth `+3`.**
`(TreeCircuit.maj3 a b c).depth ≤ max a.depth (max b.depth c.depth) + 3`.  Glue; r3's `+3`
*(fix)*, settled by the construction `(a ∧ b) ∨ (c ∧ (a ∨ b))`.

**Proof sketch.** `maj3_eq`, `depth_or2_le` twice and `depth_and2_le` twice; then `omega`. -/
theorem TreeCircuit.depth_maj3_le (a b c : TreeCircuit n) :
    (TreeCircuit.maj3 a b c).depth ≤ max a.depth (max b.depth c.depth) + 3 := by
  sorry

/-- **F3, `maj3`: fan-in two.**
`(TreeCircuit.maj3 a b c).maxFanin ≤ max 2 (max a.maxFanin (max b.maxFanin c.maxFanin))`.
Glue.

**Proof sketch.** `maj3_eq`, `maxFanin_or2_le` twice and `maxFanin_and2_le` twice; then
`omega`. -/
theorem TreeCircuit.maxFanin_maj3_le (a b c : TreeCircuit n) :
    (TreeCircuit.maj3 a b c).maxFanin ≤ max 2 (max a.maxFanin (max b.maxFanin c.maxFanin)) := by
  sorry

