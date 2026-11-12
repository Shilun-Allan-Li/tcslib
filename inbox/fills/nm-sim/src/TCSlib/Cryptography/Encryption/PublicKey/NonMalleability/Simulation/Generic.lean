/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TCSlib.Cryptography.Games.Efficiency
import TCSlib.Cryptography.Games.Hopping

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Generic tools for Theorem 174.8

Three generic facts used by both directions of [PS10, Theorem 174.8]. None of them is specific
to encryption.

* **Budget reduction** (`buildComp_budget_eq`, `toCompOn_budget_eq`). A machine's computation at
  budget `K ≥ j` that makes at most `j` queries on every path is its computation at budget `j`.
  The simulator of the ideal experiment runs at budget `1`, while T2 builds it at a polynomial
  budget.
* **One-shot coins drawn in advance** (`expect_simulate_eager`). An implementation that samples
  coins `t` at most once, on the call that leaves the "unused" states, has the law of the
  implementations with `t` fixed in advance, averaged over `t`.
* **Chunk maps** (`chunkMap`). A polynomial-time map applied to the consecutive fixed-length
  chunks of a string, concatenated (`polyTimeComputable_chunkMap`, `chunkMap_flatten`). The
  machines of both reductions read and write their tuples of ciphertexts and entries this way.

## Main definitions

* `NMSim.chunkStep`, `NMSim.chunkEmit`, `NMSim.chunkMap`.

## Main results

* `NMSim.buildComp_budget_eq`, `NMSim.toCompOn_budget_eq`.
* `NMSim.expect_congr_of_allOutputs`, `NMSim.expect_expect_sample`, `NMSim.bind_congr_of_allOutputs`.
* `NMSim.expect_simulate_eager`.
* `NMSim.expect_eq_until_bad`: equal until bad, for functions of the final state.
* `NMSim.polyTimeComputable_chunkMap`, `NMSim.chunkMap_flatten`.

## References

* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed., January 2010,
  Theorem 174.8 (book p. 174).
-/

namespace TCSlib.Cryptography.Composability.NMSim

open Complexity Turing TCSlib.Cryptography TCSlib.Cryptography.Games

/-! ### Budget reduction -/

section Budget

variable {ι α : Type} {spec : OracleSpec ι}

/-- **Budget reduction for `buildComp`.** If the computation of `next` at budget `K` from the log
`hist` makes at most `j ≤ K` queries on every path, it is the computation at budget `j`:
`buildComp next t j hist = buildComp next t K hist`.

**Proof sketch.** Induction on `j`. A final output is the same at every budget. A query at budget
`K` costs `1 ≤ j`, so `j = j' + 1` and `K = K' + 1`; both computations ask the same query and
continue with the same log, at budgets `j'` and `K' ≥ j'`, and the continuation makes at most `j'`
queries. At `j = 0` a query is impossible unless `K = 0`, where both give `timeout`. -/
theorem buildComp_budget_eq (next : QueryLog spec → Move spec α) (t : α) :
    ∀ (j K : ℕ) (hist : QueryLog spec), j ≤ K →
      (buildComp next t K hist).CostBoundedBy (fun _ => 1) j →
      buildComp next t j hist = buildComp next t K hist := by
  intro j
  induction j with
  | zero =>
    intro K hist _ hc
    cases h : next hist with
    | ret a =>
      cases K with
      | zero => rfl
      | succ K => rw [buildComp_zero_of_ret h, buildComp_succ_of_ret h]
    | query i x =>
      cases K with
      | zero => rfl
      | succ K =>
        rw [buildComp_succ_of_query h, OracleComp.costBoundedBy_query] at hc
        exact absurd hc.1 (by omega)
  | succ j ih =>
    intro K hist hK hc
    obtain ⟨K, rfl⟩ : ∃ K', K = K' + 1 := ⟨K - 1, by omega⟩
    cases h : next hist with
    | ret a => rw [buildComp_succ_of_ret h, buildComp_succ_of_ret h]
    | query i x =>
      rw [buildComp_succ_of_query h] at hc ⊢
      rw [buildComp_succ_of_query h]
      rw [OracleComp.costBoundedBy_query] at hc
      congr 1
      funext y
      exact ih K _ (by omega) (by simpa using hc.2 y)

/-- **Budget reduction for a machine:** if `D`'s computation on `x` at budget `K ≥ j` makes at
most `j` queries on every path, it is `D`'s computation at budget `j`. -/
theorem toCompOn_budget_eq (D : NUPPT) {β : Type} (codec : MachineCodec spec β) (n j K : ℕ)
    (x : List Bool) (r : D.Coins n) (hjK : j ≤ K)
    (hc : (D.toCompOn codec n K x r).CostBoundedBy (fun _ => 1) j) :
    D.toCompOn codec n j x r = D.toCompOn codec n K x r := by
  rw [NUPPT.toCompOn_eq] at hc ⊢
  rw [NUPPT.toCompOn_eq]
  exact buildComp_budget_eq _ _ j K [] hjK hc

end Budget

/-! ### Expectations on the possible outputs -/

section Expect

variable {α β : Type}

/-- Two functions that agree on every possible output have the same expectation. -/
theorem expect_congr_of_allOutputs {c : ProbComp α} {P : α → Prop} (hc : c.AllOutputs P)
    {f g : α → ℝ} (h : ∀ a, P a → f a = g a) : ProbComp.expect c f = ProbComp.expect c g :=
  le_antisymm (ProbComp.expect_mono_of_allOutputs hc fun a ha => (h a ha).le)
    (ProbComp.expect_mono_of_allOutputs hc fun a ha => (h a ha).ge)

/-- **Fubini for a uniform sample:** `𝔼_c[𝔼_{t ← T}[h a t]] = 𝔼_{t ← T}[𝔼_c[h a t]]`. -/
theorem expect_expect_sample (c : ProbComp α) (T : Type) [Fintype T] [Nonempty T]
    (h : α → T → ℝ) :
    ProbComp.expect c (fun a => ProbComp.expect (ProbComp.sample T) (h a)) =
      ProbComp.expect (ProbComp.sample T) fun t => ProbComp.expect c fun a => h a t := by
  simp only [ProbComp.expect_sample]
  rw [ProbComp.expect_const_mul, ProbComp.expect_sum]

/-- Two continuations that agree on every possible output give the same computation:
`c.bind f = c.bind g` when `f a = g a` whenever `P a`, and `c.AllOutputs P`. -/
theorem bind_congr_of_allOutputs {ι : Type} {spec : OracleSpec ι} {c : OracleComp spec α}
    {P : α → Prop} (hc : c.AllOutputs P) {f g : α → OracleComp spec β}
    (h : ∀ a, P a → f a = g a) : c.bind f = c.bind g := by
  induction c with
  | pure a => exact h a hc
  | query i x k ih =>
    rw [OracleComp.query_bind, OracleComp.query_bind]
    congr 1
    funext y
    exact ih y (OracleComp.allOutputs_query.1 hc y)

end Expect

/-! ### One-shot coins drawn in advance -/

section Eager

variable {ι σ α T : Type} {spec : OracleSpec ι} [Fintype T] [Nonempty T]

/-- From a used state, an implementation that agrees with `O` there simulates like `O`. -/
private theorem simulate_eq_of_used (O O' : QueryImpl spec σ unifSpec) (used : σ → Prop)
    (hused : ∀ i x s, used s → O' i x s = O i x s)
    (hstick : ∀ i x s, used s → (O i x s).AllOutputs fun p => used p.2)
    (c : OracleComp spec α) {s : σ} (hs : used s) : simulate O' c s = simulate O c s := by
  induction c generalizing s with
  | pure a => rw [simulate_pure, simulate_pure]
  | query i x k ih =>
    rw [simulate_query, simulate_query, hused i x s hs]
    exact bind_congr_of_allOutputs (hstick i x s hs) fun p hp => ih p.1 hp

/-- **One-shot coins drawn in advance.** Let `O` be an implementation and `OE t` its variants with
coins `t ∈ T` fixed in advance, and let `used` mark the states after the coins are spent:
- from a used state, `OE t` is `O`, and `O` keeps the state used;
- from an unused state, a call either does not use the coins (`OE t` is `O` for every `t`, and the
  state stays unused), or it is the one that spends them (`O` samples `t` and runs `OE t`, and
  every successor is used).

Then from an unused state, `O`'s simulation has the law of `OE t`'s, averaged over `t`:
`𝔼[G(simulate O c s)] = 𝔼_{t ← T} 𝔼[G(simulate (OE t) c s)]`.

**Proof sketch.** Induction on `c`. From used states the two simulations coincide
(`simulate_eq_of_used`). At a query from an unused state: in the first case, rewrite the call,
apply the induction hypothesis at the (unused) successors and exchange the expectations
(`expect_expect_sample`); in the second, expand `O`'s sample and conclude from the coincidence at
the (used) successors. -/
theorem expect_simulate_eager (O : QueryImpl spec σ unifSpec) (OE : T → QueryImpl spec σ unifSpec)
    (used : σ → Prop) (hused : ∀ t i x s, used s → OE t i x s = O i x s)
    (hstick : ∀ i x s, used s → (O i x s).AllOutputs fun p => used p.2)
    (hfresh : ∀ i x s, ¬ used s →
      (∀ t, OE t i x s = O i x s ∧ (O i x s).AllOutputs fun p => ¬ used p.2) ∨
      (O i x s = (ProbComp.sample T).bind (fun t => OE t i x s) ∧
        ∀ t, (OE t i x s).AllOutputs fun p => used p.2))
    (c : OracleComp spec α) (G : α × σ → ℝ) {s : σ} (hs : ¬ used s) :
    ProbComp.expect (simulate O c s) G =
      ProbComp.expect (ProbComp.sample T) fun t => ProbComp.expect (simulate (OE t) c s) G := by
  induction c generalizing s with
  | pure a =>
    simp only [simulate_pure, ProbComp.expect_pure]
    exact (ProbComp.expect_const _ _).symm
  | query i x k ih =>
    simp only [simulate_query, ProbComp.expect_bind]
    rcases hfresh i x s hs with h | ⟨h, hu⟩
    · have hO : ∀ t, OE t i x s = O i x s := fun t => (h t).1
      have hun : (O i x s).AllOutputs fun p => ¬ used p.2 :=
        (h (Classical.arbitrary T)).2
      simp only [hO]
      rw [expect_congr_of_allOutputs hun fun p hp => ih p.1 hp, expect_expect_sample]
    · rw [h, ProbComp.expect_bind]
      refine congrArg _ (funext fun t => ?_)
      refine expect_congr_of_allOutputs (hu t) fun p hp => ?_
      rw [simulate_eq_of_used O (OE t) used (hused t) hstick _ hp]

end Eager

/-! ### Equal until bad, for functions of the final state -/

section UntilBad

variable {ι σ α : Type} {spec : OracleSpec ι}

/-- **Equal until bad, in expectation, for functions of the output and the final state.** Let two
implementations give, from every good state, the same law to good successors, and let each keep
bad states bad. Then from a good state, for every function `G` of the output and the final state,
`𝔼[G · 1_{good}]` is the same under both simulations. This generalizes `prob_eq_until_bad`
(`Games/Hopping.lean`), whose events read only the output.

**Proof sketch.** Induction on the computation. From a bad successor the continuation's value is
`0` on both sides (`simulate_allOutputs_bad`); from a good one the two values agree by induction;
so both expectations only see the values at good successors, which `hagree` equates. -/
theorem expect_eq_until_bad {impl₀ impl₁ : QueryImpl spec σ unifSpec} (bad : σ → Prop)
    [DecidablePred bad]
    (hagree : ∀ i x s, ¬ bad s → ∀ g : spec.rng i × σ → ℝ,
      ProbComp.expect (impl₀ i x s) (fun ys => if bad ys.2 then 0 else g ys) =
        ProbComp.expect (impl₁ i x s) (fun ys => if bad ys.2 then 0 else g ys))
    (hstick₀ : ∀ i x s, bad s → (impl₀ i x s).AllOutputs fun ys => bad ys.2)
    (hstick₁ : ∀ i x s, bad s → (impl₁ i x s).AllOutputs fun ys => bad ys.2)
    (c : OracleComp spec α) (G : α × σ → ℝ) {s : σ} (hs : ¬ bad s) :
    ProbComp.expect (simulate impl₀ c s) (fun r => if bad r.2 then 0 else G r) =
      ProbComp.expect (simulate impl₁ c s) (fun r => if bad r.2 then 0 else G r) := by
  induction c generalizing s with
  | pure a => rw [simulate_pure, simulate_pure]
  | query i x k ih =>
    simp only [simulate_query, ProbComp.expect_bind]
    have hz : ∀ (impl : QueryImpl spec σ unifSpec),
        (∀ i x s, bad s → (impl i x s).AllOutputs fun ys => bad ys.2) →
        ∀ ys : spec.rng i × σ, bad ys.2 →
          ProbComp.expect (simulate impl (k ys.1) ys.2) (fun r => if bad r.2 then 0 else G r) =
            0 := by
      intro impl hst ys hb
      rw [expect_congr_of_allOutputs (simulate_allOutputs_bad bad hst _ hb)
        (g := fun _ => 0) fun r hr => if_pos hr, ProbComp.expect_const]
    have h0 : ∀ ys : spec.rng i × σ,
        ProbComp.expect (simulate impl₀ (k ys.1) ys.2) (fun r => if bad r.2 then 0 else G r) =
          if bad ys.2 then 0 else
            ProbComp.expect (simulate impl₁ (k ys.1) ys.2) (fun r => if bad r.2 then 0 else G r) := by
      intro ys
      by_cases hb : bad ys.2
      · rw [if_pos hb, hz impl₀ hstick₀ ys hb]
      · rw [if_neg hb, ih ys.1 hb]
    have h1 : ∀ ys : spec.rng i × σ,
        ProbComp.expect (simulate impl₁ (k ys.1) ys.2) (fun r => if bad r.2 then 0 else G r) =
          if bad ys.2 then 0 else
            ProbComp.expect (simulate impl₁ (k ys.1) ys.2) (fun r => if bad r.2 then 0 else G r) := by
      intro ys
      by_cases hb : bad ys.2
      · rw [if_pos hb, hz impl₁ hstick₁ ys hb]
      · rw [if_neg hb]
    rw [funext h0, hagree i x s hs, ← funext h1]

end UntilBad

/-! ### Chunk maps -/

section Chunks

/-- One step of a chunk map on `⟨ctx, w⟩` with `ctx = ⟨1^n, _⟩`: drop the first `c(n)` bits of `w`:
`chunkStep c x = ⟨fst x, (snd x).drop c(|fst (fst x)|)⟩`. -/
def chunkStep (c : PolyExpr) (x : List Bool) : List Bool :=
  pairEncode (pairFstD x) ((pairSndD x).drop (c.eval (pairFstD (pairFstD x)).length))

/-- `chunkStep c x = ⟨fst x, (snd x).drop c(|fst (fst x)|)⟩`. -/
theorem chunkStep_eq (c : PolyExpr) (x : List Bool) :
    chunkStep c x =
      pairEncode (pairFstD x) ((pairSndD x).drop (c.eval (pairFstD (pairFstD x)).length)) :=
  rfl

/-- The emission of a chunk map on `⟨ctx, w⟩`: nothing on `w = []`, and `f ctx` of the first
`c(n)` bits of `w` otherwise. -/
def chunkEmit (c : PolyExpr) (f : List Bool → List Bool → List Bool) (x : List Bool) :
    List Bool :=
  if decide (pairSndD x = []) then []
  else f (pairFstD x) ((pairSndD x).take (c.eval (pairFstD (pairFstD x)).length))

/-- `chunkEmit c f x = if snd x = [] then [] else f (fst x) ((snd x).take c(|fst (fst x)|))`. -/
theorem chunkEmit_eq (c : PolyExpr) (f : List Bool → List Bool → List Bool) (x : List Bool) :
    chunkEmit c f x = if decide (pairSndD x = []) then []
      else f (pairFstD x) ((pairSndD x).take (c.eval (pairFstD (pairFstD x)).length)) :=
  rfl

/-- **The chunk map** of `f` with chunk length `c`, on `x = ⟨ctx, w⟩` with `ctx = ⟨1^n, _⟩`: the
concatenation of `f ctx` over the consecutive `c(n)`-bit chunks of `w`, computed by `|x| + 1`
rounds of `chunkStep`: `chunkMap c f x = (List.range (|x| + 1)).flatMap fun i =>
chunkEmit c f (chunkStep c)^[i] x`. -/
def chunkMap (c : PolyExpr) (f : List Bool → List Bool → List Bool) (x : List Bool) : List Bool :=
  (List.range (x.length + 1)).flatMap fun i => chunkEmit c f ((chunkStep c)^[i] x)

/-- `chunkMap c f x = (List.range (|x| + 1)).flatMap fun i => chunkEmit c f (chunkStep c)^[i] x`. -/
theorem chunkMap_eq (c : PolyExpr) (f : List Bool → List Bool → List Bool) (x : List Bool) :
    chunkMap c f x =
      (List.range (x.length + 1)).flatMap fun i => chunkEmit c f ((chunkStep c)^[i] x) :=
  rfl

/-- One step never makes a word longer than `max |x| 2` (a malformed word becomes `⟨[], []⟩`). -/
private theorem length_chunkStep_le (c : PolyExpr) (x : List Bool) :
    (chunkStep c x).length ≤ max x.length 2 := by
  rw [chunkStep_eq, length_pairEncode, List.length_drop]
  by_cases h : pairDecode x = none
  · rw [pairFstD_of_pairDecode_eq_none h, pairSndD_of_pairDecode_eq_none h]
    simp only [List.length_nil]
    omega
  · obtain ⟨⟨a, b⟩, hab⟩ := Option.ne_none_iff_exists'.1 h
    rw [eq_pairEncode_of_pairDecode x a b hab, pairFstD_pairEncode, pairSndD_pairEncode,
      length_pairEncode]
    omega

/-- The iterated step keeps words within `|x| + 2` bits. -/
private theorem length_iterate_chunkStep_le (c : PolyExpr) (x : List Bool) (i : ℕ) :
    ((chunkStep c)^[i] x).length ≤ x.length + 2 := by
  suffices h : ((chunkStep c)^[i] x).length ≤ max x.length 2 by omega
  induction i with
  | zero => exact le_max_left _ _
  | succ i ih =>
    rw [Function.iterate_succ_apply']
    exact (length_chunkStep_le c _).trans (max_le ih (le_max_right _ _))

/-- **Chunk maps are polynomial-time** when `f` is, read as a function of `⟨ctx, chunk⟩`
(`Complexity.polyTimeComputable_iterateEmit` with the step `chunkStep`, which never lengthens a
word, and `|x|` rounds). -/
theorem polyTimeComputable_chunkMap (c : PolyExpr) {f : List Bool → List Bool → List Bool}
    (hf : PolyTimeComputable fun z => f (pairFstD z) (pairSndD z)) :
    PolyTimeComputable (chunkMap c f) := by
  have hF := polyTimeComputable_pairFstD
  have hD := polyTimeComputable_pairSndD
  have hcut : PolyTimeComputable fun x : List Bool =>
      pairEncode (pairFstD (pairFstD x)) (pairSndD x) := (hF.comp hF).pairEncode hD
  have hdrop : PolyTimeComputable fun x : List Bool =>
      (pairSndD x).drop (c.eval (pairFstD (pairFstD x)).length) :=
    ((polyTimeComputable_pairDropPoly c).comp hcut).congr fun x => by
      simp only [Function.comp_apply, pairFstD_pairEncode, pairSndD_pairEncode]
  have htake : PolyTimeComputable fun x : List Bool =>
      (pairSndD x).take (c.eval (pairFstD (pairFstD x)).length) :=
    ((polyTimeComputable_pairTakePoly c).comp hcut).congr fun x => by
      simp only [Function.comp_apply, pairFstD_pairEncode, pairSndD_pairEncode]
  have hstep : PolyTimeComputable (chunkStep c) := hF.pairEncode hdrop
  have hemit : PolyTimeComputable (chunkEmit c f) :=
    polyTimeComputable_ite (polyTimeComputable_isNil.comp hD) (polyTimeComputable_const [])
      ((hf.comp (hF.pairEncode htake)).congr fun x => by
        simp only [Function.comp_apply, pairFstD_pairEncode, pairSndD_pairEncode])
  exact (polyTimeComputable_iterateEmit hstep hemit .var (.add .var (.const 2))
    (fun x i _ => by
      rw [PolyExpr.eval_add, PolyExpr.eval_var, PolyExpr.eval_const]
      exact length_iterate_chunkStep_le c x i)).congr
    fun x => by rw [PolyExpr.eval_var, chunkMap_eq]

/-- Reading the suffixes of a list within at least its length many steps (DL-30–36 overlap: the
general form of `Forward`'s private `flatMap_range_drop`, with the reading of a nonempty suffix
assumed only for the list's members). -/
private theorem flatMap_range_drop {β : Type} (F : List β → List Bool) (g : β → List Bool)
    (hnil : F [] = []) :
    ∀ (l : List β), (∀ e ∈ l, ∀ t, F (e :: t) = g e) → ∀ m : ℕ, l.length ≤ m →
      ((List.range m).flatMap fun i => F (l.drop i)) = l.flatMap g := by
  intro l
  induction l with
  | nil =>
    intro _ m _
    rw [List.flatMap_nil]
    refine List.flatMap_eq_nil_iff.2 fun i _ => ?_
    rw [List.drop_nil, hnil]
  | cons e t ih =>
    intro hcons m hm
    obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by rw [List.length_cons] at hm; omega⟩
    rw [List.range_succ_eq_map, List.flatMap_cons, List.flatMap_map, List.drop_zero,
      hcons e List.mem_cons_self, List.flatMap_cons]
    congr 1
    simp only [List.drop_succ_cons]
    exact ih (fun e' he' => hcons e' (List.mem_cons_of_mem _ he')) m'
      (by rw [List.length_cons] at hm; omega)

/-- **The chunk map of a concatenation of chunks:** if every chunk has `c(n) > 0` bits, the chunk
map of `⟨⟨1^n, e⟩, chunks.flatten⟩` is the concatenation of `f ⟨1^n, e⟩` over the chunks.

**Proof sketch.** The `i`-th step leaves `(chunks.drop i).flatten` (dropping a first chunk of
`c(n)` bits), whose emission is `f` of the `i`-th chunk while chunks remain and `[]` afterwards;
there are at most `|x| + 1` chunks since each has a bit. -/
theorem chunkMap_flatten (c : PolyExpr) (f : List Bool → List Bool → List Bool) (n : ℕ)
    (e : List Bool) (chunks : List (List Bool)) (hlen : ∀ ch ∈ chunks, ch.length = c.eval n)
    (hpos : 0 < c.eval n) :
    chunkMap c f (pairEncode (pairEncode (List.replicate n true) e) chunks.flatten) =
      (chunks.map (f (pairEncode (List.replicate n true) e))).flatten := by
  set ctx := pairEncode (List.replicate n true) e
  have hit : ∀ i, (chunkStep c)^[i] (pairEncode ctx chunks.flatten) =
      pairEncode ctx (chunks.drop i).flatten := by
    intro i
    induction i with
    | zero => rfl
    | succ i ih =>
      rw [Function.iterate_succ_apply', ih, chunkStep_eq, pairFstD_pairEncode,
        pairSndD_pairEncode, pairFstD_pairEncode, List.length_replicate, ← List.tail_drop]
      cases h : chunks.drop i with
      | nil => rw [List.flatten_nil, List.drop_nil, List.tail_nil, List.flatten_nil]
      | cons ch rest =>
        have hch : ch.length = c.eval n :=
          hlen ch (List.mem_of_mem_drop (h ▸ List.mem_cons_self))
        rw [List.flatten_cons, List.tail_cons, ← hch, List.drop_left]
  have hlen' : chunks.length ≤ (pairEncode ctx chunks.flatten).length + 1 := by
    have : chunks.length ≤ chunks.flatten.length := by
      rw [List.length_flatten]
      clear hit
      induction chunks with
      | nil => exact le_rfl
      | cons ch rest ih =>
        rw [List.map_cons, List.sum_cons, List.length_cons]
        have := hlen ch List.mem_cons_self
        have := ih fun ch' h' => hlen ch' (List.mem_cons_of_mem _ h')
        omega
    rw [length_pairEncode]
    omega
  rw [chunkMap_eq]
  simp only [hit]
  rw [flatMap_range_drop (fun l => chunkEmit c f (pairEncode ctx l.flatten)) (f ctx)
    (by
      show chunkEmit c f (pairEncode ctx ([] : List (List Bool)).flatten) = []
      rw [List.flatten_nil, chunkEmit_eq, pairSndD_pairEncode, if_pos (decide_eq_true rfl)])
    chunks (fun ch hch t => ?_) _ hlen', List.flatMap_def]
  have hl := hlen ch hch
  have hne : ch ++ t.flatten ≠ [] := fun h => by
    rw [List.append_eq_nil_iff] at h
    rw [h.1, List.length_nil] at hl
    omega
  show chunkEmit c f (pairEncode ctx (ch :: t).flatten) = f ctx ch
  rw [chunkEmit_eq, pairSndD_pairEncode, pairFstD_pairEncode, pairFstD_pairEncode,
    List.length_replicate, List.flatten_cons, if_neg (by simpa using hne), ← hl, List.take_left]

end Chunks

end TCSlib.Cryptography.Composability.NMSim
