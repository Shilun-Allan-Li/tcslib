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
# Chunk maps for Theorem 174.8

A generic tool used by both directions of [PS10, Theorem 174.8], not specific to encryption:
**chunk maps** (`chunkMap`), a polynomial-time map applied to the consecutive fixed-length chunks
of a string, concatenated (`polyTimeComputable_chunkMap`, `chunkMap_flatten`). The machines of
both reductions read and write their tuples of ciphertexts and entries this way.

The other generic facts first proved here now live in the Games layer: budget reduction
(`Games.buildComp_budget_eq`, `Complexity.NUPPT.toCompOn_budget_eq`), output-length transport
(`Games.expect_toCompOn_outLen`), reasoning on the possible outputs
(`Games.ProbComp.expect_congr_of_allOutputs`, `Games.ProbComp.expect_expect_sample`,
`Games.OracleComp.bind_congr_of_allOutputs`), one-shot coins drawn in advance
(`Games.expect_simulate_eager`) and equal until bad in expectation (`Games.expect_eq_until_bad`).

## Main definitions

* `NMSim.chunkStep`, `NMSim.chunkEmit`, `NMSim.chunkMap`.

## Main results

* `NMSim.polyTimeComputable_chunkMap`, `NMSim.chunkMap_flatten`.

## References

* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed., January 2010,
  Theorem 174.8 (book p. 174).
-/

namespace TCSlib.Cryptography.Composability.NMSim

open Complexity Turing TCSlib.Cryptography TCSlib.Cryptography.Games

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
word, and `|x|` rounds).

**Proof sketch.** The step (keep `ctx`, drop `c(n)` bits) and the emission (`[]` on an empty
rest, else `f ctx` of the next `c(n)` bits) are polynomial-time by the pair readers,
`pairTakePoly`/`pairDropPoly` and `polyTimeComputable_ite`. The iterates stay within `|x| + 2`
bits (`length_iterate_chunkStep_le`), so `polyTimeComputable_iterateEmit` gives `chunkMap_eq`. -/
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
