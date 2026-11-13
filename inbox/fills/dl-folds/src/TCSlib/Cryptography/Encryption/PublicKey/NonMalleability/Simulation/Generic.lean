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
of a string, concatenated (`polyTimeComputable_chunkMap`, `chunkMap_flatten`): an instance of
iterate and emit (`Games.iterEmit`). The machines of
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
rounds of `chunkStep` (iterate and emit, `Games.iterEmit`): `chunkMap c f x =
(List.range (|x| + 1)).flatMap fun i => chunkEmit c f (chunkStep c)^[i] x`. -/
def chunkMap (c : PolyExpr) (f : List Bool → List Bool → List Bool) (x : List Bool) : List Bool :=
  iterEmit (chunkStep c) (chunkEmit c f) (x.length + 1) x

/-- `chunkMap c f x = (List.range (|x| + 1)).flatMap fun i => chunkEmit c f (chunkStep c)^[i] x`
(`Games.iterEmit_eq`). -/
theorem chunkMap_eq (c : PolyExpr) (f : List Bool → List Bool → List Bool) (x : List Bool) :
    chunkMap c f x =
      (List.range (x.length + 1)).flatMap fun i => chunkEmit c f ((chunkStep c)^[i] x) := by
  rw [chunkMap, iterEmit_eq]

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

/-- **Chunk maps are polynomial-time** when `f` is, read as a function of `⟨ctx, chunk⟩`
(`Games.polyTimeComputable_iterEmit` with the step `chunkStep`, which never makes a word longer
than `max |x| 2`).

**Proof sketch.** The step (keep `ctx`, drop `c(n)` bits) and the emission (`[]` on an empty
rest, else `f ctx` of the next `c(n)` bits) are polynomial-time by the pair readers,
`pairTakePoly`/`pairDropPoly` and `polyTimeComputable_ite`; one step never lengthens a word beyond
`max |x| 2` (`length_chunkStep_le`), so `polyTimeComputable_iterEmit` applies. -/
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
  exact (polyTimeComputable_iterEmit hstep hemit 2 (length_chunkStep_le c)).congr
    fun x => by rw [chunkMap]

/-- **The chunk map of a concatenation of chunks:** if every chunk has `c(n) > 0` bits, the chunk
map of `⟨⟨1^n, e⟩, chunks.flatten⟩` is the concatenation of `f ⟨1^n, e⟩` over the chunks.

**Proof sketch.** `Games.iterEmit_encode` with the encoding `l ↦ ⟨ctx, l.flatten⟩`: a step drops a
first chunk of `c(n)` bits and fixes `⟨ctx, []⟩`; the emission is `f ctx` of the first chunk while
chunks remain and `[]` afterwards; there are at most `|x| + 1` chunks since each has a bit. -/
theorem chunkMap_flatten (c : PolyExpr) (f : List Bool → List Bool → List Bool) (n : ℕ)
    (e : List Bool) (chunks : List (List Bool)) (hlen : ∀ ch ∈ chunks, ch.length = c.eval n)
    (hpos : 0 < c.eval n) :
    chunkMap c f (pairEncode (pairEncode (List.replicate n true) e) chunks.flatten) =
      (chunks.map (f (pairEncode (List.replicate n true) e))).flatten := by
  set ctx := pairEncode (List.replicate n true) e
  have hlen' : chunks.length ≤ (pairEncode ctx chunks.flatten).length + 1 := by
    have : chunks.length ≤ chunks.flatten.length := by
      rw [List.length_flatten]
      induction chunks with
      | nil => exact le_rfl
      | cons ch rest ih =>
        rw [List.map_cons, List.sum_cons, List.length_cons]
        have := hlen ch List.mem_cons_self
        have := ih fun ch' h' => hlen ch' (List.mem_cons_of_mem _ h')
        omega
    rw [length_pairEncode]
    omega
  have hstep_nil : chunkStep c (pairEncode ctx ([] : List (List Bool)).flatten) =
      pairEncode ctx ([] : List (List Bool)).flatten := by
    rw [List.flatten_nil, chunkStep_eq, pairFstD_pairEncode, pairSndD_pairEncode, List.drop_nil]
  have hstep : ∀ ch ∈ chunks, ∀ t : List (List Bool),
      chunkStep c (pairEncode ctx (ch :: t).flatten) = pairEncode ctx t.flatten := by
    intro ch hch t
    rw [chunkStep_eq, pairFstD_pairEncode, pairSndD_pairEncode, pairFstD_pairEncode,
      List.length_replicate, List.flatten_cons, ← hlen ch hch, List.drop_left]
  have hnil : chunkEmit c f (pairEncode ctx ([] : List (List Bool)).flatten) = [] := by
    rw [List.flatten_nil, chunkEmit_eq, pairSndD_pairEncode, if_pos (decide_eq_true rfl)]
  have hcons : ∀ ch ∈ chunks, ∀ t : List (List Bool),
      chunkEmit c f (pairEncode ctx (ch :: t).flatten) = f ctx ch := by
    intro ch hch t
    have hl := hlen ch hch
    have hne : ch ++ t.flatten ≠ [] := fun h => by
      rw [List.append_eq_nil_iff] at h
      rw [h.1, List.length_nil] at hl
      omega
    rw [chunkEmit_eq, pairSndD_pairEncode, pairFstD_pairEncode, pairFstD_pairEncode,
      List.length_replicate, List.flatten_cons, if_neg (by simpa using hne), ← hl, List.take_left]
  rw [chunkMap, iterEmit_encode (chunkStep c) (chunkEmit c f) (fun l => pairEncode ctx l.flatten)
    (f ctx) chunks hstep_nil hstep hnil hcons _ hlen', List.flatMap_def]

end Chunks

end TCSlib.Cryptography.Composability.NMSim
