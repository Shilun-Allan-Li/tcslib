/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TCSlib.Cryptography.Games.Efficiency.Strings
import TCSlib.Cryptography.Games.Bridges.QueryTree
import TCSlib.Cryptography.Pseudorandom.Functions.Asymptotic.Defs

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# From one-oracle `bitCodec` machines to next-query machines (efficiency fill, T4)

The translators behind `Games.exists_toOracleAdversary_of_bitCodec` (route note
`briefs/pass-shelat-ch5-8/design/S2b-efficiency.md`, §"T4"). A machine `B` against one
`bitCodec` oracle with a one-bit output reads `⟨[], log⟩` and writes `bitCodec` moves; a
next-query machine of the ch. 2–4 layer reads a history (`encodeHist`) and writes
`decodeOracleMove` moves. Two polynomial-time maps translate:
- `bridgePre` turns the history `⟨⟨x₁, y₁⟩, ⟨…, []⟩⟩` into `⟨[], ⟨⟨[], ⟨x₁, y₁⟩⟩, ⟨…, []⟩⟩⟩`,
  the empty input followed by the `bitCodec` log (the index of the only oracle is `1^0 = []`);
- `bridgePost` turns a canonical query word `⟨[false], ⟨[], x⟩⟩` into `⟨[false], x⟩`, the word
  `⟨[true], [true]⟩` into the verdict `[true, true]`, and every other word into `[true, false]`.

Both decoders check the payload length `ℓ₁(n)` themselves and agree on it, so neither map
needs the parameter.

## Main definitions

* `EffFill.relabelEmit`, `EffFill.relabel`, `EffFill.bridgePre`, `EffFill.bridgePost`.

## Main results

* `EffFill.bridgePre_encodeHist`: the history of a log translates to the log.
* `EffFill.bridgePost_spec`: the translated move is the decoded move.
* `EffFill.eval_buildTree_bridge`: the two computations evaluate alike against every oracle.

## References

* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed., January 2010,
  Definition 96.1 (oracle indistinguishability against oracle machines).
-/

namespace TCSlib.Cryptography.Games.EffFill

open Complexity Turing

/-! ### The history translator -/

/-- The piece emitted for the suffix `w` of an encoded history: `⟨⟨[], fst w⟩, []⟩` for a
non-empty suffix, nothing for the empty one. -/
def relabelEmit (w : List Bool) : List Bool :=
  if w = [] then [] else pairEncode (pairEncode [] (pairFstD w)) []

/-- `relabelEmit w = if w = [] then [] else ⟨⟨[], fst w⟩, []⟩`. -/
theorem relabelEmit_eq (w : List Bool) :
    relabelEmit w = if w = [] then [] else pairEncode (pairEncode [] (pairFstD w)) [] :=
  rfl

/-- The pieces of the first `m` suffixes `w, snd w, snd (snd w), …`, concatenated. -/
def relabelN (m : ℕ) (w : List Bool) : List Bool :=
  (List.range m).flatMap fun i => relabelEmit (pairSndD^[i] w)

/-- `relabelN m w = ⋃_{i < m} relabelEmit (snd^i w)`. -/
theorem relabelN_eq (m : ℕ) (w : List Bool) :
    relabelN m w = (List.range m).flatMap fun i => relabelEmit (pairSndD^[i] w) :=
  rfl

/-- **The history translator's body:** the pieces of the first `|x| + 1` suffixes of `x`. -/
def relabel (x : List Bool) : List Bool := relabelN (x.length + 1) x

/-- `relabel x = relabelN (|x| + 1) x`. -/
theorem relabel_eq (x : List Bool) : relabel x = relabelN (x.length + 1) x := rfl

/-- **The history translator:** `bridgePre x = ⟨[], relabel x⟩`. -/
def bridgePre (x : List Bool) : List Bool := pairEncode [] (relabel x)

/-- `bridgePre x = ⟨[], relabel x⟩`. -/
theorem bridgePre_eq (x : List Bool) : bridgePre x = pairEncode [] (relabel x) := rfl

/-- The empty word has no pieces: `relabelN m [] = []`. -/
theorem relabelN_nil (m : ℕ) : relabelN m [] = [] := by
  rw [relabelN_eq, List.flatMap_eq_nil_iff]
  intro i _
  have h : ∀ j, pairSndD^[j] ([] : List Bool) = [] := by
    intro j
    induction j with
    | zero => rfl
    | succ j ih =>
      rw [Function.iterate_succ_apply', ih]
      exact pairSndD_of_pairDecode_eq_none Turing.pairDecode_nil
  rw [h, relabelEmit_eq, if_pos rfl]

/-- One more suffix: `relabelN (m + 1) w = relabelEmit w ++ relabelN m (snd w)`. -/
theorem relabelN_succ (m : ℕ) (w : List Bool) :
    relabelN (m + 1) w = relabelEmit w ++ relabelN m (pairSndD w) := by
  rw [relabelN_eq, relabelN_eq, List.range_succ_eq_map, List.flatMap_cons, List.flatMap_map]
  rfl

/-- The history of a one-oracle `bitCodec` log, as (query, answer) pairs. -/
def logHist {ℓ₁ ℓ₂ : ℕ} (L : QueryLog (bitSpec (fun _ : Fin 1 => ℓ₁) (fun _ => ℓ₂))) :
    List ((Fin ℓ₁ → Bool) × (Fin ℓ₂ → Bool)) :=
  L.map fun e => (e.2.1, e.2.2)

/-- `logHist L` maps each entry `⟨0, x, y⟩` to `(x, y)`. -/
theorem logHist_eq {ℓ₁ ℓ₂ : ℕ} (L : QueryLog (bitSpec (fun _ : Fin 1 => ℓ₁) (fun _ => ℓ₂))) :
    logHist L = L.map fun e => (e.2.1, e.2.2) :=
  rfl

/-- **The pieces of an encoded history form the `bitCodec` log:** for every `m ≥ |L|`,
`relabelN m (encodeHist (logHist L)) = encodeLog L`.

**Proof sketch.** Induction on `L`. The empty history is `[]`, which has no pieces
(`relabelN_nil`). A non-empty history `⟨⟨x, y⟩, rest⟩` emits `⟨⟨[], ⟨x, y⟩⟩, []⟩` and continues
with `rest` (`relabelN_succ`, `encodeHist_cons`); the piece is the entry's `bitCodec` encoding
(`bitCodec_encodeEntry`, the index of the only oracle being `1^0 = []`), and the concatenation is
the nested pair (`GGMRed.pairEncode_append_right`, `encodeLog_cons`). -/
theorem relabelN_encodeHist {ℓ₁ ℓ₂ : ℕ} (dα : ℕ) :
    ∀ (L : QueryLog (bitSpec (fun _ : Fin 1 => ℓ₁) (fun _ => ℓ₂))) (m : ℕ), L.length ≤ m →
      relabelN m (encodeHist (logHist L)) =
        (bitCodec (fun _ : Fin 1 => ℓ₁) (fun _ => ℓ₂) dα).encodeLog L
  | [], m, _ => by
    rw [logHist_eq, List.map_nil, encodeHist_nil, relabelN_nil, MachineCodec.encodeLog_nil]
  | e :: L, m, hm => by
    obtain ⟨m, rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by rw [List.length_cons] at hm; omega⟩
    rw [logHist_eq, List.map_cons, ← logHist_eq, encodeHist_cons, relabelN_succ,
      pairSndD_pairEncode, relabelN_encodeHist dα L m (by rw [List.length_cons] at hm; omega),
      relabelEmit_eq, if_neg (pairEncode_ne_nil _ _), pairFstD_pairEncode,
      MachineCodec.encodeLog_cons, bitCodec_encodeEntry, ← GGMRed.pairEncode_append_right,
      List.nil_append, Fin.fin_one_eq_zero e.1, Fin.val_zero, List.replicate_zero]

/-- An encoded history has at least as many bits as entries. -/
theorem length_le_length_encodeHist {ℓ₁ ℓ₂ : ℕ} :
    ∀ h : List ((Fin ℓ₁ → Bool) × (Fin ℓ₂ → Bool)), h.length ≤ (encodeHist h).length
  | [] => Nat.zero_le _
  | p :: h => by
    rw [encodeHist_cons, length_pairEncode, List.length_cons]
    have := length_le_length_encodeHist h
    omega

/-- **The history translator on a history:** `bridgePre (encodeHist (logHist L)) =
⟨[], encodeLog L⟩`. -/
theorem bridgePre_encodeHist {ℓ₁ ℓ₂ : ℕ} (dα : ℕ)
    (L : QueryLog (bitSpec (fun _ : Fin 1 => ℓ₁) (fun _ => ℓ₂))) :
    bridgePre (encodeHist (logHist L)) =
      pairEncode [] ((bitCodec (fun _ : Fin 1 => ℓ₁) (fun _ => ℓ₂) dα).encodeLog L) := by
  rw [bridgePre_eq, relabel_eq, relabelN_encodeHist dα L _]
  have h1 := length_le_length_encodeHist (logHist L)
  rw [logHist_eq, List.length_map] at h1
  rw [logHist_eq]
  omega

/-- The emitted piece is polynomial-time. -/
theorem relabelEmit_poly : PolyTimeComputable relabelEmit :=
  (polyTimeComputable_ite polyTimeComputable_isNil (polyTimeComputable_const [])
    (((polyTimeComputable_const []).pairEncode polyTimeComputable_pairFstD).pairEncode
      (polyTimeComputable_const []))).congr fun w => by
    rw [relabelEmit_eq]
    by_cases h : w = []
    · rw [if_pos h, decide_eq_true h]
      rfl
    · rw [if_neg h, decide_eq_false h]
      rfl

/-- **The history translator is polynomial-time** (`Complexity.polyTimeComputable_iterateEmit`
with the step `pairSndD`, `|x| + 1` rounds and the orbit bound `|x|`). -/
theorem bridgePre_poly : PolyTimeComputable bridgePre := by
  have horbit : ∀ (x : List Bool) (i : ℕ), i ≤ PolyExpr.var.eval x.length →
      (pairSndD^[i] x).length ≤ PolyExpr.var.eval x.length := by
    intro x i _
    clear * -
    rw [PolyExpr.eval_var]
    induction i with
    | zero => exact le_rfl
    | succ i ih => rw [Function.iterate_succ_apply']; exact (length_pairSndD_le _).trans ih
  have h := polyTimeComputable_iterateEmit polyTimeComputable_pairSndD relabelEmit_poly .var .var
    horbit
  refine ((polyTimeComputable_const []).pairEncode h).congr fun x => ?_
  rw [bridgePre_eq, relabel_eq, relabelN_eq, PolyExpr.eval_var]

/-! ### The move translator -/

/-- **The move translator:** a canonical query word `⟨[false], ⟨[], x⟩⟩` becomes `⟨[false], x⟩`,
the output word `⟨[true], [true]⟩` becomes `[true, true]`, and every other word `[true, false]`. -/
def bridgePost (w : List Bool) : List Bool :=
  if w = pairEncode [false] (pairEncode [] (pairSndD (pairSndD w))) then
    pairEncode [false] (pairSndD (pairSndD w))
  else if w = pairEncode [true] [true] then [true, true] else [true, false]

/-- The defining equation of `bridgePost`. -/
theorem bridgePost_eq (w : List Bool) :
    bridgePost w =
      if w = pairEncode [false] (pairEncode [] (pairSndD (pairSndD w))) then
        pairEncode [false] (pairSndD (pairSndD w))
      else if w = pairEncode [true] [true] then [true, true] else [true, false] :=
  rfl

/-- **The move translator is polynomial-time** (`eq_poly` for the two tests). -/
theorem bridgePost_poly : PolyTimeComputable bridgePost := by
  have hx := polyTimeComputable_pairSndD.comp' polyTimeComputable_pairSndD
  have h1 := eq_poly polyTimeComputable_id ((polyTimeComputable_const [false]).pairEncode
    ((polyTimeComputable_const []).pairEncode hx))
  have h2 := eq_poly polyTimeComputable_id (polyTimeComputable_const (pairEncode [true] [true]))
  refine (polyTimeComputable_ite h1 ((polyTimeComputable_const [false]).pairEncode hx)
    (polyTimeComputable_ite h2 (polyTimeComputable_const [true, true])
      (polyTimeComputable_const [true, false]))).congr fun w => ?_
  rw [bridgePost_eq]
  simp only [id_eq, decide_eq_true_eq]

/-- **The translated move is the decoded move.** For every word `w`, either `decodeBitMove`
reads the query `x` (to the only oracle) and `decodeOracleMove` reads the query `x` off
`bridgePost w`, or `decodeBitMove` reads an output `a` and `decodeOracleMove` the verdict `a 0`.

**Proof sketch.** Three cases on `w`. A word `⟨[false], ⟨[], x⟩⟩` becomes `⟨[false], x⟩`: if
`|x| = ℓ₁` both decoders read the query (`decodeBitMove_query`,
`decodeOracleMove_pairEncode_ofFn`); otherwise both read the default, the all-`false` output and
the verdict `false` (`decodeBitMove_of_not_canonical`,
`decodeOracleMove_pairEncode_false_of_length_ne`). The word `⟨[true], [true]⟩` reads the output
`1` on both sides (`decodeBitMove_ret`, `decodeOracleMove_true_two`). Every other word becomes
`[true, false]`, the verdict `false`; `decodeBitMove` reads either the output `0` (the word
`⟨[true], [false]⟩`) or the default (`decodeBitMove_of_not_canonical`); its query words are all
of the first form, since `1^i = []` for `i : Fin 1`. -/
theorem bridgePost_spec (ℓ₁ ℓ₂ : ℕ) (w : List Bool) :
    (∃ x : Fin ℓ₁ → Bool,
      decodeBitMove (fun _ : Fin 1 => ℓ₁) (fun _ => ℓ₂) 1 w = .query 0 x ∧
        decodeOracleMove ℓ₁ (bridgePost w) = .query x) ∨
    (∃ a : Fin 1 → Bool,
      decodeBitMove (fun _ : Fin 1 => ℓ₁) (fun _ => ℓ₂) 1 w = .ret a ∧
        decodeOracleMove ℓ₁ (bridgePost w) = .ret (a 0)) := by
  by_cases hq : w = pairEncode [false] (pairEncode [] (pairSndD (pairSndD w)))
  · rw [bridgePost_eq, if_pos hq]
    set xw := pairSndD (pairSndD w)
    by_cases hx : xw.length = ℓ₁
    · obtain ⟨x, hxe⟩ := exists_ofFn_eq hx
      refine Or.inl ⟨x, ?_, ?_⟩
      · rw [hq, ← hxe]
        exact decodeBitMove_query (fun _ : Fin 1 => ℓ₁) (fun _ => ℓ₂) 1 0 x
      · rw [← hxe]
        exact decodeOracleMove_pairEncode_ofFn ℓ₁ x
    · refine Or.inr ⟨zeroBits 1, ?_, ?_⟩
      · refine decodeBitMove_of_not_canonical (fun i x h => hx ?_) (fun a h => ?_)
        · rw [hq, Fin.fin_one_eq_zero i, Fin.val_zero, List.replicate_zero] at h
          have h' := congrArg (fun v => pairSndD (pairSndD v)) h
          simp only [pairSndD_pairEncode] at h'
          rw [h', List.length_ofFn]
        · rw [hq] at h
          have h' := congrArg pairFstD h
          simp only [pairFstD_pairEncode] at h'
          exact absurd h' (by decide)
      · rw [decodeOracleMove_pairEncode_false_of_length_ne ℓ₁ hx, zeroBits_apply]
  · by_cases hr : w = pairEncode [true] [true]
    · refine Or.inr ⟨fun _ => true, ?_, ?_⟩
      · rw [hr]
        exact decodeBitMove_ret (fun _ : Fin 1 => ℓ₁) (fun _ => ℓ₂) 1 (fun _ => true)
      · rw [bridgePost_eq, if_neg hq, if_pos hr]
        exact decodeOracleMove_true_two ℓ₁ true
    · rw [bridgePost_eq, if_neg hq, if_neg hr, decodeOracleMove_true_two]
      by_cases hf : w = pairEncode [true] [false]
      · refine Or.inr ⟨fun _ => false, ?_, rfl⟩
        rw [hf]
        exact decodeBitMove_ret (fun _ : Fin 1 => ℓ₁) (fun _ => ℓ₂) 1 (fun _ => false)
      · refine Or.inr ⟨zeroBits 1, ?_, by rw [zeroBits_apply]⟩
        refine decodeBitMove_of_not_canonical (fun i x h => hq ?_) (fun a h => ?_)
        · rw [h, Fin.fin_one_eq_zero i, Fin.val_zero, List.replicate_zero, pairSndD_pairEncode,
            pairSndD_pairEncode]
        · have ha : List.ofFn a = [a 0] := by rw [List.ofFn_succ, List.ofFn_zero]
          rw [ha] at h
          cases h0 : a 0
          · rw [h0] at h; exact hf h
          · rw [h0] at h; exact hr h

/-! ### Evaluation -/

/-- **The two computations evaluate alike.** For a string function `D` (a machine with fixed coins),
the ch. 2–4 tree of the next-move function `h ↦ decodeOracleMove ℓ₁ (bridgePost (D (bridgePre
(encodeHist h))))` from the history of a log `L`, evaluated against `f`, is bit `0` of the
`bitCodec` computation of `L ↦ decodeBitMove (D ⟨[], encodeLog L⟩)` from `L`, evaluated against
`f` at the only oracle; for every budget.

**Proof sketch.** Induction on the budget, generalizing the log. The history translates to the
log (`bridgePre_encodeHist`), so both next moves come from the same word, and `bridgePost_spec`
gives corresponding moves. An output `a` gives the leaf `a 0` against the leaf `a`
(`buildTree_*_of_ret`, `buildComp_*_of_ret`). A query with the budget spent gives the verdict
`false` against `zeroBits 1`, whose bit `0` is `false`. A query `x` within budget asks `f x` on
both sides (`QueryTree.eval_query`, `OracleComp.evalFn_query`), and the continuations agree by
induction, since the history of `L ++ [⟨0, x, f x⟩]` is that of `L` followed by `(x, f x)`. -/
theorem eval_buildTree_bridge (ℓ₁ ℓ₂ : ℕ) (D : List Bool → List Bool)
    (f : (Fin ℓ₁ → Bool) → (Fin ℓ₂ → Bool)) :
    ∀ (q : ℕ) (L : QueryLog (bitSpec (fun _ : Fin 1 => ℓ₁) (fun _ => ℓ₂))),
      (buildTree (fun h => decodeOracleMove ℓ₁ (bridgePost (D (bridgePre (encodeHist h))))) q
          (logHist L)).eval f =
        (buildComp (fun L => decodeBitMove (fun _ : Fin 1 => ℓ₁) (fun _ => ℓ₂) 1
            (D (pairEncode [] ((bitCodec (fun _ : Fin 1 => ℓ₁) (fun _ => ℓ₂) 1).encodeLog L))))
          (zeroBits 1) q L).evalFn (fun _ => f) 0 := by
  intro q
  induction q with
  | zero =>
    intro L
    rcases bridgePost_spec ℓ₁ ℓ₂ (D (pairEncode []
        ((bitCodec (fun _ : Fin 1 => ℓ₁) (fun _ => ℓ₂) 1).encodeLog L))) with
      ⟨x, hb, ho⟩ | ⟨a, hb, ho⟩
    · rw [buildTree_zero_of_query (x := x) (by rw [bridgePre_encodeHist 1 L]; exact ho),
        buildComp_zero_of_query hb, QueryTree.eval_ret, OracleComp.evalFn_pure, zeroBits_apply]
    · rw [buildTree_zero_of_ret (b := a 0) (by rw [bridgePre_encodeHist 1 L]; exact ho),
        buildComp_zero_of_ret hb, QueryTree.eval_ret, OracleComp.evalFn_pure]
  | succ q ih =>
    intro L
    rcases bridgePost_spec ℓ₁ ℓ₂ (D (pairEncode []
        ((bitCodec (fun _ : Fin 1 => ℓ₁) (fun _ => ℓ₂) 1).encodeLog L))) with
      ⟨x, hb, ho⟩ | ⟨a, hb, ho⟩
    · rw [buildTree_succ_of_query (x := x) (by rw [bridgePre_encodeHist 1 L]; exact ho),
        buildComp_succ_of_query hb, QueryTree.eval_query, OracleComp.evalFn_query]
      have hh : logHist L ++ [(x, f x)] = logHist (L ++ [⟨0, x, f x⟩]) := by
        rw [logHist_eq, logHist_eq, List.map_append, List.map_singleton]
      rw [hh]
      exact ih (L ++ [⟨0, x, f x⟩])
    · rw [buildTree_succ_of_ret (b := a 0) (by rw [bridgePre_encodeHist 1 L]; exact ho),
        buildComp_succ_of_ret hb, QueryTree.eval_ret, OracleComp.evalFn_pure]

end TCSlib.Cryptography.Games.EffFill
