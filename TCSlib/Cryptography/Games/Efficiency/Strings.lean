/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TCSlib.Cryptography.Games.BitCodec
import TCSlib.Complexity.Randomized.Closure
import TCSlib.Cryptography.Asymptotic.EnsemblesLemmas
import TCSlib.Cryptography.Pseudorandom.Functions.Asymptotic.GGM.Reduction

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# The string layer of the efficiency fill

The machines of the efficiency targets (`TCSlib.Cryptography.Games.Efficiency`) replay a reduction
on strings. This file collects the string-level pieces they share (route note
`briefs/pass-shelat-ch5-8/design/S2b-efficiency.md`, §"Shared pieces", S1 and S2):
- appending one entry to an encoded log is a concatenation (`encodeLog_append_single`);
- fixed-length decoding with the all-`false` default, as a string function (`fixLen`);
- a `k`-way selection of a polynomial length by an index written in unary (`selLen`), and finite
  sums of polynomials (`sumPoly`);
- the **canonical decoder** `canonWord`: on every word it returns the canonical word of the move
  that `decodeBitMove` reads off it, and it is polynomial-time (`canonFun_poly`); canonicity is
  tested by re-encoding and comparing;
- an **activation loop** (`actLoop`): `GGMRed.stateLoopFun` with one activation per round, the
  activation returning `⟨[false], new state⟩` to continue or `⟨[true], output⟩` to stop, with its
  run invariant `RunsTo`;
- the machine glue (`exists_splitMachine`): a polynomial-time function of the raw layout becomes a
  machine whose first `p(n)` coins are a seed passed as data.

## Main definitions

* `EffFill.fixLen`, `EffFill.selLen`, `EffFill.sumPoly`, `EffFill.canonWord`, `EffFill.canonFun`.
* `EffFill.actLoop`, `EffFill.RunsTo`.

## Main results

* `EffFill.encodeLog_append_single`, `EffFill.ofFn_getD_decodeFin`.
* `EffFill.canonWord_eq`: the canonical decoder is `encodeBitMove ∘ decodeBitMove`.
* `EffFill.canonFun_poly`, `EffFill.fixLen_poly`, `EffFill.selLen_poly`, `EffFill.actLoop_poly`.
* `EffFill.runsTo_stop`: a run that stops evaluates the loop.
* `EffFill.exists_splitMachine`.

## References

* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed., January 2010,
  §2.1 (closure of p.p.t. machines under efficient operations) and §3.8.1 (oracle machines).
-/

namespace TCSlib.Cryptography.Games.EffFill

open Complexity Turing

variable {k : ℕ}

/-! ### Logs -/

/-- **Appending one entry to a log appends one pair:** `codec.encodeLog (h ++ [e]) =
codec.encodeLog h ++ pairEncode (codec.encodeEntry e) []` (the nested encoding is flat). -/
theorem encodeLog_append_single {ι α : Type} {spec : OracleSpec ι} (codec : MachineCodec spec α)
    (h : QueryLog spec) (e : Σ i, spec.dom i × spec.rng i) :
    codec.encodeLog (h ++ [e]) = codec.encodeLog h ++ pairEncode (codec.encodeEntry e) [] := by
  induction h with
  | nil =>
    rw [List.nil_append, MachineCodec.encodeLog_cons, MachineCodec.encodeLog_nil, List.nil_append]
  | cons e' h ih =>
    rw [List.cons_append, MachineCodec.encodeLog_cons, MachineCodec.encodeLog_cons, ih,
      GGMRed.pairEncode_append_right]

/-- An encoded log is at most `E` bits per entry when each entry, as a pair `⟨e, rest⟩`, adds at
most `E` bits: `|codec.encodeLog h| ≤ |h| · E`. -/
theorem length_encodeLog_le {ι α : Type} {spec : OracleSpec ι} (codec : MachineCodec spec α)
    (E : ℕ) : ∀ (h : QueryLog spec), (∀ e ∈ h, 2 * (codec.encodeEntry e).length + 2 ≤ E) →
      (codec.encodeLog h).length ≤ h.length * E
  | [], _ => by rw [MachineCodec.encodeLog_nil]; exact Nat.zero_le _
  | e :: h, hE => by
    rw [MachineCodec.encodeLog_cons, length_pairEncode, List.length_cons, Nat.add_mul, Nat.one_mul]
    have h1 := hE e List.mem_cons_self
    have h2 := length_encodeLog_le codec E h fun e' he' => hE e' (List.mem_cons_of_mem e he')
    omega

/-- The encoding of a log ends with the encoding of each of its suffixes, so it is at least as
long: `|codec.encodeLog O| ≤ |codec.encodeLog (P ++ O)|`. -/
theorem length_encodeLog_le_append {ι α : Type} {spec : OracleSpec ι} (codec : MachineCodec spec α)
    (O : QueryLog spec) : ∀ P : QueryLog spec,
      (codec.encodeLog O).length ≤ (codec.encodeLog (P ++ O)).length
  | [] => by rw [List.nil_append]
  | e :: P => by
    rw [List.cons_append, MachineCodec.encodeLog_cons, length_pairEncode]
    have := length_encodeLog_le_append codec O P
    omega

/-! ### Fixed-length decoding with a default -/

/-- The word `w` if it has `d` bits, and the all-`false` word of `d` bits otherwise. -/
def fixLen (d : ℕ) (w : List Bool) : List Bool :=
  if w.length = d then w else List.replicate d false

/-- `fixLen d w = if |w| = d then w else 0^d`. -/
theorem fixLen_eq (d : ℕ) (w : List Bool) :
    fixLen d w = if w.length = d then w else List.replicate d false :=
  rfl

/-- A word of the right length is kept: `fixLen d w = w` when `|w| = d`. -/
theorem fixLen_of_length_eq {d : ℕ} {w : List Bool} (h : w.length = d) : fixLen d w = w := by
  rw [fixLen_eq, if_pos h]

/-- A word of the wrong length becomes all-`false`: `fixLen d w = 0^d` when `|w| ≠ d`. -/
theorem fixLen_of_length_ne {d : ℕ} {w : List Bool} (h : w.length ≠ d) :
    fixLen d w = List.replicate d false := by
  rw [fixLen_eq, if_neg h]

/-- `fixLen d w` has `d` bits. -/
theorem length_fixLen (d : ℕ) (w : List Bool) : (fixLen d w).length = d := by
  by_cases h : w.length = d
  · rw [fixLen_of_length_eq h, h]
  · rw [fixLen_of_length_ne h, List.length_replicate]

/-- The empty word becomes all-`false`: `fixLen d [] = 0^d` (for `d = 0` both are empty). -/
theorem fixLen_nil (d : ℕ) : fixLen d [] = List.replicate d false := by
  by_cases h : ([] : List Bool).length = d
  · rw [fixLen_of_length_eq h, ← h, List.length_nil, List.replicate_zero]
  · rw [fixLen_of_length_ne h]

/-- Every word of `d` bits is the string of some `d`-bit vector. -/
theorem exists_ofFn_eq {d : ℕ} {w : List Bool} (h : w.length = d) :
    ∃ x : Fin d → Bool, List.ofFn x = w := by
  cases hd : decodeFin d w with
  | none =>
    rw [decodeFin_eq, dif_pos h] at hd
    exact absurd hd (Option.some_ne_none _)
  | some x => exact ⟨x, ((decodeFin_eq_some_iff d w x).1 hd).symm⟩

/-- **Fixed-length decoding with the all-`false` default is `fixLen`:**
`List.ofFn ((decodeFin d w).getD (zeroBits d)) = fixLen d w`. -/
theorem ofFn_getD_decodeFin (d : ℕ) (w : List Bool) :
    List.ofFn ((decodeFin d w).getD (zeroBits d)) = fixLen d w := by
  cases hd : decodeFin d w with
  | none =>
    have hne : w.length ≠ d := fun h => by
      rw [decodeFin_eq, dif_pos h] at hd
      exact absurd hd (Option.some_ne_none _)
    rw [Option.getD_none, ofFn_zeroBits, fixLen_of_length_ne hne]
  | some x =>
    rw [Option.getD_some, (decodeFin_eq_some_iff d w x).1 hd,
      fixLen_of_length_eq (List.length_ofFn)]

/-- The all-`false` word of a polynomial-time length is polynomial-time:
`z ↦ 0^{|f z|}`. -/
theorem zeros_poly {f : List Bool → List Bool} (hf : PolyTimeComputable f) :
    PolyTimeComputable fun z => List.replicate (f z).length false :=
  (EnsembleLemmas.polyTimeComputable_zeros .var hf).congr fun z => by rw [PolyExpr.eval_var]

/-- Equality of two polynomial-time words is a polynomial-time test
(`Complexity.polyTimeComputable_pairEq` on the pair). -/
theorem eq_poly {f g : List Bool → List Bool} (hf : PolyTimeComputable f)
    (hg : PolyTimeComputable g) : PolyTimeComputable fun z => [decide (f z = g z)] :=
  (polyTimeComputable_pairEq.comp' (hf.pairEncode hg)).congr fun z => by
    rw [pairFstD_pairEncode, pairSndD_pairEncode]

/-- Equality of the lengths of two polynomial-time words is a polynomial-time test
(`Complexity.polyTimeComputable_lenEq` on the pair). -/
theorem lenEq_poly {f g : List Bool → List Bool} (hf : PolyTimeComputable f)
    (hg : PolyTimeComputable g) : PolyTimeComputable fun z => [decide ((f z).length = (g z).length)]
        :=
  (polyTimeComputable_lenEq.comp' (hf.pairEncode hg)).congr fun z => by
    rw [pairFstD_pairEncode, pairSndD_pairEncode]

/-- `fixLen` with the length given in unary, `z = ⟨1^d, w⟩ ↦ fixLen d w`, is polynomial-time. -/
theorem fixLen_poly {f g : List Bool → List Bool} (hf : PolyTimeComputable f)
    (hg : PolyTimeComputable g) : PolyTimeComputable fun z => fixLen (f z).length (g z) :=
  (polyTimeComputable_ite (lenEq_poly hg hf) hg (zeros_poly hf)).congr fun z => by
    by_cases h : (g z).length = (f z).length
    · rw [fixLen_of_length_eq h, decide_eq_true h, if_pos rfl]
    · rw [fixLen_of_length_ne h, decide_eq_false h]
      rfl

/-! ### Polynomial lengths selected by an index -/

/-- The length `d i (n)` selected by the index `m = i` (and `0` for `m ≥ k`). -/
def selLen : {k : ℕ} → (Fin k → PolyExpr) → ℕ → ℕ → ℕ
  | 0, _, _, _ => 0
  | _ + 1, d, n, 0 => (d 0).eval n
  | _ + 1, d, n, m + 1 => selLen (fun i => d i.succ) n m

/-- The selected length of an index is its polynomial evaluated:
`selLen d n i = (d i).eval n`. -/
theorem selLen_eq : ∀ {k : ℕ} (d : Fin k → PolyExpr) (n : ℕ) (i : Fin k),
    selLen d n i = (d i).eval n
  | 0, _, _, i => i.elim0
  | _ + 1, d, n, i => by
    refine Fin.cases ?_ (fun j => ?_) i
    · rfl
    · rw [Fin.val_succ]
      exact selLen_eq (fun i => d i.succ) n j

/-- A selected index outside the oracle family has length zero.
Together with the finite-index reader this covers every natural index. -/
theorem selLen_of_ge : ∀ {k : ℕ} (d : Fin k → PolyExpr) (n m : ℕ),
    k ≤ m → selLen d n m = 0
  | 0, _, _, _, _ => rfl
  | _ + 1, _, _, 0, h => by omega
  | _ + 1, d, n, m + 1, h =>
      selLen_of_ge (fun i => d i.succ) n m (Nat.le_of_succ_le_succ h)

/-- The selected length in unary, `⟨u, iw⟩ ↦ 1^{selLen d |u| |iw|}`, is polynomial-time (a `k`-way
case split, by induction on `k`). -/
theorem selLen_poly : ∀ {k : ℕ} (d : Fin k → PolyExpr),
    PolyTimeComputable fun z =>
      List.replicate (selLen d (pairFstD z).length (pairSndD z).length) true
  | 0, _ => (polyTimeComputable_const []).congr fun _ => rfl
  | _ + 1, d => by
    have hrest := (selLen_poly (fun i => d i.succ)).comp'
      (polyTimeComputable_pairFstD.pairEncode (polyTimeComputable_tail.comp
          polyTimeComputable_pairSndD))
    have h := polyTimeComputable_ite (polyTimeComputable_isNil.comp polyTimeComputable_pairSndD)
      (StateLoop.unaryPoly_comp (d 0) polyTimeComputable_pairFstD) hrest
    refine h.congr fun z => ?_
    simp only [Function.comp_apply, pairFstD_pairEncode, pairSndD_pairEncode]
    cases hz : pairSndD z with
    | nil => rfl
    | cons b w =>
      simp only [List.length_cons, List.drop_one, List.tail_cons]
      rfl

/-- A finite sum of polynomials: `sumPoly d = d 0 + d 1 + ⋯ + d (k - 1)`. -/
def sumPoly : {k : ℕ} → (Fin k → PolyExpr) → PolyExpr
  | 0, _ => .const 0
  | _ + 1, d => .add (d 0) (sumPoly fun i => d i.succ)

/-- `sumPoly` of no polynomials is `0`, and of `k + 1` it is the first plus the rest:
`sumPoly d = .add (d 0) (sumPoly (d ∘ Fin.succ))`. -/
theorem sumPoly_succ {k : ℕ} (d : Fin (k + 1) → PolyExpr) :
    sumPoly d = .add (d 0) (sumPoly fun i => d i.succ) :=
  rfl

/-- Summing an empty family of length polynomials gives the constant zero. -/
theorem sumPoly_zero (d : Fin 0 → PolyExpr) : sumPoly d = .const 0 :=
  rfl

/-- Each summand is below the sum: `(d i).eval n ≤ (sumPoly d).eval n`. -/
theorem eval_le_sumPoly : ∀ {k : ℕ} (d : Fin k → PolyExpr) (i : Fin k) (n : ℕ),
    (d i).eval n ≤ (sumPoly d).eval n
  | 0, _, i, _ => i.elim0
  | _ + 1, d, i, n => by
    rw [sumPoly_succ, PolyExpr.eval_add]
    refine Fin.cases ?_ (fun j => ?_) i
    · exact Nat.le_add_right _ _
    · exact (eval_le_sumPoly (fun i => d i.succ) j n).trans (Nat.le_add_left _ _)

/-- Every selected length is below the sum: `selLen d n m ≤ (sumPoly d).eval n`. -/
theorem selLen_le_sumPoly : ∀ {k : ℕ} (d : Fin k → PolyExpr) (n m : ℕ),
    selLen d n m ≤ (sumPoly d).eval n
  | 0, _, _, _ => Nat.zero_le _
  | _ + 1, d, n, 0 => by
    rw [sumPoly_succ, PolyExpr.eval_add]
    exact Nat.le_add_right _ _
  | _ + 1, d, n, m + 1 => by
    rw [sumPoly_succ, PolyExpr.eval_add]
    exact (selLen_le_sumPoly (fun i => d i.succ) n m).trans (Nat.le_add_left _ _)

/-- The bits that one entry `⟨1^i, ⟨x, y⟩⟩` adds to an encoded log, at most
`4k + 10 + 4 Σ din + 2 Σ dout`. -/
def entryPoly (din dout : Fin k → PolyExpr) : PolyExpr :=
  .add (.const (4 * k + 10)) (.add (.mul (.const 4) (sumPoly din)) (.mul (.const 2) (sumPoly dout)))

/-- The defining equation of `entryPoly`. -/
theorem entryPoly_eq (din dout : Fin k → PolyExpr) : entryPoly din dout =
    .add (.const (4 * k + 10)) (.add (.mul (.const 4) (sumPoly din)) (.mul (.const 2) (sumPoly
        dout))) :=
  rfl

/-- **The entry bound:** a log entry of the bit-string oracles adds at most `entryPoly` bits to an
encoded log, `2 |encodeEntry e| + 2 ≤ entryPoly(n)`. -/
theorem entry_le_entryPoly (din dout : Fin k → PolyExpr) (n : ℕ)
    (e : Σ i, (bitSpec (fun i => (din i).eval n) (fun i => (dout i).eval n)).dom i ×
      (bitSpec (fun i => (din i).eval n) (fun i => (dout i).eval n)).rng i) (dα : ℕ) :
    2 * ((bitCodec (fun i => (din i).eval n) (fun i => (dout i).eval n) dα).encodeEntry e).length
      + 2 ≤ (entryPoly din dout).eval n := by
  rw [bitCodec_encodeEntry, length_pairEncode, length_pairEncode, List.length_replicate,
    List.length_ofFn, List.length_ofFn, entryPoly_eq]
  simp only [PolyExpr.eval_add, PolyExpr.eval_mul, PolyExpr.eval_const]
  have h1 := e.1.isLt
  have h2 := eval_le_sumPoly din e.1 n
  have h3 := eval_le_sumPoly dout e.1 n
  omega

/-- The parameter is at most the length of the raw layout `⟨⟨⟨1^n, y⟩, α⟩, r⟩`. -/
theorem le_length_layout (n : ℕ) (y α r : List Bool) :
    n ≤ (NUPPT.layout (List.replicate n true) y α r).length := by
  rw [NUPPT.layout_eq, length_pairEncode, length_pairEncode, length_pairEncode,
    List.length_replicate]
  omega

/-! ### The canonical decoder -/

/-- The query test of the canonical decoder: `w = ⟨[false], ⟨iw, xw⟩⟩` with `iw = 1^i`, `i < k`
and `|xw| = din i (n)`, tested by re-encoding and comparing. -/
def canonQ (din : Fin k → PolyExpr) (n : ℕ) (w : List Bool) : Bool :=
  decide (w = pairEncode [false] (pairEncode (pairFstD (pairSndD w)) (pairSndD (pairSndD w)))) &&
    decide (pairFstD (pairSndD w) = List.replicate (pairFstD (pairSndD w)).length true) &&
    decide ((pairFstD (pairSndD w)).length < k) &&
    decide ((pairSndD (pairSndD w)).length = selLen din n (pairFstD (pairSndD w)).length)

/-- `canonQ din n w` is the conjunction of the four tests (its defining equation). -/
theorem canonQ_eq (din : Fin k → PolyExpr) (n : ℕ) (w : List Bool) :
    canonQ din n w =
      (decide (w = pairEncode [false] (pairEncode (pairFstD (pairSndD w)) (pairSndD (pairSndD w))))
        && decide (pairFstD (pairSndD w) = List.replicate (pairFstD (pairSndD w)).length true)
        && decide ((pairFstD (pairSndD w)).length < k)
        && decide ((pairSndD (pairSndD w)).length = selLen din n (pairFstD (pairSndD w)).length)) :=
  rfl

/-- The output test of the canonical decoder: `w = ⟨[true], a⟩` with `|a| = dα`. -/
def canonR (dα : ℕ) (w : List Bool) : Bool :=
  decide (w = pairEncode [true] (pairSndD w)) && decide ((pairSndD w).length = dα)

/-- `canonR dα w` is the conjunction of the two tests (its defining equation). -/
theorem canonR_eq (dα : ℕ) (w : List Bool) :
    canonR dα w = (decide (w = pairEncode [true] (pairSndD w)) && decide ((pairSndD w).length = dα))
        :=
  rfl

/-- **The canonical decoder** at parameter `n` with `dα`-bit outputs: a canonical query or output
word is kept, every other word becomes the canonical word `⟨[true], 0^dα⟩` of the default. -/
def canonWord (din : Fin k → PolyExpr) (n dα : ℕ) (w : List Bool) : List Bool :=
  if canonQ din n w || canonR dα w then w else pairEncode [true] (List.replicate dα false)

/-- `canonWord din n dα w = if canonQ din n w || canonR dα w then w else ⟨[true], 0^dα⟩`. -/
theorem canonWord_eq_ite (din : Fin k → PolyExpr) (n dα : ℕ) (w : List Bool) :
    canonWord din n dα w =
      if canonQ din n w || canonR dα w then w else pairEncode [true] (List.replicate dα false) :=
  rfl

/-- **The canonical decoder is the canonical word of the decoded move:** for every word `w` (and
any answer lengths `dout`), `canonWord din n dα w = encodeBitMove (decodeBitMove w)` at the
evaluated lengths.

**Proof sketch.** Three cases. A canonical query word `⟨[false], ⟨1^i, x⟩⟩` passes the query test
(the index is below `k` and `|x| = din i (n)` by `selLen_eq`) and decodes to its query, whose
canonical word it is (`decodeBitMove_query`). A canonical output word passes the output test and
decodes to its output (`decodeBitMove_ret`). Any other word fails both tests: a word passing the
query test is, after re-encoding, the canonical word of the query at index `|iw|` with payload
`xw` (`exists_ofFn_eq`), and one passing the output test is a canonical output word. So it becomes
`⟨[true], 0^dα⟩`, the canonical word of the default (`decodeBitMove_of_not_canonical`,
`ofFn_zeroBits`). -/
theorem canonWord_eq (din : Fin k → PolyExpr) (dout : Fin k → ℕ) (n dα : ℕ) (w : List Bool) :
    canonWord din n dα w =
      encodeBitMove (fun i => (din i).eval n) dout dα
        (decodeBitMove (fun i => (din i).eval n) dout dα w) := by
  by_cases hq : ∃ (i : Fin k) (x : Fin ((din i).eval n) → Bool),
      w = pairEncode [false] (pairEncode (List.replicate i true) (List.ofFn x))
  · obtain ⟨i, x, rfl⟩ := hq
    rw [decodeBitMove_query, encodeBitMove_query, canonWord_eq_ite, if_pos]
    rw [canonQ_eq]
    simp only [pairSndD_pairEncode, pairFstD_pairEncode, List.length_replicate, List.length_ofFn,
      selLen_eq, i.isLt, decide_true, Bool.and_true, Bool.true_or]
  by_cases hr : ∃ a : Fin dα → Bool, w = pairEncode [true] (List.ofFn a)
  · obtain ⟨a, rfl⟩ := hr
    rw [decodeBitMove_ret, encodeBitMove_ret, canonWord_eq_ite, if_pos]
    rw [canonR_eq]
    simp only [pairSndD_pairEncode, List.length_ofFn, decide_true, Bool.and_true, Bool.or_true]
  have hq' : ∀ (i : Fin k) (x : Fin ((din i).eval n) → Bool),
      w ≠ pairEncode [false] (pairEncode (List.replicate i true) (List.ofFn x)) :=
    fun i x h => hq ⟨i, x, h⟩
  have hr' : ∀ a : Fin dα → Bool, w ≠ pairEncode [true] (List.ofFn a) := fun a h => hr ⟨a, h⟩
  rw [decodeBitMove_of_not_canonical hq' hr', encodeBitMove_ret, ofFn_zeroBits, canonWord_eq_ite,
    if_neg]
  rw [Bool.or_eq_true, not_or]
  constructor
  · intro h
    rw [canonQ_eq] at h
    simp only [Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨⟨⟨hw, hiw⟩, hlt⟩, hx⟩ := h
    let i : Fin k := ⟨(pairFstD (pairSndD w)).length, hlt⟩
    have hx' : (pairSndD (pairSndD w)).length = (din i).eval n := by
      rw [hx, ← selLen_eq]
    obtain ⟨x, hxe⟩ := exists_ofFn_eq hx'
    refine hq' i x ?_
    rw [hxe]
    exact hw.trans (by rw [← hiw])
  · intro h
    rw [canonR_eq] at h
    simp only [Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨hw, hlen⟩ := h
    obtain ⟨a, ha⟩ := exists_ofFn_eq hlen
    exact hr' a (by rw [ha]; exact hw)

/-- The canonical decoder as a function of `⟨1^n, ⟨1^dα, w⟩⟩`. -/
def canonFun (din : Fin k → PolyExpr) (z : List Bool) : List Bool :=
  canonWord din (pairFstD z).length (pairFstD (pairSndD z)).length (pairSndD (pairSndD z))

/-- On every raw word the canonical decoder reads its three inputs through
the total pair projections. -/
theorem canonFun_def (din : Fin k → PolyExpr) (z : List Bool) :
    canonFun din z =
      canonWord din (pairFstD z).length (pairFstD (pairSndD z)).length
        (pairSndD (pairSndD z)) :=
  rfl

/-- The canonical decoder reads `n` and `dα` in unary:
`canonFun din ⟨1^n, ⟨1^dα, w⟩⟩ = canonWord din n dα w`. -/
theorem canonFun_eq (din : Fin k → PolyExpr) (n dα : ℕ) (w : List Bool) :
    canonFun din (pairEncode (List.replicate n true) (pairEncode (List.replicate dα true) w)) =
      canonWord din n dα w := by
  rw [canonFun, pairFstD_pairEncode, pairSndD_pairEncode, pairFstD_pairEncode, pairSndD_pairEncode,
    List.length_replicate, List.length_replicate]

/-- **The canonical decoder is polynomial-time:** each test is a comparison of polynomial-time
words (`eq_poly`, `lenEq_poly`, `Complexity.StateLoop.lenLe_comp`, `selLen_poly`), and the
output a branch (`Complexity.polyTimeComputable_ite`). -/
theorem canonFun_poly (din : Fin k → PolyExpr) : PolyTimeComputable (canonFun din) := by
  have hu := polyTimeComputable_pairFstD
  have hrl := polyTimeComputable_pairFstD.comp' polyTimeComputable_pairSndD
  have hw := polyTimeComputable_pairSndD.comp' polyTimeComputable_pairSndD
  have hrest := polyTimeComputable_pairSndD.comp' hw
  have hiw := polyTimeComputable_pairFstD.comp' hrest
  have hxw := polyTimeComputable_pairSndD.comp' hrest
  have h1 := eq_poly hw ((polyTimeComputable_const [false]).pairEncode (hiw.pairEncode hxw))
  have h2 := eq_poly hiw (polyTimeComputable_unary.comp' hiw)
  have h3 : PolyTimeComputable fun z =>
      [decide ((true :: pairFstD (pairSndD (pairSndD (pairSndD z)))).length ≤
        (List.replicate k true).length)] :=
    StateLoop.lenLe_comp (polyTimeComputable_const _) ((StateLoop.cons_poly true).comp' hiw)
  have h4 := lenEq_poly hxw ((selLen_poly din).comp' (hu.pairEncode hiw))
  have hQ := polyTimeComputable_and (polyTimeComputable_and (polyTimeComputable_and h1 h2) h3) h4
  have h5 := eq_poly hw ((polyTimeComputable_const [true]).pairEncode hrest)
  have h6 := lenEq_poly hrest hrl
  have hR := polyTimeComputable_and h5 h6
  have h := polyTimeComputable_ite (polyTimeComputable_or hQ hR) hw
    ((polyTimeComputable_const [true]).pairEncode (zeros_poly hrl))
  refine h.congr fun z => ?_
  rw [canonFun, canonWord_eq_ite, canonQ_eq, canonR_eq]
  simp only [pairFstD_pairEncode, pairSndD_pairEncode, List.length_replicate, List.length_cons,
    Nat.succ_le_iff]

/-! ### Activation loops -/

/-- The step of an activation loop: the second component of the activation's result. -/
def actStep (act : List Bool → List Bool) (w : List Bool) : List Bool :=
  pairSndD (act w)

/-- `actStep act w = pairSndD (act w)`. -/
theorem actStep_eq (act : List Bool → List Bool) (w : List Bool) :
    actStep act w = pairSndD (act w) :=
  rfl

/-- The stopping test of an activation loop: the activation's result is tagged `[true]`. -/
def actAcc (act : List Bool → List Bool) (w : List Bool) : Bool :=
  decide (pairFstD (act w) = [true])

/-- `actAcc act w = decide (pairFstD (act w) = [true])`. -/
theorem actAcc_eq (act : List Bool → List Bool) (w : List Bool) :
    actAcc act w = decide (pairFstD (act w) = [true]) :=
  rfl

/-- **The activation loop:** `GGMRed.stateLoopFun` whose round is one activation `act` on the
state word `⟨x, s⟩`, returning `⟨[false], s'⟩` to continue with the state `s'` or `⟨[true], o⟩` to
stop with the output `o`; at most `R|x|` rounds, states bounded by `B|x|`. -/
def actLoop (start act : List Bool → List Bool) (R B : PolyExpr) : List Bool → List Bool :=
  GGMRed.stateLoopFun start (actStep act) (actAcc act) (actStep act) R B

/-- `actLoop start act R B = GGMRed.stateLoopFun start (actStep act) (actAcc act) (actStep act) R
B`.
-/
theorem actLoop_eq (start act : List Bool → List Bool) (R B : PolyExpr) :
    actLoop start act R B =
      GGMRed.stateLoopFun start (actStep act) (actAcc act) (actStep act) R B :=
  rfl

/-- An activation loop with polynomial-time start and activation is polynomial-time
(`GGMRed.stateLoopFun_poly`). -/
theorem actLoop_poly {start act : List Bool → List Bool} (hstart : PolyTimeComputable start)
    (hact : PolyTimeComputable act) (R B : PolyExpr) : PolyTimeComputable (actLoop start act R B) :=
  GGMRed.stateLoopFun_poly hstart (polyTimeComputable_pairSndD.comp' hact)
    (eq_poly (polyTimeComputable_pairFstD.comp' hact) (polyTimeComputable_const [true]))
    (polyTimeComputable_pairSndD.comp' hact) R B

/-- **The run invariant of an activation loop:** on input `x`, the state after `t` rounds is `S`,
no earlier round stopped, and the states so far are bounded by `B|x|`. -/
def RunsTo (start act : List Bool → List Bool) (B : PolyExpr) (x : List Bool) (t : ℕ)
    (S : List Bool) : Prop :=
  (∀ i < t, actAcc act (pairEncode x (StateLoop.orbit start (actStep act) x i)) = false) ∧
    (∀ i ≤ t, (StateLoop.orbit start (actStep act) x i).length ≤ B.eval x.length) ∧
    StateLoop.orbit start (actStep act) x t = S

/-- `RunsTo` is the conjunction of its three clauses (its defining equation). -/
theorem runsTo_iff (start act : List Bool → List Bool) (B : PolyExpr) (x : List Bool) (t : ℕ)
    (S : List Bool) :
    RunsTo start act B x t S ↔
      (∀ i < t, actAcc act (pairEncode x (StateLoop.orbit start (actStep act) x i)) = false) ∧
        (∀ i ≤ t, (StateLoop.orbit start (actStep act) x i).length ≤ B.eval x.length) ∧
        StateLoop.orbit start (actStep act) x t = S :=
  Iff.rfl

/-- The run starts at `start x`, if that state is within the bound. -/
theorem runsTo_zero {start act : List Bool → List Bool} {B : PolyExpr} {x : List Bool}
    (h : (start x).length ≤ B.eval x.length) : RunsTo start act B x 0 (start x) := by
  refine ⟨fun i hi => absurd hi (Nat.not_lt_zero _), fun i hi => ?_, StateLoop.orbit_zero _ _ _⟩
  rw [Nat.le_zero.1 hi, StateLoop.orbit_zero]
  exact h

/-- **A continuing round:** if the activation on `⟨x, S⟩` continues with `S'` within the bound,
the run reaches `S'` one round later. -/
theorem runsTo_succ {start act : List Bool → List Bool} {B : PolyExpr} {x : List Bool} {t : ℕ}
    {S S' : List Bool} (h : RunsTo start act B x t S) (hact : act (pairEncode x S) = pairEncode
        [false] S')
    (hS' : S'.length ≤ B.eval x.length) : RunsTo start act B x (t + 1) S' := by
  obtain ⟨hf, hb, hS⟩ := h
  have horb : StateLoop.orbit start (actStep act) x (t + 1) = S' := by
    rw [StateLoop.orbit_succ, hS, actStep_eq, hact, pairSndD_pairEncode]
  refine ⟨fun i hi => ?_, fun i hi => ?_, horb⟩
  · rcases Nat.lt_succ_iff_lt_or_eq.1 hi with hi | rfl
    · exact hf i hi
    · rw [hS, actAcc_eq, hact, pairFstD_pairEncode]
      rfl
  · rcases Nat.lt_or_eq_of_le hi with hi | rfl
    · exact hb i (Nat.lt_succ_iff.1 hi)
    · rw [horb]
      exact hS'

/-- **A stopping round:** if the activation on `⟨x, S⟩` stops with the output `o` at a round
`t ≤ R|x|`, the loop returns `o` (`GGMRed.stateLoopFun_eval`). -/
theorem runsTo_stop {start act : List Bool → List Bool} {R B : PolyExpr} {x : List Bool} {t : ℕ}
    {S o : List Bool} (h : RunsTo start act B x t S) (hact : act (pairEncode x S) = pairEncode
        [true] o)
    (ht : t ≤ R.eval x.length) : actLoop start act R B x = o := by
  obtain ⟨hf, hb, hS⟩ := h
  rw [actLoop_eq, GGMRed.stateLoopFun_eval _ _ _ _ R B x t ht hb hf, hS, actStep_eq, hact,
    pairSndD_pairEncode]
  rw [hS, actAcc_eq, hact, pairFstD_pairEncode]
  rfl

/-! ### Machine glue -/

/-- **A raw function with a seed as data is a machine.** For a polynomial-time `F`, an advice
family of polynomial length and a seed length `p`, there is a machine `B` and, at every
parameter, a bijection `φ` from (seed, `A`'s coins) to `B`'s coins such that `B` on the argument
`y` with coins `φ (ω, r)` returns `F` of the raw layout `⟨⟨⟨1^n, ⟨y, ω⟩⟩, advice n⟩, r⟩`.

**Proof sketch.** `B` is `NUPPT.exists_split` with `p` of `NUPPT.ofPolyTime hF A.coins adv advice`,
so its coin polynomial is `p + A.coins` (`coins_ofPolyTime`, `coinLen_eq`, `PolyExpr.eval_add`).
`φ` appends the seed and the coins (`Fin.appendEquiv`) and transports along that length
equation; its string is `ω ++ r` (`List.ofFn_fin_append`, `List.ofFn_congr`), which the split
cuts back into `ω` and `r` (`runAtL_ofPolyTime`). -/
theorem exists_splitMachine (A : NUPPT) {F : List Bool → List Bool} (hF : PolyTimeComputable F)
    (adv : PolyExpr) (advice : ℕ → List Bool) (hα : ∀ n, (advice n).length ≤ adv.eval n)
    (p : PolyExpr) :
    ∃ B : NUPPT, ∀ n : ℕ, ∃ φ : (Fin (p.eval n) → Bool) × A.Coins n ≃ B.Coins n,
      ∀ (y : List Bool) (ω : Fin (p.eval n) → Bool) (r : A.Coins n),
        B.runAt n y (φ (ω, r)) =
          F (NUPPT.layout (List.replicate n true) (pairEncode y (List.ofFn ω)) (advice n)
            (List.ofFn r)) := by
  obtain ⟨B, hBc, -, hB⟩ := NUPPT.exists_split (NUPPT.ofPolyTime hF A.coins adv advice hα) p
  refine ⟨B, fun n => ?_⟩
  have hlen : p.eval n + A.coinLen n = B.coinLen n := by
    rw [NUPPT.coinLen_eq, NUPPT.coinLen_eq, hBc, PolyExpr.eval_add, NUPPT.coins_ofPolyTime]
  refine ⟨(Fin.appendEquiv (p.eval n) (A.coinLen n)).trans
    (Equiv.arrowCongr (finCongr hlen) (Equiv.refl Bool)), fun y ω r => ?_⟩
  have hofFn : List.ofFn (((Fin.appendEquiv (p.eval n) (A.coinLen n)).trans
      (Equiv.arrowCongr (finCongr hlen) (Equiv.refl Bool))) (ω, r)) =
      List.ofFn ω ++ List.ofFn r := by
    rw [← List.ofFn_fin_append, List.ofFn_congr hlen (Fin.append ω r)]
    rfl
  rw [NUPPT.runAt_eq, hofFn, hB, List.take_left' (List.length_ofFn), List.drop_left'
    (List.length_ofFn), NUPPT.runAtL_ofPolyTime, NUPPT.layout_eq, NUPPT.advInput_eq]

end TCSlib.Cryptography.Games.EffFill
