/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hydroxyi
-/
import Mathlib.Data.Fintype.Pi
import TCSlib.Complexity.TimeHierarchy.ClockMachine

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Meyer's theorem: the tableau machine

The proof of Meyer's theorem [AB09, Thm 6.20] applies the hypothesis `EXP ⊆ P/poly` to a
*tableau language* of an exponential-time decider `M`: the language of queries
"what does the computation of `M` on `x` look like at time `t`, near head `h`?". This
file defines the machine `Complexity.Meyer.tabTM M` answering such queries; its run
analysis and the resulting `EXP` membership are in `MeyerMachineRun.lean`.

## The query format

A query is the string

  `bits ++ fcode t ++ [e, false] ++ fcode a ++ [e', false] ++ x`

where `bits` (a fixed number `nbits M` of raw bits) is the one-hot code of a *selector*
(`Complexity.Meyer.TabSel`), `t` and `a` are little-endian binary numbers written in the
pair code `fcode w = (w₀, true) (w₁, true) …`, `e, e'` are arbitrary, and the suffix
`x` is the input of `M`, verbatim. (This pair code is the image of `Turing.pairEncode`'s
doubled-bit code under a one-pass transducer, which keeps queries polynomial-time
constructible.)

## The machine

`tabTM M` has `M`'s work tapes plus three auxiliary tapes: the *copy tape* `X`, the
*counter* `C` and the *offset tape* `O`. It

1. reads the selector bits into its finite control, `t` onto `C`, `a` onto `O`, and
   copies `x` onto `X` (rejecting truncated inputs);
2. rewinds `X`, `C`, `O`;
3. runs a binary down-counter loop on `C`, each decrement fused with one step of `M`,
   whose input head is simulated on `X` with the clamping discipline of
   `Turing.FinTM.virtualMove` (the buffered-composition convention of
   `TCSlib.Complexity.TuringMachine.Simulation`); `M`'s output is summarized in an
   `Complexity.TimeHierarchy.OutReg`; the loop ends when `C` underflows or `M` halts;
4. runs a second down-counter loop on `O`, each decrement fused with one move of the
   selected head;
5. emits the selected bit of the reached configuration and halts.

So on a well-formed query it reports a bit of the configuration of `M` at time `val t`,
at offset `±val a` from a head — the *head-relative* tableau used by the verifier
(see `Meyer.lean` for why the book's oblivious snapshots are not used).

## Main definitions

* `Complexity.Meyer.TabSel` — the selectors; `Complexity.Meyer.encodeSel`,
  `Complexity.Meyer.decodeSel` — their one-hot code.
* `Complexity.Meyer.TState`, `Complexity.Meyer.tabTr`, `Complexity.Meyer.tabTM` — the
  machine.
* `Complexity.Meyer.tcfg` — its configurations in block form.

## Main results

* `Complexity.Meyer.tact_apply` — applying a block action to a block configuration.
* `Complexity.Meyer.tabTM_step` — the step of `tabTM` in block form.

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009. (§6.4, Theorem 6.20, pp. 114–115.)
-/

namespace Complexity.Meyer

open Turing Turing.FinTM Complexity.TimeHierarchy

/-! ### Selectors -/

/-- **A selector** of the tableau machine: either "is the (state, output summary) of the
configuration equal to `(σ, r)`?" (`st σ r`), or a question about the symbol at offset
`±a` from a head (`sym h neg blank`): `h = none` is the input head, `h = some i` work
head `i`; `neg` selects the direction of the offset; `blank` asks "is the symbol
blank?", otherwise "is the symbol `true`?". -/
inductive TabSel (S : Type) (k : ℕ) where
  | st : Option S → OutReg → TabSel S k
  | sym : Option (Fin k) → Bool → Bool → TabSel S k
  deriving DecidableEq, Fintype

/-- The answer bit of `sym _ _ blank` for a read symbol `v`. -/
def symBit (blank : Bool) (v : Option Bool) : Bool :=
  if blank then decide (v = none) else decide (v = some true)

/-- The answer of a selector, given the simulated state `oq`, output summary `r`, the
input read `v` and the work reads `mr` (the heads already walked to the offset). -/
def selAnswer {S : Type} [DecidableEq S] {k : ℕ} :
    TabSel S k → Option S → OutReg → Option Bool → (Fin k → Option Bool) → Bool
  | .st σ r₀, oq, r, _, _ => decide (oq = σ ∧ r = r₀)
  | .sym none _ blank, _, _, v, _ => symBit blank v
  | .sym (some h) _ blank, _, _, _, mr => symBit blank (mr h)

/-- The direction of a walk: `neg = true` walks left. -/
def walkDir (neg : Bool) : SignType := if neg then .neg else .pos

section sel

variable (S : Type) [Fintype S] [DecidableEq S] (k : ℕ)

/-- The number of selector bits: one per selector (one-hot code). -/
abbrev nbitsOf : ℕ := Fintype.card (TabSel S k)

omit [DecidableEq S] in
/-- There is at least one selector bit. -/
theorem nbitsOf_pos : 0 < nbitsOf S k :=
  Fintype.card_pos_iff.mpr ⟨.sym none false false⟩

variable {S k}

/-- **The one-hot code of a selector**: bit `i` is set iff `i` is the selector's index. -/
noncomputable def encodeSel (σ : TabSel S k) : Fin (nbitsOf S k) → Bool :=
  fun i => decide (i = Fintype.equivFin (TabSel S k) σ)

/-- The one-hot code is injective. -/
theorem encodeSel_injective : Function.Injective (encodeSel (S := S) (k := k)) := by
  intro σ τ h
  have := congrFun h (Fintype.equivFin (TabSel S k) σ)
  simp only [encodeSel, decide_true] at this
  exact (Fintype.equivFin (TabSel S k)).injective (by simpa using this.symm)

open Classical in
/-- **Decoding selector bits**: the selector whose code they are (an arbitrary default
on non-codes). -/
noncomputable def decodeSel (bits : Fin (nbitsOf S k) → Bool) : TabSel S k :=
  if h : ∃ σ, encodeSel σ = bits then h.choose else .sym none false false

/-- Decoding inverts encoding.

**Proof sketch.** The defining choice picks some selector with the same code, which is the
given one by injectivity of the one-hot code. -/
@[simp] theorem decodeSel_encodeSel (σ : TabSel S k) : decodeSel (encodeSel σ) = σ := by
  have h : ∃ τ, encodeSel τ = encodeSel σ := ⟨σ, rfl⟩
  simp only [decodeSel, dif_pos h]
  exact encodeSel_injective h.choose_spec

end sel

/-! ### The machine -/

set_option synthInstance.maxSize 1024 in
set_option synthInstance.maxHeartbeats 400000 in
/-- **Control states of the tableau machine** (see the module docstring): reading selector
bit `i` (`sel`), reading the pair code of field `f` (`fA` before a pair, `fB f b` after
its first symbol `b`; field `false` is `t`, field `true` is `a`), copying `x` (`cpy`),
rewinding the copy tape, counter and offset tape, the counter loop with the simulated
state `q`, output summary `r` and virtual-input arrival tag `b` (`dec`, `ret`), and the
walk loop (`wdec`, `wret`). -/
inductive TState (S : Type) (nb : ℕ) where
  | sel : Fin nb → (Fin nb → Bool) → TState S nb
  | fA : Bool → (Fin nb → Bool) → TState S nb
  | fB : Bool → Bool → (Fin nb → Bool) → TState S nb
  | cpy : (Fin nb → Bool) → TState S nb
  | rewX : (Fin nb → Bool) → TState S nb
  | rewC : (Fin nb → Bool) → TState S nb
  | rewO : (Fin nb → Bool) → TState S nb
  | dec : (Fin nb → Bool) → S → OutReg → Bool → TState S nb
  | ret : (Fin nb → Bool) → S → OutReg → Bool → TState S nb
  | wdec : (Fin nb → Bool) → Option S → OutReg → Bool → TState S nb
  | wret : (Fin nb → Bool) → Option S → OutReg → Bool → TState S nb
  deriving DecidableEq, Fintype

variable (M : FinTM Bool)

/-- The number of selector bits of `M`'s tableau machine. -/
abbrev nbits : ℕ := nbitsOf M.State M.k

/-- The selectors of `M`'s tableau machine. -/
abbrev Sel := TabSel M.State M.k

/-- The control states of `M`'s tableau machine. -/
abbrev St := TState M.State (nbits M)

/-- A block action: input move `im`, actions `mw` on `M`'s tapes and `aw` on the three
auxiliary tapes (`0 = X`, `1 = C`, `2 = O`), emission `o`, successor `q`. -/
def tact (im : SignType) (mw : Fin M.k → Option (Option Bool) × SignType)
    (aw : Fin 3 → Option (Option Bool) × SignType) (o : Option Bool) (q : Option (St M)) :
    Action (M.k + 3) Bool (St M) :=
  ⟨im, Fin.addCases mw aw, o, q⟩

/-- No action on any tape of a block. -/
def idle {n : ℕ} : Fin n → Option (Option Bool) × SignType := fun _ => (none, 0)

/-- Act on one tape of a block only. -/
def one {n : ℕ} (j : Fin n) (a : Option (Option Bool) × SignType) :
    Fin n → Option (Option Bool) × SignType :=
  Function.update idle j a

/-- Act on two distinct tapes of a block only. -/
def two {n : ℕ} (j : Fin n) (a : Option (Option Bool) × SignType) (j' : Fin n)
    (a' : Option (Option Bool) × SignType) : Fin n → Option (Option Bool) × SignType :=
  Function.update (one j a) j' a'

/-- Rejection of a truncated query: emit `false` and halt. -/
def reject : Action (M.k + 3) Bool (St M) := tact M 0 idle idle (some false) none

/-- **The transition table of the tableau machine** (see the module docstring). -/
noncomputable def tabTr (q : St M) (inp : Option Bool) (work : Fin (M.k + 3) → Option Bool) :
    Action (M.k + 3) Bool (St M) :=
  let mr : Fin M.k → Option Bool := fun i => work (Fin.castAdd 3 i)
  let ar : Fin 3 → Option Bool := fun j => work (Fin.natAdd M.k j)
  match q with
  | .sel i bits =>
    match inp with
    | none => reject M
    | some b =>
      tact M .pos idle idle none (some
        (if h : i.val + 1 < nbits M then .sel ⟨i.val + 1, h⟩ (Function.update bits i b)
         else .fA false (Function.update bits i b)))
  | .fA f bits =>
    match inp with
    | none => reject M
    | some b => tact M .pos idle idle none (some (.fB f b bits))
  | .fB f b bits =>
    match inp with
    | none => reject M
    | some true => tact M .pos idle (one (if f then 2 else 1) (some (some b), .pos)) none
        (some (.fA f bits))
    | some false => tact M .pos idle idle none (some (if f then .cpy bits else .fA true bits))
  | .cpy bits =>
    match inp with
    | some b => tact M .pos idle (one 0 (some (some b), .pos)) none (some (.cpy bits))
    | none => tact M 0 idle (one 0 (none, .neg)) none (some (.rewX bits))
  | .rewX bits =>
    match ar 0 with
    | some _ => tact M 0 idle (one 0 (none, .neg)) none (some (.rewX bits))
    | none => tact M 0 idle (two 0 (none, .pos) 1 (none, .neg)) none (some (.rewC bits))
  | .rewC bits =>
    match ar 1 with
    | some _ => tact M 0 idle (one 1 (none, .neg)) none (some (.rewC bits))
    | none => tact M 0 idle (two 1 (none, .pos) 2 (none, .neg)) none (some (.rewO bits))
  | .rewO bits =>
    match ar 2 with
    | some _ => tact M 0 idle (one 2 (none, .neg)) none (some (.rewO bits))
    | none => tact M 0 idle (one 2 (none, .pos)) none (some (.dec bits M.tm.q₀ .empty true))
  | .dec bits q r b =>
    match ar 1 with
    | none => tact M 0 idle idle none (some (.wdec bits (some q) r b))
    | some false => tact M 0 idle (one 1 (some (some true), .pos)) none (some (.dec bits q r b))
    | some true =>
      let a := M.tm.tr q (ar 0) mr
      let m := virtualMove b (ar 0) a.inputTape
      tact M 0 a.workTapes (two 0 (none, m) 1 (some (some false), .neg)) none
        (some (match a.state with
          | some q' => .ret bits q' (r.push a.output) (virtualNextTag b m)
          | none => .wdec bits none (r.push a.output) (virtualNextTag b m)))
  | .ret bits q r b =>
    match ar 1 with
    | none => tact M 0 idle (one 1 (none, .pos)) none (some (.dec bits q r b))
    | some _ => tact M 0 idle (one 1 (none, .neg)) none (some (.ret bits q r b))
  | .wdec bits oq r b =>
    match ar 2 with
    | none => tact M 0 idle idle (some (selAnswer (decodeSel bits) oq r (ar 0) mr)) none
    | some false =>
      tact M 0 idle (one 2 (some (some true), .pos)) none (some (.wdec bits oq r b))
    | some true =>
      match decodeSel bits with
      | .sym (some h) neg _ =>
        tact M 0 (one h (none, walkDir neg)) (one 2 (some (some false), .neg)) none
          (some (.wret bits oq r b))
      | .sym none neg _ =>
        let m := virtualMove b (ar 0) (walkDir neg)
        tact M 0 idle (two 0 (none, m) 2 (some (some false), .neg)) none
          (some (.wret bits oq r (virtualNextTag b m)))
      | .st _ _ =>
        tact M 0 idle (one 2 (some (some false), .neg)) none (some (.wret bits oq r b))
  | .wret bits oq r b =>
    match ar 2 with
    | none => tact M 0 idle (one 2 (none, .pos)) none (some (.wdec bits oq r b))
    | some _ => tact M 0 idle (one 2 (none, .neg)) none (some (.wret bits oq r b))

/-- **The tableau machine** of `M` [AB09, proof of Thm 6.20: the language "bit `j` of
the `i`-th snapshot of `M` on `x`", here in head-relative form]: see the module
docstring. -/
noncomputable def tabTM : FinTM Bool where
  k := M.k + 3
  State := St M
  tm := { q₀ := .sel ⟨0, nbitsOf_pos M.State M.k⟩ (fun _ => false), tr := tabTr M }

/-! ### Configurations in block form -/

/-- A configuration of the tableau machine in block form: state `st`, real input head
`p`, `M`'s tapes `mt` with heads `mh`, auxiliary tapes `at` with heads `ah`, output
`out`. -/
def tcfg {y : List Bool} (st : Option (St M)) (p : Fin (y.length + 2))
    (mt : Fin M.k → ℤ → Option Bool) (mh : Fin M.k → ℤ)
    (au : Fin 3 → ℤ → Option Bool) (ah : Fin 3 → ℤ) (out : List Bool) :
    Cfg (tabTM M).k Bool (tabTM M).State y where
  state := st
  inputPos := p
  workTapes := Fin.addCases mt au
  workTapePos := Fin.addCases mh ah
  output := out

/-- The tape after an optional write at the head. -/
def wr (w : Option (Option Bool)) (τ : ℤ → Option Bool) (z : ℤ) : ℤ → Option Bool :=
  match w with
  | none => τ
  | some s => Function.update τ z s

/-- **Applying a block action to a block configuration** acts blockwise.

**Proof sketch.** Extensionality on the five fields; on each tape block `Fin.addCases`
splits the action and the configuration consistently. -/
theorem tact_apply {y : List Bool} (im : SignType)
    (mw : Fin M.k → Option (Option Bool) × SignType)
    (aw : Fin 3 → Option (Option Bool) × SignType) (o : Option Bool) (q : Option (St M))
    (st : Option (St M)) (p : Fin (y.length + 2))
    (mt : Fin M.k → ℤ → Option Bool) (mh : Fin M.k → ℤ)
    (au : Fin 3 → ℤ → Option Bool) (ah : Fin 3 → ℤ) (out : List Bool) :
    (tact M im mw aw o q).apply (tcfg M st p mt mh au ah out) =
      tcfg M q (moveInputPos p im) (fun i => wr (mw i).1 (mt i) (mh i))
        (fun i => mh i + (mw i).2) (fun j => wr (aw j).1 (au j) (ah j))
        (fun j => ah j + (aw j).2) (out ++ o.toList) := by
  refine Cfg.ext rfl rfl ?_ ?_ rfl
  · funext i
    refine Fin.addCases ?_ ?_ i
    · intro j
      simp only [Action.apply, tact, tcfg, Fin.addCases_left]
      cases (mw j).1 <;> rfl
    · intro j
      simp only [Action.apply, tact, tcfg, Fin.addCases_right]
      cases (aw j).1 <;> rfl
  · funext i
    refine Fin.addCases ?_ ?_ i <;> intro j <;> simp [Action.apply, tact, tcfg]

/-- **One step of the tableau machine** from a live block configuration applies the
transition table to the block reads. -/
theorem tabTM_step {y : List Bool} (q : St M) (p : Fin (y.length + 2))
    (mt : Fin M.k → ℤ → Option Bool) (mh : Fin M.k → ℤ)
    (au : Fin 3 → ℤ → Option Bool) (ah : Fin 3 → ℤ) (out : List Bool) :
    (tabTM M).tm.step (tcfg M (some q) p mt mh au ah out) =
      (tabTr M q (tcfg M (some q) p mt mh au ah out).inputSymbol
        (Fin.addCases (fun i => mt i (mh i)) (fun j => au j (ah j)))).apply
        (tcfg M (some q) p mt mh au ah out) := by
  have hw : (tcfg M (some q) p mt mh au ah out).workTapeSymbols =
      Fin.addCases (fun i => mt i (mh i)) (fun j => au j (ah j)) := by
    funext i
    refine Fin.addCases ?_ ?_ i <;> intro j <;> simp [Cfg.workTapeSymbols, tcfg]
  unfold MultiTapeTM.step
  simp only [tcfg]
  rw [← hw]
  rfl

/-- The input symbol of a block configuration depends only on the real input head. -/
theorem tcfg_inputSymbol {y : List Bool} (st : Option (St M)) (p : Fin (y.length + 2))
    (mt : Fin M.k → ℤ → Option Bool) (mh : Fin M.k → ℤ)
    (au : Fin 3 → ℤ → Option Bool) (ah : Fin 3 → ℤ) (out : List Bool) :
    (tcfg M st p mt mh au ah out).inputSymbol =
      (tcfg M st p (fun _ _ => none) (fun _ => 0) (fun _ _ => none) (fun _ => 0) []).inputSymbol :=
  rfl

end Complexity.Meyer
