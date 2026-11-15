/-
Copyright (c) 2026 Seyoon Ragavan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Seyoon Ragavan
-/
import TCSlib.Complexity.SpaceComplexity.Logspace.InputAccess

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# The oracle-input simulator: logspace preimages along implicit functions

[AB09, proof of Lemma 4.17, Fig. 4.3]: to decide whether `f x ∈ C`, run `C`'s logspace decider
`M` on a **virtual input** `f x` that is never written down. Whenever `M` reads its input, its
head position (in binary) is a query `⟨x, i⟩` to the length and bit deciders of `f`. The
received `LogProg` call protocol does not host this by itself. A call's virtual input is read
physically, as the whole input or its leading run of `1`s followed by register words, and
nothing serves a decider's input symbols through further calls (P0 reception audit,
`audits/ch34-p0-findings.md`, note 10). This file adds the missing engine as a register-tape
program on the received compiler.

The **oracle-input simulator** `Complexity.LogProg.OIS.prog M` keeps `M`'s work tapes on
registers `0, …, M.k − 1`, where they are touched only by `M`'s own transitions. It keeps `M`'s
input position `p` as the index `p − 1` in binary on the last register `q` (with `p = 0`, the
left blank, recorded in the control state). Each step of `M` runs as follows:

1. one `whole`-mode call on `[q]` asks the length decider whether `p − 1 < |f x|`;
2. if so, a second call asks the bit decider for the symbol;
3. one ordinary step applies `M`'s transition to the work registers;
4. the increment and decrement fragments move `q` as `M`'s clamped input move dictates.

Phase P4.4b of `AroraBarakChapters3-4Plan.md`; `audits/ch4-p44-resolutions-addendum.md`
records it as the route of `Complexity.mem_LOGSPACE_of_logspaceReducible`. The simulator is
campaign-owned and lives here (decision D3), beside its only class-level corollary.

## Main definitions

* `Complexity.LogProg.OIS.Ph`, `OIS.tr`, `OIS.call` — the phases, ordinary transitions and
  call nodes of the simulator.
* `Complexity.LogProg.OIS.prog`, `OIS.start` — the simulator program and its start state.
* `Complexity.LogProg.OIS.lo`, `OIS.hi` — its register ranges.

## Main results

* `Complexity.LogProg.OIS.run` — the run contract: against any oracle answering the two
  queries truthfully, the program halts with `M`'s output on the virtual input, inside the
  ranges, with well-formed calls (proved; phase-P4.4b statement).
* `Complexity.LogProg.OIS.compile_decides` — the space contract: compiled against a bank of
  the two deciders, it computes `M`'s output on the virtual input within the ranges plus the
  bank's space (proved; phase-P4.4b statement).
* `Complexity.mem_LOGSPACE_preimage` — logspace preimages along implicitly logspace
  computable maps are in `L` (proved; phase-P4.4b statement).

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009. (§4.3, Lemma 4.17 and its proof, Figure 4.3.)
-/

namespace Complexity

open Turing

namespace LogProg.OIS

/-- The phases of the simulator: the length call (`ask`) and the bit call (`bit`); the
simulated step with the symbol read (`work a lb`, `lb` marking the left blank); the zero test
before a left move (`zt`); the increment (`iC`, `iB`) and decrement (`dD`, `dL`, `dE`, `dB`)
of the index register. -/
inductive Ph where
  | ask | bit
  | work (a : Option Bool) (lb : Bool)
  | zt
  | iC | iB
  | dD | dL | dE | dB
  deriving DecidableEq, Fintype

variable (M : FinTM Bool)

/-- The index register of the simulator, the last one. -/
abbrev q : Fin (M.k + 1) := Fin.last M.k

/-- The phase after a simulated step, from the decider's input move `d`, at the left blank
(`lb`) or at the right blank (`rb`): from the left blank, a right move reaches position `1`
(index `0`); elsewhere a left move first tests the index for zero, and a right move increments
it unless clamped at the right blank. -/
def nextPh (d : SignType) (lb rb : Bool) : Ph :=
  if lb then (if d = 1 then .ask else .work none true)
  else if d = -1 then .zt
  else if d = 1 ∧ rb = false then .iC
  else .ask

/-- The decider's action on the work registers: input head and index register still, output
forwarded, the next phase by `nextPh`. -/
def liftAct (A : Action M.k Bool M.State) (lb rb : Bool) : Action (M.k + 1) Bool (M.State × Ph) :=
  ⟨0, Fin.lastCases (none, 0) A.workTapes, A.output,
    A.state.map fun s' => (s', nextPh A.inputTape lb rb)⟩

/-- **The ordinary transitions of the simulator.** `work a lb` applies `M`'s transition at the
symbol `a` (at the right blank exactly when `a = none` and not `lb`); `zt` reads the index
register's cell `0` (blank iff the index is `0`); the increment and decrement fragments act on
the index register and return to `ask`. The call phases' transitions are never used. -/
def tr : M.State × Ph → Option Bool → (Fin (M.k + 1) → Option Bool) →
    Action (M.k + 1) Bool (M.State × Ph)
  | (s, .work a lb), _, w =>
    liftAct M (M.tm.tr s a fun i => w i.castSucc) lb (a.isNone && !lb)
  | (s, .zt), _, w =>
    regAct (q M) none 0 (match w (q M) with
      | none => (s, .work none true)
      | some _ => (s, .dD))
  | (s, .iC), _, w => incCAct (q M) (s, .iC) (s, .iB) (w (q M))
  | (s, .iB), _, w => incBAct (q M) (s, .iB) (s, .ask) (w (q M))
  | (s, .dD), _, w => decDAct (q M) (s, .dD) (s, .dL) (s, .dB) (w (q M))
  | (s, .dL), _, w => decLAct (q M) (s, .dE) (s, .dB) (w (q M))
  | (s, .dE), _, _ => decEAct (q M) (s, .dB)
  | (s, .dB), _, w => incBAct (q M) (s, .dB) (s, .ask) (w (q M))
  | (_, .ask), _, _ => junkAct
  | (_, .bit), _, _ => junkAct

/-- **The call nodes of the simulator.** `ask` asks decider `0` (the length language) about
`⟨x, bits i⟩`, `i` the index register: on *yes* go on to `bit`; on *no* the symbol is the right
blank. `bit` asks decider `1` (the bit language) and goes on to the simulated step with the
answer. -/
def call : M.State × Ph → Option (CallSpec (M.k + 1) 2 (M.State × Ph))
  | (s, .ask) => some ⟨0, .whole, [q M], (s, .bit), (s, .work none false)⟩
  | (s, .bit) => some ⟨1, .whole, [q M], (s, .work (some true) false),
      (s, .work (some false) false)⟩
  | _ => none

/-- **The oracle-input simulator** of the decider `M`: a register-tape program over `M.k + 1`
registers calling two deciders. A hand-built program: no received layer serves a decider's
input from oracle calls. -/
def prog : RProg (M.k + 1) 2 (M.State × Ph) := ⟨⟨(M.tm.q₀, .ask), tr M⟩, call M⟩

/-- The start state of the simulator: `M`'s start state, about to ask for symbol `0`. -/
def start : M.State × Ph := (M.tm.q₀, .ask)

/-- The lower register bounds: `-S` on the work registers, `-1` on the index register. -/
def lo (S : ℕ) : Fin (M.k + 1) → ℤ := Fin.lastCases (-1) fun _ => -(S : ℤ)

/-- The upper register bounds: `S` on the work registers, `W` on the index register. -/
def hi (S W : ℕ) : Fin (M.k + 1) → ℤ := Fin.lastCases (W : ℤ) fun _ => (S : ℤ)

/-- The source configuration represented on the host, with an explicit index and phase.
The index is unconstrained after a halt because no later input move is simulated. -/
private def imageCfg {v : List Bool} (x : List Bool) (c : Cfg M.k Bool M.State v)
    (i : ℕ) (ph : Ph) : Cfg (M.k + 1) Bool (M.State × Ph) x :=
  ⟨c.state.map (fun s => (s, ph)), 1,
    Fin.lastCases (FinTM.bufferTape (Nat.bits i)) c.workTapes,
    Fin.lastCases 0 c.workTapePos, c.output⟩

/-- The representation at a simulated-step boundary; the index agrees with the input
position while the source is live, and is merely in range once it has halted. -/
private def Represents {x v : List Bool} (c : Cfg M.k Bool M.State v)
    (d : Cfg (M.k + 1) Bool (M.State × Ph) x) : Prop :=
  ∃ i ≤ v.length,
    d = imageCfg M x c i (if c.inputPos.val = 0 then .work none true else .ask) ∧
    (c.state ≠ none → i = c.inputPos.val - 1)

/-- The intermediate invariant combines register ranges and the canonical call seam. -/
private def Safe {x : List Bool} (F S : ℕ)
    (d : Cfg (M.k + 1) Bool (M.State × Ph) x) : Prop :=
  (∀ r, lo M S r ≤ d.workTapePos r ∧
    d.workTapePos r ≤ hi M S (Nat.bits (F + 1)).length r) ∧
  ∀ l cs, d.state = some l → (prog M).call l = some cs →
    d.inputPos.val = 1 ∧ d.workTapePos (q M) = 0 ∧
    ∃ i ≤ F, d.workTapes (q M) = FinTM.bufferTape (Nat.bits i)

/-- An encoded configuration has bounded heads and a canonical call register, independently
of its phase. -/
private theorem imageCfg_safe {x v : List Bool} (c : Cfg M.k Bool M.State v)
    (i S : ℕ) (ph : Ph) (hi : i ≤ v.length)
    (hb : ∀ r, -(S : ℤ) ≤ c.workTapePos r ∧ c.workTapePos r ≤ (S : ℤ)) :
    Safe M v.length S (imageCfg M x c i ph) := by
  constructor
  · intro r
    refine Fin.lastCases ?_ (fun j => ?_) r
    · simp [imageCfg, lo, OIS.hi]
    · simpa [imageCfg, lo, OIS.hi] using hb j
  · intro l cs _ _
    exact ⟨by simp [imageCfg], by simp [imageCfg, q], i, hi, by simp [imageCfg, q]⟩

/-- The length call preserves the represented tapes and returns its Boolean branch. -/
private theorem ask_step {x v : List Bool} (o : Fin 2 → List Bool → Bool)
    (c : Cfg M.k Bool M.State v) (s : M.State) (hs : c.state = some s) (i : ℕ) :
    rrun (prog M) o (imageCfg M x c i .ask) 1 =
      imageCfg M x c i (if o 0 (pairEncode x (Nat.bits i)) then .bit else .work none false) := by
  simp [rrun_one, rstep, prog, call, imageCfg, hs, vword_whole₁, regWords,
    q, tapeWord_bufferTape]
  split <;> rfl

/-- The bit call preserves the represented tapes and stores the answer in the phase. -/
private theorem bit_step {x v : List Bool} (o : Fin 2 → List Bool → Bool)
    (c : Cfg M.k Bool M.State v) (s : M.State) (hs : c.state = some s) (i : ℕ) :
    rrun (prog M) o (imageCfg M x c i .bit) 1 =
      imageCfg M x c i (.work (some (o 1 (pairEncode x (Nat.bits i)))) false) := by
  simp only [rrun_one, rstep, imageCfg, hs, Option.map_some, prog, call]
  rw [vword_whole₁]
  simp only [regWords, q, Fin.lastCases_last, tapeWord_bufferTape]
  cases o 1 (pairEncode x (Nat.bits i)) <;> rfl

/-- Applying the lifted action updates exactly the source tapes and output.
The source input head moves in `M.tm.step c`; its encoded index is moved afterwards.

**Proof sketch.** Extensionality separates state, input head, work tapes, head positions and
output. Split each register into a source register or the last index register; the former
receives the source action, while the latter is unchanged. -/
private theorem work_step {x v : List Bool} (o : Fin 2 → List Bool → Bool)
    (c : Cfg M.k Bool M.State v) (s : M.State) (hs : c.state = some s) (i : ℕ) (lb : Bool) :
    rrun (prog M) o (imageCfg M x c i (.work c.inputSymbol lb)) 1 =
      imageCfg M x (M.tm.step c) i
        (nextPh (M.tm.tr s c.inputSymbol c.workTapeSymbols).inputTape lb
          (c.inputSymbol.isNone && !lb)) := by
  rw [rrun_one, rstep_noncall (prog M) o _ (s, .work c.inputSymbol lb)
    (by simp [imageCfg, hs]) rfl]
  simp only [MultiTapeTM.step, imageCfg, hs, Option.map_some, prog, tr]
  simp only [Cfg.workTapeSymbols, Fin.lastCases_castSucc]
  refine Cfg.ext ?_ ?_ ?_ ?_ rfl
  · simp [liftAct, Action.apply]; rfl
  · simp [Action.apply, liftAct]
  · funext r z
    refine Fin.lastCases ?_ (fun j => ?_) r <;>
      simp [Action.apply, liftAct]
    rfl
  · funext r
    refine Fin.lastCases ?_ (fun j => ?_) r <;>
      simp [Action.apply, liftAct]
    rfl

/-- An index-only register view of a live encoded configuration is the same encoding with
its phase and index replaced. -/
private theorem index_view {x v : List Bool} (c : Cfg M.k Bool M.State v)
    (s : M.State) (hs : c.state = some s) (i j : ℕ) (ph ph' : Ph) :
    regCfg (imageCfg M x c i ph) (s, ph') (q M) (FinTM.bufferTape (Nat.bits j)) 0 =
      imageCfg M x c j ph' := by
  refine Cfg.ext (by simp [imageCfg, hs, regCfg]) rfl ?_ ?_ rfl
  · funext r z
    refine Fin.lastCases ?_ (fun k => ?_) r <;> simp [regCfg, imageCfg, q]
  · funext r
    refine Fin.lastCases ?_ (fun k => ?_) r <;> simp [regCfg, imageCfg, q]

/-- An intermediate index-fragment configuration is safe when its state is non-call and
its index head is in the fragment's range. -/
private theorem index_fragment_safe {x v : List Bool} (c : Cfg M.k Bool M.State v)
    (i S : ℕ) (ph : Ph) (l : M.State × Ph) (f : ℤ → Option Bool) (p : ℤ)
    (hb : ∀ r, -(S : ℤ) ≤ c.workTapePos r ∧ c.workTapePos r ≤ (S : ℤ))
    (hc : (prog M).call l = none) (hp : -1 ≤ p)
    (hp' : p ≤ (Nat.bits (v.length + 1)).length) :
    Safe M v.length S (regCfg (imageCfg M x c i ph) l (q M) f p) := by
  constructor
  · intro r
    refine Fin.lastCases ?_ (fun k => ?_) r
    · simpa [regCfg, imageCfg, lo, hi, q] using And.intro hp hp'
    · simpa [regCfg, imageCfg, lo, hi, q] using hb k
  · intro l' cs hl' hcs
    have hll : l = l' := Option.some.inj hl'
    subst l'
    rw [hc] at hcs
    contradiction

/-- The frozen increment fragment advances the encoded input index and respects the
simulator invariant. -/
private theorem index_inc {x v : List Bool} (o : Fin 2 → List Bool → Bool)
    (c : Cfg M.k Bool M.State v) (s : M.State) (hs : c.state = some s) (i S : ℕ)
    (hi : i < v.length)
    (hb : ∀ r, -(S : ℤ) ≤ c.workTapePos r ∧ c.workTapePos r ≤ (S : ℤ)) :
    ∃ T, rrun (prog M) o (imageCfg M x c i .iC) T = imageCfg M x c (i + 1) .ask ∧
      ∀ n < T, Safe M v.length S (rrun (prog M) o (imageCfg M x c i .iC) n) := by
  obtain ⟨T, he, hm⟩ := inc_run (prog M) o (q M) (s, .iC) (s, .iB) (s, .ask)
    (fun _ _ => rfl) (fun _ _ => rfl) rfl rfl (imageCfg M x c i .iC) i
  rw [index_view M c s hs, index_view M c s hs] at he
  refine ⟨T, he, fun n hn => ?_⟩
  rw [index_view M c s hs] at hm
  obtain ⟨l, f, p, hp, hl, hlo, hhi⟩ := hm n hn
  rw [hp]
  apply index_fragment_safe M c i S .iC l f p hb
  · rcases hl with rfl | rfl <;> rfl
  · exact hlo
  · have hw := length_bits_mono (show i + 1 ≤ v.length + 1 by omega)
    omega

/-- The received decrement fragment reduces a positive encoded index and respects the
simulator invariant. -/
private theorem index_dec {x v : List Bool} (o : Fin 2 → List Bool → Bool)
    (c : Cfg M.k Bool M.State v) (s : M.State) (hs : c.state = some s) (i S : ℕ)
    (hi : i ≤ v.length)
    (hb : ∀ r, -(S : ℤ) ≤ c.workTapePos r ∧ c.workTapePos r ≤ (S : ℤ)) :
    ∃ T, rrun (prog M) o (imageCfg M x c i .dD) T = imageCfg M x c (i - 1) .ask ∧
      ∀ n < T, Safe M v.length S (rrun (prog M) o (imageCfg M x c i .dD) n) := by
  obtain ⟨T, he, hm⟩ := dec_run (prog M) o (q M) (s, .dD) (s, .dL) (s, .dE)
    (s, .dB) (s, .ask) (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl)
    (fun _ _ => rfl) rfl rfl rfl rfl (imageCfg M x c i .dD) i
  rw [index_view M c s hs, index_view M c s hs] at he
  refine ⟨T, he, fun n hn => ?_⟩
  rw [index_view M c s hs] at hm
  obtain ⟨l, f, p, hp, hcall, hlo, hhi⟩ := hm n hn
  rw [hp]
  exact index_fragment_safe M c i S .dD l f p hb hcall hlo
    (hhi.trans (by exact_mod_cast length_bits_mono (show i ≤ v.length + 1 by omega)))

/-- The zero test changes phase according to whether the canonical index word is empty. -/
private theorem zero_step {x v : List Bool} (o : Fin 2 → List Bool → Bool)
    (c : Cfg M.k Bool M.State v) (s : M.State) (hs : c.state = some s) (i : ℕ) :
    rrun (prog M) o (imageCfg M x c i .zt) 1 =
      imageCfg M x c i (if i = 0 then .work none true else .dD) := by
  have hv : FinTM.bufferTape (Nat.bits i) 0 = (Nat.bits i).head? := by
    simp [FinTM.bufferTape, List.head?_eq_getElem?]
  simp only [rrun_one, rstep, imageCfg, hs, Option.map_some, prog, call,
    MultiTapeTM.step, tr, Cfg.workTapeSymbols, q, Fin.lastCases_last]
  rw [hv, bits_head_odd]
  split_ifs with hi
  all_goals
    apply Cfg.ext <;> simp [regAct, Action.apply]

/-- The phase table realizes the clamped source input move using the received index
fragments; no work register or output is modified during this adjustment.

**Proof sketch.** Split the source move and the two boundaries. Staying put and clamped
moves need no steps. A right move at a letter uses `index_inc`; a left move tests zero,
then either marks the left blank or uses `index_dec`. -/
private theorem adjust_index {x v : List Bool} (o : Fin 2 → List Bool → Bool)
    (c : Cfg M.k Bool M.State v) (s : M.State) (hs : c.state = some s)
    (p : Fin (v.length + 2)) (mv : SignType) (S : ℕ)
    (hip : c.inputPos = moveInputPos p mv)
    (hb : ∀ r, -(S : ℤ) ≤ c.workTapePos r ∧ c.workTapePos r ≤ (S : ℤ)) :
    ∃ T, Represents M c (rrun (prog M) o (imageCfg M x c (p.val - 1)
        (nextPh mv (decide (p.val = 0)) (decide (p.val = v.length + 1)))) T) ∧
      ∀ n < T, Safe M v.length S (rrun (prog M) o (imageCfg M x c (p.val - 1)
        (nextPh mv (decide (p.val = 0)) (decide (p.val = v.length + 1)))) n) := by
  have hp := p.isLt
  have himg (j : ℕ) (hj : j ≤ v.length) (ph : Ph)
      (hph : ph = if c.inputPos.val = 0 then .work none true else .ask)
      (hj' : j = c.inputPos.val - 1) : Represents M c (imageCfg M x c j ph) :=
    ⟨j, hj, by rw [hph], fun _ => hj'⟩
  have hpos := (congrArg Fin.val hip).trans
    (moveInputPos_val v.length p.val p.isLt mv)
  clear hip
  by_cases hp0 : p.val = 0
  · cases mv <;> simp only [hp0, decide_true, nextPh, ↓reduceIte,
      SignType.zero_eq_zero, SignType.neg_eq_neg_one, SignType.pos_eq_one] at *
    all_goals
      refine ⟨0, himg _ (by omega) _ ?_ (by omega), fun n hn => by omega⟩
      simp_all
  · cases mv with
    | zero =>
      dsimp only at hpos
      simp only [SignType.zero_eq_zero, nextPh, hp0, decide_false, Bool.false_eq_true,
        ↓reduceIte, (by decide : (0 : SignType) ≠ -1), (by decide : (0 : SignType) ≠ 1), false_and]
      refine ⟨0, himg _ (by omega) _ ?_ (by omega), fun n hn => by omega⟩
      rw [if_neg (show c.inputPos.val ≠ 0 by omega)]
    | pos =>
      dsimp only at hpos
      by_cases hpr : p.val = v.length + 1
      · simp [nextPh, hpr, SignType.pos_eq_one]
        refine ⟨0, himg _ (by omega) _ ?_ (by omega), fun n hn => by omega⟩
        rw [if_neg (show c.inputPos.val ≠ 0 by omega)]
      · simp only [SignType.pos_eq_one, nextPh, hp0, hpr, decide_false,
          Bool.false_eq_true, ↓reduceIte, (by decide : (1 : SignType) ≠ -1), and_self]
        obtain ⟨T, he, hm⟩ := index_inc M o c s hs (p.val - 1) S (by omega) hb
        refine ⟨T, ?_, hm⟩
        rw [he]
        exact himg _ (by omega) _ (by rw [if_neg (show c.inputPos.val ≠ 0 by omega)]) (by omega)
    | neg =>
      dsimp only at hpos
      simp only [SignType.neg_eq_neg_one, nextPh, hp0, decide_false,
        Bool.false_eq_true, ↓reduceIte]
      by_cases hi : p.val - 1 = 0
      · refine ⟨1, ?_, fun n hn => ?_⟩
        · rw [zero_step M o c s hs, if_pos hi]
          exact himg _ (by omega) _ (by rw [if_pos (show c.inputPos.val = 0 by omega)]) (by omega)
        · have hn0 : n = 0 := by omega
          subst n
          exact imageCfg_safe M c _ S _ (by omega) hb
      · obtain ⟨T, he, hm⟩ := index_dec M o c s hs (p.val - 1) S (by omega) hb
        refine ⟨1 + T, ?_, fun n hn => ?_⟩
        · rw [rrun_add, zero_step M o c s hs, if_neg hi, he]
          exact himg _ (by omega) _ (by rw [if_neg (show c.inputPos.val ≠ 0 by omega)]) (by omega)
        · by_cases hn0 : n = 0
          · subst n
            exact imageCfg_safe M c _ S _ (by omega) hb
          · have heq : n = 1 + (n - 1) := by omega
            rw [heq, rrun_add, zero_step M o c s hs, if_neg hi]
            exact hm (n - 1) (by omega)

/-- A represented configuration inherits its work-head bounds from the source. -/
private theorem represents_safe {x v : List Bool} {S : ℕ}
    {c : Cfg M.k Bool M.State v} {d : Cfg (M.k + 1) Bool (M.State × Ph) x}
    (h : Represents M c d)
    (hb : ∀ r, -(S : ℤ) ≤ c.workTapePos r ∧ c.workTapePos r ≤ (S : ℤ)) :
    Safe M v.length S d := by
  obtain ⟨i, hidx, rfl, _⟩ := h
  exact imageCfg_safe M c i S _ hidx hb

/-- One simulated source step, including the final step that halts.

**Proof sketch.** At positive input position, perform the length call and, if its answer
is true, the bit call. The two oracle laws identify the supplied symbol. At the left
blank the symbol is already in the state. Apply `liftAct` once. If its next state is
`none`, the resulting represented configuration keeps the old, bounded index. Otherwise
split the input move and the boundary flags in `nextPh`: use `inc_run` away from the right
blank, and the zero test followed by `dec_run` for a positive predecessor index. A zero
index on a left move changes only the phase. The fragment bounds and the bounds on the
two source configurations give `Safe`; fragment states are non-call states. -/
private theorem represented_step {x v : List Bool} (o : Fin 2 → List Bool → Bool)
    (ho0 : ∀ i ≤ v.length, o 0 (pairEncode x (Nat.bits i)) = decide (i < v.length))
    (ho1 : ∀ i < v.length, o 1 (pairEncode x (Nat.bits i)) = v.getD i false)
    (c : Cfg M.k Bool M.State v) (d : Cfg (M.k + 1) Bool (M.State × Ph) x) (S : ℕ)
    (hrep : Represents M c d) (hlive : c.state ≠ none)
    (hb : ∀ r, -(S : ℤ) ≤ c.workTapePos r ∧ c.workTapePos r ≤ (S : ℤ))
    (hb' : ∀ r, -(S : ℤ) ≤ (M.tm.step c).workTapePos r ∧
      (M.tm.step c).workTapePos r ≤ (S : ℤ)) :
    ∃ N, Represents M (M.tm.step c) (rrun (prog M) o d N) ∧
      ∀ n < N, Safe M v.length S (rrun (prog M) o d n) := by
  obtain ⟨i, hiv, rfl, hidx⟩ := hrep
  obtain ⟨s, hs⟩ := Option.ne_none_iff_exists'.mp hlive
  have hi := hidx hlive
  have hsym : c.inputSymbol = if c.inputPos.val = 0 then none else v[i]? := by
    simp only [inputSymbol_eq, hi]
  have supply : ∃ T, rrun (prog M) o
      (imageCfg M x c i (if c.inputPos.val = 0 then .work none true else .ask)) T =
        imageCfg M x c i (.work c.inputSymbol (decide (c.inputPos.val = 0))) ∧
      ∀ n < T, Safe M v.length S (rrun (prog M) o
        (imageCfg M x c i (if c.inputPos.val = 0 then .work none true else .ask)) n) := by
    by_cases hp : c.inputPos.val = 0
    · refine ⟨0, ?_, fun n hn => by omega⟩
      simp [rrun_zero, hp, hsym]
    · simp only [hp, ↓reduceIte, decide_false, hsym]
      by_cases hv : i < v.length
      · have he : v[i]? = some (v.getD i false) := by
          simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hv]
        refine ⟨1 + 1, ?_, fun n hn => ?_⟩
        · rw [rrun_add, ask_step M o c s hs, ho0 i hiv]
          simp only [hv, decide_true, ↓reduceIte]
          rw [bit_step M o c s hs, ho1 i hv, he]
        · have hn' : n = 0 ∨ n = 1 := by omega
          rcases hn' with rfl | rfl
          · exact imageCfg_safe M c i S .ask hiv hb
          · rw [ask_step M o c s hs, ho0 i hiv]
            simp only [hv, decide_true, ↓reduceIte]
            exact imageCfg_safe M c i S .bit hiv hb
      · refine ⟨1, ?_, fun n hn => ?_⟩
        · rw [ask_step M o c s hs, ho0 i hiv]
          simp [hv]
        · have hn0 : n = 0 := by omega
          subst n
          exact imageCfg_safe M c i S .ask hiv hb
  obtain ⟨A, hA, hAm⟩ := supply
  have hwork := work_step M (x := x) o c s hs i (decide (c.inputPos.val = 0))
  have rest : ∃ T, Represents M (M.tm.step c)
      (rrun (prog M) o (imageCfg M x c i (.work c.inputSymbol
        (decide (c.inputPos.val = 0)))) T) ∧
      ∀ n < T, Safe M v.length S (rrun (prog M) o (imageCfg M x c i
        (.work c.inputSymbol (decide (c.inputPos.val = 0)))) n) := by
    by_cases hh : (M.tm.step c).state = none
    · refine ⟨1, ⟨i, hiv, ?_, fun hn => (hn hh).elim⟩, fun n hn => ?_⟩
      · rw [hwork]
        simp [imageCfg, hh]
      · have hn0 : n = 0 := by omega
        subst n
        exact imageCfg_safe M c i S _ hiv hb
    · obtain ⟨s', hs'⟩ := Option.ne_none_iff_exists'.mp hh
      have hip : (M.tm.step c).inputPos = moveInputPos c.inputPos
          (M.tm.tr s c.inputSymbol c.workTapeSymbols).inputTape := by
        simp [MultiTapeTM.step, hs, Action.apply]
      have hrb : (c.inputSymbol.isNone && !decide (c.inputPos.val = 0)) =
          decide (c.inputPos.val = v.length + 1) := by
        have hpos := c.inputPos.isLt
        by_cases hp0 : c.inputPos.val = 0
        · simp [hp0]
        · simp only [hsym, hp0, ↓reduceIte, decide_false, Bool.not_false, Bool.and_true]
          by_cases hit : i < v.length
          · simp [List.getElem?_eq_getElem hit, show c.inputPos.val ≠ v.length + 1 by omega]
          · simp [(List.getElem?_eq_none (show v.length ≤ i by omega)), show c.inputPos.val = v.length + 1 by omega]
      obtain ⟨T, he, hm⟩ := adjust_index M (x := x) o (M.tm.step c) s' hs' c.inputPos
        (M.tm.tr s c.inputSymbol c.workTapeSymbols).inputTape S hip hb'
      refine ⟨1 + T, ?_, fun n hn => ?_⟩
      · rw [rrun_add, hwork, hrb, hi]
        exact he
      · by_cases hn0 : n = 0
        · subst n
          exact imageCfg_safe M c i S _ hiv hb
        · have hn' : n = 1 + (n - 1) := by omega
          rw [hn', rrun_add, hwork, hrb, hi]
          exact hm (n - 1) (by omega)
  obtain ⟨B, hB, hBm⟩ := rest
  refine ⟨A + B, ?_, fun n hn => ?_⟩
  · rw [rrun_add, hA]
    exact hB
  · by_cases hnA : n < A
    · exact hAm n hnA
    · have hn' : n = A + (n - A) := by omega
      rw [hn', rrun_add, hA]
      exact hBm (n - A) (by omega)

/-- Every head of a source run up to time `t` is inside the scalar space radius at `t`.

**Proof sketch.** The current cell was visited by that tape. Monotonicity includes it in
the visited set at `t`; the unit-step displacement bound and the corresponding summand
of total visited-cell space give the claimed radius. -/
private theorem source_head_bounds (v : List Bool) (t n : ℕ) (hn : n ≤ t) :
    ∀ r, -(M.tm.spaceUsed (M.tm.initCfg v) t : ℤ) ≤
      (M.tm.runFrom (M.tm.initCfg v) n).workTapePos r ∧
      (M.tm.runFrom (M.tm.initCfg v) n).workTapePos r ≤
        (M.tm.spaceUsed (M.tm.initCfg v) t : ℤ) := by
  intro r
  have hmem : (M.tm.runFrom (M.tm.initCfg v) n).workTapePos r ∈
      M.tm.visitedByTapeHead (M.tm.initCfg v) n r := by
    exact Finset.mem_image.mpr ⟨n, Finset.mem_range.mpr (by omega), rfl⟩
  have habs := M.tm.abs_pos_lt_card_visited v t r
    (M.tm.visitedByTapeHead_mono (M.tm.initCfg v) hn r hmem)
  have hcard : (M.tm.visitedByTapeHead (M.tm.initCfg v) t r).card ≤
      M.tm.spaceUsed (M.tm.initCfg v) t :=
    Finset.single_le_sum (f := fun j => (M.tm.visitedByTapeHead (M.tm.initCfg v) t j).card)
      (fun j _ => Nat.zero_le _) (Finset.mem_univ r)
  exact abs_le.mp (habs.le.trans (by exact_mod_cast hcard))

/-- **The run contract of the simulator** (phase P4.4b; proved). Let `M` halt
by time `t` on the virtual input `v`. Let the oracle answer every length query
`⟨x, bits i⟩` with `i ≤ |v|`, and every bit query with `i < |v|`, truthfully. Then the
program, started on the host input `x`:

* halts with `M`'s output on `v`;
* keeps the work registers in `[-S, S]`, with `S` the space `M` uses up to `t`;
* keeps the index register in `[-1, |bits (|v| + 1)|]`;
* at every call has the input head on position `1` and the index register holding some
  `bits i`, `i ≤ |v|`, with its head on cell `0` — so the call's virtual input is
  `⟨x, bits i⟩` (`Complexity.LogProg.vword_whole₁`).

**Proof sketch.** Encode `M`'s configuration `c` on `v` as the program configuration with:

* the work tapes and heads of `c` on registers `castSucc i`;
* `bits (p − 1)` on `q`, with its head on `0` (`p` the input position of `c`; `bits 0` at
  `p = 0`);
* the host input head on `1`, and `c`'s output;
* state `(s, ask)`, or `(s, work none true)` at `p = 0`.

By induction on `n ≤ t`, the run reaches the encoding of `M.tm.runFrom (M.tm.initCfg v) n`
until `M` halts. One step goes as follows.

1. At most two calls fix the symbol `inSym v p`: by the oracle laws, the length call says
   `p − 1 < |v|`.
2. `work` applies `M.tm.tr` to the `castSucc` block (`liftAct`), so the work registers move
   exactly as `M`'s tapes.
3. The clamped move of `p` is realized by `nextPh`:
   * `inc_run` only when `p − 1 < |v|`;
   * the zero test and `dec_run` only when `p − 1 ≥ 1`;
   * a phase change at the left blank.

Intermediate configurations are those of the received fragments on `q`. The work heads are
`M`'s, so they lie in `[-S, S]` by `Turing.MultiTapeTM.abs_pos_lt_card_visited`. Template:
`ImplicitEnum.{round, rounds, run}`. -/
theorem run (x v : List Bool) (o : Fin 2 → List Bool → Bool)
    (ho0 : ∀ i ≤ v.length, o 0 (pairEncode x (Nat.bits i)) = decide (i < v.length))
    (ho1 : ∀ i < v.length, o 1 (pairEncode x (Nat.bits i)) = v.getD i false)
    (t : ℕ) (ht : (M.tm.runFrom (M.tm.initCfg v) t).state = none) :
    ∃ N, (rrun (prog M) o (Cfg.init (start M) x) N).state = none ∧
      (rrun (prog M) o (Cfg.init (start M) x) N).output =
        (M.tm.runFrom (M.tm.initCfg v) t).output ∧
      (∀ n ≤ N, ∀ r,
        lo M (M.tm.spaceUsed (M.tm.initCfg v) t) r ≤
            (rrun (prog M) o (Cfg.init (start M) x) n).workTapePos r ∧
          (rrun (prog M) o (Cfg.init (start M) x) n).workTapePos r ≤
            hi M (M.tm.spaceUsed (M.tm.initCfg v) t) (Nat.bits (v.length + 1)).length r) ∧
      ∀ n < N, ∀ l cs, (rrun (prog M) o (Cfg.init (start M) x) n).state = some l →
        (prog M).call l = some cs →
          (rrun (prog M) o (Cfg.init (start M) x) n).inputPos.val = 1 ∧
          (rrun (prog M) o (Cfg.init (start M) x) n).workTapePos (q M) = 0 ∧
          ∃ i ≤ v.length, (rrun (prog M) o (Cfg.init (start M) x) n).workTapes (q M) =
            FinTM.bufferTape (Nat.bits i) := by
  obtain ⟨u, hut, hu, heu⟩ := M.tm.exists_first_halt (M.tm.initCfg v) ht
  have rounds : ∀ n ≤ u, ∃ N,
      Represents M (M.tm.runFrom (M.tm.initCfg v) n)
        (rrun (prog M) o (Cfg.init (start M) x) N) ∧
      ∀ j < N, Safe M v.length (M.tm.spaceUsed (M.tm.initCfg v) t)
        (rrun (prog M) o (Cfg.init (start M) x) j) := by
    intro n
    induction n with
    | zero =>
      intro _
      refine ⟨0, ⟨0, Nat.zero_le _, ?_, ?_⟩, fun j hj => by omega⟩
      · refine Cfg.ext rfl ?_ ?_ ?_ rfl
        · apply Fin.ext; simp [rrun_zero, imageCfg, Cfg.init]
        · funext r z
          refine Fin.lastCases ?_ (fun i => ?_) r <;>
            simp [rrun_zero, imageCfg, Cfg.init, MultiTapeTM.initCfg, Nat.zero_bits]
        · funext r
          refine Fin.lastCases ?_ (fun i => ?_) r <;>
            simp [rrun_zero, imageCfg, Cfg.init, MultiTapeTM.initCfg]
      · intro _; rfl
    | succ n ih =>
      intro hn
      obtain ⟨N, hrep, hmid⟩ := ih (by omega)
      obtain ⟨T, hstep, hfrag⟩ := represented_step M o ho0 ho1 _ _ _ hrep (hu n (by omega))
        (source_head_bounds M v t n (by omega))
        (by simpa only [MultiTapeTM.runFrom_succ_eq_step'] using
          source_head_bounds M v t (n + 1) (by omega))
      refine ⟨N + T, ?_, fun j hj => ?_⟩
      · rw [rrun_add, MultiTapeTM.runFrom_succ_eq_step']
        exact hstep
      · by_cases hjN : j < N
        · exact hmid j hjN
        · have he : j = N + (j - N) := by omega
          rw [he, rrun_add]
          exact hfrag (j - N) (by omega)
  obtain ⟨N, hrep, hmid⟩ := rounds u le_rfl
  have hlast := represents_safe M hrep (source_head_bounds M v t u hut)
  obtain ⟨i, hi, he, _⟩ := hrep
  refine ⟨N, ?_, ?_, ?_, ?_⟩
  · rw [he]
    simp only [imageCfg, heu, ht, Option.map_none]
  · rw [he]
    exact congrArg Cfg.output heu
  · intro n hn r
    rcases lt_or_eq_of_le hn with h | rfl
    · exact (hmid n h).1 r
    · exact hlast.1 r
  · intro n hn
    exact (hmid n hn).2

/-- **The space contract of the simulator** (phase P4.4b; proved). Let:

* deciders `Ms j` decide `As j` in space `sb j`;
* on genuine queries about the host input `x`, `As 0` be the length language and `As 1` the
  bit language of the virtual input `v`;
* `M` compute `w` on `v` by time `t`;
* `B` bound the bank's clean-run radius on every query `⟨x, bits i⟩` with `i ≤ |v|`.

Then the simulator, compiled against the bank of the `Ms j`, computes `w` on `x`, visiting at
most `M.k (2S + 1) + (|bits (|v| + 1)| + 2) + kD (2B + 1)` work cells, where `S` is the space
`M` uses up to `t` and `kD` the bank's tape count.

**Proof sketch.** Take `OIS.run` with the oracle `j, V ↦ [V ∈ As j]`, whose laws are the two
hypotheses. Then apply `compile_space` with the ranges `OIS.lo` and `OIS.hi`; their sizes sum
to the first two terms. Each call's precondition `CallOK` comes from `OIS.run`'s call clause:

* the virtual input is `⟨x, bits i⟩` by `vword_whole₁` and `tapeWord_bufferTape`;
* the clean run of the bank is `bank_cleanRun`, weakened to `B` by `CleanRun.mono`;
* `|bits i| ≤ |bits (|v| + 1)|` by `length_bits_mono`. -/
theorem compile_decides (Ms : Fin 2 → FinTM Bool) (As : Fin 2 → Language Bool)
    (sb : Fin 2 → ℕ → ℕ) (hMs : ∀ j, (Ms j).DecidesInSpace (As j) (sb j)) (x v w : List Bool)
    (hA0 : ∀ i ≤ v.length, pairEncode x (Nat.bits i) ∈ As 0 ↔ i < v.length)
    (hA1 : ∀ i < v.length, pairEncode x (Nat.bits i) ∈ As 1 ↔ v.getD i false = true)
    (t : ℕ) (ht : M.ComputesInTime v w t) (B : ℕ)
    (hB : ∀ j, ∀ i ≤ v.length, max (sb j (pairEncode x (Nat.bits i)).length) 1 ≤ B) :
    ∃ T, (compileFinTM (prog M) (start M) (bankTM Ms) (bankStart Ms)).ComputesInTime x w T ∧
      (compileFinTM (prog M) (start M) (bankTM Ms) (bankStart Ms)).tm.spaceUsed
          ((compileFinTM (prog M) (start M) (bankTM Ms) (bankStart Ms)).tm.initCfg x) T ≤
        M.k * (2 * M.tm.spaceUsed (M.tm.initCfg v) t + 1) +
          ((Nat.bits (v.length + 1)).length + 2) + (bankK Ms + bankK Ms) * (2 * B + 1) := by
  classical
  let oracle : Fin 2 → List Bool → Bool := fun j V => MultiTapeTM.indicator (As j) V
  have ho0 : ∀ i ≤ v.length, oracle 0 (pairEncode x (Nat.bits i)) = decide (i < v.length) := by
    intro i hi
    dsimp only [oracle]
    rw [indicator_eq_decide]
    exact decide_eq_decide.mpr (hA0 i hi)
  have ho1 : ∀ i < v.length, oracle 1 (pairEncode x (Nat.bits i)) = v.getD i false := by
    intro i hi
    dsimp only [oracle]
    rw [indicator_eq_decide]
    have hh := hA1 i hi
    cases hv : v.getD i false <;> simp only [hv, Bool.false_eq_true, iff_false, iff_true] at hh
    · simp [hh]
    · simp [hh]
  rw [FinTM.computesInTime_iff] at ht
  obtain ⟨hhalt, hout⟩ := ht
  obtain ⟨N, hN, hOut, hBox, hCalls⟩ := run M x v oracle ho0 ho1 t hhalt
  have hc : ∀ n < N, CallOK (prog M) (bankTM Ms) (bankStart Ms) oracle
      (lo M (M.tm.spaceUsed (M.tm.initCfg v) t))
      (hi M (M.tm.spaceUsed (M.tm.initCfg v) t) (Nat.bits (v.length + 1)).length) B
      (rrun (prog M) oracle (Cfg.init (start M) x) n) := by
    intro n hn l cs hl hcs
    obtain ⟨hip, hqp, i, hiv, hqi⟩ := hCalls n hn l cs hl hcs
    have hshape : cs.mode = .whole ∧ cs.args = [q M] := by
      rcases l with ⟨s, ph⟩
      cases ph <;> simp only [prog, call, Option.some.injEq, reduceCtorEq] at hcs
      all_goals subst cs; exact ⟨rfl, rfl⟩
    have hword : regWords (rrun (prog M) oracle (Cfg.init (start M) x) n) (q M) = Nat.bits i := by
      simp only [regWords, hqi, tapeWord_bufferTape]
    have hquery : vword (callSegs cs x
        (regWords (rrun (prog M) oracle (Cfg.init (start M) x) n))) =
        pairEncode x (Nat.bits i) := by
      rcases cs with ⟨j, mode, args, yes, no⟩
      obtain ⟨rfl, rfl⟩ := hshape
      rw [vword_whole₁, hword]
    refine ⟨by rw [hshape.2]; simp, hip, ?_, ?_⟩
    · intro r hr
      rw [hshape.2, List.mem_singleton] at hr
      subst r
      rw [hword]
      refine ⟨hqi, hqp, by simp [lo, q], ?_⟩
      simpa only [hi, q, Fin.lastCases_last, Nat.cast_le] using
        (length_bits_mono (show i ≤ v.length + 1 by omega))
    · rw [hquery]
      exact (bank_cleanRun Ms As sb hMs cs.dec _).mono (hB cs.dec i hiv)
  obtain ⟨T, hT, hSpace⟩ := compile_space (prog M) (start M) (bankTM Ms) (bankStart Ms)
    oracle (lo M (M.tm.spaceUsed (M.tm.initCfg v) t))
    (hi M (M.tm.spaceUsed (M.tm.initCfg v) t) (Nat.bits (v.length + 1)).length)
    B N w hN (hOut.trans hout) hBox hc
  refine ⟨T, hT, hSpace.trans_eq ?_⟩
  rw [Fin.sum_univ_castSucc]
  simp only [lo, hi, Fin.lastCases_castSucc, Fin.lastCases_last, Finset.sum_const,
    Finset.card_univ, Fintype.card_fin, smul_eq_mul]
  congr 2; (try congr 1); omega

end LogProg.OIS

/-- **Logspace preimages along implicitly logspace computable maps are logspace**
(phase P4.4b; proved): if `f` is implicitly logspace computable and `C ∈ L`, then
`{x | f x ∈ C} ∈ L`. [AB09, Lemma 4.17(2), in preimage form; its proof's Fig. 4.3] It is stated,
and will be proved, as a corollary of `Complexity.LogProg.OIS.compile_decides`.

**Proof sketch.** Unpack `f`'s bound `C₀ (|x| + 1)^e` and its two deciders (spaces `c₀`,
`c₁` times `logSpace`), and `C`'s decider `M` (space `c · logSpace`). For each `x`, take the
time `t` of `M` on `v := f x`, and apply `OIS.compile_decides` with:

* the bank `![length decider, bit decider]`;
* the laws `pairEncode_mem_indexLang`;
* `B := (c₀ + c₁) · logSpace (2|x| + 2 + |bits (|f x| + 1)|) + 1`.

The indicator `[f x ∈ C]` is `[x ∈ {x | f x ∈ C}]`. The bound is `O(logSpace |x|)`:
`logSpace |f x|` and `|bits (|f x| + 1)|` are at most `K · logSpace |x|` by
`LogProg.log_poly_bound`, since `|f x| ≤ C₀ (|x| + 1)^e`. The arithmetic follows
`ImplicitlyLogspaceComputable.computesInSpace`. -/
theorem mem_LOGSPACE_preimage {f : List Bool → List Bool} (hf : ImplicitlyLogspaceComputable f)
    {C : Language Bool} (hC : C ∈ LOGSPACE) : ({x | f x ∈ C} : Language Bool) ∈ LOGSPACE := by
  classical
  obtain ⟨⟨A, e, hlen⟩, ⟨cb, Mb, hb⟩, ⟨cl, Ml, hl⟩⟩ := hf
  obtain ⟨c, M, hM⟩ := hC
  let Ms : Fin 2 → FinTM Bool := ![Ml, Mb]
  let As : Fin 2 → Language Bool :=
    ![indexLang (fun x i => i < (f x).length),
      indexLang (fun x i => (f x).getD i false = true)]
  let sb : Fin 2 → ℕ → ℕ := ![fun n => cl * logSpace n, fun n => cb * logSpace n]
  have hMs : ∀ j, (Ms j).DecidesInSpace (As j) (sb j) := by
    intro j
    refine Fin.cases ?_ (Fin.cases ?_ (fun i => Fin.elim0 i)) j
    · exact hl
    · exact hb
  obtain ⟨K, hK⟩ := LogProg.log_poly_bound A e 1
  obtain ⟨J, hJ⟩ := LogProg.log_poly_bound (A + 2) (e + 1) 2
  let D := LogProg.bankK Ms + LogProg.bankK Ms
  refine ⟨M.k * (2 * (c * K) + 1) + (K + 2) + D * (2 * ((cl + cb) * J + 1) + 1),
    LogProg.compileFinTM (LogProg.OIS.prog M) (LogProg.OIS.start M)
      (LogProg.bankTM Ms) (LogProg.bankStart Ms), fun x => ?_⟩
  obtain ⟨t, ht, hs⟩ := hM (f x)
  let W := (Nat.bits ((f x).length + 1)).length
  let B := (cl + cb) * logSpace (2 * x.length + 2 + W) + 1
  have hbudget : ∀ j, ∀ i ≤ (f x).length,
      max (sb j (pairEncode x (Nat.bits i)).length) 1 ≤ B := by
    intro j i hi
    have hquery : (pairEncode x (Nat.bits i)).length ≤ 2 * x.length + 2 + W := by
      rw [length_pairEncode]
      have hw : (Nat.bits i).length ≤ W := LogProg.length_bits_mono (by omega)
      omega
    have hmono := logSpace_mono hquery
    have hcoef : sb j (pairEncode x (Nat.bits i)).length ≤
        (cl + cb) * logSpace (2 * x.length + 2 + W) := by
      refine Fin.cases ?_ (Fin.cases ?_ (fun i => Fin.elim0 i)) j
      · exact Nat.mul_le_mul (Nat.le_add_right cl cb) hmono
      · exact Nat.mul_le_mul (Nat.le_add_left cb cl) hmono
    dsimp [B]
    omega
  obtain ⟨T, hT, hSpace⟩ := LogProg.OIS.compile_decides M Ms As sb hMs x (f x)
    [MultiTapeTM.indicator C (f x)]
    (fun i _ => pairEncode_mem_indexLang _ x i)
    (fun i _ => pairEncode_mem_indexLang _ x i) t ht B hbudget
  refine ⟨T, hT, hSpace.trans ?_⟩
  let L := logSpace x.length
  have hL : 1 ≤ L := by simp [L, logSpace]
  have hlog : logSpace (f x).length ≤ K * L := by
    have hm := Nat.log_mono_right (b := 2) (show (f x).length ≤ A * (x.length + 1) ^ e + 1 by
      have := hlen x; omega)
    have hk := hK x.length
    dsimp [L, logSpace]
    omega
  have hW : W ≤ K * L := by
    have hw := LogProg.length_bits_le_log ((f x).length + 1)
    have hm := Nat.log_mono_right (b := 2) (Nat.add_le_add_right (hlen x) 1)
    have hk := hK x.length
    dsimp [W, L, logSpace] at *
    omega
  have hJx : logSpace (2 * x.length + 2 + W) ≤ J * L := by
    have hw : W ≤ (f x).length + 2 :=
      (LogProg.length_bits_le_log _).trans (by have := Nat.log_le_self 2 ((f x).length + 1); omega)
    have hp : x.length + 1 ≤ (x.length + 1) ^ (e + 1) := by
      simpa only [pow_one] using
        Nat.pow_le_pow_right (show 1 ≤ x.length + 1 by omega) (show 1 ≤ e + 1 by omega)
    have he : (x.length + 1) ^ e ≤ (x.length + 1) ^ (e + 1) :=
      Nat.pow_le_pow_right (by omega) (by omega)
    have hpoly := (hlen x).trans (Nat.mul_le_mul_left A he)
    have harg : 2 * x.length + 2 + W ≤ (A + 2) * (x.length + 1) ^ (e + 1) + 2 := by
      rw [Nat.add_mul]
      omega
    exact (logSpace_mono harg).trans (hJ x.length)
  have hsrc : M.tm.spaceUsed (M.tm.initCfg (f x)) t ≤ c * K * L := by
    exact hs.trans (by simpa only [Nat.mul_assoc] using Nat.mul_le_mul_left c hlog)
  have hbank : 2 * B + 1 ≤ (2 * ((cl + cb) * J + 1) + 1) * L := by
    have hm := Nat.mul_le_mul_left (cl + cb) hJx
    have he : (2 * ((cl + cb) * J + 1) + 1) * L =
        2 * ((cl + cb) * (J * L)) + 3 * L := by ring
    rw [he]
    dsimp only [B]
    omega
  have hsource : 2 * M.tm.spaceUsed (M.tm.initCfg (f x)) t + 1 ≤
      (2 * (c * K) + 1) * L := by
    have he : (2 * (c * K) + 1) * L = 2 * (c * K * L) + L := by ring
    rw [he]
    omega
  calc
    M.k * (2 * M.tm.spaceUsed (M.tm.initCfg (f x)) t + 1) + (W + 2) + D * (2 * B + 1)
        ≤ M.k * ((2 * (c * K) + 1) * L) + ((K + 2) * L) +
            D * ((2 * ((cl + cb) * J + 1) + 1) * L) := by
          apply Nat.add_le_add
          · apply Nat.add_le_add (Nat.mul_le_mul_left M.k hsource)
            rw [Nat.add_mul]; omega
          · exact Nat.mul_le_mul_left D hbank
    _ = _ := by ring

end Complexity
