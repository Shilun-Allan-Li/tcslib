/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TCSlib contributors
-/
import TCSlib.Complexity.Randomized.PPT
import TCSlib.Cryptography.Foundations.Experiments
import TCSlib.Cryptography.HardcoreBit.Basic
import TCSlib.Cryptography.Foundations.BitLists

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Machines as adversaries of the concrete experiments

The bridge between the machine layer (`Complexity.NUPPT`, strings `List Bool`) and the
concrete security experiments of `TCSlib.Cryptography.Foundations.Experiments` (typed
inputs `Fin m → Bool`, adversaries as functions of the input and of a uniform coin string).
An `NUPPT` `A` activated at parameter `n` becomes

* an *inverter* `A.inverter n ℓ m : (Fin m → Bool) → A.Coins n → Option (Fin ℓ → Bool)`
  [PS10, Definitions 27.3, 28.4]: `A(1^n, y)` with the output decoded as an `ℓ`-bit string;
* its literal variant `A.inverterLit ℓ m` for [PS10, Definition 26.1] (`A(f(x))`, activation
  at the input length `m`, no `1^n`);
* a *distinguisher* / *predictor* `A.distinguisher n m`, `A.predictor n m`
  [PS10, Definitions 69.4, 75.2, 78.3]: `A(1^n, t) = 1`, i.e. the output is the string `[true]`;
  `A.distinguisherL n` takes an untyped sample.

Inversion with a possibly failing decoder is `invProbOpt` (the probability that the decoded
output is a preimage); it is bridged to the concrete `invProb` by `invProbOpt_le_invProb`
(any default for a failure can only increase the probability) and `invProbOpt_some` (a total
inverter has the same probability). Foundation decision D5: inverses are sought in the
domain at the current parameter, and a wrong-length output counts as failure.

The file also records that "computes `f` with probability one" [PS10, Definition 24.6]
is, on the finite uniform coin space, the same as "for every coin string"
(`Complexity.NUPPT.computes_iff_uprob`), which justifies the frozen form of
`Complexity.NUPPT.Computes`.

**Deviation:** `inverter`: wrong-length output = failure (D5); verdict `= [true]` (normalisable
by `ifEq`).

## Main definitions

* `TCSlib.Cryptography.coinBlock` — the common indexed coin-tape segment.
* `TCSlib.Cryptography.decodeFin` — decode a string as an `ℓ`-bit string, failure on a wrong
  length; `TCSlib.Cryptography.padFin` — pad/truncate (for samplers).
* `TCSlib.Cryptography.blocksEquivX`, `TCSlib.Cryptography.FunFamily.blocks` — the canonical
  block bijection `(Fin (q·ℓ) → X) ≃ (Fin q → Fin ℓ → X)` and its Bool form, with the readers
  `blocksEquivX_apply`, `blocksEquivX_symm_apply`, `FunFamily.blocks_apply`,
  `FunFamily.blocks_symm_apply`.
* `Complexity.NUPPT.inverter`, `Complexity.NUPPT.inverterLit` — an `NUPPT` as an inverter
  (with `1^n`, and literal).
* `Complexity.NUPPT.distinguisher`, `Complexity.NUPPT.distinguisherL`,
  `Complexity.NUPPT.predictor` — an `NUPPT` as a distinguisher / predictor.
* `TCSlib.Cryptography.invProbOpt` — inversion probability of a possibly failing inverter.

## Main results

* `TCSlib.Cryptography.coinBlock_eq`, `TCSlib.Cryptography.length_coinBlock` — the segment
  equation and its full-length condition; `coinBlock_flatten`, `map_coinBlock_flatten`,
  `coinBlock_flatten_append` — the segments of a concatenation of equal-length blocks;
  `ofFn_block_eq_coinBlock` — block `i` of a string of blocks and a tail is segment `i`.
* `TCSlib.Cryptography.decodeFin_ofFn`, `TCSlib.Cryptography.padFin_ofFn` — decoding and
  padding invert `List.ofFn`; `TCSlib.Cryptography.decodeFin_eq_some_iff` — decoding succeeds
  exactly on the encoding; `TCSlib.Cryptography.ofFn_padFin_of_length` — padding a string of the
  right length keeps it.
* `TCSlib.Cryptography.ofFn_cast`, `TCSlib.Cryptography.ofFn_arrowCongr_finCongr` — a bit vector
  read across an equality of widths keeps its string.
* `TCSlib.Cryptography.FunFamily.ofFn_blocks` — block `j` of a string is its `j`-th window.
* `TCSlib.Cryptography.invProbOpt_le_invProb`, `TCSlib.Cryptography.invProbOpt_some` — the
  bridges to the concrete `invProb`.
* `TCSlib.Cryptography.invProbOpt_nonneg`, `TCSlib.Cryptography.invProbOpt_le_one` — bounds.
* `Complexity.NUPPT.computes_iff_uprob` — probability one is every coin string
  [PS10, Definition 24.6].

## References

* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed., January 2010.
  (§2.1–2.2: Definitions 24.6, 26.1, 27.3; §3.1–3.3: Definitions 69.4, 75.2, 78.3.)
* [Gar26] S. Garg, *A Course in Theory of Cryptography*, lecture notes, UC Berkeley,
  draft of 22 January 2026, Definitions 2.1, 2.3, 3.2–3.4 (the concrete experiments).
-/

namespace TCSlib.Cryptography

open Complexity Turing Finset

/-! Seal A (dl-folds, final): a verbatim copy of `TCSlib/Cryptography/Asymptotic/Adversary.lean`, with every seal candidate of its
full TCSlib import closure (193 definitions, `PolyExpr.eval` exempt) irreducible from here on. -/
attribute [local irreducible] _root_.Complexity.NUPPT.Computes _root_.Complexity.NUPPT.Uniform _root_.Complexity.NUPPT.advInput _root_.Complexity.NUPPT.adviceLen _root_.Complexity.NUPPT.coinLen _root_.Complexity.NUPPT.coinsCongr _root_.Complexity.NUPPT.coinsEquivPoly _root_.Complexity.NUPPT.coinsEquiv_ofPolyTime _root_.Complexity.NUPPT.coinsEquiv_ofPolyTimeUniform _root_.Complexity.NUPPT.ofPolyTime _root_.Complexity.NUPPT.ofPolyTimeUniform _root_.Complexity.NUPPT.output _root_.Complexity.NUPPT.runAt _root_.Complexity.NUPPT.runAtL _root_.Complexity.NUPPT.runLit _root_.Complexity.NUPPT.timeBound _root_.Complexity.PPT _root_.Complexity.PPT.ofPolyTime _root_.Complexity.PPT.toNUPPT _root_.Complexity.PolyBound _root_.Complexity.PolyExpr.eval.match_1 _root_.Complexity.PolyExpr.normal _root_.Complexity.PolyExpr.subst _root_.Complexity.PolyExpr.subst.match_1 _root_.Complexity.PolyTimeComputable _root_.Complexity.TimeConstructible _root_.Complexity.instDecidableEqPolyExpr.decEq _root_.Complexity.instDecidableEqPolyExpr.decEq.match_1 _root_.Complexity.instReprPolyExpr.repr _root_.Complexity.instReprPolyExpr.repr.match_1 _root_.Complexity.pairFstD _root_.Complexity.pairMapSnd _root_.Complexity.pairMapSnd.match_1 _root_.Complexity.pairSndD _root_.Complexity.polyTimeComputable_unary.match_1_1 _root_.TCSlib.Cryptography.HardcoreBit.PushesUniform _root_.TCSlib.Cryptography.acceptProb _root_.TCSlib.Cryptography.distAdv _root_.TCSlib.Cryptography.invProb _root_.TCSlib.Cryptography.predProb _root_.TCSlib.Cryptography.uexp _root_.TCSlib.Cryptography.uprob _root_.TCSlib.Cryptography.xorPerm _root_.TCSlib.InformationTheory.FinDist.HasMinEntropy _root_.TCSlib.InformationTheory.FinDist.collision _root_.TCSlib.InformationTheory.FinDist.map _root_.TCSlib.InformationTheory.FinDist.probTrue _root_.TCSlib.InformationTheory.FinDist.prod _root_.TCSlib.InformationTheory.FinDist.uniform _root_.TCSlib.InformationTheory.statDist _root_.Turing.Action.apply _root_.Turing.Action.apply.match_1 _root_.Turing.Action.mapState _root_.Turing.Cfg.ext.match_1 _root_.Turing.Cfg.init _root_.Turing.Cfg.inputSymbol _root_.Turing.Cfg.mapState _root_.Turing.Cfg.ofWords _root_.Turing.Cfg.select _root_.Turing.Cfg.workTapeSymbols _root_.Turing.CodeTM.serialize _root_.Turing.CodeTM.toFinTM _root_.Turing.FinTM.Computes _root_.Turing.FinTM.ComputesFunInTime _root_.Turing.FinTM.ComputesFunInTimeVia _root_.Turing.FinTM.ComputesInTime _root_.Turing.FinTM.VirtualTag _root_.Turing.FinTM.appendBitTM _root_.Turing.FinTM.branchTM _root_.Turing.FinTM.branchTM.match_1 _root_.Turing.FinTM.bufferTape _root_.Turing.FinTM.bufferedCompTM _root_.Turing.FinTM.bufferedCompTM.match_1 _root_.Turing.FinTM.bufferedFirstCfg _root_.Turing.FinTM.bufferedScanCfg _root_.Turing.FinTM.bufferedSecondCfg _root_.Turing.FinTM.callEntry _root_.Turing.FinTM.callExit _root_.Turing.FinTM.callTM _root_.Turing.FinTM.callTM.match_1 _root_.Turing.FinTM.condTM _root_.Turing.FinTM.condTM.match_1 _root_.Turing.FinTM.constTM _root_.Turing.FinTM.controlAction _root_.Turing.FinTM.emitAction _root_.Turing.FinTM.idTM _root_.Turing.FinTM.idTM.match_1 _root_.Turing.FinTM.ifEqTM _root_.Turing.FinTM.ifEqTM.match_1 _root_.Turing.FinTM.incFixedTM _root_.Turing.FinTM.incFixedTM.match_1 _root_.Turing.FinTM.incFixedTM.match_3 _root_.Turing.FinTM.indexedVisit _root_.Turing.FinTM.leftAction _root_.Turing.FinTM.leftCfg _root_.Turing.FinTM.lengthBitsTM _root_.Turing.FinTM.lengthBitsTM.match_1 _root_.Turing.FinTM.pairExtractTM _root_.Turing.FinTM.pairExtractTM.match_1 _root_.Turing.FinTM.pairExtractTM.match_3 _root_.Turing.FinTM.pairExtractTM.match_5 _root_.Turing.FinTM.pairLenCheckTM _root_.Turing.FinTM.pairValidTM _root_.Turing.FinTM.pairValidTM.match_1 _root_.Turing.FinTM.polyBitsTM _root_.Turing.FinTM.polyUnaryTM _root_.Turing.FinTM.polyUnaryTM.match_1 _root_.Turing.FinTM.prependTM _root_.Turing.FinTM.prependTM.match_1 _root_.Turing.FinTM.redirectTM _root_.Turing.FinTM.redirectTM.match_1 _root_.Turing.FinTM.redirectTM.match_3 _root_.Turing.FinTM.rewind_scan.match_1 _root_.Turing.FinTM.rightAction _root_.Turing.FinTM.rightCfg _root_.Turing.FinTM.splitSolveTM _root_.Turing.FinTM.splitSolveWithTM _root_.Turing.FinTM.stripLastTM _root_.Turing.FinTM.stripLastTM_computes.match_1 _root_.Turing.FinTM.sweepAct _root_.Turing.FinTM.sweepCfg _root_.Turing.FinTM.sweepFold _root_.Turing.FinTM.sweepFold.match_1 _root_.Turing.FinTM.sweepRevCfg _root_.Turing.FinTM.sweepTape _root_.Turing.FinTM.tapeBlocks _root_.Turing.FinTM.timedCondTM _root_.Turing.FinTM.timedCondTM.match_1 _root_.Turing.FinTM.toCodeTM _root_.Turing.FinTM.toCodeTM.match_1 _root_.Turing.FinTM.unaryTokenTM _root_.Turing.FinTM.unaryTokenTM.match_1 _root_.Turing.FinTM.virtualMove _root_.Turing.FinTM.virtualNextTag _root_.Turing.FinTM.virtualNextTag.match_1 _root_.Turing.MultiTapeTM.AgreeOn _root_.Turing.MultiTapeTM.ComputableInTimeAndSpace _root_.Turing.MultiTapeTM.ComputesFunInTimeAndSpace _root_.Turing.MultiTapeTM.ComputesInTimeAndSpace _root_.Turing.MultiTapeTM.DecidableInTimeAndSpace _root_.Turing.MultiTapeTM.haltsAtStep _root_.Turing.MultiTapeTM.indicator _root_.Turing.MultiTapeTM.initCfg _root_.Turing.MultiTapeTM.outputSymbol _root_.Turing.MultiTapeTM.relabelState _root_.Turing.MultiTapeTM.runFrom _root_.Turing.MultiTapeTM.spaceUsed _root_.Turing.MultiTapeTM.spaceUsedByTape _root_.Turing.MultiTapeTM.step _root_.Turing.MultiTapeTM.step.match_1 _root_.Turing.MultiTapeTM.visitedByTapeHead _root_.Turing.actionBits _root_.Turing.captureAction _root_.Turing.captureAction.match_1 _root_.Turing.captureCfg _root_.Turing.dbl _root_.Turing.embedEmitCfg _root_.Turing.embedEmitRetTM _root_.Turing.embedEmitTM _root_.Turing.embedSilentCfg _root_.Turing.embedSilentRetTM _root_.Turing.embedSilentRetTM.match_1 _root_.Turing.embedSilentTM _root_.Turing.emitAction _root_.Turing.emitCfg _root_.Turing.incFixed _root_.Turing.incFixed.match_1 _root_.Turing.instInhabitedCfg.default _root_.Turing.moveInputPos _root_.Turing.optBoolBits _root_.Turing.optBoolBits.match_1 _root_.Turing.optOptBoolBits _root_.Turing.optOptBoolBits.match_1 _root_.Turing.optStateBits _root_.Turing.optStateBits.match_1 _root_.Turing.pairDecode _root_.Turing.pairDecode.match_1 _root_.Turing.pairDiagTM _root_.Turing.pairDiagTM.match_1 _root_.Turing.pairDiagTM.match_3 _root_.Turing.pairEncode _root_.Turing.signBits _root_.Turing.signBits.match_1 _root_.Turing.solveSplit _root_.Turing.solveSplitWith _root_.Turing.spaceUsedOfCfgs _root_.Turing.splitAtLastTrue _root_.Turing.splitAtLastTrue.match_1 _root_.Turing.stateWord _root_.Turing.unaryFin _root_.Turing.unaryTokenSplit _root_.Turing.unaryTokenSplit.match_1 _root_.Turing.visitedOfCfgs


/-- The `i`-th segment of `B` bits of a coin string; a short final segment is truncated. -/
def coinBlock (B i : ℕ) (r : List Bool) : List Bool := (r.drop (i * B)).take B

/-- The defining equation of `coinBlock`: `coinBlock B i r = (r.drop (i·B)).take B`. -/
theorem coinBlock_eq (B i : ℕ) (r : List Bool) : coinBlock B i r = (r.drop (i * B)).take B := rfl

/-- A coin segment has exactly `B` bits when its end lies within the input tape. -/
theorem length_coinBlock {B i : ℕ} {r : List Bool} (h : (i + 1) * B ≤ r.length) :
    (coinBlock B i r).length = B := by
  simp only [coinBlock_eq, List.length_take, List.length_drop]
  rw [Nat.add_mul, Nat.one_mul] at h
  omega

/-- **The blocks of a concatenation of `B`-bit blocks:** if every block of `l` has `B` bits,
segment `i < |l|` of `l.flatten` is `l[i]`.

**Proof sketch.** Induction on `l`: segment `0` is the first block (`List.take_left'`), and
segment `i + 1` drops the first block (`List.drop_append`) and is segment `i` of the rest. -/
theorem coinBlock_flatten {B : ℕ} : ∀ (l : List (List Bool)), (∀ c ∈ l, c.length = B) →
    ∀ (i : ℕ) (hi : i < l.length), coinBlock B i l.flatten = l[i]
  | [], _, _, hi => by simp at hi
  | c :: cs, hl, 0, _ => by
    have hc : c.length = B := hl c (by simp)
    simp [coinBlock_eq, ← hc]
  | c :: cs, hl, i + 1, hi => by
    have hc : c.length = B := hl c (by simp)
    have hrest := coinBlock_flatten cs (fun d hd => hl d (by simp [hd])) i (by simpa using hi)
    simp only [List.getElem_cons_succ, ← hrest, coinBlock_eq, List.flatten_cons]
    rw [show (i + 1) * B = c.length + i * B by rw [hc, Nat.succ_mul]; ring, List.drop_append,
      List.drop_eq_nil_of_le (by omega), List.nil_append, Nat.add_sub_cancel_left]

/-- **The blocks of a concatenation, mapped:** if every block of `cs` has `k` bits, mapping `F`
over the segments `coinBlock k i cs.flatten` for `i < |cs|` is mapping `F` over `cs`
(`coinBlock_flatten`, entry by entry). -/
theorem map_coinBlock_flatten {α : Type} (k : ℕ) (F : List Bool → α) :
    ∀ cs : List (List Bool), (∀ c ∈ cs, c.length = k) →
      (List.range cs.length).map (fun i => F (coinBlock k i cs.flatten)) = cs.map F := by
  intro cs hc
  refine List.ext_getElem (by rw [List.length_map, List.length_range, List.length_map])
    fun i h₁ h₂ => ?_
  rw [List.getElem_map, List.getElem_range, List.getElem_map,
    coinBlock_flatten cs hc i (by rw [List.length_map, List.length_range] at h₁; exact h₁)]

/-- **Reading back the blocks before a tail:** if `g 0, …, g (r-1)` have `k` bits each, segment
`i < r` of `g 0 ++ ⋯ ++ g (r-1) ++ t` is `g i`.

**Proof sketch.** Induction on `r`: for `i < r` the last block and the tail form the new tail;
for `i = r` the segment starts right after the first `r·k` bits (`length_flatten_map_range`). -/
theorem coinBlock_flatten_append (k r : ℕ) (g : ℕ → List Bool) (hg : ∀ i < r, (g i).length = k)
    (t : List Bool) (i : ℕ) (hi : i < r) :
    coinBlock k i (((List.range r).map g).flatten ++ t) = g i := by
  induction r generalizing t with
  | zero => exact absurd hi (Nat.not_lt_zero _)
  | succ r ih =>
    rw [List.range_succ, List.map_append, List.flatten_append, List.map_singleton,
      List.flatten_singleton, List.append_assoc]
    by_cases h : i < r
    · exact ih (fun j hj => hg j (by omega)) _ h
    · have hir : i = r := by omega
      subst hir
      rw [coinBlock_eq, List.drop_append_of_le_length (by
          rw [length_flatten_map_range k i g fun j hj => hg j (by omega)]),
        List.drop_of_length_le (by rw [length_flatten_map_range k i g fun j hj => hg j (by omega)]),
        List.nil_append, List.take_left' (hg i (by omega))]

/-- Decode a string as an `ℓ`-bit string: `some` of its bits if the length is exactly `ℓ`,
`none` otherwise (a wrong-length answer of an inverter is a failure, D5). -/
def decodeFin (ℓ : ℕ) (w : List Bool) : Option (Fin ℓ → Bool) :=
  if h : w.length = ℓ then some (fun i => w.get (Fin.cast h.symm i)) else none

/-- The defining equation of `decodeFin`: `decodeFin ℓ w` is `some` of the bits of `w` when
`|w| = ℓ`, and `none` otherwise. -/
theorem decodeFin_eq (ℓ : ℕ) (w : List Bool) :
    decodeFin ℓ w = if h : w.length = ℓ then some (fun i => w.get (Fin.cast h.symm i)) else none :=
  rfl

/-- Pad with `false` or truncate a string to exactly `ℓ` bits (the output convention of
samplers, where no failure is possible). -/
def padFin (ℓ : ℕ) (w : List Bool) : Fin ℓ → Bool := fun i => w.getD i false

/-- The defining equation of `padFin`: `padFin ℓ w = fun i => w.getD i false`. -/
theorem padFin_def (ℓ : ℕ) (w : List Bool) :
    padFin ℓ w =
      (fun i => w.getD i false :
        Fin ℓ → Bool) := rfl

/-- Bit `i` of `padFin ℓ w` is bit `i` of `w`, default `false`. -/
theorem padFin_apply (ℓ : ℕ) (w : List Bool) (i : Fin ℓ) : padFin ℓ w i = w.getD i false :=
  rfl

/-- Decoding the encoding of an `ℓ`-bit string returns it. -/
theorem decodeFin_ofFn {ℓ : ℕ} (x : Fin ℓ → Bool) : decodeFin ℓ (List.ofFn x) = some x := by
  simp [decodeFin]

/-- A decoded string has exactly the decoded length. -/
theorem length_eq_of_decodeFin_eq_some {ℓ : ℕ} {w : List Bool} {x : Fin ℓ → Bool}
    (h : decodeFin ℓ w = some x) : w.length = ℓ := by
  by_contra hw
  simp [decodeFin, hw] at h

/-- **Decoding succeeds exactly on the encoding**: `decodeFin ℓ w = some x ↔ w = List.ofFn x`,
for every width `ℓ` (`ℓ = 0` included) and every string `w`.

**Proof sketch.** A successful decoding has `|w| = ℓ` (`length_eq_of_decodeFin_eq_some`); after
substituting the width, `w = List.ofFn (w.get ·)` (`List.ofFn_get`) decodes to the bits of `w`
(`decodeFin_ofFn`), which are therefore `x`. Conversely `decodeFin_ofFn`. -/
theorem decodeFin_eq_some_iff (ℓ : ℕ) (w : List Bool) (x : Fin ℓ → Bool) :
    decodeFin ℓ w = some x ↔ w = List.ofFn x := by
  constructor
  · intro h
    have hw := length_eq_of_decodeFin_eq_some h
    subst hw
    have h' := decodeFin_ofFn (fun j : Fin w.length => w.get j)
    rw [List.ofFn_get, h, Option.some.injEq] at h'
    rw [h']
    exact (List.ofFn_get w).symm
  · rintro rfl
    exact decodeFin_ofFn x

/-- Padding the encoding of an `ℓ`-bit string returns it. -/
theorem padFin_ofFn {ℓ : ℕ} (x : Fin ℓ → Bool) : padFin ℓ (List.ofFn x) = x := by
  funext i
  simp [padFin]

/-- The encoding of `padFin L w` is `w` when `|w| = L`: `List.ofFn (padFin L w) = w`. -/
theorem ofFn_padFin_of_length {L : ℕ} {w : List Bool} (hw : w.length = L) :
    List.ofFn (padFin L w) = w := by
  refine List.ext_getElem (by simp [hw]) fun j hj₁ hj₂ => ?_
  simp [padFin_def, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj₂]

/-! ### Bit vectors across equal widths -/

/-- Reading a bit vector across an equality of widths keeps its string:
`⟦cast h f⟧ = ⟦f⟧` when `a = b`. -/
theorem ofFn_cast {a b : ℕ} (hab : a = b) (h : (Fin a → Bool) = (Fin b → Bool))
    (f : Fin a → Bool) : List.ofFn (cast h f) = List.ofFn f := by
  subst hab
  rfl

/-- Reading a vector at an equal width keeps its word:
`⟦(arrowCongr (finCongr h) (refl Bool)) v⟧ = ⟦v⟧`. -/
theorem ofFn_arrowCongr_finCongr {a b : ℕ} (h : a = b) (v : Fin a → Bool) :
    List.ofFn ((Equiv.arrowCongr (finCongr h) (Equiv.refl Bool)) v) = List.ofFn v := by
  subst h
  rfl

/-! ### Blocks of a flat tuple -/

/-- A tuple of `q · ℓ` entries with values in an arbitrary type `X` as `q` consecutive blocks of
`ℓ` entries: block `i`, position `j` is entry `finProdFinEquiv (i, j) = j + ℓ·i` (Mathlib's
`finProdFinEquiv` and `Equiv.curry`). All `q`, `ℓ` (zero included). -/
def blocksEquivX (q ℓ : ℕ) (X : Type*) : (Fin (q * ℓ) → X) ≃ (Fin q → Fin ℓ → X) :=
  (Equiv.arrowCongr finProdFinEquiv.symm (Equiv.refl X)).trans (Equiv.curry _ _ _)

/-- The forward reader of `blocksEquivX`: block `i`, position `j` of `x` is entry
`finProdFinEquiv (i, j)` of `x`. -/
theorem blocksEquivX_apply (q ℓ : ℕ) {X : Type*} (x : Fin (q * ℓ) → X) (i : Fin q) (j : Fin ℓ) :
    blocksEquivX q ℓ X x i j = x (finProdFinEquiv (i, j)) := rfl

/-- The inverse of `blocksEquivX` reads block `p.divNat`, position `p.modNat`. -/
theorem blocksEquivX_symm_apply (q ℓ : ℕ) {X : Type*} (t : Fin q → Fin ℓ → X) (p : Fin (q * ℓ)) :
    (blocksEquivX q ℓ X).symm t p = t p.divNat p.modNat := rfl

/-- A string of `q · ℓ` bits as `q` consecutive blocks of `ℓ` bits (block `i` occupies the
positions `ℓ·i, …, ℓ·i + ℓ - 1`): the encoding of the tuple `(x₁, …, x_q)` of
[PS10, Theorem 35.1] as the `q·ℓ`-bit concatenation; the Bool specialization of
`blocksEquivX`. -/
def FunFamily.blocks (q ℓ : ℕ) : (Fin (q * ℓ) → Bool) ≃ (Fin q → Fin ℓ → Bool) :=
  blocksEquivX q ℓ Bool

/-- The defining equation of `blocks`: block `i`, position `j` is position `ℓ·i + j` of `x`. -/
theorem FunFamily.blocks_apply (q ℓ : ℕ) (x : Fin (q * ℓ) → Bool) (i : Fin q) (j : Fin ℓ) :
    FunFamily.blocks q ℓ x i j = x (finProdFinEquiv (i, j)) :=
  blocksEquivX_apply q ℓ x i j

/-- The inverse of `blocks` reads block `k.divNat`, position `k.modNat`. -/
theorem FunFamily.blocks_symm_apply (q ℓ : ℕ) (t : Fin q → Fin ℓ → Bool) (k : Fin (q * ℓ)) :
    (FunFamily.blocks q ℓ).symm t k = t k.divNat k.modNat :=
  blocksEquivX_symm_apply q ℓ t k

/-- **Block `j` is the `j`-th window of the string:**
`⟦FunFamily.blocks q ℓ ω j⟧ = (⟦ω⟧.drop (j·ℓ)).take ℓ`.

**Proof sketch.** Block `j` ends within the string, `j·ℓ + ℓ ≤ q·ℓ`, so both sides have `ℓ` bits.
Position `k` of block `j` is position `finProdFinEquiv (j, k) = k + ℓ·j` of `ω`
(`FunFamily.blocks_apply`), which is position `k` of the window. -/
theorem FunFamily.ofFn_blocks (q ℓ : ℕ) (ω : Fin (q * ℓ) → Bool) (j : Fin q) :
    List.ofFn (FunFamily.blocks q ℓ ω j) = ((List.ofFn ω).drop (j * ℓ)).take ℓ := by
  have hle : (j : ℕ) * ℓ + ℓ ≤ q * ℓ := by
    have := Nat.mul_le_mul_right ℓ (Nat.succ_le_of_lt j.isLt)
    rw [Nat.succ_mul] at this
    exact this
  refine List.ext_getElem ?_ fun k h₁ h₂ => ?_
  · simp only [List.length_ofFn, List.length_take, List.length_drop]
    omega
  · rw [List.getElem_ofFn, List.getElem_take, List.getElem_drop, List.getElem_ofFn]
    refine (FunFamily.blocks_apply q ℓ ω j ⟨k, _⟩).trans ?_
    congr 1
    refine Fin.ext ?_
    rw [finProdFinEquiv_apply_val]
    show k + ℓ * j = j * ℓ + k
    rw [Nat.mul_comm]
    omega

/-- **Block `i` of a string of `r` blocks of `k` bits and a tail** is segment `i`:
`⟦j ↦ w (castAdd sl (finProdFinEquiv (i, j)))⟧ = coinBlock k i ⟦w⟧`.

**Proof sketch.** The block is block `i` of the first `r·k` bits (`FunFamily.blocks_apply`),
whose word is the window `(⟦w⟧.take (r·k)).drop (i·k)).take k` (`FunFamily.ofFn_blocks`,
`List.ofFn_add`); the tail does not reach the window since `i·k + k ≤ r·k`. -/
theorem ofFn_block_eq_coinBlock {r k sl : ℕ} (w : Fin (r * k + sl) → Bool) (i : Fin r) :
    List.ofFn (fun j : Fin k => w (Fin.castAdd sl (finProdFinEquiv (i, j)))) =
      coinBlock k i (List.ofFn w) := by
  have hle : (i : ℕ) * k + k ≤ r * k := by
    have := Nat.mul_le_mul_right k (Nat.succ_le_of_lt i.isLt)
    rw [Nat.succ_mul] at this
    exact this
  have hblk : (fun j : Fin k => w (Fin.castAdd sl (finProdFinEquiv (i, j)))) =
      FunFamily.blocks r k (fun p => w (Fin.castAdd sl p)) i :=
    funext fun j => (FunFamily.blocks_apply r k (fun p => w (Fin.castAdd sl p)) i j).symm
  have hx : (List.ofFn fun p : Fin (r * k) => w (Fin.castAdd sl p)).length = r * k :=
    List.length_ofFn
  have hw : List.ofFn w = List.ofFn (fun p : Fin (r * k) => w (Fin.castAdd sl p)) ++
      List.ofFn (fun j : Fin sl => w (Fin.natAdd (r * k) j)) := List.ofFn_add
  rw [hblk, FunFamily.ofFn_blocks, coinBlock_eq, hw,
    List.drop_append_of_le_length (by omega), List.take_append_of_le_length (by
      rw [List.length_drop]; omega)]

/-- `A(1^n, y)` as an inverter: output decoded as an `ℓ`-bit string, wrong length = failure
[PS10, Definitions 27.3 and 28.4, the experiment `f(A(1^n, y)) = y`].

**Deviation:** wrong-length output = failure (D5). For a typed family this loses nothing. For
a string function `f : {0,1}* → {0,1}*` the text's experiment also accepts a preimage of
another length, so the typed experiment can count fewer successes and typed one-wayness is
implied by, but weaker than, the text's, unless `|f(x)|` determines `|x|` (length-regular `f`
whose output length is a non-constant `PolyExpr`, hence injective in the input length; with
constant output length neither notion is satisfiable). The proviso is stated where string functions enter the typed world,
`FunFamily.ofString` (`Asymptotic/OneWay.lean`; gate 03a, note 15). -/
def _root_.Complexity.NUPPT.inverter (A : NUPPT) (n ℓ m : ℕ) :
    (Fin m → Bool) → A.Coins n → Option (Fin ℓ → Bool) :=
  fun y r => decodeFin ℓ (A.runAt n (List.ofFn y) r)

/-- The defining equation of `NUPPT.inverter`: the output of `A(1^n, y; r)` decoded as an
`ℓ`-bit string, `A.inverter n ℓ m y r = decodeFin ℓ (A.runAt n (List.ofFn y) r)`. -/
theorem _root_.Complexity.NUPPT.inverter_def (A : NUPPT) (n ℓ m : ℕ) (y : Fin m → Bool)
    (r : A.Coins n) : A.inverter n ℓ m y r = decodeFin ℓ (A.runAt n (List.ofFn y) r) := rfl

/-- The literal inverter `A(y)` of [PS10, Definition 26.1]: activation at parameter `|y| = m`
(the text gives the adversary `f(x)` only; the `1^{|y|}` prefix carries no information). -/
def _root_.Complexity.NUPPT.inverterLit (A : NUPPT) (ℓ m : ℕ) :
    (Fin m → Bool) → A.Coins m → Option (Fin ℓ → Bool) :=
  fun y r => decodeFin ℓ (A.runAt m (List.ofFn y) r)

/-- `A(1^n, t)` as a distinguisher: accepts iff the output is the string `[true]`
[PS10, Definition 69.4]. -/
def _root_.Complexity.NUPPT.distinguisher (A : NUPPT) (n m : ℕ) :
    (Fin m → Bool) → A.Coins n → Bool :=
  fun t r => decide (A.runAt n (List.ofFn t) r = [true])

/-- `A(1^n, w)` as a distinguisher of untyped samples (ciphertexts, views, histories). -/
def _root_.Complexity.NUPPT.distinguisherL (A : NUPPT) (n : ℕ) : List Bool → A.Coins n → Bool :=
  fun w r => decide (A.runAt n w r = [true])

/-- The defining equation of `distinguisherL`:
`A.distinguisherL n w r = decide (A.runAt n w r = [true])`. -/
theorem _root_.Complexity.NUPPT.distinguisherL_eq (A : NUPPT) (n : ℕ) (w : List Bool)
    (r : A.Coins n) : A.distinguisherL n w r = decide (A.runAt n w r = [true]) := rfl

/-- `A(1^n, y)` as a predictor of a bit: the same verdict convention as a distinguisher
[PS10, Definitions 75.2 and 78.3]. -/
def _root_.Complexity.NUPPT.predictor (A : NUPPT) (n m : ℕ) :
    (Fin m → Bool) → A.Coins n → Bool :=
  A.distinguisher n m

/-- The literal inverter is the inverter at parameter `m`. -/
theorem _root_.Complexity.NUPPT.inverterLit_eq (A : NUPPT) (ℓ m : ℕ) :
    A.inverterLit ℓ m = A.inverter m ℓ m := rfl

/-- The typed distinguisher is the untyped one on `List.ofFn t`. -/
theorem _root_.Complexity.NUPPT.distinguisher_eq (A : NUPPT) (n m : ℕ) (t : Fin m → Bool)
    (r : A.Coins n) : A.distinguisher n m t r = A.distinguisherL n (List.ofFn t) r := rfl

/-- The predictor is the distinguisher. -/
theorem _root_.Complexity.NUPPT.predictor_eq (A : NUPPT) (n m : ℕ) :
    A.predictor n m = A.distinguisher n m := rfl

/-- The inverter succeeds on `(y, r)` iff the machine's output is the encoding of some `x'`. -/
theorem _root_.Complexity.NUPPT.inverter_eq_some_iff (A : NUPPT) (n ℓ m : ℕ) (y : Fin m → Bool)
    (r : A.Coins n) (x' : Fin ℓ → Bool) :
    A.inverter n ℓ m y r = some x' ↔ A.runAt n (List.ofFn y) r = List.ofFn x' := by
  constructor
  · intro h
    have hw : (A.runAt n (List.ofFn y) r).length = ℓ := length_eq_of_decodeFin_eq_some h
    simp only [NUPPT.inverter, decodeFin, dif_pos hw, Option.some.injEq] at h
    subst h
    refine List.ext_get (by simp [hw]) fun i h₁ h₂ => ?_
    simp
  · intro h
    show decodeFin ℓ _ = _
    rw [h, decodeFin_ofFn]

/-- The probability that a possibly failing inverter `A`, given `f x` for uniform `x` and
uniform coins, outputs `some x'` with `f x' = f x` (the typed experiment of
[PS10, Definition 27.3] with a wrong-length output counted as failure, D5). -/
noncomputable def invProbOpt {α β ρ : Type*} [Fintype α] [Fintype ρ] (f : α → β)
    (A : β → ρ → Option α) : ℝ :=
  uprob fun z : α × ρ => ∃ x', A (f z.1) z.2 = some x' ∧ f x' = f z.1

/-- The defining equation of `invProbOpt`:
`invProbOpt f A = Pr_{(x, r)}[∃ x', A(f x, r) = some x' ∧ f x' = f x]`, over uniform
`(x, r) ∈ α × ρ`. -/
theorem invProbOpt_def {α β ρ : Type*} [Fintype α] [Fintype ρ] (f : α → β)
    (A : β → ρ → Option α) :
    invProbOpt f A = uprob fun z : α × ρ => ∃ x', A (f z.1) z.2 = some x' ∧ f x' = f z.1 := rfl

/-- Replacing a failure by any default can only increase the inversion probability: the
bridge from `invProbOpt` to the concrete `invProb` [Gar26, Definition 2.1]. -/
theorem invProbOpt_le_invProb {α β ρ : Type*} [Fintype α] [Fintype ρ] [Inhabited α] (f : α → β)
    (A : β → ρ → Option α) :
    invProbOpt f A ≤ invProb f (fun y r => (A y r).getD default) := by
  rw [invProbOpt_def, invProb_def]
  refine uprob_mono ?_
  rintro ⟨x, r⟩ ⟨x', hx', hf⟩
  simp [hx', hf]

/-- A total inverter has the same probability under both conventions. -/
theorem invProbOpt_some {α β ρ : Type*} [Fintype α] [Fintype ρ] (f : α → β) (A : β → ρ → α) :
    invProbOpt f (fun y r => some (A y r)) = invProb f A := by
  unfold invProbOpt
  simp only [invProb_def]
  congr 1
  funext z
  simp

/-- The inversion probability is nonnegative. -/
theorem invProbOpt_nonneg {α β ρ : Type*} [Fintype α] [Fintype ρ] (f : α → β)
    (A : β → ρ → Option α) : 0 ≤ invProbOpt f A :=
  uprob_nonneg _

/-- The inversion probability is at most one. -/
theorem invProbOpt_le_one {α β ρ : Type*} [Fintype α] [Fintype ρ] (f : α → β)
    (A : β → ρ → Option α) : invProbOpt f A ≤ 1 :=
  uprob_le_one _

/-- **"With probability one" is "for every coin string"** [PS10, Definition 24.6]: `A`
computes `f` in the frozen sense (`Complexity.NUPPT.Computes`, equality for every coin
string) iff at every parameter and argument the event `A(1^n, y; r) = f(⟨1^n, y⟩)` has
probability one over the uniform coins. (On a finite uniform space an event of probability
one is the whole space, `HardcoreBit.forall_of_uprob_eq_one`.) -/
theorem _root_.Complexity.NUPPT.computes_iff_uprob (A : NUPPT) (f : List Bool → List Bool) :
    A.Computes f ↔
      ∀ n y, uprob (fun r : A.Coins n => A.runAt n y r = f (NUPPT.advInput n y)) = 1 := by
  rw [NUPPT.computes_iff]
  constructor
  · intro h n y
    have hp : (fun r : A.Coins n => A.runAt n y r = f (NUPPT.advInput n y)) = fun _ => True :=
      funext fun r => propext ⟨fun _ => trivial, fun _ => h n y r⟩
    rw [hp, uprob_true]
  · intro h n y r
    exact HardcoreBit.forall_of_uprob_eq_one (h n y) r

end TCSlib.Cryptography
