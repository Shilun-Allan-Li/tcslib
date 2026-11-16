/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TCSlib.Cryptography.SecureComputation.ComposeSecurity.Machines

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# The composed parties as polynomial-time functions of the machine layout

The efficiency half of the composition theorem [Gol04, §7.3.1, the protocol of Theorem 7.3.3]:
Alice's and Bob's next-message functions in `H.compose ρ` (`HybridProtocol.composeP`,
`composeV`) are polynomial-time functions of the machine layout
`GI.ilayout x z hist r = ⟨⟨⟨1^{|x|}, ⟨⟨x, z⟩, encodeMsgs hist⟩⟩, []⟩, r⟩`, when `main`'s and `ρ`'s
strategies are efficient and the call inputs are polynomial-time (`HybridProtocol.PolyTime`,
`Functionality.PolyTime`).

The pieces are shared by the two parties and generic in the strategies:
* `ComposeMachines.runW`: one activation of a `ρ`-party in run `j` after `p` pairs of the run,
  on the call input (recomputed from the `main`-tape), the run tape cut from the coins and the
  run's messages read from the history at the interleaved pairs (`polyTimeComputable_slots`);
* `ComposeMachines.ansW`: the `L(n)` run outputs, each padded to the answer length, concatenated;
* `ComposeMachines.mainW`: one activation of a `main`-party on its input paired with the answers,
  its `main`-tape and the messages after the runs.

## Main definitions

* `ComposeMachines.runW`, `ansW`, `mainW`, `moverW`: the shared pieces.
* `HybridProtocol.composePW`, `composeVW`: the two parties on the layout.

## Main results

* `ComposeMachines.runW_ilayout`, `ansW_ilayout`, `mainW_ilayout`: the pieces on a layout.
* `ComposeMachines.polyTimeComputable_runW`, `polyTimeComputable_ansW`,
  `polyTimeComputable_mainW`: the pieces are polynomial-time.
* `HybridProtocol.composeP_next_eq_composePW`, `composeV_next_eq_composeVW`: the composed
  parties are the layout functions.
* `HybridProtocol.polyTimeComputable_composePW`, `polyTimeComputable_composeVW`: and these are
  polynomial-time.

## References

* [Gol04] O. Goldreich, *Foundations of Cryptography, Volume 2: Basic Applications*, Cambridge
  University Press, 2004, §7.3.1 (the composed protocol of Theorem 7.3.3).
* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed., January 2010,
  §4.4 (interactive machines and their time complexity, pp. 114–116).
-/

namespace TCSlib.Cryptography.SecureComputation

open Complexity Turing Complexity.StateLoop TCSlib.Cryptography.EncodingMachines

namespace ComposeMachines

/-! ### The mover test -/

/-- **The mover test in unary**: `moverW vF b w = [moverIsV vF |fst w| = b]` (whether the
party moving at position `|fst w|` of `ρ` is the verifier, compared with `b`). -/
def moverW (vF b : Bool) (w : List Bool) : List Bool :=
  [moverIsV vF (pairFstD w).length == b]

/-- The defining equation of `moverW`: `moverW vF b w = [moverIsV vF |fst w| == b]`. -/
theorem moverW_eq (vF b : Bool) (w : List Bool) :
    moverW vF b w = [moverIsV vF (pairFstD w).length == b] := rfl

/-- The mover test is polynomial-time: the parity of the unary length `|fst w|`
(`EncodingMachines.modNum_poly`, `eqTest_poly`), compared with constants
(`Complexity.polyTimeComputable_ite`).
`PolyTimeComputable (moverW vF b)`. -/
theorem polyTimeComputable_moverW (vF b : Bool) : PolyTimeComputable (moverW vF b) := by
  have hpar : PolyTimeComputable fun w =>
      [decide (modNum (pairFstD w).length 2 = (if vF then 0 else 1))] :=
    eqTest_poly (modNum_poly (unaryLength_poly polyTimeComputable_pairFstD) (unaryConst_poly 2))
      (unaryConst_poly _)
  have h := polyTimeComputable_ite hpar (polyTimeComputable_const [b])
    (polyTimeComputable_const [!b])
  refine h.congr fun w => ?_
  rw [moverW_eq, moverIsV_def, modNum_eq]
  rcases Nat.mod_two_eq_zero_or_one (pairFstD w).length with hp | hp <;>
    cases vF <;> cases b <;> simp [hp]

/-! ### One activation of a `ρ`-party in a run -/

/-- **One `ρ`-activation in run `j` after `p` pairs of the run**, on the word
`u = ⟨1^j, ⟨1^p, w⟩⟩` with `w` a layout (common input `x`, input `z`, messages `M`, coins `r`,
`n = |x|`): the `ρ`-party's machine `Fρ` on the layout with common input `x`, input
`fcall ⟨1^n, ⟨z, ⟨r_{<c₀(n)}, 1^j⟩⟩⟩` (the call input from the `main`-tape), the messages
of the run read at the pairs `R(n)·j + q`, `q < p`, selected by `moverIsV vF q = b`, and the run
tape `r[c₀(n) + j·c(n), c₀(n) + (j + 1)·c(n))`. -/
def runW (Fρ fcall : List Bool → List Bool) (c₀ c R : PolyExpr) (vF b : Bool)
    (u : List Bool) : List Bool :=
  Fρ (NUPPT.layout (List.replicate (GI.argX (pairSndD (pairSndD u))).length true)
    (pairEncode (pairEncode (GI.argX (pairSndD (pairSndD u)))
        (fcall (pairEncode (List.replicate (GI.argX (pairSndD (pairSndD u))).length true)
          (pairEncode (GI.argZ (pairSndD (pairSndD u)))
            (pairEncode ((NUPPT.inCoins (pairSndD (pairSndD u))).take
                (c₀.eval (GI.argX (pairSndD (pairSndD u))).length))
              (List.replicate (pairFstD u).length true))))))
      ((List.range (pairFstD (pairSndD u)).length).flatMap fun q =>
        if moverIsV vF q == b then
          pairEncode (pairFstD (pairSndD^[R.eval (GI.argX (pairSndD (pairSndD u))).length *
            (pairFstD u).length + q] (GI.argM (pairSndD (pairSndD u))))) []
        else []))
    []
    (((NUPPT.inCoins (pairSndD (pairSndD u))).drop
        (c₀.eval (GI.argX (pairSndD (pairSndD u))).length +
          (pairFstD u).length * c.eval (GI.argX (pairSndD (pairSndD u))).length)).take
      (c.eval (GI.argX (pairSndD (pairSndD u))).length)))

/-- The defining equation of `runW` (see `runW`).
`runW Fρ fcall c₀ c R vF b u = Fρ (NUPPT.layout (List.replicate (GI.argX (pairSndD (pairSndD
u))).length true) (pairEncode (pairEncode (GI.argX (pairSndD (pairSndD u))) (fcall (pairEncode
(List.replicate (GI.argX (pairSndD (pairSndD u))).length true) (pairEncode (GI.argZ (pairSndD
(pairSndD u))) (pairEncode ((NUPPT.inCoins (pairSndD (pairSndD u))).take (c₀.eval (GI.argX (pairSndD
(pairSndD u))).length)) (List.replicate (pairFstD u).length true)))))) ((List.range (pairFstD
(pairSndD u)).length).flatMap fun q => if moverIsV vF q == b then pairEncode (pairFstD
(pairSndD^[R.eval (GI.argX (pairSndD (pairSndD u))).length * (pairFstD u).length + q] (GI.argM
(pairSndD (pairSndD u))))) [] else [])) [] (((NUPPT.inCoins (pairSndD (pairSndD u))).drop (c₀.eval
(GI.argX (pairSndD (pairSndD u))).length + (pairFstD u).length * c.eval (GI.argX (pairSndD (pairSndD
u))).length)).take (c.eval (GI.argX (pairSndD (pairSndD u))).length)))`. -/
theorem runW_eq (Fρ fcall : List Bool → List Bool) (c₀ c R : PolyExpr) (vF b : Bool)
    (u : List Bool) :
    runW Fρ fcall c₀ c R vF b u =
      Fρ (NUPPT.layout (List.replicate (GI.argX (pairSndD (pairSndD u))).length true)
        (pairEncode (pairEncode (GI.argX (pairSndD (pairSndD u)))
            (fcall (pairEncode (List.replicate (GI.argX (pairSndD (pairSndD u))).length true)
              (pairEncode (GI.argZ (pairSndD (pairSndD u)))
                (pairEncode ((NUPPT.inCoins (pairSndD (pairSndD u))).take
                    (c₀.eval (GI.argX (pairSndD (pairSndD u))).length))
                  (List.replicate (pairFstD u).length true))))))
          ((List.range (pairFstD (pairSndD u)).length).flatMap fun q =>
            if moverIsV vF q == b then
              pairEncode (pairFstD (pairSndD^[R.eval (GI.argX (pairSndD (pairSndD u))).length *
                (pairFstD u).length + q] (GI.argM (pairSndD (pairSndD u))))) []
            else []))
        []
        (((NUPPT.inCoins (pairSndD (pairSndD u))).drop
            (c₀.eval (GI.argX (pairSndD (pairSndD u))).length +
              (pairFstD u).length * c.eval (GI.argX (pairSndD (pairSndD u))).length)).take
          (c.eval (GI.argX (pairSndD (pairSndD u))).length))) := rfl

/-- **`runW` on a layout**: on `⟨1^j, ⟨1^p, GI.ilayout x z hist r⟩⟩` it is `Fρ` on the layout of
the run activation: `runW … ⟨1^j, ⟨1^p, GI.ilayout x z hist r⟩⟩ =
Fρ (GI.ilayout x (fcall ⟨1^{|x|}, ⟨z, ⟨r_{<c₀}, 1^j⟩⟩⟩) (slotMsgs sel (R·j) p hist)
(runTape c₀ c j r))` with `sel q = (moverIsV vF q == b)` (`encodeMsgs_slotMsgs`). -/
theorem runW_ilayout (Fρ fcall : List Bool → List Bool) (c₀ c R : PolyExpr) (vF b : Bool)
    (x z : List Bool) (hist : List (List Bool)) (r : List Bool) (j p : ℕ) :
    runW Fρ fcall c₀ c R vF b (pairEncode (List.replicate j true)
        (pairEncode (List.replicate p true) (GI.ilayout x z hist r))) =
      Fρ (GI.ilayout x (fcall (pairEncode (List.replicate x.length true)
          (pairEncode z (pairEncode (r.take (c₀.eval x.length)) (List.replicate j true)))))
        (Compose.slotMsgs (fun q => moverIsV vF q == b) (R.eval x.length * j) p hist)
        (Compose.runTape (c₀.eval x.length) (c.eval x.length) j r)) := by
  rw [runW_eq, pairSndD_pairEncode, pairSndD_pairEncode, pairFstD_pairEncode,
    pairFstD_pairEncode, List.length_replicate, List.length_replicate, GI.argX_ilayout,
    GI.argZ_ilayout, GI.argM_ilayout, GI.inCoins_ilayout, GI.ilayout_def, encodeMsgs_slotMsgs,
    Compose.runTape_eq]

/-- **`runW` is polynomial-time** when `Fρ` and `fcall` are.
`PolyTimeComputable (runW Fρ fcall c₀ c R vF b)`.

**Proof sketch.** The layout is assembled (`NUPPT.polyTimeComputable_layout`) from the slot
projections, the unary polynomials `c₀(n)`, `c(n)`, `R(n)` (`unaryPoly_comp`), the call input
(`fcall` after `pairEncode`), the typed cuts of the coins (`EncodingMachines.truncate_poly`,
`Complexity.polyTimeComputable_pairDropPoly` at the unary count `c₀(n) + j·c(n)`) and the
interleaved-slot map at the offset `R(n)·j` (`polyTimeComputable_slots`). -/
theorem polyTimeComputable_runW {Fρ fcall : List Bool → List Bool} (hFρ : PolyTimeComputable Fρ)
    (hcall : PolyTimeComputable fcall) (c₀ c R : PolyExpr) (vF b : Bool) :
    PolyTimeComputable (runW Fρ fcall c₀ c R vF b) := by
  have hw : PolyTimeComputable fun u => pairSndD (pairSndD u) :=
    polyTimeComputable_pairSndD.comp' polyTimeComputable_pairSndD
  have hx := GI.argX_poly.comp' hw
  have hn : PolyTimeComputable fun u =>
      List.replicate (GI.argX (pairSndD (pairSndD u))).length true := unaryLength_poly hx
  have hj : PolyTimeComputable fun u => List.replicate (pairFstD u).length true :=
    unaryLength_poly polyTimeComputable_pairFstD
  have hp : PolyTimeComputable fun u => List.replicate (pairFstD (pairSndD u)).length true :=
    unaryLength_poly (polyTimeComputable_pairFstD.comp' polyTimeComputable_pairSndD)
  have hr := NUPPT.polyTimeComputable_inCoins.comp' hw
  have hc₀ := unaryPoly_comp c₀ hx
  have hc := unaryPoly_comp c hx
  have hR := unaryPoly_comp R hx
  have hinp : PolyTimeComputable fun u => fcall (pairEncode
      (List.replicate (GI.argX (pairSndD (pairSndD u))).length true)
      (pairEncode (GI.argZ (pairSndD (pairSndD u)))
        (pairEncode ((NUPPT.inCoins (pairSndD (pairSndD u))).take
            (c₀.eval (GI.argX (pairSndD (pairSndD u))).length))
          (List.replicate (pairFstD u).length true)))) :=
    hcall.comp' (hn.pairEncode ((GI.argZ_poly.comp' hw).pairEncode
      ((truncate_poly hr hc₀).pairEncode hj)))
  have hsel : PolyTimeComputable fun w' => [moverIsV vF (pairFstD w').length == b] :=
    (polyTimeComputable_moverW vF b).congr fun w' => moverW_eq vF b w'
  have hslots := polyTimeComputable_slots (sel := fun _ q => moverIsV vF q == b)
    (off := fun u => R.eval (GI.argX (pairSndD (pairSndD u))).length * (pairFstD u).length)
    (p := fun u => (pairFstD (pairSndD u)).length)
    hsel
    (unaryMul_poly hR hj) hp (GI.argM_poly.comp' hw)
  have hdrop : PolyTimeComputable fun u => (NUPPT.inCoins (pairSndD (pairSndD u))).drop
      (c₀.eval (GI.argX (pairSndD (pairSndD u))).length +
        (pairFstD u).length * c.eval (GI.argX (pairSndD (pairSndD u))).length) :=
    ((polyTimeComputable_pairDropPoly .var).comp'
      ((unaryAdd_poly hc₀ (unaryMul_poly hj hc)).pairEncode hr)).congr fun u => by
        rw [pairFstD_pairEncode, pairSndD_pairEncode, PolyExpr.eval_var,
          List.length_replicate]
  exact (hFρ.comp' (NUPPT.polyTimeComputable_layout hn ((hx.pairEncode hinp).pairEncode hslots)
    (polyTimeComputable_const []) (truncate_poly hdrop hc))).congr fun u => by
      rw [runW_eq]

/-! ### The answers -/

/-- **The answers on the layout**: the `L(n)` run outputs of the `ρ`-party (`runW` with
`p = R(n)`), each padded to `out(n)` bits, concatenated:
`ansW … w = (range L(n)).flatMap fun j => padTo out(n) (runW … ⟨1^j, ⟨1^{R(n)}, w⟩⟩)`. -/
def ansW (Fρ fcall : List Bool → List Bool) (c₀ c R L out : PolyExpr) (vF b : Bool)
    (w : List Bool) : List Bool :=
  (List.range (L.eval (GI.argX w).length)).flatMap fun j =>
    padTo (out.eval (GI.argX w).length) (runW Fρ fcall c₀ c R vF b
      (pairEncode (List.replicate j true)
        (pairEncode (List.replicate (R.eval (GI.argX w).length) true) w)))

/-- The defining equation of `ansW` (see `ansW`).
`ansW Fρ fcall c₀ c R L out vF b w = (List.range (L.eval (GI.argX w).length)).flatMap fun j => padTo
(out.eval (GI.argX w).length) (runW Fρ fcall c₀ c R vF b (pairEncode (List.replicate j true)
(pairEncode (List.replicate (R.eval (GI.argX w).length) true) w)))`. -/
theorem ansW_eq (Fρ fcall : List Bool → List Bool) (c₀ c R L out : PolyExpr) (vF b : Bool)
    (w : List Bool) :
    ansW Fρ fcall c₀ c R L out vF b w =
      (List.range (L.eval (GI.argX w).length)).flatMap fun j =>
        padTo (out.eval (GI.argX w).length) (runW Fρ fcall c₀ c R vF b
          (pairEncode (List.replicate j true)
            (pairEncode (List.replicate (R.eval (GI.argX w).length) true) w))) := rfl

/-- **The answers are polynomial-time** (`polyTimeComputable_flatMap_range` over the unary count
`L(n)`, with the chunk `padTo_poly` of `polyTimeComputable_runW`).
`PolyTimeComputable (ansW Fρ fcall c₀ c R L out vF b)`. -/
theorem polyTimeComputable_ansW {Fρ fcall : List Bool → List Bool} (hFρ : PolyTimeComputable Fρ)
    (hcall : PolyTimeComputable fcall) (c₀ c R L out : PolyExpr) (vF b : Bool) :
    PolyTimeComputable (ansW Fρ fcall c₀ c R L out vF b) := by
  have hw := polyTimeComputable_pairSndD
  have hx := GI.argX_poly.comp' hw
  have hchunk : PolyTimeComputable fun v =>
      padTo (out.eval (GI.argX (pairSndD v)).length) (runW Fρ fcall c₀ c R vF b
        (pairEncode (List.replicate (pairFstD v).length true)
          (pairEncode (List.replicate (R.eval (GI.argX (pairSndD v)).length) true)
            (pairSndD v)))) :=
    padTo_poly ((polyTimeComputable_runW hFρ hcall c₀ c R vF b).comp
      ((unaryLength_poly polyTimeComputable_pairFstD).pairEncode
        ((unaryPoly_comp R hx).pairEncode hw))) (unaryPoly_comp out hx)
  exact (polyTimeComputable_flatMap_range hchunk (unaryPoly_comp L GI.argX_poly)).congr
    fun w => rfl

/-! ### One activation of a `main`-party -/

/-- **One `main`-activation on the layout**: the `main`-party's machine `Fm` on the layout with
common input `x`, input `⟨z, ans w⟩`, the messages after the first `d w` (`pairSndD^[d w] M`)
and the `main`-tape `r_{<c₀(n)}`. -/
def mainW (Fm ans : List Bool → List Bool) (d : List Bool → ℕ) (c₀ : PolyExpr) (w : List Bool) :
    List Bool :=
  Fm (NUPPT.layout (List.replicate (GI.argX w).length true)
    (pairEncode (pairEncode (GI.argX w) (pairEncode (GI.argZ w) (ans w)))
      (pairSndD^[d w] (GI.argM w)))
    [] ((NUPPT.inCoins w).take (c₀.eval (GI.argX w).length)))

/-- The defining equation of `mainW` (see `mainW`).
`mainW Fm ans d c₀ w = Fm (NUPPT.layout (List.replicate (GI.argX w).length true) (pairEncode
(pairEncode (GI.argX w) (pairEncode (GI.argZ w) (ans w))) (pairSndD^[d w] (GI.argM w))) []
((NUPPT.inCoins w).take (c₀.eval (GI.argX w).length)))`. -/
theorem mainW_eq (Fm ans : List Bool → List Bool) (d : List Bool → ℕ) (c₀ : PolyExpr)
    (w : List Bool) :
    mainW Fm ans d c₀ w =
      Fm (NUPPT.layout (List.replicate (GI.argX w).length true)
        (pairEncode (pairEncode (GI.argX w) (pairEncode (GI.argZ w) (ans w)))
          (pairSndD^[d w] (GI.argM w)))
        [] ((NUPPT.inCoins w).take (c₀.eval (GI.argX w).length))) := rfl

/-- **`mainW` on a layout**: `mainW Fm ans d c₀ (GI.ilayout x z hist r) =
Fm (GI.ilayout x ⟨z, ans (GI.ilayout x z hist r)⟩ (hist.drop (d …)) r_{<c₀})`
(`GI.iterate_pairSndD_encodeMsgs`). -/
theorem mainW_ilayout (Fm ans : List Bool → List Bool) (d : List Bool → ℕ) (c₀ : PolyExpr)
    (x z : List Bool) (hist : List (List Bool)) (r : List Bool) :
    mainW Fm ans d c₀ (GI.ilayout x z hist r) =
      Fm (GI.ilayout x (pairEncode z (ans (GI.ilayout x z hist r)))
        (hist.drop (d (GI.ilayout x z hist r))) (r.take (c₀.eval x.length))) := by
  rw [mainW_eq, GI.argX_ilayout, GI.argZ_ilayout, GI.argM_ilayout, GI.inCoins_ilayout,
    GI.iterate_pairSndD_encodeMsgs, GI.ilayout_def, GI.ilayout_def]

/-- **`mainW` is polynomial-time** when `Fm`, the answers and the unary drop count are
(`iterSnd_poly`, `EncodingMachines.truncate_poly`).
`PolyTimeComputable (mainW Fm ans d c₀)`. -/
theorem polyTimeComputable_mainW {Fm ans : List Bool → List Bool} (hFm : PolyTimeComputable Fm)
    (hans : PolyTimeComputable ans) {d : List Bool → ℕ}
    (hd : PolyTimeComputable fun w => List.replicate (d w) true) (c₀ : PolyExpr) :
    PolyTimeComputable (mainW Fm ans d c₀) :=
  (hFm.comp' (NUPPT.polyTimeComputable_layout (unaryLength_poly GI.argX_poly)
    ((GI.argX_poly.pairEncode (GI.argZ_poly.pairEncode hans)).pairEncode
      (iterSnd_poly GI.argM_poly hd))
    (polyTimeComputable_const [])
    (truncate_poly NUPPT.polyTimeComputable_inCoins (unaryPoly_comp c₀ GI.argX_poly)))).congr
    fun w => by rw [mainW_eq]


/-- **`ansW` on a layout**: the concatenation over `j < L(|x|)` of the padded run outputs
`padTo out(|x|) (Fρ (GI.ilayout x (fcall ⟨1^{|x|}, ⟨z, ⟨r_{<c₀}, 1^j⟩⟩⟩)
(slotMsgs sel (R·j) R hist) (runTape c₀ c j r)))` (`runW_ilayout`). -/
theorem ansW_ilayout (Fρ fcall : List Bool → List Bool) (c₀ c R L out : PolyExpr) (vF b : Bool)
    (x z : List Bool) (hist : List (List Bool)) (r : List Bool) :
    ansW Fρ fcall c₀ c R L out vF b (GI.ilayout x z hist r) =
      (List.range (L.eval x.length)).flatMap fun j =>
        padTo (out.eval x.length) (Fρ (GI.ilayout x
          (fcall (pairEncode (List.replicate x.length true)
            (pairEncode z (pairEncode (r.take (c₀.eval x.length)) (List.replicate j true)))))
          (Compose.slotMsgs (fun q => moverIsV vF q == b) (R.eval x.length * j)
            (R.eval x.length) hist)
          (Compose.runTape (c₀.eval x.length) (c.eval x.length) j r))) := by
  rw [ansW_eq, GI.argX_ilayout]
  refine List.flatMap_congr fun j _ => ?_
  rw [runW_ilayout]

/-- **A concatenation over `Fin L` as a concatenation over `range L`**:
`(List.ofFn fun j : Fin L => E j).flatten = (List.range L).flatMap E`. -/
theorem flatten_ofFn_eq_flatMap_range (E : ℕ → List Bool) (L : ℕ) :
    (List.ofFn fun j : Fin L => E j).flatten = (List.range L).flatMap E := by
  rw [List.ofFn_eq_map, ← List.map_coe_finRange, List.flatMap_map, List.flatMap_def]

end ComposeMachines

/-! ### The composed parties on the layout -/

namespace HybridProtocol

open ComposeMachines

section Parties

variable {G : Functionality} (H : HybridProtocol G) (ρ : Protocol)

/-- **Alice of `H.compose ρ` on the layout** [Gol04, §7.3.1], given machines `Fρ` for `ρ.P`,
`Fm` for `main.P` and `fcall` for her call inputs: with `k` the number of messages received
(`GI.msgCount`), `n = |x|`, `L = calls(n)`, `R = ρ.rounds(n)`:
- if `k < L·R`: `[]` if `ρ`'s mover `k % R` is Bob, else her `ρ`-move in run `k / R` after
  `k % R` pairs (`runW`, reading Bob's moves);
- else, if `main`'s verifier moves first and `k = L·R`: the leading filler `[]`;
- else her `main`-move on `⟨z, her answers⟩` (`ansW`) and the messages after the first `L·R`
  (`mainW`). -/
def composePW (Fρ Fm fcall : List Bool → List Bool) (w : List Bool) : List Bool :=
  if decide (GI.msgCount (GI.argM w) <
      H.calls.eval (GI.argX w).length * ρ.rounds.eval (GI.argX w).length) then
    if moverIsV ρ.verifierFirst (GI.msgCount (GI.argM w) % ρ.rounds.eval (GI.argX w).length) then []
    else runW Fρ fcall H.main.P.coins ρ.P.coins ρ.rounds ρ.verifierFirst true
      (pairEncode
        (List.replicate (GI.msgCount (GI.argM w) / ρ.rounds.eval (GI.argX w).length) true)
        (pairEncode
          (List.replicate (GI.msgCount (GI.argM w) % ρ.rounds.eval (GI.argX w).length) true) w))
  else if (H.main.verifierFirst && decide (GI.msgCount (GI.argM w) =
      H.calls.eval (GI.argX w).length * ρ.rounds.eval (GI.argX w).length)) then []
  else mainW Fm (ansW Fρ fcall H.main.P.coins ρ.P.coins ρ.rounds H.calls G.outA
      ρ.verifierFirst true)
    (fun w => H.calls.eval (GI.argX w).length * ρ.rounds.eval (GI.argX w).length) H.main.P.coins w

/-- The defining equation of `composePW` (see `composePW`).
`H.composePW ρ Fρ Fm fcall w = if decide (GI.msgCount (GI.argM w) < H.calls.eval (GI.argX w).length
* ρ.rounds.eval (GI.argX w).length) then if moverIsV ρ.verifierFirst (GI.msgCount (GI.argM w) %
ρ.rounds.eval (GI.argX w).length) then [] else runW Fρ fcall H.main.P.coins ρ.P.coins ρ.rounds
ρ.verifierFirst true (pairEncode (List.replicate (GI.msgCount (GI.argM w) / ρ.rounds.eval (GI.argX
w).length) true) (pairEncode (List.replicate (GI.msgCount (GI.argM w) % ρ.rounds.eval (GI.argX
w).length) true) w)) else if (H.main.verifierFirst && decide (GI.msgCount (GI.argM w) = H.calls.eval
(GI.argX w).length * ρ.rounds.eval (GI.argX w).length)) then [] else mainW Fm (ansW Fρ fcall
H.main.P.coins ρ.P.coins ρ.rounds H.calls G.outA ρ.verifierFirst true) (fun w => H.calls.eval
(GI.argX w).length * ρ.rounds.eval (GI.argX w).length) H.main.P.coins w`. -/
theorem composePW_eq (Fρ Fm fcall : List Bool → List Bool) (w : List Bool) :
    H.composePW ρ Fρ Fm fcall w =
      if decide (GI.msgCount (GI.argM w) <
          H.calls.eval (GI.argX w).length * ρ.rounds.eval (GI.argX w).length) then
        if moverIsV ρ.verifierFirst (GI.msgCount (GI.argM w) % ρ.rounds.eval (GI.argX w).length)
        then []
        else runW Fρ fcall H.main.P.coins ρ.P.coins ρ.rounds ρ.verifierFirst true
          (pairEncode
            (List.replicate (GI.msgCount (GI.argM w) / ρ.rounds.eval (GI.argX w).length) true)
            (pairEncode
              (List.replicate (GI.msgCount (GI.argM w) % ρ.rounds.eval (GI.argX w).length) true) w))
      else if (H.main.verifierFirst && decide (GI.msgCount (GI.argM w) =
          H.calls.eval (GI.argX w).length * ρ.rounds.eval (GI.argX w).length)) then []
      else mainW Fm (ansW Fρ fcall H.main.P.coins ρ.P.coins ρ.rounds H.calls G.outA
          ρ.verifierFirst true)
        (fun w => H.calls.eval (GI.argX w).length * ρ.rounds.eval (GI.argX w).length)
        H.main.P.coins w := rfl

/-- **Bob of `H.compose ρ` on the layout**, given machines `Fρ` for `ρ.V`, `Fm` for `main.V` and
`fcall` for his call inputs: with `c` the number of messages received and `k = c − 1`:
- if `k < L·R`: his `ρ`-move in run `k / R` after `k % R` pairs if `ρ`'s mover `k % R` is Bob
  (`runW`, reading Alice's moves), else `[]`;
- else his `main`-move on `⟨z, his answers⟩` and the messages after the first `L·R + lead`. -/
def composeVW (Fρ Fm fcall : List Bool → List Bool) (w : List Bool) : List Bool :=
  if decide (GI.msgCount (GI.argM w) - 1 <
      H.calls.eval (GI.argX w).length * ρ.rounds.eval (GI.argX w).length) then
    if moverIsV ρ.verifierFirst ((GI.msgCount (GI.argM w) - 1) % ρ.rounds.eval (GI.argX w).length)
    then runW Fρ fcall H.main.V.coins ρ.V.coins ρ.rounds ρ.verifierFirst false
      (pairEncode
        (List.replicate ((GI.msgCount (GI.argM w) - 1) / ρ.rounds.eval (GI.argX w).length) true)
        (pairEncode
          (List.replicate ((GI.msgCount (GI.argM w) - 1) % ρ.rounds.eval (GI.argX w).length)
            true) w))
    else []
  else mainW Fm (ansW Fρ fcall H.main.V.coins ρ.V.coins ρ.rounds H.calls G.outB
      ρ.verifierFirst false)
    (fun w => H.calls.eval (GI.argX w).length * ρ.rounds.eval (GI.argX w).length + H.lead)
    H.main.V.coins w

/-- The defining equation of `composeVW` (see `composeVW`).
`H.composeVW ρ Fρ Fm fcall w = if decide (GI.msgCount (GI.argM w) - 1 < H.calls.eval (GI.argX
w).length * ρ.rounds.eval (GI.argX w).length) then if moverIsV ρ.verifierFirst ((GI.msgCount
(GI.argM w) - 1) % ρ.rounds.eval (GI.argX w).length) then runW Fρ fcall H.main.V.coins ρ.V.coins
ρ.rounds ρ.verifierFirst false (pairEncode (List.replicate ((GI.msgCount (GI.argM w) - 1) /
ρ.rounds.eval (GI.argX w).length) true) (pairEncode (List.replicate ((GI.msgCount (GI.argM w) - 1) %
ρ.rounds.eval (GI.argX w).length) true) w)) else [] else mainW Fm (ansW Fρ fcall H.main.V.coins
ρ.V.coins ρ.rounds H.calls G.outB ρ.verifierFirst false) (fun w => H.calls.eval (GI.argX w).length *
ρ.rounds.eval (GI.argX w).length + H.lead) H.main.V.coins w`. -/
theorem composeVW_eq (Fρ Fm fcall : List Bool → List Bool) (w : List Bool) :
    H.composeVW ρ Fρ Fm fcall w =
      if decide (GI.msgCount (GI.argM w) - 1 <
          H.calls.eval (GI.argX w).length * ρ.rounds.eval (GI.argX w).length) then
        if moverIsV ρ.verifierFirst
          ((GI.msgCount (GI.argM w) - 1) % ρ.rounds.eval (GI.argX w).length)
        then runW Fρ fcall H.main.V.coins ρ.V.coins ρ.rounds ρ.verifierFirst false
          (pairEncode
            (List.replicate ((GI.msgCount (GI.argM w) - 1) / ρ.rounds.eval (GI.argX w).length) true)
            (pairEncode
              (List.replicate ((GI.msgCount (GI.argM w) - 1) % ρ.rounds.eval (GI.argX w).length)
                true) w))
        else []
      else mainW Fm (ansW Fρ fcall H.main.V.coins ρ.V.coins ρ.rounds H.calls G.outB
          ρ.verifierFirst false)
        (fun w => H.calls.eval (GI.argX w).length * ρ.rounds.eval (GI.argX w).length + H.lead)
        H.main.V.coins w := rfl

/-- **Alice of `H.compose ρ` is `composePW`**: if `Fρ`, `Fm` compute `ρ.P` and `main.P` on the
layout and `fcall` computes Alice's call inputs (the `callA` clause of `HybridProtocol.PolyTime`),
then `(H.composeP ρ).next x z r hist = H.composePW ρ Fρ Fm fcall (GI.ilayout x z hist r)`.

**Proof sketch.** Unfold both sides (`composeP_next`, `composePW_eq`); the number of messages
read from the layout is `|hist|` (`GI.msgCount_encodeMsgs`). In a run branch `j = k / R < L`, so
the call input is `runInputA` (`runInputA_of_lt`) and `runW` is `runNextA` (`runW_ilayout`,
`runNextA_eq`). In the main branch `mainW` is `main.P.next` on the answers read by `ansW`, which
are `answersFromA` (`ansW_ilayout`, `answersFromA_eq`, `ofFn_padFin`). -/
theorem composeP_next_eq_composePW {Fρ Fm fcall : List Bool → List Bool}
    (hFρ : ∀ x z r hist, ρ.P.next x z r hist = Fρ (GI.ilayout x z hist r))
    (hFm : ∀ x z r hist, H.main.P.next x z r hist = Fm (GI.ilayout x z hist r))
    (hcall : ∀ n (x r : List Bool) (j : Fin (H.calls.eval n)),
      fcall (pairEncode (List.replicate n true) (pairEncode x (pairEncode r
        (List.replicate j true)))) = List.ofFn (H.callA n x r j))
    (x z r : List Bool) (hist : List (List Bool)) :
    (H.composeP ρ).next x z r hist = H.composePW ρ Fρ Fm fcall (GI.ilayout x z hist r) := by
  have hrun : ∀ j p, j < H.calls.eval x.length →
      H.runNextA ρ x z r hist j p =
        runW Fρ fcall H.main.P.coins ρ.P.coins ρ.rounds ρ.verifierFirst true
          (pairEncode (List.replicate j true)
            (pairEncode (List.replicate p true) (GI.ilayout x z hist r))) := by
    intro j p hj
    rw [runW_ilayout, hcall x.length z _ ⟨j, hj⟩, ← H.runInputA_of_lt x z r hj, ← hFρ,
      runNextA_eq]
    congr 2
    funext q
    rw [beq_true]
  rw [composeP_next, composePW_eq, GI.argM_ilayout, GI.argX_ilayout, GI.msgCount_encodeMsgs]
  simp only [decide_eq_true_eq, Bool.and_eq_true]
  by_cases hk : hist.length < H.calls.eval x.length * ρ.rounds.eval x.length
  · have hR : 0 < ρ.rounds.eval x.length := Nat.pos_of_ne_zero fun h => by
      rw [h, Nat.mul_zero] at hk
      omega
    have hj : hist.length / ρ.rounds.eval x.length < H.calls.eval x.length :=
      (Nat.div_lt_iff_lt_mul hR).2 hk
    rw [if_pos hk, if_pos hk]
    by_cases hm : moverIsV ρ.verifierFirst (hist.length % ρ.rounds.eval x.length) = true
    · rw [if_pos hm, if_pos hm]
    · rw [if_neg hm, if_neg hm, hrun _ _ hj]
  · rw [if_neg hk, if_neg hk]
    by_cases hl : H.main.verifierFirst = true ∧
        hist.length = H.calls.eval x.length * ρ.rounds.eval x.length
    · rw [if_pos hl, if_pos hl]
    · rw [if_neg hl, if_neg hl, mainW_ilayout, GI.argX_ilayout, ← hFm, answersFromA_eq,
        ansW_ilayout,
        flatten_ofFn_eq_flatMap_range
          (fun j => List.ofFn (padFin (G.outA.eval x.length)
            (H.runNextA ρ x z r hist j (ρ.rounds.eval x.length))))]
      congr 2
      refine List.flatMap_congr fun j hj => ?_
      rw [ofFn_padFin, hrun _ _ (List.mem_range.1 hj), runW_ilayout]

/-- **Bob of `H.compose ρ` is `composeVW`**: if `Fρ`, `Fm` compute `ρ.V` and `main.V` on the
layout and `fcall` computes Bob's call inputs, then
`(H.composeV ρ).next x z r hist = H.composeVW ρ Fρ Fm fcall (GI.ilayout x z hist r)`.

**Proof sketch.** As `composeP_next_eq_composePW`, with `k = |hist| − 1`, `runNextB`,
`runInputB_of_lt`, the selector `!moverIsV` (`beq_false`), `answersFromB` and the drop count
`L·R + lead`. -/
theorem composeV_next_eq_composeVW {Fρ Fm fcall : List Bool → List Bool}
    (hFρ : ∀ x z r hist, ρ.V.next x z r hist = Fρ (GI.ilayout x z hist r))
    (hFm : ∀ x z r hist, H.main.V.next x z r hist = Fm (GI.ilayout x z hist r))
    (hcall : ∀ n (y r : List Bool) (j : Fin (H.calls.eval n)),
      fcall (pairEncode (List.replicate n true) (pairEncode y (pairEncode r
        (List.replicate j true)))) = List.ofFn (H.callB n y r j))
    (x z r : List Bool) (hist : List (List Bool)) :
    (H.composeV ρ).next x z r hist = H.composeVW ρ Fρ Fm fcall (GI.ilayout x z hist r) := by
  have hrun : ∀ j p, j < H.calls.eval x.length →
      H.runNextB ρ x z r hist j p =
        runW Fρ fcall H.main.V.coins ρ.V.coins ρ.rounds ρ.verifierFirst false
          (pairEncode (List.replicate j true)
            (pairEncode (List.replicate p true) (GI.ilayout x z hist r))) := by
    intro j p hj
    rw [runW_ilayout, hcall x.length z _ ⟨j, hj⟩, ← H.runInputB_of_lt x z r hj, ← hFρ,
      runNextB_eq]
    congr 2
    funext q
    rw [beq_false]
  rw [composeV_next, composeVW_eq, GI.argM_ilayout, GI.argX_ilayout, GI.msgCount_encodeMsgs]
  simp only [decide_eq_true_eq]
  by_cases hk : hist.length - 1 < H.calls.eval x.length * ρ.rounds.eval x.length
  · have hR : 0 < ρ.rounds.eval x.length := Nat.pos_of_ne_zero fun h => by
      rw [h, Nat.mul_zero] at hk
      omega
    have hj : (hist.length - 1) / ρ.rounds.eval x.length < H.calls.eval x.length :=
      (Nat.div_lt_iff_lt_mul hR).2 hk
    rw [if_pos hk, if_pos hk]
    by_cases hm : moverIsV ρ.verifierFirst ((hist.length - 1) % ρ.rounds.eval x.length) = true
    · rw [if_pos hm, if_pos hm, hrun _ _ hj]
    · rw [if_neg hm, if_neg hm]
  · rw [if_neg hk, if_neg hk, mainW_ilayout, GI.argX_ilayout, ← hFm, answersFromB_eq, ansW_ilayout,
      flatten_ofFn_eq_flatMap_range
        (fun j => List.ofFn (padFin (G.outB.eval x.length)
          (H.runNextB ρ x z r hist j (ρ.rounds.eval x.length))))]
    congr 2
    refine List.flatMap_congr fun j hj => ?_
    rw [ofFn_padFin, hrun _ _ (List.mem_range.1 hj), runW_ilayout]

/-- **`composePW` is polynomial-time** when `Fρ`, `Fm` and `fcall` are.
`PolyTimeComputable (H.composePW ρ Fρ Fm fcall)`.

**Proof sketch.** Three branches (`Complexity.polyTimeComputable_ite`) on unary tests of the
message count (`GI.msgCount_poly`) against `L(n)·R(n)` (`ltTest_poly`, `eqTest_poly`), the
mover test at `k % R` (`polyTimeComputable_moverW`, `modNum_poly`), and the pieces
`polyTimeComputable_runW` (at `k / R`, `divNum_poly`), `polyTimeComputable_ansW` and
`polyTimeComputable_mainW`. -/
theorem polyTimeComputable_composePW {Fρ Fm fcall : List Bool → List Bool}
    (hFρ : PolyTimeComputable Fρ) (hFm : PolyTimeComputable Fm)
    (hcall : PolyTimeComputable fcall) : PolyTimeComputable (H.composePW ρ Fρ Fm fcall) := by
  have hk : PolyTimeComputable fun w => List.replicate (GI.msgCount (GI.argM w)) true :=
    GI.msgCount_poly.comp' GI.argM_poly
  have hR := unaryPoly_comp ρ.rounds GI.argX_poly
  have hLR := unaryMul_poly (unaryPoly_comp H.calls GI.argX_poly) hR
  have hdiv : PolyTimeComputable fun w =>
      List.replicate (GI.msgCount (GI.argM w) / ρ.rounds.eval (GI.argX w).length) true :=
    (divNum_poly hk hR).congr fun w => by rw [divNum_eq]
  have hmod : PolyTimeComputable fun w =>
      List.replicate (GI.msgCount (GI.argM w) % ρ.rounds.eval (GI.argX w).length) true :=
    (modNum_poly hk hR).congr fun w => by rw [modNum_eq]
  have hmv : PolyTimeComputable fun w =>
      [moverIsV ρ.verifierFirst (GI.msgCount (GI.argM w) % ρ.rounds.eval (GI.argX w).length)] :=
    ((polyTimeComputable_moverW ρ.verifierFirst true).comp'
      (hmod.pairEncode polyTimeComputable_id)).congr fun w => by
        rw [moverW_eq, pairFstD_pairEncode, List.length_replicate, beq_true]
  have hrun := (polyTimeComputable_runW hFρ hcall H.main.P.coins ρ.P.coins ρ.rounds
    ρ.verifierFirst true).comp' (hdiv.pairEncode (hmod.pairEncode polyTimeComputable_id))
  have hmain := polyTimeComputable_mainW hFm (polyTimeComputable_ansW hFρ hcall H.main.P.coins
    ρ.P.coins ρ.rounds H.calls G.outA ρ.verifierFirst true) hLR H.main.P.coins
  have hlead : PolyTimeComputable fun w =>
      [H.main.verifierFirst && decide (GI.msgCount (GI.argM w) =
      H.calls.eval (GI.argX w).length * ρ.rounds.eval (GI.argX w).length)] :=
    polyTimeComputable_and (polyTimeComputable_const [H.main.verifierFirst]) (eqTest_poly hk hLR)
  exact (polyTimeComputable_ite (ltTest_poly hk hLR)
    (polyTimeComputable_ite hmv (polyTimeComputable_const []) hrun)
    (polyTimeComputable_ite hlead (polyTimeComputable_const []) hmain)).congr
    fun w => (H.composePW_eq ρ Fρ Fm fcall w).symm

/-- **`composeVW` is polynomial-time** when `Fρ`, `Fm` and `fcall` are.
`PolyTimeComputable (H.composeVW ρ Fρ Fm fcall)`.

**Proof sketch.** As `polyTimeComputable_composePW`, with the count `k − 1` (`unarySub_poly`),
two branches in the run phase and the drop count `L(n)·R(n) + lead` (`unaryAdd_poly`). -/
theorem polyTimeComputable_composeVW {Fρ Fm fcall : List Bool → List Bool}
    (hFρ : PolyTimeComputable Fρ) (hFm : PolyTimeComputable Fm)
    (hcall : PolyTimeComputable fcall) : PolyTimeComputable (H.composeVW ρ Fρ Fm fcall) := by
  have hk : PolyTimeComputable fun w => List.replicate (GI.msgCount (GI.argM w) - 1) true :=
    unarySub_poly (GI.msgCount_poly.comp' GI.argM_poly) (unaryConst_poly 1)
  have hR := unaryPoly_comp ρ.rounds GI.argX_poly
  have hLR := unaryMul_poly (unaryPoly_comp H.calls GI.argX_poly) hR
  have hdiv : PolyTimeComputable fun w =>
      List.replicate ((GI.msgCount (GI.argM w) - 1) / ρ.rounds.eval (GI.argX w).length) true :=
    (divNum_poly hk hR).congr fun w => by rw [divNum_eq]
  have hmod : PolyTimeComputable fun w =>
      List.replicate ((GI.msgCount (GI.argM w) - 1) % ρ.rounds.eval (GI.argX w).length) true :=
    (modNum_poly hk hR).congr fun w => by rw [modNum_eq]
  have hmv : PolyTimeComputable fun w =>
      [moverIsV ρ.verifierFirst
        ((GI.msgCount (GI.argM w) - 1) % ρ.rounds.eval (GI.argX w).length)] :=
    ((polyTimeComputable_moverW ρ.verifierFirst true).comp'
      (hmod.pairEncode polyTimeComputable_id)).congr fun w => by
        rw [moverW_eq, pairFstD_pairEncode, List.length_replicate, beq_true]
  have hrun := (polyTimeComputable_runW hFρ hcall H.main.V.coins ρ.V.coins ρ.rounds
    ρ.verifierFirst false).comp' (hdiv.pairEncode (hmod.pairEncode polyTimeComputable_id))
  have hmain := polyTimeComputable_mainW hFm (polyTimeComputable_ansW hFρ hcall H.main.V.coins
    ρ.V.coins ρ.rounds H.calls G.outB ρ.verifierFirst false)
    (unaryAdd_poly hLR (unaryConst_poly H.lead)) H.main.V.coins
  exact (polyTimeComputable_ite (ltTest_poly hk hLR)
    (polyTimeComputable_ite hmv hrun (polyTimeComputable_const [])) hmain).congr
    fun w => (H.composeVW_eq ρ Fρ Fm fcall w).symm

end Parties

end HybridProtocol

end TCSlib.Cryptography.SecureComputation
