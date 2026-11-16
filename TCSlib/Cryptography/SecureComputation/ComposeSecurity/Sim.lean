/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TCSlib.Cryptography.SecureComputation.ComposeSecurity.Assembly
import TCSlib.Cryptography.SecureComputation.ComposeSecurity.Reductions

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# The post-processing `Φ` and the simulators of the composed protocol

Steps 1 and 4 of the proof of the composition theorem [Gol04, §7.3.1, proof of Theorem 7.3.3]. A
party's simulator for `H.compose ρ` runs the hybrid simulator `S^H` and post-processes its output
`hv`, read as a view of `main` with private input `⟨x, a⟩`, `main`-tape `mt` and messages `me`:
for each call `j < L(n)` it recomputes the call input `fcall ⟨1^n, ⟨x, ⟨mt, 1^j⟩⟩⟩`, runs `ρ`'s
simulator `S^ρ` on it and on the `j`-th block of `a`, with the `j`-th block of fresh coins, and
assembles the view of `H.compose ρ` (`ComposeSim.asmView`). The same post-processing applied to
the hybrid real sample gives the last hybrid of the proof, and applied before a distinguisher it
gives the reduction to the hybrid model's security (`exists_dPhi`).

## Main definitions

* `ComposeSim.simV`: one simulated run, `ComposeSim.vlW`: their encoded list.
* `ComposeSim.phiV`: the post-processing of a view; `ComposeSim.phiD`: of a sample `⟨view, out⟩`.

## Main results

* `ComposeSim.phiV_view`: `phiV` on an encoded view of `main` with input `1^n` is the assembled
  view of the simulated runs.
* `ComposeSim.polyTimeComputable_phiV`, `polyTimeComputable_phiD`.
* `ComposeSim.exists_simulator`, `ComposeSim.exists_dPhi`: the simulator and the reduction as
  non-uniform PPT machines.

## References

* [Gol04] O. Goldreich, *Foundations of Cryptography, Volume 2: Basic Applications*, Cambridge
  University Press, 2004, §7.3.1 (the proof of Theorem 7.3.3).
-/

namespace TCSlib.Cryptography.SecureComputation.ComposeSim

open Complexity Turing Complexity.StateLoop TCSlib.Cryptography.EncodingMachines ComposeMachines

variable (Sρ : NUPPT) (fcall : List Bool → List Bool) (calls rounds cρ out : PolyExpr)
  (vF b : Bool) (lead : ℕ)

/-- **One simulated run**: on `v = ⟨1^j, ⟨⟨u, α⟩, ⟨hv, s⟩⟩⟩` (`u = 1^n`, `α` the advice of
`S^ρ`, `hv = ⟨⟨x₁, ⟨xin, a⟩⟩, ⟨mt, me⟩⟩` a view, `s` the fresh coins), `S^ρ`'s output on the
call input `fcall ⟨u, ⟨xin, ⟨mt, 1^j⟩⟩⟩` and the answer block `coinBlock out(n) j a`, with
advice `α` and coins `coinBlock Sρ.coins(n) j s`. -/
def simV (v : List Bool) : List Bool :=
  Sρ.output (NUPPT.layout (pairFstD (pairFstD (pairSndD v)))
    (pairEncode
      (fcall (pairEncode (pairFstD (pairFstD (pairSndD v)))
        (pairEncode (pairFstD (pairSndD (pairFstD (pairFstD (pairSndD (pairSndD v))))))
          (pairEncode (pairFstD (pairSndD (pairFstD (pairSndD (pairSndD v))))) (pairFstD v)))))
      (coinBlock (out.eval (pairFstD (pairFstD (pairSndD v))).length) (pairFstD v).length
        (pairSndD (pairSndD (pairFstD (pairFstD (pairSndD (pairSndD v))))))))
    (pairSndD (pairFstD (pairSndD v)))
    (coinBlock (Sρ.coins.eval (pairFstD (pairFstD (pairSndD v))).length) (pairFstD v).length
      (pairSndD (pairSndD (pairSndD v)))))

/-- `simV` on its word: with `w = ⟨⟨1^n, α⟩, ⟨⟨⟨x₁, ⟨xin, a⟩⟩, ⟨mt, me⟩⟩, s⟩⟩`,
`simV ⟨1^j, w⟩ = Sρ.output (layout 1^n ⟨fcall ⟨1^n, ⟨xin, ⟨mt, 1^j⟩⟩⟩, coinBlock out(n) j a⟩ α
(coinBlock Sρ.coins(n) j s))`. -/
theorem simV_pairEncode (n j : ℕ) (α x₁ xin a mt me s : List Bool) :
    simV Sρ fcall out (pairEncode (List.replicate j true)
        (pairEncode (pairEncode (List.replicate n true) α)
          (pairEncode (pairEncode (pairEncode x₁ (pairEncode xin a)) (pairEncode mt me)) s))) =
      Sρ.output (NUPPT.layout (List.replicate n true)
        (pairEncode (fcall (pairEncode (List.replicate n true)
            (pairEncode xin (pairEncode mt (List.replicate j true)))))
          (coinBlock (out.eval n) j a)) α (coinBlock (Sρ.coins.eval n) j s)) := by
  simp only [simV, pairFstD_pairEncode, pairSndD_pairEncode, List.length_replicate]

/-- **The encoded list of the simulated runs** on `w = ⟨⟨1^n, α⟩, ⟨hv, s⟩⟩`:
`vlW w = (range calls(n)).flatMap fun j => ⟨simV ⟨1^j, w⟩, []⟩`. -/
def vlW (w : List Bool) : List Bool :=
  (List.range (calls.eval (pairFstD (pairFstD w)).length)).flatMap fun j =>
    pairEncode (simV Sρ fcall out (pairEncode (List.replicate j true) w)) []

/-- The defining equation of `vlW` (see `vlW`).
`vlW Sρ fcall calls out w = (List.range (calls.eval (pairFstD (pairFstD w)).length)).flatMap fun j
=> pairEncode (simV Sρ fcall out (pairEncode (List.replicate j true) w)) []`. -/
theorem vlW_eq (w : List Bool) :
    vlW Sρ fcall calls out w =
      (List.range (calls.eval (pairFstD (pairFstD w)).length)).flatMap fun j =>
        pairEncode (simV Sρ fcall out (pairEncode (List.replicate j true) w)) [] := rfl

/-- **The post-processing of a view** (`Φ` on views): on `w = ⟨⟨1^n, α⟩, ⟨hv, s⟩⟩` with
`hv = ⟨⟨x₁, ⟨xin, a⟩⟩, ⟨mt, me⟩⟩`, the assembled view (`asmW`) of `x₁`, `xin`, `mt`, `me` and the
simulated runs (`vlW`). -/
def phiV (w : List Bool) : List Bool :=
  asmW calls rounds cρ vF b lead
    (pairEncode (pairEncode (pairEncode (pairFstD (pairFstD (pairFstD (pairSndD w))))
        (pairFstD (pairSndD (pairFstD (pairFstD (pairSndD w))))))
      (pairEncode (pairFstD (pairSndD (pairFstD (pairSndD w))))
        (pairSndD (pairSndD (pairFstD (pairSndD w))))))
      (vlW Sρ fcall calls out w))

/-- The defining equation of `phiV` (see `phiV`).
`phiV Sρ fcall calls rounds cρ out vF b lead w = asmW calls rounds cρ vF b lead (pairEncode
(pairEncode (pairEncode (pairFstD (pairFstD (pairFstD (pairSndD w)))) (pairFstD (pairSndD (pairFstD
(pairFstD (pairSndD w)))))) (pairEncode (pairFstD (pairSndD (pairFstD (pairSndD w)))) (pairSndD
(pairSndD (pairFstD (pairSndD w)))))) (vlW Sρ fcall calls out w))`. -/
theorem phiV_eq (w : List Bool) :
    phiV Sρ fcall calls rounds cρ out vF b lead w =
      asmW calls rounds cρ vF b lead
        (pairEncode (pairEncode (pairEncode (pairFstD (pairFstD (pairFstD (pairSndD w))))
            (pairFstD (pairSndD (pairFstD (pairFstD (pairSndD w))))))
          (pairEncode (pairFstD (pairSndD (pairFstD (pairSndD w))))
            (pairSndD (pairSndD (pairFstD (pairSndD w))))))
          (vlW Sρ fcall calls out w)) := rfl

/-- **`phiV` on a view of `main` with common input `1^n`**: on
`⟨⟨1^n, α⟩, ⟨⟨⟨1^n, ⟨xin, a⟩⟩, ⟨mt, me⟩⟩, s⟩⟩` it is
`asmView … 1^n xin mt me V` with `V j = S^ρ`'s output on the call input and the answer block
`j`, with the coin block `j` (`asmW_pairEncode`, `asmView_congr`, `msgAt_encodeMsgs`). -/
theorem phiV_view (n : ℕ) (α xin a mt me s : List Bool) :
    phiV Sρ fcall calls rounds cρ out vF b lead
        (pairEncode (pairEncode (List.replicate n true) α)
          (pairEncode (pairEncode (pairEncode (List.replicate n true) (pairEncode xin a))
            (pairEncode mt me)) s)) =
      asmView calls rounds cρ vF b lead (List.replicate n true) xin mt me fun j =>
        Sρ.output (NUPPT.layout (List.replicate n true)
          (pairEncode (fcall (pairEncode (List.replicate n true)
              (pairEncode xin (pairEncode mt (List.replicate j true)))))
            (coinBlock (out.eval n) j a)) α (coinBlock (Sρ.coins.eval n) j s)) := by
  rw [phiV_eq, vlW_eq]
  simp only [pairFstD_pairEncode, pairSndD_pairEncode]
  rw [asmW_pairEncode]
  refine asmView_congr _ _ _ _ _ _ _ _ _ _ fun j hj => ?_
  rw [List.length_replicate] at hj ⊢
  rw [← List.flatMap_map (fun j => simV Sρ fcall out (pairEncode (List.replicate j true)
      (pairEncode (pairEncode (List.replicate n true) α)
        (pairEncode (pairEncode (pairEncode (List.replicate n true) (pairEncode xin a))
          (pairEncode mt me)) s)))) (fun m => pairEncode m []),
    ← encodeMsgs_eq_flatMap, msgAt_encodeMsgs, Compose.getD_map_range hj, simV_pairEncode]

/-- **The post-processing of a sample** (`Φ` on samples `⟨view, out⟩`): on
`w = ⟨⟨u, α⟩, ⟨⟨hv, o⟩, s⟩⟩`, `phiD w = ⟨phiV ⟨⟨u, α⟩, ⟨hv, s⟩⟩, o⟩`. -/
def phiD (w : List Bool) : List Bool :=
  pairEncode (phiV Sρ fcall calls rounds cρ out vF b lead
      (pairEncode (pairFstD w) (pairEncode (pairFstD (pairFstD (pairSndD w)))
        (pairSndD (pairSndD w)))))
    (pairSndD (pairFstD (pairSndD w)))

/-- `phiD` on its word: `phiD ⟨⟨u, α⟩, ⟨⟨hv, o⟩, s⟩⟩ = ⟨phiV ⟨⟨u, α⟩, ⟨hv, s⟩⟩, o⟩`. -/
theorem phiD_pairEncode (u α hv o s : List Bool) :
    phiD Sρ fcall calls rounds cρ out vF b lead
        (pairEncode (pairEncode u α) (pairEncode (pairEncode hv o) s)) =
      pairEncode (phiV Sρ fcall calls rounds cρ out vF b lead
        (pairEncode (pairEncode u α) (pairEncode hv s))) o := by
  simp only [phiD, pairFstD_pairEncode, pairSndD_pairEncode]

variable {fcall}

/-- **`simV` is polynomial-time** when `fcall` is: `PolyTimeComputable (simV Sρ fcall out)`.

**Proof sketch.** The components `1^n`, `α`, `xin`, `a`, `mt`, `s` of the word are projections;
the call input is `fcall` on a pairing of them; the answer block and the coin block are
`coinSlice`s (`GI.coinSlice_poly`); and `S^ρ`'s output on the assembled layout is polynomial-time
(`NUPPT.polyTimeComputable_output`, `NUPPT.polyTimeComputable_layout`). -/
theorem polyTimeComputable_simV (hcall : PolyTimeComputable fcall) :
    PolyTimeComputable (simV Sρ fcall out) := by
  have hw := polyTimeComputable_pairSndD
  have hu : PolyTimeComputable fun v => pairFstD (pairFstD (pairSndD v)) :=
    polyTimeComputable_pairFstD.comp' (polyTimeComputable_pairFstD.comp' hw)
  have hhv : PolyTimeComputable fun v => pairFstD (pairSndD (pairSndD v)) :=
    polyTimeComputable_pairFstD.comp' (polyTimeComputable_pairSndD.comp' hw)
  have hz : PolyTimeComputable fun v => pairSndD (pairFstD (pairFstD (pairSndD (pairSndD v)))) :=
    polyTimeComputable_pairSndD.comp' (polyTimeComputable_pairFstD.comp'
      (polyTimeComputable_pairFstD.comp' (polyTimeComputable_pairSndD.comp' hw)))
  have hxin := polyTimeComputable_pairFstD.comp' hz
  have ha := polyTimeComputable_pairSndD.comp' hz
  have hmt : PolyTimeComputable fun v => pairFstD (pairSndD (pairFstD (pairSndD (pairSndD v)))) :=
    polyTimeComputable_pairFstD.comp' (polyTimeComputable_pairSndD.comp' hhv)
  have hs : PolyTimeComputable fun v => pairSndD (pairSndD (pairSndD v)) :=
    polyTimeComputable_pairSndD.comp' (polyTimeComputable_pairSndD.comp' hw)
  have hα : PolyTimeComputable fun v => pairSndD (pairFstD (pairSndD v)) :=
    polyTimeComputable_pairSndD.comp' (polyTimeComputable_pairFstD.comp' hw)
  have hin := hcall.comp' (hu.pairEncode (hxin.pairEncode (hmt.pairEncode
    polyTimeComputable_pairFstD)))
  exact (Sρ.polyTimeComputable_output.comp' (NUPPT.polyTimeComputable_layout hu
    (hin.pairEncode (GI.coinSlice_poly out hu polyTimeComputable_pairFstD ha)) hα
    (GI.coinSlice_poly Sρ.coins hu polyTimeComputable_pairFstD hs))).congr fun v => rfl

/-- **`vlW` is polynomial-time** (`ComposeMachines.polyTimeComputable_flatMap_range` of
`polyTimeComputable_simV` over the unary count `calls(n)`).
`PolyTimeComputable (vlW Sρ fcall calls out)`. -/
theorem polyTimeComputable_vlW (hcall : PolyTimeComputable fcall) :
    PolyTimeComputable (vlW Sρ fcall calls out) := by
  have hchunk : PolyTimeComputable fun v =>
      pairEncode (simV Sρ fcall out (pairEncode (List.replicate (pairFstD v).length true)
        (pairSndD v))) [] :=
    ((polyTimeComputable_simV Sρ out hcall).comp' ((unaryLength_poly
      polyTimeComputable_pairFstD).pairEncode polyTimeComputable_pairSndD)).pairEncode
      (polyTimeComputable_const [])
  exact (polyTimeComputable_flatMap_range (E := fun w j =>
      pairEncode (simV Sρ fcall out (pairEncode (List.replicate j true) w)) []) hchunk
    (unaryPolyOf_poly calls (unaryLength_poly (polyTimeComputable_pairFstD.comp'
      polyTimeComputable_pairFstD)))).congr fun w => (vlW_eq Sρ fcall calls out w).symm

/-- **`phiV` is polynomial-time** (`polyTimeComputable_asmW` after projections and `vlW`).
`PolyTimeComputable (phiV Sρ fcall calls rounds cρ out vF b lead)`. -/
theorem polyTimeComputable_phiV (hcall : PolyTimeComputable fcall) :
    PolyTimeComputable (phiV Sρ fcall calls rounds cρ out vF b lead) := by
  have hhv : PolyTimeComputable fun w => pairFstD (pairSndD w) :=
    polyTimeComputable_pairFstD.comp' polyTimeComputable_pairSndD
  have hv1 := polyTimeComputable_pairFstD.comp' hhv
  have hv2 := polyTimeComputable_pairSndD.comp' hhv
  exact ((polyTimeComputable_asmW calls rounds cρ vF b lead).comp'
    ((((polyTimeComputable_pairFstD.comp' hv1).pairEncode (polyTimeComputable_pairFstD.comp'
      (polyTimeComputable_pairSndD.comp' hv1))).pairEncode
      ((polyTimeComputable_pairFstD.comp' hv2).pairEncode
        (polyTimeComputable_pairSndD.comp' hv2))).pairEncode
      (polyTimeComputable_vlW Sρ calls out hcall))).congr fun w => rfl

/-- **`phiD` is polynomial-time** (`polyTimeComputable_phiV` after re-pairing).
`PolyTimeComputable (phiD Sρ fcall calls rounds cρ out vF b lead)`. -/
theorem polyTimeComputable_phiD (hcall : PolyTimeComputable fcall) :
    PolyTimeComputable (phiD Sρ fcall calls rounds cρ out vF b lead) := by
  have hsmp : PolyTimeComputable fun w => pairFstD (pairSndD w) :=
    polyTimeComputable_pairFstD.comp' polyTimeComputable_pairSndD
  exact (((polyTimeComputable_phiV Sρ calls rounds cρ out vF b lead hcall).comp'
    (polyTimeComputable_pairFstD.pairEncode ((polyTimeComputable_pairFstD.comp' hsmp).pairEncode
      (polyTimeComputable_pairSndD.comp' polyTimeComputable_pairSndD)))).pairEncode
    (polyTimeComputable_pairSndD.comp' hsmp)).congr fun w => rfl

/-- **The simulator of the composed protocol** (step 1): for a hybrid simulator `SH`, there is a
non-uniform PPT `S` with coins `SH.coins + calls · Sρ.coins` such that
`S(1^n, y; r) = phiV ⟨⟨1^n, Sρ.advice n⟩, ⟨SH(1^n, y; r_{<SH.coins(n)}), r_{≥SH.coins(n)}⟩⟩`
(`exists_post`). -/
theorem exists_simulator (SH : NUPPT) (hcall : PolyTimeComputable fcall) :
    ∃ S : NUPPT, S.coins = .add SH.coins (.mul calls Sρ.coins) ∧ ∀ n y r, S.runAtL n y r =
      phiV Sρ fcall calls rounds cρ out vF b lead
        (pairEncode (pairEncode (List.replicate n true) (Sρ.advice n))
          (pairEncode (SH.runAtL n y (r.take (SH.coinLen n))) (r.drop (SH.coinLen n)))) :=
  exists_post SH (polyTimeComputable_phiV Sρ calls rounds cρ out vF b lead hcall) Sρ.advice Sρ.adv
    Sρ.advice_length (.mul calls Sρ.coins)

/-- **The reduction to the hybrid model** (step 4): for a distinguisher `D`, there is a non-uniform
PPT `DΦ` with coins `calls · Sρ.coins + D.coins` such that
`DΦ(1^n, w; r) = D(1^n, phiD ⟨⟨1^n, Sρ.advice n⟩, ⟨w, r_{<p(n)}⟩⟩; r_{≥p(n)})`,
`p = calls · Sρ.coins` (`exists_pre`). -/
theorem exists_dPhi (D : NUPPT) (hcall : PolyTimeComputable fcall) :
    ∃ DΦ : NUPPT, DΦ.coins = .add (.mul calls Sρ.coins) D.coins ∧ ∀ n y r, DΦ.runAtL n y r =
      D.runAtL n (phiD Sρ fcall calls rounds cρ out vF b lead
        (pairEncode (pairEncode (List.replicate n true) (Sρ.advice n))
          (pairEncode y (r.take ((PolyExpr.mul calls Sρ.coins).eval n)))))
        (r.drop ((PolyExpr.mul calls Sρ.coins).eval n)) :=
  exists_pre D (polyTimeComputable_phiD Sρ calls rounds cρ out vF b lead hcall) Sρ.advice Sρ.adv
    Sρ.advice_length (.mul calls Sρ.coins)

end TCSlib.Cryptography.SecureComputation.ComposeSim
