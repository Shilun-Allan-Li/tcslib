/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TCSlib.Cryptography.SecureComputation.ComposeSecurity.Accept
import TCSlib.Cryptography.SecureComputation.ComposeSecurity.Reductions

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# The reduction of one hybrid step to the sub-protocol

Step 3 of the proof of the composition theorem [Gol04, §7.3.1, proof of Theorem 7.3.3]. A
distinguisher between neighbouring hybrids, at fixed inputs, run index and other coordinates,
becomes a distinguisher for one sample of `ρ`: the reduction holds as advice a **template**
(`tmplW`): the header `⟨⟨x₁, xin⟩, ⟨mt, me⟩⟩` of the assembled view, the encoded words of the
runs before and after the run under attack, and the other party's output. On a `ρ`-sample `w`
it inserts the view `pairFstD w` between them, assembles the view (`asmW`) and pairs it with the
output (`hybW`). The template is chosen at each `n` for the worst-case instance, so one
non-uniform machine serves every `n` (`exists_gap_le`).

## Main definitions

* `ComposeSim.tmplW`: the template; `ComposeSim.hybW`: the reduction's pre-processing.

## Main results

* `ComposeSim.hybW_tmplW`: the pre-processing on a template.
* `ComposeSim.polyTimeComputable_hybW`.
* `ComposeSim.exists_gap_le`: the worst-case gap over the instances of each `n` is at most the
  sub-protocol's negligible bound.

## References

* [Gol04] O. Goldreich, *Foundations of Cryptography, Volume 2: Basic Applications*, Cambridge
  University Press, 2004, §7.3.1 (the proof of Theorem 7.3.3).
-/

namespace TCSlib.Cryptography.SecureComputation.ComposeSim

open Finset Complexity Turing TCSlib.Cryptography ComposeProb ComposeMachines

/-- **The template of a hybrid step**: `⟨⟨hdr, encodeMsgs pre⟩, ⟨encodeMsgs suf, out⟩⟩` for the
header `hdr`, the words `pre` of the runs before the attacked one, the words `suf` of those
after it and the output `out`.
`tmplW hdr pre suf out = pairEncode (pairEncode hdr (Strategy.encodeMsgs pre)) (pairEncode
(Strategy.encodeMsgs suf) out)`. -/
def tmplW (hdr : List Bool) (pre suf : List (List Bool)) (out : List Bool) : List Bool :=
  pairEncode (pairEncode hdr (Strategy.encodeMsgs pre))
    (pairEncode (Strategy.encodeMsgs suf) out)

/-- The defining equation of `tmplW` (see `tmplW`).
`tmplW hdr pre suf out = pairEncode (pairEncode hdr (Strategy.encodeMsgs pre)) (pairEncode
(Strategy.encodeMsgs suf) out)`. -/
theorem tmplW_eq (hdr : List Bool) (pre suf : List (List Bool)) (out : List Bool) :
    tmplW hdr pre suf out =
      pairEncode (pairEncode hdr (Strategy.encodeMsgs pre))
        (pairEncode (Strategy.encodeMsgs suf) out) := rfl

/-- **The pre-processing of the hybrid-step reduction**: on `z = ⟨⟨u, β⟩, ⟨w, r⟩⟩` with
`β = ⟨⟨hdr, P⟩, ⟨Q, out⟩⟩`, the pair of `asmW ⟨hdr, P ++ ⟨pairFstD w, Q⟩⟩` and `out`. -/
def hybW (calls rounds cρ : PolyExpr) (vF b : Bool) (lead : ℕ) (z : List Bool) : List Bool :=
  pairEncode (asmW calls rounds cρ vF b lead
      (pairEncode (pairFstD (pairFstD (pairSndD (pairFstD z))))
        (pairSndD (pairFstD (pairSndD (pairFstD z))) ++
          pairEncode (pairFstD (pairFstD (pairSndD z))) (pairFstD (pairSndD (pairSndD
            (pairFstD z)))))))
    (pairSndD (pairSndD (pairSndD (pairFstD z))))

/-- The defining equation of `hybW` (see `hybW`).
`hybW calls rounds cρ vF b lead z = pairEncode (asmW calls rounds cρ vF b lead (pairEncode (pairFstD
(pairFstD (pairSndD (pairFstD z)))) (pairSndD (pairFstD (pairSndD (pairFstD z))) ++ pairEncode
(pairFstD (pairFstD (pairSndD z))) (pairFstD (pairSndD (pairSndD (pairFstD z))))))) (pairSndD
(pairSndD (pairSndD (pairFstD z))))`. -/
theorem hybW_eq (calls rounds cρ : PolyExpr) (vF b : Bool) (lead : ℕ) (z : List Bool) :
    hybW calls rounds cρ vF b lead z =
      pairEncode (asmW calls rounds cρ vF b lead
          (pairEncode (pairFstD (pairFstD (pairSndD (pairFstD z))))
            (pairSndD (pairFstD (pairSndD (pairFstD z))) ++
              pairEncode (pairFstD (pairFstD (pairSndD z))) (pairFstD (pairSndD (pairSndD
                (pairFstD z)))))))
        (pairSndD (pairSndD (pairSndD (pairFstD z)))) := rfl

/-- **The pre-processing on a template**: `hybW ⟨⟨u, tmplW hdr pre suf out⟩, ⟨w, r⟩⟩ =
⟨asmW ⟨hdr, encodeMsgs (pre ++ pairFstD w :: suf)⟩, out⟩` (`encodeMsgs_append`). -/
theorem hybW_tmplW (calls rounds cρ : PolyExpr) (vF b : Bool) (lead : ℕ)
    (u hdr out w r : List Bool) (pre suf : List (List Bool)) :
    hybW calls rounds cρ vF b lead (pairEncode (pairEncode u (tmplW hdr pre suf out))
        (pairEncode w r)) =
      pairEncode (asmW calls rounds cρ vF b lead
        (pairEncode hdr (Strategy.encodeMsgs (pre ++ pairFstD w :: suf)))) out := by
  rw [hybW_eq, tmplW_eq, encodeMsgs_append, Strategy.encodeMsgs_cons]
  simp only [pairFstD_pairEncode, pairSndD_pairEncode]

/-- **The pre-processing is polynomial-time** (`polyTimeComputable_asmW` after projections,
`append` and `pairEncode`).
`PolyTimeComputable (hybW calls rounds cρ vF b lead)`. -/
theorem polyTimeComputable_hybW (calls rounds cρ : PolyExpr) (vF b : Bool) (lead : ℕ) :
    PolyTimeComputable (hybW calls rounds cρ vF b lead) := by
  have hβ : PolyTimeComputable fun z => pairSndD (pairFstD z) :=
    polyTimeComputable_pairSndD.comp' polyTimeComputable_pairFstD
  have h1 := polyTimeComputable_pairFstD.comp' hβ
  have h2 := polyTimeComputable_pairSndD.comp' hβ
  have hw : PolyTimeComputable fun z => pairFstD (pairFstD (pairSndD z)) :=
    polyTimeComputable_pairFstD.comp' (polyTimeComputable_pairFstD.comp'
      polyTimeComputable_pairSndD)
  exact (((polyTimeComputable_asmW calls rounds cρ vF b lead).comp'
    ((polyTimeComputable_pairFstD.comp' h1).pairEncode
      ((polyTimeComputable_pairSndD.comp' h1).append
        (hw.pairEncode (polyTimeComputable_pairFstD.comp' h2))))).pairEncode
    (polyTimeComputable_pairSndD.comp' h2)).congr fun z => rfl

/-- **The worst-case hybrid step is bounded by the sub-protocol's security.** Let `rs n x y` and
`is n x y` be samplers of `ρ` on inputs of `G`'s lengths, indistinguishable with a negligible
bound uniform over the inputs (`hS`). Let `Θ n` be finite sets of instances, each with inputs
`xA θ`, `yB θ` of `ρ` and a template whose length is at most `q(n)`. Then for every non-uniform
PPT `D` there is a negligible `ε₂` with, for all `n` and `θ : Θ n`,
`|Pr_t[D(K θ (pairFstD (rs t)))] − Pr_s[D(K θ (pairFstD (is s)))]| ≤ ε₂(n)`, where
`K θ v = ⟨asmW ⟨hdr θ, encodeMsgs (pre θ ++ v :: suf θ)⟩, out θ⟩` (the template filled with `v`).

**Proof sketch.** At each `n` with instances, take the instance `θ*` with the largest gap
(`Finset.exists_max_image`) and give its template as advice (length at most `q(n)`). The
machine `D ∘ hybW` with no extra coins (`exists_pre`) accepts a sample `w` as `D` accepts
`K θ* (pairFstD w)` (`acceptProb_pre`, `hybW_tmplW`, `acceptProb_fst`), so its advantage
between `rs` and `is` at the inputs of `θ*` is the gap at `θ*`, at most `ε₂(n)` by `hS`, and
every gap at `n` is at most the gap at `θ*`. -/
theorem exists_gap_le {G : Functionality} {T Sc : ℕ → Type} [∀ n, Fintype (T n)]
    [∀ n, Fintype (Sc n)]
    (rs : ∀ n, (Fin (G.inA.eval n) → Bool) → (Fin (G.inB.eval n) → Bool) → T n → List Bool)
    (is : ∀ n, (Fin (G.inA.eval n) → Bool) → (Fin (G.inB.eval n) → Bool) → Sc n → List Bool)
    (hS : ∀ D : NUPPT, ∃ ε : ℕ → ℝ, Negligible ε ∧
      ∀ n (x : Fin (G.inA.eval n) → Bool) (y : Fin (G.inB.eval n) → Bool),
        distAdv (rs n x y) (is n x y) (D.distinguisherL n) ≤ ε n)
    (calls rounds cρ : PolyExpr) (vF b : Bool) (lead : ℕ) {Θ : ℕ → Type} [∀ n, Fintype (Θ n)]
    (xA : ∀ n, Θ n → Fin (G.inA.eval n) → Bool) (yB : ∀ n, Θ n → Fin (G.inB.eval n) → Bool)
    (hdr out : ∀ n, Θ n → List Bool) (pre suf : ∀ n, Θ n → List (List Bool)) (q : PolyExpr)
    (hq : ∀ n θ, (tmplW (hdr n θ) (pre n θ) (suf n θ) (out n θ)).length ≤ q.eval n)
    (D : NUPPT) :
    ∃ ε₂ : ℕ → ℝ, Negligible ε₂ ∧ ∀ n (θ : Θ n),
      |acceptProb (fun t => pairEncode (asmW calls rounds cρ vF b lead (pairEncode (hdr n θ)
            (Strategy.encodeMsgs (pre n θ ++ pairFstD (rs n (xA n θ) (yB n θ) t) :: suf n θ))))
            (out n θ)) (D.distinguisherL n) -
        acceptProb (fun s => pairEncode (asmW calls rounds cρ vF b lead (pairEncode (hdr n θ)
            (Strategy.encodeMsgs (pre n θ ++ pairFstD (is n (xA n θ) (yB n θ) s) :: suf n θ))))
            (out n θ)) (D.distinguisherL n)| ≤ ε₂ n := by
  classical
  -- the gap of an instance
  let K : ∀ n, Θ n → List Bool → List Bool := fun n θ v =>
    pairEncode (asmW calls rounds cρ vF b lead (pairEncode (hdr n θ)
      (Strategy.encodeMsgs (pre n θ ++ v :: suf n θ)))) (out n θ)
  let gap : ∀ n, Θ n → ℝ := fun n θ =>
    |acceptProb (fun t => K n θ (pairFstD (rs n (xA n θ) (yB n θ) t))) (D.distinguisherL n) -
      acceptProb (fun s => K n θ (pairFstD (is n (xA n θ) (yB n θ) s))) (D.distinguisherL n)|
  have hmax : ∀ n, Nonempty (Θ n) → ∃ θs : Θ n, ∀ θ, gap n θ ≤ gap n θs := fun n hn => by
    obtain ⟨θs, -, h⟩ := exists_max_image univ (gap n) univ_nonempty
    exact ⟨θs, fun θ => h θ (mem_univ θ)⟩
  -- the advice: the template of the worst instance
  let β : ℕ → List Bool := fun n => if h : Nonempty (Θ n) then
    tmplW (hdr n (Classical.choose (hmax n h))) (pre n (Classical.choose (hmax n h)))
      (suf n (Classical.choose (hmax n h))) (out n (Classical.choose (hmax n h))) else []
  have hβ : ∀ n, (β n).length ≤ q.eval n := fun n => by
    by_cases h : Nonempty (Θ n)
    · simp only [β, dif_pos h]
      exact hq n _
    · simp only [β, dif_neg h, List.length_nil]
      exact Nat.zero_le _
  obtain ⟨Dh, hc, hDh⟩ := exists_pre D (polyTimeComputable_hybW calls rounds cρ vF b lead) β q hβ
    (.const 0)
  obtain ⟨ε, hε, hbound⟩ := hS Dh
  refine ⟨ε, hε, fun n θ => ?_⟩
  have hn : Nonempty (Θ n) := ⟨θ⟩
  have hθs := Classical.choose_spec (hmax n hn)
  -- `Dh` accepts a sample as `D` accepts the filled template of the worst instance
  have key : ∀ {σ : Type} [Fintype σ] (X : σ → List Bool),
      acceptProb X (Dh.distinguisherL n) =
        acceptProb (fun s => K n (Classical.choose (hmax n hn)) (pairFstD (X s)))
          (D.distinguisherL n) := by
    intro σ _ X
    rw [acceptProb_pre X Dh D (.const 0) n (fun w e => hybW calls rounds cρ vF b lead
      (pairEncode (pairEncode (List.replicate n true) (β n)) (pairEncode w e))) hc (hDh n)]
    refine Eq.trans ?_ (acceptProb_fst (τ := Fin ((PolyExpr.const 0).eval n) → Bool)
      (fun s => K n (Classical.choose (hmax n hn)) (pairFstD (X s))) (D.distinguisherL n))
    refine congrArg (fun f => acceptProb f (D.distinguisherL n)) (funext fun z => ?_)
    simp only [β, dif_pos hn]
    rw [hybW_tmplW]
  have h := hbound n (xA n (Classical.choose (hmax n hn))) (yB n (Classical.choose (hmax n hn)))
  rw [distAdv_def, key, key] at h
  exact (hθs θ).trans h

end TCSlib.Cryptography.SecureComputation.ComposeSim
