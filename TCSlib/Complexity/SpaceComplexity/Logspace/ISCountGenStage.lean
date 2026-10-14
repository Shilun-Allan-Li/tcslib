/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hydroxyi
-/
import TCSlib.Complexity.SpaceComplexity.Logspace.ISCountGenWalk

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# The stages of the window-growing counting machine

The counting part of `Complexity.LogProg.ISGen.igA` [AB09, §4.3.2, proof of Theorem 4.20],
proved with **guarded continuations**:

* the inner enumeration (`guloop`) needs its continuation only when the guessed enumeration
  succeeded with the count `cp`;
* the outer enumeration (`gvloop`) needs its continuation only at counts `c'` reached by a
  successful guessed enumeration;
* the stages (`gstage`), started with the correct count `cp = |C_i|`, therefore reach their
  end (`cmp`) only with the correct final count `cp = |C_K|`, and some branch accepts iff no
  ball `C_{i+1}, …, C_K` contains an accepting code and the continuation at `cmp` accepts.

The last point is what the radius loop needs: its next radius is entered with the true count
of the reachable codes only, so it never has to terminate from a phantom count.

Infrastructure for [AB09, §4.3.2]; not itself a result of the book.

## Main results

* `Complexity.LogProg.ISGen.guloop`, `Complexity.LogProg.ISGen.gvloop`,
  `Complexity.LogProg.ISGen.gstage`.

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009. (§4.3.2, Theorem 4.20.)
-/

namespace Complexity.LogProg

namespace ISGen

open Turing ISCount ISTac

variable {E : ℕ} {orc : Fin 4 → List Bool → Bool} {x : List Bool} {B : ℕ}

/-- **The inner enumeration** (guarded) [AB09, §4.3.2: certifying `v ∉ C_{i+1}` by
enumerating `C_i`]: at `uh`, some branch accepts iff the guessed enumeration of
`u, …, K - 1` (members of `C_i` that are neither `v` nor step to `v`, counted from `cnt`)
ends with the count `cp` and the continuation at `vn` accepts (with `u`, `cnt` cleared);
every branch terminates. The continuation is only needed when the enumeration succeeds.

**Proof sketch.** Induction on `K - u`. At `u = K` compare the count with `cp`. Otherwise
choose: certify `u ∈ C_i` by a walk (`gwalk_spec`), reject if `u = v` or `(u, v)` is a step
pair, count `u`; or skip `u`. The guard is carried along: a counted `u` is a certified
member that is not `v` and does not step to `v`, a skipped one is unconstrained, so success
of the rest of the enumeration implies success of the whole. -/
theorem guloop (Q : Prop) (σ : St) (hσ : σ.Bd B) (hK : σ.K + 1 ≤ B) (hu : σ.u ≤ σ.K)
    (hcnt : σ.cnt ≤ σ.u) (hz : σ.g = 0 ∧ σ.cur = 0 ∧ σ.stp = 0)
    (hQ : GS (fun t => Mem σ.K (RelO orc x σ.s) (InitO orc x σ.s) σ.i t ∧ t ≠ σ.v ∧
          ¬ RelO orc x σ.s t σ.v) (fun _ => True) (fun c => c = σ.cp)
        (σ.K - σ.u) σ.u σ.cnt →
      IG (E := E) orc x B .vn { σ with u := 0, cnt := 0 } Q) :
    IG (E := E) orc x B .uh σ
      (GS (fun t => Mem σ.K (RelO orc x σ.s) (InitO orc x σ.s) σ.i t ∧ t ≠ σ.v ∧
          ¬ RelO orc x σ.s t σ.v) (fun _ => True) (fun c => c = σ.cp ∧ Q)
        (σ.K - σ.u) σ.u σ.cnt) := by
  suffices H : ∀ r (σ : St), σ.K - σ.u = r → σ.Bd B → σ.K + 1 ≤ B → σ.u ≤ σ.K →
      σ.cnt ≤ σ.u → (σ.g = 0 ∧ σ.cur = 0 ∧ σ.stp = 0) →
      (GS (fun t => Mem σ.K (RelO orc x σ.s) (InitO orc x σ.s) σ.i t ∧ t ≠ σ.v ∧
          ¬ RelO orc x σ.s t σ.v) (fun _ => True) (fun c => c = σ.cp) r σ.u σ.cnt →
        IG (E := E) orc x B .vn { σ with u := 0, cnt := 0 } Q) →
      IG (E := E) orc x B .uh σ
        (GS (fun t => Mem σ.K (RelO orc x σ.s) (InitO orc x σ.s) σ.i t ∧ t ≠ σ.v ∧
          ¬ RelO orc x σ.s t σ.v) (fun _ => True) (fun c => c = σ.cp ∧ Q) r σ.u σ.cnt) by
    exact H _ σ rfl hσ hK hu hcnt hz hQ
  intro r
  induction r with
  | zero =>
    intro σ hr hσ hK hu hcnt hz hQ
    refine NSem.jeq_pos rfl (St.greg hσ _ _) (by isr; omega) ?_
    by_cases he : σ.cnt = σ.cp
    · refine (NSem.jeq_pos (P := Q) rfl (St.greg hσ _ _) (by isr; exact he) ?_).congr ?_
      · refine NSem.clr rfl (St.greg hσ _ _) ?_
        isr
        refine NSem.clr rfl (St.greg (by isb) _ _) ?_
        isr
        exact hQ he
      · simp only [GS, he, true_and]
    · refine (NSem.jeq_neg rfl (St.greg hσ _ _) (by isr; exact he)
        (NSem.ret rfl (St.greg hσ _ _))).congr ?_
      simp only [GS, he, false_and, Bool.false_eq_true]
  | succ r ih =>
    intro σ hr hσ hK hu hcnt hz hQ
    obtain ⟨hg, hcur, hstp⟩ := hz
    -- the continuation at `un`: next `u`, with the guard pulled back
    have hnext : ∀ c', c' ≤ σ.u + 1 →
        (GS (fun t => Mem σ.K (RelO orc x σ.s) (InitO orc x σ.s) σ.i t ∧ t ≠ σ.v ∧
            ¬ RelO orc x σ.s t σ.v) (fun _ => True) (fun c => c = σ.cp) r (σ.u + 1) c' →
          GS (fun t => Mem σ.K (RelO orc x σ.s) (InitO orc x σ.s) σ.i t ∧ t ≠ σ.v ∧
            ¬ RelO orc x σ.s t σ.v) (fun _ => True) (fun c => c = σ.cp) (r + 1) σ.u
            σ.cnt) →
        IG (E := E) orc x B .un { σ with cnt := c' }
          (GS (fun t => Mem σ.K (RelO orc x σ.s) (InitO orc x σ.s) σ.i t ∧ t ≠ σ.v ∧
            ¬ RelO orc x σ.s t σ.v) (fun _ => True) (fun c => c = σ.cp ∧ Q) r (σ.u + 1)
            c') := by
      intro c' hc' hpull
      refine NSem.inc rfl (St.greg (by isb) _ _) ?_
      isr
      exact ih { σ with cnt := c', u := σ.u + 1 } (by dsimp only; omega) (by isb) hK
        (by dsimp only; omega) (by dsimp only; omega) ⟨hg, hcur, hstp⟩
        (fun h => IG.of_eq (by ext <;> rfl) (hQ (hpull h)))
    refine NSem.jeq_neg rfl (St.greg hσ _ _) (by isr; omega) ?_
    have hin : Mem σ.K (RelO orc x σ.s) (InitO orc x σ.s) σ.i σ.u →
        IG (E := E) orc x B .uE σ (σ.u ≠ σ.v ∧ ¬ RelO orc x σ.s σ.u σ.v ∧
        GS (fun t => Mem σ.K (RelO orc x σ.s) (InitO orc x σ.s) σ.i t ∧ t ≠ σ.v ∧
          ¬ RelO orc x σ.s t σ.v) (fun _ => True) (fun c => c = σ.cp ∧ Q) r (σ.u + 1)
          (σ.cnt + 1)) := by
      intro hmem
      by_cases he : σ.u = σ.v
      · refine (NSem.jeq_pos rfl (St.greg hσ _ _) (by isr; exact he)
          (NSem.ret rfl (St.greg hσ _ _))).congr ?_
        simp [he]
      refine NSem.jeq_neg rfl (St.greg hσ _ _) (by isr; exact he) ?_
      by_cases hr' : RelO orc x σ.s σ.u σ.v
      · refine (nsem_call₃_pos rfl (St.greg hσ _ _) (by isr; exact hr')
          (NSem.ret rfl (St.greg hσ _ _))).congr ?_
        simp [hr']
      refine nsem_call₃_neg rfl (St.greg hσ _ _) (by isr; simpa [SavitchARM.Rel] using hr') ?_
      refine NSem.inc rfl (St.greg hσ _ _) ?_
      isr
      exact (hnext (σ.cnt + 1) (by omega)
        (fun h => Or.inl ⟨⟨hmem, he, hr'⟩, h⟩)).congr (by simp [he, hr'])
    have hw := gwalk_spec true _ σ hσ hK
      (fun hm => IG.of_eq (by ext <;> simp [hg, hcur, hstp]) (hin (by simpa [St.wb, St.wt]
        using hm)))
    have hskip := hnext σ.cnt (by omega) (fun h => Or.inr ⟨trivial, h⟩)
    refine (NSem.choose (A := igA E) (l := .uch) rfl (St.greg hσ _ _) hw
      (IG.of_eq (by ext <;> rfl) hskip)).congr ?_
    simp only [GS, St.wb, St.wt, if_true, true_and, and_assoc]

/-- **The outer enumeration** (guarded) [AB09, §4.3.2: computing `|C_{i+1}|`]: at `vh`, some
branch accepts iff the guessed enumeration of `v, …, K - 1` (members of `C_{i1}` certified by
walks and not accepting; non-members certified by the inner enumeration with count `cp`),
counted from `c`, ends with a count accepted by the continuation at `se`; every branch
terminates. The continuation is only needed at counts `c'` that a successful enumeration
ends with.

**Proof sketch.** Induction on `K - v`. At `v = K` go to the stage end. Otherwise choose:
certify `v ∈ C_{i+1}` by a walk (`gwalk_spec`), reject if `v` is accepting, count `v`; or
certify `v ∉ C_{i+1}` by the inner enumeration (`guloop`). The guard is carried along: a
counted `v` is a certified non-accepting member, a skipped one a certified non-member, so
success of the rest of the enumeration implies success of the whole. -/
theorem gvloop (Kont : ℕ → Prop) (σ : St) (hσ : σ.Bd B) (hK : σ.K + 1 ≤ B)
    (hv : σ.v ≤ σ.K) (hc : σ.c ≤ σ.v) (hz : σ.Clear)
    (hKont : ∀ c', c' ≤ σ.K →
      GS (fun t => Mem σ.K (RelO orc x σ.s) (InitO orc x σ.s) σ.i1 t ∧ ¬ AccO orc x σ.s t)
        (fun t => GS (fun u => Mem σ.K (RelO orc x σ.s) (InitO orc x σ.s) σ.i u ∧ u ≠ t ∧
          ¬ RelO orc x σ.s u t) (fun _ => True) (fun c => c = σ.cp) σ.K 0 0)
        (fun c => c = c') (σ.K - σ.v) σ.v σ.c →
      IG (E := E) orc x B .se { σ with v := σ.K, c := c' } (Kont c')) :
    IG (E := E) orc x B .vh σ
      (GS (fun t => Mem σ.K (RelO orc x σ.s) (InitO orc x σ.s) σ.i1 t ∧ ¬ AccO orc x σ.s t)
        (fun t => GS (fun u => Mem σ.K (RelO orc x σ.s) (InitO orc x σ.s) σ.i u ∧ u ≠ t ∧
          ¬ RelO orc x σ.s u t) (fun _ => True) (fun c => c = σ.cp) σ.K 0 0)
        Kont (σ.K - σ.v) σ.v σ.c) := by
  suffices H : ∀ r (σ : St), σ.K - σ.v = r → σ.Bd B → σ.K + 1 ≤ B → σ.v ≤ σ.K →
      σ.c ≤ σ.v → σ.Clear →
      (∀ c', c' ≤ σ.K →
        GS (fun t => Mem σ.K (RelO orc x σ.s) (InitO orc x σ.s) σ.i1 t ∧ ¬ AccO orc x σ.s t)
          (fun t => GS (fun u => Mem σ.K (RelO orc x σ.s) (InitO orc x σ.s) σ.i u ∧ u ≠ t ∧
            ¬ RelO orc x σ.s u t) (fun _ => True) (fun c => c = σ.cp) σ.K 0 0)
          (fun c => c = c') r σ.v σ.c →
        IG (E := E) orc x B .se { σ with v := σ.K, c := c' } (Kont c')) →
      IG (E := E) orc x B .vh σ
        (GS (fun t => Mem σ.K (RelO orc x σ.s) (InitO orc x σ.s) σ.i1 t ∧ ¬ AccO orc x σ.s t)
          (fun t => GS (fun u => Mem σ.K (RelO orc x σ.s) (InitO orc x σ.s) σ.i u ∧ u ≠ t ∧
            ¬ RelO orc x σ.s u t) (fun _ => True) (fun c => c = σ.cp) σ.K 0 0)
          Kont r σ.v σ.c) by
    exact H _ σ rfl hσ hK hv hc hz hKont
  intro r
  induction r with
  | zero =>
    intro σ hr hσ hK hv hc hz hKont
    have he : σ.v = σ.K := by omega
    refine NSem.jeq_pos rfl (St.greg hσ _ _) (by isr; exact he) ?_
    exact IG.of_eq (by ext <;> simp [he]) (hKont σ.c (by omega) rfl)
  | succ r ih =>
    intro σ hr hσ hK hv hc hz hKont
    obtain ⟨hg, hcur, hstp, hu, hcnt⟩ := hz
    -- the continuation at `vn`: next `v`, with the guard pulled back
    have hnext : ∀ c', c' ≤ σ.v + 1 →
        (∀ c'', GS (fun t => Mem σ.K (RelO orc x σ.s) (InitO orc x σ.s) σ.i1 t ∧
              ¬ AccO orc x σ.s t)
            (fun t => GS (fun u => Mem σ.K (RelO orc x σ.s) (InitO orc x σ.s) σ.i u ∧ u ≠ t ∧
              ¬ RelO orc x σ.s u t) (fun _ => True) (fun c => c = σ.cp) σ.K 0 0)
            (fun c => c = c'') r (σ.v + 1) c' →
          GS (fun t => Mem σ.K (RelO orc x σ.s) (InitO orc x σ.s) σ.i1 t ∧
              ¬ AccO orc x σ.s t)
            (fun t => GS (fun u => Mem σ.K (RelO orc x σ.s) (InitO orc x σ.s) σ.i u ∧ u ≠ t ∧
              ¬ RelO orc x σ.s u t) (fun _ => True) (fun c => c = σ.cp) σ.K 0 0)
            (fun c => c = c'') (r + 1) σ.v σ.c) →
        IG (E := E) orc x B .vn { σ with c := c' }
          (GS (fun t => Mem σ.K (RelO orc x σ.s) (InitO orc x σ.s) σ.i1 t ∧
              ¬ AccO orc x σ.s t)
            (fun t => GS (fun u => Mem σ.K (RelO orc x σ.s) (InitO orc x σ.s) σ.i u ∧ u ≠ t ∧
              ¬ RelO orc x σ.s u t) (fun _ => True) (fun c => c = σ.cp) σ.K 0 0)
            Kont r (σ.v + 1) c') := by
      intro c' hc' hpull
      refine NSem.inc rfl (St.greg (by isb) _ _) ?_
      isr
      exact ih { σ with c := c', v := σ.v + 1 } (by dsimp only; omega) (by isb) hK
        (by dsimp only; omega) (by dsimp only; omega) ⟨hg, hcur, hstp, hu, hcnt⟩
        (fun c'' hc'' h => IG.of_eq (by ext <;> rfl) (hKont c'' hc'' (hpull c'' h)))
    refine NSem.jeq_neg rfl (St.greg hσ _ _) (by isr; omega) ?_
    -- the member branch
    have hin : Mem σ.K (RelO orc x σ.s) (InitO orc x σ.s) σ.i1 σ.v →
        IG (E := E) orc x B .vA σ (¬ AccO orc x σ.s σ.v ∧
        GS (fun t => Mem σ.K (RelO orc x σ.s) (InitO orc x σ.s) σ.i1 t ∧ ¬ AccO orc x σ.s t)
          (fun t => GS (fun u => Mem σ.K (RelO orc x σ.s) (InitO orc x σ.s) σ.i u ∧ u ≠ t ∧
            ¬ RelO orc x σ.s u t) (fun _ => True) (fun c => c = σ.cp) σ.K 0 0)
          Kont r (σ.v + 1) (σ.c + 1)) := by
      intro hmem
      by_cases ha : AccO orc x σ.s σ.v
      · refine (nsem_call₂_pos rfl (St.greg hσ _ _) (by isr; exact ha)
          (NSem.ret rfl (St.greg hσ _ _))).congr ?_
        simp [ha]
      refine nsem_call₂_neg rfl (St.greg hσ _ _) (by isr; simpa [SavitchARM.AccO] using ha) ?_
      refine NSem.inc rfl (St.greg hσ _ _) ?_
      isr
      exact (hnext (σ.c + 1) (by omega)
        (fun c'' h => Or.inl ⟨⟨hmem, ha⟩, h⟩)).congr (by simp [ha])
    have hw := gwalk_spec false _ σ hσ hK
      (fun hm => IG.of_eq (by ext <;> simp [hg, hcur, hstp]) (hin (by simpa [St.wb, St.wt]
        using hm)))
    -- the non-member branch
    have hout : IG (E := E) orc x B .uI σ
        (GS (fun u => Mem σ.K (RelO orc x σ.s) (InitO orc x σ.s) σ.i u ∧ u ≠ σ.v ∧
            ¬ RelO orc x σ.s u σ.v) (fun _ => True) (fun c => c = σ.cp) σ.K 0 0 ∧
          GS (fun t => Mem σ.K (RelO orc x σ.s) (InitO orc x σ.s) σ.i1 t ∧ ¬ AccO orc x σ.s t)
            (fun t => GS (fun u => Mem σ.K (RelO orc x σ.s) (InitO orc x σ.s) σ.i u ∧ u ≠ t ∧
              ¬ RelO orc x σ.s u t) (fun _ => True) (fun c => c = σ.cp) σ.K 0 0)
            Kont r (σ.v + 1) σ.c) := by
      refine NSem.clr rfl (St.greg hσ _ _) ?_
      isr
      refine NSem.clr rfl (St.greg (by isb) _ _) ?_
      isr
      have hU := guloop (E := E) (orc := orc) (x := x) _ { σ with u := 0, cnt := 0 }
        (by isb) hK (Nat.zero_le _) le_rfl ⟨hg, hcur, hstp⟩
        (fun hgs => IG.of_eq (by ext <;> simp [hu, hcnt])
          (hnext σ.c (by omega) (fun c'' h => Or.inr ⟨by simpa using hgs, h⟩)))
      refine hU.congr ?_
      simp only [Nat.sub_zero]
      exact gs_and _ _ _ _ _ _ _
    refine (NSem.choose (A := igA E) (l := .vch) rfl (St.greg hσ _ _) hw hout).congr ?_
    simp only [GS, St.wb, St.wt, Bool.false_eq_true, if_false, and_assoc]

/-- **The stages with the correct count** [AB09, §4.3.2]: at `sh` with stage `i ≤ K`,
`i1 = i + 1` and the correct previous count `cp = |C_i|`, some branch accepts iff none of the
balls `C_{i+1}, …, C_K` contains an accepting code and the continuation at `cmp` accepts,
where it is entered with `i = K`, `i1 = K + 1` and `cp = |C_K|` (and some values of `v`,
`c`); every branch terminates.

**Proof sketch.** Induction on `K - i`. At `i = K` go to `cmp`. Otherwise clear `v`, `c` and
run the outer enumeration (`gvloop`); a successful enumeration has count `|C_{i+1}|` and no
accepting member (`gs_outer`, with the inner enumeration certifying exactly non-membership,
`gs_inner`, `not_mem_succ_iff`), so the stage end copies the correct count into `cp`
(`nsem_copy`), increments `i`, `i1` and recurs. -/
theorem gstage (Q : Prop) (σ : St) (hσ : σ.Bd B) (hK : σ.K + 1 ≤ B) (hi : σ.i ≤ σ.K)
    (hi1 : σ.i1 = σ.i + 1)
    (hcp : σ.cp = (ball σ.K (RelO orc x σ.s) (InitO orc x σ.s) σ.i).card) (hz : σ.Clear)
    (hQ : ∀ v' c', v' ≤ B → c' ≤ B →
      IG (E := E) orc x B .cmp
        { σ with i := σ.K, i1 := σ.K + 1, v := v', c := c',
                 cp := (ball σ.K (RelO orc x σ.s) (InitO orc x σ.s) σ.K).card } Q) :
    IG (E := E) orc x B .sh σ
      ((∀ j, σ.i < j → j ≤ σ.K →
        ∀ t ∈ ball σ.K (RelO orc x σ.s) (InitO orc x σ.s) j, ¬ AccO orc x σ.s t) ∧ Q) := by
  suffices H : ∀ r (σ : St), σ.K - σ.i = r → σ.Bd B → σ.K + 1 ≤ B → σ.i ≤ σ.K →
      σ.i1 = σ.i + 1 → σ.cp = (ball σ.K (RelO orc x σ.s) (InitO orc x σ.s) σ.i).card →
      σ.Clear →
      (∀ v' c', v' ≤ B → c' ≤ B →
        IG (E := E) orc x B .cmp
          { σ with i := σ.K, i1 := σ.K + 1, v := v', c := c',
                   cp := (ball σ.K (RelO orc x σ.s) (InitO orc x σ.s) σ.K).card } Q) →
      IG (E := E) orc x B .sh σ
        ((∀ j, σ.i < j → j ≤ σ.K →
          ∀ t ∈ ball σ.K (RelO orc x σ.s) (InitO orc x σ.s) j, ¬ AccO orc x σ.s t) ∧ Q) by
    exact H _ σ rfl hσ hK hi hi1 hcp hz hQ
  intro r
  induction r with
  | zero =>
    intro σ hr hσ hK hi hi1 hcp hz hQ
    have he : σ.i = σ.K := by omega
    refine (NSem.jeq_pos rfl (St.greg hσ _ _) (by isr; exact he)
      (IG.of_eq ?_ (hQ σ.v σ.c (by isb) (by isb)))).congr ?_
    · ext <;> simp [he, hi1, hcp]
    · constructor
      · intro h; exact ⟨fun j h1 h2 => by omega, h⟩
      · exact fun h => h.2
  | succ r ih =>
    intro σ hr hσ hK hi hi1 hcp hz hQ
    have hlt : σ.i ≠ σ.K := by omega
    refine NSem.jeq_neg rfl (St.greg hσ _ _) (by isr; exact hlt) ?_
    refine NSem.clr rfl (St.greg hσ _ _) ?_
    isr
    refine NSem.clr rfl (St.greg (by isb) _ _) ?_
    isr
    obtain ⟨hg, hcur, hstp, hu, hcnt⟩ := hz
    -- the out-guesses certify exactly non-membership in `C_{i+1}`
    have hB : ∀ t < σ.K, GS (fun u => Mem σ.K (RelO orc x σ.s) (InitO orc x σ.s) σ.i u ∧
        u ≠ t ∧ ¬ RelO orc x σ.s u t) (fun _ => True) (fun c => c = σ.cp) σ.K 0 0 ↔
        ¬ Mem σ.K (RelO orc x σ.s) (InitO orc x σ.s) σ.i1 t := by
      intro t ht
      rw [hcp, gs_inner, hi1, not_mem_succ_iff ht]
    refine (gvloop (fun c' => (∀ j, σ.i + 1 < j → j ≤ σ.K →
        ∀ t ∈ ball σ.K (RelO orc x σ.s) (InitO orc x σ.s) j, ¬ AccO orc x σ.s t) ∧ Q)
        { σ with v := 0, c := 0 } (by isb) hK (Nat.zero_le _) le_rfl
        ⟨hg, hcur, hstp, hu, hcnt⟩ (fun c' hc' hgs => ?_)).congr ?_
    · -- the stage end, entered with the correct count
      dsimp only at hc' hgs ⊢
      rw [Nat.sub_zero, gs_outer _ _ _ hB] at hgs
      obtain ⟨-, hcc⟩ := hgs
      rw [hi1] at hcc
      refine NSem.clr rfl (St.greg (by isb) _ _) ?_
      isr
      refine nsem_copy (igA E) orc x B rcp rc (by decide) .sec .sinc .si rfl rfl _ _
        (St.greg (E := E) (by isb) none none) (by simp) ?_
      isr
      refine NSem.inc rfl (St.greg (by isb) _ _) ?_
      isr
      refine NSem.inc rfl (St.greg (by isb) _ _) ?_
      isr
      exact ih { σ with v := σ.K, c := c', cp := c', i := σ.i + 1, i1 := σ.i1 + 1 }
        (by dsimp only; omega) (by isb) hK (by dsimp only; omega) (by dsimp only; omega)
        (by dsimp only; exact hcc.symm) ⟨hg, hcur, hstp, hu, hcnt⟩
        (fun v' c'' hv' hc'' => IG.of_eq (by ext <;> rfl) (hQ v' c'' hv' hc''))
    · dsimp only
      rw [Nat.sub_zero, gs_outer _ _ _ hB, hi1]
      constructor
      · rintro ⟨h1, h2, hq⟩
        refine ⟨fun j hj1 hj2 => ?_, hq⟩
        rcases Nat.eq_or_lt_of_le hj1 with h | h
        · subst h; exact h1
        · exact h2 j h hj2
      · rintro ⟨h, hq⟩
        exact ⟨h (σ.i + 1) (by omega) (by omega), fun j h1 h2 => h j (by omega) h2, hq⟩

end ISGen

end Complexity.LogProg
