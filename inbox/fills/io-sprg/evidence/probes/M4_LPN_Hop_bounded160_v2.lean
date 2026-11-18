/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TCSlib.Cryptography.Obfuscation.StructuredSeed.Reductions.LPN.Sections

set_option maxHeartbeats 500000
set_option diagnostics true
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Actual-law LPN averaging and the selected hybrid hop

## Main definitions

None; this module proves properties of the imported reduction interface.

## Main results

* Pointwise preprocessing identities and fixed-advice section acceptances.
* Actual-nuisance-law advice fixing before every realizer.
* `Params.lpn_hop` with its unchanged full statement.

## References

* [JLS26] A. Jain, H. Lin, A. Sahai, *Indistinguishability Obfuscation from Well-Founded
  Assumptions*, J. ACM 73(1), Article 1, February 2026, Lemma 4.2, p. 19.
* [PS10] R. Pass, A. Shelat, *A Course in Cryptography*, 2010, Definition 26.8.

**Deviations.** Dv8 and Dv12 retain the actual independent nuisance law and global advice family.
Dv16 quantifies every realizer of the same layout-only explicit reduction.
-/

namespace TCSlib.Cryptography.Obfuscation.StructuredSeed

open Complexity Turing
open scoped BigOperators

namespace Internal

-- Specialized pointwise/section/averaging helpers may be added here after the split.

/-- One advice tuple dominates the adjacent LPN chain gap under the actual nuisance law.
Averaging glue for [JLS26, Lemma 4.2, p. 19]. No realizer occurs in this statement.

**Proof sketch.** Keep the actual generator draw, buckets, seed, repetition table, uniform
public vectors and comparison tail in one finite nuisance product. The fixed-advice section
identities expose the canonical challenged matrix and fresh selected value. Compose the
existing typed product/Fubini laws, move that matrix before the seed/table, and use the
public coordinate-resampling law. The two acceptance probabilities are therefore averages
under the same actual law. Absolute-gap convexity and the existing finite averaging selector
fix one tuple before any machine realizer is introduced. -/
theorem lpn_fix_advice (P : Params) (π : PrimeSchedule) (A : NUPPT) (L : ℕ)
    (h : L = P.ℓ (P.kappaOf L)) (tailReal : Bool)
    (hop : Fin (P.kappaOf L + 1)) (hhop : hop.val < P.kappaOf L) :
    ∃ w : P.LPNAdvice π L,
      Games.advantage (P.chainGame A tailReal hop.val (P.kappaOf L) (π (P.kappaOf L)))
        (P.chainGame A tailReal (hop.val + 1) (P.kappaOf L) (π (P.kappaOf L))) ≤
      LWE.decisionAdvantage ((P.lpnFamily_raw π).toLWE.parameters L)
        ((P.lpnFamily_raw π).toLWE.noise L)
        (fun x (r : A.Coins (P.kappaOf L)) =>
          decide (A.runAtL (P.kappaOf L) (P.lpnPre π L w x) (List.ofFn r) = [true])) := by
  classical
  let κ := P.kappaOf L
  let pp := π κ
  let GDraw := P.G.IdDraw (P.n κ)
  let Buck := Fin (P.m κ) → Fin (P.B κ)
  let Seed := Fin (P.n κ) → Bool
  let Rep := (Fin (P.ℓ κ) → ZMod pp.p) ×
    (Fin (P.n κ) → Fin (P.W κ) × ZMod pp.p)
  let Table := Fin κ → Rep
  let V := Fin (P.n κ) → ZMod pp.p
  let U := Fin κ → V
  let Tail := Fin (P.m κ) → Bool
  let Post := U × Tail
  let Mat := Matrix (Fin (P.n κ)) (Fin (P.ℓ κ)) (ZMod pp.p)
  let Coins := A.Coins κ
  let Ω := GDraw × (Buck × (Seed × (Table × Post)))
  let avg (α : Type) [Fintype α] [Nonempty α] (f : α → ℝ) : ℝ :=
    Games.ProbComp.expect (Games.ProbComp.sample α) f
  let k : Fin κ := ⟨hop.val, hhop⟩
  let mk : Ω → P.LPNAdvice π L := fun ν =>
    { hop := hop
      I := P.G.idCore (P.n κ) ν.1
      buckets := ν.2.1
      draw := (ν.2.2.1, ν.2.2.2.1)
      uniform := ν.2.2.2.2.1
      tail := if tailReal then
        fun j => P.G.eval (P.n κ) (P.G.idCore (P.n κ) ν.1) ν.2.2.1 (P.outputIndex κ j)
        else ν.2.2.2.2.2 }
  let disc : Ω → P.LPNChal π L → Coins → Bool := fun ν x r =>
    decide (A.runAtL κ (P.lpnPre π L (mk ν) x) (List.ofFn r) = [true])
  let R : Ω → ℝ := fun ν => acceptProb
    (LWE.sample ((P.lpnFamily_raw π).toLWE.parameters L)
      ((P.lpnFamily_raw π).toLWE.noise L)) (disc ν)
  let Uacc : Ω → ℝ := fun ν => acceptProb (id : P.LPNChal π L → _) (disc ν)
  let F : ℕ → GDraw → Buck → Seed → Mat → Table → Post → Coins → ℝ :=
    fun i g b σ M table post r =>
      if A.runAtL κ
        (P.challengeStr κ pp (P.G.idCore (P.n κ) g, b, M)
          (P.publicSeed κ pp
            (P.chainPublic κ pp (P.G.idCore (P.n κ) g, b, M) (σ, table) post.1 i) false)
          (if tailReal then
            fun j => P.G.eval (P.n κ) (P.G.idCore (P.n κ) g) σ (P.outputIndex κ j)
            else post.2)) (List.ofFn r) = [true] then 1 else 0
  let C : ℕ → ℝ := fun i => avg GDraw (fun g => avg Buck (fun b => avg Mat (fun M =>
    avg Seed (fun σ => avg Table (fun t => avg Post (fun post =>
      avg Coins (fun r => F i g b σ M t post r)))))))
  have hpairPost (f : Post → ℝ) :
      avg Post f = avg U (fun u => avg Tail (fun t => f (u, t))) := ?_
  swap
  · simpa only [avg, Games.ProbComp.expect_bind, Games.ProbComp.expect_pure] using
      (Games.Bridge.expect_sample_pair (α := U) (β := Tail) f).symm
  have hsplit (f : Ω → ℝ) : avg Ω f =
      avg GDraw (fun g => avg Buck (fun b => avg Seed (fun σ =>
        avg Table (fun t => avg Post (fun post => f (g, b, σ, t, post)))))) := ?_
  swap
  · dsimp only [avg]
    rw [← Games.Bridge.expect_sample_pair (α := GDraw)
      (β := Buck × (Seed × (Table × Post))) f]
    simp only [Games.ProbComp.expect_bind, Games.ProbComp.expect_pure]
    apply congrArg (Games.ProbComp.expect (Games.ProbComp.sample GDraw))
    funext g
    rw [← Games.Bridge.expect_sample_pair (α := Buck) (β := Seed × (Table × Post))
      (fun z : Buck × (Seed × (Table × Post)) => f (g, z))]
    simp only [Games.ProbComp.expect_bind, Games.ProbComp.expect_pure]
    apply congrArg (Games.ProbComp.expect (Games.ProbComp.sample Buck))
    funext b
    rw [← Games.Bridge.expect_sample_pair (α := Seed) (β := Table × Post)
      (fun z : Seed × (Table × Post) => f (g, b, z))]
    simp only [Games.ProbComp.expect_bind, Games.ProbComp.expect_pure]
    apply congrArg (Games.ProbComp.expect (Games.ProbComp.sample Seed))
    funext σ
    rw [← Games.Bridge.expect_sample_pair (α := Table) (β := Post)
      (fun z : Table × Post => f (g, b, σ, z))]
    simp only [Games.ProbComp.expect_bind, Games.ProbComp.expect_pure]
  have hmove (G : Seed → Table → Post → Mat → ℝ) :
      avg Seed (fun σ => avg Table (fun t => avg Post (fun post =>
        avg Mat (fun M => G σ t post M)))) =
      avg Mat (fun M => avg Seed (fun σ => avg Table (fun t =>
        avg Post (fun post => G σ t post M)))) := ?_
  swap
  · have hp (σ : Seed) (t : Table) :
        avg Post (fun post => avg Mat (fun M => G σ t post M)) =
          avg Mat (fun M => avg Post (fun post => G σ t post M)) :=
      Games.ProbComp.expect_sample_comm (α := Post) (β := Mat)
        (fun (post : Post) (M : Mat) => G σ t post M)
    have ht (σ : Seed) :
        avg Table (fun t => avg Mat (fun M => avg Post (fun post => G σ t post M))) =
          avg Mat (fun M => avg Table (fun t => avg Post (fun post => G σ t post M))) :=
      Games.ProbComp.expect_sample_comm (α := Table) (β := Mat)
        (fun (t : Table) (M : Mat) => avg Post (fun post => G σ t post M))
    calc
      avg Seed (fun σ => avg Table (fun t => avg Post (fun post =>
          avg Mat (fun M => G σ t post M)))) =
        avg Seed (fun σ => avg Table (fun t => avg Mat (fun M =>
          avg Post (fun post => G σ t post M)))) :=
        congrArg (avg Seed) (funext fun σ => congrArg (avg Table) (funext fun t => hp σ t))
      _ = avg Seed (fun σ => avg Mat (fun M => avg Table (fun t =>
          avg Post (fun post => G σ t post M)))) := congrArg (avg Seed) (funext ht)
      _ = avg Mat (fun M => avg Seed (fun σ => avg Table (fun t =>
          avg Post (fun post => G σ t post M)))) :=
        Games.ProbComp.expect_sample_comm (α := Seed) (β := Mat)
          (fun (σ : Seed) (M : Mat) => avg Table (fun t => avg Post (fun p => G σ t p M)))
  have hupdateTable (G : Table → Post → Coins → ℝ) :
      avg Table (fun t => avg Post (fun post => avg Rep (fun fresh =>
        avg Coins (fun r => G (Function.update t k fresh) post r)))) =
      avg Table (fun t => avg Post (fun post => avg Coins (fun r => G t post r))) := ?_
  swap
  · have hs (t : Table) :
        avg Post (fun post => avg Rep (fun fresh =>
          avg Coins (fun r => G (Function.update t k fresh) post r))) =
        avg Rep (fun fresh => avg Post (fun post =>
          avg Coins (fun r => G (Function.update t k fresh) post r))) :=
      Games.ProbComp.expect_sample_comm (α := Post) (β := Rep)
        (fun (post : Post) (fresh : Rep) =>
          avg Coins (fun r => G (Function.update t k fresh) post r))
    exact (congrArg (avg Table) (funext hs)).trans
      (Games.ProbComp.expect_sample_update k
        (fun t : Table => avg Post (fun post => avg Coins (fun r => G t post r))))
  have hupdateUniform (G : U → Tail → Coins → ℝ) :
      avg U (fun u => avg Tail (fun t => avg V (fun fresh =>
        avg Coins (fun r => G (Function.update u k fresh) t r)))) =
      avg U (fun u => avg Tail (fun t => avg Coins (fun r => G u t r))) := ?_
  swap
  · have hs (u : U) :
        avg Tail (fun t => avg V (fun fresh =>
          avg Coins (fun r => G (Function.update u k fresh) t r))) =
        avg V (fun fresh => avg Tail (fun t =>
          avg Coins (fun r => G (Function.update u k fresh) t r))) :=
      Games.ProbComp.expect_sample_comm (α := Tail) (β := V)
        (fun (t : Tail) (fresh : V) =>
          avg Coins (fun r => G (Function.update u k fresh) t r))
    exact (congrArg (avg U) (funext hs)).trans
      (Games.ProbComp.expect_sample_update k
        (fun u : U => avg Tail (fun t => avg Coins (fun r => G u t r))))
  have hupdatePost (G : Post → Coins → ℝ) :
      avg Post (fun post => avg V (fun fresh =>
        avg Coins (fun r => G (Function.update post.1 k fresh, post.2) r))) =
      avg Post (fun post => avg Coins (fun r => G post r)) := ?_
  swap
  · calc
      avg Post (fun post => avg V (fun fresh =>
          avg Coins (fun r => G (Function.update post.1 k fresh, post.2) r))) =
        avg U (fun u => avg Tail (fun t => avg V (fun fresh =>
          avg Coins (fun r => G (Function.update u k fresh, t) r)))) :=
        hpairPost (fun post : Post => avg V (fun fresh =>
          avg Coins (fun r => G (Function.update post.1 k fresh, post.2) r)))
      _ = avg U (fun u => avg Tail (fun t => avg Coins (fun r => G (u, t) r))) :=
        hupdateUniform (fun (u : U) (t : Tail) (r : Coins) => G (u, t) r)
      _ = avg Post (fun post => avg Coins (fun r => G post r)) :=
        (hpairPost (fun post : Post => avg Coins (fun r => G post r))).symm
  have hsecR (ν : Ω) : R ν = avg Mat (fun M => avg Rep (fun fresh =>
      avg Coins (fun r => F hop.val ν.1 ν.2.1 ν.2.2.1 M
        (Function.update ν.2.2.2.1 k fresh) ν.2.2.2.2 r))) := ?_
  swap
  · simpa only [R, disc, mk, F, avg] using lpn_real_section P π A L h (mk ν) k rfl
  have hsecU (ν : Ω) : Uacc ν = avg Mat (fun M => avg V (fun fresh =>
      avg Coins (fun r => F (hop.val + 1) ν.1 ν.2.1 ν.2.2.1 M ν.2.2.2.1
        (Function.update ν.2.2.2.2.1 k fresh, ν.2.2.2.2.2) r))) := ?_
  swap
  · simpa only [Uacc, disc, mk, F, avg] using
      lpn_uniform_section P π A L h (mk ν) k rfl
  have hrealAvg : avg Ω R = C hop.val := ?_
  swap
  · rw [hsplit R]
    dsimp only [C]
    apply congrArg (avg GDraw)
    funext g
    apply congrArg (avg Buck)
    funext b
    calc
      avg Seed (fun σ => avg Table (fun t => avg Post (fun post => R (g, b, σ, t, post)))) =
        avg Seed (fun σ => avg Table (fun t => avg Post (fun post => avg Mat (fun M =>
          avg Rep (fun fresh => avg Coins (fun r =>
            F hop.val g b σ M (Function.update t k fresh) post r)))))) :=
        congrArg (avg Seed) (funext fun σ => congrArg (avg Table) (funext fun t =>
          congrArg (avg Post) (funext fun post => hsecR (g, b, σ, t, post))))
      _ = avg Mat (fun M => avg Seed (fun σ => avg Table (fun t => avg Post (fun post =>
          avg Rep (fun fresh => avg Coins (fun r =>
            F hop.val g b σ M (Function.update t k fresh) post r)))))) :=
        hmove (fun (σ : Seed) (t : Table) (post : Post) (M : Mat) =>
          avg Rep (fun fresh => avg Coins (fun r =>
            F hop.val g b σ M (Function.update t k fresh) post r)))
      _ = avg Mat (fun M => avg Seed (fun σ => avg Table (fun t => avg Post (fun post =>
          avg Coins (fun r => F hop.val g b σ M t post r))))) :=
        congrArg (avg Mat) (funext fun M => congrArg (avg Seed) (funext fun σ =>
          hupdateTable (fun (t : Table) (post : Post) (r : Coins) => F hop.val g b σ M t post r)))
  have huniformAvg : avg Ω Uacc = C (hop.val + 1) := ?_
  swap
  · rw [hsplit Uacc]
    dsimp only [C]
    apply congrArg (avg GDraw)
    funext g
    apply congrArg (avg Buck)
    funext b
    calc
      avg Seed (fun σ => avg Table (fun t => avg Post (fun post =>
          Uacc (g, b, σ, t, post)))) =
        avg Seed (fun σ => avg Table (fun t => avg Post (fun post => avg Mat (fun M =>
          avg V (fun fresh => avg Coins (fun r =>
            F (hop.val + 1) g b σ M t (Function.update post.1 k fresh, post.2) r)))))) :=
        congrArg (avg Seed) (funext fun σ => congrArg (avg Table) (funext fun t =>
          congrArg (avg Post) (funext fun post => hsecU (g, b, σ, t, post))))
      _ = avg Mat (fun M => avg Seed (fun σ => avg Table (fun t => avg Post (fun post =>
          avg V (fun fresh => avg Coins (fun r =>
            F (hop.val + 1) g b σ M t (Function.update post.1 k fresh, post.2) r)))))) :=
        hmove (fun (σ : Seed) (t : Table) (post : Post) (M : Mat) =>
          avg V (fun fresh => avg Coins (fun r =>
            F (hop.val + 1) g b σ M t (Function.update post.1 k fresh, post.2) r)))
      _ = avg Mat (fun M => avg Seed (fun σ => avg Table (fun t => avg Post (fun post =>
          avg Coins (fun r => F (hop.val + 1) g b σ M t post r))))) :=
        congrArg (avg Mat) (funext fun M => congrArg (avg Seed) (funext fun σ =>
          congrArg (avg Table) (funext fun t => hupdatePost
            (fun (post : Post) (r : Coins) => F (hop.val + 1) g b σ M t post r))))
  have hchain (i : ℕ) : Games.accept (P.chainGame A tailReal i κ pp) = C i := ?_
  swap
  · rw [P.chainGame_eq, Games.accept_eq, Games.ProbComp.prob_eq_expect]
    simp only [P.idSamp'_eq, Games.ProbComp.expect_bind, Games.ProbComp.expect_map,
      Games.OracleComp.pure_eq_pure, Games.ProbComp.expect_pure, P.idCore_eq,
      NUPPT.distinguisherL_eq,
      NUPPT.runAt_eq, decide_eq_true_eq]
    change avg (GDraw × (Buck × Mat)) (fun ix => avg (Seed × Table) (fun d =>
      avg U (fun u => avg Tail (fun t => avg Coins (fun r =>
        F i ix.1 ix.2.1 d.1 ix.2.2 d.2 (u, t) r))))) = C i
    dsimp only [C, avg]
    rw [← Games.Bridge.expect_sample_pair (α := GDraw) (β := Buck × Mat)
      (fun ix : GDraw × (Buck × Mat) => avg (Seed × Table) (fun d =>
        avg U (fun u => avg Tail (fun t => avg Coins (fun r =>
          F i ix.1 ix.2.1 d.1 ix.2.2 d.2 (u, t) r)))))]
    simp only [Games.ProbComp.expect_bind, Games.ProbComp.expect_pure]
    apply congrArg (avg GDraw)
    funext g
    rw [← Games.Bridge.expect_sample_pair (α := Buck) (β := Mat)
      (fun z : Buck × Mat => avg (Seed × Table) (fun d =>
        avg U (fun u => avg Tail (fun t => avg Coins (fun r =>
          F i g z.1 d.1 z.2 d.2 (u, t) r)))))]
    simp only [Games.ProbComp.expect_bind, Games.ProbComp.expect_pure]
    apply congrArg (avg Buck)
    funext b
    apply congrArg (avg Mat)
    funext M
    rw [← Games.Bridge.expect_sample_pair (α := Seed) (β := Table)
      (fun d : Seed × Table => avg U (fun u => avg Tail (fun t =>
        avg Coins (fun r => F i g b d.1 M d.2 (u, t) r))))]
    simp only [Games.ProbComp.expect_bind, Games.ProbComp.expect_pure]
    apply congrArg (avg Seed)
    funext σ
    apply congrArg (avg Table)
    funext table
    exact (hpairPost (fun post : Post =>
      avg Coins (fun r => F i g b σ M table post r))).symm
  have hreal : Games.accept (P.chainGame A tailReal hop.val κ pp) = avg Ω R :=
    (hchain hop.val).trans hrealAvg.symm
  have huniform : Games.accept (P.chainGame A tailReal (hop.val + 1) κ pp) = avg Ω Uacc :=
    (hchain (hop.val + 1)).trans huniformAvg.symm
  have havg := Games.ProbComp.abs_expect_sub_le_expect
    (Games.ProbComp.sample Ω) (f := R) (g := Uacc)
    (h := fun ν => |R ν - Uacc ν|) (fun _ => le_rfl)
  obtain ⟨ν, hν⟩ := LamportReduction.exists_expect_sample_le
    (fun ν : Ω => |R ν - Uacc ν|)
  refine ⟨mk ν, ?_⟩
  rw [Games.advantage_eq, hreal, huniform, LWE.decisionAdvantage_eq, distAdv_def]
  exact havg.trans hν

end Internal

namespace Params

/-- One advice family bounds any selected LPN hop for every realizing non-uniform PPT machine
[JLS26, Lemma 4.2, p. 19]. Dv8 and Dv12 retain buckets and hardwire averaged values.
Dv16 uses the shared, layout-length-only RealizesOn; more realisers are admitted, so this
security statement is at least as strong as the every-coin-string draft. The sentinel
hop makes advice inhabited at κ=0; the hop inequality is requested only below κ.

**Proof sketch.** For each scheduled dimension, average over every nonchallenge value
and fix a maximizing advice tuple. Reindex at ℓ(κ), transport the canonical challenge
by its explicit equivalence, and use the shared realiser verdict/coin readers. Uniform
coin prefixes recover A's coins; the resulting gap is bounded by the LPN advantage. -/
theorem lpn_hop (P : Params) (π : PrimeSchedule) (A : NUPPT)
    (tails : ℕ → Bool) (hops : ∀ κ, Fin (κ + 1)) :
    ∃ w : ∀ L, P.LPNAdvice π L, ∀ B : NUPPT,
      B.RealizesOn (P.lpnEnc π) (A.coins.subst .var)
        (fun L x r => P.lpnRed π A L (w L) x r) →
      ∀ κ, (hops κ).val < κ →
        Games.advantage (P.chainGame A (tails κ) (hops κ).val κ (π κ))
          (P.chainGame A (tails κ) ((hops κ).val + 1) κ (π κ)) ≤
            (P.lpnFamily_raw π).adv B (P.ℓ κ) := sorry

end Params

end TCSlib.Cryptography.Obfuscation.StructuredSeed
