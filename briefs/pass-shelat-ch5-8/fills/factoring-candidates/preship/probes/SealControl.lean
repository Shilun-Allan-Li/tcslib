import TCSlib.Cryptography.Candidates.Rabin

/-! Seal control (pre-ship): reading three foreign definitions the targets must open, unsealed
(each `example` closes) and sealed with `attribute [local irreducible]` (each must fail). Shows
that without a published equation the reading is a definitional unfolding (rule 10). -/

open Complexity Turing TCSlib.Cryptography TCSlib.Cryptography.Candidates

namespace ProbeSealUnsealed

example (F : Collection) (δ : ℕ → ℝ)
    (h : ∀ n (r : F.gen.Coins n), StatClose (fun s : F.sample.Coins n =>
      F.decD (F.index n r) (F.sample.runAt n (F.index n r) s)) (fun x : F.D (F.index n r) => some x) (δ n)) :
    F.SampleClose δ := h

example (z : List Bool) : NUPPT.inParam z = pairFstD (pairFstD (pairFstD z)) := rfl

example (𝓕 : FunFamily) (F : List Bool → List Bool) (hF : PolyTimeComputable F)
    (hx : ∀ n (x : Fin (𝓕.inLen.eval n) → Bool), F (NUPPT.advInput n (List.ofFn x)) = List.ofFn (𝓕.f n x)) :
    𝓕.Easy := ⟨F, hF, hx⟩

end ProbeSealUnsealed

namespace ProbeSealSealed

attribute [local irreducible] Collection.SampleClose NUPPT.inParam FunFamily.Easy

example (F : Collection) (δ : ℕ → ℝ)
    (h : ∀ n (r : F.gen.Coins n), StatClose (fun s : F.sample.Coins n =>
      F.decD (F.index n r) (F.sample.runAt n (F.index n r) s)) (fun x : F.D (F.index n r) => some x) (δ n)) :
    F.SampleClose δ := h

example (z : List Bool) : NUPPT.inParam z = pairFstD (pairFstD (pairFstD z)) := rfl

example (𝓕 : FunFamily) (F : List Bool → List Bool) (hF : PolyTimeComputable F)
    (hx : ∀ n (x : Fin (𝓕.inLen.eval n) → Bool), F (NUPPT.advInput n (List.ofFn x)) = List.ofFn (𝓕.f n x)) :
    𝓕.Easy := ⟨F, hF, hx⟩

end ProbeSealSealed
