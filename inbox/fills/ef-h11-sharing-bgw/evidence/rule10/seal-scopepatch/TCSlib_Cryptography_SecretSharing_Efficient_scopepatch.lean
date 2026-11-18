/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TCSlib.Cryptography.SecretSharing.Defs
import TCSlib.Cryptography.CoinSampling.Contract
import TCSlib.Complexity.ClassP.BinaryArith.Words
import TCSlib.Complexity.ClassP.BinaryArith.ModPow
import TCSlib.Complexity.ClassP.BinaryArith.Loops

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false
attribute [local irreducible] Complexity.PolyTimeComputable Complexity.pairFstD Complexity.pairSndD Turing.pairEncode Complexity.BinArith.add Complexity.BinArith.encWords Complexity.BinArith.mod Complexity.BinArith.mul Complexity.BinArith.powMod Complexity.BinArith.sub Complexity.LogProg.bitsVal Complexity.NUPPT.advInput Complexity.PolyExpr.eval Complexity.PrefixByLength.take TCSlib.Cryptography.CoinSampling.SamplesEfficiently TCSlib.SecretSharing.AccessStructure.threshold TCSlib.SecretSharing.Scheme.Correct TCSlib.SecretSharing.Scheme.LocalReconstruct TCSlib.SecretSharing.Scheme.PerfectPrivacy TCSlib.Cryptography.CoinSampling.CoinSampler.fail

/-!
# Efficient secret sharing: the interface

`SecretSharing.Scheme` (`TCSlib.Cryptography.SecretSharing.Defs`) records the data of a scheme
without efficiency, a recorded deviation from [PS10, Def 152.1], which asks `Share` and `Recon`
to be probabilistic polynomial-time. This file states that efficiency requirement. A scheme over
an abstract field with every nonzero element a party has exponentially many shares, so the
efficient form is **parametric**: public parameters `π` (written as a parameter word
`encPub π`) fix a finite list of parties, and

* the share map of **one** party, `⟨π, sec, coins, i⟩ ↦ share`, is `PolyTimeComputable`;
* reconstruction from a **listed** set of parties with their shares is `PolyTimeComputable`;
* the dealer's coins are drawn by an honest sampler in the `CoinSampling.SamplesEfficiently`
  form (`DealerSamples`): exactly uniform on success, failure at most `2^{-κ}`.

The typed maps are a `Scheme` for every `π`, and correctness and privacy are the existing
`Scheme.Correct` and `Scheme.PerfectPrivacy`, read at every `π` (no second definition of either
notion). Instances restrict an existing scheme to the listed parties with `Scheme.restrict`,
whose correctness and privacy transfer from the unrestricted scheme
(`Scheme.restrict_correct`, `Scheme.restrict_perfectPrivacy`).

## Main definitions

* `SecretSharing.Scheme.restrict`: a scheme restricted to an injected party type, with coins read
  through an equivalence.
* `SecretSharing.DealerSamples`: the dealer's coins are sampled efficiently, with the sampler's
  parameter word computed in polynomial time from the public parameters.
* `SecretSharing.EfficientScheme`: the efficient secret-sharing interface.
* `SecretSharing.EfficientScheme.Correct`, `.PerfectPrivacy`, `.LocalReconstruct`: the existing
  notions at every public parameter.
* `SecretSharing.ShamirParams`, `SecretSharing.ShamirParams.encode`: the public parameters of a
  `k`-out-of-`n` Shamir scheme over `ℤ_p`, and their parameter word.
* `SecretSharing.resWord`, `SecretSharing.addModW`, `SecretSharing.subModW`,
  `SecretSharing.mulModW`, `SecretSharing.invModW`: residues mod `p` as binary numerals, and the
  modular arithmetic on them (the inverse by Fermat, `x^{p−2}`), from `Complexity.BinArith`.

## Main results

* `Scheme.restrict_correct`, `Scheme.restrict_localReconstruct`,
  `Scheme.restrict_perfectPrivacy`: transfer to a restriction.
* `AccessStructure.threshold_map_auth`: the threshold structure is read through an injection.
* `samplesEfficiently_comap`: an efficient sampler reindexed along a map of public inputs.
* `addModW_resWord`, `subModW_resWord`, `mulModW_resWord`, `invModW_resWord` and their
  `polyTimeComputable_*` lemmas: the residue layer is polynomial-time and exact.

## References

* [Sha79] A. Shamir, *How to share a secret*, Communications of the ACM 22(11), 1979.
* [Bei11] A. Beimel, *Secret-sharing schemes: a survey*, IWCC 2011, §1–2.
* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed., January 2010,
  §6.1.1 (Definition 152.1, `(k, n)` secret sharing).
-/

namespace TCSlib.SecretSharing

open Finset Complexity Turing TCSlib.Cryptography
open Complexity.LogProg (bitsVal bitsVal_bits)

variable {P Q Secret Share Rand Rand' : Type*}

/-! ### Restriction to listed parties -/

/-- `threshold k` read through an injection `e : Q ↪ P`: `A.map e` has at least `k` members iff
`A` has (`Finset.card_map`). Glue. -/
theorem AccessStructure.threshold_map_auth (k : ℕ) (e : Q ↪ P) (A : Finset Q) :
    (AccessStructure.threshold k).Auth (A.map e) ↔ (AccessStructure.threshold k).Auth A := by
  rw [AccessStructure.threshold_auth, AccessStructure.threshold_auth, Finset.card_map]

/-- **The restriction of a scheme** `S` on parties `P` to the parties `Q`, injected by `e`, with
the coins `Rand'` read through an equivalence `ε : Rand' ≃ Rand`: party `i` receives
`S.share sec (ε r) (e i)`, and a set `A` reconstructs as `S`'s set `A.map e` would, from the share
assignment extended by `s₀` off the image of `e`. This is how [PS10, Prot 154.4]'s `n` parties
`1, …, n` sit inside `Shamir.scheme` (whose parties are all nonzero field elements); see the
deviation note there. Glue. -/
noncomputable def Scheme.restrict (S : Scheme P Secret Share Rand) (e : Q ↪ P) (ε : Rand' ≃ Rand)
    (s₀ : Share) : Scheme Q Secret Share Rand' where
  share sec r i := S.share sec (ε r) (e i)
  reconstruct A f := S.reconstruct (A.map e) (Function.extend e f fun _ => s₀)

namespace Scheme

variable (S : Scheme P Secret Share Rand) (e : Q ↪ P) (ε : Rand' ≃ Rand) (s₀ : Share)

/-- `(S.restrict e ε s₀).share sec r i = S.share sec (ε r) (e i)`. -/
theorem restrict_share (sec : Secret) (r : Rand') (i : Q) :
    (S.restrict e ε s₀).share sec r i = S.share sec (ε r) (e i) := rfl

/-- `(S.restrict e ε s₀).reconstruct A f = S.reconstruct (A.map e) (extend e f s₀)`. -/
theorem restrict_reconstruct (A : Finset Q) (f : Q → Share) :
    (S.restrict e ε s₀).reconstruct A f =
      S.reconstruct (A.map e) (Function.extend e f fun _ => s₀) := rfl

variable {S}

/-- If `S` reconstructs locally, the restricted reconstruction is `S`'s reconstruction from any
assignment agreeing with `f` on `A.map e`. Glue (`Function.Injective.extend_apply`). -/
theorem restrict_reconstruct_of_eqOn (hL : S.LocalReconstruct) (A : Finset Q) (f : Q → Share)
    (g : P → Share) (hfg : ∀ i ∈ A, g (e i) = f i) :
    (S.restrict e ε s₀).reconstruct A f = S.reconstruct (A.map e) g := by
  rw [restrict_reconstruct]
  refine (Scheme.localReconstruct_iff S).1 hL _ _ _ fun j hj => ?_
  obtain ⟨i, hi, rfl⟩ := Finset.mem_map.1 hj
  rw [e.injective.extend_apply, hfg i hi]

/-- **Locality transfers to a restriction.** Glue. -/
theorem restrict_localReconstruct (hL : S.LocalReconstruct) :
    (S.restrict e ε s₀).LocalReconstruct := by
  refine (Scheme.localReconstruct_iff _).2 fun A f g hfg => ?_
  rw [restrict_reconstruct_of_eqOn e ε s₀ hL A f (Function.extend e g fun _ => s₀)
    fun i hi => by rw [e.injective.extend_apply, hfg i hi], restrict_reconstruct]

/-- **Correctness transfers to a restriction**: if `S` is correct for `Γ` and reconstructs
locally, and every `Γ'`-authorized set of `Q` maps to a `Γ`-authorized set, the restriction is
correct for `Γ'`. Glue. -/
theorem restrict_correct {Γ : AccessStructure P} {Γ' : AccessStructure Q} (hS : S.Correct Γ)
    (hL : S.LocalReconstruct) (hΓ : ∀ A, Γ'.Auth A → Γ.Auth (A.map e)) :
    (S.restrict e ε s₀).Correct Γ' := by
  refine (Scheme.correct_iff _ Γ').2 fun A hA sec r => ?_
  rw [restrict_reconstruct_of_eqOn e ε s₀ hL A ((S.restrict e ε s₀).share sec r)
    (S.share sec (ε r)) fun i _ => (restrict_share S e ε s₀ sec r i).symm]
  exact (Scheme.correct_iff S Γ).1 hS _ (hΓ A hA) sec (ε r)

/-- **Perfect privacy transfers to a restriction**: if `S` is perfectly private for `Γ` and every
`Γ'`-unauthorized set of `Q` maps to a `Γ`-unauthorized set, the restriction is perfectly private
for `Γ'`; the coin bijection is `S`'s, conjugated by `ε`. Glue. -/
theorem restrict_perfectPrivacy {Γ : AccessStructure P} {Γ' : AccessStructure Q}
    (hS : S.PerfectPrivacy Γ) (hΓ : ∀ B, ¬ Γ'.Auth B → ¬ Γ.Auth (B.map e)) :
    (S.restrict e ε s₀).PerfectPrivacy Γ' := by
  refine (Scheme.perfectPrivacy_iff _ Γ').2 fun B hB sec sec' => ?_
  obtain ⟨σ, hσ⟩ := (Scheme.perfectPrivacy_iff S Γ).1 hS _ (hΓ B hB) sec sec'
  refine ⟨(ε.trans σ).trans ε.symm, fun r i hi => ?_⟩
  rw [restrict_share, restrict_share, Equiv.trans_apply, Equiv.apply_symm_apply,
    Equiv.trans_apply]
  exact hσ (ε r) (e i) (Finset.mem_map_of_mem e hi)

end Scheme

/-! ### The dealer's coins -/

/-- **Reindexing an efficient sampler along a map of public inputs** `φ κ : P' κ → P κ`: the
same sampler, read at `φ κ π'` (the same `UniformSampler`, coin polynomial and core machine;
`CoinSampling.samplesEfficiently_iff_exists`). Glue; a candidate for `CoinSampling.Contract`. -/
theorem samplesEfficiently_comap {P P' : ℕ → Type} {Draw β : (κ : ℕ) → P κ → Type}
    {y : ∀ κ, P κ → List Bool} {encDraw : ∀ κ π, Draw κ π → List Bool}
    {encOut : ∀ κ π, β κ π → List Bool} {core : ∀ κ π, Draw κ π → β κ π}
    (h : CoinSampling.SamplesEfficiently y encDraw encOut core) (φ : ∀ κ, P' κ → P κ) :
    CoinSampling.SamplesEfficiently (Draw := fun κ π => Draw κ (φ κ π))
      (β := fun κ π => β κ (φ κ π)) (fun κ π => y κ (φ κ π)) (fun κ π => encDraw κ (φ κ π))
      (fun κ π => encOut κ (φ κ π)) fun κ π => core κ (φ κ π) := by
  obtain ⟨U, c, e, f, he, hc, hf, hfe⟩ := (CoinSampling.samplesEfficiently_iff_exists _ _ _ _).1 h
  exact (CoinSampling.samplesEfficiently_iff_exists _ _ _ _).2
    ⟨U, c, fun κ π => e κ (φ κ π), f, fun κ π => he κ (φ κ π), fun κ π => hc κ (φ κ π), hf,
      fun κ π => hfe κ (φ κ π)⟩

/-- **The dealer's coins are sampled efficiently**: at every security parameter `κ` and every
public parameter `π` admissible at `κ` (`Adm κ π`, typically a bit-length bound on the coin space
in terms of `κ`), the coins `r : Rand π` are drawn by an honest sampler in the
`CoinSampling.SamplesEfficiently` form, whose output is `encRand π r`, with the identity core, so
that on success they are exactly uniform and the failure is at most `2^{-κ}`
[PS10, Def 23.4]; and the sampler's parameter word `y κ π` is computed by one
`PolyTimeComputable` map from `⟨1^κ, encPub π⟩`. The draw's own encoding `encDraw` is the
sampler's and is not constrained. This is the probabilistic half of [PS10, Def 152.1]'s
requirement that `Share` be probabilistic polynomial-time. -/
def DealerSamples {Pub : Type} (Rand : Pub → Type) (Adm : ℕ → Pub → Prop)
    (encPub : Pub → List Bool) (encRand : ∀ π, Rand π → List Bool) : Prop :=
  ∃ (y : ∀ κ, {π // Adm κ π} → List Bool)
    (encDraw : ∀ κ (π : {π // Adm κ π}), Rand π.1 → List Bool),
    (∃ g : List Bool → List Bool, PolyTimeComputable g ∧
      ∀ κ π, g (NUPPT.advInput κ (encPub π.1)) = y κ π) ∧
    CoinSampling.SamplesEfficiently y encDraw (fun _ π => encRand π.1) fun _ _ r => r

/-- The defining equation of `DealerSamples`. -/
theorem dealerSamples_iff {Pub : Type} (Rand : Pub → Type) (Adm : ℕ → Pub → Prop)
    (encPub : Pub → List Bool) (encRand : ∀ π, Rand π → List Bool) :
    DealerSamples Rand Adm encPub encRand ↔
      ∃ (y : ∀ κ, {π // Adm κ π} → List Bool)
        (encDraw : ∀ κ (π : {π // Adm κ π}), Rand π.1 → List Bool),
        (∃ g : List Bool → List Bool, PolyTimeComputable g ∧
          ∀ κ π, g (NUPPT.advInput κ (encPub π.1)) = y κ π) ∧
        CoinSampling.SamplesEfficiently y encDraw (fun _ π => encRand π.1) fun _ _ r => r :=
  Iff.rfl

/-! ### The interface -/

/-- **An efficient secret-sharing scheme** [PS10, Def 152.1], with its efficiency clause, which
`Scheme` does not model (`Defs.lean`'s recorded deviation): public parameters `π : Pub` with a
parameter word `encPub π`; for each `π` a finite party type `Party π`, the typed maps
`scheme π : Scheme (Party π) (Secret π) (Share π) (Rand π)` and an access structure `access π`;
encodings of parties, secrets, shares and coins; and three efficiency fields:

* `share_poly`: one `PolyTimeComputable` map computes party `i`'s share
  `⟨π, ⟨sec, ⟨r, i⟩⟩⟩ ↦ (scheme π).share sec r i`;
* `reconstruct_poly`: one `PolyTimeComputable` map computes, from `π` and the encoded list of
  pairs `⟨i, f i⟩` over a duplicate-free listing `l` of a set `A`, the secret
  `(scheme π).reconstruct A f`;
* `dealer_efficient`: the dealer's coins are drawn efficiently (`DealerSamples`), at the public
  parameters `Adm κ`-admissible at the security parameter `κ`.

The two maps are uniform: one machine for every `π`, with no advice and no hard-wired modulus.
Security is not part of the data: see `EfficientScheme.Correct` and
`EfficientScheme.PerfectPrivacy`. **Deviation:** [PS10]'s `Recon` receives `k` shares with their
indices; here it receives a listed set with its shares, as in `Scheme`. -/
structure EfficientScheme where
  /-- The public parameters. -/
  Pub : Type
  /-- The parties listed by the public parameters. -/
  Party : Pub → Type
  /-- The secrets. -/
  Secret : Pub → Type
  /-- The shares. -/
  Share : Pub → Type
  /-- The dealer's coins. -/
  Rand : Pub → Type
  /-- The typed scheme at each public parameter. -/
  scheme : ∀ π, Scheme (Party π) (Secret π) (Share π) (Rand π)
  /-- The access structure at each public parameter. -/
  access : ∀ π, AccessStructure (Party π)
  /-- The public parameters admissible at a security parameter. -/
  Adm : ℕ → Pub → Prop
  /-- The parameter word of the public parameters. -/
  encPub : Pub → List Bool
  /-- The encoding of a party. -/
  encParty : ∀ π, Party π → List Bool
  /-- The encoding of a secret. -/
  encSecret : ∀ π, Secret π → List Bool
  /-- The encoding of a share. -/
  encShare : ∀ π, Share π → List Bool
  /-- The encoding of the dealer's coins. -/
  encRand : ∀ π, Rand π → List Bool
  /-- One party's share is polynomial-time. -/
  share_poly : ∃ f : List Bool → List Bool, PolyTimeComputable f ∧
    ∀ π sec r i, f (pairEncode (encPub π) (pairEncode (encSecret π sec)
      (pairEncode (encRand π r) (encParty π i)))) = encShare π ((scheme π).share sec r i)
  /-- Reconstruction from a listed set is polynomial-time. -/
  reconstruct_poly : ∃ f : List Bool → List Bool, PolyTimeComputable f ∧
    ∀ π (A : Finset (Party π)) (l : List (Party π)) (sh : Party π → Share π), l.Nodup →
      (∀ i, i ∈ l ↔ i ∈ A) →
      f (pairEncode (encPub π) (BinArith.encWords
        (l.map fun i => pairEncode (encParty π i) (encShare π (sh i))))) =
        encSecret π ((scheme π).reconstruct A sh)
  /-- The dealer's coins are sampled efficiently. -/
  dealer_efficient : DealerSamples Rand Adm encPub encRand

namespace EfficientScheme

variable (E : EfficientScheme)

/-- **Correctness** of an efficient scheme: at every public parameter, the typed scheme is
correct for its access structure (`Scheme.Correct`). [PS10, Def 152.1, item 2] -/
def Correct : Prop := ∀ π, (E.scheme π).Correct (E.access π)

/-- `E.Correct ↔ ∀ π, (E.scheme π).Correct (E.access π)`. -/
theorem correct_iff : E.Correct ↔ ∀ π, (E.scheme π).Correct (E.access π) := Iff.rfl

/-- **Local reconstruction** at every public parameter (`Scheme.LocalReconstruct`). -/
def LocalReconstruct : Prop := ∀ π, (E.scheme π).LocalReconstruct

/-- `E.LocalReconstruct ↔ ∀ π, (E.scheme π).LocalReconstruct`. -/
theorem localReconstruct_iff : E.LocalReconstruct ↔ ∀ π, (E.scheme π).LocalReconstruct :=
  Iff.rfl

/-- **Perfect privacy** of an efficient scheme: at every public parameter, the typed scheme is
perfectly private for its access structure (`Scheme.PerfectPrivacy`). [PS10, Def 152.1, item 3],
in the perfect form of `Scheme.PerfectPrivacy`. -/
def PerfectPrivacy : Prop := ∀ π, (E.scheme π).PerfectPrivacy (E.access π)

/-- `E.PerfectPrivacy ↔ ∀ π, (E.scheme π).PerfectPrivacy (E.access π)`. -/
theorem perfectPrivacy_iff :
    E.PerfectPrivacy ↔ ∀ π, (E.scheme π).PerfectPrivacy (E.access π) := Iff.rfl

end EfficientScheme

/-! ### Shamir's public parameters -/

/-- **The public parameters of a `k`-out-of-`n` Shamir scheme over `ℤ_p`** [PS10, Prot 154.4]:
a prime `p`, a threshold `0 < k ≤ n` and a party count `n < p` (so that the parties
`1, …, n` are distinct and nonzero mod `p`). -/
structure ShamirParams where
  /-- The prime modulus. -/
  p : ℕ
  /-- The threshold. -/
  k : ℕ
  /-- The number of parties. -/
  n : ℕ
  /-- `p` is prime. -/
  prime : p.Prime
  /-- The threshold is positive. -/
  k_pos : 0 < k
  /-- The threshold is at most the number of parties. -/
  k_le_n : k ≤ n
  /-- The parties `1, …, n` are nonzero mod `p`. -/
  n_lt_p : n < p

namespace ShamirParams

/-- **The parameter word** of Shamir's public parameters: `⟨p, ⟨1^k, n⟩⟩`, with `p` and `n` as
little-endian binary numerals (`Nat.bits`, the format of `Complexity.BinArith`) and `k` in unary,
so that the share map's loop over the `k - 1` coefficients runs in time polynomial in the
input. -/
def encode (π : ShamirParams) : List Bool :=
  pairEncode (Nat.bits π.p) (pairEncode (List.replicate π.k true) (Nat.bits π.n))

/-- `π.encode = ⟨bits p, ⟨1^k, bits n⟩⟩`. -/
theorem encode_eq (π : ShamirParams) :
    π.encode = pairEncode (Nat.bits π.p) (pairEncode (List.replicate π.k true) (Nat.bits π.n)) :=
  rfl

/-- The first slot of the parameter word is the numeral of `p`. -/
theorem pairFstD_encode (π : ShamirParams) : pairFstD π.encode = Nat.bits π.p := by
  rw [encode_eq, pairFstD_pairEncode]

/-- The second slot of the parameter word is `1^k`. -/
theorem pairFstD_pairSndD_encode (π : ShamirParams) :
    pairFstD (pairSndD π.encode) = List.replicate π.k true := by
  rw [encode_eq, pairSndD_pairEncode, pairFstD_pairEncode]

/-- The third slot of the parameter word is the numeral of `n`. -/
theorem pairSndD_pairSndD_encode (π : ShamirParams) :
    pairSndD (pairSndD π.encode) = Nat.bits π.n := by
  rw [encode_eq, pairSndD_pairEncode, pairSndD_pairEncode]

end ShamirParams

/-! ### Residues as binary words -/

section Residues

variable {p : ℕ}

/-- **A residue as a word**: `a : ZMod p` written as the little-endian binary numeral of its
least nonnegative representative, `Nat.bits a.val` (the format of `Complexity.BinArith`). -/
def resWord (a : ZMod p) : List Bool := Nat.bits a.val

/-- `resWord a = Nat.bits a.val`. -/
theorem resWord_eq (a : ZMod p) : resWord a = Nat.bits a.val := rfl

/-- The numeral of a residue reads back as its representative. -/
theorem bitsVal_resWord (a : ZMod p) : bitsVal (resWord a) = a.val := by
  rw [resWord_eq, bitsVal_bits]

/-- The word of the residue of a natural number `v < p` is `v`'s numeral
(`ZMod.val_cast_of_lt`). -/
theorem resWord_natCast_of_lt {v : ℕ} (h : v < p) : resWord (v : ZMod p) = Nat.bits v := by
  rw [resWord_eq, ZMod.val_cast_of_lt h]

/-- A residue's word is no longer than the numeral of the modulus (`ZMod.val_lt`). -/
theorem length_resWord_le [NeZero p] (a : ZMod p) :
    (resWord a).length ≤ (Nat.bits p).length := by
  rw [resWord_eq, Nat.size_eq_bits_len, Nat.size_eq_bits_len]
  exact Nat.size_le_size (ZMod.val_lt a).le

/-- Residue words are injective (`ZMod.val_injective`). -/
theorem resWord_injective [NeZero p] : Function.Injective (resWord (p := p)) := by
  intro a b h
  have := congrArg bitsVal h
  rw [bitsVal_resWord, bitsVal_resWord] at this
  exact ZMod.val_injective p this

end Residues

/-! ### Modular arithmetic on words

Leaf maps on the layout `⟨p, ⟨a, b⟩⟩` (numerals), composed from `Complexity.BinArith`'s `add`,
`sub`, `mul`, `mod` and `powMod`. Each output is cut to the length of the modulus word
(`Complexity.PrefixByLength.take`): on residue words this changes nothing
(`length_resWord_le`), and on every word it bounds the output by the modulus, which is what the
loop envelopes below need. -/

section Leaves

/-- `(a + b) mod p` on `⟨p, ⟨a, b⟩⟩`, cut to the length of `p`. -/
def addModW (z : List Bool) : List Bool :=
  PrefixByLength.take (pairEncode (pairFstD z) (BinArith.mod (pairEncode (BinArith.add
    (pairEncode (pairFstD (pairSndD z)) (pairSndD (pairSndD z)))) (pairFstD z))))

/-- `addModW z = take ⟨p, mod ⟨add ⟨a, b⟩, p⟩⟩` on `z = ⟨p, ⟨a, b⟩⟩`. -/
theorem addModW_eq (z : List Bool) :
    addModW z = PrefixByLength.take (pairEncode (pairFstD z) (BinArith.mod (pairEncode
      (BinArith.add (pairEncode (pairFstD (pairSndD z)) (pairSndD (pairSndD z)))) (pairFstD z))))
    := rfl

/-- `(a · b) mod p` on `⟨p, ⟨a, b⟩⟩`, cut to the length of `p`. -/
def mulModW (z : List Bool) : List Bool :=
  PrefixByLength.take (pairEncode (pairFstD z) (BinArith.mod (pairEncode (BinArith.mul
    (pairEncode (pairFstD (pairSndD z)) (pairSndD (pairSndD z)))) (pairFstD z))))

/-- `mulModW z = take ⟨p, mod ⟨mul ⟨a, b⟩, p⟩⟩` on `z = ⟨p, ⟨a, b⟩⟩`. -/
theorem mulModW_eq (z : List Bool) :
    mulModW z = PrefixByLength.take (pairEncode (pairFstD z) (BinArith.mod (pairEncode
      (BinArith.mul (pairEncode (pairFstD (pairSndD z)) (pairSndD (pairSndD z)))) (pairFstD z))))
    := rfl

/-- `(a + p − b) mod p` on `⟨p, ⟨a, b⟩⟩`, cut to the length of `p`: the difference of two
residues. -/
def subModW (z : List Bool) : List Bool :=
  PrefixByLength.take (pairEncode (pairFstD z) (BinArith.mod (pairEncode (BinArith.sub
    (pairEncode (BinArith.add (pairEncode (pairFstD (pairSndD z)) (pairFstD z)))
      (pairSndD (pairSndD z)))) (pairFstD z))))

/-- `subModW z = take ⟨p, mod ⟨sub ⟨add ⟨a, p⟩, b⟩, p⟩⟩` on `z = ⟨p, ⟨a, b⟩⟩`. -/
theorem subModW_eq (z : List Bool) :
    subModW z = PrefixByLength.take (pairEncode (pairFstD z) (BinArith.mod (pairEncode
      (BinArith.sub (pairEncode (BinArith.add (pairEncode (pairFstD (pairSndD z)) (pairFstD z)))
        (pairSndD (pairSndD z)))) (pairFstD z)))) := rfl

/-- **The inverse modulo a prime, by Fermat**: `a^{p−2} mod p` on `⟨p, a⟩`, through
`BinArith.powMod`, cut to the length of `p`. This is the first public modular-inverse map of the
library; its inline relative is the pivot inverse of `Complexity.BinArith.detWStep`
(`BinaryArith/DetMod.lean`), which composes `powMod` and `sub` the same way. -/
def invModW (z : List Bool) : List Bool :=
  PrefixByLength.take (pairEncode (pairFstD z) (BinArith.powMod (pairEncode (pairSndD z)
    (pairEncode (BinArith.sub (pairEncode (pairFstD z) (Nat.bits 2))) (pairFstD z)))))

/-- `invModW z = take ⟨p, powMod ⟨a, ⟨sub ⟨p, 2⟩, p⟩⟩⟩` on `z = ⟨p, a⟩`. -/
theorem invModW_eq (z : List Bool) :
    invModW z = PrefixByLength.take (pairEncode (pairFstD z) (BinArith.powMod (pairEncode
      (pairSndD z) (pairEncode (BinArith.sub (pairEncode (pairFstD z) (Nat.bits 2)))
        (pairFstD z))))) := rfl

/-- Cutting a word to the length of `u`: at most `|u|` letters (`PrefixByLength.take_def`).
Glue. -/
theorem length_take_pairEncode_le (u w : List Bool) :
    (PrefixByLength.take (pairEncode u w)).length ≤ u.length := by
  rw [PrefixByLength.take_def, pairFstD_pairEncode]
  exact List.length_take_le _ _

/-- Cutting a residue word to the length of the modulus word changes nothing. Glue. -/
theorem take_pairEncode_resWord {p : ℕ} [NeZero p] (a : ZMod p) :
    PrefixByLength.take (pairEncode (Nat.bits p) (resWord a)) = resWord a := by
  rw [PrefixByLength.take_def, pairFstD_pairEncode, pairSndD_pairEncode]
  exact List.take_of_length_le (length_resWord_le a)

/-- The leaves' outputs are no longer than the modulus word. -/
theorem length_addModW_le (z : List Bool) : (addModW z).length ≤ (pairFstD z).length := by
  rw [addModW_eq]; exact length_take_pairEncode_le _ _

/-- The leaves' outputs are no longer than the modulus word. -/
theorem length_mulModW_le (z : List Bool) : (mulModW z).length ≤ (pairFstD z).length := by
  rw [mulModW_eq]; exact length_take_pairEncode_le _ _

variable {p : ℕ} [NeZero p]

/-- `addModW ⟨p, ⟨a, b⟩⟩ = a + b` on residue words (`ZMod.val_add`). -/
theorem addModW_resWord (a b : ZMod p) :
    addModW (pairEncode (Nat.bits p) (pairEncode (resWord a) (resWord b))) = resWord (a + b) := by
  rw [addModW_eq, pairSndD_pairEncode, pairFstD_pairEncode, pairFstD_pairEncode,
    pairSndD_pairEncode, resWord_eq, resWord_eq, BinArith.add_pairEncode,
    BinArith.mod_pairEncode, ← ZMod.val_add, ← resWord_eq, take_pairEncode_resWord]

/-- `mulModW ⟨p, ⟨a, b⟩⟩ = a · b` on residue words (`ZMod.val_mul`). -/
theorem mulModW_resWord (a b : ZMod p) :
    mulModW (pairEncode (Nat.bits p) (pairEncode (resWord a) (resWord b))) = resWord (a * b) := by
  rw [mulModW_eq, pairSndD_pairEncode, pairFstD_pairEncode, pairFstD_pairEncode,
    pairSndD_pairEncode, resWord_eq, resWord_eq, BinArith.mul_pairEncode,
    BinArith.mod_pairEncode, ← ZMod.val_mul, ← resWord_eq, take_pairEncode_resWord]

/-- `(a + p − b) mod p` is the representative of `a − b` (`ZMod.val_natCast`). Glue. -/
theorem val_sub_eq_add_sub_mod (a b : ZMod p) : (a - b).val = (a.val + p - b.val) % p := by
  have hb : b.val ≤ a.val + p := le_add_left (ZMod.val_lt b).le
  have hcast : ((a.val + p - b.val : ℕ) : ZMod p) = a - b := by
    rw [Nat.cast_sub hb, Nat.cast_add, ZMod.natCast_self, add_zero, ZMod.natCast_zmod_val,
      ZMod.natCast_zmod_val]
  rw [← hcast, ZMod.val_natCast]

/-- `subModW ⟨p, ⟨a, b⟩⟩ = a − b` on residue words. -/
theorem subModW_resWord (a b : ZMod p) :
    subModW (pairEncode (Nat.bits p) (pairEncode (resWord a) (resWord b))) = resWord (a - b) := by
  rw [subModW_eq, pairSndD_pairEncode, pairFstD_pairEncode, pairFstD_pairEncode,
    pairSndD_pairEncode, resWord_eq, resWord_eq, BinArith.add_pairEncode,
    BinArith.sub_pairEncode, BinArith.mod_pairEncode, ← val_sub_eq_add_sub_mod, ← resWord_eq,
    take_pairEncode_resWord]

/-- **Fermat's inverse**: in `ZMod q` with `q` prime, `a^{q−2} = a⁻¹` for `a ≠ 0`
(`ZMod.pow_card_sub_one_eq_one`). Glue. -/
theorem pow_sub_two_eq_inv {q : ℕ} [Fact q.Prime] {a : ZMod q} (ha : a ≠ 0) :
    a ^ (q - 2) = a⁻¹ := by
  have h2 : 2 ≤ q := (Fact.out : q.Prime).two_le
  refine eq_inv_of_mul_eq_one_left ?_
  rw [← pow_succ, show q - 2 + 1 = q - 1 by omega]
  exact ZMod.pow_card_sub_one_eq_one ha

omit [NeZero p] in
/-- `invModW ⟨q, a⟩ = a⁻¹` on residue words, for `q` prime and `a ≠ 0`
(`BinArith.powMod_pairEncode`, `pow_sub_two_eq_inv`). -/
theorem invModW_resWord {q : ℕ} [Fact q.Prime] {a : ZMod q} (ha : a ≠ 0) :
    invModW (pairEncode (Nat.bits q) (resWord a)) = resWord a⁻¹ := by
  have hq : q ≠ 0 := (Fact.out : q.Prime).ne_zero
  have hv : a.val ^ (q - 2) % q = (a⁻¹).val := by
    rw [← pow_sub_two_eq_inv ha, ← ZMod.val_natCast, Nat.cast_pow, ZMod.natCast_zmod_val]
  rw [invModW_eq, pairSndD_pairEncode, pairFstD_pairEncode, BinArith.sub_pairEncode, resWord_eq,
    BinArith.powMod_pairEncode _ _ _ hq, hv, ← resWord_eq, take_pairEncode_resWord]

end Leaves

section LeavesPoly

/-- Cutting `g` to the length of `u` is polynomial-time when both are
(`polyTimeComputable_takePrefixByLength`). Glue. -/
theorem PolyTimeComputable.takeTo {u g : List Bool → List Bool} (hu : PolyTimeComputable u)
    (hg : PolyTimeComputable g) :
    PolyTimeComputable fun z => PrefixByLength.take (pairEncode (u z) (g z)) :=
  polyTimeComputable_takePrefixByLength.comp' (hu.pairEncode hg)

/-- `addModW` is polynomial-time (`BinArith.polyTimeComputable_add`, `_mod`). -/
theorem polyTimeComputable_addModW : PolyTimeComputable addModW :=
  (PolyTimeComputable.takeTo polyTimeComputable_pairFstD (BinArith.polyTimeComputable_mod.comp
    ((BinArith.polyTimeComputable_add.comp (BinArith.polyTimeComputable_slot2.pairEncode
      BinArith.polyTimeComputable_slot3)).pairEncode polyTimeComputable_pairFstD))).congr
    fun z => (addModW_eq z).symm

/-- `mulModW` is polynomial-time (`BinArith.polyTimeComputable_mul`, `_mod`). -/
theorem polyTimeComputable_mulModW : PolyTimeComputable mulModW :=
  (PolyTimeComputable.takeTo polyTimeComputable_pairFstD (BinArith.polyTimeComputable_mod.comp
    ((BinArith.polyTimeComputable_mul.comp (BinArith.polyTimeComputable_slot2.pairEncode
      BinArith.polyTimeComputable_slot3)).pairEncode polyTimeComputable_pairFstD))).congr
    fun z => (mulModW_eq z).symm

/-- `subModW` is polynomial-time (`BinArith.polyTimeComputable_add`, `_sub`, `_mod`). -/
theorem polyTimeComputable_subModW : PolyTimeComputable subModW :=
  (PolyTimeComputable.takeTo polyTimeComputable_pairFstD (BinArith.polyTimeComputable_mod.comp
    ((BinArith.polyTimeComputable_sub.comp ((BinArith.polyTimeComputable_add.comp
      (BinArith.polyTimeComputable_slot2.pairEncode polyTimeComputable_pairFstD)).pairEncode
      BinArith.polyTimeComputable_slot3)).pairEncode polyTimeComputable_pairFstD))).congr
    fun z => (subModW_eq z).symm

/-- `invModW` is polynomial-time (`BinArith.polyTimeComputable_powMod`, `_sub`). -/
theorem polyTimeComputable_invModW : PolyTimeComputable invModW :=
  (PolyTimeComputable.takeTo polyTimeComputable_pairFstD
    (BinArith.polyTimeComputable_powMod.comp (polyTimeComputable_pairSndD.pairEncode
      ((BinArith.polyTimeComputable_sub.comp (polyTimeComputable_pairFstD.pairEncode
        (polyTimeComputable_const _))).pairEncode polyTimeComputable_pairFstD)))).congr
    fun z => (invModW_eq z).symm

end LeavesPoly

end TCSlib.SecretSharing
