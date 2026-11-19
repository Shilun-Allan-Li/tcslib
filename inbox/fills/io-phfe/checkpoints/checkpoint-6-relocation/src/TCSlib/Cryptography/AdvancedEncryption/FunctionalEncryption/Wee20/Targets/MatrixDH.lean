/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TCSlib.Cryptography.Pairing.MatrixDH.SelfReduction

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# The L1 MDDH preprocessing target and its realisation link

The target is a uniform polynomial-time string preprocessing specification. The shared
realisation API turns its proof and the explicit polynomial advice bound into existence
of a realising non-uniform adversary, without a local machine construction.

## Main definitions

* `MddhPreTargets`: one preprocessing witness per fixed dimension/schedule interface.

## Main results

* `mddhRealizable_of_preTarget`: the shared preprocessing-to-realisation implication.

## References

* [Wee20] H. Wee, *Functional Encryption for Quadratic Functions from k-Lin, Revisited*,
  TCC 2020; full version, Cryptology ePrint Archive, Report 2020/1420, Section 2.1, p.4.

-/

namespace TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.Wee20

open Complexity Turing TCSlib.Cryptography.Pairing

/-- Uniform preprocessing computes the explicit MDDH hybrid from its scalar advice and
canonical DLIN challenge [Wee20, Section 2.1, p.4, polynomial-loss implementation].
Phase B obligation; not proved in this development.

For each fixed order schedule and dimension pair, one preprocessing witness is chosen
before κ, every advice value and every challenge. The witness does not depend on a
consumer adversary. The fixed prime schedule only indexes scalar advice; the modulus
is read from the challenge. This is an L1 preprocessing target, distinct from the L2
interactive-realiser hypotheses. -/
def MddhPreTargets (G : BilinearGen) : Prop :=
  ∀ (p : ℕ → ℕ) (hp : ∀ κ r, (G.inst κ r).order = p κ) (d ℓ : PolyExpr),
    ∃ f : List Bool → List Bool, PolyTimeComputable f ∧
      ∀ κ (ω : BilinearGen.MddhAdvice p d ℓ κ) (c : G.DLINChallenge κ),
        f (pairEncode (G.mddhAdviceEnc p hp d ℓ κ ω) (G.dlinEnc κ c)) =
          G.mddhPre p hp d ℓ κ ω c

/-- The preprocessing witness depends only on the fixed schedule and dimensions and
precedes every security parameter, advice value and challenge. -/
theorem mddhPreTargets_iff (G : BilinearGen) : MddhPreTargets G ↔
    ∀ (p : ℕ → ℕ) (hp : ∀ κ r, (G.inst κ r).order = p κ) (d ℓ : PolyExpr),
      ∃ f : List Bool → List Bool, PolyTimeComputable f ∧
        ∀ κ (ω : BilinearGen.MddhAdvice p d ℓ κ) (c : G.DLINChallenge κ),
          f (pairEncode (G.mddhAdviceEnc p hp d ℓ κ ω) (G.dlinEnc κ c)) =
            G.mddhPre p hp d ℓ κ ω c := Iff.rfl

/-- The uniform L1 preprocessing target supplies machine realisers for every fixed advice
family by the shared realisation theorem [Wee20, Section 2.1, p.4]. Realisers are constrained
only on encoded challenges and layout-length coins. No sampler or reduction machine is
constructed locally.

**Proof sketch.** Read MddhPreTargets and mddhRealizable_iff. Select its common preprocessing
map for p,hp,d,ell without an adversary argument. Instantiate
NUPPT.exists_realizesOn_of_preTarget_id with mddhAdviceEnc, mddhPre, and the uniform
polynomial advice bound length_mddhAdviceEnc_le. Use RealizesOn.congr and
dlinToMddh_eq to identify the named reduction for the current consumer adversary. -/
theorem mddhRealizable_of_preTarget (G : BilinearGen) (hT : MddhPreTargets G)
    (p : ℕ → ℕ) (hp : ∀ κ r, (G.inst κ r).order = p κ) (d ℓ : PolyExpr) :
    G.MDDHRealizable p hp d ℓ :=
  (G.mddhRealizable_iff p hp d ℓ).2 fun D ω =>
    Exists.elim ((mddhPreTargets_iff G).1 hT p hp d ℓ) fun f hf =>
      Exists.elim
        (D.exists_realizesOn_of_preTarget_id G.dlinEnc (G.mddhAdviceEnc p hp d ℓ)
          (G.mddhPre p hp d ℓ) hf.1 hf.2 ω (G.mddhAdviceLen d ℓ)
          (fun κ => G.length_mddhAdviceEnc_le p hp d ℓ κ (ω κ))) fun B hB =>
        ⟨B, hB.congr fun κ c r _ => (G.dlinToMddh_eq p hp d ℓ D ω κ c r).symm⟩

end TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.Wee20
