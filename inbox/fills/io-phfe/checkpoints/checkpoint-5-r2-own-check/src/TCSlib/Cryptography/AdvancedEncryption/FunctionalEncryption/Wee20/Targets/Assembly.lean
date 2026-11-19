/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.Wee20.Targets.CircuitEfficiency
import TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.Wee20.Targets.Scheme
import TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.Wee20.Targets.Sim
import TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.Wee20.Targets.Garbling
import TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.Wee20.Targets.LinearEfficiency
import TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.Wee20.Targets.MatrixDH

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Pure assembly from efficiency targets

This is the only module constructing efficient PHFE primitives, either efficient simulator,
or the efficient partial garbling. Every construction merely attaches target proofs to an
unchanged raw bundle. There is no machine construction, sampling implementation, or hidden
existential choice in the assembly.

## Main definitions

* `Targets`: the conjunction of all named construction targets.
* `layeredPG`, `wee20PHFE`, `wee20Sim`, `wee20SASim`: pure efficient assembly.

## Main results

* `layeredPG_toRaw`, `wee20PHFE_toRaw`, `wee20Sim_toRaw`, `wee20SASim_toRaw`: raw identity.

## References

* [GJLS21] R. Gay, A. Jain, H. Lin, A. Sahai, *Indistinguishability Obfuscation from
  Simple-to-State Hard Problems: New Assumptions, New Techniques, and Simplification*,
  EUROCRYPT 2021; full version, Cryptology ePrint Archive, Report 2020/764,
  revision of 3 January 2025, Definitions 4.1, 4.3 and 4.6.
* [Wee20] H. Wee, *Functional Encryption for Quadratic Functions from k-Lin, Revisited*,
  TCC 2020; full version, Cryptology ePrint Archive, Report 2020/1420, Sections 2.2 and 3.
* [AGW20] M. Abdalla, J. Gong, H. Wee, *Functional Encryption for Attribute-Weighted
  Sums from k-Lin*, 2020, Lemma 2, p.12, Appendix A, pp.37-38, (28)-(32).
* [IW14] Y. Ishai, H. Wee, *Partial Garbling Schemes and Their Applications*, 2014,
  Definition 1, pp.6-7, and Section 4.2, pp.9-11.

-/

namespace TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.Wee20

open Complexity Turing TCSlib.Cryptography.Pairing
open TCSlib.Cryptography.CoinSampling

/-- The concrete construction's named uniform-efficiency targets are supplied together.
[GJLS21, Definitions 4.1, 4.3 and 4.6; Wee20, Sections 2.2 and 3].
Phase B obligation; not proved in this development.

No field is a hypothesis of raw correctness or a raw security inequality. The L1 target
supplies realisers via the shared theorem; L2 interactive-realiser hypotheses remain
separate statements of the raw security theorems. -/
structure Targets (G : BilinearGen) (ℓ n : PolyExpr) (d : ℕ) : Prop where
  /-- The five honest-algorithm targets. -/
  scheme : SchemeTargets G ℓ n d
  /-- Both concrete simulators' targets. -/
  simulators : SimTargets G ℓ n d
  /-- Deterministic layered matrix generation and reconstruction targets. -/
  garbling : PGTargets ℓ (n.mul n) d
  /-- The one uniform linear-time encryption target. -/
  linear : LinearEfficient G
  /-- The GJLS21 supported-key Boolean-circuit encryption target. -/
  circuitLinear : CircuitLinearEfficient G
  /-- Uniform L1 matrix-DH preprocessing. -/
  mddh : MddhPreTargets G

/-- All targets are exactly their displayed conjunction, including both the source
circuit target and the additional uniform-machine target. -/
theorem targets_iff (G : BilinearGen) (ℓ n : PolyExpr) (d : ℕ) : Targets G ℓ n d ↔
    SchemeTargets G ℓ n d ∧ SimTargets G ℓ n d ∧ PGTargets ℓ (n.mul n) d ∧
      LinearEfficient G ∧ CircuitLinearEfficient G ∧ MddhPreTargets G :=
  ⟨fun h => ⟨h.scheme, h.simulators, h.garbling, h.linear, h.circuitLinear, h.mddh⟩,
    fun h => ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2⟩⟩
/-- The efficient layered primitive is pure assembly of its raw family and two targets
[AGW20, Lemma 2, p.12; IW14, Definition 1 continuation, p.7]. No algorithm is selected or
changed by this assembly. -/
def layeredPG (ℓ n : PolyExpr) (d : ℕ) (hT : PGTargets ℓ n d) :
    PartialGarbling ℓ n (fun κ p => PolyTensor p (ℓ.eval κ) (n.eval κ) d) where
  toRaw := layeredPG_raw ℓ n d
  lgen_eff := hT.lgen_eff
  rec_eff := hT.rec_eff

/-- Efficient garbling retains precisely the raw layered algorithms and laws. -/
theorem layeredPG_toRaw (ℓ n : PolyExpr) (d : ℕ) (hT : PGTargets ℓ n d) :
    (layeredPG ℓ n d hT).toRaw = layeredPG_raw ℓ n d := rfl

/-- The efficient PHFE primitive is pure assembly of the layered raw scheme and the five
honest-algorithm targets [GJLS21, Definition 4.1; Wee20, Section 3.1]. -/
def wee20PHFE (G : BilinearGen) (ℓ n : PolyExpr) (d : ℕ) (hT : SchemeTargets G ℓ n d) :
    FEScheme (phfeClass ℓ n G.wG d) where
  toRaw := wee20PHFE_raw G ℓ n d (layeredPG_raw ℓ (n.mul n) d)
  pubGen_eff := hT.pubGen_eff
  setup_eff := hT.setup_eff
  enc_eff := hT.enc_eff
  keyGen_eff := hT.keyGen_eff
  dec_eff := hT.dec_eff

/-- Efficient PHFE retains precisely the raw layered construction. -/
theorem wee20PHFE_toRaw (G : BilinearGen) (ℓ n : PolyExpr) (d : ℕ)
    (hT : SchemeTargets G ℓ n d) :
    (wee20PHFE G ℓ n d hT).toRaw =
      wee20PHFE_raw G ℓ n d (layeredPG_raw ℓ (n.mul n) d) := rfl

/-- The efficient committed simulator is pure assembly from its own three concrete
targets [GJLS21, Definition 4.3]. No generic sampler-preprocessing closure is assumed. -/
noncomputable def wee20Sim (G : BilinearGen) (ℓ n : PolyExpr) (d : ℕ)
    (hT : SimTargets G ℓ n d) :
    FEScheme.Raw.Simulator (wee20PHFE_raw G ℓ n d (layeredPG_raw ℓ (n.mul n) d)) where
  toRaw := wee20Sim_raw G ℓ n d (layeredPG_raw ℓ (n.mul n) d)
  setup_eff := hT.sim_setup_eff
  enc_eff := hT.sim_enc_eff
  key_eff := hT.sim_key_eff
  state_bounded := hT.sim_state_bounded
  value_bounded := hT.sim_value_bounded

/-- Efficient committed simulation retains the exact raw simulator. -/
theorem wee20Sim_toRaw (G : BilinearGen) (ℓ n : PolyExpr) (d : ℕ)
    (hT : SimTargets G ℓ n d) :
    (wee20Sim G ℓ n d hT).toRaw =
      wee20Sim_raw G ℓ n d (layeredPG_raw ℓ (n.mul n) d) := rfl

/-- The efficient semi-adaptive simulator is pure assembly from its three concrete
targets [Wee20, Section 2.2]. Its encryption input excludes the private message. -/
noncomputable def wee20SASim (G : BilinearGen) (ℓ n : PolyExpr) (d : ℕ)
    (hT : SimTargets G ℓ n d) :
    FEScheme.Raw.SASimulator (wee20PHFE_raw G ℓ n d (layeredPG_raw ℓ (n.mul n) d)) where
  toRaw := wee20SASim_raw G ℓ n d (layeredPG_raw ℓ (n.mul n) d)
  setup_eff := hT.sa_setup_eff
  enc_eff := hT.sa_enc_eff
  key_eff := hT.sa_key_eff
  state_bounded := hT.sa_state_bounded
  value_bounded := hT.sa_value_bounded

/-- Efficient semi-adaptive simulation retains the exact raw simulator. -/
theorem wee20SASim_toRaw (G : BilinearGen) (ℓ n : PolyExpr) (d : ℕ)
    (hT : SimTargets G ℓ n d) :
    (wee20SASim G ℓ n d hT).toRaw =
      wee20SASim_raw G ℓ n d (layeredPG_raw ℓ (n.mul n) d) := rfl


/-- The assembled public-key width is the exact linear dimension accounting
[Wee20, Section 3.1; GJLS21, Definition 4.6, printed p.22]. -/
theorem wee20PHFE_mpkLen_eval (G : BilinearGen) (ℓ n : PolyExpr) (d κ : ℕ)
    (hT : SchemeTargets G ℓ n d) :
    (wee20PHFE G ℓ n d hT).mpkLen.eval κ =
      (16 + 24 * n.eval κ + 8 * ℓ.eval κ) * G.wG.eval κ + 10 :=
  (congrArg (fun S : FEScheme.Raw (phfeClass ℓ n G.wG d) => S.mpkLen.eval κ)
    (wee20PHFE_toRaw G ℓ n d hT)).trans
    ((congrArg (fun w : PolyExpr => w.eval κ)
      (wee20PHFE_raw_mpkLen G ℓ n d (layeredPG_raw ℓ (n.mul n) d))).trans
      (PHFE.mpkLen_eval G ℓ n κ))

/-- The assembled ciphertext has exactly `(6n+5)wG` bits, independently of the
function degree and public-vector length [Wee20, Section 3.1]. The public input is
passed separately and is not counted as part of the ciphertext. -/
theorem wee20PHFE_ctLen_eval (G : BilinearGen) (ℓ n : PolyExpr) (d κ : ℕ)
    (hT : SchemeTargets G ℓ n d) :
    (wee20PHFE G ℓ n d hT).ctLen.eval κ = (6 * n.eval κ + 5) * G.wG.eval κ :=
  (congrArg (fun S : FEScheme.Raw (phfeClass ℓ n G.wG d) => S.ctLen.eval κ)
    (wee20PHFE_toRaw G ℓ n d hT)).trans
    ((congrArg (fun w : PolyExpr => w.eval κ)
      (wee20PHFE_raw_ctLen G ℓ n d (layeredPG_raw ℓ (n.mul n) d))).trans
      (PHFE.ctLen_eval G n κ))

end TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.Wee20
