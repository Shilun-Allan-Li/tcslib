import TCSlib.Cryptography.ZeroKnowledge.ThreeColoring.Protocol

set_option maxHeartbeats 400000
set_option autoImplicit false

/-! Controls for the col-a seal: three readings of sealed definitions through their bodies.
Each must FAIL in the sealed section and PASS in the unsealed one. -/

namespace TCSlib.Cryptography.SealACtl

open Complexity Turing

section Sealed
attribute [local irreducible] _root_.Complexity.PolyExpr.normal _root_.Complexity.PolyTimeComputable _root_.Complexity.pairFstD _root_.Complexity.pairSndD _root_.TCSlib.Cryptography.ColMachines.colorVal _root_.TCSlib.Cryptography.ColMachines.countTrue _root_.TCSlib.Cryptography.EncodingMachines.divNum _root_.TCSlib.Cryptography.EncodingMachines.firstIdx _root_.TCSlib.Cryptography.EncodingMachines.modNum _root_.TCSlib.Cryptography.HardcoreBit.PushesUniform _root_.TCSlib.Cryptography.L3COL _root_.TCSlib.Cryptography.Negligible _root_.TCSlib.Cryptography.ProperColoring _root_.TCSlib.Cryptography.Protocol.ProverBounded _root_.TCSlib.Cryptography.Protocol.outV _root_.TCSlib.Cryptography.Protocol.withV _root_.TCSlib.Cryptography.R3COL _root_.TCSlib.Cryptography.StatClose _root_.TCSlib.Cryptography.Strategy.coinLen _root_.TCSlib.Cryptography.ThreeColorable _root_.TCSlib.Cryptography.decColoring _root_.TCSlib.Cryptography.decGraph _root_.TCSlib.Cryptography.decGraphAt _root_.TCSlib.Cryptography.edgeIdxOfMsg _root_.TCSlib.Cryptography.edgeMsg _root_.TCSlib.Cryptography.edgeOf _root_.TCSlib.Cryptography.encColoring _root_.TCSlib.Cryptography.encGraph _root_.TCSlib.Cryptography.exec _root_.TCSlib.Cryptography.instDecidableProperColoring _root_.TCSlib.Cryptography.moverIsV _root_.TCSlib.Cryptography.sampleEdgeIdx _root_.TCSlib.Cryptography.samplePerm3 _root_.TCSlib.Cryptography.uprob _root_.Turing.pairEncode _root_.TCSlib.Cryptography.ColRep.chView _root_.TCSlib.Cryptography.ColRep.blockRead

/-- C1: destructuring `R3COL` (Language.lean) reads its body. -/
example (x y : List Bool) (h : R3COL x y) : ∃ n : ℕ, x.length = n * n := by
  obtain ⟨n, G, c, rfl, rfl, -⟩ := h
  exact ⟨n, length_encGraph G⟩

/-- C2: `colorVal` (Machines.lean) by `rfl`. -/
example (y : List Bool) (u : ℕ) :
    ColMachines.colorVal y u = (2 * (y.getD (2 * u) false).toNat + (y.getD (2 * u + 1) false).toNat) % 3 :=
  rfl

/-- C3: `ColRep.chView` (helper) by `rfl`. -/
example (ch : ℕ → List Bool) : ColRep.chView ch 1 = [ch 0, []] := rfl

end Sealed

section Unsealed

example (x y : List Bool) (h : R3COL x y) : ∃ n : ℕ, x.length = n * n := by
  obtain ⟨n, G, c, rfl, rfl, -⟩ := h
  exact ⟨n, length_encGraph G⟩

example (y : List Bool) (u : ℕ) :
    ColMachines.colorVal y u = (2 * (y.getD (2 * u) false).toNat + (y.getD (2 * u + 1) false).toNat) % 3 :=
  rfl

example (ch : ℕ → List Bool) : ColRep.chView ch 1 = [ch 0, []] := rfl

end Unsealed

end TCSlib.Cryptography.SealACtl
