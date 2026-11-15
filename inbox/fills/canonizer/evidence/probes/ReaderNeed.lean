import TCSlib.Complexity.TuringMachine.CodeSimulator

/-! Seal probe of the fill `canonizer` (checkpoint 1): the three facts the route needs, each
closed by definitional unfolding at the issue base, where no published lemma states them.
Unsealed, all three elaborate. Under every whole-closure seal each must fail exactly once:
- `need_codeFormat` unfolds `oneTapeFormat` (and `codeDecode`) of `CodeFormat.lean`;
- `need_codeSimulator` unfolds `oneTapeMachineFormat` of `CodeSimulator.lean`;
- `need_transport` is the transport of `exists_polyCanonizer`'s specification that
  `Turing.exists_uniformMachineCode` (`Diagonalization/EXPCOM.lean`) performs by unfolding.
So each of the two readers is needed, and together they give the transport. -/

open Turing

theorem need_codeFormat (xs : List Bool) :
    oneTapeFormat.serialize (oneTapeFormat.decode xs) = (codeDecode xs).serialize := rfl

theorem need_codeSimulator (α : List Bool) :
    oneTapeMachineFormat.serialize (oneTapeMachineFormat.decode α) =
      oneTapeFormat.serialize (oneTapeFormat.decode α) := rfl

theorem need_transport :
    ∃ (C : FinTM Bool) (d : ℕ),
      C.ComputesFunInTime (fun α => (codeDecode α).serialize) fun n => d * (n + 1) ^ d :=
  oneTapeMachineFormat.exists_polyCanonizer
