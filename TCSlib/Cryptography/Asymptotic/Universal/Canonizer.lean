/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TCSlib.Complexity.TuringMachine.CodeSimulator

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# An effective machine code with a polynomial canonizer

The encoding hypothesis of [PS10, §2.13, Theorem 63.1] as formalized (`CanonizerExp`) asks for an
effective machine code whose canonizer runs in time at most exponential in the code length. The
machine library's one-tape code format has a canonizer running in time `d · (n + 1)^d` on every
input (`Turing.MachineFormat.exists_polyCanonizer`, at `Turing.oneTapeMachineFormat`). This file
reads its specification as one of `α ↦ (codeDecode α).serialize`
(`Turing.oneTapeMachineFormat_serialize_decode`, `Turing.oneTapeFormat_serialize_decode`), builds
the effective machine code with the serialization `CodeTM.serialize`, the decoder `codeDecode`
and that canonizer (the scheme of `Turing.exists_uniformMachineCode`, here with its time bound
visible), and bounds the polynomial time by an exponential: `d · (k + 1)^d ≤ d · 2^{d k}`.

## Main results

* `TCSlib.Cryptography.exists_codeCanonizer`: a machine computing `α ↦ (codeDecode α).serialize`
  in time `d · (n + 1)^d`.
* `TCSlib.Cryptography.exists_effectiveMachineCode_canonizerTime_le`: an effective machine code
  with `canonizerTime k ≤ d · 2^{d k}` for every `k`.

## References

* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed., January 2010,
  §2.13, Theorem 63.1 (book p. 63).
-/

namespace TCSlib.Cryptography

open Turing

/-- **A polynomial canonizer of the one-tape codes:** there are a machine `C` and a degree `d`
such that `C` computes `α ↦ (codeDecode α).serialize` in time `n ↦ d · (n + 1)^d`, on every input
(malformed codes included: they decode to the fallback machine):
`∃ C d, C.ComputesFunInTime (fun α => (codeDecode α).serialize) fun n => d * (n + 1) ^ d`.

**Proof sketch.** `Turing.MachineFormat.exists_polyCanonizer` at `oneTapeMachineFormat` computes
`α ↦ oneTapeMachineFormat.serialize (oneTapeMachineFormat.decode α)`, which is
`(codeDecode α).serialize` by the readers `oneTapeMachineFormat_serialize_decode` and
`oneTapeFormat_serialize_decode`. -/
theorem exists_codeCanonizer :
    ∃ (C : FinTM Bool) (d : ℕ),
      C.ComputesFunInTime (fun α => (codeDecode α).serialize) fun n => d * (n + 1) ^ d := by
  obtain ⟨C, d, hC⟩ := oneTapeMachineFormat.exists_polyCanonizer
  have hf : (fun α => oneTapeMachineFormat.serialize (oneTapeMachineFormat.decode α)) =
      fun α => (codeDecode α).serialize :=
    funext fun α =>
      (oneTapeMachineFormat_serialize_decode α).trans (oneTapeFormat_serialize_decode α)
  exact ⟨C, d, hf ▸ hC⟩

/-- **An effective machine code with an exponential canonizer** [PS10, §2.13, the encoding
behind Theorem 63.1]: there are an effective machine code `c` and `d : ℕ` with
`c.canonizerTime k ≤ d · 2^{d k}` for every `k`.

**Proof sketch.** Take `C, d` from `exists_codeCanonizer` and the code
`⟨CodeTM.serialize, codeDecode, codeDecode_serialize_pad⟩` with canonizer `C` and
`canonizerTime n = d · (n + 1)^d`. Since `k + 1 ≤ 2^k` (`Nat.lt_two_pow_self`),
`(k + 1)^d ≤ (2^k)^d = 2^{d k}` (`Nat.pow_le_pow_left`, `pow_mul`). The case `d = 0` needs no
care (both sides are `0`), nor does `k = 0` (`1 ≤ 1`). -/
theorem exists_effectiveMachineCode_canonizerTime_le :
    ∃ (c : EffectiveMachineCode) (d : ℕ), ∀ k, c.canonizerTime k ≤ d * 2 ^ (d * k) := by
  obtain ⟨C, d, hC⟩ := exists_codeCanonizer
  refine ⟨{ toMachineCode := ⟨CodeTM.serialize, codeDecode, codeDecode_serialize_pad⟩
            canonizer := C
            canonizerTime := fun n => d * (n + 1) ^ d
            canonizer_computes := hC }, d, fun k => ?_⟩
  show d * (k + 1) ^ d ≤ d * 2 ^ (d * k)
  have hk : k + 1 ≤ 2 ^ k := Nat.lt_two_pow_self
  have hpow : (k + 1) ^ d ≤ 2 ^ (d * k) := by
    rw [mul_comm, pow_mul]
    exact Nat.pow_le_pow_left hk d
  exact Nat.mul_le_mul_left d hpow

end TCSlib.Cryptography
