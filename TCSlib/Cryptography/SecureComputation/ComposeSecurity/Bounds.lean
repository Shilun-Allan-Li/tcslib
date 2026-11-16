/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TCSlib.Cryptography.SecureComputation.ComposeSecurity.Machines

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Polynomial length bounds

The advice of a non-uniform reduction has polynomially bounded length (`NUPPT.advice_length`). The
reductions of the composition theorem [Gol04, §7.3.1, proof of Theorem 7.3.3] hard-wire views and
outputs of executions, so their lengths must be bounded by a polynomial in `n`. This file collects
the lengths of the encodings (`encodeMsgs`, the machine layouts), of the transcripts, and of the
outputs of machines and efficient strategies.

## Main results

* `ComposeBound.length_encodeMsgs_le`, `length_transcriptWith_fst_le`, `_snd_le`.
* `ComposeBound.length_runAt_le`, `Efficient.length_next_le`, `length_ilayout`.

## References

* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed., January 2010,
  §2.1 (non-uniform PPT machines, Definition 26.8) and §4.4 (time complexity of interactive
  machines).
-/

namespace TCSlib.Cryptography.SecureComputation.ComposeBound

open Complexity Turing

/-! ### Lengths of encodings and outputs -/

/-- **A transcript has at most `rounds` messages per party**:
`|(π.transcriptWith P' x y z r).1| ≤ π.rounds(|x|)` (`Compose.exec_eq_map`). -/
theorem length_transcriptWith_fst_le (π : Protocol) (P' : Strategy) (x y z : List Bool)
    (r : π.ExecCoins P' x) : (π.transcriptWith P' x y z r).1.length ≤ π.rounds.eval x.length := by
  rw [Protocol.transcriptWith_eq, Compose.exec_eq_map, List.length_map]
  exact (List.length_filter_le _ _).trans (List.length_range).le

/-- The verifier's half: `|(π.transcriptWith P' x y z r).2| ≤ π.rounds(|x|)`. -/
theorem length_transcriptWith_snd_le (π : Protocol) (P' : Strategy) (x y z : List Bool)
    (r : π.ExecCoins P' x) : (π.transcriptWith P' x y z r).2.length ≤ π.rounds.eval x.length := by
  rw [Protocol.transcriptWith_eq, Compose.exec_eq_map, List.length_map]
  exact (List.length_filter_le _ _).trans (List.length_range).le

/-- **The length of an encoded history**: if every message has at most `c` bits,
`|encodeMsgs l| ≤ |l| (2c + 2)` (`encodeMsgs_eq_flatMap`, `BinArith.length_encWords_le`).
It is the public `CommitmentLemmas.length_encodeMsgs_le` (`ZeroKnowledge/CommitmentLemmas.lean`). -/
theorem length_encodeMsgs_le (l : List (List Bool)) (c : ℕ) (h : ∀ w ∈ l, w.length ≤ c) :
    (Strategy.encodeMsgs l).length ≤ l.length * (2 * c + 2) :=
  TCSlib.Cryptography.CommitmentLemmas.length_encodeMsgs_le l c h

/-- **The length of a machine layout**:
`|layout u y α r| = 2(2(2|u| + 2 + |y|) + 2 + |α|) + 2 + |r|`
(`NUPPT.layout_eq`, `length_pairEncode`). -/
theorem length_layout (u y α r : List Bool) :
    (NUPPT.layout u y α r).length = 2 * (2 * (2 * u.length + 2 + y.length) + 2 + α.length) + 2 +
      r.length := by
  rw [NUPPT.layout_eq, length_pairEncode, length_pairEncode, length_pairEncode]

/-- **The output of a machine is polynomially long**:
`|A.runAt n y r| ≤ A.Ct (|layout 1^n y (A.advice n) ⟦r⟧| + 1)^A.ct`
(`NUPPT.output_length_le`, `NUPPT.runAtL_eq_output_layout`). -/
theorem length_runAt_le (A : NUPPT) (n : ℕ) (y : List Bool) (r : A.Coins n) :
    (A.runAt n y r).length ≤ A.Ct * (2 * (2 * (2 * n + 2 + y.length) + 2 +
      (A.advice n).length) + 2 + A.coinLen n + 1) ^ A.ct := by
  have h := A.output_length_le (NUPPT.layout (List.replicate n true) y (A.advice n) (List.ofFn r))
  rw [NUPPT.timeBound_def, length_layout, List.length_replicate, List.length_ofFn] at h
  rw [NUPPT.runAt_eq, NUPPT.runAtL_eq_output_layout]
  exact h

/-- **The next message of an efficient strategy is polynomially long** in the length of its
activation's layout: for some `C, c`, `|S.next x z r hist| ≤ C (|GI.ilayout x z hist r| + 1)^c`
(`ComposeMachines.Efficient.exists_polyTime`, `PolyTimeComputable.output_length_le`). -/
theorem Efficient.length_next_le {S : Strategy} (h : S.Efficient) :
    ∃ C c : ℕ, ∀ x z r hist, (S.next x z r hist).length ≤
      C * ((GI.ilayout x z hist r).length + 1) ^ c := by
  obtain ⟨F, hF, hnext⟩ := ComposeMachines.Efficient.exists_polyTime h
  obtain ⟨C, c, hC⟩ := hF.output_length_le
  exact ⟨C, c, fun x z r hist => by rw [hnext]; exact hC _⟩

/-- **The length of a strategy layout**: `|GI.ilayout x z hist r| =
2(2(2|x| + 2 + (2(2|x| + 2 + |z|) + 2 + |encodeMsgs hist|)) + 2) + 2 + |r|`. -/
theorem length_ilayout (x z : List Bool) (hist : List (List Bool)) (r : List Bool) :
    (GI.ilayout x z hist r).length =
      2 * (2 * (2 * x.length + 2 + (2 * (2 * x.length + 2 + z.length) + 2 +
        (Strategy.encodeMsgs hist).length)) + 2) + 2 + r.length := by
  rw [GI.ilayout_def, length_layout, List.length_replicate, length_pairEncode, length_pairEncode,
    List.length_nil, Nat.add_zero]

end TCSlib.Cryptography.SecureComputation.ComposeBound
