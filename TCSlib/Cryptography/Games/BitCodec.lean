/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TCSlib.Cryptography.Games.Machines
import TCSlib.Cryptography.Asymptotic.Adversary

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Bit-string oracles and their machine codec

The security games of [PS10] ch. 5–8 give machine adversaries a finite family of oracles on
fixed-length bit strings: a tagging oracle, a signing oracle, encryption and decryption oracles,
and so on. At parameter `n` oracle `i` takes `din i` bits and answers with `dout i` bits
(`bitSpec`). This file fixes the codec through which a next-move machine (`NUPPT.toComp`) plays
against such a family, and through which it returns a fixed-length output (`bitCodec`):
- **a query** to oracle `i` on `x` is the output `⟨[false], ⟨1^i, x⟩⟩`;
- **a final output** `a` is `⟨[true], a⟩`;
- **anything else**, a malformed or wrong-length string, decodes to the all-`false` output (the
  ch. 2–4 layer's convention D7: ill-formed outputs count as a fixed default);
- **a log entry** `(i, x, y)` is encoded as `⟨1^i, ⟨x, y⟩⟩`;
- **when the query budget runs out**, the output is the all-`false` string.

It is the shared codec of every prong's statements, and the T0 definitions of the efficiency fill
(`briefs/pass-shelat-ch5-8/fills/efficiency/`).

## Main definitions

* `Games.bitSpec din dout`: `k` oracles on fixed-length bit strings.
* `Games.decodeIdx`, `Games.decodeBitMove`: decoding of an oracle index and of a machine output as
  a move.
* `Games.bitCodec din dout dα`: the codec.

## Main results

* `Games.decodeIdx_replicate`, `Games.decodeBitMove_query`, `Games.decodeBitMove_ret`: the
  well-formed encodings decode as intended.

## References

* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed., January 2010,
  §3.8.1 (oracle machines) and Definitions 134.2, 136.2 and 168.1 (oracle adversaries).
-/

namespace TCSlib.Cryptography.Games

open Complexity Turing

variable {k : ℕ}

/-- **`k` oracles on fixed-length bit strings:** oracle `i` takes `din i` bits and answers with
`dout i` bits. -/
abbrev bitSpec (din dout : Fin k → ℕ) : OracleSpec (Fin k) :=
  ⟨fun i => Fin (din i) → Bool, fun i => Fin (dout i) → Bool⟩

/-- Decoding of an oracle index written in unary: `1^i` with `i < k` is `i`. -/
def decodeIdx (k : ℕ) (iw : List Bool) : Option (Fin k) :=
  if h : iw.length < k then some ⟨iw.length, h⟩ else none

/-- The unary code of an index decodes to it. -/
theorem decodeIdx_replicate (i : Fin k) : decodeIdx k (List.replicate i true) = some i := by
  unfold decodeIdx
  have h : (List.replicate (i : ℕ) true).length < k := by simp
  rw [dif_pos h]
  exact congrArg some (Fin.ext (by simp))

/-- The default output: the all-`false` string. -/
def zeroBits (d : ℕ) : Fin d → Bool := fun _ => false

/-- Decoding of a machine output as a move against `bitSpec din dout` with `dα`-bit outputs:
`⟨[false], ⟨1^i, x⟩⟩` with `i < k` and `|x| = din i` is the query `x` to oracle `i`;
`⟨[true], a⟩` with `|a| = dα` is the output `a`; anything else is the output `zeroBits dα`. -/
def decodeBitMove (din dout : Fin k → ℕ) (dα : ℕ) (w : List Bool) :
    Move (bitSpec din dout) (Fin dα → Bool) :=
  match pairDecode w with
  | some ([false], rest) =>
    match pairDecode rest with
    | some (iw, xw) =>
      match decodeIdx k iw with
      | some i =>
        match decodeFin (din i) xw with
        | some x => .query i x
        | none => .ret (zeroBits dα)
      | none => .ret (zeroBits dα)
    | none => .ret (zeroBits dα)
  | some ([true], aw) =>
    match decodeFin dα aw with
    | some a => .ret a
    | none => .ret (zeroBits dα)
  | _ => .ret (zeroBits dα)

/-- **The codec of bit-string oracles:** moves decoded by `decodeBitMove`, a log entry
`(i, x, y)` encoded as `⟨1^i, ⟨x, y⟩⟩`, and the all-`false` output when the budget runs out. -/
def bitCodec (din dout : Fin k → ℕ) (dα : ℕ) :
    MachineCodec (bitSpec din dout) (Fin dα → Bool) where
  decodeMove := decodeBitMove din dout dα
  encodeEntry e :=
    pairEncode (List.replicate e.1 true) (pairEncode (List.ofFn e.2.1) (List.ofFn e.2.2))
  timeout := zeroBits dα

/-- A well-formed query decodes as the query. -/
theorem decodeBitMove_query (din dout : Fin k → ℕ) (dα : ℕ) (i : Fin k)
    (x : Fin (din i) → Bool) :
    decodeBitMove din dout dα
        (pairEncode [false] (pairEncode (List.replicate i true) (List.ofFn x))) = .query i x := by
  simp [decodeBitMove, pairDecode_pairEncode, decodeIdx_replicate, decodeFin_ofFn]

/-- A well-formed output decodes as the output. -/
theorem decodeBitMove_ret (din dout : Fin k → ℕ) (dα : ℕ) (a : Fin dα → Bool) :
    decodeBitMove din dout dα (pairEncode [true] (List.ofFn a)) = .ret a := by
  simp [decodeBitMove, pairDecode_pairEncode, decodeFin_ofFn]

end TCSlib.Cryptography.Games
