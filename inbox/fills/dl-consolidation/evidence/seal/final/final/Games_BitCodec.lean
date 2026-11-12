/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Lean
import TCSlib.Cryptography.Games.Machines
import TCSlib.Cryptography.Asymptotic.Adversary
import TCSlib.Cryptography.Games.Probability
/- DLC-SEAL Games_BitCodec: whole-file closure seal of `TCSlib/Cryptography/Games/BitCodec.lean`. -/
set_option maxHeartbeats 0 in
run_cmd do
  let env ← Lean.getEnv
  let excl : List Lean.Name := []
  let mut sealed : Array Lean.Name := #[]
  let mut abbrevs : Nat := 0
  let mut already : Nat := 0
  let mut excluded : Nat := 0
  for (n, ci) in env.constants.map₁.toList do
    let some mi := env.getModuleIdxFor? n | continue
    let m := env.header.moduleNames[mi.toNat]!
    unless (`TCSlib).isPrefixOf m do continue
    let .defnInfo d := ci | continue
    if excl.contains n then
      excluded := excluded + 1
      continue
    match d.hints with
    | .abbrev =>
      abbrevs := abbrevs + 1
      continue
    | _ => pure ()
    let st ← Lean.Elab.Command.liftCoreM <| Lean.getReducibilityStatus n
    if st == .irreducible then
      already := already + 1
      sealed := sealed.push n
      continue
    Lean.Elab.Command.elabCommand (← `(command| attribute [local irreducible] $(Lean.mkIdent n):ident))
    let st' ← Lean.Elab.Command.liftCoreM <| Lean.getReducibilityStatus n
    unless st' == .irreducible do throwError "DLC-SEAL: not sealed {n}"
    sealed := sealed.push n
  Lean.modifyEnv fun cur =>
    Lean.Meta.globalInstanceExtension.modifyState cur fun s => sealed.foldl (fun s n => s.erase n) s
  let env' ← Lean.getEnv
  for n in sealed do
    if Lean.Meta.isGlobalInstance env' n then throwError "DLC-SEAL: instance unfolding kept for {n}"
  Lean.logInfo m!"DLC-SEAL Games_BitCodec: sealed={sealed.size} (already irreducible {already}) abbrev-excluded={abbrevs} excluded={excluded}"


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
* `Games.encodeBitMove`: the canonical word of a move.
* `Games.bitCodec din dout dα`: the codec.
* `Games.castImpl`: an implementation of bit-string oracles read along equal length functions.

## Main results

* `Games.decodeIdx_replicate`, `Games.decodeBitMove_query`, `Games.decodeBitMove_ret`: the
  well-formed encodings decode as intended.
* `Games.decodeIdx_eq_some_iff`, `Games.decodeBitMove_eq_query_iff`: only the canonical words
  decode as an index or a query.
* `Games.decodeBitMove_of_not_canonical`: every other word decodes to the all-`false` output.
* `Games.padFin_ofFn_zeroBits`, `Games.padFin_replicate_false`, `Games.padFin_nil`,
  `Games.decodeFin_nil_getD`: all-`false` strings and the empty answer read as `zeroBits`.
* `Games.simulate_castImpl_toCompOn`, `Games.expect_simulate_castImpl_toCompOn`: transport of a
  machine's run between two codecs with equal lengths.

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

/-- Oracle `i` of `bitSpec din dout` takes `din i`-bit strings. -/
theorem bitSpec_dom (din dout : Fin k → ℕ) (i : Fin k) :
    (bitSpec din dout).dom i = (Fin (din i) → Bool) :=
  rfl

/-- Oracle `i` of `bitSpec din dout` answers with `dout i`-bit strings. -/
theorem bitSpec_rng (din dout : Fin k → ℕ) (i : Fin k) :
    (bitSpec din dout).rng i = (Fin (dout i) → Bool) :=
  rfl

/-- Decoding of an oracle index written in unary: `1^i` with `i < k` is `i`; every other word
(one containing `false`, or of length at least `k`) is `none`. -/
def decodeIdx (k : ℕ) (iw : List Bool) : Option (Fin k) :=
  if h : iw.length < k ∧ iw = List.replicate iw.length true then some ⟨iw.length, h.1⟩ else none

/-- The unary code of an index decodes to it. -/
theorem decodeIdx_replicate (i : Fin k) : decodeIdx k (List.replicate i true) = some i := by
  unfold decodeIdx
  have h : (List.replicate (i : ℕ) true).length < k ∧
      List.replicate (i : ℕ) true =
        List.replicate (List.replicate (i : ℕ) true).length true := by
    simp
  rw [dif_pos h]
  exact congrArg some (Fin.ext (by simp))

/-- **Exactly the unary codes decode**, each to its index:
`decodeIdx k iw = some i ↔ iw = 1^i`. -/
theorem decodeIdx_eq_some_iff {iw : List Bool} {i : Fin k} :
    decodeIdx k iw = some i ↔ iw = List.replicate i true := by
  refine ⟨fun h => ?_, fun h => h ▸ decodeIdx_replicate i⟩
  unfold decodeIdx at h
  split_ifs at h with hw
  rw [Option.some.injEq] at h
  rw [← h]
  exact hw.2

/-- **Every other word is rejected:** `decodeIdx k iw = none` exactly when `iw` is the unary code
of no index below `k`. -/
theorem decodeIdx_eq_none_iff {iw : List Bool} :
    decodeIdx k iw = none ↔ ∀ i : Fin k, iw ≠ List.replicate i true := by
  constructor
  · intro h i hi
    rw [decodeIdx_eq_some_iff.2 hi] at h
    exact Option.some_ne_none i h
  · intro h
    cases hd : decodeIdx k iw with
    | none => rfl
    | some i => exact absurd (decodeIdx_eq_some_iff.1 hd) (h i)

/-- The default output: the all-`false` string. -/
def zeroBits (d : ℕ) : Fin d → Bool := fun _ => false

/-- Every bit of the default output is `false`: `zeroBits d j = false`. -/
theorem zeroBits_apply (d : ℕ) (j : Fin d) : zeroBits d j = false :=
  rfl

/-- The default output, written as a string, is `d` copies of `false`:
`List.ofFn (zeroBits d) = List.replicate d false`. -/
theorem ofFn_zeroBits (d : ℕ) : List.ofFn (zeroBits d) = List.replicate d false := by
  rw [show zeroBits d = fun _ => false from rfl, List.ofFn_const]

/-- The all-`false` answer, read at any width, is all-`false`:
`padFin d ⟦zeroBits m⟧ = zeroBits d`. -/
theorem padFin_ofFn_zeroBits (d m : ℕ) : padFin d (List.ofFn (zeroBits m)) = zeroBits d := by
  funext i
  rw [padFin_apply, ofFn_zeroBits, zeroBits_apply, List.getD_eq_getElem?_getD,
    List.getElem?_replicate]
  split <;> rfl

/-- An all-`false` list reads as the all-`false` vector at every width:
`padFin d (List.replicate m false) = zeroBits d`. -/
theorem padFin_replicate_false (d m : ℕ) : padFin d (List.replicate m false) = zeroBits d := by
  rw [← ofFn_zeroBits, padFin_ofFn_zeroBits]

/-- The empty list reads as the all-`false` vector: `padFin d [] = zeroBits d`. -/
theorem padFin_nil (d : ℕ) : padFin d [] = zeroBits d := padFin_replicate_false d 0

/-- An empty answer decodes to all-`false` at every length:
`(decodeFin ℓ []).getD (zeroBits ℓ) = zeroBits ℓ`. -/
theorem decodeFin_nil_getD (ℓ : ℕ) : (decodeFin ℓ []).getD (zeroBits ℓ) = zeroBits ℓ := by
  rw [decodeFin_eq]
  split
  · next h =>
    subst h
    funext i
    exact absurd i.isLt (Nat.not_lt_zero _)
  · rfl

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

/-- **The canonical word of a move:** the query `x` to oracle `i` is `⟨[false], ⟨1^i, x⟩⟩`, and
the output `a` is `⟨[true], a⟩`. `decodeBitMove` inverts it (`decodeBitMove_encodeBitMove`). -/
def encodeBitMove (din dout : Fin k → ℕ) (dα : ℕ) :
    Move (bitSpec din dout) (Fin dα → Bool) → List Bool
  | .query i x => pairEncode [false] (pairEncode (List.replicate i true) (List.ofFn x))
  | .ret a => pairEncode [true] (List.ofFn a)

/-- The canonical word of a query:
`encodeBitMove din dout dα (query i x) = ⟨[false], ⟨1^i, x⟩⟩`. -/
theorem encodeBitMove_query (din dout : Fin k → ℕ) (dα : ℕ) (i : Fin k)
    (x : Fin (din i) → Bool) :
    encodeBitMove din dout dα (.query i x) =
      pairEncode [false] (pairEncode (List.replicate i true) (List.ofFn x)) :=
  rfl

/-- The canonical word of an output: `encodeBitMove din dout dα (ret a) = ⟨[true], a⟩`. -/
theorem encodeBitMove_ret (din dout : Fin k → ℕ) (dα : ℕ) (a : Fin dα → Bool) :
    encodeBitMove din dout dα (.ret a) = pairEncode [true] (List.ofFn a) :=
  rfl

/-- **The codec of bit-string oracles:** moves decoded by `decodeBitMove`, a log entry
`(i, x, y)` encoded as `⟨1^i, ⟨x, y⟩⟩`, and the all-`false` output when the budget runs out. -/
def bitCodec (din dout : Fin k → ℕ) (dα : ℕ) :
    MachineCodec (bitSpec din dout) (Fin dα → Bool) where
  decodeMove := decodeBitMove din dout dα
  encodeEntry e :=
    pairEncode (List.replicate e.1 true) (pairEncode (List.ofFn e.2.1) (List.ofFn e.2.2))
  timeout := zeroBits dα

/-- The codec decodes moves with `decodeBitMove`: `(bitCodec din dout dα).decodeMove w =
decodeBitMove din dout dα w`. -/
theorem bitCodec_decodeMove (din dout : Fin k → ℕ) (dα : ℕ) (w : List Bool) :
    (bitCodec din dout dα).decodeMove w = decodeBitMove din dout dα w :=
  rfl

/-- The codec encodes the log entry `(i, x, y)` as `⟨1^i, ⟨x, y⟩⟩`. -/
theorem bitCodec_encodeEntry (din dout : Fin k → ℕ) (dα : ℕ)
    (e : Σ i, (bitSpec din dout).dom i × (bitSpec din dout).rng i) :
    (bitCodec din dout dα).encodeEntry e =
      pairEncode (List.replicate e.1 true) (pairEncode (List.ofFn e.2.1) (List.ofFn e.2.2)) :=
  rfl

/-- When the budget runs out, the codec's output is all-`false`:
`(bitCodec din dout dα).timeout = zeroBits dα`. -/
theorem bitCodec_timeout (din dout : Fin k → ℕ) (dα : ℕ) :
    (bitCodec din dout dα).timeout = zeroBits dα :=
  rfl

/-- The codec's log encoding does not depend on the output length: `bitCodec din dout dα` and
`bitCodec din dout dα'` encode every log alike. -/
theorem encodeLog_bitCodec (din dout : Fin k → ℕ) (dα dα' : ℕ) (h : QueryLog (bitSpec din dout)) :
    (bitCodec din dout dα).encodeLog h = (bitCodec din dout dα').encodeLog h := by
  induction h with
  | nil => rw [MachineCodec.encodeLog_nil, MachineCodec.encodeLog_nil]
  | cons e h ih =>
    rw [MachineCodec.encodeLog_cons, MachineCodec.encodeLog_cons, ih, bitCodec_encodeEntry,
      bitCodec_encodeEntry]

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

/-- **Only the canonical query word decodes as a query:** `decodeBitMove din dout dα w` is the
query `x` to oracle `i` exactly when `w = ⟨[false], ⟨1^i, x⟩⟩` (the converse of
`decodeBitMove_query`).

**Proof sketch.** Follow `decodeBitMove`'s branches: only the branch in which the tag is `[false]`,
the rest parses as a pair, the index word decodes and the payload has the right length returns a
query. There, each successful parse determines its input: a parsed pair is the pairing of its parts
(`eq_pairEncode_of_pairDecode`), a decoded index word is `1^i` (`decodeIdx_eq_some_iff`), and a
decoded payload is `List.ofFn x`. -/
theorem decodeBitMove_eq_query_iff {din dout : Fin k → ℕ} {dα : ℕ} {w : List Bool} {i : Fin k}
    {x : Fin (din i) → Bool} :
    decodeBitMove din dout dα w = .query i x ↔
      w = pairEncode [false] (pairEncode (List.replicate i true) (List.ofFn x)) := by
  refine ⟨fun h => ?_, fun h => h ▸ decodeBitMove_query din dout dα i x⟩
  unfold decodeBitMove at h
  split at h
  · rename_i rest hw
    split at h
    · rename_i iw xw hr
      split at h
      · rename_i j hj
        split at h
        · rename_i x' hx
          cases h
          rw [eq_pairEncode_of_pairDecode _ _ _ hw, eq_pairEncode_of_pairDecode _ _ _ hr,
            decodeIdx_eq_some_iff.1 hj, (decodeFin_eq_some_iff _ _ _).1 hx]
        · cases h
      · cases h
    · cases h
  · split at h <;> cases h
  · cases h

/-- **The default:** a word that is neither a canonical query `⟨[false], ⟨1^i, x⟩⟩` nor a
canonical output `⟨[true], a⟩` decodes to the output `zeroBits dα`. With `decodeBitMove_query`
and `decodeBitMove_ret` this determines `decodeBitMove` on every word.

**Proof sketch.** Follow `decodeBitMove`'s branches. Every branch but two returns `zeroBits dα`.
In the query branch, the successful parses make `w` a canonical query word, as in
`decodeBitMove_eq_query_iff`, against `hq`; in the output branch, they make `w` a canonical output
word, against `hr`. -/
theorem decodeBitMove_of_not_canonical {din dout : Fin k → ℕ} {dα : ℕ} {w : List Bool}
    (hq : ∀ (i : Fin k) (x : Fin (din i) → Bool),
      w ≠ pairEncode [false] (pairEncode (List.replicate i true) (List.ofFn x)))
    (hr : ∀ a : Fin dα → Bool, w ≠ pairEncode [true] (List.ofFn a)) :
    decodeBitMove din dout dα w = .ret (zeroBits dα) := by
  unfold decodeBitMove
  split
  · rename_i rest hw
    split
    · rename_i iw xw hr'
      split
      · rename_i j hj
        split
        · rename_i x hx
          refine absurd ?_ (hq j x)
          rw [eq_pairEncode_of_pairDecode _ _ _ hw, eq_pairEncode_of_pairDecode _ _ _ hr',
            decodeIdx_eq_some_iff.1 hj, (decodeFin_eq_some_iff _ _ _).1 hx]
        · rfl
      · rfl
    · rfl
  · rename_i aw hw
    split
    · rename_i a ha
      refine absurd ?_ (hr a)
      rw [eq_pairEncode_of_pairDecode _ _ _ hw, (decodeFin_eq_some_iff _ _ _).1 ha]
    · rfl
  · rfl

/-- **Canonical words decode to their move:** `decodeBitMove (encodeBitMove m) = m`. -/
theorem decodeBitMove_encodeBitMove (din dout : Fin k → ℕ) (dα : ℕ)
    (m : Move (bitSpec din dout) (Fin dα → Bool)) :
    decodeBitMove din dout dα (encodeBitMove din dout dα m) = m := by
  cases m with
  | query i x => exact decodeBitMove_query din dout dα i x
  | ret a => exact decodeBitMove_ret din dout dα a

/-- Distinct moves have distinct canonical words. -/
theorem encodeBitMove_injective (din dout : Fin k → ℕ) (dα : ℕ) :
    Function.Injective (encodeBitMove din dout dα) := fun m m' h => by
  rw [← decodeBitMove_encodeBitMove din dout dα m, h, decodeBitMove_encodeBitMove]

/-! ### Transport along equal lengths -/

section Transport

open ProbComp

variable {σ : Type}

/-- **An implementation read along length functions:** answer the query `x` to oracle `i` of
`bitSpec ins outs` by asking `O` the query `padFin (ins' i) ⟦x⟧` and reading its answer `y` as
`padFin (outs i) ⟦y⟧`. When `ins = ins'` and `outs = outs'` this is `O` itself
(`castImpl_self`). -/
def castImpl {ins ins' outs outs' : Fin k → ℕ} (O : QueryImpl (bitSpec ins' outs') σ unifSpec) :
    QueryImpl (bitSpec ins outs) σ unifSpec :=
  fun i x s => (O i (padFin (ins' i) (List.ofFn x)) s).bind fun p =>
    .pure (padFin (outs i) (List.ofFn p.1), p.2)

/-- The defining equation of `castImpl`: `castImpl O i x s =
(O i (padFin (ins' i) ⟦x⟧) s).bind fun p => pure (padFin (outs i) ⟦p.1⟧, p.2)`. -/
theorem castImpl_eq {ins ins' outs outs' : Fin k → ℕ}
    (O : QueryImpl (bitSpec ins' outs') σ unifSpec) (i : Fin k) (x : Fin (ins i) → Bool)
    (s : σ) :
    castImpl (ins := ins) (outs := outs) O i x s =
      (O i (padFin (ins' i) (List.ofFn x)) s).bind fun p =>
        .pure (padFin (outs i) (List.ofFn p.1), p.2) :=
  rfl

/-- Read along the same lengths, an implementation is unchanged: `castImpl O = O`. -/
theorem castImpl_self {ins outs : Fin k → ℕ} (O : QueryImpl (bitSpec ins outs) σ unifSpec) :
    castImpl (ins := ins) (outs := outs) O = O := by
  funext i x s
  rw [castImpl_eq, padFin_ofFn]
  simp only [padFin_ofFn]
  exact OracleComp.bind_pure _

/-- **Transport of a machine's run:** if `ins = ins'`, `outs = outs'` and `d = d'`, simulating
`castImpl O` on the run of `M` through `bitCodec ins outs d` gives, with outputs read as lists,
the simulation of `O` on the run of `M` through `bitCodec ins' outs' d'`.

**Proof sketch.** Substitute the equalities; then `castImpl O = O` (`castImpl_self`). -/
theorem simulate_castImpl_toCompOn {ins ins' outs outs' : Fin k → ℕ} {d d' : ℕ}
    (hi : ins = ins') (ho : outs = outs') (hd : d = d')
    (O : QueryImpl (bitSpec ins' outs') σ unifSpec) (M : NUPPT) (n q : ℕ) (x : List Bool)
    (r : M.Coins n) (s : σ) :
    (simulate (castImpl (ins := ins) (outs := outs) O)
        (M.toCompOn (bitCodec ins outs d) n q x r) s).bind
        (fun p => .pure (List.ofFn p.1, p.2)) =
      (simulate O (M.toCompOn (bitCodec ins' outs' d') n q x r) s).bind
        (fun p => .pure (List.ofFn p.1, p.2)) := by
  subst hi ho hd
  rw [castImpl_self]

/-- **Transport of a machine's run, in expectation:** for every function `G` of the output (read
as a list) and the final state, `simulate_castImpl_toCompOn` in the form
`𝔼[G (⟦p.1⟧, p.2)]` over the two simulations. -/
theorem expect_simulate_castImpl_toCompOn {ins ins' outs outs' : Fin k → ℕ} {d d' : ℕ}
    (hi : ins = ins') (ho : outs = outs') (hd : d = d')
    (O : QueryImpl (bitSpec ins' outs') σ unifSpec) (M : NUPPT) (n q : ℕ) (x : List Bool)
    (r : M.Coins n) (s : σ) (G : List Bool × σ → ℝ) :
    expect (simulate (castImpl (ins := ins) (outs := outs) O)
        (M.toCompOn (bitCodec ins outs d) n q x r) s) (fun p => G (List.ofFn p.1, p.2)) =
      expect (simulate O (M.toCompOn (bitCodec ins' outs' d') n q x r) s)
        (fun p => G (List.ofFn p.1, p.2)) := by
  have h := congrArg (fun c => expect c G) (simulate_castImpl_toCompOn hi ho hd O M n q x r s)
  simp only [expect_bind, expect_pure] at h
  exact h

end Transport

end TCSlib.Cryptography.Games
