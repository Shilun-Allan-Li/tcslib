/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TCSlib.Cryptography.SecureComputation.GarblingSpecial
import TCSlib.Complexity.ClassP.BinaryArith.Words
import Lean

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let mut requested := 0
  let mut excluded := 0
  for (name, ci) in env.constants.toList do
    if let some idx := env.getModuleIdxFor? name then
      let home := env.header.moduleNames[idx.toNat]!
      if home.toString.startsWith "TCSlib." then
        if let .defnInfo d := ci then
          let status ← liftCoreM <| Lean.getReducibilityStatus name
          let matcher := Lean.Meta.isMatcherCore env name
          let rec body : Nat → Expr → Expr
            | 0, e => e
            | fuel+1, .lam _ _ b _ => body fuel b
            | fuel+1, .letE _ _ v b _ => body fuel (b.instantiate1 v)
            | _, e => e
          let ty := d.type.getForallBody.getAppFn.constName?
          let val := body 64 d.value
          let coe := ty == some `CoeFun || ty == some `Coe
          let map := if val.getAppArgs.isEmpty then val else val.getAppArgs.back!
          let projection := match (body 64 map).getAppFn with
            | .proj .. => true
            | .const n _ => env.isProjectionFn n
            | _ => false
          let isNotation : Bool := (name == `Complexity.PolyExpr.eval && false) ||
            (true && coe && projection)
          if isNotation || (status == .reducible && !matcher) then
            excluded := excluded + 1
            logInfo m!"EXCLUDED\t{home}\t{name}"
          else
            let id := mkIdent name
            if status != .irreducible then
              elabCommand (← `(command| attribute [local irreducible] $id:ident))
            let installed ← liftCoreM <| Lean.getReducibilityStatus name
            unless installed == .irreducible do
              throwError "seal not installed: {name}"
            requested := requested + 1
            logInfo m!"SEALED\t{home}\t{name}"
  logInfo m!"SEAL_COUNTS requested={requested} excluded={excluded}"

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Tagged special decryption at arbitrary message lengths

The published decryption adapter specializes the message length to the key length.
A nested garbled row also needs the outer message length `4n + 2`. This module
provides one adapter whose key and message lengths are separate unary input words.
Failure is `[]` and a successful message `m` is `true :: m`, including the empty message.

## Main definitions

* `YaoHybridProof.specialDecTagged`: tagged decryption on `⟨N, ⟨L, ⟨k, c⟩⟩⟩`.

## Main results

* `YaoHybridProof.specialDecTagged_poly`: polynomial time on every input word.

## References

* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed.,
  January 2010, Algorithm 157.2 and Protocol 162.6.
-/

namespace TCSlib.Cryptography.SecureComputation.YaoHybridProof

open Complexity Turing

/-- Tagged special decryption on `⟨N, ⟨L, ⟨k, c⟩⟩⟩`: run `spDecStr E |N| |L| k c`,
returning `[]` on failure and `true :: m` on success with message `m`.
The unary lengths are separate, so the adapter covers either encryption layer.
[PS10, Algorithm 157.2] -/
def specialDecTagged (E : List Bool → List Bool) (z : List Bool) : List Bool :=
  match spDecStr E (pairFstD z).length (pairFstD (pairSndD z)).length
      (pairFstD (pairSndD (pairSndD z))) (pairSndD (pairSndD (pairSndD z))) with
  | none => []
  | some m => true :: m

/-- For every `z`, `specialDecTagged E z` encodes the result of decryption with
key length `|fst z|`, message length `|fst (snd z)|`, key `fst (snd (snd z))`
and ciphertext `snd (snd (snd z))` by `none ↦ []`, `some m ↦ true :: m`. -/
theorem specialDecTagged_eq (E : List Bool → List Bool) (z : List Bool) :
    specialDecTagged E z =
      match spDecStr E (pairFstD z).length (pairFstD (pairSndD z)).length
          (pairFstD (pairSndD (pairSndD z))) (pairSndD (pairSndD (pairSndD z))) with
      | none => []
      | some m => true :: m := rfl

/-- For a polynomial-time evaluator `E`, `specialDecTagged E` is polynomial-time
on every word, with independent unary key and message lengths.
[PS10, Algorithm 157.2]

**Proof sketch.** Read the two unary lengths, key, nonce and ciphertext body.
Test the three shape equalities. Compute the pad and compare its key-length
prefix with the ciphertext prefix. If both tests pass, append a success marker
to the XOR of the suffixes; otherwise return the empty failure word. Each
operation uses the published pairing, length, cut and XOR closure contracts. -/
theorem specialDecTagged_poly {E : List Bool → List Bool} (hE : PolyTimeComputable E) :
    PolyTimeComputable (specialDecTagged E) := by
  have hN := polyTimeComputable_pairFstD
  have hL := polyTimeComputable_pairFstD.comp polyTimeComputable_pairSndD
  have hkc := polyTimeComputable_pairSndD.comp polyTimeComputable_pairSndD
  have hk := polyTimeComputable_pairFstD.comp hkc
  have hct := polyTimeComputable_pairSndD.comp hkc
  have hr := polyTimeComputable_pairFstD.comp hct
  have hc := polyTimeComputable_pairSndD.comp hct
  have hp := hE.comp (hk.pairEncode hr)
  have h1 := polyTimeComputable_lenEq.comp (hk.pairEncode hN)
  have h2 := polyTimeComputable_lenEq.comp (hr.pairEncode hN)
  have h3 := polyTimeComputable_lenEq.comp (hc.pairEncode (hN.append hL))
  have hguard := polyTimeComputable_and h1 (polyTimeComputable_and h2 h3)
  have hctake := (polyTimeComputable_pairTakePoly .var).comp (hN.pairEncode hc)
  have hptake := (polyTimeComputable_pairTakePoly .var).comp (hN.pairEncode hp)
  have hcDrop := (polyTimeComputable_pairDropPoly .var).comp (hN.pairEncode hc)
  have hpDrop := (polyTimeComputable_pairDropPoly .var).comp (hN.pairEncode hp)
  have heq := polyTimeComputable_pairEq.comp (hctake.pairEncode hptake)
  have hxor := polyTimeComputable_pairXor.comp (hcDrop.pairEncode hpDrop)
  have hgood := (polyTimeComputable_prepend [true]).comp hxor
  have h := polyTimeComputable_ite hguard
    (polyTimeComputable_ite heq hgood (polyTimeComputable_const []))
    (polyTimeComputable_const [])
  convert h using 1
  funext z
  simp only [specialDecTagged_eq, spDecStr_eq, Function.comp_apply,
    pairFstD_pairEncode, pairSndD_pairEncode, PolyExpr.eval_var, List.length_append,
    ← Bool.decide_and, decide_eq_true_eq]
  split_ifs <;> rfl

/-- On the explicit layout, `specialDecTagged E ⟨N, ⟨L, ⟨k, c⟩⟩⟩` is
`[]` if `spDecStr E |N| |L| k c` fails and `true :: m` if it returns `m`. -/
theorem specialDecTagged_pairEncode (E : List Bool → List Bool) (N L k c : List Bool) :
    specialDecTagged E (pairEncode N (pairEncode L (pairEncode k c))) =
      match spDecStr E N.length L.length k c with
      | none => []
      | some m => true :: m := by
  rw [specialDecTagged_eq]
  simp only [pairFstD_pairEncode, pairSndD_pairEncode]

/-- Apply a word function `F` to the payload of a successful tagged word:
`bindTagged F [] = []`, and `bindTagged F (b :: m) = F m`. -/
def bindTagged (F : List Bool → List Bool) (w : List Bool) : List Bool :=
  if w = [] then [] else F (w.drop 1)

/-- For every `w`, `bindTagged F w = if w = [] then [] else F (w.drop 1)`. -/
theorem bindTagged_eq (F : List Bool → List Bool) (w : List Bool) :
    bindTagged F w = if w = [] then [] else F (w.drop 1) := rfl

/-- On a tagged optional payload, `bindTagged` applies `F` exactly in the success case. -/
theorem bindTagged_option (F : List Bool → List Bool) (o : Option (List Bool)) :
    bindTagged F (match o with | none => [] | some m => true :: m) =
      match o with | none => [] | some m => F m := by
  cases o with
  | none => rw [bindTagged_eq, if_pos rfl]
  | some m =>
    rw [bindTagged_eq, if_neg (List.cons_ne_nil true m)]
    rfl

/-- If `F` is polynomial-time, then `bindTagged F` is polynomial-time on all words. -/
theorem bindTagged_poly {F : List Bool → List Bool} (hF : PolyTimeComputable F) :
    PolyTimeComputable (bindTagged F) := by
  simpa only [bindTagged_eq, Function.comp_apply, decide_eq_true_eq] using
    polyTimeComputable_ite polyTimeComputable_isNil (polyTimeComputable_const [])
      (hF.comp polyTimeComputable_tail)

/-- Check a tagged word at `⟨N, w⟩`: reject the empty failure word and
wrong-length payloads, and return `true :: payload` when its length is `|N|`. -/
def checkFinTagged (z : List Bool) : List Bool :=
  if pairSndD z = [] then []
  else if ((pairSndD z).drop 1).length = (pairFstD z).length then
    true :: (pairSndD z).drop 1 else []

/-- For every `z`, `checkFinTagged z` succeeds exactly when `snd z` is nonempty
and its payload `drop 1 (snd z)` has length `|fst z|`. -/
theorem checkFinTagged_eq (z : List Bool) :
    checkFinTagged z = if pairSndD z = [] then []
      else if ((pairSndD z).drop 1).length = (pairFstD z).length then
        true :: (pairSndD z).drop 1 else [] := rfl

/-- Checking the tagged encoding of `o : Option (List Bool)` produces the tagged
encoding of `o.bind (decodeFin |N|)`, with a decoded key represented by `List.ofFn`.

**Proof sketch.** Failure stays failure. For a successful string, split on its
`decodeFin` result. A failed decode has the wrong length by the decoder reader;
a successful decode identifies the string with `List.ofFn` of its key by the
published exact-decoding characterization. -/
theorem checkFinTagged_option (N : List Bool) (o : Option (List Bool)) :
    checkFinTagged (pairEncode N (match o with | none => [] | some m => true :: m)) =
      match o.bind (TCSlib.Cryptography.decodeFin N.length) with
      | none => []
      | some k => true :: List.ofFn k := by
  cases o with
  | none =>
    rw [checkFinTagged_eq, pairSndD_pairEncode, if_pos rfl]
    rfl
  | some m =>
    rw [checkFinTagged_eq, pairFstD_pairEncode, pairSndD_pairEncode,
      if_neg (List.cons_ne_nil true m), List.drop_succ_cons, List.drop_zero, Option.bind_some]
    cases hd : TCSlib.Cryptography.decodeFin N.length m with
    | none =>
      have hne : m.length ≠ N.length := by
        intro hm
        rw [TCSlib.Cryptography.decodeFin_eq, dif_pos hm] at hd
        contradiction
      rw [if_neg hne]
    | some k =>
      have hm := (TCSlib.Cryptography.decodeFin_eq_some_iff N.length m k).mp hd
      rw [hm, List.length_ofFn, if_pos rfl]

/-- The exact-length tagged key check `checkFinTagged` is polynomial-time on all words. -/
theorem checkFinTagged_poly : PolyTimeComputable checkFinTagged := by
  have hp := polyTimeComputable_tail.comp polyTimeComputable_pairSndD
  have ht := polyTimeComputable_lenEq.comp (hp.pairEncode polyTimeComputable_pairFstD)
  have hg := (polyTimeComputable_prepend [true]).comp hp
  have h := polyTimeComputable_ite
    (polyTimeComputable_isNil.comp polyTimeComputable_pairSndD)
    (polyTimeComputable_const [])
    (polyTimeComputable_ite ht hg (polyTimeComputable_const []))
  convert h using 1
  funext z
  simp only [checkFinTagged_eq, Function.comp_apply, pairFstD_pairEncode,
    pairSndD_pairEncode, decide_eq_true_eq]
  split_ifs <;> rfl

/-- Nested special decryption on `⟨N, ⟨keys, c⟩⟩`, with `keys` an encoded word list.
Zero keys check the cleartext; one key uses `E₁`; two keys remove the `E₂` outer
layer at message length `4|N| + 2`, then the `E₁` inner layer. Other key counts
fail. Successful keys are tagged as `true :: key`; failure is `[]`.
[PS10, Protocol 162.6] -/
def nestedDecTagged (E₁ E₂ : List Bool → List Bool) (z : List Bool) : List Bool :=
  let N := pairFstD z
  let keys := pairFstD (pairSndD z)
  let c := pairSndD (pairSndD z)
  if keys = [] then checkFinTagged (pairEncode N (true :: c))
  else if pairSndD keys = [] then
    checkFinTagged (pairEncode N
      (specialDecTagged E₁ (pairEncode N (pairEncode N (pairEncode (pairFstD keys) c)))))
  else if pairSndD (pairSndD keys) = [] then
    let outer := specialDecTagged E₂ (pairEncode N
      (pairEncode (List.replicate (innerLen.eval N.length) true)
        (pairEncode (pairFstD keys) c)))
    if outer = [] then [] else
      checkFinTagged (pairEncode N
        (specialDecTagged E₁ (pairEncode N
          (pairEncode N (pairEncode (pairFstD (pairSndD keys)) (outer.drop 1))))))
  else []

/-- For every input `z`, `nestedDecTagged E₁ E₂ z` branches on zero, one or two
encoded keys and performs the corresponding tagged special decryptions and
exact key-length check. -/
theorem nestedDecTagged_eq (E₁ E₂ : List Bool → List Bool) (z : List Bool) :
    nestedDecTagged E₁ E₂ z =
  let N := pairFstD z
  let keys := pairFstD (pairSndD z)
  let c := pairSndD (pairSndD z)
  if keys = [] then checkFinTagged (pairEncode N (true :: c))
  else if pairSndD keys = [] then
    checkFinTagged (pairEncode N
      (specialDecTagged E₁ (pairEncode N (pairEncode N (pairEncode (pairFstD keys) c)))))
  else if pairSndD (pairSndD keys) = [] then
    let outer := specialDecTagged E₂ (pairEncode N
      (pairEncode (List.replicate (innerLen.eval N.length) true)
        (pairEncode (pairFstD keys) c)))
    if outer = [] then [] else
      checkFinTagged (pairEncode N
        (specialDecTagged E₁ (pairEncode N
          (pairEncode N (pairEncode (pairFstD (pairSndD keys)) (outer.drop 1))))))
  else [] := rfl

/-- On the encoded key list `ks`, `nestedDecTagged E₁ E₂ ⟨N, ⟨keys, c⟩⟩`
is `[]` when `(nestedSpecial E₁ E₂ |N|).dec ks c` fails and is
`true :: List.ofFn k` when it returns key `k`. [PS10, Protocol 162.6]

**Proof sketch.** Split into zero, one, two and more keys. The list-code readers
select the corresponding branch. The exact-length checker implements `decodeFin`.
In the two-key case split on the outer decryption result; failure is preserved,
while success exposes exactly the ciphertext on which the inner layer is called. -/
theorem nestedDecTagged_encoded (E₁ E₂ : List Bool → List Bool) (N : List Bool)
    (ks : List (Fin N.length → Bool)) (c : List Bool) :
    nestedDecTagged E₁ E₂
        (pairEncode N (pairEncode (BinArith.encWords (ks.map List.ofFn)) c)) =
      match (nestedSpecial E₁ E₂ N.length).dec ks c with
      | none => []
      | some k => true :: List.ofFn k := by
  cases ks with
  | nil =>
    rw [nestedDecTagged_eq, nestedSpecial_dec]
    simp only [List.map_nil, BinArith.encWords_nil, pairFstD_pairEncode,
      pairSndD_pairEncode, if_true]
    exact checkFinTagged_option N (some c)
  | cons k₁ ks =>
    cases ks with
    | nil =>
      rw [nestedDecTagged_eq, nestedSpecial_dec]
      simp only [List.map_nil, List.map_cons, BinArith.encWords_nil,
        BinArith.encWords_cons, pairFstD_pairEncode, pairSndD_pairEncode,
        pairEncode_ne_nil, if_false, if_true]
      rw [specialDecTagged_pairEncode]
      exact checkFinTagged_option N (spDecStr E₁ N.length N.length (List.ofFn k₁) c)
    | cons k₂ ks =>
      cases ks with
      | nil =>
        rw [nestedDecTagged_eq, nestedSpecial_dec]
        simp only [List.map_nil, List.map_cons, BinArith.encWords_nil,
          BinArith.encWords_cons, pairFstD_pairEncode, pairSndD_pairEncode,
          pairEncode_ne_nil, if_false, if_true, specialDecTagged_pairEncode,
          List.length_replicate]
        cases ho : spDecStr E₂ N.length (innerLen.eval N.length) (List.ofFn k₁) c with
        | none => simp only [if_true, Option.bind_none]
        | some m =>
          simp only [List.cons_ne_nil, if_false, List.drop_succ_cons, List.drop_zero,
            Option.bind_some]
          exact checkFinTagged_option N (spDecStr E₁ N.length N.length (List.ofFn k₂) m)
      | cons k₃ ks =>
        rw [nestedDecTagged_eq, nestedSpecial_dec]
        simp only [List.map_cons, BinArith.encWords_cons, pairFstD_pairEncode,
          pairSndD_pairEncode, pairEncode_ne_nil, if_false]

/-- If `E₁` and `E₂` are polynomial-time, then `nestedDecTagged E₁ E₂`
is polynomial-time on every input, including malformed key lists and ciphertexts.
[PS10, Protocol 162.6]

**Proof sketch.** Pair projections read the parameter, keys and ciphertext.
Emptiness tests distinguish the four key-count cases. The no-key branch uses the
exact-length decoder; the one-key branch calls the inner decryption adapter.
The two-key branch computes the unary outer-message length `4n + 2`, calls the
outer adapter, preserves its failure marker and otherwise calls the inner one.
All branches use the already proved total tagged adapters and FP closure. -/
theorem nestedDecTagged_poly {E₁ E₂ : List Bool → List Bool}
    (hE₁ : PolyTimeComputable E₁) (hE₂ : PolyTimeComputable E₂) :
    PolyTimeComputable (nestedDecTagged E₁ E₂) := by
  have hN := polyTimeComputable_pairFstD
  have hkeys := polyTimeComputable_pairFstD.comp polyTimeComputable_pairSndD
  have hc := polyTimeComputable_pairSndD.comp polyTimeComputable_pairSndD
  have hk₁ := polyTimeComputable_pairFstD.comp hkeys
  have hrest := polyTimeComputable_pairSndD.comp hkeys
  have hk₂ := polyTimeComputable_pairFstD.comp hrest
  have hrest₂ := polyTimeComputable_pairSndD.comp hrest
  have hL := (polyTimeComputable_unaryPoly innerLen).comp hN
  have houter := (specialDecTagged_poly hE₂).comp
    (hN.pairEncode (hL.pairEncode (hk₁.pairEncode hc)))
  have hinner₁ := (specialDecTagged_poly hE₁).comp
    (hN.pairEncode (hN.pairEncode (hk₁.pairEncode hc)))
  have hinner₂ := (specialDecTagged_poly hE₁).comp
    (hN.pairEncode (hN.pairEncode
      (hk₂.pairEncode (polyTimeComputable_tail.comp houter))))
  have hzero := checkFinTagged_poly.comp
    (hN.pairEncode ((polyTimeComputable_prepend [true]).comp hc))
  have hone := checkFinTagged_poly.comp (hN.pairEncode hinner₁)
  have htwo := polyTimeComputable_ite (polyTimeComputable_isNil.comp houter)
    (polyTimeComputable_const []) (checkFinTagged_poly.comp (hN.pairEncode hinner₂))
  have h := polyTimeComputable_ite (polyTimeComputable_isNil.comp hkeys) hzero
    (polyTimeComputable_ite (polyTimeComputable_isNil.comp hrest) hone
      (polyTimeComputable_ite (polyTimeComputable_isNil.comp hrest₂) htwo
        (polyTimeComputable_const [])))
  convert h using 1
  funext z
  simp only [nestedDecTagged_eq, Function.comp_apply, decide_eq_true_eq]
  split_ifs <;> rfl

end TCSlib.Cryptography.SecureComputation.YaoHybridProof
