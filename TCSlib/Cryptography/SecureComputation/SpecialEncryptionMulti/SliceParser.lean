/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TCSlib.Cryptography.Asymptotic.BlockEncryptor
import TCSlib.Cryptography.Encryption.PrivateKey.FromPRF.MultiMsgOut
import TCSlib.Cryptography.Games.Efficiency

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# The efficient slice post-processor

## Main definitions

* `SliceReduction.slicePost`: read slice descriptors and ciphertexts in parallel.

## Main results

* `SliceReduction.polyTimeComputable_slicePost`: the parser is polynomial-time on all words.
* `SliceReduction.slicePost_encode`: its exact law on encoded descriptor/ciphertext pairs.

## References

* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, Theorem 99.2 with slices.
-/

namespace TCSlib.Cryptography.SecureComputation.SliceReduction

open Complexity Turing TCSlib.Cryptography

/-- Drop one descriptor and one ciphertext from the paired parser state:
`parserStep z = ⟨snd (fst z), snd (snd z)⟩`. -/
def parserStep (z : List Bool) : List Bool :=
  pairEncode (pairSndD (pairFstD z)) (pairSndD (pairSndD z))

/-- `parserStep z = ⟨snd (fst z), snd (snd z)⟩`. -/
theorem parserStep_eq (z : List Bool) :
    parserStep z = pairEncode (pairSndD (pairFstD z)) (pairSndD (pairSndD z)) := rfl

/-- Emit one slice ciphertext chunk. A descriptor `⟨u,v⟩` selects offset `|u|` and width
`|v|`; on a state `⟨advice,ciphertexts⟩`, read both first entries, keep the nonce, cut the
body, and emit `⟨⟨nonce,body.drop |u| |>.take |v|⟩,[]⟩`. Emit nothing if ciphertexts are empty. -/
def parserEmit (z : List Bool) : List Bool :=
  if pairSndD z = [] then [] else
    pairEncode (pairEncode (pairFstD (pairFstD (pairSndD z)))
      (((pairSndD (pairFstD (pairSndD z))).drop
        (pairFstD (pairFstD (pairFstD z))).length).take
          (pairSndD (pairFstD (pairFstD z))).length)) []

/-- `parserEmit z` is empty if `snd z=[]`; otherwise it is the encoded chunk
`⟨⟨fst (fst (snd z)),(snd (fst (snd z))).drop |fst (fst (fst z))|
  |>.take |snd (fst (fst z))|⟩,[]⟩`. -/
theorem parserEmit_eq (z : List Bool) :
    parserEmit z = if pairSndD z = [] then [] else
      pairEncode (pairEncode (pairFstD (pairFstD (pairSndD z)))
        (((pairSndD (pairFstD (pairSndD z))).drop
          (pairFstD (pairFstD (pairFstD z))).length).take
            (pairSndD (pairFstD (pairFstD z))).length)) [] := rfl

/-- The total slice parser runs `|z|+1` emissions:
`slicePost z = Games.iterEmit parserStep parserEmit (z.length+1) z`. -/
def slicePost (z : List Bool) : List Bool :=
  Games.iterEmit parserStep parserEmit (z.length + 1) z

/-- `slicePost z = Games.iterEmit parserStep parserEmit (z.length+1) z`. -/
theorem slicePost_eq (z : List Bool) :
    slicePost z = Games.iterEmit parserStep parserEmit (z.length + 1) z := rfl

/-- Dropping both list heads never lengthens the state beyond the empty pair:
`(parserStep z).length ≤ max z.length 2`.

**Proof sketch.** Reuse the published pair-state bound after shortening the second
component. Shortening the first component can only reduce its contribution to the public
pairing length formula. -/
theorem length_parserStep_le (z : List Bool) : (parserStep z).length ≤ max z.length 2 := by
  rw [parserStep_eq]
  have hf := length_pairSndD_le (pairFstD z)
  have hs := OneWay.PosLoop.length_pairEncode_pairFstD_le z
    (pairSndD (pairSndD z)) (length_pairSndD_le (pairSndD z))
  refine le_trans ?_ hs
  rw [length_pairEncode, length_pairEncode]
  omega

/-- The slice parser is polynomial-time on every input word:
`PolyTimeComputable slicePost`.

**Proof sketch.** Total pair projections read the current descriptor and ciphertext.
The descriptor's two unary lengths drive the published polynomial-time drop and take
operations. Pair the retained nonce and cut body and emit a self-delimited list chunk.
The step drops both list heads and stays within `max |z| 2`, so the published iterate-and-emit
host gives a polynomial-time parser, including malformed inputs. -/
theorem polyTimeComputable_slicePost : PolyTimeComputable slicePost := by
  have hf := polyTimeComputable_pairFstD
  have hs := polyTimeComputable_pairSndD
  have hadv := hf.comp' hf
  have hct := hf.comp' hs
  have ho := hf.comp' hadv
  have hw := hs.comp' hadv
  have hbody := hs.comp' hct
  have hdrop := (polyTimeComputable_pairDropPoly .var).comp' (ho.pairEncode hbody)
  have htake := (polyTimeComputable_pairTakePoly .var).comp' (hw.pairEncode hdrop)
  have hemit : PolyTimeComputable parserEmit := by
    have hnil := polyTimeComputable_isNil.comp' hs
    have hout := ((hf.comp' hct).pairEncode htake).pairEncode (polyTimeComputable_const [])
    convert polyTimeComputable_ite hnil (polyTimeComputable_const []) hout using 1
    funext z
    rw [parserEmit_eq]
    simp only [pairFstD_pairEncode, pairSndD_pairEncode, PolyExpr.eval_var]
    by_cases h : pairSndD z = []
    · rw [if_pos h, decide_eq_true h]; rfl
    · rw [if_neg h, decide_eq_false h]; rfl
  exact Games.polyTimeComputable_iterEmit
    ((hs.comp' hf).pairEncode (hs.comp' hs)) hemit 2 length_parserStep_le

/-- On paired encoded lists of descriptors and ciphertexts, the parser cuts every body
and keeps every nonce:
`slicePost ⟨encodeList (l.map fst),encodeList (l.map snd)⟩ = encodeList
  (l.map fun (d,c) => ⟨fst c,(snd c).drop |fst d| |>.take |snd d|⟩)`.
[PS10, Theorem 99.2, with slices]

**Proof sketch.** Regard the state as one encoding of a list of descriptor/ciphertext
pairs. The step removes the two heads, the empty state is fixed, and emission reads the
specified chunk of each ciphertext. The list encoding contains at least one bit per entry,
so `|state|+1` iterations suffice. Apply the existing iterate-and-emit encoding theorem and
the existing flat-map law for the ciphertext list encoding. -/
theorem slicePost_encode (l : List (List Bool × List Bool)) :
    slicePost (pairEncode (PrivateKeyScheme.encodeList (l.map Prod.fst))
      (PrivateKeyScheme.encodeList (l.map Prod.snd))) =
        PrivateKeyScheme.encodeList (l.map fun e => pairEncode (pairFstD e.2)
          (((pairSndD e.2).drop (pairFstD e.1).length).take (pairSndD e.1).length)) := by
  let enc : List (List Bool × List Bool) → List Bool := fun t =>
    pairEncode (PrivateKeyScheme.encodeList (t.map Prod.fst))
      (PrivateKeyScheme.encodeList (t.map Prod.snd))
  let g : (List Bool × List Bool) → List Bool := fun e =>
    pairEncode (pairEncode (pairFstD e.2)
      (((pairSndD e.2).drop (pairFstD e.1).length).take (pairSndD e.1).length)) []
  have hnil : enc [] = pairEncode [] [] := by
    simp only [enc, List.map_nil, PrivateKeyScheme.encodeList_nil]
  have hcons (e : List Bool × List Bool) (t : List (List Bool × List Bool)) :
      enc (e :: t) = pairEncode
        (pairEncode e.1 (PrivateKeyScheme.encodeList (t.map Prod.fst)))
        (pairEncode e.2 (PrivateKeyScheme.encodeList (t.map Prod.snd))) := by
    simp only [enc, List.map_cons, PrivateKeyScheme.encodeList_cons]
  have hstep_nil : parserStep (enc []) = enc [] := by
    rw [hnil, parserStep_eq, pairFstD_pairEncode, pairSndD_pairEncode]
    simp only [pairSndD_eq, pairDecode_nil, Option.map_none, Option.getD_none]
  have hstep : ∀ e ∈ l, ∀ t, parserStep (enc (e :: t)) = enc t := by
    intro e he t
    rw [hcons, parserStep_eq]
    simp only [pairFstD_pairEncode, pairSndD_pairEncode, enc]
  have hemit_nil : parserEmit (enc []) = [] := by
    rw [hnil, parserEmit_eq, pairSndD_pairEncode, if_pos rfl]
  have hemit : ∀ e ∈ l, ∀ t, parserEmit (enc (e :: t)) = g e := by
    intro e he t
    rw [hcons, parserEmit_eq, pairSndD_pairEncode, if_neg (pairEncode_ne_nil _ _)]
    simp only [pairFstD_pairEncode, pairSndD_pairEncode, g]
  have hfuel : l.length ≤ (enc l).length + 1 := by
    have h := TCSlib.Cryptography.length_le_length_encodeList (l.map Prod.snd)
    rw [List.length_map] at h
    dsimp only [enc]
    rw [length_pairEncode]
    omega
  rw [slicePost_eq]
  change Games.iterEmit parserStep parserEmit ((enc l).length + 1) (enc l) = _
  rw [Games.iterEmit_encode parserStep parserEmit enc g l hstep_nil hstep
    hemit_nil hemit _ hfuel, MultiMsg.encodeList_eq_flatMap, List.flatMap_map]

end TCSlib.Cryptography.SecureComputation.SliceReduction
