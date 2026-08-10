<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/Switching/Circuit.lean :: foldr_add_map -->
<!-- origin: no source citation; informalized directly from the Lean proof -->

# Summing fold commutes with a pointwise-agreeing map

**Claim.** Let `h : α → β`, `f : α → Nat`, `g : β → Nat`, and `cs : List α`.
If `g (h c) = f c` for every `c ∈ cs`, then the two summing folds agree:

`(cs.map h).foldr (fun c acc => g c + acc) 0 = cs.foldr (fun c acc => f c + acc) 0`.

The `Nat`-valued analogue of `foldr_and_map` / `foldr_or_map`, with `+`/`0` in
place of `&&`/`true`.

**Proof.** `induction cs <;> aesop`. Nil gives `0 = 0`; cons rewrites the head
summand by `heq` at `c` and applies the inductive hypothesis to the tail.

**Remark.** Intended for the literal-count preservation proofs, where
`litCount` on a node is exactly this fold over the children and the child-wise
hypothesis is `∀ c ∈ cs, (h c).litCount = c.litCount`.

**Used in.** Nothing — dead code. `toNAnd_toNOr_litCount` instead states the
same statement as a local `have h_foldr` and proves it by
`intros cs hcs; induction cs <;> aesop` (twice); `private` prevents any external
use.
