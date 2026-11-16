# Subagent c: generic seed-by-seed garbling relabeling

Source RelabelGarbling.lean, namespace YaoHybridProof.RelabelGarbling.
202 lines,16 source declarations, no source sorry, no frozen-file edits.

## Contract and checkpoint4 mapping

`argValues C v i` restricts any wire-value map to gate i's argument positions.
`relabelSeed C v s` relabels keys by b XOR v(w), addresses row coins by
xorPerm(argValues) a, and composes the old row permutation with that XOR.
It has full tuple and all three field readers.

`keyAt_relabel` handles every Nat vertex, including defaults outside C.size;
`keyAt_original` is its inverse form. `argKeys_relabel` identifies the whole
argument-key list. `row_relabel` states that encryption under the new seed,
with output bit gateOut(a XOR argValues) XOR v(output), is the old row at
a XOR argValues. `garbledTable_relabel` gives exact equality of the original
table and that transformed expression under the relabeled permutation, using
the identical fixed enumeration. No row-order probability fact is required.

`inputKeys_relabel` gives the full input-key list identity.
`selectedKeys_original` handles arbitrary selected wire lists, subsets and
repetitions, for Alice's keys and OT answer-key components. `output_pair_relabel`
expresses the original key pair as the relabeled pair swapped when v(output).
All statements are generic in MultiEnc K W rho, with no fan-in, correctness,
key-distinctness, PRF or polynomial-time assumptions.

The next tape-to-seed bridge must identify this seed action with CoinRelabel.
No full H0=H1 sampler or Bob view claim is made here. Encoded message/view
identities can apply the row/table and key/pair equations through their encoders.

## Overlap and reuse

- Garbling.lean keyAt_eq(:240), argKeys_eq(:250), garbledRow_eq(:262),
  garbledTable_eq(:275), inputKeys_eq(:315) are reused as published readers.
  No row/table definition is duplicated. The RHS of the table theorem is an
  explicit transformed encryption expression, not a second garbledTable def.
- BitLists.lean:105,110 xorPerm/xorPerm_apply are reused directly. The inline
  double-XOR cancellation in garbledTable_relabel is derived from xorPerm_apply
  and existing Bool.xor_assoc/xor_self/xor_false. The nearest private proof is
  the involution argument inside xorPerm's definition; no public self-inverse
  reader exists at the base. The consumer uses only the public apply reader.
- List.map_congr_left, congrArg List.ofFn and function extensionality compose
  pointwise equalities; no list-window/probability lemma is re-proved.
- The fill's RowFromCoins.rowWordWith(:199) and TablesFromCoins.tableWordWith(:39)
  were examined first. The former is a nested-special-encryption word machine
  with addressed coin words, the latter an encoded and arity-guarded table
  assembler. Neither states this arbitrary MultiEnc/K/rho mathematical identity.
  The direct transformed RHS avoids adding a parallel row/table API and can
  later identify their supplied output-bit map with this formula.
- Unmerged sc-garble Garbling/Probability.lean contains uniform marginals of
  keys/row coins and general successful-decryption facts, not a wire-value
  relabeling identity. No declaration or probability proof was copied from it.

## Verification

RelabelGarbling-05 passes. Axioms-01 prints all source signatures and dynamically
scans every stored module constant (including generated argValues auxiliaries):
standard axioms only, all transitive closures sorried=[]. All four whole-file
Rule10 diagnostic variants pass at CLI -DmaxErrors=0, so no foreign-unfolding
repair was needed. The dsimp only in the table proof reduces its local let
and beta applications and names no TCSlib definition. All raw source versions,
logs, manifests, inventory and runners are retained. The lead reruns final
merged checks. No commits were made by this agent.
