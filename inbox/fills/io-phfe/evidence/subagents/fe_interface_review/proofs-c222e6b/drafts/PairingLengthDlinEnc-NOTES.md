# BilinearGen.length_dlinEnc candidate

Status: scratch inspection-only candidate; root native verification pending. No Lean, lake,
build, Git, live edit or extra agent was run. Frozen header/prose copied byte-for-byte;
one tactic block, no holes/sorry, no helper/import/statement change, all lines ≤100 columns.
The dependency length_dlinStr is still pending native verification/integration, so this
candidate does not yet establish a standard-only encoding-length chain.

Read dlinEnc_eq and apply length_dlinStr. The group's type already fixes its encoding width
as G.wG.eval κ: BilinearGen.group has result BilinearGroup (wG.eval κ) (wT.eval κ), so no
new width transport or group encoding computation is introduced. The description subtype
contains an existential reachability proof r,hr. Eliminate that proposition in this proof,
rewrite description.val backwards along hr, then use the published G.length_desc.
This does not choose/recover generator coins inside any algorithm or encode them into the
challenge; the witness is used only to discharge an equality of lengths.

Every explicit rewrite item is a published reader. No foreign or core/Mathlib definition is
passed to simp/rw/unfold. No group logarithm, inverse encoding, or scalar representation is
used. The statement remains uniform over all reachable public descriptions and generators.

## Actual searches/read references

* Read current live Pairing/Linear.lean:165-189 for exact frozen header and dlinEnc_eq.
* `rg -n 'theorem length_desc|length_desc|descLen'` over the Pairing sources located
  BilinearGen.length_desc in Group.lean:310. An initial search named nonexistent
  Pairing/Gen.lean; the actual declaration is in Group.lean and was read there.
* `rg -n 'description.property|length_desc.*hr|length_desc.*r|desc.*length.*property'`
  over Pairing/FE located the already-published proof-only reachability elimination route
  in MatrixDH/Parameters.lean:137 (order_eq_of_publicParams).
* Read MatrixDH/Parameters.lean:35-52 for the GroupDescription subtype contract.
* Read Group.lean:299-316 for desc_eq and length_desc; searched group/wG fields and verified
  Group.lean:293,297 give the fixed widths of group κ d independently of the description.
* Read the pending PairingLengthDlinStr.lean.inc to verify exact formula and dependency.

No new helper/probe is needed: published length_dlinStr and length_desc exactly supply the
required equations. Native focus is ordinary existential/property elimination and rewriting
its reachability equality after the tuple-length reader has removed the dependent group.
