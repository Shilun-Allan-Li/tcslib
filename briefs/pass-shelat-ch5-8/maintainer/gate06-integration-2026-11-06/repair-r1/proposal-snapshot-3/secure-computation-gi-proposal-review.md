# SecureComputation and GI proposal review

**Static result: no new mathematical/security concern; one known open interface blocker.**
The blocker is the root-reported valid R2 `Garbling.garbledValues_getD` diagnostic, which
is also visible statically: `refine runWith_sim` requires the imported `DAGCircuit.values`
body. Its owner has no `values_eq` in the reviewed snapshot. The size/eval readers do not
supply this equation. Root has authorized the next follow-up: add the exact owner term
reader and rewrite `garbledValues_eq` / `DAGCircuit.values_eq` before applying simulation.
This report does not mark that blocker resolved before native replay.

Reviewed 29 remaining proposal artifacts plus four typed-OT prerequisites already covered
by the earlier transport review. All 33 patches compose in memory against exact frozen
`e9d64158461bfe24ddc88ab885bc4017899b4c16` across 15 files; the mutable checkout was not used as their base.
Patch-set fingerprint: `bee096e5682852978097775f8a3351382e4c84c4a9dab70bf2a77b4c82307116`.

| Area | Static assessment |
|---|---|
| Compose / ComposePhases | The zero cases use public execution equations. Coin-length chains preserve exact sums/products. Transcript, view and output terms connect the same received-message pairs through the appropriate public readers. `Eq.trans`/`Eq.mpr` directions are correct. The output premise `hM` remains; no zero-round guarantee is introduced. |
| ComposeSecurity | `exists_mainExec` and `exists_runExec` preserve the exact take/runTape words; the new coin-length equality directions match `exists_ofFn_eq`. Predicate readers expose the same efficiency/bound clauses. The composed bound remains `B_main+B_run`; `polyTime_compose` transports strategy efficiency through the matching P/V field equations. No security premise or simulator contract changes. |
| Garbling / GarblingSpecial | Size/output-bound transports and the circuit eval equation have the correct directions. The nested-encryption repair opens exactly `MultiEnc.DecCorrect`; all existing key-count cases and pad-length assumptions remain. The imported `values` gap above is the sole known open blocker in these reviewed repairs. |
| SpecialEncryptionSecurity | The two public coin-length proofs and typed evaluator-tape proof preserve `List.ofFn` words, including zero-length tapes, before applying the unchanged evaluator specification. No algorithm/security header or admission changes. Cascade outcomes require native replay. |
| GI/GNI owner readers and term chains | The new repeated-strategy equations expand definitions homed in GI/Proofs; no new host or copied algorithm is added. Full-Sigma `decGraph_eq_of_sqrt` transports the graph dimension and value together, so the single/repeated prover chains cover malformed words too. Coin-block positions, last-challenge selection and the `π * σ⁻¹` order remain unchanged. GNI run/verdict branches retain their original bounds. Encoded-instance consumers then use existing public single-round equations. |
| Yao outputs / HBC wrappers | The output proof proposals calculate the unchanged two-message, Alice-first protocol through readers. The hybrid HBC `iff` is used only for the hybrid predicate. YaoReal retains the concrete composition-security term and transports its round premise through the public constant-two equation. Joint PRF, OT and other security hypotheses/admissions remain unchanged. |

## Retired Yao decoder

The original public `decodeMsgs_eq` proof already contains an all-input fuel-sufficiency
bridge: if `v.length ≤ k`, the private fuel decoder equals `BinArith.decWords v`. For a
nonempty word, the public strict second-projection length theorem supplies enough fuel for
the recursive call. Thus choosing `k=v.length` establishes equality for **every word**, not
only correctly encoded lists. Malformed pairing/default behavior is preserved as well.

The delegation keeps the four existing public definition/lemma headers. The new nil/non-nil
reader uses `decWords_nil` / `decWords_of_ne`; the inverse proof identifies the two encoders
through public nil/cons equations and applies `decWords_encWords`. It does not read a foreign
ordinary body. The deleted private fuel definition and two private decoder lemmas have no
remaining references in the composed Yao source. The independently named length lemma in
ThreeColoring is unrelated and untouched. The inverse/empty cases, zero-length messages and
malformed input coverage are preserved; no admission is introduced by deleting this copy.

## Boundaries and policy

All selected patch hunk counts and exact contexts validate. Existing admissions are unchanged
in every composed source. Aside from the approved equivalent decoder delegation, the repairs
add equations or change proofs; none adds a definition/host, simp attribute, security notion,
cryptographic assumption or data algorithm. The four typed-OT prerequisite statement casts
retain their earlier equivalence verdict and are not recertified as new work here.

The GI `rfl` readers use their own definitions, with Core/Mathlib reductions allowed by policy.
Consumer term chains use public equations. No additional explicit foreign-definition unfold
is visible in the inspected additions. The known Garbling `values` conversion remains a
necessary foreign ordinary read until its owner reader is added.

This is source/mathematical review, with no Lean/cache or native check run by the reviewer.
Elaboration and rewrite matching, complete implicit-read sealing, and any new diagnostic
follow-ups remain root's serial verification. No Gate06 closure or filled substantive
security admission is claimed. Only this review and its scratch input manifest were written;
no library, Git or campaign-evidence mutation occurred.

Input manifest: `/Users/seyoonr/.codex/worktrees/ps-gate06-integration/tcslib-pass-shelat-ch2-4/.lake/ps-maintainer/gate06/repairs/secure-computation-gi-proposal-review.inputs.json` (SHA-256 `a212e7a21f496ce1bae964e084b29cbc775750b414538220233574802eba4322`).
It records every reviewed patch fingerprint, application order and original/composed source
hash. The frozen exact-proposal helper was used only through its reviewed pure APIs, with
its SHA checked and its CLI disabled; no other agent program was executed.
