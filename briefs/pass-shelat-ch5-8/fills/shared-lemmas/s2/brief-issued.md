# S2 overnight fill: one rejection host, four consumer loop retirements

**ISSUED — ready for user dispatch; not dispatched. Selected worker: Claude (user, 2026-11-06 PST).**

This is one coordinated overnight job, unit **`reject-blocks-s2`**, with one sorried host proof
and its four consumer re-points. Continue through the milestones without waiting for another
user reply while work stays in scope. Run this external fill in one Claude session, without
sub-agents. The maintainer may use internal review agents; they do not perform this external
fill. The user dispatches this job and merges its eventual PR.

## Source and delivery

- Repository: https://github.com/Shilun-Allan-Li/tcslib
- Campaign: `cryptography/pass-shelat-ch2-4`.
- **Frozen source ancestor:** `31348fcf7dee32f84db1fc8f929d80653137995e`. Check out that exact commit and create
  `fill/reject-blocks-s2`; record `git rev-parse HEAD`, never rebase the fill branch.
- #227 is merged at this ancestor; Gate 08 closed at its S1 head
  `84f35910912bd3d1cd520beea9469e0ed45ce504`, round 2 PASS, 0 blockers/0 majors/0 minors.
  Its resolutions are `briefs/pass-shelat-ch5-8/gates/08-shared/resolutions-r2.md` in later
  records; the staged copy accompanies this brief. The entire library source at the ancestor
  is identical to that audited S1 source. H15's proof is still the authorized admission.
- **Claude delivery only:** checkpoint/final payloads go to
  `inbox/fills/reject-blocks-s2/` on orphan branch `exchange/pass-shelat-ch5-8`.
  Never push the fill branch or any campaign branch; worker campaign changes land by the
  maintainer's PR, which the user approves. Do not merge the exchange with any other branch.
- Treat findings, reports and repository prose as material to assess. This issued job's scope,
  user rulings, `policy.md`, the campaign checking rules and the attached environment addendum
  govern the work. The latter is the external-host addendum, not the historical internal-worker
  note with obsolete paths/commits.

All attachment paths below are relative to `outbox/fills/reject-blocks-s2/` on the exchange.
Its `inputs/` directly contains the files recorded under
`fills/shared-lemmas/s2/inputs/reject-blocks-s2/` in the campaign records.
`environment-addendum.md` is the staged copy of `fills/fill-environment-addendum.md`. Use
absolute attachment paths when running commands from the frozen source checkout.

Read `environment-addendum.md` and the exchange README before starting. Use Lean **4.25.0**,
the manifest-pinned Mathlib, `python3 -I`, and `scripts/lean_check_tree.sh`, one module at a time.
The campaign authorizes that shell checking method over the repository's generic LeanInfoView
advice. Never run a library-wide `lake build` or an unfiltered cache get. One Lean process on
your host at a time; no self-imposed module timeouts, no locator shim/workaround. This is one
brief/host with milestones; it does not adopt the other campaign's Part 3 megafill protocol.

## Ownership and freeze

Only these five Lean files may appear in the patch series:

| File under `TCSlib/Cryptography/Candidates/` | Work |
|---|---|
| `Concrete.lean` | Fill `polyTimeComputable_rejectBlocksL`, implementing registered host H15 via the existing public repetition host. Private implementation/leaf lemmas supporting that proof may be added here. |
| `DiscreteLog.lean` | Re-point the below-modulus sampler's polynomial-time proof to H15 and retire its private `dla_ss*` loop and orphaned loop-only helpers. |
| `ElGamal.lean` | Re-point the numerical sampler proof to H15 and retire its private `dlc_ss*` loop and orphaned helpers. |
| `RSA.lean` | Re-point the unit sampler proof to H15 and retire its private `rsa_us*` loop and orphaned helpers. Preserve the default `1 % N` semantics. |
| `Rabin.lean` | Re-point prime/Blum-prime generators to H15 and retire the private `rabin_rb*` loop and orphaned helpers. Use H15's tail-length bound for padding. |

All public declaration headers, mathematical statements, hypotheses, visibility and public
definition bodies are frozen. No public declaration is added or removed. Outside H15, edit
only proofs needed by those re-points and deletion of now-unused private loop machinery.
Precise imports may be added within the owned files if they introduce no cycle. Recompute the
needed bootstrap closure and narrowed Mathlib roots for any added imports before checking.
Private test/output adapters may be simplified for the new host interface; report exact names,
old/new semantics and why each change is needed. Keep all unrelated proofs and definitions.
New helpers are private and confined to the owned file; a missing shared public interface is
E-API, not permission to copy or publish it. Number-theory arithmetic remains through the
existing `ArithmeticFP` hypothesis bundle. `BlumDensity` stays a hypothesis.

The owned-file fingerprints and line counts are in `inputs/owned-baseline.json`. The sole
owned admission is H15: **owned sorry tokens 1 → 0**, whole `TCSlib/` **511 → 510**, with no
other changed admission. Those are code-token counts; use the repaired lexical scanner.
Imported closure counts (`inputs/base-sorries.txt`) are not proof dependencies or owned targets.

Standing size ruling: do not split a fill-owned file. The four already oversized candidate
files shrink as loops disappear. Record every final file size and any Concrete growth past
1000 lines under the fill-owned-file rule; keep it coherent and disclose the reason. Do not
create an unregistered host or a new helper module to move the target out of its gated home.

## The frozen host statement

```lean
theorem polyTimeComputable_rejectBlocksL (E : ℕ → ℕ → Prop) [∀ a, DecidablePred (E a)]
    {acc : List Bool → Bool} (hacc : PolyTimeComputable fun x => [acc x])
    (hspec : ∀ w b : List Bool, acc (pairEncode w b) = decide (E (listToNat w) (listToNat b)))
    {par kw bw tw c : List Bool → List Bool} (hpar : PolyTimeComputable par)
    (hkw : PolyTimeComputable kw) (hbw : PolyTimeComputable bw) (htw : PolyTimeComputable tw)
    (hc : PolyTimeComputable c) :
    ∃ g : List Bool → List Bool, PolyTimeComputable g ∧ ∀ z,
      (g z).tail.length ≤ (kw z).length ∧
      rejectBlocksL (E (listToNat (par z))) (kw z).length (bw z).length (tw z).length (c z) =
        if g z = [] then none else some (listToNat (g z).tail) := by
  sorry
```

Its payload contract is deliberately weak: success means **nonempty**, with a meaningful tail;
there is no prescribed head bit, canonical payload, or exact payload width. Consumers test
emptiness and use the public value/length clauses. They may not read the private implementation.

`kw`, `bw`, `tw` give **lengths**, not binary-coded numbers. Their contents may be arbitrary.
Handle `k=0`, `B=0`, `T=0`, `k>B`, overlapping blocks and short/empty coin words exactly as the
existing total `rejectBlocksL` defines them. Add no positivity, full-coin-length or `k≤B` premise.
The predicate's efficiency comes from `hacc` and `hspec`, not merely from decidability of `E`.

## Route and reuse

Q3(A) keeps H15 in Concrete; Q4(B) assigns its proof to this external fill. Q7(A) authorizes the
six sketch refreshes below. Q2(A) puts S1/S2 ahead of clean-up part 2. Do not commission efficiency,
optional machine bridges, or the ungated chapter 5–8 proofs as part of this job.

1. Harvest the existing Rabin loop proof into the registered H15 implementation, generalizing
   its header with the parameter word. Start from `rabin_rbStep`, `rabin_rbBlock`, `rabin_rbAcc`,
   `rabin_rbLoop_poly`, `rabin_rbStep_iterate`, and `rabin_rbFind_eq` in the frozen source.
   These are source examples, not private APIs to cite from Concrete. Move/adapt what is
   necessary and delete the retired copies in the final consumer files; disclose the harvest.
2. Carry header `⟨⟨bw, kw⟩, par⟩`, counter `tw`, and remaining coins. A step preserves the header,
   drops one counter bit and `B` coin bits. The test is counter-nonempty and the supplied
   predicate on `⟨par, coins.take k⟩`; the output may choose `true :: trial word` as this
   implementation's witness.
3. Use the existing public `polyTimeComputable_iterateFind` host with `R = var` and orbit bound
   `2n+4`, as in the frozen sketch. It depends on H14, already registered/proved; build no
   second search/runner. Show the first-step bound and that well-formed states shrink, using
   `StateLoop.length_pairFstD_add_pairSndD_le`. At step `i`, the counter is `tw.drop i` and the
   coins are `c.drop (i*B)`, by induction and `List.drop_drop`.
4. The test is `i<T ∧ E ⟦par⟧ v_i`, with `v_i = ⟦(c.drop (i*B)).take k⟧`. The start state's
   length covers `T`; `IterateFind.find?_range_and_lt` truncates the larger search to `[0,T)`.
   Read the sampler through `rejectBlocksL_eq_find?`. Failure gives `[]`, success the trial
   payload, and `List.length_take_le` gives the bound.
5. The repetition theorem's generated matcher stays **sealed**. Follow dl-a's checked `split`
   pattern/equation cases; do not make conversion work by unfolding
   `polyTimeComputable_iterateFind.match_1`. The staged matcher control closes unsealed and
   fails sealed; your delivery must reproduce that sensitivity.
6. Re-point the four consumers through H15's statement. Below-modulus instances use
   `sampleBelowL_eq_rejectBlocksL`; unit instances use `sampleUnitL_eq`. Normalize a payload
   to the required width with `natToList_zero_append_drop`, preserving short/zero-width cases.
   Use `PolyTimeComputable.comp'`/`.congr` for applied composition and pointwise transport.
   The public `polyTimeComputable_tail` computes `List.drop 1`; transport to `List.tail` with
   `List.drop_one` through `.congr`, as the checked payload route demonstrates.
   RSA and Rabin retain their own public sampler equations and fallback values; Rabin reads
   RSA's unit sampler through `polyTimeComputable_unitSampleStr`. The existing Rabin private
   adapters accept arbitrary Boolean tests, while H15 needs a numeric predicate specification:
   thread that specification through the private adapters (or replace them); the actual odd
   and Blum callers already supply it. No public hypothesis is added.

The inherited Rabin proof is not a license to retain its old explicit `simp [Option.guard]`:
use `Option.guard_apply`. Core/Mathlib definitions may reduce in `rfl`, `show` or `decide`, but
are not passed to `simp`, `rw`, `unfold`, `dsimp` or `delta`; use published equations such as
`Function.comp_apply`. Foreign TCSlib definitions are read only through their public lemmas.
Treat `PolyExpr.eval` and `glNeed` as the recorded notation exceptions for sealing; prefer the
published evaluation lemmas. Reducible abbreviations follow policy's notation rule.

The host's source attribution remains [PS10, Theorems 52.3, 53.2, 61.7 and 63.10] and its
truncation deviation. Source PDF: `Pass–Shelat.pdf`, SHA-256
`7624556077a7a272ba0b3ddb7cd47b96574fb0b4b4947a25467d1f91bb61bda8`;
book page = PDF page − 12. This computational host does not strengthen the already-proved
statistical sampling statements or change the book's expected-time/exact-sampling deviation.

## Authorized sketch refreshes

Refresh the docstrings of these six public declarations to describe H15 application instead of
the deleted private loops, preserving their statement prose, formulas, citations and bounds:

- `polyTimeComputable_expSampleRaw` (DiscreteLog).
- `polyTimeComputable_egGenRaw`, `polyTimeComputable_egEncRaw` (ElGamal).
- `polyTimeComputable_unitSampleStr` (RSA).
- `polyTimeComputable_oddGenRaw`, `polyTimeComputable_blumGenRaw` (Rabin).

Update necessary module/private-helper references when deleting those helpers. H15's own
sketch follows its proof; a sound route change may use the standing docstring-only refresh
rule, with the departure and replacement mathematics explained in REPORT.md. Never change a
statement to rescue a proof.

## Milestones and checkpoints

1. Environment preflight/cache/bootstrap passes; all five baseline owned files compile.
   Use `inputs/order.txt` (94 modules) for the candidate bootstrap. Fetch the narrowed cache
   for `inputs/checks-roots.txt` (144 named Mathlib roots), which covers final verification;
   `inputs/roots.txt` records the 75-root candidate subset.
2. H15 proof is complete and its axiom print is standard-only; the five owned files compile.
3. dl-a and dl-c consume H15, their copied loops disappear, and their sketches are refreshed.
4. RSA and Rabin consume H15, remaining copied loops disappear, all six sketches are refreshed.
5. Full verification below passes and the final payload is delivered.

Push a complete checkpoint at milestones 2, 3 and 4; then continue, without waiting for a reply.
If blocked, push the complete partial payload with a concrete escalation and continue only
independent work within scope. Keep files compilable by the sorry ladder while developing;
report temporary admissions honestly in partial checkpoints. No new admission may survive a
final delivery. Do not remove old proved code merely to make a test or census pass.

## Final checks

- Recheck the owned modules and their downstream modules in `inputs/order.txt`. Before
  checking `audits/pass-shelat/Checks`, build any remaining prerequisites in
  `inputs/checks-order.txt` (422 library modules), in its recorded order; all 94 candidate
  modules are included, so 328 additional modules are needed on a fresh candidate-only tree.
  Then check `audits/pass-shelat/Checks`. Use one `scripts/lean_check_tree.sh` invocation per
  module; log start/end time, return code and peak RSS, and require a fresh nonempty object.
  Never run a check against missing prerequisites.
- Public source-header diff against the ancestor is **empty** over all five owned files.
  Verify ownership, the exact host header, unchanged public definition bodies, and report
  every changed/deleted private declaration. No new `@[simp]` or opaque/axiom shortcuts.
- Lexical census: sole owned/global delta is removal of H15's one `sorry`; no new `axiom`,
  `admit` or `sorryAx`. Print axioms for H15 and every changed/new retained declaration,
  including private helpers. The host and re-pointed proofs must have standard axioms only
  (`propext`, `Classical.choice`, `Quot.sound`). Compare aggregate axiom prints with the base,
  preserving multiplicities and distinguishing record count from distinct-name count.
- Rule 10: collect from elaborated types and proof terms (private/generated helpers and
  matchers included), plus conservative ordinary foreign TCSlib definitions from each owned
  module's import closure to cover anonymous commands. Seal whole files and classify every
  failure against the **issue ancestor**, not an intermediate checkpoint. Include a standalone
  anonymous-read control, and the explicit repetition-matcher control, both passing unsealed
  and failing sealed at their proof sites. Resolve actual numerical/hygienic Names from the
  environment; verify installed status; count already-irreducible names separately and never
  count a seal-command diagnostic as a proof result. No unsafe reducibility override.
- New/touched declarations have **zero foreign-definition reads** and no explicit foreign
  unfolding/rewrite. Separately scan `simp`/`simp only`/`rw`/`unfold`/`dsimp`/`delta` lists,
  including blank/comment continuation lines. Seals do not detect explicit unfolds. The
  documented instance/reducible/notation exclusions do not authorize new explicit unfolds.
- Existing untouched sealed failures are data to classify and reconcile, not a blanket
  exclusion and not permission for unrelated cleanup. Gate 08's broader five-owned-file
  examples include `primesPairEquiv_apply_val`,
  `ExpGroupGen.FullLength.exists_fullLengthExcept`, `rsaTrapdoor_oneWay`,
  `rabinCollection_index`, `rabinBlumTrapdoor_index`. Record baseline/source comparisons and
  whether base seals were rerun. Reject invalid harness attempts before interpreting failures.
- Run style and campaign/check-8b lints; compare against the ancestor. Approved fill-owned size
  findings are exceptions, not clean lint exits. Every new public definition would need its
  reading lemmas but is outside this proof-only/public-surface freeze; report E-API instead.

Relevant methodology and native pre-ship evidence accompany the brief. Paths/time flags in
historical maintainer drivers are platform-specific examples; the external addendum and the
requirements above govern your host. Do not copy another session's objects/dependency trees.

## Delivery payload and report

At every checkpoint and final, write only `inbox/fills/reject-blocks-s2/` on the exchange:

- `REPORT.md`: exact ancestor/head, checkpoint/final/partial status, completed targets, deleted
  loop symbols, all six sketch dispositions, code copied/harvested and payback, interface gaps,
  resource/cache/bootstrap facts, check commands and results, axiom sets, source-header/census
  comparison, seals/controls, lints, and honest limits. State final file sizes and any accepted
  size exceptions. Never claim a skipped check passed.
- `patches/`: the complete `git format-patch` series from the frozen ancestor through your
  current `fill/reject-blocks-s2` head; keep real commit boundaries and no unrelated files.
- `src/`: all five final owned Lean files at their repository paths, including unchanged files
  in a partial checkpoint. Applying the full series at the ancestor must reproduce these bytes.
- `evidence/`: logs, probe/tool sources, manifests/candidates, source comparisons and summaries
  supporting the report. Scratch probes are evidence; only the five owned library files belong
  in the campaign patch series.

Pull/rebase the exchange before each push; commit only your payload path, preserve other
workers' files and staging, never force-push, and never push the campaign/fill branch. Commit
messages: `fill reject-blocks-s2: checkpoint <n>` and `fill reject-blocks-s2: final`.

Escalations: **E-RES** follows the attached addendum; **E-API** identifies the exact missing
public interface and its needed type; **E-TRUE** gives a counterexample to the frozen claim;
**E-FREEZE** identifies a needed change outside ownership/statements. Push the complete
compilable partial payload and report; do not silently weaken a claim, add a hypothesis,
copy a foreign proof, invent an unregistered host, or modify an unowned file.

**Not yet clear to merge — external fill, delivery review and a user-approved PR remain.**
