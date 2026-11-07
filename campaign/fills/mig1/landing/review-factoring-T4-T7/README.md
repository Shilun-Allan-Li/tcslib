# T4/T7 independent disposition review

**T4's three assigned corollary re-points are implemented in the prepared tree.**
T7's scheduled inspection is documented below; this is not a claim that every
candidate is factored, retained debt is acknowledged, or MIG-1 is clear to merge.
No Lean, source edit, Git operation, screen, cache or new API implementation was
performed. Source chunks, comparison results, exact hashes and citation records
are retained in this folder.

## Governing scope

The 2026-10-17 ruling in `campaign/items/mig24/TRIAGE.md:55` folds T1–T6/T2b into
MIG-1 as named factoring obligations and schedules T7 for the next PR editing
each file. The immutable megafill brief is more precise: lines136–140 assign T4
and say **“Inspect T7's Loop, Encoding and Simulation singletons”**; lines141–144
permit same-home private helpers and existing cross-file public equations, and
require a precise gap/incomplete disposition if a shared family needs new public
interface. This is an inspection obligation, not authorization to implement every
possible T7 abstraction or to acknowledge retained debt.

Producer `REPORT.md:210` claims T4 done; line213 records the three T7 inspections.
Those are attributed delivery claims. The findings below are independent reads of
the actual prepared source. Other T7 pairs in Sweep, Embed and Contract/Basic
are outside this particular touched-file disposition; reading a file here does
not make it a source edit in this PR.

## T4: actual public reuse confirmed

| Current Composition declaration | Public contract used | Witness |
| --- | --- | --- |
| `computesFunInTime_comp:461` | `bufferedCompTM_computesFunInTime` | `bufferedCompTM M₁ M₂`, coefficient2 |
| `exists_comp_on_image:495` | `bufferedCompTM_computesFunInTime_on_image` | `bufferedCompTM M U` |
| `exists_comp_partial:592` | `bufferedCompTM_computes_iff` | `bufferedCompTM M₁ M₂` |

Each body is a direct existential package of the public theorem. None reconstructs
the capture/rewind/second-phase correctness argument. All three differ from the
API1160 baseline and are byte-identical to the producer's delivered corollaries.
The supplied final2 compiled metadata independently contains each exact public
theorem as a direct reference, with standard3 axiom closure
(`T4-public-reuse.json`). This review did not run a fresh elaboration. T4 can be
reported as implemented, with merge/gate completion still the maintainer's task.

## T7: unchanged legacy material, case by case

All six inspected endpoints are literal-equal to API1160, including attached
docstrings. The five delivery-owned endpoints are also literal-equal to the final
producer source. VirtualInput is not delivery-owned; it matches the frozen API
source. Thus these are retained legacy proofs, not changed/new proof roots covered
by the landing's region seals (`source-comparison.json`). Line numbers below are
from the captured current source; whole-file comment cleanup has moved Loop's
lines without changing these chunks.

**Loop (`loop_run:150`, `FinTM.loop_halted_run:2498`).** The public theorem assumes
empty outputs at its round configurations and a possibly live exhaustion
configuration which halts with `[false]` within an additional segment bounded by
`B`; its conclusion costs `(N+1)*B`. The private theorem instead starts its
exhaustion terminal already halted with output `[false]`, requires no empty
output there, and costs `N*B`. At `N=0` the private terminal's output is nonempty,
so the public theorem's empty-output premise is unavailable. A direct citation
does not preserve the private statement. Conversely the private theorem cannot
directly accept the public theorem's live terminal.

Their inductive driver still shares substantial material: first-round verdict,
shifted family and `runFrom_add` composition. Different statements therefore do
not prove that factoring is impossible. A same-home common terminal-summation
argument, or an extended family including the public exhaustion segment, remains
an unimplemented candidate. No such construction was checked here, and no new
public interface is shown necessary for this in-file pair. The producer's
“differ in terminal and bound” is accurate as a direct-reuse boundary, not a
permanent exemption or factoring-closure argument.

**Encoding (`exists_codeTM_spaceUsed:736`,
`FinTM.toCodeTM_computesInTime_iff:764`).** Both already cite public
`FinTM.computesInTime_relabelState` (`Encoding:699`); the existential row also
cites `MultiTapeTM.relabelState_spaceUsed`. Their common code is bundle
destructuring, eliminating `hk : M.k=1`, and packaging a finite-state relabeling.
One theorem states the result for the designated converter and the other chooses
a code with an additional all-times space clause. The mathematical relabeling
argument is already shared through the public lemmas, rather than proved twice.
No missing relabeling API or further required factoring was established by this
bounded read. This supports the producer's inspection disposition for this pair.

**Simulation/VirtualInput (`bufferedSecondCfg_run:1068`,
`vhostEmitTM_runFrom:278`).** These retain the same existential-tag induction:
obtain a valid endpoint tag from the previous time, obtain the next tag from the
machine-specific step lemma, and chain the two runs. The host configurations and
step contracts differ; neither run theorem directly applies to the other's host.
Their common driver is more specific than a bare two-rewrite induction tile: it
propagates a validity predicate and an existential arrival tag.

Two existing bounded API candidates were inspected:

- `MultiTapeTM.runFrom_comm_of_step` (`Deterministic:252`) requires one fixed
  encoding function commuting with steps. The two targets instead allow either
  valid initial Boolean tag and existentially update it, so that hypothesis is
  not supplied by their current step contracts.
- `Lockstep.runFrom` (`Build/Contract/Basic:1337`) likewise takes a fixed encoding
  and exact block costs. Additionally Contract/Basic imports Simulation at line7;
  Simulation cannot simply import that later layer without a cycle. The brief
  does not authorize another import or a private cross-file host.

The precise common-driver gap is a relation-preserving run interface: from
`R c d` and a one-step preservation premise
`R a b → R (M.step a) (H.step b)`, obtain
`R (M.runFrom c t) (H.runFrom d t)` at the same time. For these clients, `R` is
“there exists a valid arrival tag and the host is the corresponding encoded
source configuration.” A shared interface would need to live below Simulation
or another approved route would be needed. This is a **candidate interface
shape only**, not a proposed implementation, approved name/home, proof of
logical necessity, or assertion that no other published route exists. No exact
drop-in interface was found in the bounded run/Lockstep candidates above.

Accordingly, the cross-file common-driver factoring remains **incomplete if
pursued**. The producer's “needs a public lockstep interface” should be read as
this unresolved sharing route, not a proved necessity or permission to add one.

## Ledger boundary and additional reader caveat

The ledger's old Catalog `a2_loop_halted_run`/map/redirect copy accounting covers
those Catalog copies and their source-side membership. Their retirement does
not by itself acknowledge the retained Loop-internal terminal variant or the
Simulation/VirtualInput tagged-run family. The user-approved run-induction
exclusion at `duplication-ledger.md:363–374` is explicitly about two generic
rewrite tiles with no shared setup argument. It may bear on some common text;
it is not an explicit disposition of this entire existential-valid-tag argument.
This review therefore neither counts a fresh debt family by assertion nor grants
an acknowledgment/exclusion for the whole pair. The ruling/scheduling record is
not blanket acceptance of all similarities in touched files.

There is also a bounded source-level rule-10 caveat: both retained tag-run zero
branches are `exact ⟨b, hb, rfl⟩`. Their typing/equality reads foreign `runFrom`
at time zero. The existing `MultiTapeTM.runFrom_zero` provides the obvious
mechanical reader-repoint candidate. No repair or strict-negative test was run
under this read-only task; the current unchanged proofs must not be represented
as newly opaque-certified. This reader issue is separate from the common-driver
factoring/interface candidate. Root has been notified and owns its disposition.

Suggested records wording: **“T4 implemented by public corollaries. T7's three
touched-file pairs inspected: relabeling already reuses its public mathematics;
terminal-loop variants have different direct premises/bounds with a retained
local factoring candidate; tagged cross-file run sharing has a precisely
recorded incomplete route. No new API or retained debt is approved.”**

The source chunks, source/input hashes and exact existing compiled T4 references
are complete here. No new screen, quantitative debt census, global API-absence
claim, new public proposal implementation, or gate clearance is claimed.
