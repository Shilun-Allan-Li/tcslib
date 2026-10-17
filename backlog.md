# Backlog

The consolidated tracking file for the Arora-Barak campaign branch
(`complexity/arora-barak-ch1`) and adjacent repository work: human-review
design questions, queued and on-hold campaign work, deferred formalizations,
pending decisions, and housekeeping. Consolidated 2026-09-18 from the two
campaign plans, the audit resolutions records, and session assessments.

**Conventions.** This file is the *canonical home* of the human-review
question statements (§1) — the plans keep stable numbered stubs, since audit
documents cite the numbering — and the *tracking index* for everything else
(scope prose remains in the plans; decision-log history is never moved).
New items land here; an item leaves only by a decision recorded in the
relevant plan's decision log. From the next audit round onward this file
joins the bundle attachment set.

---

## 1. Human-review design questions (reserved — never closed by an automated gate)

Flagged for a **human** auditor/maintainer: the LLM audit rounds verify
correctness, but these are matters of architectural taste and trust-surface
policy.

### CH1-Q1 — the 3A Mathlib-computability bridge

*Origin: `AroraBarakChapter1Plan.md` §5 (epoch 3, batch A);
`MathlibBridge.lean`, `Turing.exists_effectiveMachineCode`.*

The audited docstring sketch called for the canonizer machine to be
**hand-assembled from this repository's composition combinators** ("its
construction uses the composition combinators", optionally with a polynomial
`canonizerTime`). The delivered proof instead (i) proves the canonization
*function* primitive recursive, (ii) compiles it through **Mathlib's verified
recursion-theory pipeline** (`ToPartrec.Code.exists_code` →
`PartrecToTM2.tr_eval`), (iii) simulates the resulting TM2 stack machine in
our model with a bespoke private `bridgeTM`, and (iv) lands in the binary
alphabet via the proved `alphabet_reduction`, extracting the time bound by
finite maxima (no polynomial bound claimed — permitted, since
`canonizerTime` is existential). The batch flagged the deviation itself; the
maintainer verification pass confirmed the proof is sorry-free with the
standard axiom footprint and zero public-interface drift. **Open questions
for a human:** (a) is the heavyweight `Mathlib.Computability.TMToPartrec`
import into the TM tree acceptable, or should the bridge be quarantined
behind the planned phase-5 `MathlibBridge` module boundary (it effectively
front-runs that module)? (b) is the enlarged trust/review surface (Mathlib's
TM2 semantics + the private `bridgeTM` simulation, ~150 private
declarations) preferable to a longer but self-contained combinator
construction? (c) should the abandoned polynomial-`canonizerTime` claim be
recorded as permanently out of scope, or re-derived later from the
combinator route if one is ever written? Since the epoch-3→4 merge the
bridge lives in the dedicated `MathlibBridge.lean`, which implements the
quarantine that part (a) contemplates — the `TMToPartrec` import is confined
to that one module and nothing outside `exists_effectiveMachineCode` depends
on it — but the implemented quarantine does **not** dispose of this
question: parts (a)-(c) remain open for human review (epoch-4 audit,
finding 3: an earlier version of this text misplaced the bridge inside
`Encoding.lean`).

*Cross-link: part (c) gained relevance in Chapter 2 — see §3, "Polynomial
canonizer for a concrete scheme".*

### CH1-Q2 — the 3B universal-interpreter proof architecture

*Origin: `AroraBarakChapter1Plan.md` §5 (epoch 3, batches B + B2);
`Universal.lean`, `Turing.universal`.*

The proof followed the audited sketch's outline (prefix-only startup,
canonizer capture onto a table tape, four-work-tape interpreter with a fixed
finite controller), but the realized architecture is by far the campaign's
most involved artifact: 2465 lines (2831 after the epoch-4A timed fill), 104
private declarations built across two agent sessions (WIP `f191b918` +
continuation), a bespoke checkpoint relation (`universalRelation`) with
generic block-simulation assembly (`universal_block_run` /
`universal_from_blocks`), a virtual left boundary via a marker tape, a unary
state tape with group-wise table scanning, and an *exact* per-phase cost
ledger realized to `universalBlockBound = 3L + 5N + 20`. The kernel checks
all of it, and the public statement is frozen and audited — but the *design*
was never itself an audit deliverable at this level of detail. **Open
questions for a human:** (a) is this the right load-bearing shape — and
which parts (the capture wrapper, the block-run/`universal_run_join`
assembly, the marker-directed rewind and unary-copy gadget patterns, all
flagged by the agents as promotion candidates) should graduate to shared
modules rather than being re-derived? (b) is the exact-ledger posture
(`3L + 5N + 20` proved to the transition) worth its brittleness against any
future change to `CodeTM.serialize`, or should the maintained invariant be
an existential bound with the exact ledger demoted to documentation? (c)
does the interpreter's claim to *be* the book's universal machine (as
opposed to satisfying the frozen statement, which the kernel settles)
deserve a targeted human read of the construction's core definitions
(`UniversalControl`, `universalInterpreter`, `universalRelation`), given no
executable diagnostics of the whole interpreter ever ran (the batch-B smoke
tests aborted on deep recursion and were discarded)?

*Cross-link: question (b)'s exact ledger is now also load-bearing for the
Chapter-2 `TMSAT_mem_NP` fill (the quantitative public bridge, §2), which
will expose a form of the constant publicly.*

### CH2-Q1 — generality of `HALT_not_mem_NP`

*Origin: `AroraBarakChapter2Plan.md` (phase-1, round-2 audit, finding 3);
`ClassNP/Reductions.lean`.*

The statement is currently at `Turing.EffectiveMachineCode` generality
because its proof route reuses Chapter 1's `HALT_not_computable`, whose own
proof runs the universal evaluator. The round-2 auditor showed this
restriction is **not mathematically necessary**: a direct diagonalization —
the public diagonal-pairing machine, the searcher's finite-control transform
with the halt/loop roles swapped, `Turing.exists_codeTM`, no evaluator —
proves `HALT` undecidable for *every* lawful `Turing.MachineCode` (and the
earlier "trivial-machine scheme" counterexample is unlawful: constant
decoding violates `decode_encode`). **The question:** add that diagonal
lemma as a new audited statement (a strengthening of Chapter 1's
uncomputability story that shares its main fill obligation, the
control-transform lemma, with `HALT_NPHard`) and generalize
`HALT_not_mem_NP` to `MachineCode` — or keep the conservative signature as a
documented API/proof-route restriction? Maintainer's provisional choice,
pending review: the conservative signature, with the docstring stating the
restriction honestly; the diagonal lemma is deliberately *not* slipped into
a repair round, since it would enlarge the audited surface of Chapter 1's
uncomputability chapter.

---

### CH7-D1 — the block stack's per-loop lemma family (duplication threshold crossed)

*Origin: the ch7 fill gate, run on the merged ch3-4 tree after PR #11
(`audits/ch7-fill-pack.md`, question 7); maintainer pre-screen
`audits/evidence/ch7/ch7-fill-duplication-screen.md`. This item is opened
under `workflow.md` §4, which leaves no discretion once a file passes one
fifth copied material.*

The OR, XOR and strict-majority block loops each re-prove the same orbit,
length and init lemmas under renaming. The proofs are identical up to the
step function's name, so a single lemma quantified over the step function
would serve all three. Six `private` members:

- four in `ClassNP/PolyTimeBlockMajority.lean`: **4 of its 14 declarations
  (28.6%, 85 lines), over the threshold**;
- two in `ClassNP/PolyTimeBlockTests.lean` (2 of 25).

No pre-existing repository material is copied. **The question:**
acknowledge the debt and name its owner and resolution window. The fill
gate's auditor is instructed to report the family at major ("human
acknowledgment required", `audits/TEMPLATE.md` failure mode 5), and the gate
cannot close until this is answered.

Maintainer's provisional proposal, pending review: the owner is the
Chapter-7 campaign (Aparna). The window is the post-gate cleanup her pack
already proposes for splitting the counting layer out of
`Randomized/Classes.lean`. The resolution is one generic orbit/length lemma
set in `PolyTimeBlockLoop.lean` consumed by all three loops, with statements
unchanged. The alternative is to fold it into 12.2c alongside the EmitIter
harmonization.

**Answered (user, 2026-10-10): fold into 12.2c.** The debt is acknowledged.
The owner is the user's own 12.2c per-theme refactor, not the ch7 campaign:
deduplication is being done there anyway, and colleagues are spared it. The
resolution is one generic lemma set with statements unchanged, coordinated
with the ch7 owner because the files are hers, and run after the ch7 fill
gate closes.

**Extended (user, 2026-10-10; ch7 fill gate round 2, R2-2).** Under the
standing source-inclusive census the family is larger: at least 12/25 in
`PolyTimeBlockTests`, which crosses the threshold in a further file; at
least 8/14 in `PolyTimeBlockMajority`; and 1/32 in `PolyTimeBlockLoop`.
The auditor also found the `anyStep`/`majStep`, `anyEmit`/`majEmit`,
orbit and loop-output adaptations. The extension is acknowledged, with the
same owner and resolution, its scope widened to the generic
guard/countdown/orbit/single-emission reasoning the auditor identified.

---

### CH7-D2 — `EmitIterEmbed`'s re-proved run facts (duplication threshold crossed)

*Origin: the ch7 fill gate, round 2 (`audits/ch7-fill-r2-findings.md`,
R2-1). Opened under `workflow.md` §4.*

`Build/EmitIterEmbed.lean` re-proves five existing run facts, so at least
5 of its 18 declarations (27.8%) are copies:

- `step_output_prefix` and `runFrom_output_prefix`: Loop's private
  `emLoop_step_prefix`/`emLoop_run_prefix`;
- `runFrom_output_extends`: a specialization of `Finite`'s public
  `MultiTapeTM.output_prefix`;
- `runFrom_of_halted`: `Deterministic`'s public `runFrom_of_halt`;
- `state_isSome_of_runFrom`: Loop's private `loop_live_prefix`.

**Answered (user, 2026-10-10): acknowledged, folded into 12.2c item 6.**
The run facts get one home in `Deterministic.lean`/`Finite.lean`.
`EmitIterEmbed`'s versions become citations or re-exports with statements
unchanged, and Loop's three private copies are deleted. Coordinated with
the ch7 owner.

---

### CH34-D2 — `Codes2Tape.lean`'s format-specific parse layer (duplication threshold crossed)

*Origin: ZF-B/ZF-B2, integrated 2026-10-10
(`audits/zone-agent-reports/f1-B2-REPORT.md`). Opened under `workflow.md`
§4, which leaves no discretion past one fifth.*

After the promote-first step (f171767f) and ZF-B2's deletion of all 46
format-independent copies, **23 of `Codes2Tape.lean`'s 33 declarations
(69.7%; 3 strict twins)** remain two-tape instances of `CodeParser.lean`'s
and `MathlibBridge.lean`'s one-tape top layer: the record reader and table,
parse, decode, scan, canonize, and their laws. They cannot be cited across
formats. `NDCodes`'s pending `exists_effectiveNDMachineCode` will need the
same layer a third time. **The question:** acknowledge the debt and name
its owner and window. The maintainer's provisional assignment is 12.2c
docket item (iii), a format-parameterized parse layer serving all three
formats, with statements unchanged, under the user's standing preference.
It awaits the user's explicit confirmation; the A-S2 fill gate cannot close
over it until then.

**Answered (user, 2026-10-10): acknowledged**, and added to the 12.2c
tasklist (`AroraBarakChapters3-4Plan.md` §4d, item 8) as an explicit task.

**Brief issued (2026-10-10):** `briefs/ch34-t1-item8.md` (12.2c tranche T1).
A new `TuringMachine/CodeFormat.lean` holds the generic layer (table grammar
`Turing.CodeFormat`, a `k`-generic record reader, the shared two-work-tape
table); the one-tape and two-tape formats become instances, statements
unchanged. **Sanctioned exception:** `workPair` and `actionBits₂` move verbatim
from the chapter file `NDCodes.lean` into `CodeFormat.lean` (one added import
in NDCodes, no NDCodes statement changes), so that their bridge lemma exists
once instead of as a forced duplicate. The ND instance remains `NDCodes`'
group-C fill, which this layer unblocks. Pre-ship probes:
`audits/evidence/ch34-t1/Item8*PreShip.lean.txt`.

---

### CH34-D3 — the two uniform-scheme assemblies (B5a's pre-disclosed forced mirror, in a file with earlier copies)

*Origin: the B5a fill, delivery 1, integrated 2026-10-12
(`audits/b5a-fill-agent-reports/REPORT.md`, "Duplication governance";
`audits/fills-4-integration.md`). Opened under `workflow.md` §4, which leaves
no discretion when a delivery adds copies to a file that received copies in an
earlier epoch: `Codes2Tape.lean` did (CH34-D2).*

B5a's brief pre-disclosed the two scheme instances as a forced mirror pair.
The frozen target structures (`UniformMachineCode` in `EXPCOM.lean`,
`UniformMachineCode2` in `Codes2Tape.lean`) are distinct, and each must be
packed from the same two §12.11 contracts. The screen measures
`Codes2Tape.lean::exists_uniformMachineCode2` ↔
`EXPCOM.lean::exists_uniformMachineCode` at 322/428 and 322/429 characters
(75%). That is one declaration in each file: 322 characters, or 11.0% of
`Codes2Tape`'s 2,934 extracted body characters and 8.9% of `EXPCOM`'s 3,626
(the agent's denominators, `evidence/copy-coverage.txt` in the delivery).
Both are below one fifth. The agent's conservative union metric (33.2% and
20.4%) also counts the pre-existing frozen structure and writer matches (item
8's residual family), which are not copied proved material. **The question:**
acknowledge the pair as forced, or name a factoring. Each body is pure
packing: two `obtain`s from the §12.11 rows, then a field-by-field structure
literal. A generic public lemma over `MachineFormat` could absorb the two
`obtain`s, but not the field mapping, which is specific to each frozen structure
and is most of the 322 characters. Eliminating the pair would mean redefining
both frozen chapter-3 structures as instances of one generic structure: a
statement change to audited definitions, needing its own gate, to remove about
a dozen lines of boilerplate.

**Answered (user, 2026-10-12): acknowledged as forced.** No factoring is
scheduled. The pair stays as delivered, and the B5a fill gate may close over
it. A later delivery that adds to the pair, or copies anything else into
either file, is new debt under `workflow.md` §4.

---

### CH34-D4 — `EXPCOM.lean` past one fifth copied material (B5b's summit, in a file under CH34-D3)

*Origin: the B5b fill, integrated 2026-10-12 (`audits/ch34-fill-agent-reports/b5b-REPORT.md`,
"Duplication"; `audits/fills-6-integration.md`). Opened under `workflow.md` §4 on both counts:
the delivery takes `EXPCOM.lean` past one fifth copied material, and the file already received
copies in an earlier epoch (CH34-D3).*

B5b's conservative ledger counts 4,930 of `EXPCOM.lean`'s 13,500 extracted body characters as
copied: **36.52%**. **Erratum (B5b gate, round 1, minor 3):** the review-discovered
`expcom_inc_prefix` (107 normalized body characters) was left out of the numerator; with it the
historical count is 5,037 of 13,500, **37.31%**. The delivery's own calculation, 36.52%, stays as
it was reported. The numerator takes whole bodies, not shared text:
- the three ledger lemmas and the summit, transcribed from the brief's probe (the prescribed
  route);
- three pre-disclosed forced restatements: the powers-of-two `Nat.bits` fact (181 characters
  shared with Separation's private `bits_two_pow`, 94% / 84%, the delivery's one new screen
  pair), the all-`true` overflow direction of `incFixed` (public in `MeyerTableau`, which
  `EXPCOM` cannot import; no shared text), and the padding parse's triple uniqueness (194
  characters shared with the frozen reduction);
- CH34-D3's 322-character mirror.

The maintainer's review adds one undisclosed restatement: `expcom_inc_prefix` restates Catalog's
private `catalog_increment_value`.

**The question:** acknowledge the ledger as delivered, or schedule the factorings. Each one
promotes a small fact that does not depend on `EXPCOM`, with no statement change:
- the `Nat.bits` shift law (`(2^j·m).bits = replicate j false ++ m.bits`, and its `m = 1` case)
  as a public lemma in `Encoding` or `Build/Convention`; it also retires the copies in
  `Separation` and `ConfigGraph` (F6-1(a));
- the overflow criterion of `incFixed` in `Build/Convention` (F6-1(e));
- `catalog_increment_value`, made public and cited in place of `expcom_inc_prefix`;
- a shared triple-uniqueness lemma for the padding parse.

**Maintainer's recommendation:** acknowledge the probe transcriptions as forced (they are the
brief's route), and schedule the first three factorings in the dedup window.

**Answered (user, 2026-10-12): factor before closing.** The three factorings land in a maintainer
PR before the B5b gate closes:
- the `Nat.bits` shift law, `Turing.bits_two_pow_mul` with its case `bits_two_pow_eq_replicate`,
  in `TuringMachine/Encoding` (`Build/Convention` cannot see `Nat.bits` without a new import);
- the `incFixed` overflow criterion, `Turing.incFixed_eq_none_iff_replicate`, in
  `Build/Convention`;
- the `incFixed` prefix law, `Turing.incFixed_replicate_true_append`, also in `Build/Convention`.
  This replaces "make `catalog_increment_value` public": the general law sits where
  `incFixed` is defined, and both Catalog's `catalog_increment_value` and EXPCOM's
  `expcom_inc_prefix` are derived from it.

The probe transcriptions are acknowledged as forced. Two copies sit in colleague-owned files
and stay for the user's dedup window: `TimeHierarchy/Separation.lean`'s private `bits_two_pow`,
and `CircuitComplexity/MeyerTableau.lean`'s public `incFixed_eq_none_iff`. The new public names
avoid both, so neither file changes.

**Done (2026-10-12; `6c7e35bd`, PR #70; `audits/ch34-d4-record.md`; replay 167/167).** The four
public lemmas landed in `Encoding` and `Build/Convention`. `EXPCOM`'s `expcom_bits_two_pow` and
`expcom_inc_prefix` and `ConfigGraph`'s `s1b_radius_bits` are deleted. `expcom_all_true` and
Catalog's `catalog_increment_value` keep their statements and are derived from the public laws.
**Still open:**
- the two colleague-owned retirements above (F6-1(j), acknowledged by the user with the
  factoring's one new pair);
- the shared triple-uniqueness lemma for the padding parse (194 characters shared with the
  frozen reduction), which the ruling did not include. It stays a dedup-window request.

---

### C1-P1: promote C1c's blank-cell query bound to `Oracle.lean` (from the epoch C1 fill gate, note 15)

C1c proved a private blank-cell bound in `OracleNondeterministic.lean`: a
blank query cell at position `n` gives `(queryString cfg).length ≤ n`. Its
natural home is `TuringMachine/Oracle.lean`, where the deterministic
`queryString_length_le` could then cite it instead of re-deriving the tail.
The window is the next batch that owns `Oracle.lean` (B1 is the likely
candidate). Statement unchanged; additive.

**Discharged (2026-10-11, B1).** The bound is public as
`Turing.OracleTM.queryString_length_le_of_blank` in `Oracle.lean`, and
`queryString_length_le` now cites it, statement byte-identical. E5
(`OracleNDTM.queryString_runWith_length_le`) cites it too; the private copy is
deleted.

### FH-1: one public first-halt lemma; seven private copies to retire (from B1)

*Design it with MIG-0's no-earlier-exit cut field.*

`Turing.MultiTapeTM.exists_first_halt` (`Finite.lean`, 2026-10-11, B1) is the
shared form of the least-halting-time argument. It discharges the
liveness-before-halt guard of `capture_run`/`emit_run` and the R1 returning
contracts. Seven private copies predate it and are untouched. They are recorded
here for the dedup window, and each owning file's batch re-derives its copy
through the public lemma:

- `ClassNP/EXP.lean:812`: `enumCont_first_halt`
- `ClassNP/SAT.lean:914`: `sat_first_halt`
- `ClassNP/SAT.lean:4013`: `sat_call_first_halt`
- `CookLevin/Hardness.lean:6164`: `clA5_call_first_halt`
- `Build/Catalog.lean:5981`: `f2_loop_first_halt`
- `Build/Catalog.lean:8926`: `f2_splitCount_firstHalt`
- `Build/Loop.lean:187`: `loop_first_halt`

Line numbers are at `22b6c84a`.

### FAC-1: nine `TuringMachine` files missing from the topic facade (from the §12.8 gate)

Policy §1 asks a topic facade to import every file of its topic. At the
§12.8 statement gate (decision 6, user, 2026-10-11) the five §12.8 modules
were wired in: `SymbolLift`, `Build/CounterLoop`, `Build/Scan`,
`Build/InputCall` and `Build/CfgRecord`. Nine older files are still absent
from `TCSlib/Complexity/TuringMachine.lean`:

- `Build/EmitIterBody`, `Build/EmitIterEmbed` (ch7, colleague-owned)
- `Build/VirtualInput`, `Build/Zone` (§13; Zone is under the §13d revision)
- `Codes2Tape`
- `NondeterministicSpace`
- `OracleAgreement`, `OracleFinite`, `OracleNondeterministic`

Some of these are reachable from the root through other facades. Each needs
the import and a Contents entry, then a downstream replay of the facade. The
colleague-owned files need their owners' agreement. Schedule: the 12.2c
per-theme split, or earlier with each owning file's next batch.

### H-1: refresh the stale ch1 audit program `audits/programs/ch1-infra-BridgeExportAxioms.lean` (from the 12.2c item 8 integration)

The program, written 2026-10-03, still expects `Complexity.TMSAT_mem_NP` to
contain a `sorry`; it was proved on 2026-10-04 (`9f748601`). Its later checks
on `TMSAT_NPHard`/`TMSAT_NPComplete` are stale too. It fails identically at
every commit since, unrelated to any batch. Refresh its expectations to the
current state, or retire it in favour of the axiom logs. `ch1-infra-BuildSpecAxioms.lean`
still passes.

### BL-W: optional hypothesis weakenings of the `Complexity.BlockLoop` layer (from the 12.2c T1 item 7 gate, note 13)

`BlockLoop.orbit` needs nonempty heads only below `K`. `iterate_done` does not
need `hp`. `flatMap_emit_orbit` needs nonemptiness only at `K`. The OR
engine's `hxr` is dispensable. Each weakening is additive or a statement
change, so it waits for a window that may touch these public statements
(coordinate with the ch7 owner). Optional.

---

### R80B-E1: define `counterLoopTM` as the identity instance of `counterLoopTMVia` (from the R8.0b fill gate, finding F1)

*This is MIG-4 (scenario B: the duplicated statements are retired).*

The R8.0b fill (§12.8 stream D) mandated two definition texts: the new rich-body host
`Turing.counterLoopTMVia` and the frozen `Bool` host `Turing.counterLoopTM`. Their copy-text pair
is 91% (and 84% the other way). The brief's freeze made factoring impossible within the fill.
There is one host induction, and the `Bool` contracts are Z5 re-derivations of the generic ones,
so no proof is duplicated; the pair is definitional.

**Answered (user, 2026-10-11): accepted as a one-off exception** for exactly this definition
pair. It is recorded in `audits/s12-8-fill-D-resolutions.md` and in the ledger. **Cleanup: the
12.2c window.** Place the generic host before the `Bool` specialization, and redefine
`counterLoopTM M a exit := counterLoopTMVia (Function.Embedding.refl Bool) M a exit` (the
symbol lift at `refl` is the identity table, `counter_refl_agree`). Then re-check every
consumer under that separately authorized definition change. This is a frozen-definition
change, so it needs its own gate.

### U-1: re-derive the chapter-1 universal machine from B5a's generic step block (user, 2026-10-11)

*Merged with MIG-2 (user, 2026-10-12): the timed-layer dedup and this re-derivation are one migration item.*

The chapter-1 universal machine (`Turing.universal`, `universal_quadratic`, `timed_universal`) is
a bespoke interpreter of about 5,300 lines across `Universal.lean`, `UniversalStartup.lean`,
`UniversalInterpreter.lean` and `UniversalBlock.lean`. It is hard-wired to one work tape, and it
is already copied once: the timed form carries its own private stopped-interpreter layer. B5a
(`briefs/b5a-fill.md`, design §12.11) builds one format-parameterized interpreter instead. That
is a single private step block for one simulated transition of a `k`-tape coded table, whose
per-round cost is independent of `t` and `x`.

**The item:** after B5a lands, re-derive the three chapter-1 statements from that step block, and
delete the bespoke interpreter layers.

**H1 alone does not suffice.** The frozen statements need what B5a's headline does not give:
- **full output:** `universal` computes `M_α(x)`, and `timed_universal` emits `true :: output`,
  whereas H1 answers only `[true]`/`[false]` from a silent output summary;
- **a per-code linear bound with no `|x|` term:** `universal` is `C(α)·(t + 1)` and
  `timed_universal` is `C(α)·(t + 1)²`, whereas H1 is a polynomial in `|α| + |x| + t`;
- **no deadline, and divergence preserved:** `universal` runs until halt, and its converse says
  every completed output of `U` is one of the simulated machine's.

**Route.** Reuse the step block under new hosts. The natural route is H2 above (the per-code
linear timed simulator, with its suffix-input host), plus an emitting variant of the block's
output handling and an unclocked loop host for `universal`. Keep all three statements unchanged;
`UniversalStartup`'s public input pieces (`universalInput_read`/`_move`) are the suffix-input
host's components.

**Governance.** A 12.2c item: its own PR and gate. The chapter-1 statements are frozen, and every
consumer of `universal`/`timed_universal` is re-checked. Prerequisite: the B5a fill (H1's step
block proved). *Origin: B5a design discussion; user, 2026-10-11.*

### SH-1: retire `Nondeterminism`'s private 2B shell onto W2-V (from the fills-4 integration)

`FinTM.exists_certificateShell` (W2-V, `Build/CertShell.lean`) is proved and admission-free. It
is the public form of the private certificate shell that `ClassNP/Nondeterminism.lean` uses for
`ntime_poly_subset_NP` (`cont_choiceVerifier_mem_P`, its loader, `choiceCore`). Design §12.10,
decision 3, names the deduplication as the shell's second customer, a 12.2c item. W2-V's
`certSplitWord` matches `Nondeterminism`'s private `contSplitWord` at 100% and `e3SplitWord` at
90%. This is one four-line `match` term, the output function of the public
`FinTM.computesFunInTime_splitSolve`, and it was pre-disclosed by W2-V's brief
(`audits/fills-4-integration.md`).

**Scope (corrected 2026-10-12, from the 12.2c readiness check).** W2-V's shell serves only
*polynomial* certificate lengths, so only the polynomial use retires. `Nondeterminism`'s NEXP
route keeps its own exponential search: `e3Split` solves `n + C·2^((n+1)^c) = m`, and its loader
reuses `contPairTM`, which embeds `choiceCore`. **The task, as scoped:** re-derive
`cont_choiceVerifier_mem_P` from `exists_certificateShell` and delete `contSplitWord` with it,
which retires the 100% pair. `e3SplitWord`, `contPairTM` and `choiceCore` stay for the
exponential route. Retiring those too would need a width-parametric public shell: a new
statement, with its own gate, and not worth it for the remaining 90% textual match. Statements
stay unchanged. **Prerequisite:** W2-V's own fill gate (the wave-1 fill gate), so that the cited
shell is audited first. The task gets its own PR and gate.

### UNIV-1 (optional): universe-polymorphic `counterLoopTMVia` and `phaseHostTM` (user, 2026-10-12)

*Folds into MIG-0's universe decision (the contract structure's `Type`/`Type*` choice).*

The record-table continuation found that `exists_tableFindTM`, stated for `Γ : Type*`, could
not use its mandated loop: `Turing.counterLoopTMVia` (`Build/CounterLoop.lean`) and
`Turing.phaseHostTM` (`Build/Seam.lean`) take their alphabet in `Type`. The user chose option
(b): `exists_tableFindTM` is restated at `Γ : Type`, a maintainer statement fix with its own
gate (`audits/fills-5-integration.md`). Every consumer's alphabet (`RecSym Q T`, `Bool`) lies in
`Type`. **Option (a), kept here for later:** generalize the two hosts and their run contracts to
`Type*`. That means about a dozen public statements in two gated core files, strictly more general,
with a revision gate and a downstream replay of most of the machine library. The risk is universe
inference in the sigma-typed phase states. The gain is a universe-polymorphic core. Nothing in
the campaign needs it now. If done, `exists_tableFindTM` can be re-generalized to `Type*`
without breaking any consumer. A 12.2c item, its own PR and gate.

### F6-1: promotion and deduplication requests from fills-6 (2026-10-12)

*Origin: the fills-6 deliveries and three read-only reviews (`audits/fills-6-integration.md`).
None blocks a gate; each is picked up when its owning file is next open, or in the dedup
window.*

- **(a) `Nat.bits` shift law.** **Done** by CH34-D4 (`6c7e35bd`): `Turing.bits_two_pow_mul` and
  `bits_two_pow_eq_replicate` in `Encoding` retired `s1b_radius_bits` (`ConfigGraph`) and
  `expcom_bits_two_pow` (`EXPCOM`). Open: the colleague-owned `bits_two_pow`
  (`TimeHierarchy/Separation`), under (j).
- **(b) The Seam space lemma in `Constructible`.** `b3a_seam_space` is a general-configuration
  corollary of the public trajectory theorem `seamCompTM_visitedByTapeHead_ofCfg`, and B3a
  disclosed it as a promotion candidate. **Corrected at the B3a gate (minor 3):** the public
  additive lemmas `seamCompTM_spaceUsedByTape_le_add` and `seamCompTM_spaceUsed_le_add` need a live
  `Cfg.ofWords` endpoint, while `b3a_seam_space` is used at a genuine halt, so citing them is not
  a valid retirement. Promote a general-configuration
  additive corollary, derive the canonical corollaries from it, then replace the private helper.
  `b3a_cfg` is close to `Cfg.ofWords`; define it through `Cfg.ofWords` if the shapes agree (note 8).
- **(c) Canonical bits in `CodeSimulator`.** `canonBits_of_last` and `canonBits_value` overlap
  semantically with `NotTimeConstructible`'s private `ntc_bits_codeBitsNat_append_true` and
  `ntc_codeBitsNat_eq_ofDigits`, and with `UHaltMachine`'s `bits_foldr_bit_one`. One public
  little-endian digit layer (in `Encoding`) would serve all three files.
- **(d) Scan preservation.** `RecordTable`'s `rt_find_scan` overlaps `CfgRecord`'s private
  `recordStep_scan_preserves`. Promote the CfgRecord lemma and cite it at MIG-13.
- **(e) `incFixed` overflow.** **Done** by CH34-D4 (`6c7e35bd`):
  `Turing.incFixed_eq_none_iff_replicate` in `Build/Convention`, from which `expcom_all_true` is
  now derived with its statement unchanged. Open: retiring `MeyerTableau.incFixed_eq_none_iff`
  onto it, under (j).
- **(f) `oracleEmbed_updateTape`** (`OracleSim`): a generic embedding fact; promote it at MIG-16
  (`Build/Embed` is the likely home).
- **(g) Head displacement.** Catalog's `f2_head_steps` is private and retires with MIG-1. Briefs
  should name the public `workTapePos_step_le` instead.
- **(h) A fixed-width prefix reader** (B5a H1's disclosed gap). No row reads a fixed-width,
  undelimited prefix into finite control. H1's `h1RecordTM` does it for one record; a generic
  row may follow if a second consumer appears.
- **(i) Older pairs exposed by the fills-6 combined screen.** OracleSim's `oracleChoiceAction`,
  `oracleChoiceCfg` and `oracleShadowAction` against `Simulation.lean`'s `leftAction`,
  `rightAction` and `rightCfg` (53–75%); `oracleBankCfg_eq` against Loop's `emCall_exit_fixed`
  (56%); `CodeSimulator.guardBlock_orbit` against `Games.playOut_eq_iterate` (74%). No earlier
  population held both sides. **Ruled at the wave-1 fill gate (2026-10-12):**
  - the action and configuration pairs are forced tape-layout specializations, not copies (N11);
  - `oracleBankCfg_eq` is a copy to factor (major F1). **Acknowledged by the user**, with its
    resolution scheduled in MIG-0b: one public R1 reconstruction lemma in `Build/Embed`, at the
    layering split, cited by OracleSim, Loop (`emCall_exit_fixed`'s `hframe`) and CodeSimulator
    (`canonEmbedEq`, F7-1(b)), with the `Primitives` and `CertShell` analogues reconciled then;
  - `guardBlock_orbit` waits for the B5a fill gate.
- **(j) The `incFixed` criterion's two public homes** (from the CH34-D4 factoring,
  `audits/ch34-d4-record.md`). `Build/Convention`'s `incFixed_eq_none_iff_replicate` and
  `CircuitComplexity/MeyerTableau`'s `incFixed_eq_none_iff`, the colleague's original, match at
  100% (93 characters). Retire the second by citing the first in the user's dedup window. Also
  colleague-owned: `TimeHierarchy/Separation`'s private `bits_two_pow` can cite
  `Turing.bits_two_pow_eq_replicate`, and Catalog's `f2_incFixed_cases` goes with MIG-1.
  **Acknowledged (user, 2026-10-12)**, on condition that the retirement stays on this backlog.

### F7-1: promotion, deduplication and style requests from fills-7 (2026-10-12)

*Origin: the fills-7 continuations (`audits/fills-7-integration.md`).*

- **(a) Promote the step block as host H2** (design §14). `h1RoundTM`, `h1Round_effect` and the
  representation `h1RoundRep`, with the whole-record skipper `h1SkipTM` and its successor leaf
  `h1SuccTM`, from `CodeSimulator`'s H1 gap to a public Build module, by PR and gate, **before any
  second consumer is briefed**: B6's `U₀` (RD-3), C1, U-1, EXPCOM. `h1Run_headBound`, the run form
  of `workTapePos_step_le`, goes with it. H1's own assembly may continue on the private copy.
  When both H2 and MIG-0b have landed, the absolute-value head bound becomes a corollary of
  MIG-0b's interval form `workTapePos_runFrom_mem_Icc` in `Finite`, not a second proof (MIG-0b
  round 2, NOTES-r2 §10 item 5).
  **Designed (2026-10-13):** promote as is to `Build/StepBlock.lean` (`Turing.StepBlock`), stated
  in the existing style, with five small additive results (`audits/evidence/h2/H2-design.md`;
  draft `StepBlockDraft.lean.txt`: 0 errors, the seven contracts sorried, 58 of 58 copies
  faithful). The statement gate H2-S is `audits/h2-promotion-pack.md`. **Round 1 (2026-10-13):
  0 blockers / 3 majors / 5 minors, gate open** (`audits/h2-promotion-findings.md`): no copied
  contract is false; `roundTM_iterate` needs the lower bound `t ≤ T`, H5 is a block simulation
  rather than literal lockstep, and the bundle lacked consumer sources. **Round 2 (2026-10-13):**
  `audits/h2-promotion-r2-pack.md`, re-run at `1781a230` (after fills-8). It restates and proves
  `roundTM_iterate` with `t ≤ T`, adds `roundTM_firstExit_unique`, restates H5 as a block
  simulation, and adds the import and move manifests and a fidelity script that fails closed.
  Proposed for H2-M:
  - re-wrap H1's frozen over-long lines and rename the unused binder `hr` to `_hr`
    (α-equivalent, probed);
  - a 56-name public surface, with 15 helpers made private;
  - H1's `h1RoundTime` stays private until MIG-0b's round adapter;
  - the consumer obligation CO-RF is recorded on `U₀` and U-1.

  **Round 2 CLOSED the gate** (2026-10-14: 0 blockers / 0 majors / 8 minors;
  `audits/h2-promotion-r2-findings.md`, resolutions `audits/h2-promotion-r2-resolutions.md`).
  Next: H2-M, the move PR, before any B5a brief.
  **H2-M landed (2026-10-14, PR #88; replay 7 of 7 modules):** `Build/StepBlock.lean` holds the
  121 moved declarations under their round-2 names and the six additives, all proved;
  `CodeSimulator.lean` keeps its 105 staying declarations and its two headline sorries. Eleven
  moved private lemmas with long proofs lack a proof sketch, as they did in `CodeSimulator`: a
  docs-only follow-up.
  The move, H2-M (a
  freeze-checked maintainer PR with an 8-module replay), lands **between** the B5a
  continuations, since both own regions of `CodeSimulator.lean`.
- **(b) The R1 configuration-reconstruction family.** The canonizer continuation's
  `canonEmbedEq` reconstructs an embedded configuration from its selected-bank projections and
  the unchanged ambient frame. That is the argument of `OracleSim.oracleBankCfg_eq` and of the
  local `hframe` in `Loop.emCall_exit_fixed`, the wave-1 gate's major F1. It also has analogues in
  `Primitives` and `CertShell`, per the report. One public lemma in `Build/Embed` serves them all.
  Its scheduling is the wave-1 gate's ruling; this records the new member. **MIG-0b round 2
  (2026-10-13):** `embedEmitCfg_eq`, over `Type*`, also serves `CounterLoop.counter_layout`,
  `CodeSimulator.canonEmbedWords`, `CertShell.cert_embed_words` and MIG-0a's
  `embedEmitCfg_select`. fills-8 added a member, `RecordTable.rt_embed_matches` (4 uses), which
  retires at MIG-13. The silent flavour `CertShell.cert_silent_words` is a **named remaining
  part**, resolved at MIG-14 by a capture-field export and a silent corollary; `embedEmitCfg_eq`
  does not discharge it.
- **(c) The fixed-field record walk.** The two B5a batches both walk a record's fixed fields. The
  overlap was pre-disclosed, and the text screen does not show it. Factor it in the B5a
  completion, or with H2's promotion.
- **(d) Small canonizer promotions:** the strict install-call adapter `canonStrictInstall`, the
  preserving installation `canonPreserveInstall` and the embedded seek `exists_canonSeekOnBank`,
  derived uses of public hosts. Reconcile them with MIG-0b's `ReturnContract` case split (the
  MIG-0a gate's minor 5) rather than promoting them as they are.
- **(e) Style debt, for each owner's next continuation:** H1's 67 Lean linter warnings and 83
  lines over 100 characters; the record tables' 8 lines; the canonizer's 1 line.
- **(f) A frozen canonizer copy (from the B5a canonizer cont3 brief, 2026-10-14):**
  `CodeSimulator`'s private `canonOffset_spec` reproduces `Encoding`'s `length_bits_le_self` in full
  (100% shared text). It became visible once `Encoding` joined the brief's screen population. It
  is in the frozen canonizer region, so it is not touched by cont3: retire it, by citing the
  public lemma, at the canonizer's completion or in MIG-1 F-D's CodeSimulator edit.
- **(g) The canonizer cont3 integration after #94 (2026-10-14).** The H1 landing (#94) moves the
  canonizer's private `canonBits_value` to the public `Turing.foldr_bit_eq_ofDigits` in
  `Build/CounterLoop`. If #94 lands before the cont3 delivery integrates, every citation of
  `canonBits_value` in that delivery is renamed at integration. This is mechanical and done by the
  maintainer. The brief lists it among the frozen privates it may cite.
- **(h) Canonizer cont3 delivered, phase 1 (2026-10-14; `fill-b5a-canon-cont3.zip`, Codex
  `80d32a96`, report `audits/b5a-fill-agent-reports/canon-4-REPORT.md`).**
  - The strip machine `exists_canonStripTM` and the prescribed `computesFunInTime_cond` glue are
    proved. So the headline `exists_polyCanonizer` is proved modulo exactly two private stubs,
    `exists_canonDecider` and `exists_canonGrammarStage`. This is the user's partial rule, checked
    by an axiom walk.
  - A continuation-budget partial with no mathematical obstruction. 18 new privates; no public
    or statement change.
  - It cherry-picks cleanly onto the post-#94 tip, and cites no `canonBits_value`, so (g)'s
    rename is not needed. At the tip it gives 0 errors and three sorry warnings: the two stubs
    and `exists_uniformSimulator`.
  - Duplication: only the pre-disclosed in-file pair (`scan_grammar_guard`/`canonScan_all`, 55%).
  - Integration PR on branch `lean/b5a-canon-cont3`; replay of 8 modules.
  - **Next: a cont4 brief**, phases 2–5 of the report's frontier: the bounded unary reader, the
    record validator, the grammar stage with its fail-fast length bound, the decider on one
    bank, then note 50.
- **(i) The canonizer cont4 brief issued (2026-10-15):** `briefs/b5a-fill-canon-cont4.md`.
  - **Inputs** `46be1104`, on a side branch from `ff4cab18`, merged in `6ee00231`, so the
    worker's base keeps the pre-ship Lean content `c9cc485b`.
  - **Screens:** re-measured with v3, base and overlay 2,576 pairs each.
- **(j) Canonizer cont4 delivered, phase 2 (2026-10-15; `fill-b5a-canon-cont4.zip`, Codex
  `e8bbf4a7`, report `audits/b5a-fill-agent-reports/canon-5-REPORT.md`).**
  - **Proved:** the eight prescribed grammar bridges, the bounded unary reader
    `exists_canonUnaryTM` (C1) and the generic record validator `exists_canonRecordTM` (C2), with
    the recommended statements unchanged. 35 new privates; no public or statement change.
  - **Still open:** the two frozen stubs `exists_canonGrammarStage` and `exists_canonDecider`.
    The headline is proved modulo exactly those two (the delivery's admission walk, re-run at
    the tip).
  - **At the tip** (`CodeSimulator` unchanged since the base; its imports moved with #98–#106):
    0 errors against `oleans-lg24`, and three sorry warnings: the two stubs and
    `exists_uniformSimulator`. The new declarations print the standard axioms only. 0 lint FAILs.
  - **Duplication:** one new in-file pair, `exists_canonStripTM` reproducing `canonPatchWord`
    at 59% (a boundary-split tactic idiom, 134 characters). **User (2026-10-15): factor it in a
    continuation.** The cont5 brief lifts `exists_canonStripTM`'s freeze for that one edit, so
    that it cites `canonPatchWord`. The worker removed two cross-file pairs before delivering.
  - **PR #107** (cherry-picked, authorship kept, plus a comment-only status-text commit);
    replay 9 modules from #106's snapshot.
  - **Landed (2026-10-15, PR #107 as `6354471a`; replay 9 of 9, 0 errors, at the PR head
    `510c87c1`; snapshot `oleans-lcanon4` for the tip `6354471a`).** CodeSimulator keeps its
    three sorry warnings (the two stubs and `exists_uniformSimulator`); the eight downstream
    modules' sorry counts equal #106's replay. The merge differs from the replayed head only in
    records (`backlog.md` and the report).
  - **Next: a cont5 brief**, phases 3–5: the grammar stage, the decider on one bank, then
    note 50; plus the one factoring edit above.
- **(k) The canonizer cont5 brief issued (2026-10-15):** `briefs/b5a-fill-canon-cont5.md`.
  - **Inputs** `596cae56`, on a side branch from `ce418f21`, merged in `a842a356`, so the
    worker's base keeps the pre-ship Lean content `6354471a` (#107 merged).
  - **The factoring edit is prescribed as a patch** (`audits/evidence/b5a-canon-cont5/factor.patch`,
    applied as the worker's first commit). A new private `canonPatchWord_le` (patching a buffered
    word by one at least as long) is cited by the strip machine's copy block and by
    `canonPatchWord`, its equal-width instance. Patched file: 0 errors, the 3 expected sorry
    warnings, no other warning.
  - **Screens** (v3, cont4's 45 files): base 2,648 pairs, patched 2,647. The pair
    `exists_canonStripTM` ← `canonPatchWord` is gone and no pair is new.
  - **Pre-ship:** every inherited probe passes. Note 50 and the headline reach `sorryAx` only
    through the two frozen stubs (the read-only walk). Order list 100 modules; base sorry set 46.
  - **Dispatched (2026-10-15)**: brief attachment SHA-256 `ecf6553c…cac5`, the addendum
    `a25474c5…`; branch `fill/b5a-canon-cont5`; delivery `fill-b5a-canon-cont5.zip`.
  - **Delivered (2026-10-15):** `fill-b5a-canon-cont5.zip`, SHA-256 `52e94a60…4dba0`. Queued for
    the same review sub-agent, after F3.
  - **Reviewed (2026-10-16, screens pending):** ready to integrate as an escalation partial.
    `exists_canonDecider` is proved modulo the open `exists_canonGrammarStage`. Its **E1 is real:**
    the brief's pitfall that the record parser can be the counter-loop body without a wrapper is
    false, since the parser never returns to its entry. The brief's order list also missed
    `ClassNP/TMSAT`.
    - **User (2026-10-16):** cont6 is authorized to use the worker's `phaseHostTM` adapter with a
      fresh anchor (a composition over the phase host, not a new host). The partial lands once
      its screens are clean.
    - **Screens clean** (0 new pairs; one pair removed by the factoring). **Landing PR #113**
      (`lean/b5a-canon-cont5-partial`): the two delivered commits cherry-picked from the bundle,
      plus the status text and the grammar-stage appendix updated for the ruling. Replay
      `replay-lc5p.sh` covers 9 modules (snapshot `oleans-lc5p` from `oleans-lf3p`).

### ARM-1: duplication in the received ARM-extensions code (from the ARM fill gate, 2026-10-14)

*Origin: Hydroxyi's merge `8c23f3bc`, pushed directly to the campaign branch (backlog §2, ARM
extensions); the gate pack `audits/arm-extensions-fill-pack.md`.*

The pack's copy-text screen (MEASURED before the audit) puts the received code past the
one-fifth escalation threshold of `workflow.md` §4: 33 of its 73 files by whole-body share, 14 by
shared text, 8 of them on copies of existing library material alone. Copies of existing
material: 18 declarations disclosed by Hydroxyi and 47 not, 12 of them substantive (mostly
re-derivations of `arm_decides` in `Machines/`); among the new files, 103 internal pairs in 45
families. Disclosure gaps: seven `b4m*` twins (the reply says three); Bridge's four helpers and
Engine's `InputAccess` adaptations, disclosed only in the files; `decChain`, a copy of the
private `arm_increments`, disclosed nowhere. **Needs the user's acknowledgement** before the
ARM fill gate closes. Payback (user, 2026-10-14): a separate PR after the B6 hosts land
promotes the five families Hydroxyi named; the rest is dedup debt for the user's dedup window.
Also found: the copy-text screen labels files by basename and drops cross-file pairs between
same-named files (17 among the new files alone). Whether earlier screens with colliding
basenames in their populations lost pairs is to be checked.
**Checked and fixed (2026-10-14; `audits/evidence/screenfix/`):**
- **The fix:** `audits/evidence/retrofit/copy-text-screen-v2.py` keys files by repository path,
  with `regression-control.sh` as its control. Where all basenames are distinct, its output is
  byte-identical to v1's. **Future briefs and gates use v2**, and any flattened base is re-run
  with v2 before diffing.
- **No recorded result needs a correction.** 7 of 57 past populations had collisions; all were
  unaffected or were run on flattened copies, and ARM's 17 pairs were in the recorded output.
- **Residual, shared by v1 and v2:** two same-named declarations in one file are never
  compared. The one real case is `CfgRecord`'s `Fintype`/`DecidableEq` instance pair at lines
  1249/1255 (66 characters, 100%; s12.8 fill C cont1 recorded 689 → 690 pairs, truly 689 → 692).
  It is accepted as an instance idiom and recorded here. A self-pair keying fix waits for the
  next baseline reset.
- **v3 (2026-10-14; the Diagonal Part 1 gate's minor m2; `audits/evidence/screenfix/v3/`):** the
  residual is fixed. `audits/evidence/retrofit/copy-text-screen-v3.py` identifies a declaration
  by path and source position and skips only the declaration itself. A short name repeated in a
  file is labelled by its namespace-qualified name. Where no file repeats a screened short name,
  the output is byte-identical to v2's. At the tip `ff4cab18` (723 files) the only pair v3 adds is
  the CfgRecord instance pair above, already recorded. **Future briefs and gates use v3**, in
  place of v2.
**Gate round 1 (2026-10-14): 0 blockers, 5 majors, 9 minors; open**
(`audits/arm-extensions-fill-findings.md`). No frozen statement changed and no interface is false.
The majors: the disclosed debt awaits acknowledgement, and D6 (seven `b4m*` twins) and D7 (the
`InputAccess` adaptations) are outside the payback PR; twelve substantive library adaptations
were undisclosed; the internal families (103 pairs) and the same-file overlaps (130 pairs, dropped
by the ledger script) need classifying; and the received machinery is not in the §14 registry
(hosts come first). **User (2026-10-14):** the complete ledger is recounted and classified first,
then acknowledged once, in round 2; the deduplication is the user's own window, coordinated with
Hydroxyi; the received machinery is registered in §14, its first uses an accepted exception, with
a contract gate before any further consumer; the maintainer makes the minor fixes in the new files
in one PR, which the user clears with Hydroxyi.
**Minor fixes landed (2026-10-14, PR #93; replay 74 of 74):** findings 6 (`truth_mem_PSPACE`'s
sketch bound), 10 (the `ClassPSPACE` facade's twelve direct imports) and 11 (42 long lines, 15
headings, two sketches); comments and imports only. Left over: the `SpaceComplexity` facade's two
long Contents lines (into the payback PR, which edits that area); proof sketches for
`numVars_le_length_serialize`, `reflTransGen_stepRel` and `nz_run`; `TQBFHardVerifier`'s Main
results entry for `predB_iff`, which `TQBFHardBridge` declares.
**Dedup decisions, copies of campaign code (user, 2026-10-14).** These go in the payback PR after
the B6 hosts. It changes public statements (D1), so it gets a full gate.
- **D1:** standardize on the existing public `Turing.Cfg.InWindow` (`Build/CfgRecord.lean`).
  Delete ConfigGraph's private `InWindow`, its bridge `inWindow_iff_cfgInWindow`, and Codec's
  `InWin` (`Codec/Word.lean`). The user's fallback for an import cycle is not needed: `CfgRecord`
  is already in `Codec/Word`'s closure (`Word` → `ConfigGraph` → `RecordTable` → `CfgRecord`,
  checked at `6fbdefac`). The two predicates are equivalent but are not the same term (the head
  and cell bounds are grouped differently). So `InWin`'s 48 uses in seven files change
  (`Codec/{Bridge,Checks,Langs,Step,Valid,Word}`, `ExpBFS/Radius`), public statements among them.
  `Radius`'s general window lemmas (`inWin_mono`, `inWin_stepWith`, `inWin_init`) are candidates to
  move next to `Cfg.InWindow`.
- **D2, D2h, D3, D5:** promote ConfigGraph's originals, stated with `Cfg.InWindow`, and delete the
  copies in `Codec/Bridge` and `ExpBFS/Radius`. Delete ConfigGraph's dead private `s1b_*` block in
  the same PR.
- **D4:** promote `CircuitComplexity/DAGCircuitSat`'s Tseitin lemma and delete
  `TQBFHardTseitin`'s copy. Both are Hydroxyi's files, so D4 is cleared with him, as with the ARM
  minor-fix PR.
- **D6:** delete our private `b4m*` appendix of `ClassPSPACE/TQBF.lean` (lines 2474–3185 at
  `6fbdefac`: 45 declarations, 712 lines; corrected from 44 by the round-2 count). It is dead because `TQBF_mem_PSPACE` is now
  `LogProg.TQBFARM.truth_mem_PSPACE`. `TQBFARM/Semantics`' public twins stay.
- **D7 and `decChain`:** one parameterized stride decoder in `Logspace/InputAccess`, with
  `Codec/Engine`'s `decodeStride_loop`, `incChain` and `decChain` as its instances.
- **`length_lbStep`** (private, `TQBFHardParams`): share a helper with
  `PolyTimeBlockLoop.length_xorPairStep_le`.
**Round 2 (2026-10-14).** The complete classified ledger is **acknowledged by the user**
(`audits/evidence/arm-fill/r2/ledger-r2-tables.md`; A4+: 163 declarations, 15.3% of the received
code by shared text). Added to this list by the user: the 15 proposed pairs (13 small copies of
campaign helpers private in `QueryReshape`, `Mult`, CookLevin, `InputAccess`, `QBF` and beside
ConfigGraph's `outSummary_eq_accept_iff`, with `toCNF_extension_iff` riding with D4; the ledger's
§3) and `VWord.getD_drop`, a Bool copy of the public `Programs/Util/List.getD_drop`. The round-2
pack is dispatch folder 21. Its auditor rules whether the scope is complete.
**Round 2 returned (2026-10-14): OPEN, 0 blockers / 2 majors / 6 minors**
(`audits/arm-extensions-fill-r2-findings.md`; resolutions `…-r2-resolutions.md`). The arithmetic
reproduces; findings 6, 7, 10, 12, 13 and 14 close. Majors: two genuine copies were classified
incidental (`arm_reach` inlines `DblLang.Rch.trans`; `halvCount_loop` re-proves `InputAccess`'s
`access_width_half`), and H7–H13 are not yet installed in design §14. **User: remove the two
copies before closure**, by a refactor PR cleared with Hydroxyi (a generic guarded-segment
composition lemma, the seed of K18; the promoted `access_width_half`), presented in round 3. The
maintainer installs the registry rows and the record corrections.
**Clearance with Hydroxyi (user, 2026-10-14).**
- **No consultation needed, only an FYI, for the mechanical edits in his files:**
  - the payback PR's copy deletions and re-points;
  - D1's swap to the equivalent `Cfg.InWindow`;
  - D7, with his public statements kept;
  - the documentation leftovers;
  - round 3's `halvCount_loop`.
- **D4:** a one-time exception to the `CircuitComplexity/*` rule. It covers making
  `DAGCircuitSat`'s private `eval_tseitinGates_values` public (visibility only), in the payback
  PR.
- **`arm_reach` waits for Hydroxyi.** Its removal needs a generic guarded-run composition lemma,
  which is ARM-2's reachability-kit design, so R2-1 stays open on that one copy until he decides,
  or until the user acknowledges it in the meantime.
- **Hydroxyi is consulted on ARM-2.** He is told about H7–H13's gate-before-reuse rule.
**Payback tree built (2026-10-14; `$S/land-payback`, 59/59 at `c52663f1`), and the user's decisions on its
stopped items:**
- **D4 extended:** `DAGCircuitSat`'s second private lemma, `values_getD_eq_of_eval_tseitinGates`,
  is also made public (visibility only), so L024's copy goes.
- **G-pairidx:** a new public `pairEncode_getD_snd` in `InputAccess` replaces L050 and L052.
- **G-rep** (`pt_rep_mul`, whose original is private in `CookLevin/Hardness`) goes to ARM-2 and
  the dedup window, with a home decision.
- **G-vword** (L119/L120) is accepted as not real duplication.
- **Accepted:** the extra deletion of `codec_core_window` via the public
  `Cfg.InWindow.core_bounds`; D7's single `arm_chain` lemma with `bif up`; `drop_canon` keeps
  its name.
- **Final tree (2026-10-14; 60 of 60 at `ff4cab18`, Lean-equal to `c9cc485b`, against `oleans-ltip3`):**
  27 files (23 code, 4 comment-only), +539 −1,549 (net −1,010) lines; replay 119 modules.
  **Landed (2026-10-15,
  PR #101; 60 of 60 at `eb750e63`; replay 119 of 119 from #100's snapshot; snapshot `oleans-lpay`
  for the tip `9c0ae906`).** `DAGCircuitSat`'s edit
  is exactly the two visibility changes. **It lands after MIG-1 S (#98)**, rebased and re-checked
  at that tip, then replayed from S's output. ARM round 3 (folder 25) gated it post-merge: PASS
  (2026-10-15). `arm_reach` stays as acknowledged debt (L066) until ARM-2 (a).
- **ARM round 3 pack built (2026-10-15; folder 25; bundle `b0e9f8f2…f834`, 243 sections).**
  - **Measurements:** 314 pairs at the landed tree, 48 removed and 9 new, all inspected. K+ is 142
    declarations, 13.7% by shared text. No P1/P1+ declaration remains. #98–#102 change nothing in
    the ledger.
  - **User (2026-10-15):** L066 (`arm_reach` ~ `Rch.trans`) is **acknowledged as debt** until
    ARM-2 (a)'s generic guarded-run lemma (designed with Hydroxyi) lands. Round 3 also serves as
    the payback's own gate, post-merge (#101 merged without one, on the maintainer's
    recommendation).
  - **GATE CLOSED 2026-10-15: PASS, 0 blockers / 0 majors / 2 minors**
    (`audits/arm-extensions-fill-r3-findings.md`; resolutions `…-r3-resolutions.md`).
    - R2-1 closes: L049 is paid back, and L066 is acknowledged. Its implementation stays with
      ARM-2 (a), family K18.
    - R2-2 to R2-8 close. The payback's statement gate is discharged post-merge: its 28
      restatements and 20 additions are faithful.
    - The received H7–H13 hosts still need their own contract gates before further consumers.
    - R3-1 (the stale H10/H11 wording in design §14) and R3-2 (L002/L057's original side
      relabelled `drop_len`; it is `drop_bit`) are fixed in the commit that records the gate.

### ARM-2: the ARM layer's internal duplication, to coordinate with Hydroxyi (user, 2026-10-14)

*Origin: the ARM fill gate (ARM-1), groups B and C of the maintainer's duplication summary.*

The user judges a correct fix nontrivial: it needs shared interfaces designed, not mechanical
promotions. So it is to be coordinated with Hydroxyi before any brief, then landed under the zone
rules (a PR plus its gate). Its input is the round-2 classified ledger of the ARM gate.
- **(a) Re-derivations of Hydroxyi's earlier `Machines/` library:**
  - `narm_decides` from `arm_decides` (54%);
  - `narm_decides_poly` from `arm_decides_poly` (90%);
  - `spaceUsedWith_le_of_ranges` from `Compile.spaceUsed_le_of_ranges`;
  - `runFrom_count_eq` from `ConfigCount.coreCode_inj`;
  - `MReach.trans` and `MReach.halt` from `ReachesB.trans` and `AReach.halt` (99%).

  Direction: state the reachability facts once over an arbitrary step relation, and give the ARM
  variants (ARM, NARM, the wide-register forms, MARM) one step-semantics interface. Then a single
  bridge theorem has the nondeterministic and memory-tape bridges as instances, for example
  deriving the nondeterministic bridge from the deterministic one through `detPart`.
- **(b) Duplication inside the new files:**
  - the bank-setup and precondition plumbing: `arm_decides_space`, `marm_dtime` and
    `narm_decides_space` are 76–88% shared with `npre_of_npreS`;
  - the codec layout runs `layout_run` and `layout2_run` (4,139 shared characters);
  - the register-loop blocks of the Savitch, inductive-counting, PATH and TQBF machines (103
    cross-file pairs in 45 families);
  - 130 same-file pairs, for example `ps_tcmp`/`ps_scmp`, `move2_run`/`dmove_run` and
    `parse_run`/`parse_run₂`.

  Direction: a small shared kit, with one bank-setup and precondition lemma, a generic layout run,
  parameterized comparison and transfer loops, and generic endpoint-field comparisons.
- **(c) Finding 12's helper moves** (user, 2026-10-14): `Path.getD_flatMap_rows`,
  `NARMProof.NSPACE.mono_const`, `ARMWidth`'s `LOGSPACE_subset_PSPACE` and
  `SPACE_succ_pow_subset_PSPACE`, and the `Complexity.ExpBFS` / `Complexity.LogProg.ExpBFS`
  namespace split.
- **Scope** (acknowledged, round 2): the ledger's groups A2a (10 declarations) and A2b (119),
  with their families K1–K20.
- **Later:** the run-composition kit is a candidate to unify with `Build/Contract` (MIG-0).

## 2. Campaign work queued or on hold

### MIG / RS: the foundation migration and the restyling backlog (user, 2026-10-12; design §16)

The user lifted the no-retroactive-migration rules for this work and chose scenario B. Duplicate
statement families are retired, with full gates and consumer edits. Restyling is opportunistic:
**pick any row whose prerequisites are met.**

**Schedule (user, 2026-10-16, in answer to a modularity review): interleave MIG items with the
fills, starting with MIG-12 and MIG-4, and add the mirror-pair factoring (MIG-24, below).**
- **The review's evidence** (maintainer, 2026-10-16):
  - `TuringMachine/` has 2,201 private declarations against 1,509 public ones (78 files).
  - In the ten files of #116 alone, the copy-text screen finds 103 pairs, 14 of them at 90% or
    more. Most are left/right or silent/emit siblings: `zoneShiftIn`/`zoneShiftOut`,
    `embedSilentRetTM`/`embedEmitRetTM`, `zonedTape_left`/`_right`,
    `rewind_heads`/`timed_rewind`.
  - There is one cross-file verbatim copy: `canonOffset_spec` (CodeSimulator) repeats
    Encoding's `length_bits_le_self` (100%).
  - MIG-2 to MIG-17 are largely unexecuted.
- **MIG-12 first needs its part of MIG-11.** It depends on MIG-11, of which 9 framed rows have
  contracts so far (`Build/Contract/Catalog`: clear, the two mapped sweeps, walk, skip,
  skip-back, seek-end, seek-start, scan). Its first phase is therefore the contracts of the
  framed rows that `CfgRecord` composes. Under the new definitions-with-lemmas rule, they land
  with their `simps` field equations.
- **MIG-4: closed as done** (user, 2026-10-16; see its row). The proofs were already shared.
- **MIG-12's plan:** `audits/evidence/mig12/DESIGN.md`. The order is #112 merged, then MIG-11a
  (contracts for copy, compare, and the increment and decrement successes, with a public
  `compareStop` for compare's exact time; a maintainer PR and a statement gate), then the MIG-12
  fill brief (swap gate).
- **MIG-11a opened (2026-10-16): PR #117** (`lean/mig11a-row-contracts`).
  - `08bcc57d` on the tip; then `b131d239`, stacked on #116, so #116 merges first.
  - Adds `compareStop` with its lemmas and the exact-time compare (`compareTM_run_ofCfg` is now
    its corollary); `copyTM_contract`, `compareTM_contract`; and `Build/Contract/Counter` with
    `counterRowContract` and the increment and decrement as its instances.
  - Elaboration clean, standard axioms, freeze adds only, lint check 8 unchanged.
  - Evidence `audits/evidence/mig11a/`; pack `audits/mig11a-statements-pack.md`.
  - **The replay passed (user, 2026-10-16):** 86 of 86, sorry counts static-equal. The
    snapshot `oleans-lm11a` is the tip plus #116 plus #117. The screen shows no new copied
    proof.
  - **The statement gate is staged:** `infra_local/gate-dispatches/33-mig11a-statements-gate/`,
    bundle SHA-256 `84d0442f…b99b` (39 sections; Lean `1358ff73`, other `455cb240`).
    **Dispatched (user, 2026-10-16).**
  - **Merged (user, 2026-10-16; `bd1ae147`).** The tip's Lean is #117's `98472df2`.
  - **Gate: PASS, 0/0/2/0, CLOSED (2026-10-16).** `audits/mig11a-statements-{findings,resolutions}.md`.
    Minor 1 (a docstring claimed a width-preserving `fix`) is fixed in `98472df2`, docstring only;
    minor 2 (a stale lint log) is corrected: 0 FAIL, 69 WARN over 79 files at `1358ff73`.
    **Ready to merge at `98472df2`, before #118.**
  - **Follow-up (the review, 2026-10-16):** publish `incFixed_length` (`Build/Convention`) and
    `decFixed_length` (`Build/CounterLoop`, from `counter_dec_spec`), each
    `fix w = some v → v.length = w.length`. Then have the private copies `rt_incFixed_length`
    (`RecordTable`) and `sc_dec_success_width` (`StepClock`) cite them. MIG-12 does not need them,
    because its transport takes the width as a hypothesis. They ride with the next PR that edits
    those files.
- **The briefs' pre-ship inventories (2026-10-16), and PR #118, the brief-inventory API**
  (`lean/brief-api`, `277735f2`, stacked on #117).
  - **The inventories:** U2-S, the F3 continuation, F5 and cont6, measured at the tip (#116's
    Lean). A read-only elaborator lists the definitions in each brief's cited statements; the
    list is crossed with lint check 8 and judged against each route
    (`audits/evidence/brief-api/NOTES.md`).
  - **The gaps it fills:**
    - `bufferedCompTM`, `universalPrefixTM` and `prefixCanonTM` (`k`/`State`), for U2-S;
    - `VirtualTag`, `vhostBuffer`, `vhostBank`, for F5;
    - `RecSym.digitEmb`, `posWidth`, `binDigits`, for F3;
    - `counterLoopBody`, `stateWord`, for cont6;
    - `decFixed`, for #117 and MIG-12.
  - **Checks:** elaboration clean, standard axioms, freeze adds only; check 8 goes 168 → 158.
    Pack `audits/brief-api-pack.md`.
  - **The replay** `replay-lbapi.sh` (311 modules, from `oleans-lm11a`): **passed (user,
    2026-10-16)**, 311 of 311, static-equal (94). The screen of the six files shows 0 new pairs
    (404 declarations, 167 pairs at base and head).
  - **Second commit `36325650`, for the G4 continuation** (2026-10-16). G4's pre-ship inventory
    (the 94 probe names and the 260 published lemmas its route reads) found that the
    contract layer's predicates have no `_iff`: `Round`, `Segment`, `HeadBox`,
    `Cfg.SameOutside`, `Contract.Traj`. The rebalance scan's rounds (two escapes and a head
    relation) cannot come from `Round.of_cut`. Also missing were `roundOrbit_zero`, the hull
    formulas, and `Cfg.bindState`'s fields (`inPhase_post` is stated through it).
    - Added before the gate, following the user's #116 precedent (the zone API, option (a)).
    - Checks clean; check 8 drops 6 more. The two-file screen's 9 new pairs are the
      `variable`-line artifact.
    - **The chained replay `replay-lbapi2.sh` passed (user, 2026-10-16):** 86 of 86,
      static-equal (56). The snapshot `oleans-lbapi2` is the tip plus #118.
    - The head `4ae686be` merges the tip (#117); its Lean differs from the replayed head only in
      #117's corrected docstring.
  - **The gate is staged:** `infra_local/gate-dispatches/34-brief-api-gate/`, bundle SHA-256
    `ea12197a…d6bf` (100 sections; Lean `4ae686be`, other `a2b27243`). **Dispatched (user,
    2026-10-16).**
- **The next briefs, drafted and measured at #118's head (2026-10-16;
  `audits/evidence/drafts/README.md`).** U2-S, F5, the F3 continuation, the canonizer's
  continuation 6 (now a full brief) and **the G4 continuation** (new: it re-points the partial's
  four helpers that unfold `zonedTape`, `zoneSlotOf` and `zoneCapacity`). All pre-ship checks
  pass against `oleans-lbapi2`. Each issues after #118 merges, with its base hash filled.
- **MIG-12's brief, drafted** (`audits/evidence/drafts/mig12-fill-cfgrecord.DRAFT.md`):
  - the swap: `RecordRun` retires onto `Segment`, and the phases become row-contract
    compositions, with every one of the 21 publics frozen;
  - the counter-loop phase stays (MIG-15);
  - order 279, base sorries 83 (none in `CfgRecord`), replay closure 52;
  - the import overlay (adding the contract facade) is clean.
  - **Its inventory found three gaps**, in `SymbolLift` and `Convention`:
    - `Cfg.liftSymbols` had only state and head lemmas;
    - `Action.liftSymbols` had none;
    - `incFixed` had no case lemmas.
  - **MIG-12's API** (branch `lean/mig12-api`, `9872634e`, stacked on #118):
    - the contents: the lifts' fields, `incFixed`'s cases, and `incFixed_length` and
      `decFixed_length` (#117's gate review);
    - checks: clean, standard axioms, freeze adds only, the WARN set unchanged;
    - replay `replay-lm12api.sh`: 160 modules from `oleans-lbapi2`. **Passed (user,
      2026-10-16):** 160 of 160, 0 failed, static-equal (80); snapshot `oleans-lm12api`.
    - #118's gate failed (0/2/1; findings 1–2 are cont6's inventory), so MIG-12's API folds into
      #118's round 2, as planned.
- **#118's gate, round 1: FAIL 0/2/1 (2026-10-16/17;** `audits/brief-api-{findings,resolutions}.md`).
  - **Findings 1–2 (cont6):** `codeSkipRepeat`'s cases; the two round-contract counter loops'
    fields.
  - **Finding 3:** a miscount in NOTES.
  - **The method fix:** the inventory now includes the cited definitions themselves and checks
    structure fields. The review's re-run found **N1**, `Cfg.mapState`'s and
    `Action.mapState`'s fields: the F5 and U2-S drafts cited a private Seam lemma.
  - **Round 2 is prepared locally, not pushed** (`wt-bapi`, `4624fc05`). It fast-forwards to
    MIG-12's API `9872634e`, then adds `88fb25f3` (findings 1–2) and `4624fc05` (N1), the
    review's patches unchanged.
    - Checks are clean.
    - Replay `replay-lbapi3.sh`: 274 modules from `oleans-lm12api`.
    - Pack `audits/brief-api-r2-pack.md`; evidence `audits/evidence/brief-api/r2/`.
    - Drafts updated (cont6, F5, U2-S, F3's Route B note); the staged probes have the new names.
  - **Pushed (user's go-ahead, 2026-10-17):** `lean/brief-api` at `4624fc05`; the PR body is
    updated. **`replay-lbapi3.sh` passed (user):** 274 of 274, static-equal (88); snapshot
    `oleans-lbapi3`.
  - **The r2 gate is staged:** `infra_local/gate-dispatches/35-brief-api-r2-gate/`, bundle SHA-256
    `901e1fa9…c2bd` (108 sections; Lean `4624fc05`, other `00e23bf3`). Not yet dispatched. After
    the merge, the five briefs issue (and MIG-12's).
    - **Packaging waits for #118's gate:** it goes into #118's round 2 if there is one, or
      otherwise becomes its own PR and gate.
- **Lint check 8's blind spot (2026-10-16):** a definition counts as covered when any lemma is
  named after it. `Cfg.liftSymbols` passed on `Cfg.liftSymbols_inputSymbol` alone, without its
  field equations. **Proposed check 8b:** a structure-valued definition needs `simps` or a
  lemma per field. Until then, inventories cross the definitions with their unfolding sites,
  as MIG-12's did.
    - G4's partial helpers that unfold `zonedTape`, `zoneSlotOf` and `zoneCapacity` re-point
      to #116's lemmas in the continuation brief.
  - **Measured for issue (U2-S):** order 91, base sorry set 35 (cross-checked against the
    replays, 0 mismatches), probe 85 names. F5: order 79, sorry set 35. The briefs issue after
    #118 merges.
- **#116 merged (user, 2026-10-16; `d1bf6c99`).** The tip's Lean is `93c4c630`, so its snapshot
  is `oleans-lcapi`. #117 is brought up to date (`1358ff73`, Lean unchanged since its replay) and
  GitHub reports it clean.
- **#116's merge check (2026-10-16):** GitHub showed #116 as conflicting with a stale base
  (`eaedd234`). A local merge was clean. The tip, with records only, was merged into
  `lean/core-api` (`b22e7214`); its Lean content is identical to the gated `93c4c630`, and
  GitHub now reports clean.
- **Not adopted** (user, 2026-10-16): a systematic promotion pass at each landing, and a public
  one-step leaf row. Policy's existing route stays: a private copy plus a requested shared
  lemma, promoted at a shared-file window.
- **Adopted with it:** *definitions land with their lemmas* (`policy.md` §1; lint check 8,
  `b19ab034`). At the tip, check 8 lists 205 public definitions in 50 `TuringMachine/` files,
  and 1,173 in 254 files of `TCSlib/Complexity`, that predate the rule. #112 and #116 cover part
  of that list. The rest is covered as consumers need it. The estimates come from seven read-only reviews
(design §16), in lines, and are ESTIMATED unless marked; negative means saved.

**Gates:**
- **swap:** statements are unchanged, so a freeze check, a replay and a fidelity gate;
- **stmt:** new public statements, so a statement gate;
- **full:** retired or changed statements, so a full gate, with the consumers edited in the same PR.

**MIG: the foundation, in this order.**

| ID | Scope | Action | Estimate | Needs | Gate | Notes |
|---|---|---|---|---|---|---|
| MIG-0 | new `Build/Contract.lean` | Item 0, with the §16 requirements: the contract structure, tape frames and `.keep`, composition theorems as thin wrappers over the existing public rows, and tactics | +1.5k to +2.5k (MEASURED after MIG-0b round 2: about +3.2k, MIG-0a 1,101 lines and MIG-0b net +2,084 over 17 files; round-2 minor 1) | — | stmt | first; unlocks MIG-11 to MIG-17 and RS. **Statement draft fit-tested** (design §16a; user, 2026-10-12: universe `Type`, frames a derived layer). Two increments: MIG-0a (the structure, frames, `trans`, `seq`, `inPhase`, `embed`, `branch`, `release`, and two additive exports in Embed and Seam; gate round 1: 0/1/5, round 2 closed 0/0/1, landed by PR #83), then MIG-0b (gate round 1, 2026-10-13: 0/2/4; round 2 CLOSED 2026-10-14, 0/0/3, `audits/mig0b-r2-findings.md`; next its landing PR, without part 7, the alphabet pair, which lands with RS-5), revised after that round (design §16a): the segment, round and joint-trajectory layers, the layering split, the release export, the lift, the counter loop, renaming, the alphabet-reduction and robustness adapters, the tactics |
| MIG-1 | `Build/Catalog` (the `f2_` region, about lines 1785–11365), `Primitives`, `Composition`, `Loop`, `Wrappers`, `Encoding`, `Simulation`, `ClassP/TimeConstructible` | Named witnesses (about 30 defs with spec theorems) for the 66 existential rows; then delete the 304 `f2_` copies (6,255 of their lines are verbatim, MEASURED). The 22 space rows become corollaries. Retire the R3 canonical `_run` rows (0 external consumers) | −7.6k to −8.3k, +0.4k | decision 12.2 lifted | stmt + full | highest confidence; half the saving. **Drafted (2026-10-13):** `audits/evidence/mig1/` (design, measured inventory, statement draft: 0 errors, 26 sorries). Measured at `6aa9f67b`: 53 existential rows, not 66 (plus `timeConstructible_id`, hidden in a definition); 304 copies, of which 232 are code-identical to a home declaration (4,351 lines; the 6,255 is not reproduced); 20 of the 22 region publics are space rows, the other two head lemmas; the R3 `_run` rows have 5 citations in 2 files (`CertShell`, `CodeSimulator`), not 0. Net about −7.4k (ESTIMATE). Spec theorems in the existing style, not `Contract` instances (layering: the landed `Contract.lean` imports `Catalog`; MIG-0b's split removes that obstacle, and the decision rests on the rows' shape and the order of work). **Answered (user, 2026-10-13): all four as recommended**: the R3 retirement in MIG-1's last PR, after the B5a continuation integrates (else five rows, leaving `copyTM_run`); both consolidations; the space rows stay in Catalog as corollaries; MIG-17's named loop hosts are done by MIG-1. **Statement gate (2026-10-14):** `audits/mig1-statements-pack.md`. It covers the 26 witnesses with their real bodies, 45 new public statements (14 proved), the 55 rows as `type_of%` corollaries (all proved), and the deletion plan for 378 declarations. Net about −7.0k lines (ESTIMATE). **Round 1 (2026-10-14): 0 blockers, 1 major, 3 minors; open** (`audits/mig1-statements-findings.md`). No public statement is false and no witness body differs from its source. The major is in the deletion plan: it retargets the extended loop contract's preparation step at Loop's private `loopHost_prepare`, which lacks the fuel-head clause (`∀ i, -T ≤ c.workTapePos i ≤ T`) that the contract passes to its head lemma. The repair strengthens `loopHost_prepare` in F-C, and is shown by elaborating the moved contract against the surviving home lemmas. The minors: the evidence runner masks failures, the bundle lacks inputs its reproduction names, three pack sentences overstate. **Open questions answered (user, 2026-10-14): all five as recommended**: the decision-loop S-form family is dropped (its 14 `a2_` lemmas deleted); the eight citation specs are proved at S (the three split specs stay dependent on F-C's loop specs); the run head bound has one proof, MIG-0b's `workTapePos_runFrom_mem_Icc` in `Finite`, with H2's absolute form a corollary beside it; Simulation imports `Mathlib.Algebra.BigOperators.Fin` and homes `ComputesInTime.spaceUsed_le`. **Round 2 CLOSED** (2026-10-14: 0 blockers / 0 majors / 3 minors; `audits/mig1-statements-r2-findings.md`, resolutions `audits/mig1-statements-r2-resolutions.md`): the strengthened `loopHost_prepare` and the overlay over surviving home lemmas repair finding 1; the minors are runner and checker strength and one accessibility description, recorded for S and F-C. Next: stage S, unblocked now that the B6 hosts landed (#92, 2026-10-14; both edit `Encoding.lean`), re-measured at its base, with MIG-0b's interval lemma as the head bound. **The rule "F-D before the next B5a brief" is lifted** (user, 2026-10-14): B5a's canonizer continuation goes first, and F-D's one CodeSimulator site rebases onto it; B5a's H1 continuation follows the C1 H1-harvest landing (user: harvest first). **Stage S built (2026-10-14; `$S/land-mig1s`, 51 of 51 checks, at `3a6e89f4`):** 25 witnesses (15 public in place, 10 new), 42 statements (25 proved, 17 sorried), 67 public names (70 with F-B's 3), 191 asserted renames; no row's statement or proof changes; replay about 306 modules. The head lemma is untouched: StepBlock's `abs_workTapePos_runFrom_sub_le` keeps its own proof, and its re-proof as a corollary of `workTapePos_runFrom_mem_Icc` is for H2/MIG-0b's owners. **User (2026-10-14): a cleanup pass in S's PR**: drop the gated docstrings' stale "(landing: …)" notes, update the module docstrings for the new names and the moved head lemmas, remove 3 unused `simp` arguments, accept two whitespace wraps. Its PR follows #94 (H1), so the replays chain. Carried: F-D gains 2 docstring sites; `exists_codeTM_spaceUsed` (added by #92, a 54th existential row) becomes a corollary of a `toCodeTM_spaceUsed` spec at F-A. **PR #98 (2026-10-14):** rebuilt at the merged tip `c9cc485b` against `oleans-ltip3`, 54 of 54 checks. Three checks that were pinned to the first base now take the run's base and snapshot commit: the merges list, the snapshot's build commit, and the CodeSimulator R3 site's line, which #94/#96 moved from 1282 to 1275 (still one site). Replay 307 modules. It merges first; Diagonal Part 1 and the dedup payback rebase on it, one after the other (their replay lists share 4 facades). **Merged (2026-10-15, `eb750e63`; replay 307 of 307, sorry warnings 80 + the 17 sorried specs; snapshot `oleans-lmig1s`).** Next for MIG-1: the fill batches F-A to F-D |
| MIG-2 | `TuringMachine/Universal` (195–1316, 1317–1606, 2367–2644) | Retire the duplicate timed layer (`timedCut*`, `timedPrefix`, `timedCapture`), through a stop-before variant or proofs parametric in the table | about −1k | — | swap | `timed_universal_concrete`'s coefficient must not grow (TMSAT); **merged with U-1** (one re-derivation, from both directions) |
| MIG-3 | `Robustness/SingleTape` | `one_work_tape` reuses `dg_all_inputs`; drop the `sweep_*` chain | about −450 | — | swap | |
| MIG-4 | `Build/CounterLoop` | R80B-E1: `counterLoopTM` becomes the identity instance of `counterLoopTMVia`; retire the duplicated statements | about −450 | — | full | **Closed as done (user, 2026-10-16).** R8.0b had already derived `counterLoopTM_run_done`/`_run_escape` from `counterLoopTMVia`'s through the 94-line bridge `counter_refl_agree`. What remains is the two definitions and the two corollaries; `counterLoopTM` has about 70 uses in 10 files (not 14 in one). Kept as is |
| MIG-5 | `Build/EmitIterBody`, `Build/EmitIterEmbed` | Cite `inputCopyTM_run_ofCfg` and the rewinds (223 re-proved lines); derive `padAction`/`embedCfg` from Embed and retire them | −300 to −420 | — | full | CH7-D2; 1 external consumer |
| MIG-6 | `TuringMachine/Encoding`, `Codes2Tape` | Parameterize by tape count; retire the mirror | about −180 | — | full | CH34-D2; 4 external consumers |
| MIG-7 | `TuringMachine/UniversalStartup` | `universalCaptureTM` onto Embed's `embedSilentTM` | about −130 | — | swap | |
| MIG-8 | `ClassNP/Nondeterminism` | Retire the unreferenced `e3_split_of_body` chain (2652–2780) and `a3n_prevalidation`; merge the polynomial and exponential duplicates (about 165 lines) | about −300 | **check against SH-1 first** (SH-1 keeps the NEXP `e3Split` route) | swap / full | |
| MIG-9 | `Build/InputLength`, `ClassP/TimeConstructible` `counterTM`, Loop's `loopDebit` | One canonical bit-length counter | about −200 beyond MIG-1 | MIG-1 | full | |
| MIG-10 | `Diagonalization/Relativization` (341–406) | Promote the oracle relabel transport to the library, as its docstring suggests | −60 to −110 | — | stmt | |
| MIG-11 | the framed Build rows | Contract instances of about 25 framed rows | +0.3k to +0.5k | MIG-0 | stmt | grow the tactics against MIG-12 |
| MIG-12 | `Build/CfgRecord` | Rebase on the Contract; the private `RecordRun` (76 uses) becomes MIG-0b's segment layer, with same-machine concatenation. **Corrected (MIG-0a gate, round 1, major):** `Contract.seq` does not replace it, since it changes the machine and adds a dispatch step, and a segment's endpoint need not be a first exit | −1.6k to −2.1k | MIG-0b, MIG-11 | swap | best ratio of saving to lines touched |
| MIG-13 | `Build/RecordTable` | Rebase; `rt_copy_seam` retires; write any still-open rows in the new style. The find round (`rt_find_round_entry`, return or escape) needs MIG-0b's round layer | −350 to −550 | MIG-0b | swap | |
| MIG-14 | `Build/CertShell`, `Build/InputCall` | Rebase | about −560 | MIG-0 | swap | |
| MIG-15 | `Build/CounterLoop` | `counterSpan`, a segment property that admits time zero, becomes MIG-0b's segment layer with a joint-trajectory relation; the loop body's interface uses the round layer. **Corrected (MIG-0a gate, round 1, major; round 2, minor 1):** per-tape intervals cannot carry its head-vector relation, and a `ReturnContract` excludes the escaping round. **MIG-0b round 2:** `counterLoopOrbit` becomes an abbreviation of `roundOrbit` at MIG-0b; the compatibility name stays, and its four consumer edits land with MIG-0b | −440 to −640 | MIG-0b, MIG-4 | swap | |
| MIG-16 | `Build/OracleSim` | Rebase on the R1 contracts | −250 to −400 | MIG-0 | swap | exact lockstep lemmas stay |
| MIG-17 | `Build/Primitives`, `Build/Loop` | Named loop hosts (done by MIG-1; user, 2026-10-13); `splitSafe` (private in `Build/Primitives`, avoidance through the endpoint) becomes MIG-0b's `SafeSegment`, and `SafeRun` (`Build/EmitIterEmbed.lean`, avoidance strictly before the endpoint) a `Segment`; first-exit Contracts only where a first exit is proved (MIG-0a gate, round 2, minor 1; locations from the MIG-0b draft). `Loop` must import the core contract module, so MIG-0b's layering split comes first | −1k to −2k | MIG-0b, MIG-1 | swap | 15 external files cite the P-rows (statements kept) |
| MIG-19 | `SpaceComplexity/ConfigGraph` (S1b's delivery) | **Closed 2026-10-14 (moot):** the three are proved (`ExpTime.lean`, ARM route, design §14 H12); S1b's private block is deleted by the payback PR (§1 ARM-1). *Was:* Re-derive `NSPACE ⊆ DTIME(2^O(S))`, `NL ⊆ P` and Ex 4.3 as programs (design §16, decision 3); retire S1b's private BFS host | S1b's delivery added 333 lines (612 → 945, MEASURED); the program's own cost is estimated with stage 2 | stage 2, machine-configuration routines | swap | user, 2026-10-12: S1b finished first, then stopped as a partial (fills-6): the two corollaries are proved modulo `NSPACE_subset_exp_dtime` only, so this row needs the simulation alone |
| MIG-20 | the chapter-2 emitter files (`emitterCompare*`, `emitterP2Erase*`) | 12.2c item 3 (F25a/F27a): onto `compareTM` and `clearTM` | small | MIG-1 (the Catalog→Primitives import) | swap | |
| MIG-21 | `CookLevin/Hardness` (`clPlacement`, the selectors) | 12.2c item 13: restate the layouts as plain `Fin k ↪ Fin l` embeddings; delete the selector layer (about 120–259 lines) | about −150 to −250 | the T2a gate (item 6's export) | swap | Hardness stays at machine level |
| MIG-22 | `ClassPSPACE/TQBF` (B4 membership's delivery) | **Closed 2026-10-14 (moot):** `TQBF_mem_PSPACE` is `LogProg.TQBFARM.truth_mem_PSPACE`; the pure core is deleted with the `b4m*` appendix (D6). The general AND/OR evaluator stays registry H1. *Was:* `TQBF_mem_PSPACE` as a program: a recursive QBF evaluator in the §15 language, compiled through stage 2, with the proved pure core (`b4mValue`, `b4mValue_truth`, `b4mWalk_value`) as its specification. Retire the unused leaf-contract definitions, which lack an input/records precondition | to be estimated with stage 2's space accounting | stage 2 with a space bound, the input extensions (§15a) | stmt + swap | user, 2026-10-12: "Stop; do it as a program". Registry H1, the AND/OR evaluator (design §14) |
| MIG-23 | `Build/RecordTable` rows 15, 16, 19, 20 (find, append, validity, next) | Paused, with no consumer since S1b stopped and Savitch moved to the language. Retire them under scenario B unless stage 2's memory design or another consumer claims them; keep the proved find round (`rt_findRound` and its contracts) | small (statements only) | a consumer decision | full | user, 2026-10-12: "Narrow to rows 17–18"; rows 17–18 continue for B6's window route |
| MIG-24 | the mirror and sibling pairs: `Build/Zone` (`zoneShiftIn`/`Out`'s lifting skeleton), `Build/ZoneTape` (`zonedTape_left`/`_right`, `_left_sep`/`_right_sep`, `zoneOwner_sep`/`_beyond`), `Build/Embed` (the silent/emit transports, their steps and return forms), `Simulation` (`leftCfg_step`/`rightCfg_step`, `rewind_heads`/`timed_rewind`), `Encoding` (`pairDiag_double`/`_copy`; `exists_codeTM_spaceUsed`); one cross-file copy (`canonOffset_spec` onto `length_bits_le_self`) | Derive one sibling from the other through a symmetry (as `zoneCascadeLeft` through `ZoneContents.swap`), or state one side- or flavour-parametric form with the two as instances. Statements are kept where consumers cite them. The vendored `Configuration`/`Deterministic` pairs are excluded | ESTIMATED small (hundreds of lines); a library-wide screen measures the full list first | — | swap where statements are kept; full where a sibling retires | user, 2026-10-16: added to the schedule |
| MIG-18 | port of [AFM26]'s `Util/Asymptotics` (1,769 lines upstream) | `Dominated`, `Scale.SoftO` and the `growth` tactic, then ledgers without constants | +0.5k to +1.4k; saves part of about 3.5k ledger lines | the PROG-1 port tooling | fidelity, then swap | payoff mostly in ClassNP, ClassP, SpaceComplexity and PolyHierarchy |

**RS: the restyling backlog, opportunistic; chip away at it.**

| ID | Scope | Action | Estimate | Needs | Gate | Notes |
|---|---|---|---|---|---|---|
| RS-1 | `Universal`, `UniversalInterpreter`, `UniversalBlock`, `UniversalStartup` | Contracts with exact time, cut and positive duration | −0.8k to −1k after MIG-2 and MIG-7 | MIG-0 | swap | 0 Build combinators used today (MEASURED) |
| RS-2 | `TuringMachine/CodeSimulator` | The counter-loop rule absorbs the guard ledgers; its open rows go in the new style | −60 to −130 | MIG-0 | swap | |
| RS-3 | `Robustness/SingleTape` | `DGSpan` becomes a MIG-0b `Segment` (a segment property, not a first-exit contract; MIG-0b draft); the sweep framing | −400 to −570 beyond MIG-3 | MIG-0 | swap | the visited-set space ledger stays |
| RS-4 | `Robustness/Oblivious*` (5 files) | A decoration-lift rule and frames for `prepInvariant_step` | −450 to −650 | MIG-0, lockstep combinators | swap | the schedule must stay one input-insensitive table |
| RS-5 | `Robustness/AlphabetReduction`, `Bidirectional` | Per-phase head envelopes; and prove `FinTM.exists_alphabetReduction_lockstep` (admitted in MIG-0b) in `AlphabetReduction`, against `arTM`, `arCfg` and `arCfg_cycle`, with the intermediate-control lemma (80–150 lines, ESTIMATE) | −100 to −250 | MIG-0 | swap | |
| RS-6 | `ClassNP/Nondeterminism` | `b2Host` phases onto contracts | −500 to −900 | the Contract's nondeterministic variant | swap | exact choice-word splits are load-bearing |
| RS-7 | `TimeHierarchy/*` (ClockLoop, ClockMachine, CodePrefix, Diagonal, Separation) | Re-base the clock and prefix machines on CounterLoop, Scan, Embed and Seam; ledgers through MIG-18 | −200 to −320, more if re-based | MIG-0, MIG-18 | swap | the Meyer files use the counter lemmas: keep them |
| RS-8 | `Diagonalization/*` | Ledgers through the asymptotics calculus | −50 to −100 | MIG-18 | swap | |
| RS-9 | `TuringMachine/MathlibBridge` | Frames for the stack store | −90 to −150 | MIG-0 | swap | |
| RS-10 | `Oracle`, `OracleAgreement`, `OracleFinite`, `OracleNondeterministic`, `Build/OracleCall` | An oracle Contract adapter | −50 to −100 | MIG-0, oracle variant | swap | run-equality transfers stay |
| — | `CodeParser`, `CodeFormat`, the proved part of `Build/Zone`, `Codes2Tape` beyond MIG-6 | nothing to restyle (MEASURED) | 0 | | | |

Colleague-owned machine files (`SpaceComplexity/Machines/*`, `CounterProg*`, the CircuitComplexity
machines) are outside MIG/RS. Their deduplication is the maintainer's 12.2c window.
`Build/Zone.lean`'s module header is stale (it says every contract is sorried, but 38 of 40 are
proved); fix it in the first MIG PR that touches Build.

* **PROG-1: the vendored programming layer's follow-ups** (from the [AFM26] port, 2026-10-12;
  design §15b).
  - (a) Port the sieve (`Light/Lib/Sieve`), once a Mathlib bump provides `Nat.primesLE`, or with
    a local definition.
  - (b) At every Lean or Mathlib bump, remove the names in `TCSlib/Programs/Compat.lean` that the
    bump provides, and revisit the `with_unfolding_none` to `with_reducible` swap.
  - (c) The extensions are a statement phase with its gate: reading the input in place, `emit`, and
    the coin stream for nondeterminism and randomization. **Semantics decided** (user,
    2026-10-12; design §15c): now **PROG-2**.
  - (d) Stage 2, the RAM-to-`FinTM` simulation.
  - (e) Port upstream's `Lang/Renumber.lean` and `Machine/Footprint.lean` when the extensions or
    stage 2 need them (fidelity gate, finding 3). Both are generic, and outside the vendored
    closure.

* **PROG-2: the extension edit set** (user, 2026-10-12; design §15c). All four extensions in one
  scripted vendored edit set:
  - `inBit`/`inLen` with a RAM `rdIn` (`len` only if needed);
  - `emit`, with an append-only output;
  - read-once coins (`coin x`);
  - `half`, as a statement and a RAM shift.

  I/O and coins become indices of `Exec`, so `Ends`, `Meets` and the routines are unchanged; a new
  `EndsIO` sees them. Also part of the set:
  - the `Exec` determinism lemma, which randomized acceptance needs;
  - `Fits`'s input-length clause;
  - an update to `ComputationalModels.lean`'s instruction-count docstring.

  **Estimate:** 600–1,000 vendored lines, by `scripts/vendor_afm26/`, plus 700–1,150 new.
  **Gate:** a fidelity check of the vendored edits, then a statement gate for the new rules.
  **Obligation from the stage-2 gate (F3):** the edited compiler must supply `1 ≤ lim.word` at the
  existing simulation calls (`Compiler/Simulation.lean:277`, `:356`), as an invariant or a
  premise; it does not follow from `input_le`.

* **PROG-3: memory footprint along a run** (from the PROG-2 survey; design §15c, obstacle 1).
  `compileProgram_correct` describes only the final memory. Stage 2's space bound needs every
  intermediate memory inside `[-lowCell, lim.space)`. Close it with a stronger `Steps` or by
  porting `Machine/Footprint.lean` (PROG-1(e)). It is a prerequisite for stage 2's space bound,
  and so for L, Savitch and PSPACE through programs, and for C2's log-space programs (design
  §16b item 4).

* **PROG-4: stage 2's statement requirements** (user, 2026-10-12; design §16b items 1 and 4).
  Stage 2 (PROG-1(d)) is drafted together with PROG-2 and PROG-3, and its statement carries:
  - **a computed word size:** `W` is a function of the input length that the compiled machine
    computes within its space bound (`c·log n` for P and L, `c·S(n)` for Savitch);
  - **deterministic and nondeterministic forms:** each `coin` one `FinNDTM` choice step, with
    bounds uniform over the coin streams;
  - **a logspace grade:** `O(1)` cells and `W = O(log n)` give space `O(log n)`.

  **Gate:** a statement gate, before any fill. **Drafted (2026-10-12; design §15d):** the
  statement drafts and notes are in `audits/evidence/stage2/`. **Answered (user, 2026-10-12):**
  all four as recommended (design §15d). **Statement gate (2026-10-13):**
  `audits/stage2-statements-pack.md`, covering PROG-2 (as a specification mirror), PROG-3 and
  PROG-4. **Gate CLOSED** (round 1, 2026-10-14: 0 blockers / 0 majors / 4 minors;
  `audits/stage2-statements-findings.md`, resolutions `audits/stage2-statements-resolutions.md`).
  No theorem is false; the homes, the namespace and `initMem` are approved. Next: the landing PR
  (parts A, C, D, E and the slice lemmas), then PROG-2's scripted edit and its fidelity gate.
  **Landed** (PR #86). **Paused (user, 2026-10-14):** the ARM merge proves PSPACE = NPSPACE,
  `PATH ∈ NL` and NL = coNL, the customers of the coin programs and of Savitch at polynomial
  space; general `savitch` stays sorried. No stage-2 brief (PROG-2's edit and fidelity gate,
  PROG-4's fills) is written until the user resumes it.

The route decisions of 2026-10-12 (design §16b) add three work items, numbered by §16b's items
(items 1 and 4 are PROG-4):

* **RD-2: restate B4a in place over H6** (§16b item 2). Public definitions of the codec and its
  three CNFs (`TQBF.lean`), with closed-form variable indexing designed with the
  machine-to-formula kit H6 (design §14), and theorems in place of `exists_adjacency_codec_cnf`'s
  `∃`. A statement gate, then a re-fill. Also needed for `TQBF_PSPACEHard`: Tseitin on
  `Std.Sat.CNF ℕ`, correct for every prefix assignment. Open with it: whether the `ψᵢ` emitter is
  a machine or a program with `emit`. **Designed (2026-10-12):** `audits/evidence/rd2/` (design
  note and statement draft; design §16b item 2). **Answered (user, 2026-10-12):** all five as
  recommended; in particular, the old existential is retired and the emitter is a machine.
  **Statement gate (2026-10-13):** `audits/rd2-statements-pack.md`. **CLOSED** (round 1,
  2026-10-14: PASS, 0 blockers / 0 majors / 2 minors; `audits/rd2-statements-findings.md`,
  resolutions `audits/rd2-statements-resolutions.md`). Next: the landing PR (with minor 1's sketch
  fix), then the semantic re-fill (RD-2a) and the uniformity fill (RD-2b). `fragment_append`
  joins the Cook–Levin re-basing family (minor 2).
  **Landed** (PR #85). **Fills held (user, 2026-10-14):** the ARM merge proves `TQBF_PSPACEHard`
  without `ConfigCodec` or `FormulaKit`, which now have no consumer. The RD-2a/b briefs are
  drafted (the maintainer re-ran their six pre-ship probes: 0 errors) but not committed or
  dispatched; their base data predates the ARM merge's `TQBF.lean` changes, so it is
  regenerated if they go ahead. The user's four answers on them (2026-10-14, all as
  recommended): integrate partials; delete the two unusable KEEP rows as a disclosed deviation;
  `Mathlib.Data.List.MinMax` in `Gate.lean`; `CfgRecord`'s docstring is the maintainer's.
* **RD-3: re-route B6 and restate `space_universal` forward-only** (§16b item 3).
  `SpaceComplexity/Hierarchy.lean`: `space_universal` keeps only its forward clause ([AB09]
  Exercise 4.1), and `space_hierarchy`'s sketch moves to the window route (a self-simulating
  universal `U₀` under a configuration-count clock), dropping the proved normal-form obligation.
  A statement gate. The fill needs H2, H3 and H5. **Gate passed (2026-10-13, 0/0/4;
  `audits/b6-restatement-findings.md`, resolutions `audits/b6-restatement-resolutions.md`).** **Host
  statements drafted (2026-10-13):** `audits/evidence/b6hosts/`: H3 with its step clock, H5, `U₀`
  and the bridges. The draft has 0 errors and 10 sorried contracts; everything else is proved,
  including the two former fill obligations (`exists_codeTM`'s space clause, a decider's space
  bound at every time). **Answered (user, 2026-10-13), all five as recommended:** `space_universal`
  is strengthened to `C·s` in the B6 hosts' pack, through H5's ruler device; no binary-position
  device; the public summary tag lands in `ConfigGraph`, with S1b's private copies re-pointed in
  the same PR; the configuration-count runner goes to a new `SpaceComplexity/WindowClock.lean`, so
  that `Build` never imports `SpaceComplexity` (the maintainer's recommendation, not the
  drafter's); `∃` statements now, named machines at fill. **Statement gate (2026-10-13):**
  `audits/b6-hosts-statements-pack.md`. **CLOSED** (round 1, 2026-10-14: PASS, 0 blockers / 0 majors
  / 5 minors; `audits/b6-hosts-statements-findings.md`, resolutions
  `audits/b6-hosts-statements-resolutions.md`). It covers eleven parts: five new modules and
  additions to six existing files. The unit has 0 errors, its 10 contracts are sorried, and
  `space_universal` is strengthened to `C·s`. The step clock's trajectory clause is strengthened to
  carry the tapes, the input position and the output; C1's form `exists_stepClockTM` is unchanged.
  **Landed (2026-10-14, PR #92; replay 270 of 270):** regenerated from the gated unit at
  `13a16a69`, with the five fixes; `SelfUniversal` keeps the gated `CodeSimulator` import. The
  first replay attempt failed on a missing Mathlib link in the new PR worktree (maintainer
  error, now prechecked). Follow-up, a small PR of its own: switch that import to
  `Build.StepBlock` and re-point `exists_selfStartupTM`'s citation of
  `Turing.oneTapeMachineFormat.serialize_eq`. Next: the B6 fill briefs for the ten contracts,
  with record-table row 18.
  **B6 fill plan (2026-10-14; `audits/evidence/b6-fill/B6-fill-plan.md`).**
  - **Six batches:**
    - F1: StepClock, `exists_stepClockTMVia`, which also serves C1;
    - F2: WindowRun, the two window rows;
    - F3: WindowClock, briefed by Route A after F1 integrates;
    - F4: SelfUniversal;
    - F5: InputDevice, the three ruler rows;
    - F6: `space_universal`.
  - **Later, H,** the headline region of `Hierarchy`.
  - **Critical path to `space_hierarchy`:** F1 → F2 → F3 → H, with F4 alongside.
  - **User (2026-10-15), the remaining batches:**
    - **F4** (`U₀`) is the `k = 1` case of U2's statements (#102). Brief H2-F
      (`StepBlock.exists_forwardLoopTM`) next, then U2-S and U2-U; `U₀` follows as their `k = 1`
      corollaries (the U2 design's decision (a)).
    - **Imports** (fill plan decisions 3 and 4): each brief authorizes exactly its imports as the
      worker's first edit. F5: `Build/Contract/Basic` and `Build/Seam` in `InputDevice`. F6 and H:
      the union, with H after F6 integrates.
  - **Briefs `b6-fill-stepclock.md` (F1) and `b6-fill-windowrun.md` (F2) are issued.**
  - **Dedup, for the dedup window:** the public `wordPatch` has the same definition as
    `CounterLoop`'s private `counterPatch`, which the screen misses. `counter_debit` retires onto
    F1's `sc_debit` once that is promoted.
  - **F1 stopped on escalation E1 and is re-briefed (2026-10-14):** the route needed `CounterLoop`
    privates and unfoldings that v1's rule 10 forbade (report
    `audits/b6-fill-agent-reports/stepclock-1-REPORT.md`). Per the user's decision, brief v2
    (`briefs/b6-fill-stepclock-v2.md`) authorizes exactly 19 promotions (3 visibility-only, 16 new
    lemmas in `CounterLoop` and `SymbolLift`). It ships a route probe that discharges every route
    seam from public names (0 errors, exactly the 3 fill stubs sorried), with a static scan for
    private citations and unfoldings. F2 is re-dispatched unchanged with the environment addendum.
    - **Two more items for the dedup window,** in the family above: `sc_wordPatch_twice` and
      `sc_wordPatch_frame` prove for `wordPatch` what the private `counter_patch_twice` and
      `counter_patch_frame` prove for `counterPatch`. `sc_dec_inputPos` overlaps `Build/StepBlock`'s
      `Bool`-only `inputPos_runFrom_of_inputTape_eq_zero`; one generic lemma in `Simulation` would
      serve both. None makes a screen pair.
  - **F2 delivered (2026-10-15, `fill-b6-windowrun copy.zip`, SHA-256 `2cb4bfb6…d29f`; Codex
    `e260585d`; reports `audits/b6-fill-agent-reports/windowrun-1-REPORT.md` (the first attempt,
    stopped on the environment before the addendum) and `windowrun-2-REPORT.md`):
    **both targets proved.** `exists_windowLoopTM` uses only the standard axioms;
    `exists_windowRunnerTM` adds `sorryAx` only through `exists_stepClockTMVia` (F1, in flight),
    by the worker's direct-admission walk. 25 new privates, none public; prescribed machines
    unchanged; the environment addendum used exactly as written.
    - **Maintainer integration checks:**
      - checksums;
      - the patch reproduces the file, and it is the only file;
      - freeze: 10/10 public, only the two authorized bodies changed;
      - no forbidden construct or `sorry` in the 913 added lines; widths ≤ 98;
      - the bundle's sole prerequisite is the base `70b503b4`;
      - no name MIG-1 S renames.
    - **Elaboration at the tip** (`WindowRun.lean` unchanged since the base) against
      `oleans-ltip3`: 0 errors, 0 warnings, axioms as stated.
    - **Screens:** the worker's v1 screens (its brief) show 2 new in-file pairs, both the
      pre-disclosed instance boilerplate (83%, 50%). The maintainer's v3 re-screen at the tip is
      queued.
    - **Landing:** branch `lean/b6-f2-windowrun` (cherry-picked, authorship kept). Replay 4
      modules. It lands after MIG-1 S (#98), whose replay list contains all four.
    - **Landed (2026-10-15, PR #99; replay 4 of 4 from #98's snapshot; snapshot `oleans-lf2`).**
    - **Maintainer v3 re-screen at the tip (the 21-file population):** 495 → 497 pairs, the 2 new
      ones exactly the pre-disclosed instance pairs (83%, 50%), none cross-file. The ledger is
      confirmed.
  - **F1 v2 delivered (2026-10-15, `fill-b6-stepclock-v2.zip`, SHA-256 `9ba3f781…009c`; Codex
    `e81df474`, three commits; report `audits/b6-fill-agent-reports/stepclock-2-REPORT.md`):
    complete.**
    - **What's proved:** `exists_stepClockTMVia`, so the frozen `exists_stepClockTM` (C1's) is
      admission-free and F2's runner becomes sorry-free. Standard axioms throughout.
    - **The promotion list:** applied verbatim (both shared files equal the overlays).
    - **Additions:** 33 privates. The only restatement is the recommended `sc_debit`, gaining
      one state-image conclusion.
    - **No escalations; new copies: none** (only the two pre-disclosed controller pairs).
    - **Promotion candidates:** `sc_debit`, `sc_clockTM`, `sc_dec_inputPos`,
      `sc_observedSegment`, `sc_firstExit`.
    - **Maintainer checks:**
      - checksums and the shim hash;
      - the overlays, and the patches reproducing the files;
      - freeze 5/5 public, only the target's body changed;
      - no `sorry` in the final files; hygiene; width ≤ 99;
      - no name MIG-1 S renames;
      - the three files are unchanged at the tip.
    - **Landing PR #103** (cherry-picked, authorship kept); replay 80 modules from #102's
      snapshot.
    - **Landed (2026-10-15, PR #103; replay 80 of 80 from #102's snapshot; snapshot `oleans-lf1`
      for the tip `14c2fc19`).** The only sorry count that moved is `Build/StepClock`'s, 1 to 0.
      C1's step clock and F2's windowed runner now rest on no `sorry`.
  - **F3's brief issued (2026-10-15): `briefs/b6-fill-configclock.md`** (Route A, the gate's ruling
    now that the shared clock is filled).
    - **Inputs** `8420da14`, on a side branch from `ef45bcb2`, merged in `7755f6a2`, so the worker's
      base keeps the Lean content `b6e0344c` (#108 merged).
    - **The clock:** all-`true` digits of width `c · (field total)`, written by a recommended
      generic two-tape clock writer (stub, elaborated). It uses the mapped copy (#108) per field,
      `skipTM`, one permitted one-cell move (no public row stops on a delimiter) and
      `skipBackTM`. Then F2's runner, then `clearTM_run_ofCfg` on `halted`/`left`.
    - **Pre-ship:** the overlay gives 2 sorry warnings (the stub and the target), no other. The
      import probe (54 names) and the consumer probe (row 18's endpoint, after clearing the
      radius word, meets the precondition) are clean.
    - **Inputs measured:** order list 176 modules; base sorry set 28; v3 screen base on F2's
      21-file population: 503 pairs.
    - **Dispatched (2026-10-15)**: brief attachment SHA-256 `6bf925d1…2980`, the addendum
      `a25474c5…`; branch `fill/b6-configclock`; delivery `fill-b6-configclock.zip`.
    - **Delivered (2026-10-15):** `fill-b6-configclock.zip`, SHA-256 `73708719…d8bd`. Under review
      by a review sub-agent (user, 2026-10-15: sub-agents are reserved for reviewing incoming fills
      and audits).
    - **Reviewed (2026-10-15; `audits/evidence/b6-fill-configclock/delivery-review.md`):** a clean
      partial, 0 of 1. It adds five private arithmetic lemmas (`cw_*`), and every check passes:
      integrity, freeze, elaboration at the tip, probes, axioms, lint, and the v3 screen (0 new
      pairs). Its escalation **E1 is real:** ground rule 10 forbids unfolding `RecordAt`, but the
      route needs its cells, and no public eliminator exists. The same holds for `recordLength`'s
      formula and `n + 2 ≤ 2^posWidth n`.
      - **User (2026-10-15):** (a) the continuation may unfold the specification-level
        definitions `RecordAt`, `recordLength` and `posWidth` in WindowClock (no API PR); and
        the partial lands now.
      - **Landing PR #111** (`lean/b6-f3-partial`): the worker's commit cherry-picked from the
        bundle, plus the appendix updated for the ruling. Replay `replay-lf3p.sh` covers 2
        modules, after #110's (snapshot `oleans-lf3p` from `oleans-lpcanon`). Next: F3's
        continuation brief.
      - **Landed (2026-10-16, PR #111; replay 2 of 2; snapshot `oleans-lf3p`, the tip `c2897d7f`).**
      - **Superseded for the continuation (user, 2026-10-16, G4's E1 ruling, below):**
        specification facts come from published equation lemmas, not from unfolding. F3's
        three facts go into the same API PR: a `RecordAt` eliminator, `recordLength`'s formula
        and `n + 2 ≤ 2^posWidth n`.
  **Record-table row 18's fill brief issued (2026-10-14):** `briefs/w1-fill-recordtable-cont5.md`
  (inputs `8dfbc881`, at `1b6b972c`):
  - The route is a 14-phase chain over row 17 through R1. Three prescribed privates are proved;
    one obligation remains.
  - The tail writer's recursion on `k` is not a host (the user's ruling).
  - Its consumer probe shows the endpoint meets `exists_configWindowRunnerTM`'s precondition. The
    consumer must clear the radius tape.
  - Dedup, for the dedup window: `rt_embed_matches` is now a private twin of the public
    `embedEmitCfg_eq`. Its consumers are `rt_exists_cleanDigitBoundTM` and `rt_cellWindow_ready_run`.
  **Row 18 delivered (2026-10-14, `fill-w1-recordtable-cont5.zip`; Codex `6aef1d2a`, report
  `audits/wave1-fill-agent-reports/recordtable-6-REPORT.md`): `exists_recordInitTM` is proved**,
  with its statement unchanged, 18 new privates, and only the standard axioms.
  - **Maintainer integration checks:** checksums; the patch reproduces the file; one file only;
    freeze 28/28 public, no statement changed, only row 18's body changed, no existing private
    changed; no forbidden construct, `sorry` or `axiom` in added lines. It elaborates at the
    post-#94 tip against `oleans-lh1` with 0 errors and the four paused rows' sorries.
  - **Duplication ledger:** 5 new in-file pairs, no cross-file pair.
    - Two are the pre-disclosed `rt_tailState` instance pair.
    - One is a 113-character composition pair.
    - **Two are larger:** `rt_position_run` and `rt_tail_run` reproduce 954 and 836 of
      `rt_moveWord_run`'s 1,606 characters. The worker classifies them as shared framed-contract
      and R2 bookkeeping, not re-proved moves. They are carried to the epoch's duplication ledger
      for classification. RecordTable already holds earlier debt (`rt_embed_matches`).
  - **Integration PR:** branch `lean/rt5-row18`; replay of 51 modules from `oleans-lh1`.
  - **Promotion candidates** (the worker's): the scratch-template transport, the finite-tail
    writer, the position component, the two-field cleanup, and `binDigits_one`.
* **C1-D: the NTIME hierarchy's design** (2026-10-13; `audits/evidence/c1/C1-design.md`, statement
  draft `C1HostsDraft.lean.txt`: 0 errors, 5 sorries, 10 theorems proved). The proposed route:
  - **guess first:** the universal NDTM and the diagonalizer write the whole choice word with a
    small nondeterministic writer, then interpret deterministically. That removes SC-3 (no
    nondeterministic counter loop); the shared nondeterministic infrastructure is a transfer and
    slice lemma and a nondeterministic phase host, which stage 2's nondeterministic form needs
    too;
  - **the exponential decider is derived**, as `BF := E(UN)`, with `E` a public exhaustive-replay
    theorem;
  - **nondeterministic codes are interpreted through their replay table**, with H2 unchanged
    (`CodeNDTM.serialize_eq_tableBitsK` is proved);
  - **a step-clocked runner** is designed with B6's H3;
  - **the universal machine's input is a bounded window copy** plus an input-locality lemma.

  Machine level confirmed. Estimate: 13k–26k lines. **Answered (user, 2026-10-13): all five as
  recommended** (note §6): guess first, which closes SC-3; `BF := E(UN)`; the replay table; one
  step clock shared with B6 (`exists_stepClockTMVia`, gated with the B6 hosts); the bounded window
  copy. **Statement gate (2026-10-13):** `audits/c1-hosts-statements-pack.md` (six landing modules;
  0 errors, 5 sorries, 11 public theorems proved). It adds an input-locality lemma and a window
  copier for decision 5, and it strengthens the interpreter core `R`. **CLOSED** (round 1,
  2026-10-14: PASS, 0 blockers / 0 majors / 11 minors; `audits/c1-hosts-statements-findings.md`,
  resolutions `audits/c1-hosts-statements-resolutions.md`). Next: the landing PR, after #86, since
  the slice lemma's proof replaces #86's `sorry`, carrying the six text fixes. Then, before UN's
  brief, the guess-then-run assembly lemma's gate in `Build/NDHost`, and before `R`'s brief, the
  H1 hosted-clock harvest (rulings 2 and 5). (The
  B6 hosts' pack strengthens `exists_stepClockTMVia`; C1 cites it only in sketches and its
  dependency note, which re-point to `Build/StepClock.lean` at landing.)
  Records corrected: `clockTM` is linear (design §12.7, plan item 12); `exists_effectiveNDMachineCode`
  is already proved (plan §4e's C1 row). Still to fix: `NTimeHierarchy.lean`'s docstring says
  "quadratic" (lines 51 and 110), to correct in C1's first Lean PR; and design §12.8 routed
  `PATH_mem_NL` through SC-3, stale since C2 moved to programs (marked superseded 2026-10-13).
  **Landed (2026-10-14, PR #87; replay 147 of 147, with the ARM merge):** `Nondeterministic.lean`'s
  Part A proves `runWith_eq_fixChoice_runFrom` (#86's `sorry` closed), and
  `NondeterministicSpace.lean` proves its space companion. The new `ChoiceReplay`,
  `Build/NDHost`, `Build/InputWindow`, `NDCodeSimulator` and `ClassNP/ExhaustiveReplay` carry the
  five gated contracts, sorried for the C1 fills. `NTimeHierarchy.lean`'s "quadratic" docstrings
  are fixed. Next: the guess-then-run assembly gate and the H1 hosted-clock harvest, then the
  fill briefs.
  **C1-A assembly statement gate (2026-10-14):** `audits/c1-assembly-statements-pack.md`
  (dispatch folder 19, built at `e831b5b0`). It covers the host `Turing.guessRunTM` (six phases
  over `phaseHostND`) and eight theorems, appended to `Build/NDHost.lean`: the handoff, liveness,
  the whole branch, the halting setup, all-branch halting, exact-budget acceptance, the core's
  clean precondition and the silent composite. The unit (896 lines) has 0 errors and no new
  `sorry`; six theorems are proved modulo the gated `ndWriterTM_run_block`. Consumer probes derive
  UN's frozen statement and D's `NTIME` shape. Four open questions (the rewind's `Catalog` import,
  UN's setup as a fill obligation, an `embedSilentCfg_cap` export, the verdict leaf inline).
  Independent of #92 and #93; if #92 lands first, the landing re-runs the cut check.
  **Round 1 (2026-10-14): OPEN, 0 blockers / 1 major / 3 minors**
  (`audits/c1-assembly-statements-findings.md`; resolutions `…-resolutions.md`). No theorem is
  false and no hypothesis is spurious. The major is policy only: `guessRunCfg_clean` repeats
  `Inclusions`' private `b2b_capture_shape`. It is repaired by the public `embedSilentCfg_cap` in
  `Build/Embed`, with `b2b_capture_shape` retired onto it. The minors are one docstring and two
  evidence-tooling fixes. Rulings: the `Catalog` import kept, UN's setup a fill obligation (its
  `hsetup` verbatim in UN's brief), the export added, the leaf inline. Next: round 2 at the tip.
  **Round 2 CLOSED (2026-10-14): 0 blockers / 0 majors / 1 minor**
  (`audits/c1-assembly-statements-r2-findings.md`). The export is in `Build/Embed`, and
  `b2b_capture_shape` stays private, rebased on it. The minor is the name screen's allowlist
  boundary, fixed in the landing. Next: the landing PR for Embed, NDHost and Inclusions, with
  about 150 downstream modules to replay.
  **H1 hosted-clock harvest statement gate (2026-10-14):** `audits/h1-harvest-statements-pack.md`
  (folder 20): the public counter loop over the step block in a new `Build/StepBlockLoop.lean`,
  with CodeSimulator's eight private declarations deleted. **CLOSED** (round 1: PASS, 0 blockers /
  0 majors / 4 minors; `audits/h1-harvest-statements-findings.md`, resolutions `…-resolutions.md`).
  Ruling 5 is satisfied and R's loop phase follows. The minors are three checker-strength fixes
  and one stale citation, all fixed for the landing. Next: one maintainer landing PR at the
  merged base (a 9-module replay with `SelfUniversal`); registry row H2-L when it lands.
  **Landed (2026-10-14, PR #94; replay 76 of 76):** `Build/StepBlockLoop`, CodeSimulator's private
  assembly deleted, `counterValue_bits` and the moved `foldr_bit_eq_ofDigits` in `Build/CounterLoop`;
  new snapshot `oleans-lh1`. R's brief cites the public contracts.
* **RD-5: §13d G2–G4 after MIG-0b** (§16b item 5). **G2–G4 statement gate CLOSED (2026-10-14: PASS 0/0/5;
  `audits/s13d-g24-statements-findings.md`, resolutions `…-resolutions.md`):** both duplication
  families removed; it lands after MIG-1 S, rebased; G4's fill brief identifies or gates its host
  first.
  **Landing PR #106 (2026-10-15):** rebuilt at the tip `6672531c` (after #105) against `oleans-lmain`
  (`audits/evidence/s13d/g24/landing/`).
  - The gate's writers apply unchanged; MIG-1 S's two `Catalog` endpoint theorems unfold no table.
  - 7 checks and 8 checker controls pass, every result equal to the gate's. The v3 screen's delta
    is exactly the accepted 24 new and 7 removed pairs.
  - Minors 3 and 4 are fixed, in prose only. Minor 1 is annotated in the design note's §5(e);
    minors 1 and 2 are carried to G5's statement phase.
  - Replay: 87 modules from #104's snapshot.
  - **Landed (2026-10-15, PR #106; replay 87 of 87; snapshot `oleans-lg24` for the tip `107f1687`).**
    The only sorry counts that moved: `Build/Catalog` 0 to 2 and `Build/Zone` 2 to 1, plus the new
    `ZoneTape` (0) and `ZoneRebalance` (2).
  - **Next:**
    - the G2 fill: `copyMapTM_run_ofCfg`, `transferMapTM_run_ofCfg` and the pure
      `zoneCascadeRight_home`. **Done by the maintainer (user 2026-10-15), PR #108 (`8e3cee48`,
      then the Zone factoring `a9ee4701`; `audits/evidence/s13d/g2-fill/NOTES.md`):** one trace
      lemma for both mapped rows (the copy is the transfer with residue `some`), the plain rows
      as their identity instances, and one shared induction for `zoneSide_cascadeRight` and
      `zoneCascadeRight_home`, with the index-0 unfolding and the frame half each proved once.
      Both files have 0 sorry, standard axioms, 0 new warnings and no statement change. The v3
      screen goes from 384 to 369 pairs. **User (2026-10-15):** factor the Zone pairs and
      approve the two Catalog idiom pairs; then approve the one remaining Zone pair (54%, 314
      chars, the successor of a base pair). Replay: 87 modules from `oleans-lcanon4`.
      **Landed (2026-10-15, PR #108 as `b6e0344c`; replay 87 of 87, 0 errors, at `a9ee4701`;
      snapshot `oleans-lg2` for the tip `b6e0344c`).** The only sorry counts that moved:
      `Build/Catalog` 2 to 0 and `Build/Zone` 1 to 0. **The G2 fill gate dispatched
      (2026-10-15; folder 27, bundle SHA-256 `f6044d47…dcfc7`, 60 sections; pack
      `audits/s13d-g2-fill-pack.md`).** **CLOSED (round 1: PASS 0/0/3;
      `audits/s13d-g2-fill-findings.md`, resolutions `…-resolutions.md`).** The re-pointed
      regression is accepted. Minor 1 (the clear row's inline clauses, residual in the acknowledged
      §12.6 family) and minor 3 (two stale sketches) are fixed in PR #109; minor 2 (the notes'
      per-file subtotals) is corrected by an erratum.
    - G4's host first (obligation 3): identify the public host for the two-tape scratch and
      ruler layout, or gate a missing one, before G4's fill brief. **Surveyed (2026-10-15;
      `audits/evidence/s13d/g4-hosts/G4-HOSTS-SURVEY.md`):** every host is public (round
      iteration without a counter, `Round.iterate`/`RoundContract`; `Contract.seq`/`inPhase`/
      `branch`; the mapped column moves; the one-tape seeks; `scanTM`). One leaf is missing: a
      two-tape lockstep walk that stays where it ends, the ruler for mirror crossings and slot
      offsets. Its two named customers are the G4 rows. The seeks and `scanTM` also lack Contract
      wrappers. **User (2026-10-15): public, gated first.** Next: a small statement unit (the
      walk row in both directions in `Build/Catalog` beside R8.3, its Contract, and Contract
      wrappers for the seeks and `scanTM` in `Contract/Catalog`), with its own statement gate;
      then G4's fill brief cites them. **Built (2026-10-15; `audits/evidence/s13d/walk/`, pack
      `audits/s13d-walk-statements-pack.md`, folder 28), and complete:** `walkTM` with its
      proved framed row; the skip is its one-tape instance (`skipTM_eq_walkTM` by `rfl`;
      `skipTM_run_ofCfg` re-proved through it). In `Contract/Catalog`: `framedContract`
      (`sweepContract` now its two-pass instance), `seekPost`, and six contracts (walk, skip,
      skip back, seek end, seek start, scan). 119 publics, standard axioms, 0 new warnings. The
      screen goes from 392 to 390 pairs; one new mirror pair (`seekStartTM_contract` ←
      `seekEndTM_contract`, 53%), **approved by the user (2026-10-15)**. The landing PR
      (`lean/walk-row`) follows the gate. **The walk statement gate dispatched (2026-10-15;
      folder 28, bundle SHA-256 `66f5d270…22b6d`, 50 sections).** **CLOSED (round 1: PASS
      0/0/2; `audits/s13d-walk-statements-findings.md`, resolutions `…-resolutions.md`).**
      Minor 1 is an erratum to the survey's displacement convention: the walk moves `|w| + 1`. G4's
      fill brief uses the auditor's adjustment (one ruler-only step, then the walk over the
      tail). Minor 2 (the walk's sketch) is fixed in PR #109. **Landing PR #109** (`93ea007f`; it
      also carries the G2 fill gate's minors 1 and 3): replay 84 modules from `oleans-lg2`.
      **Landed (2026-10-15, PR #109 as `e5fcd8ee`; replay 84 of 84, 0 errors, at `93ea007f`, no
      sorry count moved; snapshot `oleans-lwalk` for the tip `e5fcd8ee`).** Next: G4's fill
      brief.
    - **G4's fill brief issued (2026-10-15): `briefs/s13d-fill-g4.md`.**
      - **User (2026-10-15):** one brief in two phases (the kit and the extension row, then the
        rebalance row); the brief authorizes exactly two imports (`Build/Contract/Catalog`,
        `Build/Contract/Seam`) as the worker's first edit.
      - **Inputs** `1299799c`, merged in `4db8beff` (Lean content `e5fcd8ee`).
      - **Pre-ship:** the overlay (the imports and two recommended layout bridges) gives 4 sorry
        warnings, the stubs and the rows, and no other. The import probe resolves 94 names.
      - **Measured:** order list 79; base sorry set 37; v3 screen base on a 10-file population:
        429 pairs.
      - The brief carries the walk gate's convention adjustment, and recommends a commuting
        reorder of each pass (proved pure first) with a unary zone count on scratch.
      - **Dispatched (2026-10-15, user):** brief attachment SHA-256 `21c3c31f…4e081`, the
        addendum `a25474c5…`; branch `fill/s13d-g4`; delivery `fill-s13d-g4.zip`.
      - **Delivered (2026-10-15):** `fill-s13d-g4.zip`, SHA-256 `31b1ce63…28c6`. Queued third for
        the review sub-agent, after B6 F3 and the canonizer's continuation 5.
      - **Reviewed (2026-10-16, screens pending):** partial 0 of 2. It adds 18 checked `zr_`
        helpers, and every non-screen check passes. Its **E1 is real**, the same rule-10 class as
        F3's: the layout data and every row contract's fields can only be read by unfolding.
      - **User (2026-10-16): an API PR first**, not unfolding, and it is the rule for future
        briefs. A maintainer PR adds public equation lemmas for the contracts used, the
        `Contract` combinators' fields and the layout's base and boundary facts (with F3's
        three). It has its own audit gate (the §13d PR-plus-gate rule). The replay is about 89
        modules. The G4 partial lands once its screens are clean (user).
      - **Review final (2026-10-16):** screens clean, 763 → 778 declarations and 429 = 429 pairs, 0
        new. Landing next (user: prepare clean landings overnight). The appendices' "blocked under
        rule 10" wording is reworded at landing.
      - **Landing PR #115** (`lean/s13d-g4-partial`): the worker's commit, plus the appendices
        reworded to point to #112. Replay `replay-lg4p.sh` covers 2 modules, chained after H2-F's
        (`oleans-lg4p` from `oleans-lh2f`). **Re-pointing candidate:** `zr_mirror_tape` unfolds
        `zonedTape`, which predates the no-unfolding rule.
      - **The specification API, PR #112** (`lean/spec-api`, `9f66ac7e`; pack `audits/spec-api-pack.md`,
        evidence `audits/evidence/spec-api/`).
        - **Generated:** 85 field equations (`simps`, `isSimp := false`) for `Contract.trans`,
          `seq`, `inPhase`, `branch`, `framedContract`, `seekPost`, `sweepPost` and the ten row
          contracts.
        - **Hand-written:** seven layout lemmas in Catalog, `recordAt_iff`, `record_pos_lt`
          public, `recordLength_eq`.
        - Checks clean; the screen is running. The gate is dispatched next, and the merge waits
          for it. The replay (89 modules) is re-sequenced after the partials landing first.
      - **User (2026-10-16), the rule's scope: "Everything".** Every definition a brief's route reads
        gets a published equation lemma before dispatch, wherever it lives. A pre-ship inventory
        per brief finds the missing ones.
        - Maintainer's boundary, stated to the user: the machine model's semantic primitives
          (`MultiTapeTM.step`, `runFrom`, `Action.apply`, `Cfg.mapState`) are read through their
          existing lemmas. A worker's own leaf may unfold `step` on its own table.
        - **Core API PR, in preparation** (`lean/core-api`, for U2-S and F5): `Cfg.init`'s fields,
          `bufferedFirstCfg`'s and `bufferedSecondCfg`'s fields, `pairEncode_eq`, `unaryFin_eq`,
          `embedSilentCfg_unselected` and the transports' scalar fields,
          `mem_visitedByTapeHead_iff`, and the two visited-set splits moved from `StepBlock` to
          `Deterministic`. Next to add: `serializeK_eq`, after #113. It has its own gate, and its
          replay is about 320 modules (from `Configuration`).
        - U2-S's and F5's briefs (inputs measured at `c2897d7f`) wait for it.
        - **PR #116 opened (overnight, 2026-10-16;** `lean/core-api`, head `2cdc026e`). Beyond the list
          above, it adds:
          - `serializeK_eq` (a CodeSimulator hunk apart from #113's);
          - `Cfg.inputSymbol_of_zero`/`_of_end`, `Cfg.workTapeSymbols_eq`;
          - `MultiTapeTM.initCfg_eq`.
          Checks are clean. On the screen, the one changed pair is pre-existing, relocated by the
          move (`roundTM_iterate` ← `visitedByTapeHead_step_subset`, 76% → 71%).
          - **Its gate is staged, not dispatched:** `infra_local/gate-dispatches/30-core-api-gate/`,
            bundle SHA-256 `0b8860d6…1a0e` (48 sections), pack `audits/core-api-pack.md`.
          - Its replay (about 320 modules) waits until #112, #114 and #115 merge; the branch is
            then brought up to date.
          - The U2-S and F5 drafts now carry the new rule 10 and their API lemma lists (copies in
            `audits/evidence/core-api/drafts/`).
          - **Extended overnight (head `84acb1f7`)** with the F3 and G4 continuation inventories'
            gaps beyond #112: `wordPatch_of_mem`/`_of_not_mem` (F3 reads F2's endpoint through
            `wordPatch`) and `zoneCapacity_eq`. The nine-file screen is 440 → 443 declarations,
            92 = 92 pairs. The gate is **re-staged** with bundle SHA-256 `79b8052e…d4bf` (56
            sections), still not dispatched.
        - **Open for the user: G4's continuation and the zone layer.** G4's original brief let the
          worker unfold `Build/Zone`'s and `Build/ZoneTape`'s pure definitions. Under "Everything",
          its continuation needs published lemmas for the zone definitions the rebalance route
          reads. 14 of the 34 zone definitions have none (`zoneShiftIn`/`Out`, `zoneMove`,
          `zoneStepPair`, `zoneHomeWrite`, `swap`, `zoneSlotSet`, `zoneCellAt`, …). The options
          are to add a zone API to #116 before its gate, to make a separate zone-API PR with its
          own gate, or to carve out an exception for the zone layer. That is a design ruling, so
          the maintainer stopped there.
        - **Ruled (user, 2026-10-16): option (a), the zone API joins #116 before its gate.**
          Applied as #116's fifth commit `d5255232`. The full inventory counts 35 definitions:
          - 3 need no lemma (`ZoneCell`, `ZoneSym`, the structure `ZoneContents`);
          - 5 were already covered (`zoneCapacity`, `zoneStart`, `zoneOwner`, `zoneIndex`,
            `zoneShiftIndex`);
          - the other 27 now have equations covering every input (32 hand-written lemmas, 24
            `simps` field equations).

          The same commit rewrites six bare-label docstrings to state their formulas (#112's
          finding 4, same style). The elaboration is clean (Zone and ZoneTape: 0 errors, 0
          warnings), with standard axioms only, the lint unchanged and the freeze adds only. The
          ten-file screen goes 462 → 468 declarations and 103 → 103 pairs, with no new copy. The
          gate was re-staged (bundle rebuilt) and is not yet dispatched.
        - **Drafts (not issued):** `audits/evidence/drafts/` holds the F3 continuation (on the new
          rule, citing #112's lemmas), cont6 (the adapter authorized; the order list includes
          `ClassNP/TMSAT`), U2-S and F5.
      - **#112's gate dispatched (user, 2026-10-16):** `infra_local/gate-dispatches/29-spec-api-gate/`,
        bundle SHA-256 `91f96cf5…dca1` (52 sections). Lean comes from #112's head `28824c36`, now
        stacked on #113 (user: "stack and chain"); everything else from `2e4f414c`.
      - **Overnight replay started (user, 2026-10-16):** `replay-overnight.sh` runs #113's replay
        (9 modules, `oleans-lc5p`), then #112's (89 modules, `oleans-lapi`). The landings prepared
        overnight chain after it.
        - **Both passed:** #113's 9 of 9 (CodeSimulator has 2 sorries, as expected) and #112's 89 of
          89, failed 0. The per-module sorry counts match the static set at #112's tree (89 of
          89, 0 mismatches; 58 in total).
        - **#113 is ready to merge.** #112 waits for its gate.
        - **#113 merged (user, 2026-10-16, `5eff4146`).** The chained replays passed: `replay-lh2f.sh`
          4 of 4 (UniversalK has 3 sorries; StepBlockForward 0) and `replay-lg4p.sh` 2 of 2
          (ZoneRebalance has 2). **#114 and #115 are ready to merge.** Each branch holds only its
          own commits on the campaign branch, so neither carries #112. Each file was checked both
          without #112 (the review elaborations, against `oleans-lwalk`) and with it (the
          replays).
      - **#112's gate returned (user, 2026-10-16): FAIL, 0/2/2/1** (`audits/spec-api-findings.md`).
        - Major 1: field equations for `ReturnContract.release`, `RoundContract.release` and
          `Contract.ofSegment`.
        - Major 2: an application equation for `sweepMapWrite`.
        - Minor 3: WindowClock's appendix still says unfolding is permitted.
        - Minor 4: two docstrings use the bare-label style.
        - Note 5: the replay log was not in the bundle.

        - **Reviewed:** all five findings are true, and finding 2 is downgraded to minor
          (`audits/evidence/spec-api/r2/gate-review.md`; resolutions in
          `audits/spec-api-resolutions.md`).
        - **Round 2 pushed:** `lean/spec-api` `52965dc9` applies the review's patches unchanged
          (they supersede the maintainer's draft). `caa93c12` then merges the tip, with #114 and
          #115.
        - **The replay passed (user, 2026-10-16):** `replay-lapi2.sh`, 85 of 85, 0 failed. The
          sorry counts equal round 1's, except `StepBlockForward`, 1 → 0 (#114). The snapshot
          `oleans-lapi2` is the merged head `caa93c12`, which is the tip plus #112.
        - **Round-2 gate** (folder 31, bundle `a82bd16a…710a`), dispatched by the user, returned
          **PASS, 0/0/0/1. The gate is CLOSED** (`audits/spec-api-r2-findings.md`, the review
          `r2/gate-review-r2.md`). The note asked for consumer-instantiation evidence; it is
          resolved by the review's `ConsumerProbe` (exit 0) and the copy-route probe's recorded
          exit. **PR #112 is ready to merge,** before #116.
        - **#112 merged (user, 2026-10-16).** The tip's Lean equals `caa93c12`, so the tip's
          snapshot is `oleans-lapi2`.
      - **#116's gate returned (user, 2026-10-16): FAIL, 0/2/3/0** (`audits/core-api-findings.md`,
        untracked until resolved).
        - Major 1: `cleanTM`'s initialization.
        - Major 2: `FinTM.ComputesFunInTime`.
        - Minor 3: the bundle's consumer files predate #115.
        - Minors 4 and 5: the records.

        - **Reviewed:** all five findings are true, at the auditor's severities
          (`audits/evidence/core-api/r2/gate-review.md`; resolutions `audits/core-api-resolutions.md`).
          Finding 1's proposed home, `Machines/CleanSweep`, is Hydroxyi's. The fix is instead a
          generic restart pair in campaign-owned `Finite.lean` (`runFrom_with_q₀`,
          `initCfg_with_q₀`), and U2-S restarts the cleaned canonizer through `cleanTM_run` (the
          U2-S draft is updated).
        - **Round 2 pushed:** `lean/core-api`:
          - `f2e0f3d7`: the review's patches, unchanged;
          - `395771bc`: the tip merged in;
          - `93c4c630`: #112's round 2 merged in, stacked and chained as for #112 and #113.
            **#112 merges first.**
        - **The replay passed (user, 2026-10-16):** `replay-lcapi.sh`, 320 of 320, 0 failed. The
          sorry counts equal a static count (94 in total). The snapshot `oleans-lcapi` is the
          stacked head `93c4c630` (the tip plus #112 plus #116).
        - **The round-2 gate is staged:** `infra_local/gate-dispatches/32-core-api-r2-gate/`, bundle
          SHA-256 `559c64bb…592b` (89 sections; Lean `93c4c630`, other `179db5b3`), pack
          `audits/core-api-r2-pack.md`. **Dispatched (user, 2026-10-16).**
        - **It returned PASS, 0/0/0/0. The gate is CLOSED** (`audits/core-api-r2-findings.md`; the
          review `r2/gate-review-r2.md`, with `RestartPublishedProbe`, exit 0). **PR #116 is ready
          to merge;** #117 is stacked on it.
      - **#114 and #115 merged (user, 2026-10-16; `a2b834b3`, `c451e358`).** H2-F is complete
        (`exists_forwardLoopTM` proved; the §14 H2 row is updated), and G4's partial has landed.
        The library's snapshot for the tip is `oleans-lg4p`; it was built on #112's tree, which
        adds lemmas only.
      - **#116's gate dispatched (user, 2026-10-16):** `infra_local/gate-dispatches/30-core-api-gate/`,
        bundle SHA-256 `fc8219a6…78e5` (63 sections; Lean `d5255232`, other `e2301305`).
      - **User (2026-10-16), the primitives boundary:** workers read `MultiTapeTM.step`, `runFrom`,
        `Action.apply` and `Cfg.mapState` through the existing lemmas, and may unfold `step` and
        `Action.apply` only for a leaf defined in their own file.
  **Two-tape universal (U2) designed (2026-10-14; `audits/evidence/u2/U2-design.md`, probes).**
  - **The design:** one `k`-generic construction on H2's step block. It has a new public host
    H2-F (the emitting round loop, in `Build/StepBlockLoop`), U2-S (the startup), U2-U
    (self-application universal, `C_α·(t+1)` time and `C·(s+1)` space) and U2-E (the code-first
    evaluator, which re-derives `Turing.universal` at `k = 1`).
  - The hierarchy needs only U2-U at `k = 2`, on the native input. Hydroxyi's `clockTM` clocks;
    there is no uniform scheme or input copy.
  - `Diagonal.lean`'s parameterization over `DiagSimulator Φ` and `SelfSimulator Ψ` is fully
    proved in the probe, with standard axioms. All four public theorems re-derive verbatim.
  - **User (2026-10-14), all as recommended:**
    - (a) B6's `U₀` and its startup are generalized to `k` before B6's `U₀` fill is briefed, with
      B6's statements kept verbatim as the `k = 1` corollaries;
    - (b) H2-F becomes a public host, gated hosts-first;
    - (c) no verdict-only variant;
    - (d) Theorem 1.9 keeps the relaxed quantifier;
    - the illustration `DTIME(n+1) ⊊ DTIME((n+1)²)` is dropped, so `Separation`'s log lemma is
      not copied;
    - the facade `TimeHierarchy.lean`'s one stale docstring sentence is fixed in the Diagonal PR;
    - **Diagonal Part 1 (the parameterization) lands early,** by PR plus a small statement gate.
  - **Diagonal Part 1 statement gate CLOSED (2026-10-14; folder 24; PASS 0/0/2;
    `audits/diagonal-p1-statements-findings.md`, resolutions `…-resolutions.md`).**
    - **The two minors:** both are evidence-checker fixes, repaired in the closing commit with
      three new negative controls: the name screen missed fully qualified names, and the copy
      screen had a same-name blind spot (now v3).
    - **Rulings:** `W`, `diag_cost_le` and the verdict-only clause are kept. The facade sentence
      waits for the end-of-chain PR.
    - **The auditor's suggested compiled checks** (zero overheads, a constant `decode`, the
      projection `rfl`s) go to the end-of-chain PR.
    - **Next:** the landing PR after MIG-1 S, with a fresh `run.sh` at that tip and an 11-module
      replay.
    - **Landed (2026-10-15, PR #100; 14 of 14 checks fresh at `eb750e63` against #98's snapshot;
      replay 11 of 11 from #99's; snapshot `oleans-ldiag`, valid for the tip `dc8d0409`).**
  - **U2 statement gate dispatched (2026-10-14; folder 26; `audits/u2-statements-pack.md`).**
    - **The unit:** a new `TuringMachine/UniversalK.lean` with the scheme interface
      `EffectiveCodeK k`, the two received schemes as instances, and U2-S, U2-U and U2-E. H2-F is
      `StepBlock.exists_forwardLoopTM` in `Build/StepBlockLoop`, renamed from `exists_emitLoopTM`,
      which already names `Turing.FinTM.exists_emitLoopTM`. B6's `exists_selfStartupTM` and
      `exists_selfUniversal` are re-proved in place as the `k = 1` corollaries, signatures
      byte-identical (decision (a)). One promotion: `Code2TM.serialize_eq_serializeK`.
    - **Status:** 4 contracts sorried, the rest proved; 10 checks pass against `oleans-ltip3`;
      replay 10 modules. The consumer probe takes G5 as a hypothesis and reaches the `f log f` and
      book-form hierarchy through Diagonal Part 1, with `sorryAx` only from U2-U.
    - **Five questions to the auditor**, with recommendations: H2-F's home, two disclosed screen
      pairs, the field name `machine`, `exists_code2TM`'s home, and U2-E's fill timing. The user
      decides after the findings.
    - **Gate CLOSED (2026-10-15: PASS, 0 blockers / 0 majors / 2 minors / 3 notes;
      `audits/u2-statements-findings.md`, resolutions `…-resolutions.md`).**
      - **The auditor's review:** no false or vacuous contract and no changed signature; each
        contract argued true constructively; H2-F is the right host boundary.
      - **The minors:** the axiom checker's strictness (m1), fixed for the landing; and H2-F's
        §14 registry entry (m2), added at landing.
      - **User (2026-10-15):**
        - Q1: H2-F moves to a new `Build/StepBlockForward.lean`, so `CodeSimulator` (the B5a
          continuation 4's file) stays out of U2's replay;
        - Q2: the four boilerplate pairs are acknowledged, with no payback;
        - Q3–Q5 as recommended.
      - **Next:** the landing, rebuilt for the new home and re-checked at the tip.
      - **Landing PR #102 (2026-10-15):** 10 of 10 checks fresh at `9c0ae906` against #101's
        snapshot. These include the stricter axiom checker (m1) and its mixed-axiom control.
        H2-F is in `Build/StepBlockForward`, and `CodeSimulator`/`StepBlockLoop` are untouched.
        The replay is 5 modules. The §14 H2 row now records H2-F (m2).
      - **Landed (2026-10-15, PR #102; replay 5 of 5 from #101's snapshot; snapshot `oleans-lu2`).**
      - **H2-F's fill brief issued (2026-10-15): `briefs/h2f-fill-forwardloop.md`** (user: H2-F,
        then U2-S and U2-U).
        - **Inputs** `54fb8482`, merged in `409c47a4` (Lean content `e5fcd8ee`).
        - **Pre-ship:** the import probe resolves 41 names with no import added.
        - **Measured:** order list 79; base sorry set 37; v3 screen base on an 11-file population:
          100 pairs, 2 of them `forwardLoopCfg`'s frozen 52% pairs with `Simulation`.
        - **The composition** is fixed in the brief. The block's live exit is its entry, so the
          block runs inside the release adapter `seamReleaseTM`, as one phase of the phase host,
          beside a one-step forwarding leaf. The cost is `T + 3` (`T + 2` on a halting step), so
          `C = 3`.
        - **Dispatched (user) and delivered (2026-10-16):** `fill-h2f-forwardloop.zip`, SHA-256
          `7fc0da15…8037`. **Reviewed: complete, 1 of 1**
          (`audits/evidence/h2f-fill/delivery-review.md`). The route is the brief's: the release
          adapter inside the phase host, the forwarding leaf, cost `T + 3`/`T + 2`, `C = 3`.
          - It has 20 `fl_` privates and no admission (axioms standard; the sorry walk is empty).
          - The v3 screen is 404/100 → 418/101. The one new pair is in-file, `fl_restore` ←
            `fl_home` at 55%: shared `Fin.addCases` scaffolding, below the 90% copy threshold.
          - Landing next (user, 2026-10-16: prepare clean landings overnight).
          - **Landing PR #114** (`lean/h2f-forwardloop`): the worker's commit cherry-picked from the
            bundle, plus the module status text. Replay `replay-lh2f.sh` covers 4 modules,
            chained after the overnight #112 replay (`oleans-lh2f` from `oleans-lapi`). The
            sorry count drops by one.
          - **Re-pointing candidate (the no-unfolding rule postdates its brief):** the proof
            unfolds StepBlock's `Rep`, `summaryCells`, `outputSummary`, `tableTape`,
            `summaryTape` and `exit`, and `visitedByTapeHead`. Re-point it once those get published
            lemmas. Optional; the fill gate may note it.
      - **U2-S's pre-issue promotion (user, 2026-10-15: "Maintainer PR first"): PR #110**
        (`lean/u2s-prefix-canon`, `cb669b4d`).
        - `prefixCanonTM F`, with `prefixCanon_start`, `_run` and `_complete`, generic in the
          canonizer. `universalCanonTM` and `universalCanon_complete` become its instance, the
          latter's statement unchanged. The parser `universalPrefixTM` is public because the
          generic statements name it.
        - **Replay:** 101 modules (`replay-lpcanon.sh`, snapshot `oleans-lpcanon` from
          `oleans-lwalk`).
        - **U2-S's cleanup (user, 2026-10-15): cite Hydroxyi's `Complexity.LogProg.cleanTM` as it
          is**, with the one import `SpaceComplexity.Machines.Clean` authorized in U2-S's brief.
          The route runs the cleaned canonizer inside `prefixCanonTM`, so `prefixCanon_run`'s
          exact formula gives suffix independence. Capture and placement go through R1′
          (`embedSilentRetTM`).
        - The U2-S brief is drafted. Its inputs are measured after #110 merges.
        - **Landed (2026-10-16, PR #110; replay 101 of 101, failed 0; snapshot `oleans-lpcanon`).**
          #110's own copy-text screen ran after the merge (it had been queued behind the review
          sub-agent's): 111 declarations and 57 pairs before and after, 0 new pairs.
    - **`Turing.universal` at `k = 1`** fits U2-E's statement verbatim. Its re-derivation (U-1)
      waits for U2-E's fill, so a sorry-free theorem does not come to depend on a sorried one.
  - Forwarded to G5's statement phase: `two_work_tapes_run` per run, with the converse; its
    function-level form; `Nat.log 2` in the statements; a per-run export of the alphabet
    reduction.
  - Estimate: about 1.8k–3.3k lines on the hierarchy path (ESTIMATE). The statements of design §13d's G2–G4, stated as
  `Contract`s, then their gate and fills, then the Hennie–Stearns assembly. The open zone rows
  `exists_zoneShiftInTM` and `exists_zoneShiftOutTM` retire through the G3/G4 gate.
  **Started (user, 2026-10-14):** the G2–G4 statement pack is being drafted as `Contract`s over
  MIG-0b's library, with a design note for the two-tape universal machine (linear overhead) in
  parallel. The last step parameterizes the diagonal argument in Hydroxyi's
  `TimeHierarchy/Diagonal.lean` in place, over the universal machine and its overhead, so the
  `f log f` theorem is a corollary: done by the maintainer and the user, no new file (user
  authorization, 2026-10-14).

* **Chapter-2 fill campaign (E1-E5)** — **active** (hold lifted
  2026-10-02 after the ch-6 integration and audit closed). All four
  statement-phase gates closed; 59 audited-true admissions.
  **Epoch/batch partition recorded** in `AroraBarakChapter2Plan.md` §4
  (fill-campaign subsection): E1 assemblies + poly-calculus + formula
  mathematics (batches 1A–1D, 28 targets), E2 enumerator + compilations +
  Ex 2.1/HALT + `TMSAT` (2A–2D, 11), E3 padding + SAT track + snapshot
  locality (3A–3D, 14), E4 the Cook-Levin summit + TAUTOLOGY dual (4A–4B,
  6), E5 closure. Padding moved E2 → E3 (recorded refinement);
  `EXP_subset_NEXP` 1C → 3A (recorded amendment). **E1 integrated 2026-10-02**
  (27/27 targets filled, nine agent commits, freeze audit clean, 32
  admissions remain, zero `sorryAx` across all fills); **epoch-1 gate CLOSED**
  2026-10-02, single round, 0 blockers/majors
  (`audits/ch2-epoch1-resolutions.md`); 27/59 proved, 32 remain.
  Deferred from E1: promotion of 1D's `foldr_max_le_of_forall` **and its
  companion `le_foldr_max_of_mem`** (auditor suggestion) to a shared list
  utility (disposition D3).
  **E2 briefs issued** 2026-10-02
  (`briefs/ch2-epoch2-batch{A,B,C,D}.md`; 10 targets + the mandated
  `timed_universal` bridge statement; inheritances embedded verbatim;
  hardened repo/branch headers; D1 axiom wording).
  **E2 checkpoints integrated 2026-10-03 — all four batches partial, epoch
  gate OPEN** (four Codex commits `da8bd091`…`4b4cd418` off `6c09453e`;
  maintainer verification clean — deleted-lines, surface, replay, fresh
  53-module sweep with 29 direct admissions, axiom-root traversal matching
  every REPORT; logs `audits/logs/ch2-e2-checkpoint-{sweep,axioms}.log`;
  decision-log row in the ch2 plan). 5 of 10 target bodies written;
  admission-free closure: `timeConstructible_poly` only. Uniform frontier:
  concrete machine construction/timed integration (147 helpers delivered,
  145 admission-free). Open sites: 2A's single `enumMachine_contracts`
  (closes `NP_subset_EXP` **and** both HALT targets), 2B's
  `choiceVerifier ∈ P` + untouched reverse direction, 2C's two verifier
  memberships (`CONTINUATION.md` shipped), 2D's `D-MEM`/`D-WRAP`/`D-EMIT`
  (+ the bridge escalation — **RESOLVED 2026-10-03**: Chapter 1 exports
  `Turing.timed_universal_concrete` and the TMSAT bridge is discharged
  via `tmsat_concrete_coefficient` + monotonicity; `TMSAT_mem_NP` now
  roots at `D-MEM` alone, tree admissions 46; decision-log rows in both
  plans). 2C also requests promotion of `prefixTM`/`fixedPair`
  fixed-prefixing lemmas (held with D3; subsumed by Build P3/P6 at the
  shared round).
  Next (sequencing per the frozen library design, 2026-10-03; spec
  layer and bridge export both landed 2026-10-03): the shared
  infrastructure audit pack (Build spec surface + the bridge export and
  its TMSAT discharge) → gate → library fills (harvest-adaptation
  batches; loop flagged for continuation budget) → E2 continuation
  briefs citing the library → epoch-2 audit.
* **Machine-construction library** (`machine-library-design.md`, design
  FROZEN 2026-10-03; decision-log rows in `AroraBarakChapter1Plan.md`):
  `TuringMachine/Build/{Convention,Wrappers,Loop,Primitives}.lean` — 12
  primitives (P1–P12, harvest-heavy), capture/silence + halt-redirect +
  timed cond wrappers, the bounded-loop combinator factored from 2A's
  `enumMachine_contracts`. **Spec layer LANDED 2026-10-03** (design §9a
  refinements recorded): `Cfg.ofWords` seam + pure vocabulary fully
  proved; 18 sorried contracts (4 wrapper, 2 loop, 12 primitive); order
  list and facade at 57 modules. **Bridge export landed 2026-10-03**
  (`Turing.timed_universal_concrete`; TMSAT bridge discharged, tree
  admissions 46). **Infra audit pack prepared 2026-10-03**
  (`audits/ch1-infra-{pack,bundle}.md`). **Round 1: gate OPEN** (blocker:
  `exists_loopTM` refuted by zero-step advances; majors: all-state-word
  round domain, D5 interface gaps). **Round-2 repairs executed +
  re-audit pack prepared 2026-10-03** (`audits/ch1-infra-r2-{pack,
  bundle}.md`): loop redesigned (positive duration, input-indexed `Inv`,
  input-dependent step/accept), `exists_loopFindTM` + P13 `pairConcat` +
  P14 `pairDup` + C1 `pairMapSnd` added, sketches corrected, errata
  acknowledged, historical evidence supplied, D5 re-issued as a concrete
  mapping; Build 22 contracts, tree 50 admissions. **Round 2: 0
  blockers, 1 major, 3 minors** (loops/P13-P14-C1/tables passed; the
  major: the final-answer loop conclusion cannot discharge
  `enumMachine_contracts`). **Round-3 repair executed + pack prepared**
  (`audits/ch1-infra-r3-{pack,bundle}.md`): `exists_loopCfgTM`
  configuration-level export + §9c translation, coefficient-shift and
  pairing-derivation notes adopted, D5 v3 narrowed to epoch-2 + P10;
  Build 23 contracts, tree 51 admissions. **GATE CLOSED 2026-10-03**
  (round 3: 0 blockers/majors, 3 documentation minors swept in the
  closing commit; `audits/ch1-infra-resolutions.md`): the spec surface
  is audited-true, D5 v3 approved (D-MEM explicitly limited; 2B
  component-level; E3/E4 deferred to their brief audits), the
  `enumMachine_contracts` translation certified exactly. **Fill briefs
  issued 2026-10-03** (`briefs/lib-fill-batch{W,P,L}.md`: 4 + 15 + 4
  targets, 14/34/18 pts, P and L with continuation anticipated;
  sanctioned roots `capture_run` → P/L and `exists_loopFindTM` →
  P-splitSolve; L carries the round-3 item-4 construction ledger as
  binding). **Checkpoints integrated 2026-10-03**: W complete (4/4,
  admission-free; `cond` multiplier 5; two promotion requests held for
  the fill-audit round), P 11/15 (frontier `pairLenCheck`; sanctioned
  roots unused), L the 2A pattern (`loop_run` + both summation lemmas
  proved; combinators at the single admitted `loopHost_contracts`;
  `capture_run` consumed in the helpers). Tree: 57/57 zero errors,
  **33 admissions**; size exceptions for `Primitives.lean` (1,687) and
  `Loop.lean` (1,466) recorded. **Continuation briefs issued 2026-10-03**
  (`briefs/lib-fill-batch{P2,L2}.md`, base `90273dd6`): P2 = targets
  12–15 (14 pts; one sanctioned root, `loopHost_contracts` via
  `exists_loopFindTM`, for `splitSolve` only); L2 = `loopHost_contracts`
  (10 pts; zero sanctioned admissions — completion ends the file
  admission-free; the checkpoint agent's continuation document is
  binding). Next: dispatch, then integration, then the library
  fill-audit round (carrying W's two promotion requests and the P/L
  size exceptions), then the E2 continuation briefs.
  **Round 2 integrated 2026-10-04: L2 COMPLETE** (`loopHost_contracts`
  proved; the loop admission-free end to end, realized constant 10),
  **P2 13/15** (12–13 filled via the proved W layer; target-14
  relocation support proved; frontier `pairMapSnd`/`splitSolve`).
  Tree: 57/57 zero errors, **30 admissions**; 21/23 contracts
  admission-free. **P3 closure brief issued 2026-10-04**
  (`briefs/lib-fill-batchP3.md`, base `b2f46419`; targets 14–15, 8 pts,
  zero sanctioned admissions; completion = 23/23, the whole `Build/`
  tree admission-free). **P3 integrated 2026-10-04: `pairMapSnd`
  PROVED (coefficient 40), 22/23**; `splitSolve` reduced to the body
  controller (`splitSolve_of_body` + proved components; one named
  gap). Tree: 57/57 zero errors, **29 admissions**. **P4 closure brief
  issued 2026-10-04** (`briefs/lib-fill-batchP4.md`, base `494d4835`;
  one target, 5 pts, zero sanctioned admissions; the P3 frontier
  document's ten steps are the work plan; completion = 23/23).
  **P4 integrated 2026-10-04: THE LIBRARY IS COMPLETE — 23/23,
  `Build/` admission-free, tree at 28 campaign-only admissions**
  (W 1 round, L 2, P 4; ~250 new privates; every sanctioned root
  closed at merge). **Fill-audit pack prepared 2026-10-04**
  (`audits/ch1-libfill-{pack,bundle}.md`; whole-span attestation:
  net deletions = exactly the 23 placeholders, zero non-private
  additions). **GATE CLOSED 2026-10-04, single round: 0 blockers, 0
  majors, 2 instrument/documentation minors swept in the closing
  commit** (`audits/ch1-libfill-resolutions.md`). **The library is
  complete and audited end to end.** D6 approved-deferred (serial
  promotion of `timed_input_bound`/`timed_rewind`, post-gate); D7
  approved-trailing (the `Loop`/`Primitives` split, ride-along
  audited, with the auditor's cross-file-privates qualification
  binding). **E2 continuation briefs issued 2026-10-04**
  (`briefs/ch2-e2cont-batch{A,B,C,D}.md`, base `64d82f84`).
  **Integrated 2026-10-04: A/C/D COMPLETE, B 1-of-3** — nine of ten
  epoch-2 targets admission-free (enumerator cluster incl. the HALT
  pair; Exercise 2.1; the full TMSAT package); B's one frontier is
  the integrated reverse NDTM host (guessing phase, coverage, and
  normalization banked; five-step plan in its REPORT). Tree: 57/57
  zero errors, **23 admissions**; ch2 ledger **36/59 proved**. Next:
  the B reverse-compiler continuation brief, then the epoch-2 audit.
  **B2 brief issued 2026-10-04** (`briefs/ch2-e2cont-batchB2.md`, base
  `e72d95bf`; 9 pts; zero sanctioned admissions; completion closes the
  epoch at 10/10). **B2 integrated 2026-10-05: EPOCH 2 CONSTRUCTION
  COMPLETE — all ten targets admission-free** (commit `1514fd6b`;
  Theorem 2.6 machine-checked both directions; 42 new `b2*` privates;
  scheduler seam closed by read-normalization, dispatch on the actual
  first halt, definitional table coincidence; independent kernel
  traversal `audits/logs/ch2-e2cont-B2-axioms.log`). Tree: 57/57 zero
  errors, **21 admissions** (5 padding + `EXP_subset_NEXP` + 15 E3/E4
  statement layer); ch2 ledger **38/59 proved**. **Epoch-2 audit pack
  prepared 2026-10-05** (`audits/ch2-epoch2-{pack,bundle}.md` + the
  whole-span attestation under `audits/evidence/ch2-epoch2/`; 34
  attachments). **GATE CLOSED 2026-10-05, PASS in one round: 0
  blockers, 0 majors, 2 minors (audit-material errata, swept via
  `audits/ch2-epoch2-resolutions.md`), 11 notes** — the auditor
  rebuilt all 57 modules from empty oleans and verified all 386
  privates / 1,167 kernel declarations admission-free. **Epoch 2 is
  complete and audited end to end.** The post-gate serial queue is
  unblocked, in order: **D6 promotions — EXECUTED 2026-10-05**
  (`Turing.MultiTapeTM.timed_input_bound` in `Deterministic.lean`,
  symbol-generalized; `Turing.FinTM.timed_rewind` in `Simulation.lean`
  verbatim; Wrappers privates removed, clients on the public API;
  57/57 zero errors, 21 admissions unchanged, promoted lemmas +
  epoch-2 closure regressions all clean —
  `audits/logs/d6-promotion-{sweep,axioms,lint}.log`), then **D7 —
  EXECUTED AS A MEASURED DEFERRAL 2026-10-05**
  (`audits/evidence/d7-split-analysis.md`; tool
  `scripts/d7_split_analysis.py`): pure relocation infeasible — each
  file is one private family (96–99.9% span); compliant splits need
  ≥ 125 cross-file promotions program-wide (34/43/24/16/8 per file),
  intersecting E5's live-replacement/deletion sets, so the physical
  splits run **after E5** via one internal-namespace visibility
  proposal, ride-along reviewed in the E3 pack (pilot: the
  Nondeterminism forward/reverse cut, cost 5); size justifications
  stand — then **E5 — EXECUTED 2026-10-05, deletion-only** (the three
  inventoried dead families removed: 28 privates, 549 lines; EXP
  2,887 → 2,534, Nondeterminism 2,627 → 2,454; live routes untouched;
  contract-evidence lemmas deliberately retained; 57/57 zero errors,
  21 admissions unchanged, closure regressions PASS —
  `audits/logs/e5-dedup-{sweep,axioms,lint}.log`; D7 re-measured
  post-E5: 34/43/24/13/8, deferral confirmed). **The post-gate serial
  queue is complete.** **E3 briefs issued 2026-10-05**
  (`briefs/ch2-epoch3-batch{A,B,C,D}.md`, base `b55180a8`; 3A padding
  cluster 26 pts / 3B SAT track 24 pts (continuation anticipated) / 3C
  snapshot locality 22 pts / 3D TAUTOLOGY membership 6 pts; zero
  sanctioned admissions; completion closes the E3 statement layer at
  15 targets). **Integrated 2026-10-05: C/D COMPLETE, B 2-of-3, A at
  the exponential split body** — 8 new closures (the five snapshot
  locality lemmas, both SAT memberships, TAUTOLOGY membership); tree
  57/57 zero errors, **13 admissions**; ledger **46/59 proved**. Two
  new size exceptions recorded (SAT 2,363; Tautology 1,278). A's
  frontier: the native exponential split-search body existential
  (five-step plan in its REPORT; 35 `e3_*` privates banked). B's
  frontier: run lemmas + time proof for `satRedTM`'s streaming states
  9–34 (startup proved; all reduction mathematics banked).
  **Emitter-increment design drafted 2026-10-05**
  (`machine-library-design.md` §11, awaiting decisions 11.1–11.3:
  `emitLoop` + `emitPhase` + P16–P18 + width-parametric split search;
  ≈ 27 pts; 3B-cont and 4A are the customers). **3A-cont brief issued
  2026-10-05** (`briefs/ch2-e3cont-batchA.md`, base `b75b6771`,
  bespoke in parallel with the design review; zero sanctioned
  admissions). §11 approved 2026-10-05 (11.1–11.3); **emitter spec layer
  landed** (5 sorried contracts + 2 transformers + 2 vocabulary defs;
  57/57 zero errors, 18 = 13 + 5 admissions exactly; regressions
  PASS) and the **emitter-infra audit pack prepared**
  (`audits/emitter-infra-{pack,bundle}.md`, 14 attachments; gate on
  zero blockers/majors, findings to
  `audits/emitter-infra-findings.md`). 3A-cont dispatched by the user
  (bespoke, independent); **integrated 2026-10-05 as a verified
  partial checkpoint** (69 `e3c*` privates banked — the full phase
  family for the split-search body; zero targets closed, zero new
  admissions; a maintainer base-hash erratum in the brief was caught
  by the agent and is recorded with its process correction). **Round 1: 0 blockers / 2 majors / 3 minors** (adequacy, not
  falseness); repairs landed (the two clean-call bridge contracts in
  `Loop.lean`, the 3B/4A mappings in §11b, the forwarding-host sketch
  correction, token/doc sweeps; 57/57 zero errors, 20 = 13 + 7
  admissions; full-print regressions PASS) and **round-2 pack
  prepared** (`audits/emitter-infra-r2-{pack,bundle}.md`, 31
  attachments incl. the evidence addendum both majors demanded).
  **Round 2: 0 blockers / 2 majors / 1 minor** (R1 3–5 closed;
  constructions validated); **round-3 repairs landed** (`0 < C.k` on
  both bridges — the zero-tape degeneracy; §11c's corrected 4A
  stage-to-seam mapping superseding §11b item 3; the §11a marker) and
  the **round-3 pack prepared** (36 attachments incl. the phase-4
  reaudit table and the A-cont `e3c*` provenance). **A-cont-2 brief issued
  2026-10-05** (`briefs/ch2-e3cont-batchA2.md`, base `d5ac2377`,
  rev-parse-verified; targets 2/4/5 only — 1/3/6 deferred to
  post-fill instantiation via `splitSolveWith`; ≈ 13 pts, zero
  sanctioned admissions, dispatches in parallel with the r3 audit).
  **EMITTER GATE CLOSED 2026-10-05** (round 3: 0/0/1 —
  `audits/emitter-infra-resolutions.md`; the attribution minor swept
  comment-only in the closing commit; binding fill/brief handoffs
  recorded). **Fill briefs issued 2026-10-05**
  (`briefs/emitter-fill-batch{L,P,W}.md`, base `d7b5b6f9`; L ≈ 17 pts
  bridges-then-emitLoop via the forwarding host, P ≈ 10 pts
  splitSolveWith under the gate disciplines, W 3 pts emit_run; zero
  sanctioned admissions each; the `e3c*` family as harvest template;
  completion drops the tree 20 → 13). **W integrated 2026-10-05**
  (`emit_run` proved, one private, Wrappers admission-free; spec
  7 → 6). **A-cont-2 integrated 2026-10-05**: the exponential
  reverse host closed (29 `a2*` privates; B2 host + native binary
  countdown); targets 4/5 escalated over a recorded maintainer
  scoping erratum (the Thm 2.22 route cites the excluded
  `EXP_subset_NEXP`) and move to **A-cont-3, now covering 1/6/3/4/5**
  post-`splitSolveWith`. **P integrated** (2/3: appendBit + unaryToken closed;
  `splitSolveWith` at the body wall with 83 privates banked incl.
  the whole-bank cleaner `emitterBankTM` + the conditional
  `emitterSplit_of_body`). **L integrated — COMPLETE 3/3**
  (`Loop.lean` admission-free, 5,713 lines, 119 privates; unified
  `emCallTM` bridge controller at the audited envelope; forwarding
  host + `emLoop_sum`). **The emitter layer stands at 6/7**; tree at
  **13 admissions** (12 campaign + `splitSolveWith`). **P2 brief issued 2026-10-05**
  (`briefs/emitter-fill-batchP2.md`, base `08884731`; the last
  contract against the predecessor's five-step plan, with the proved
  W/L layer now citable and L's `emCallTM` as the controller
  precedent; completion = emitter 7/7, tree 12). **P2 integrated 2026-10-05 — THE
  EMITTER LAYER IS COMPLETE (7/7, `Build/` admission-free)**: the
  split-search body closed via the proved install bridges in one
  round — the increment's thesis confirmed at first consumption; 68
  privates; tree at **12 admissions, all campaign**. **Fill-audit pack
  prepared 2026-10-05** (`audits/emitter-fill-{pack,bundle}.md`, 22
  attachments; whole-span attestation name-exact at 271 privates;
  gate on zero blockers/majors, findings to
  `audits/emitter-fill-findings.md`). **FILL GATE CLOSED 2026-10-05, PASS
  in one round (0/0/2/7)** — the emitter increment is complete and
  audited end to end (`audits/emitter-fill-resolutions.md`; both
  minors maintainer errata, swept). **The closing wave is dispatched-ready
  2026-10-05**: A-3 (`briefs/ch2-e3cont-batchA3.md`, 1→6→3→4→5 via
  `splitSolveWith`; zero sanctioned), 3B-cont
  (`briefs/ch2-e3cont-batchB.md`, the emit-loop rebuild under the
  r2-finding-5 schedule; zero sanctioned), 4A
  (`briefs/ch2-epoch4-batchA.md`, the summit under the embedded
  boundary table; one sanctioned root via 3B-cont for the SAT3
  pair; Astra distillation explicitly non-binding). **A-3 (run β of a
  recorded parallel-run incident; α discarded whole under logged
  criteria) and 3B-cont integrated 2026-10-05**: the padding cluster,
  `EXP_subset_NEXP`, and `SAT_reducible_SAT3` closed; tree at **6
  admissions** (`TAUTOLOGY_coNPComplete` + Hardness five); ledger
  **53/59**. **4A checkpoint integrated 2026-10-05**: 1/5 closed +
  77 privates banking the summit's whole pure layer (tableau,
  product encoding, chunk-exact serialization identity, quadratic
  ledger, oblivious normalization, certificate call, conditional
  emitter assembly); frontier = the packed-record producer, the
  round controller, equisatisfiability (four-step plan); tree at
  **5 admissions**; ledger **54/59**; Hardness 1,193 lines (new
  recorded exception). **4A-2 brief issued 2026-10-05**
  (`briefs/ch2-epoch4-batchA2.md`, base `f815da30`; the four-step
  plan binding; sanctioned root withdrawn — zero admissions
  sanctioned; producer = the checkpoint boundary).
  **4A-2 native-preparation checkpoint integrated 2026-10-06**
  (Codex `a4ca9302`): a verified partial *earlier* than the
  complete-producer boundary — **52 new proved privates** for the
  native preparation phase (the exact arithmetic header
  `clPrepHeader`, the all-false reference simulation
  `clRef*`/`clRefClock*` identified with the public
  `oblivious_schedule`, the in-place binary counter `clCount*`
  with carry/rewind re-proved on a silent absorbing machine, and
  the `clRefCount*` administrative frame); **no target closed,
  zero new admissions**, tree still at **5 admissions**, ledger
  **54/59** unchanged; Hardness.lean now 2,112 lines (size
  exception continues). Verification independently reproduced
  (checksums 25/25; freeze 919/0; byte-identical replay; 57/57
  sweep; whole-module traversal = 375 decls / 4 sorry roots; lint
  0 FAIL / 1 WARN; `audits/logs/e4A2-checkpoint-*`). **4A-3
  frontier**: the complete packed-record producer (trajectory +
  signed-position records + greatest-strictly-earlier last-visit
  search with a sequential-access ledger), genuine `initCfg`
  startup, the ordered emission controller under common budget
  `P` ≠ `T`, and the output-identity-then-equisatisfiability
  close. **4A-3 brief issued and the recording checkpoint
  integrated 2026-10-06** (Codex `9f1808a6`): **150 more proved
  privates** — the stored inclusive trajectory (`clRec_complete`,
  rows `0..T`, silence + `(4l+7)(T+1)²` cost + `2l(T+1)²` length),
  signed/clamped tracking, the cross-sum comparator, the charged
  sequential field reader — no target closed, zero new admissions,
  tree still at **5 admissions**, ledger **54/59**; Hardness.lean
  4,471 lines (exception continues); three-pass traversal 757
  decls / 4 roots / kernel surface = the five theorems
  (`audits/logs/e4A3-checkpoint-*`). **4A-4 frontier (still step 1,
  components complete — producer assembly is the minimum bar)**:
  header unpacking, row loader + greatest-strictly-earlier search
  with scratch resets and one charged ledger, the complete
  producer, then startup, the controller under `P` ≠ `T`, output
  identity, equisatisfiability. **4A-4 complete-producer checkpoint
  integrated 2026-10-06** (Codex `8e2d7ee1`): **step 1 closed** —
  `clPackedRecords_machine` proves the entire packed result (header +
  inclusive trajectory + full greatest-strictly-earlier visit table)
  from native input in one machine with total ledger `a*(|x|+1)^r`;
  176 new privates (455 total); no target closed, zero new
  admissions, tree still at **5 admissions**, ledger **54/59**;
  Hardness.lean 7,446 lines (exception continues; prime
  routine-layer retrofit target); three-pass traversal 1191 decls /
  4 roots / surface = five theorems
  (`audits/logs/e4A4-checkpoint-*`). **4A-5 frontier (the body,
  expected to close the gate)**: final install with the producer +
  genuine `initCfg` startup → ordered controller with common budget
  `P` (≠ `T`, ≠ producer ledger) → `clEmitter_of_body` +
  `clTableau_chunks` output identity → pure equisatisfiability;
  sanctioned checkpoint only at the proved output identity.
  **4A CLOSED 2026-10-06** (Codex `57507830`+`06ce95fa`): the
  five-target completion gate passes — Cook–Levin machine-checked
  end to end on the campaign's own audited model; `SAT_NPHard`,
  `SAT_NPComplete`, `SAT3_NPHard`, `SAT3_NPComplete` all empty
  roots at the standard triple; `Hardness.lean` admission-free
  (9,937 lines, 618 privates — THE prime routine-layer retrofit
  target); net deletions = exactly the four authorized `sorry`
  bodies; no-allowlist traversal 1550 decls / 0 sorryAx / surface =
  five theorems (`audits/logs/e4A5-closure-*`,
  `audits/programs/ch2-e4A5-ClosureAxioms.lean`). **Ledger 58/59;
  tree at 1 admission** (`TAUTOLOGY_coNPComplete`). **4B brief issued 2026-10-06**
  (`briefs/ch2-epoch4-batchB.md`, base `b133a3d4`; the docstring
  route binding; new DNF names binding; fallback-flips-sides and
  empty-term/empty-DNF pitfalls pinned; ≈ 7 pts; completion = the
  campaign tree admission-free). **4B CLOSED 2026-10-06** (Codex
  `9e9494aa`): `TAUTOLOGY_coNPComplete` via the audited dual route —
  the five definitional links + the `R(n)=0` one-round emit-loop
  transducer (28 privates, linear time); **ledger 59/59, the
  campaign tree at ZERO admissions** — the whole 65-module surface
  (11,436 kernel declarations) admission-free
  (`audits/logs/e4B-closure-*`,
  `audits/programs/ch2-e4B-ClosureAxioms.lean`). → the epoch-3/4
  audit pack — **GATE CLOSED 2026-10-06, PASS in round 3** (0 blockers /
  0 majors cumulative; findings/resolutions on record)
  (ride-alongs included: colleague's DNF adaptation, the parallel-run
  provenance, the discarded α hash, **colleague merge #2's 9-module
  private rewiring + the 57→65 order extension**) → E5 closure — **phase 1 complete 2026-10-06**
  (dedup 153 privates, drift attestation CLEAN, closure pack,
  zero-sorry sweep + traversal PASS); **phase 2 (blueprint
  increment) pending a user decision on the dep-graph refresh**
  (stale `dep_graph.json`; refresh needs the banned build —
  options: one-off artifact build in a throwaway worktree, or
  defer past the main merge) → the machine-routine layer +
  retrofit (recorded decisions).
  Subsumes 2C's
  `prefixTM`/`fixedPair` promotion requests. Dedup of superseded batch
  privates is an E5 closure task — **auditor-adopted live/dead guidance (epoch-3/4 round 1, finding 14)**: `clFill*` → producer path is LIVE; `clCertificateCall` and `clTrack_schedule` dead at source; `e3c*` mixed (`e3c_bits_injective` live); SAT's max-pass prefix live; dedup from a kernel-derived inventory, never by prefix or checkpoint label. Also queued for the retrofit: the 11 disclosed generated kernel artifacts (imported-definition equation lemmas + the private-structure `deriving` instance in SAT.lean). Mathlib TM2 rejected as substrate
  (evaluation recorded in the ch1 decision log).
* **Machine-routine layer (user decision 2026-10-06: build once
  chapter 2 is done, in the E5-closure/D7 window, before chapter 3).**
  Three pieces, sized by the A-chain's evidence (≈ half of the A2/A3
  deliveries' 202 native privates are hand-rebuilt universal routines;
  `emitterBank*`/`emitterP2*` relocation privately re-harvested three
  times; A3's proved costs `3|w|+3` copy / `2|w|+2` clear match the
  prior art's `3w+2`/`2w+2` to within one step):
  1. a generic **bank-embedding theorem** — a verified routine on its
     own small tape set runs on any selected tape subset of a `k`-tape
     machine, cost unchanged, all other tapes/heads framed (the public
     generic form of `emitterBank*`/`clBank*`/`clSlot*`);
  2. a generic **seam-composition lemma** — sequential composition of
     two controllers at a canonical `Cfg.ofWords` seam with first-return
     cuts and additive budgets (the generic form of the per-batch
     dispatch gluing);
  3. **catalog promotion** of transfer/clear/copy/compare/increment as
     public machines with exact costs, seeded from the already-audited
     A-chain privates (D6-style promotion, not new proof work).
  **Survey update 2026-10-06 (pre-§12, recorded ahead of the
  colleague meeting 2026-10-07)**: the colleague's ch6 merge already
  supplies the **function-level half** of this layer —
  `TuringMachine/CounterProg{,Run}` (goto programs over unary
  registers, compiled once into `FinTM`, `t` abstract steps ≤
  `t(2t+3)` machine steps, FP bridge), `ClassNP/Transducer` (Mealy
  machines as work-tape-free FinTMs in `|x|+1`), `ClassNP/
  PolyTimePairing`/`PClosure` (FP/`P` closure, built ON our audited
  catalog), `UnaryTape`. The §12 design must **consume, not
  duplicate** these; the remaining gap is the **config-level half**
  (bank-embedding, seam-composition at canonical `Cfg.ofWords`
  seams — the emitter r1 finding stands: function contracts cannot
  deliver clean-return seams) plus residual catalog promotions.
  Items for the meeting: colleague roadmap (more campaign-module
  rewiring?), `CounterProg` as general substrate vs. sibling
  module, `Build/*` ownership during the retrofit window, ch3/
  TimeHierarchy alignment. Citation duty now extends to the
  colleague's modules alongside lax-434930.
  Mechanism: a design addendum (`machine-library-design.md` §12) →
  statement gate → fills → audit, folded into the queued D7
  internal-namespace visibility proposal. **Citation discipline
  (binding, user guideline 2026-10-06): diligently cite the code this
  adapts — the design is inspired by Édouard Bonnet's
  `classical-complexity` (Lax Archive lax-434930), module
  `proofs/Lax434930Proofs/InclusionAux/TimeCompiler/` (StackProgram's
  `compile_correct`, StackRename's `rename_executes`/`executes_in_sum`,
  and the transfer/clear/copy/for/repeat routine catalog), commit
  `0c0840319318215fd7b36a9a822b81ce55cf6941`, Apache-2.0. The §12
  addendum, the affected module docstrings, and the blueprint entries
  must each carry this citation. Adapt design, never code: different
  toolchain (their Lean 4.33 / our 4.25) and machine model (TM2 keyed
  stacks vs FinTM tapes with heads); nothing is imported or
  transcribed, and the external files stay out of the repo.**
* **`Build/` catalog layout refactor toward per-theme files (queued;
  user decision 2026-10-08, §12 open decision 12.2).** The routine layer's
  new catalog rows land in a single `Build/Catalog.lean` (option (a)) to
  keep the audited `Primitives.lean` byte-identical; once the retrofit
  shrinks the `Build/` files, refactor the catalog toward the symmetrical
  per-theme layout (option (c): `Build/Catalog/{Transfer,Arith,…}.lean`),
  folded into the queued D7 split window. *Origin:
  `machine-library-design.md` §12, decision 12.2.*
* **Retrofit pass over chapters 1–2 with the routine layer (user
  decision 2026-10-06: queued as backlog, explicitly important — to be
  done at some point, not time-bound).** Once the machine-routine layer
  is audited, revisit the existing ch1 and ch2 formalizations —
  Cook–Levin included — and simplify them against it: replace the
  privately re-derived bank/relocation/dispatch/frame families
  (`emitterBank*`, `emitterP2*` relocation, `clBank*`/`clSlot*`,
  `clCopy*`/`clCmp*`/`clRead*`/`clCount*`, and their ch1 analogues in
  `Build/Primitives.lean`/`Build/Loop.lean`) with catalog citations and
  the two generic theorems. Expected effect: large private-count and
  line-count reductions in the five size-exception files, directly
  serving the deferred D7 splits. Statement freeze applies — public
  surfaces never change; every replacement batch goes through the
  standard sweep + traversal + audit protocol. Prerequisite: the
  machine-routine layer's gate is CLOSED.
  **Inventories + partition recorded 2026-10-09** (plan §4d; verbatim
  reports `audits/retrofit-inventory/`): realizable conservative scope
  ≈ −98 privates / −1,900 lines, dominated by dead code (`emitterBank*`
  itself is dead — delete, not port); the R1/R2/catalog-shaped glue is
  overwhelmingly LEAVE under the strict-simplification bar (monolithic
  hosts, loop back-edges, canonical-only rows, missing selected-tape
  exports). Batches RB1 (Loop) / RB2 (Primitives) / RB3 (Hardness),
  `Universal*` excluded; **integration by side branch + PR, user merges
  manually** (user rule 2026-10-09). Decisions D-R1 (Embed selected-tape
  exports, proposed to ride the §13 Z1 gate), D-R2 (Primitives ownership
  — option (a) deferred to 12.2c with feasibility proven; stretch (c)
  inside RB2), D-R3 (machine-agreement transfer lemma, deferred) are in
  §4d. The artifact-count note above corrects to **12** generated kernel
  artifacts, located in `Nondeterminism`/`EXP`/`SAT`, none in Hardness.
* **Audit-mandated fill-brief inheritances** (each brief must carry these
  verbatim from the cited records):
  - `NP_subset_EXP` enumerator: the contract-by-contract table —
    `audits/ch2-phase1-round3-findings.md` (via `…-resolutions.md`).
  - NTIME/Theorem-2.6 compilations: the simulator invariant tables and
    branch-correspondence contracts — `audits/ch2-phase2-findings.md`
    (note 3: no untimed composition or bare computability substitutions).
  - `TMSAT_mem_NP`: the `PolyBound` budget chain and the **new public
    quantitative bridge** for `timed_universal`'s constant — one simulator
    chosen before code and input, both success and timeout clauses, the
    suggested form `(3|α| + 14·canonizerTime(|α|) + 50)·(t+1)²` avoiding a
    `PolyBound` import into Chapter 1; Chapter-1 surface growth via the
    shared-file mechanism, flagged for its own audit —
    `audits/ch2-phase3-{findings,reaudit-findings,resolutions}.md`.
  - `TMSAT_NPHard`: exact-value emission case table and the explicit `T'`
    deadline formula (never majorize the certificate length) — same records.
  - Cook-Levin emitter (E4): the six-stage output-silence contract **and**
    the round-2 boundary-check table, the product snapshot encoding, and the
    exact serialization-length ledger (never constant-per-clause) —
    `audits/ch2-phase4-{findings,reaudit-findings,resolutions}.md`.
  - Locality fills: strict `s < t` in `prevVisit`; keep no-write and
    write-blank distinct (`some none` erases); writes on the halting
    transition count — phase-4 Derivation A.
  - `TAUTOLOGY_mem_coNP`: the DNF evaluation-congruence bridge as a private
    lemma — phase-4 round 1, note 6.
* **Chapter-2 blueprint increment** — at campaign closure (E5), per the
  Chapter-1 precedent (dep-graph merge, writer agents, validator).
* **P3.4 — Ladner's theorem (queued; user decision 2026-10-08: CH34-Q6
  core-late, moved to backlog at the P3.3 draft).** The last undrafted
  statement phase of the chapters-3-4 campaign
  (`AroraBarakChapters3-4Plan.md` §4): `Diagonalization/Ladner.lean` with
  `SAT_H` (SAT padded by the diagonal gaps of `H`), Ex 3.6(a) (`H`
  computable in polynomial time), the Claim of [AB09, Theorem 3.3]'s proof,
  Ex 3.6(b), and Theorem 3.3 itself (`P ≠ NP` gives an `NP`-intermediate
  language), ~6 sorried statements. Draft when the live rounds settle (the
  `Diagonalization.lean` facade unfreezes at the P3.2 close); it consumes
  the closed chapter-2 `SAT` surface and the received `polyTimeComputable`
  layer, and is independent of P3.3's code layer. *Origin:
  `AroraBarakChapters3-4Plan.md` §4 (P3.4 row), decision CH34-Q6.*
* **ARM extensions + colleague sync (moved to backlog 2026-10-09; user
  decision — outreach to Hydroxyi/Jason Dong initiated the same day).**
  The three proposed extensions to the co-owned `LogProg` tree
  (`AroraBarakChapters3-4Plan.md` §2.5), each a future infrastructure
  statement phase with its own audit gate once agreed: (1) a
  **nondeterministic ARM** — a `choose` instruction compiling to
  `FinNDTM` with the space theorem carried over (customers: `PATH ∈ NL`,
  Immerman-Szelepcsényi, Cor 4.21); (2) a **polynomial-width ARM
  variant** — `poly(n)`-bit registers for the `PSPACE`-level algorithms
  (`TQBF ∈ PSPACE`, `NP ⊆ PSPACE`, Savitch at polynomial level); (3) the
  **configuration codec as a program** — extends Hydroxyi's deterministic
  `ConfigCount` to NDTMs, adapting (citing, never vendoring) cslib's
  upstream `ConfigBound` design. Also on the sync agenda: `CounterProg`'s
  one-way input (the `2^O(S)` searches need indexed access or a rewind
  instruction), and the two citation-audit provenance questions, asked as
  questions (their `LogProg` compiler vs lax-434930's `TimeCompiler`;
  `ConfigCount.core` vs cslib `ConfigBound`'s `Cfg.core`). Also a
  received-code duplication observation, from the B7 fill gate's closure
  (`audits/b7-fill-resolutions.md`): `Machines/Bin.lean::bits_getLast`
  reproduces `Machines/FragDec.lean::bits_head_odd` at 90%. These are two
  `Nat.bits` lemmas proved by the same strong induction, both received in
  `f70c57c2`; it is offered as a possible shared helper. **Blocks fills
  only, never statements**: the machine-heavy P4.x fills named above plus
  the ARM interface statements deferred out of P4.1; every other fill
  epoch and the retrofit proceed. Returns to the plan on Hydroxyi's
  reply. *Origin: plan §2.5, §4a/§4b stage 1, CH34-Q2; the 2026-10-08
  citation-audit row.*
  **Update (user, 2026-10-12; design §16b item 4):** C2 is written as
  programs with read-once coins and compiled by stage 2, so the campaign
  no longer needs extension (1). Extension (2)'s remaining customers,
  Savitch and TQBF membership, are programs of the language too (design
  §16, decision 3; MIG-22; `NP ⊆ PSPACE` is proved at machine level), and
  extension (3) is replaced by the language's machine-configuration
  routines (design §15c). The rest of the sync agenda stands. Hydroxyi
  should be told when next in touch (the user's call).
  **Reply received and merged (2026-10-14).** Hydroxyi accepted all three extensions, added a
  fourth (MARM, a monotone memory tape with a time bridge) and proved the customers:
  `PATH_NLComplete`, `compl_PATH_mem_NL`, `NL_eq_coNL`, `NSPACE_compl_eq`, `TQBF_mem_PSPACE`,
  `TQBF_PSPACEHard`, `TQBF_PSPACEComplete`, `PSPACE_eq_NPSPACE` and `NSPACE_subset_exp_dtime`
  (which moved, with `NL_subset_P` and `polyTimeReducible_of_mem_NL`, to
  `SpaceComplexity/ExpTime.lean`). The merge `8c23f3bc` (74 files added, 8 changed) was pushed
  directly to the campaign branch, not by PR; the reply is `arm-extensions-response.md`. No
  statement of ours changed (maintainer freeze). The classes stay defined at Turing-machine
  level: ARM programs enter only through bridge theorems whose conclusions are statements about
  `FinTM`/`FinNDTM`. Their answers: `CounterProg` keeps its one-way input (ARM's indexed access
  serves the searches), and both provenance questions are answered no. **User (2026-10-14):** a
  fill-style external gate of the received code; the payback promotions in a separate PR after
  the B6 hosts; RD-2's fills held; stage 2 paused. §1 ARM-1 records the duplication and the payback decisions; §1 ARM-2 the
  refactor to coordinate with Hydroxyi.

---

## 3. Deferred formalizations

### Chapter 1

* **Phase 5 (deliberately unscheduled; "a task for much later"):** the
  `O(T log T)` oblivious simulation ([AB09] §1.7 / Ex 1.6); the RAM-TM
  exercise (Ex 1.9); a fuller mathlib recursion-theory bridge beyond the
  `MathlibBridge` quarantine. *Origin: ch1 plan §5, decision of 2026-09-16.*
* **Waived model bridges** — revisit only if a downstream result ever needs
  a formal bridge: the append-only-output and start-marker-initialization
  conventions vs. [AB09]'s model (no read-write-output machine is
  formalized; no exact [AB09] step count is ever imported). *Origin: ch1
  plan §5 phase-2 notes; ch1 phase-2 audit findings 3/13.*
* **`Universal.lean` factoring** — 2831 lines (escalation recorded at
  epoch 4A): ~1100 lines are stopped-interpreter administrative copies
  forced by per-module `match` auxiliaries; the 4A report's three
  shared-lemma generalizations are the designated future factoring. Also
  CH1-Q2(a)'s promotion candidates. *Origin: ch1 decision log, epoch-4A row.*
* **Polynomial canonizer for a concrete scheme** (CH1-Q1(c) continued):
  Chapter 2's `TMSAT_mem_NP`/`TMSAT_NPComplete` now carry the hypothesis
  `PolyBound c.canonizerTime`; a combinator-built effective scheme with a
  *proved* polynomial canonizer would discharge the hypothesis for a
  concrete scheme and reconnect Q1(c). *Origin: ch2 phase-3 audit.*
  **Now stated** as `Turing.MachineFormat.exists_polyCanonizer`
  (`CodeSimulator.lean`, design §12.11, filled with B5a). Its one-tape
  instance discharges the hypothesis for a concrete scheme, an off-batch
  customer.
* **Blueprint planner refinement** — writers flagged planner `\uses` edges
  not present in the cited proofs (reproduced verbatim per pipeline rules).
  *Origin: ch1 decision log, blueprint-extraction row.* **Ch2 increment
  instances (2026-10-06/07)**: `NPHard.polyTimeReducible` → `clLastRound`;
  `clA5Equisat` → `SAT_NPHard` (forward edge); `sat_comp_on_image` → `SAT`;
  `satHost_clean` → `SAT_reducible_SAT3` (forward edge);
  `choice_certificate_iff` → `capturedSummary`; `cont_split_bridge` →
  `contPairTM`; `goes_loop` → `run_pos_le`, `MOp`;
  `pairedVerifier_malformed` → `paddedVerifier`; `emit_run` → `redirectTM`;
  `taut_membership_of_verifier` → `TautSyntax`; `taut_machine_pair` →
  `tautSplit` (forward edge); `foldr_max_le_of_forall` →
  `falsifyingClause_eval_false`; `polyTimeComputable_of_linear` →
  `pairMapSnd`; `PolyTimeReducible.trans` → `mem_P_of_polyTimeReducible`;
  `acceptTM_halts_iff` → `prefixTM`. The forward edges (a helper "using" the theorem it serves)
  suggest the planner attributes by source-range adjacency or docstring
  mentions rather than by kernel dependency; the kernel walker used for the
  E5 dedup could supply exact edges.
* **Blueprint `\difficulty` calibration across writers** — parallel
  writers split on trivial structural inductions whose cases each close in
  one line: some rate them 3 (no real branching), others rubric-literal 4
  (any induction or case split). Observed in the ch2 increment (NP,
  Snapshot, CNFEncoding at 3; Nondeterministic, CounterProg at 4). The
  dataset would benefit from one normalization pass, which is mechanically
  detectable from the proof source; or tighten the rubric text in the
  writer agent definition. *Origin: blueprint-writer reports, ch2
  increment parts 2–3.*
* **For the colleague: `ClassNP/PClosure.lean` docstring/statement gap** —
  the `lenEq_mem_P`/`lenLe_mem_P` docstrings speak of *pairs*, but the
  languages range over all bit strings, the total projections sending a
  non-pair to the empty word (so every non-pair lies in the `lenEq`
  language). The statements are fine; the docstrings undersell their
  domain. The blueprint documents the Lean behavior. *Origin:
  blueprint-writer report, ch2 increment part 4.*
* **Blueprint-writer process fix: require the per-entry strict check** —
  in the ch2 increment, writers that ran `statement_quality.py` /
  `dataset_hygiene.py` from the command line were grading the dataset
  *cache*, not their chapter, and every one of the 178 strict-rubric
  flags came from exactly those five writers (SAT, Primitives, EXP, CoNP,
  PClosure); writers that imported `check(..., strict=True)` and ran it
  per entry produced zero. Fix: state the per-entry function-call check
  as a hard requirement in `.claude/agents/blueprint-writer.md` (and
  ideally add a `--chapter` mode to the scripts). The orchestrator-side
  uniform pass used here (`build_dataset.parse_blueprint` + both checks,
  names demangled via `PRIVATE_RE`) could also become a `/blueprint-
  extract` step. *Origin: ch2 increment, 2026-10-07.*
* **Stale module docstring: `Build/Primitives.lean`** — still says every
  theorem below is sorried; the emitter fill gate closed every one of them.
  Comment-only fix, eligible for the next comment-only sweep (comment-
  stripped byte-identity check per precedent). Same sweep: the
  `emitterP2EraseCfg` docstring says the input stays "at its origin", but
  the definition places the head at position 1 (the first input cell) —
  the blueprint now states the Lean behavior. *Origin: blueprint-writer
  reports, ch2 increment parts 1 and 6.*

### Chapters 2-3

* **§2.4 web of reductions** (`INDSET`, `0/1 IPROG`, `dHAMPATH`, exercise
  problems) — each needs a graph/arithmetic encoding surface; the legacy
  `Complexity/NPReductions/*` files may eventually be **retargeted** as the
  structure-level halves (see §5). *Origin: ch2 plan §1.*
* **§2.5 decision-versus-search** (Theorem 2.18). *Origin: ch2 plan §1.*
* **Parsimonious and Levin reductions** ([AB09] §2.3.6). *Origin: ch2 plan §1.*
* **Ex 2.6, the universal NDTM** — Chapter 3's tool. *Origin: ch2 plan §1.*
* **Ex 2.30, Berman's theorem.** *Origin: ch2 plan §1.*
* **General Boolean formulas** — `TAUTOLOGY` is deliberately stated on the
  documented DNF fragment; a general-formula carrier (AST, evaluation,
  serialization) is new work, and any future general `TAUTOLOGY` must not be
  silently identified with the fragment. *Origin: ch2 phase-3/4 audits.*
* **`MathlibBridge` poly-time upgrade** (open lever): `bridgeTM` costs O(1)
  native steps per TM2 operation, so a Mathlib `TM2ComputableInPolyTime`
  certificate would transfer. (The Chapter-6 bridges were built on native
  machines without it; see §3.)
  *Origin: ch2 plan decision log ("revisit at phase 3" — still open).*
* **Oracle complexity classes** (Chapter 3): `Oracle.lean` has the raw model
  and both lockstep embeddings, audited; the class layer, the
  persistent-vs-auto-erased query-tape statement (polynomial overhead only —
  constant overhead provably impossible), and relativization (Baker-Gill-
  Solovay) are future Chapter-3 work. *Origin: ch1 plan §5 phase-2 notes;
  session assessment 2026-09-18.*
* **B5a linear headline (formerly "B5a headline H2", renamed 2026-10-13 to avoid confusion with host H2): the per-code-linear timed simulator** (user, 2026-10-11:
  "H1 for now, but add H2 to backlog"). `CodeSimulator.lean`'s headline is
  H1, polynomial in `|α| + |x| + t` jointly, which is exactly what the two
  uniform schemes need. **H2** gives the same verdicts within
  `d · (|α| + 1)^d · (t + 1)`, with no `|x|` term and linear in `t` per
  code. It would make the one interpreter the stage-1 timed universal at
  linear overhead. It needs a **suffix-input host**: the simulated machine
  reads `x` in place inside the native input, behind a left-boundary
  marker. The pieces are public (`universalInput_read`/`_move`,
  `UniversalStartup.lean`), but no host composes them. H2 ⇒ H1 is already
  proved (`exists_uniformSimulator_of_timed`, B5a statement probe), so H2
  can later be added beside H1 without disturbing its consumers. The step
  block's per-round cost is independent of `t` and `x`, so the B5a fill's
  trace is the H2 core. H2 is also the natural route for 12.2c item **U-1** (§1).
  *Origin: B5a dossier D3; design §12.11.*

### Chapter 6 (Arora–Barak §§6.1–6.5): what is proved, and what remains

The machine-facing Chapter-6 bridge theorems this section used to list are all
**proved, sorry-free** (headline `#print axioms`: `propext`, `Classical.choice`,
`Quot.sound` only), over the book's DAG model `BoolCircuit.DAGCircuit`:

* Thm 6.6 `P ⊆ P/poly` — `Complexity.P_subset_PPoly` (oblivious tableau,
  `CircuitComplexity/PSubsetPPoly*.lean`); `P ⊊ P/poly` (p. 110) —
  `Complexity.P_ssubset_PPoly`, with the machine-model `UHALT`
  (`Complexity.UHALT_not_mem_P`, `UHaltMachine.lean`).
* Lem 6.10 / 6.11 — `BoolCircuit.dagCktSatLang_NPComplete`,
  `BoolCircuit.dagCktSatLang_polyTimeReducible_SAT3`, and Cook–Levin via circuits
  `Complexity.SAT3_NPHard_viaCircuits` (the p. 111 alternative proof); CKT-SAT `∈ NP` is
  `BoolCircuit.dagCktSatLang_mem_NP`, circuit evaluation `BoolCircuit.CVAL_mem_P`.
* Remark 6.7, Thm 6.13 — `Complexity.tabFamily_isPUniform`,
  `Language.mem_P_iff_exists_isPUniform`; Def 6.14, Thm 6.15 and the logspace half of
  Remark 6.7 — `Complexity.tabFamily_isLogspaceUniform`,
  `Language.mem_P_iff_exists_isLogspaceUniform`.
* Def 6.16, Ex 6.17, Thm 6.18 — `Complexity.DTIMEAdvice`,
  `Complexity.mem_PAdvicePoly_of_le_allOnes` (with the named `UHALT` instances
  `Complexity.UHALT_mem_DTIMEAdvice_one`, `Complexity.UHALT_mem_PAdvicePoly`),
  `Complexity.PPoly_eq_PAdvicePoly`, and the book's advice length `n^d` literally:
  `Complexity.PPoly_eq_iUnion_DTIMEAdvice_pow` (`P/poly = ⋃ DTIME(n^c + 1)/n^d`,
  `PAdviceSubsetPPoly.lean`). The time `n^c + 1` is forced, not cosmetic: the literal
  `DTIME(n^c)/a` is empty for `c ≥ 1` (`Complexity.DTIMEAdvice_pow_eq_empty`, zero steps
  on the empty input), so the literal union collapses to constant time
  (`Complexity.iUnion_DTIMEAdvice_pow_eq`); also
  `DTIME(T)/0 = DTIME(T)` for `T(n) ≥ n + 1` (`Complexity.DTIMEAdvice_zero_eq_DTIME`)
  and `⋃_c DTIME(n^c + 1)/0 = P` (`Complexity.iUnion_DTIMEAdvice_zero_eq_P`).
* Thm 6.19 Karp–Lipton — `Complexity.PH_eq_SigmaP_two_of_NP_subset_PPoly`; Thm 6.20
  Meyer — `Complexity.EXP_eq_SigmaP_two_of_EXP_subset_PPoly`, and the p. 115 corollary
  `Complexity.not_EXP_subset_PPoly_of_P_eq_NP`.
* Thm 6.21 — `BoolCircuit.exists_hard_function_dag` (book bound `2ⁿ/(10n)`), with the
  p. 115 probabilistic form `BoolCircuit.prob_computableDAG_shannon_le`, proved by the
  book's steps: `BoolCircuit.prob_eval_eq_apply` (`Pr[C(x) = f(x)] = 1/2`),
  `BoolCircuit.prob_computes` / `prob_computes_eq_prod` (`Pr[C computes f] = 2^{-2ⁿ}`, the
  product of the per-input probabilities) and the union bound `BoolCircuit.prob_computableDAG_le_count`
  (`ShannonProbabilistic.lean`).
* p. 108 circuit remarks — Lupanov `O(2ⁿ/n)` (`BoolCircuit.exists_dagCircuit_faninTwo_size_le_div`,
  `Lupanov.lean`); fan-out two (`DAGCircuit.exists_fanoutTwo`, `FanOut.lean`), including
  `¬¬v` buffers under the literal fan-in-exactly-two convention
  (`DAGCircuit.exists_fanoutTwo_notNot`, `5S`; `DAGCircuit.IsStrict.exists_fanoutTwo`,
  `20S`; `StrictFanOut.lean`); the literal Def 6.1 (`DAGCircuit.IsStrict`,
  `Language.inPPoly_iff_inStrictPPoly`); formulas as fan-out-one circuits, both ways
  (`TreeCircuit.toDAG_fanout_le_one`, `DAGCircuit.exists_treeCircuit_of_fanout_le_one`,
  `FormulaFanOut.lean`).
* Def 6.5's literal `⋃_c SIZE(n^c)` — empty (`Language.not_inSIZE_pow`); `P/poly` is the
  literal bound from length 2 on (`Language.inPPoly_iff_eventually`, `PPoly.lean`).

Remaining Chapter-6 items (each documented as a divergence in its file):

* **Thm 6.22, the size hierarchy over the book's `SIZE`** — only the tree-circuit
  analogue exists (`BoolCircuit.treeSize_ssubset`, `Hierarchy.lean`); the DAG version
  needs a DAG-native padding/counting argument on top of `exists_hard_function_dag`.
* **Tree-circuit CKT-SAT** (`Encoding.lean`, `CircuitSat.lean`) carries no `≤ₚ` claim —
  only equisatisfiability and a clause count; the book's Lem 6.11 is the DAG version
  above.
* The `O(T log T)` oblivious simulation (Remark 1.7) is Chapter 1's Phase 5 above; the
  circuits of `P ⊆ P/poly` are quadratic instead, which suffices for every Chapter-6 use.

---

## 4. Decisions pending (user)

* **Chapter-6 integration** — the Chapter-6 theorem surface is complete up to the
  items listed in §3 (Chapter 6); resolved in part: ch6 was merged into the
  campaign branch (`a2a2728b`), and the circuit nomenclature pass agreed
  with the ch6 authors landed 2026-10-01 in three commits: `HasLogDepth`
  → `HasPolylogDepth`; the `ACP` namespace unbundled (generic circuit
  material → `BoolCircuit`, the Razborov–Smolensky chain →
  `RazborovSmolensky`, `AC_GateOps` → `BoolCircuit.stdGateOps`);
  `FeedForwardCircuit.lean` relocated to
  `Complexity/CircuitComplexity/FeedForward.lean` (since renamed
  `LayeredCircuit.lean`), so `Complexity` no
  longer imports from `BooleanAnalysis` (verification:
  `scripts/circuit_module_order.txt`, the 23-module dependency sweep).
  Still open: their `Formulas.lean` defines `Literal`/`Term`/`DNF`/`CNF`
  at the **root namespace** (policy §1 leak; future ambiguity against
  `Std.Sat.CNF`/`Std.Sat.Literal`) — namespace choice deliberately
  deferred (user: `BoolCircuit` is not the right home for formulas);
  three CNF ecosystems coexist (their width-indexed `CNF n`, legacy
  `NPReductions.CNFFormula V`, the audited `Std.Sat.CNF ℕ`) with three
  SAT→3SAT artifacts; `UHalt.lean` introduces a **second computability
  framework** (Mathlib `ComputablePred` vs. the campaign's quarantine and
  its own `HALT_not_computable`) — the machine-model counterpart
  `UHaltMachine.lean` (`Complexity.UHALT_not_mem_P`) now carries `P ⊊ P/poly`,
  so `UHalt.lean` is a parallel statement, not a dependency; the merged circuit
  surface **passed the external audit protocol**
  2026-10-02 (three rounds, 0 blockers throughout;
  `audits/ch6-circuits-resolutions.md`, CLOSED) — campaign statements may
  cite its definitions, subject to the recorded divergences (the audit's
  interface notes 12–15 in `audits/ch6-circuits-findings.md` were followed by the
  bridge theorems now listed in §3). The dangling `ch6/PLAN.md` references were repointed
  here in the round-1 repairs. Loose ends for the colleagues:
  `Basic.lean` at 691 lines (> 600 target); and the audit's sweep logs
  show the **LMN tree is not sorry-free** (five `sorry` warnings across
  `CircuitCompression`, `IterativeReduction`, `Depth3Switching`,
  `CircuitTreeManip`) — outside the audited surface, flagged for its
  authors.
* **Fill-campaign start** (§2) — on hold by the same instruction.
* **Disposition of the three §1 questions** — CH1-Q1, CH1-Q2, CH2-Q1.
* **`TCSlib.Tactics` blueprint exclusion** — 92 metaprogramming-scaffolding
  declarations deliberately excluded from the dataset; user may override.
  *Origin: ch1 blueprint-extraction row.*
* **Fate of `AroraBarakChapter1Plan.md` at merge** — graduate to `docs/` vs.
  superseded by the blueprint. *Origin: ch1 decision log (final row).*

---

## 5. Repository housekeeping

* **The campaign's merge to `main` (user, 2026-10-15).**
  - **Purpose:** our infrastructure goes to `main`, and `main` then goes into
    `cryptography/garg-ch1-3`, so the cryptography work can build on it. The cryptography
    branch does not go to `main` yet.
  - **Bundles pruned first** (`99a0e4b3`): the campaign's 75 dispatched bundles (122.8 MB)
    leave the tree, indexed in `audits/BUNDLES.md`; bundles are no longer committed
    (`workflow.md`). Hydroxyi has been told, since the merge carries the campaign's edits
    to 14 of his files.
  - **Checks before the merge:** the 19 campaign-side root facades load together in Lean.
    A static name scan finds no clash with main's other modules or with the cryptography
    branch.
  - **#104 landed** (main into the campaign; `policy.md` resolved to the campaign's text,
    which contains main's). **Root-build replay: 265 of 265,** the root's import closure
    missing from the snapshot and then the root itself, at `ff2d6f6b`. Snapshot
    `oleans-lmain` is the first that covers the whole root closure (699 modules).
  - **The PR into `main`** comes from `integrate/campaign-to-main`, fixed at the replayed
    state. Later campaign work reaches `main` in later merges, each after a root-build
    replay.
  - **Hydroxyi's `complexity/arora-barak-ch7`** forks from the campaign at `8c23f3bc` and
    conflicts with it in five files. Four are `Randomized/*`, where the comment-only
    citation renumbering `f4b23f05` meets his edits; the fifth is the TuringMachine facade.
    Its integration is his.
* **Legacy `Complexity/NPReductions/*`**: 14 pre-existing style-lint FAILs
  (missing docstrings/References), outside the campaign surface; eventual
  fate coupled to the §3 retargeting idea. The ch6 branch adds (clean,
  additive) counting lemmas to `SATTo3SAT.lean`.
* **Dependabot**: 88 alerts on the repository default branch (2 critical,
  16 high) — repo-level, unrelated to this branch's content.
* **`AGENTS.md` / `.claude/CLAUDE.md`** partially superseded by campaign
  practice (`workflow.md` §7 records the boundary): the `lean_proof/`-based
  flow and the LeanInfoView-only verification guidance predate the gate
  script; align or annotate eventually.
* **`audits/TEMPLATE.md`** predates the evolved pack format (attestation
  evidence separation, bundle conventions); refresh before the next fresh
  campaign starts from it.
* **Statements-only package split (idea; no near-term action):** a
  `concepts`/`proofs`-style two-package layout — frozen statement surfaces
  compiled without proof code, importable by downstream chapters — would
  mechanize the statement-freeze discipline the campaign currently enforces
  by protocol (statement gates, briefs, audit packs). Observed in external
  prior art: Lax Archive lax-429075/lax-434930 (Bonnet, Cook–Levin on Lean
  4.33; examined 2026-10-05, scratchpad-only, Apache-2.0, non-binding, never
  imported), where each claimed result is an `axiom` in a statements package
  and a platform replay checks the proof network closes. Composes with the
  §2 D7 internal-namespace visibility proposal; revisit no earlier than
  that proposal, if at all. *Origin: prior-art comparison, 2026-10-05.*
* **Algorithm-adjacent files outside CI and provenance** (from the 2026-10-12 library-reuse
  assessment; colleague-owned, so this is a note for the owners, not campaign work).
  `Cryptography/RSA.lean` holds a root-namespace `TimeM` with trusted costs, plus a ticked
  insertion sort. It has no copyright header, is not imported from `TCSlib.lean`, and its design
  and notation appear to follow upstream cslib's `TimeM`. The attribution duty of policy §2
  (*Vendored code* / *Design adaptation*) should be checked before §15's curriculum layer
  reuses it. `GraphTheory/KargerMinCut*.lean` and `GraphTheory/Core/` are not imported from
  `TCSlib.lean` either, so CI never builds them (policy §1, *Exports*).
* **SAT/Tautology blueprint pages after the B4 promotion** (from the T2a gate, note 18): the
  pages still name the twelve promoted CNF-grammar declarations by their old private `SAT.lean`
  names. Regenerate them at the next blueprint increment.
* **`HANDOFF.md`** — the have→lemma extractor campaign's own tracking
  document; deliberately *not* absorbed here.
