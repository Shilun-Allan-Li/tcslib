# Pre-gate review: B6's H fill (Codex), commit `30222bbd`

Scope: `deliver/fill-b6-hierarchy-in` at `30222bbd` (base `e6bc1968`), merged into `lean/b6h-landing` at
`14ee2e46` (worktree `wt-h`). The delivery, extracted at `deliveries/h-final/x/`, was read as data.
The brief is `campaign/fills/b6/briefs/b6-fill-hierarchy.md`. No tracked file was modified.

**Verdict: no blocker, no major.** Four minors are in the REPORT and the public text, and none touches
soundness. The two completed targets are proved on the standard axioms; I checked this with my own
sealed elaboration of the delivered source. E-PAD is within the brief's permitted escalation. Its
statement is true as written, precise, and absent from the library and from the open PR branches.

Elaborations used: 3 of 3, run one at a time with `leanelab.sh` against `oleans-lnth`. The olean set
is the base's Lean content; `git diff e6bc1968 14ee2e46 -- TCSlib` shows `Hierarchy.lean` as the only
Lean change. Probe sources and raw outputs are in `wt-hk/rvprobe/hdreview/`:

- `HDSeal.lean`/`.out`: the delivered source with the delivered 71-definition seal and four
  `[-simp]` removals inserted before the first private. A constant walk and the axiom prints are
  appended before `end Complexity`.
- `HDDup.lean`/`.out`: eleven `exact?` duplication goals against the base closure.
- `HDDup2.lean`/`.out`: three goals against the overlay closure.

## Findings

| # | Severity | Where | Finding | Fix |
|---|---|---|---|---|
| 1 | minor | REPORT §"Checkpoints and declarations", row 7 | Row 7 says "Complete public logarithmic-space strictness corollary, admission-free". At checkpoint 7's commit `a55f653d`, committed before checkpoints 2–6, `LOGSPACE_ssubset_PSPACE` still depended on `sorryAx` through `space_hierarchy`'s `sorry`. The agent's own log `evidence/logs/cp7-verify` prints `[propext, sorryAx, Classical.choice, Quot.sound]`. The rule-4 ordering itself is allowed. Only the wording is wrong, and nothing is unsound at the final commit. | Reword row 7: "proved from `space_hierarchy`'s statement; admission-free from checkpoint 6 (`37a041bc`) on". Mention that the commit order is cp1, cp5, cp7, cp2, cp3, cp4, cp6, cp8. |
| 2 | minor | Delivery; REPORT §"Delivery integrity" | The brief asks for one zip per checkpoint, delivered at once. Only `fill-b6-hierarchy.zip` reached `deliveries/h-final/`. The REPORT lists SHA-256s for eight checkpoint archives that the maintainer does not hold. Checkpoint 8 was amended after its first archive (`bf4d026a` became `30222bbd`). The final zip does carry the per-checkpoint evidence (`evidence/{citations,inspection,logs}/cp1…cp8`), the eight-patch series and the bundle. The patch chain checks out: blob `287acce8` → … → `40d62c36` = `30222bbd:Hierarchy.lean`. | Ask Codex for the seven intermediate zips, or record a waiver: the final zip, the patch series and the bundle make them redundant for the gate. |
| 3 | minor | `Hierarchy.lean:2533–2559`, `SPACE_linear_ne_NP`'s docstring | The sketch pads with `List.replicate (\|x\|²) true` and gives the padded length as `m = n² + 2n + 2`. The route, `sph_linear_ne_NP_of_padding` and E-PAD all use the brief's `(\|x\|+1)²` pad (`polyUnary 1 2`), which gives `m = n² + 4n + 3`. Both pads are mathematically valid, but the public sketch and the escalated interface disagree. The sketch also keeps internal phrasing ("a derived obligation from…", "the chapter-2 padding-cluster discipline"). `NP`'s closure is now published as `preimage_mem_NP` and is not cited. | At landing, or when E-PAD lands: state the `(\|x\|+1)²` pad and `m = (n+1)² + 2n + 2`, cite `Complexity.preimage_mem_NP`, and drop the two internal phrases. |
| 4 | minor | REPORT §"Escalation E-PAD", proposed `**Implementation.**` for `SPACE_linear_ne_NP` | The paragraph ends with process text: "If that padded decider cannot be assembled from the named hosts, retain the admission and escalate its exact missing statement." It is not public text, and it omits the pad. | Land it as: "Use the polynomial-time padding map `x ↦ pairEncode x (replicate ((\|x\|+1)²) true)` and `preimage_mem_NP`; a linear-space decider of the padded language turns `SPACE (n+1) = NP` into `SPACE (n²+1) ⊆ SPACE (n+1)`, against the hierarchy at `n + 1` and `n² + 1`." |
| 5 | note | `space_hierarchy`'s docstring (2402–2501); module docstring (60) | This is base text kept under region (d), as the brief prescribes. The sketch still describes a `counterLoopTMVia` clock, `exists_recordStepTM` rounds and a clock width. The normalization is given as `exists_codeTM` plus a re-derived space clause through `relabelState_runFrom_init`. The proof uses the runner's internal clock and `exists_codeTM_spaceUsed`, which rule 5 requires. The module docstring says "`g`'s witness drives the window radius and the clock width". The REPORT's proposed Implementation paragraph corrects the clock but not the relabel sentence. | When landing the Implementation paragraph, also rewrite the "Relabel it… (`Turing.exists_codeTM`, plus the space clause it does not state…)" sentence to cite `exists_codeTM_spaceUsed`, and drop "and the clock width". |
| 6 | note | REPORT §"Escalation E-PAD" | The search for E-PAD did not consider the nearest published host. `Complexity.LogProg.OIS.compile_decides` and `Complexity.mem_LOGSPACE_preimage` (`SpaceComplexity/Logspace/PreimageHost`) run an arbitrary decider `M` on a virtual input `f x`, never written. The space is `M.k(2S+1) + O(log) + bank`, with `S` the space `M` uses on the virtual input. This module is outside H's frozen nine-import closure, so it does not invalidate the escalation, but it bears on the API PR (see the assessment below). | Record it in the E-PAD ticket. |
| 7 | note | `sph_select_fields` (838), `sph_seam_heads` (700), `sph_halt_contract` (2067), `sph_written_record` (1361) | These are general consumer lemmas, not copies. **`sph_select_fields`:** `Cfg.select` has no published field equations; my `exact?` on its state and work-tape conjuncts returns only `exact rfl`, which is definitional and which rule 10 forbids. The private is therefore a genuine API gap, and the REPORT lists it as a promotion candidate. **`sph_seam_heads`:** a seam head-envelope lemma, parallel to the env clause of `Contract.seq`/`Traj.seq`. `exact?` timed out at 400k and 2M heartbeats, matching the agent's result. **`sph_halt_contract`:** builds a `Contract` by structure literal where `Contract.ofSegment` with `exists_first_halt` would also serve. **`sph_written_record`:** mirrors an inline step of `CfgRecord`'s private `recordStep_apply_run`. It is not a declaration copy, and the screen shows no pair against it. | Promote `Cfg.select_{state,inputPos,output,workTapes,workTapePos}` next to `embedEmitCfg_select` in `Build/Embed` at the next shared-file window, and re-point `sph_select_fields`. The others need no action. |
| 8 | note | `sph_linear_ne_NP_of_padding` (2364–2398) | A 35-line private with no consumer in the file. It takes `space_hierarchy`'s statement and E-PAD as hypotheses and is admission-free. It is beyond the escalation's minimum, but it does no harm: once E-PAD lands, the target's body becomes `sph_linear_ne_NP_of_padding space_hierarchy <E-PAD>`. | The maintainer can accept or drop it. Keeping it is reasonable. |
| 9 | note | File size | 2,563 lines, 4 public and 43 private declarations. `style_lint` reports "2564 lines (> 1000, must split)" and campaign lint has one new WARN (81 against the base's 80). The brief's rule 8 waives the size limit. About 2,200 lines are the diagonalizer pipeline (`sph_suffix`, `sph_record_suffix`, `sph_valid_machine`, `sph_validated_machine`), generic in the simulated `FinTM Bool`. | Optional later split or harvest, for example a public diagonalizer row; it is not needed for this gate. |

## Checks that passed

**1. Soundness and freeze**

- **Statements frozen.** The four public statements, `theorem … :` up to `:= by`, are byte-identical
  to the base: `space_universal`, `space_hierarchy`, `LOGSPACE_ssubset_PSPACE`, `SPACE_linear_ne_NP`.
- **F6 untouched.** `space_universal`'s docstring and body (4,826 bytes) are byte-identical, and so is
  its module "Main results" entry, which keeps its dated text as the brief requires.
- **Regions.** Every diff hunk is in an allowed region: (a) the imports after line 10; (b) the 2,241
  lines inserted after base line 162; (c) the bodies at base 271 and 285, with `SPACE_linear_ne_NP`'s
  body still `sorry`; (d) the docstrings. There are no `set_option`, `attribute`, `instance`,
  notation or new `open` lines.
- **Imports.** Exactly the base's five plus the overlay's four, in the order the brief gives.
- **Identity.** The delivered source equals the zip's source and the landing worktree's file.
- **Proofs and axioms**, from `HDSeal.out`, my own sealed copy:
  - 0 errors; two `sorry` warnings, at `space_universal` and `SPACE_linear_ne_NP`.
  - `space_hierarchy` and `LOGSPACE_ssubset_PSPACE` print `[propext, Classical.choice, Quot.sound]`.
    `SPACE_linear_ne_NP` adds `sorryAx`.
  - A walk over all 149 constants local to the file (theorems among them) finds `sorryAx` only in
    `space_universal` and `SPACE_linear_ne_NP`, and no non-standard axiom anywhere. All 43 privates
    are admission-free.

**2. Rule 10**

- **Seal coverage, my walk.** The used constants (type and value) of every local declaration,
  auxiliaries included, reference 104 other-file TCSlib definitions:
  - 71 are irreducible under the seal, which is exactly the delivered 71.
  - The other 33 are all `reducible`: structure projections, the abbrev `Cfg.Halted`, and the
    generated `casesOn`/`noConfusion`/`ctorIdx`. These are exempt under `TEMPLATE.md`'s abbreviation
    rule.
  - No semireducible other-file definition is left unsealed. No further definitions sit in the
    statements of the 135 cited TCSlib theorems.
- **Agent's walk.** `evidence/citations/final.md` classifies the same 71 as `def`.
- **`[-simp]`.** All four (`Action.apply`, `Cfg.init`, `MultiTapeTM.initCfg`, `NDTM.initCfg`) are
  removed. No other `@[simp]` definition is among the 71.
- **Controls.** The raw logs show `cp8-final/002` with 75 PASS and 0 FAIL unsealed, and `003` with
  0 PASS and 75 FAIL sealed. The controls are 67 delta `rfl` controls, 2 `Fintype.card` usage
  controls, 2 equation controls (`windowRun`, `NDTM.runWith`) and 4 simp controls. The
  final_v2 seal is identical to cp8's.
- **Rewrite arguments, my scan.** No `rw`/`simp`/`simpa`/`dsimp`/`simp_all`/`norm_num` argument
  names an other-file definition; the only match was the local hypothesis `hi`. There is no
  `unfold` or `delta` anywhere. The 10 `show`/`change` sites reduce only structure-update
  projections, own definitions or core definitions, and all of them pass the seal.
- **Rule 11.** No R3 row, no `_private`, no `capture_run`/`capture_visitedByTapeHead`, no Bool
  seam-space corollary, no `length_bits_succ_le`, no `Contract.liftSymbols`.
  `inputRewindTM_run` is used only on the binary source `inputRewindTM 0` before the lift, which is
  the brief's route. `exists_codeTM_spaceUsed` is used, not `relabelState`. All 43 privates carry
  the `sph_`/`Sph` prefix.

**3. Duplication**

- **Probes.** `exact?` finds no replacement for `sph_seam_avoids`, `sph_written_record`,
  `sph_halt_contract`, `sph_fold_valid`, `sph_sq_le_two_pow`, `sph_inclusion`, `sph_summary`,
  `sph_record_size` or the E-PAD interface. For `sph_seam_heads` the search was inconclusive
  (heartbeat timeout). For `sph_select_fields` the only proof found is `rfl`.
- **Screens.**
  - The before-screen is byte-identical to `b6-fill-hierarchy-screen-base.txt`.
  - The after-screen (`screen-after-final-v2.txt`) has exactly 12 lines on `Hierarchy.lean`, all
    below 90%. The dispositions are sound: 4 are against `Cfg.mapState_mapState`, as an `Cfg.ext`
    field idiom, and 8 are same-file.
  - The first-final screen's two genuine `mapState_mapState` re-derivations were repaired by
    citation.
  - No pair is against another file's private. "New copies: none" holds.

**4. Public text**

- No campaign labels remain in the owned docstrings. The phase, gate, round, finding, design,
  registry and row names the brief lists are all removed. F6's docstring, lines 84–145, is
  untouched by mandate.
- No line exceeds 100 characters, measured in characters.
- Every private lemma over about 20 lines has a literal "Proof sketch", 35 in all.
- The public targets keep their `[AB09]` attributions and sketches.
- The module docstring keeps its `## References` and is free of status text.

**5. REPORT figures and evidence**

- **Counts.** Line count, 43 privates, the 71/75 seal and controls, the 321-check import probe
  (`final-v2-import`, 0 errors), lint 0 FAIL / 81 WARN, the 26-entry base sorry list by name, and the
  12-pair table are all accurate.
- **Patches and bundle.** The bundle requires only `e6bc1968`, and its verification log is
  included.
- **Implementation paragraphs.** They are proposed in the REPORT, not inserted, as the brief requires.

## E-PAD assessment

**Within the brief's terms: yes.** The user's 2026-11-06 ruling lets checkpoint 8 end in a named
escalation for "the padded language's decider". The brief itself lists the pad-length test and the
assembly as unhosted. The body is still `sorry`, preceded by a literal "Proof sketch". The missing
statement is in the REPORT, and nothing else depends on it.

**Stated precisely and true.** For `L ∈ SPACE (n²+1)` with decider space `c·(n²+1)`, the padded word
is `y = pairEncode x (replicate ((n+1)²) true)`. Its length is `|y| = 2n + 2 + (n+1)² = n² + 4n + 3`,
from `length_pairEncode`, so `c·(n²+1) ≤ c·|y|`.

A decider of `L'` works as follows:

1. Check the doubled-code syntax, the `[false, true]` separator, the all-`true` pad and the pad length
   `(n+1)²`, in O(|y|) space (in fact logarithmic).
2. Install `x`, which costs `≤ |y|` cells.
3. Run `L`'s decider in `c·|y|` cells.

The total is `O(|y| + 1)`, so the statement holds for every `L`.

The REPORT rightly stresses validate-first. On a malformed `y`, `|pairFstD y|` can be about `|y|/2`,
and running the decider there would cost about `c·|y|²/4`, which is not linear.

The pad matches `polyTimeComputable_polyUnary 1 2`, and the interface is exactly the hypothesis
`hpad` that the machine-checked `sph_linear_ne_NP_of_padding` consumes. Supplying it closes the
target.

**Absent: confirmed.**

- **`ClassNP/Nondeterminism`'s padding.** The A3 checks and `a3n_pad_eq` are private and
  polynomial-*time* only, with an exponential pad and no space clause.
- **`SpaceComplexity`.** It has no padding lemma (the hits are codec and bank padding). Its only
  closure lemmas are `SPACE.mono` and `mono_const`, with no intersection or preimage closure.
- **Branches.** No padding theorem exists on any `origin/lean/*` branch. The open PRs (#211, #214,
  #215, #216, #210, #195) add none.

**What an API PR would take.** I recommend publishing a more general row than the specific
interface, for example `Complexity.mem_SPACE_pad` in a new `SpaceComplexity/Padding` module. For
`L ∈ SPACE s` and a pad `q n = C·(n+1)^d`, with `s n ≤ a·(q n + 2n + 2)`, the padded language would be
in `SPACE (m + 1)`. E-PAD is then the instance at `C = 1`, `d = 2`. There are two routes:

- **(i) The machine route, from H's hosts.** This is roughly the size of one of H's phases, a few
  hundred lines:
  - A new pad validator: syntax by an `inputFoldTM`-style scan, and the length by a binary counter
    compared against `(n+1)²`. This is the real gap: a leaf or host row with a space clause.
  - `seamCompTM₂` or `Contract.branch` for reject-first.
  - `FinTM.exists_inputCallTM` at `computesFunInTime_pairFst` to install `x`, with its space by
    `spaceUsed_le_mul_succ`.
  - `vhostEmitTM_runFrom` and `vhostEmitTM_spaceUsed_le` to run the decider, for space `S + |y| + 2`.
  - Packaging through `decidesInSpace_iff` and `SPACE.mono_const`.
- **(ii) The preimage route.** Generalize `mem_LOGSPACE_preimage` to a `mem_SPACE_preimage`: from
  `LogProg.OIS.compile_decides`, `f` implicitly logspace computable and `C ∈ SPACE s` with
  `s (|f x|) ≤ a·t (|x|)` and `t ≥ logSpace`, conclude `f⁻¹ C ∈ SPACE t`. Then take
  `f y = if valid y then pairFstD y else w₀`. This needs:
  - logspace bit deciders for that conditional projection, with the pad-length arithmetic from
    `Logspace/Mult`;
  - a small case split for when `w₀ ∈ L` cannot be avoided (`L = univ`, where `L'` is the validity
    language).

  Route (ii) gives a reusable space analogue of `preimage_mem_NP`. Route (i) stays inside H's host
  family. Either way the consumer change in `Hierarchy.lean` is a one-line body plus one import,
  which needs the user's import ruling under rule 6.
