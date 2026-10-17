# External audit pack — the ND inventory API, round 2 (PR #122)

Campaign: the Arora-Barak chapters 3-4 plan, C1 (the nondeterministic time hierarchy, [AB09, Theorem
3.2]). The user's "Everything" rule (2026-10-16, `policy.md` §1): every definition a brief's route
reads gets a published equation before the brief is dispatched.
- **Why:** round 1 (gate 37, PR #119, merged before its gate) returned **FAIL 0/2/3/2**
  (`audits/nd-api-findings.md`; resolutions `audits/nd-api-resolutions.md`).
  - Its finding 1: RC's serialization route was unpublished.
  - Its finding 3: a docstring.
  - Gate 38's minor 5 (`audits/nd-normalform-resolutions.md`) rides along: the `ClassNP` facade's
    Contents line.
  - The reviews of C1 wave 1's first four deliveries (2026-10-17; `audits/evidence/c1/fills/`)
    found four more gaps on wave-1 and wave-2 routes.
  - Gate 40 (`audits/ntime-diag-statements-r2-findings.md`) found a stale module docstring.
- **The head:** `lean/nd-api-r2` at `6a48b93e`, five commits on #121's round-2 head `0a5878ed`.

| Commit | File | Additions |
|---|---|---|
| `aeee7a2e` | `TuringMachine/Build/StepBlock` | `workReadsK_zero`, `workReadsK_succ`, `tableBitsK_eq` (gate 37, finding 1) |
| | `TuringMachine/CodeFormat` | `actionBitsK_eq`, `codeSkipActionK_append` (finding 1) |
| | `TuringMachine/Encoding` | the twelve case equations of `signBits`, `optBoolBits`, `optOptBoolBits`, `optStateBits` (finding 1) |
| | `TuringMachine/Build/VirtualInput` | `vhostSilentCfg_eq`'s docstring: the capture tape holds `capPre ++ c.output`, the physical output is `out₀` (finding 3) |
| | `ClassNP` (facade) | the Contents entry for `NDNormalForm` (gate 38, minor 5) |
| `b6627401` | `TuringMachine/Build/CounterLoop` | `counterValue_eq` (C1-R's escalation E1) |
| | `TuringMachine/CodeParser` | `codeBitsNat_eq` (E1) |
| `423b6536` | `TuringMachine/Simulation` | `MultiTapeTM.agreeOn_iff` (C1-WC's review; the user's ruling) |
| `63d69835` | `TuringMachine/Simulation` | `FinTM.bufferTape_eq`, `FinTM.bufferTape_of_neg` (the seam-layout contract's consumer) |
| `6a48b93e` | `TuringMachine/NDCodeSimulator` | the module Design bullet: R's prefix clause is kept with no consumer (gate 40, minor 1) |

In all: 22 public equations and 3 docstring changes, with no `@[simp]`. Every proof is `rfl` or
`Iff.rfl`, except `codeSkipActionK_append` (through `codeEraseActionK` and
`codeReadActionK_append`) and `bufferTape_of_neg` (through `bufferTape_eq`). Each file's Main
results or Contents names its additions.

- **Evidence:** `audits/evidence/nd-api/r2/`:
  - the per-file elaborations with `#print axioms` appended (`logs/`);
  - the freezes (`freeze/`), the lint before and after (`lint/`), the screen (`screen/`);
  - the edit scripts (`apply-r2.py.txt`, `apply-r2b.py.txt`), the patch, the replay script and
    list, and the PR body.
- **The review probe** for finding 1, with the definitions irreducible, is
  `audits/evidence/nd-api/r2/RCApiDraft.lean.txt`. It derives `workReadsK 3`'s order, the
  three-tape table and the choice field's bits.
- **The bundle** contains:
  - the nine touched files at the head;
  - the consumers: `NDCodeSimulator` (RC and R), `Build/StepBlockLoop` (the hosted loop's value
    hypothesis), `Build/InputWindow`;
  - the reviews that motivated each addition.

## Brief for the auditor

1. **Faithfulness.** Does each equation state exactly its definition's behaviour?
   - `workReadsK_succ`'s order: tape `0` outermost.
   - `tableBitsK_eq`'s nesting: state, then input read, then work reads.
   - `actionBitsK_eq`'s field order, and the encoders' bits.
   - `counterValue_eq` and `codeBitsNat_eq`.
   - `agreeOn_iff`, and `bufferTape_eq` / `bufferTape_of_neg`.
2. **Gate 37's finding 1 is closed.** Can RC's route now read the three-tape table and re-emit
   its records with every definition on the route read through a published equation? Check
   against RC's sketch (`NDCodeSimulator.lean`, `exists_replayCanonizer`) and the probe.
3. **The later gaps are closed:**
   - **E1:** R's loop hypothesis `Nat.ofDigits 2 (w.map Bool.toNat) = t` follows from
     `counterValue_eq` and `counterValue_bits`.
   - **WC:** its join can introduce `AgreeOn` through `agreeOn_iff`.
   - **The seam layout:** its consumer reads the summary tape's cell `0` through
     `bufferTape_of_neg`.

   Is anything still unpublished on those routes?
4. **No behaviour change.** The diff adds declarations and docstrings only. No existing statement,
   definition or proof body changes (the freezes).
5. **The three docstrings** are accurate: `vhostSilentCfg_eq`, the `ClassNP` Contents line, and
   `NDCodeSimulator`'s Design bullet.
6. **Duplication:** the screen's one new pair (below). Is the explanation right, and is it debt?
7. **Records:** do this pack, the PR body and the resolutions agree with the evidence?

## Repository-side attestations (verify or challenge)

- **Elaboration**, each touched module against `oleans-lndnf` (the tip's Lean): 0 errors. The
  warnings equal the bases': `Encoding` 1 (`pairDiagTM_computes`), `Simulation` 1
  (`branchTM_spaceUsed`), `NDCodeSimulator` 2 (its contracts), the others 0. A probe in
  `CounterLoop` derives `Nat.ofDigits 2 ((Nat.bits t).map Bool.toNat) = t` from the new equation.
- **Axioms:** 16 of the 22 use none. `workReadsK_zero`, `workReadsK_succ`, `tableBitsK_eq` and
  `counterValue_eq` use `propext`. `codeSkipActionK_append` and `bufferTape_of_neg` use `propext`
  and `Quot.sound`.
- **Freeze:** 22 publics added, none removed, no private change. The body changes are the three
  docstrings.
- **Lint:** 0 FAIL. `TuringMachine/` stays at 63 WARN, and `ClassNP/` at 15. Check 8 no longer
  lists `workReadsK`, `tableBitsK`, `actionBitsK`, `codeSkipActionK`, the four encoders or
  `AgreeOn`.
- **Screen** (commit 1's 8 files, `screen/`): 337 → 337 declarations, 68 → 69 pairs. The new pair,
  `NDCodes::CodeNDTM.serialize` reproducing `StepBlock::tableBitsK` at 79/141 = 56%, is a chunk
  boundary artifact; both texts are unchanged.
  - At the base, the screen counted the following `namespace StepBlock` (18 non-blank characters)
    into `tableBitsK`'s chunk: 79/159, under the floor.
  - `tableBitsK_eq` now ends the chunk at 141.
- **Replay:** `replay-lndapi2.sh`, the nine files' downstream closure: 313 modules,
  `Simulation`'s closure. Chained from `oleans-lndiag2` (#121 round 2's replay).
  REPLAY-RESULT

## Findings format

| # | Severity | File · declaration | Claim | Evidence / counterexample | Proposed fix |
|---|---|---|---|---|---|

Severity guide as in `audits/TEMPLATE.md`. Findings go verbatim into `audits/nd-api-r2-findings.md`.
The gate closes when it has zero blockers and zero majors.

**Deliver your findings as a downloadable Markdown file named `nd-api-r2-findings.md`** (the
findings table and the verdict line, no other wrapping), and also paste its content in your reply.
