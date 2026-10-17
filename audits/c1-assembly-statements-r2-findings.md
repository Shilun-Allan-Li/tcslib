Input SHA-256: `e2cd68c2f0762a80603c072106f293f2a94795cbfee00b812d5614e3914708c0` — independently verified, matching the expected digest. Exactly **65 sections**, counted by anchored repository-path headers.

**C1-A guess-then-run assembly statement gate — round 2 external audit, 2026-10-14.**

**Verdict: CLOSED — 0 blockers, 0 majors, 1 minor.** M1 is repaired by the requested public export, without accepting duplication debt. The existing statements are frozen as claimed. The remaining minor is a directory-boundary defect in the name-screen allowlist: m3 is therefore still open in that limited respect. Under `workflow.md` §3, a minor does not hold the statement gate; repair it in the closing commit and recheck it. The promised landing replay remains required.

Scope: the four round-1 findings, the two additions, the three landing files, the shim arrangement, freeze, controls, and the round-2 pack's seven brief points. I started with the pack and restated the new statements before reading their docstrings. The original upload was not changed.

I independently regenerated and compared the evidence, ran the Python checks and shell isolation-control path, and performed finite transition experiments. **I did not independently rerun Lean.** A Lean 4.25.0 executable is installed, but the required Mathlib/tcslib dependency snapshot and elaboration wrapper are not supplied. Kernel elaboration, elaborated-type equality, and axiom prints remain maintainer execution evidence, tested against the sources where possible. This audit does not discharge the writer/core fills, UN's setup construction, or H1's separate prerequisite.

**Findings.** Paths abbreviated below are under `audits/evidence/c1/assembly/r2/`; “unit” means `C1Assembly.lean.txt`. Line numbers refer to the extracted source, with presentation fences removed.

| # | Severity | File · declaration | Claim | Evidence / counterexample | Proposed fix |
|---|---|---|---|---|---|
| R2-m3 | minor — residual m3 | `scripts/names_asm.py:116`, allowlist membership; pack's m3 resolution | Only pending files under the reviewed `audits/evidence/c1/assembly/` directory are exempted. | The test is `os.path.abspath(u).startswith(os.path.abspath(a))`. Normalization removes the allowlist's trailing slash. With that reviewed directory and an **outside sibling** `audits/evidence/c1/assembly-other/Clash.lean.txt` declaring `Turing.guessRunTM`, I reproduced `ALLOWED`, `shared names counted: 0`, and **exit 0**. The sibling is not inside the reviewed directory. This does not establish a collision in the actual supplied landing; it refutes the claimed boundary of the exception. | Use path-component containment, e.g. `os.path.commonpath([os.path.abspath(u), os.path.abspath(a)]) == os.path.abspath(a)`, or an exact reviewed file list. Add a sibling-directory collision control alongside the existing pending-file control; require exit 1. I tested the component-aware replacement in a scratch copy: the sibling and ordinary pending collisions return 1, while the legitimate round-1 evidence returns 0. |

No other blocker, major, or minor was established.

**Rulings on round 1.**

| Finding | Ruling | Basis |
|---|---|---|
| M1 — repeated capture calculation | **Closed** | The export's signature is character-identical to round 1's proposed signature; its landing proof is also the proposed proof. Both capture-field branches of `guessRunCfg_clean` and `b2b_capture_shape` now cite its projections. Their local slot-search calculation is gone. Retaining the latter private whole-configuration lemma is justified below. |
| m1 — acceptance docstring | **Closed** | The prose now qualifies a rejecting verdict by “different from `acc`,” and explains acceptance-first dispatch when the verdict states coincide. The preceding empty-output condition remains explicit. No distinctness hypothesis was added and the theorem is unchanged. |
| m2 — negative controls | **Closed** | Handoff-time state is now a positive corollary, instantiated both symbolically and concretely. `neg4` asserts liveness of an actually halted branch at length 19; its logged failure is a `decide` refutation, not a type mismatch. `neg1` is correctly labelled one bit early. The early-setup-exit example explicitly demonstrates failure of `hPfirst` at the later return time. The pack acknowledges both round-1 misdescriptions. |
| m3 — fail-closed tooling | **Still open, minor, only as R2-m3 above** | The exit condition now includes non-allowlisted pending clashes. The original pending collision returns 1. Isolation deletes stale targets, propagates generator failure through `pipefail`, and skips elaboration after failure; I reproduced that behavior using the production loop. The short-name summary now includes `GuessRunPhase.State`. The allowlist's directory boundary still needs repair. |

**New statements and hypotheses — brief points 2 and 6.**

`embedSilentCfg_cap` says that, for any source configuration, ambient tape/head frame, capture prefix, and physical output, a capture tape outside the selected bank contains exactly `pre ++ c.output`, and its head equals that word's length. This is a pure configuration identity: it assumes neither reachability nor a live source state, and it does not retain the old ambient capture cells or head. Its two conclusions are precisely

\[
\begin{aligned}
 (\operatorname{embedSilentCfg}\;\iota\;cap\;tapes\;heads\;pre\;out_0\;c).workTapes\;cap
   &=\operatorname{bufferTape}(pre\mathbin{++}c.output),\\
 (\operatorname{embedSilentCfg}\;\iota\;cap\;tapes\;heads\;pre\;out_0\;c).workTapePos\;cap
   &=|pre\mathbin{++}c.output|.
\end{aligned}
\]

The hypothesis gives `ι a ≠ cap` for every source index `a`; hence the partial-inverse search returns `none`. In each field of the supplied `embedSilentCfg` definition, the next test is `cap = cap`, so the capture branch gives the displayed equality. This is exactly the existing `embedSlot_unselected` interface. No extra finiteness, blank-frame, empty-prefix, or source-liveness hypothesis is needed. If `cap` is selected, the selected-tape branch wins, so the hypothesis cannot be omitted.

`guessRunTM_runWith_handoff_state` says that **every** choice word of length `TP + 2*m + 9`, under the six existing setup hypotheses, leaves the assembled machine in `some ⟨GuessRunPhase.run, qentry⟩`. It is the state projection of the unchanged handoff equality: `guessRunCfg` sets the source state to `some qentry`, and `mapState` tags it with `.run`. It requires no suffix-verdict hypothesis. Its timing agrees with the existing decomposition:

\[
TP+1+(m+1)+1+1+1+(m+3)+1=TP+2m+9.
\]

Both new docstrings agree with these readings. The new corollary inherits the handoff theorem's writer-contract dependency; the export does not.

**Reuse and the retained private lemma — brief point 1.**

The landing export is at `landed/Embed.lean.txt:1022`. In landed NDHost, `guessRunCfg_clean` uses its tape and head equations at lines 956 and 970. In landed Inclusions, `b2b_capture_shape` uses them at lines 745 and 758. Both consumers have zero `finRange` occurrences; Embed retains its original two occurrences. Direct comparison confirms deletion of the local `hslot` proofs and both representation-exposing capture branches, not merely a rename of them.

**Keep `b2b_capture_shape` private.** It identifies an entire transported configuration with an updated ambient configuration: state, input position, selected blank banks, capture contents/head, remaining frame, and physical output. The export supplies only two fields. Its three surviving uses, at landed Inclusions lines 902, 909, and 1425, rewrite this whole identity for setup start, setup end, and trial setup. They are unchanged. Replacing each use with the two capture equations would still require the remaining configuration proof at each site. Keeping this single consumer-local lemma, now built from the public field interfaces, introduces no copied implementation and needs no debt acknowledgment.

I reran the supplied P1 copy-text screen: before **195 declarations / 63 pairs / 9,835 characters**, after **215 / 67 / 10,327**, exactly matching the log. The four additional directed pairs are the two six-way instance dispatchers already present in round 1 and two repeated applications of the existing handoff theorem. These are typeclass dispatch and theorem reuse, not copied private calculations or hosts. No new cross-file pair involving the assembly and Embed/Inclusions appears. P2's larger Catalog screen was inspected, not independently rerun. The threshold-based screen is supporting evidence; the explicit source comparison establishes M1's repair even though that small old copy did not register as a removed screen pair.

**Shim ruling — brief point 3.**

**Adequate for this statement gate, pending the promised real-dependency replay.** I verified that the shim and landing declaration have character-identical docstrings and signatures, with the same ambient variable context. The landing proof stays inside Embed and cites its private lemma; the evidence proof appears only in the unit/checking files. The generated landed NDHost and Inclusions contain no shim and obtain the public export through their existing Embed import path via `Build.Seam`.

The supplied cut log checks the real landing export in Embed's own closure, records its axioms as `[propext, Quot.sound]`, and records identical elaborated types for the shim and landing export. Consumer proofs use the theorem's propositions, not its proof implementation. Thus substituting the separately checked theorem with that same type is a sound modular checking arrangement. The shim's unfolding proof is explicitly temporary checking material; it is not retained production duplication. The logs do **not** establish that the three landed files and all downstream modules have already been rebuilt together. Preserve that distinction and compile the actual export and dependent closure at landing.

**Freeze — brief point 5.**

| Comparison | Existing declarations preserved | Additions | Changed existing code |
|---|---:|---|---|
| Tip Embed → landed Embed | 46/46 | `embedSilentCfg_cap` | None |
| Tip NDHost → landed NDHost | 6/6 | 21 assembly declarations, including the new handoff-state corollary | None; one `Build.Catalog` import added |
| Tip Inclusions → landed Inclusions | 68/68 | None | Only `b2b_capture_shape`'s proof |
| Round-1 unit → round-2 unit | 20/20 | The export and handoff-state corollary | Only `guessRunCfg_clean`'s proof |

I reproduced all four supplied freezes and their changed-statement control. A separate nested-comment/string-aware comparison confirms the stronger source facts: Embed's old executable code is identical after removing the single addition; NDHost's complete old code is an exact prefix after the documented import; Inclusions is identical outside the one private proof; and the unit's 20 old declarations retain their order. Inspection of the complete comment-stripped unit diff confirms that its only old-code edits are the capture-proof replacements. This includes private statements and the surrounding contexts, not just public declaration names. **No existing statement changed.**

**Definition check.** Round 2 changes no production definition body. The frozen assembly definitions retain the following meanings, consistent with round 1's reading and their docstrings:

| Definition or instance family | Meaning |
|---|---|
| `NDWriterState.instFintype` | Transfer finiteness from `Option Q`, treating `done` as a live control state. |
| `GuessRunPhase`, `GuessRunPhase.State`, and its two instances | Six phase tags, their respective control types, and componentwise finiteness/decidable equality. |
| `guessRunPhases` | Setup, bounded writer, forward skip, backward seek, deterministic suffix, and a one-step emitting/halt leaf. |
| `guessRunRed` | Silent redirects at designated live exits; acceptance tested before rejection. |
| `guessRunTM` | The existing nondeterministic phase host instantiated with those phases and redirects. |
| `guessRunCfg` | Replace the state and overwrite exactly the guessed interval, preserving other fields. |
| `streamStartCfg` | Live entry state, input position 1, stream on its designated tape, other tapes blank, heads 0, empty output. |

The new evidence-only definition `sanPFlip` starts in `true`, toggles its Boolean state on each standalone step, and changes no tape, head, or output. Its exit is therefore visited at time 0 and again at time 2, as the new example requires.

**Adversarial checks — brief points 4 and 6.** These combine direct mathematical instantiation with an independent Python transcription of the supplied transitions; they are not additional Lean kernel checks.

| Instance | Result |
|---|---|
| Empty capture prefix and source output; dirty ambient capture tape and head −39 | Capture tape becomes everywhere blank and its head becomes 0. This is the specialization needed by `guessRunCfg_clean`. |
| Prefix of length 1,024 and source output `[true, false]` | Capture word has length 1,026 and head 1,026. Old ambient cells, including one at position 10,001, are absent. |
| Halted source, zero source tapes, arbitrary nonempty physical output | The capture identity still holds; physical output remains the supplied `out₀`. Other unselected frame fields remain unchanged. Twenty-four transport cases were checked. |
| Omit `hcap`, select the capture tape, source tape cell 0 is `true` and source head is 7, empty prefix/output | The transport retains that selected source tape/head, contradicting the proposed empty capture tape/head 0. |
| `m = TP = 0`, immediately accepting suffix | Across all 2,048 length-11 words: run-entry state at 9, live output phase at 10, halted with `[true]` at 11. |
| Two-cell setup, `TP = m = 2` | All 32,768 length-15 words reach run entry with head restored to 0 and exactly bits 3 and 4 written. This agrees with the positive theorem-level and concrete probes. |
| Accepting two-cell stream at length 19 | `2 + 2*2 + 2 + 11 = 19`; state is `none`. Thus revised `neg4` is false. The bundled log specifically records `decide` refuting `.state ≠ none`. |
| Stream moved one bit early | For an all-false prefix/suffix the suffix reads `false,false`, so the claimed `[true]` output is false. The offset is one bit. |
| `sanPFlip`, reported setup time 2 | Standalone setup returns to its exit at 2, but the host dispatches at its initial exit and is halted accepting at 11. The guard at time 0 refutes `hPfirst` for 2. |
| Coincident verdict states and empty output | The acceptance-first redirect emits `true`, consistent with the repaired docstring. |

The silent noisy-reader control also gives physical output `[true]`, with two captured `true` symbols and capture head 2, supporting `neg2`; the zero-stream host remains live at 10, supporting `neg3`.

**Tooling and evidence ledger — brief points 4 and 7.**

- All **11** regenerated export/landing/cut/probe files are byte-identical to the supplied files. The unit is 988 lines, SHA-256 `c2928ab0a330fee368b0e801de6f4261332d82f950e5a64dcfb164910dfe1fbd`, matching its log.
- The name screen reports no collision against the **17 bundled TCSlib files / 840 names**. Its tree-collision and ordinary pending-collision controls both return 1; legitimate round-1 evidence is allowed. R2-m3 is the additional demonstrated exception-boundary failure. The full 721-file / 282-pending-file census cannot be reconstructed from this bundle.
- Isolation generation makes one writer substitution in each file and one core substitution in the universal probe. The `(j)` mutation returns 1 and deletes a planted stale target. Running the production isolation loop with a sentinel elaborator confirms that neither failed generation invokes it. The logged axiom split is consistent with these sources: seven assembly results depend on the writer contract; the universal probe additionally depends on the core contract.
- Width and lint checks reproduce **0 over-width lines**, **0 FAIL**, and **3 file-size WARN**. The supplied summary contains the claimed 53 PASS entries; I do not relabel those historical Lean executions as independently rerun checks.
- Six supplied base-module hashes match the base log. `Encoding.lean`, the complete pinned tree, snapshot/replay record, and wrapper are absent. Commit ancestry, snapshot identity, the global closure counts, and historical no-write claims remain attestations. These limits do not contradict the verified statement freeze.
- The universal consumer probe's consequent matches the bundled frozen `exists_timed_universal_NDTM` after whitespace removal. Its quantified setup hypothesis remains a fill obligation. The old consumer-probe file itself is not supplied for an independent byte comparison with round 1.

The four earlier architectural rulings stand: keep the catalog rewind and import; carry the setup obligation into UN's fill brief while preserving H1's separate prerequisite; land the public capture export with this gate; keep the verdict leaf inline. No further statement change is required. Fix R2-m3, record its control, and carry out the declared landing replay using the real export.

**Glossary.** Mathematical notation is inherited from the packet. `ι` selects source tapes; `cap` is the capture tape; `tapes` and `heads` are the ambient frame; `pre` is the capture prefix; `out₀` is physical output; `c` is a source configuration; `++` is list concatenation and `|·|` is list length. `TP` is the setup's first-exit time; `m` is the guessed stream length in the assembly; `TQ` is the suffix's first-verdict time; `qentry`, `acc`, and `rej` are suffix entry/verdict states; `w` is the choice word; `a` is a source-tape index. “Live” means the configuration's state is `some` rather than `none`.
