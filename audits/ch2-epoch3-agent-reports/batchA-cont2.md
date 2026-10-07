# Chapter 2 — E3 continuation A2: reverse host complete; scope escalation

**PARTIAL: 1 of 3 owned targets closed.** `NEXP_subset_iUnion_NTIME` is proved.
Theorem 2.22 and its contraposition remain unchanged admissions because their
binding route requires a still-admitted, explicitly excluded theorem. This is
an escalation under the statement/scope freeze, not a completed A2 gate.
No new private declaration is admitted.

## Provenance and exact frontier

- Repository: `https://github.com/Shilun-Allan-Li/tcslib`.
- Required and actual base: `d5ac2377b66010304c2b8a2727ce37b1dc86cbdd`.
- Working branch: `fill/ch2-e3cont-A2`.
- Delivery commit: `3e7b23661b7973efd29d4252596dfd24e676828f`.
- Delivery tree: `7cf840dfe8079eb3a663fb0484c47f4edd2ae6f9`.
- The new brief was read from `complexity/arora-barak-ch1` at remote tip
  `dd22fb9e33a17b81ce7f334c248c59893af17e48`; its explicitly required ancestor
  was object-verified and used as the source base. No guessed base was used.
- All binding briefs, both predecessor reports, `AGENTS.md`, and `policy.md`
  were read. The brief's explicit pinned shell-verification instructions
  governed verification. Single-agent execution; no push, PR, rebase, or
  modification of another named local branch.

| A2 order | Target | Status |
|---|---|---|
| 1 | `NEXP_subset_iUnion_NTIME` | Closed: native binary countdown scheduler, integrated reverse host, exact witness correspondence, all-branch totality, exponential budget normalization. |
| 2 | `EXP_eq_NEXP_of_P_eq_NP` | Original statement, docstring and admission unchanged. Escalation below. No new paired padding verifier or input-to-padded-word emitter is claimed. |
| 3 | `P_ne_NP_of_EXP_ne_NEXP` | Unchanged admission; not filled ahead of target 2 and not made dependent on its admission. |

The original campaign's targets 1, 3, and 6 are untouched, including the
entire displayed native-body existential in `ntime_expPow_subset_NEXP` and
the entire `EXP.lean` file. Both predecessors' 104 source private declarations
are untouched, as are all B2/continuation proofs and all `Build/` files.

## Escalation: binding route versus excluded admitted dependency

At the required pin, the binding docstring of `EXP_eq_NEXP_of_P_eq_NP` begins
its proof route with the inclusion `EXP ⊆ NEXP` supplied by
`Complexity.EXP_subset_NEXP`. In `TCSlib/Complexity/ClassNP/EXP.lean`, lines
2531–2532, that theorem is still `by sorry`.

The A2 brief simultaneously:

1. requires Theorem 2.22 to follow this audited certificate route;
2. explicitly excludes `EXP_subset_NEXP`, prohibits modifying `EXP.lean`,
   and reserves the shared split-search machinery for a different workstream;
3. sanctions **no** `sorryAx` dependency and requires empty admission roots.

Consequently, citing that inclusion would fail the required axiom gate.
Re-proving the excluded inclusion privately by duplicating its split-search
construction would silently expand the deliberately restricted scope. Neither
was done. This is a dependency/scope conflict, **not** a claim that the frozen
mathematical theorem is false or unprovable. The independent first target was
completed before delivery; no new work on the subsequent targets was started.

**Requested maintainer resolution:** supply the proved `EXP_subset_NEXP` on a
new authorized pin and issue a continuation for the remaining two targets, or
explicitly revise the binding scope/route to provide another admission-free
forward inclusion. The reverse inclusion in Theorem 2.22 still needs the
nested-pair polynomial verifier and the deterministic exponential pad emitter;
this delivery does not claim those are complete.

The two exact checks (all-true pad with the exact evaluated length, and witness
length exactly equal to it), malformed outer/inner pair rejection, and
pre-validation polynomial bit charging remain binding obligations of that
continuation. The existing `e3_exp_bits_timed`/`e3c_eval_budget` assets are
available but alone discharge neither verifier construction nor either check.
The native countdown emitter proved here can serve as the bespoke pad-emission
phase, but joining it to exact `pairEncode` output and the captured padded
language decider remains to be done.

Requested shared lemmas: **none**. Statement changes: **none**. The escalation
requests a resolved dependency/scope contract, not permission to conceal an
admission or alter a theorem.

## Reverse-host binding obligations

| Obligation | Discharging declarations and precise behavior |
|---|---|
| Native binary evaluation | The unchanged `e3_exp_bits_timed` computes the canonical bits for the exact exponential width on every input. `a2_exp_scheduler` uses `bufferedComp_start` and `bufferedSecondCfg_run` at the actual intermediate configuration; output is captured and rewound before the countdown starts. |
| Genuine countdown startup | `a2_copy_step`, `a2_copy_run`, `a2_load_rewind`, `a2_start` copy the binary word from genuine blank startup and rewind to counter head zero, with empty output. The mandatory move off the right blank handles the empty word. |
| Binary countdown and exact emission | `a2Debit`, `a2Debit_value`, `a2Debit_length`, `a2Borrow_*` prove fixed-width borrow and rewind. `a2_countdown` emits exactly one true for each successful debit and none at underflow, preserving arbitrary output prefixes. `a2_decode_computes` includes copying, every debit, and the final underflow. Coefficient zero is the empty binary word and causes zero guess writes. |
| Actual completion and length-only boundaries | `b2UnaryTM`, `b2_unary_run`, `b2_unary_mask`, and `b2_unary_first` are reused unchanged. The scheduler is normalized to unary physical input reads, so its complete trajectory, first halt, and emission mask depend only on input length. The mathematical bound supplies existence of a first halt; it is never a native clock. |
| Physical-position witness extraction and coverage | The unchanged `b2_guess_coverage` and `b2_host_contract` consume `contSelect`/`cont_select_surjective` and the actual emission positions. Startup offsets are included in full branch words. Administrative choices are ignored; only an actual emission writes its current nondeterministic choice as the next certificate bit. |
| Original input, assembly, and verifier isolation | The unchanged `b2_start`, `b2_assembly`, and `b2_verify_timed` preserve and assemble `x ++ u`, initialize blank verifier tapes and virtual head one, guard both input boundaries, capture every emission including the halting emission, and emit one final decision bit. |
| Table coincidence | The host is exactly the existing `b2Host` instantiated with the new scheduler. `b2_tables_coincide` remains the definitional proof for all reads outside live guessing. `contGuessTM`'s definition ignores choices on silent scheduler transitions inside that phase as well. |
| Totality and membership | `a2_compile` invokes the whole-host contract on every branch, not merely accepting branches. Every extracted/covered certificate has exactly the prescribed exponential length. Verifier run times may depend on its bits; the proved upper bound is common to all branches. |
| All-length time normalization | `a2_host_bound`, `a2_exponent_bound`, `a2_envelope`, and `a2_normalize` absorb every phase and explicitly handle lengths zero and one. The reused `acceptsWithin_iff_of_halts` supplies both backward truncation and forward padding (internally using `FinNDTM.AcceptsWithin.mono`). |

The countdown is one native emission phase, not a claim that streaming a
function is free. Its local subtraction/rewind implementation adapts the
proved private counter template from the pinned `Build/Loop.lean` into the
owned file, extending its finite control with copying and emission. No
library file, private library name, or sorried emitter specification is cited.

## Verification

- **Final full fresh sweep: 57/57 modules**, 57 fresh nonempty oleans,
  exit **0**, **zero `error:` lines**, `FULL_SWEEP_COMPLETE`. The output
  directory was absent before this sweep. The separate owned-and-downstream
  checks also passed.
- **19 admission warnings**, down from the base's 20. This includes the seven
  concurrent emitter specifications and all remaining original target
  admissions; the requested completed-A2 count of 17 is **not** claimed.
- `NEXP_subset_iUnion_NTIME` prints exactly
  `[propext, Classical.choice, Quot.sound]` with **empty admission roots**.
- Checked-kernel traversal covers declaration types and values (including
  opaque values), and inductive constructors. All **29 source helpers / 121
  new helper-and-generated declarations** have empty roots and at most the
  standard axiom triple, including the retained unreferenced success criterion.
- All **12** epoch-2 regression headlines printed by the committed closure
  template retain empty roots and the standard triple.
- Both unfilled owned targets and the three excluded padding targets remain
  at exactly their own original admission roots. The log's
  `A2_PARTIAL_AUDIT_PASS` validates this explicit partial inventory; it does
  **not** certify the three-target completion gate.
- Exact preservation, `git diff --check`, bundle verification, and detached
  patch replay pass. The work branch is clean.
- Pinned Lean **4.25.0**, commit `cdd38ac5115bdeec5f609e9126cce00f51ae88b3`;
  mathlib `029db123ddaa7f8fd0d18cea3b1b33bf84dacd1e`. All 11 installed package
  revisions match the manifest and have no tracked source changes; four
  optional documentation packages were not installed.
- `lake exe cache get` was invoked **once** and failed on leantar archive
  ownership. The disclosed recovery uses the extracted leantar executable
  and the pinned hash-directed cache API. Its filtered import closure unpacked
  all **916** required files successfully. The initial full-cache recovery was
  interrupted in favor of that smaller closure. `environment.txt`,
  `RecoverCache.lean`, and the cache logs record the procedure.
- The host required the included own-process executable-path adapter; it
  changes only `/proc/<own pid>/exe` resolution, not Lean or its kernel.
  No `lake build` was run. All TCSlib checks used the committed tree script;
  the final axiom program used the same fresh olean tree.

Final sweep tail:

```text
CHECK TCSlib/Complexity/TuringMachine
CHECK TCSlib/Complexity/ClassP
CHECK TCSlib/Complexity/Uncomputability
CHECK TCSlib/Complexity/Formulas
CHECK TCSlib/Complexity/CookLevin
CHECK TCSlib/Complexity/ClassNP
FULL_SWEEP_COMPLETE
```


## Declaration inventory and preservation

Only `TCSlib/Complexity/ClassNP/Nondeterminism.lean` changes: 608 insertions
and two deletions (the previous target admission and the docstring closing line).
The existing docstring is preserved with an append-only A2 completion paragraph.
`verify_surface.py` removes only the new private block, appended paragraph and
new target proof, then reconstructs the pinned original file **byte-for-byte**.
It also checks the exact public signature, private-only inventory, absence of
new admissions, and that git has exactly the one permitted changed path.

- Final source size: **5013 lines / 259945 UTF-8 bytes**.
- Source SHA-256: `144d18a669f4aa70bdd903c385089b37d39c4a6a2186393d510f5a015b34b3ee`.
- Owned-file explicit admissions: **5 → 4**, removing only the reverse-host one.
- All **29** new source declarations are private and proved:

- `a2Debit`
- `a2BorrowPos`
- `a2BorrowPos_le`
- `a2Debit_length`
- `a2Value`
- `a2Value_bits`
- `a2Debit_value`
- `a2Debit_success`
- `a2Buffer_read`
- `a2Buffer_write`
- `a2DebitTM`
- `a2DebitCfg`
- `a2Borrow_step`
- `a2Borrow_run`
- `a2Borrow_rewind`
- `a2Borrow_correct`
- `a2_countdown`
- `a2LoadCfg`
- `a2_copy_step`
- `a2_copy_run`
- `a2_load_rewind`
- `a2_start`
- `a2_decode_computes`
- `a2_exp_scheduler`
- `a2_host_bound`
- `a2_compile`
- `a2_exponent_bound`
- `a2_envelope`
- `a2_normalize`

`a2Debit_success` is retained as an explicit positive-value/underflow check.
All other new declarations contribute to the filled target. Generated auxiliary
declarations are included in the kernel audit as well. The numeric all-length
absorption proof follows the proved `enumExponent_bound` precedent in
`EXP.lean`, without modifying that file or citing a private name across modules.

The brief's size exception and in-file ownership rule are retained. Style lint
reports **0 FAIL / 5 WARN**, the warnings being the existing large-module
exceptions. Lean's non-fatal tactic/simplification warnings remain visible;
zero errors does not mean warning-free output.


## Archive and reproduction

`fill-ch2-e3cont-A2.zip` is flat: every member is at the root, including
`SHA256SUMS`, which covers every other member. The payload includes the report,
full modified source, numbered format-patch, incremental git bundle, final
sweep and axiom logs, audit/surface scripts, dependency/recovery records, and
the five binding brief/report snapshots. No toolchain, dependency cache, olean,
or full repository clone is included.

| Archive item | Use |
|---|---|
| `Nondeterminism.lean` | Full replacement for `TCSlib/Complexity/ClassNP/Nondeterminism.lean`. |
| `0001-*.patch` | Apply with `git am` at the exact required base, preserving Codex authorship. |
| `fill-ch2-e3cont-A2.bundle` | Alternative incremental delivery; requires the recorded base and contains only the A2 work-branch ref. |
| `final-sweep.log` | Required fresh 57-module sweep. |
| `axiom-print.log`, `ClosureAxioms.lean` | Public axiom prints and checked-kernel closure traversal. |
| `verification.json`, `surface-check.json` | Machine-readable verification and preservation results. |
| `run-axiom-audit.sh`, `verify_surface.py` | Reproduce the audits against the source checkout. |
| `environment.txt` | Pinned setup, disclosed recovery and reproduction instructions. |

Run `sha256sum -c SHA256SUMS` after extraction. Use the repository's committed
`lean_check_tree.sh` and module order with the pinned toolchain/cache to repeat
the sweep; the archive's script copy is provenance and expects its original
`scripts/` location if run directly. Set `TCSLIB_OLEANS` to the freshly checked
tree before running `run-axiom-audit.sh`.

The incremental bundle verifies, and a detached `git am` replay at the required
base reproduces the exact delivery git tree and byte-identical source. The
replay worktree was removed; no other named local branch was changed.

## Notation

In the source and obligation table, `x` is the original input and `u` is its
certificate. `C,c` are the existing exact-width parameters; `E` is the binary
evaluator machine in `a2_exp_scheduler`; `R` is its numerical output value;
`bits` is that value's canonical little-endian word; `P` is the positive
polynomial evaluation envelope; `m` is input length plus certificate length
plus one. `A,B,K,r,d` are fixed natural time coefficients/degrees as typed in
the corresponding declarations; `S,M,V` denote scheduler, verifier machine,
and verifier language. `τ` is the length-indexed actual first scheduler halt.
All other identifiers are declarations listed in this report or the pinned
source. These are implementation names, not changes to the public statements.
