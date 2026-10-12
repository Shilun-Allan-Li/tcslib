# B5b — EXPCOM summit

**Complete delivery: 1/1 target filled, proved modulo exactly the three authorized infrastructure admissions.**

## Scope and base

Repository: `https://github.com/Shilun-Allan-Li/tcslib`.
Starting branch: exactly `complexity/arora-barak-ch3-4`.
Work branch: `fill/ch34-b5b`.
Base: `ebc58d67068c609f41a3d63ee5660f6d5ec9d01c`.
The required `git merge-base --is-ancestor 3ba353460e2d7a877cada66de214dbd3152fe8a7 HEAD` returned 0 before work. No rebase, push or PR; no other branch changed.

The binding brief and named policy, workflow, design and audit records were read. The base has the specified ten sorry-warning declarations; no parallel fill landed in this checkout. The exact names are in `logs/base-sorry-names.txt`.

## Result

**1/1 target filled.** The owned module has zero source sorries; every new private helper is proved. The summit is proved modulo exactly the three authorized infrastructure rows below, as independently confirmed by the dependency census. No partial frontier remains.

The sole public target is `Complexity.NPOracle_EXPCOM_subset_EXP`. Its statement is unchanged. The intended dependency boundary is exactly:

- `Turing.FinOracleTM.exists_plain_simulation` (W2-S);
- `Turing.MachineFormat.exists_polyCanonizer` (§12.11);
- `Turing.MachineFormat.exists_uniformSimulator` (§12.11).

The private decider follows route A: two parse-validity bits plus the all-true-tail test; append false and increment to form the binary deadline; rebuild the simulator's canonical input; direct malformed inputs to the code-empty/input-empty/zero-deadline word; use the uniform simulator's two fields on this image; compose with `FinTM.exists_comp_on_image`; absorb its original-input-length budget into `(2*C+d+2)*2^((c+d)*(m+1))`. The zero-deadline case cites the existing public `FinTM.not_computesInTime_zero`. No theorem assumes a simulator promise on malformed raw input or reduces the choice defining `expCode`.

The summit and three ledger bodies are exact transcriptions of the committed S1210 probe, with only the prescribed private-name substitutions. The route uses W2-C, monotone W2-S from a preloaded choice word, W2-V, the public projection decider and the `ExpPoly` ledger. There is no new host, trace, machine implementation, shell or enumerator. The front end also cites the public pairing-swap row to reuse the clock-before-code rearrangement.

## Owned regions and private declarations

Only `TCSlib/Complexity/Diagonalization/EXPCOM.lean` is changed:

1. The flagged comment and exactly the two sanctioned imports after original line 11 (`Build.CertShell`, `ClassNP.ExpPoly`). No additional Mathlib import.
2. Seventeen private declarations in the original gap after the padding reduction and before the summit docstring.
3. The flagged `Fill appendix (B5b, the §12.10 compositional route)` appended to the summit docstring. The original sketch is preserved and explicitly superseded by the appendix.
4. The summit's body.

No public declaration was added or removed. No existing signature, status text, other declaration, namespace or option was changed. Reversing precisely these four edits produces the base file byte for byte. The report's freeze log also checks the unchanged public declaration order and the exact summit transcription.

| New private declaration | Role |
|---|---|
| `expcom_bits_two_pow` | Little-endian binary clock for a power of two |
| `expcom_inc_prefix` | Carry through the unary true prefix |
| `expcom_all_true` | Empty increment output implies an all-true tail |
| `expcom_tail` | Total nested tail projection |
| `expcom_ok` | The three-part validity bit |
| `expcom_simIn` | Canonical simulator input reconstruction |
| `expcom_front` | Guarded reconstruction with a fixed rejecting fallback |
| `expcom_ok_iff` | Exact characterization of genuine triples |
| `expcom_front_poly` | Polynomial-time front end from public composition rows |
| `expcom_front_triple` | Reconstructed input on a genuine triple |
| `expcom_decider_budget` | Polynomial setup plus simulation fits a linear exponential |
| `expcom_mem_triple` | Unique parsed witness determines EXPCOM membership |
| `expcom_simulator_on_image` | Membership bit and uniform time bound on the front-end image |
| `expcom_decider` | The brief's exact private decider statement |
| `expcom_expPoly_const` | Sanctioned constant ledger transcription |
| `expcom_expPoly_mul_two_pow` | Sanctioned exponential ledger transcription |
| `expcom_summit_budget` | Sanctioned shell/projection/simulation ledger transcription |

Zero-context diff hunk headers (exactly the four owned regions):

```diff
@@ -11,0 +12,3 @@ import TCSlib.Complexity.TuringMachine.CodeSimulator
@@ -300,0 +304,311 @@ theorem EXP_subset_POracle_EXPCOM : EXP ⊆ POracle EXPCOM := by
@@ -350 +664,16 @@ simulation invariant tying the host's configuration coding to `runWith`; the
@@ -352 +681,50 @@ theorem NPOracle_EXPCOM_subset_EXP : NPOracle EXPCOM ⊆ EXP := by
```

Final file: **760 lines, 9 public and 18 private declarations** (17 private additions plus the original padding helper). The brief explicitly waives a file-size cap.

## Duplication and promotion requests

Before screen (unchanged 22-file population):

```
declarations screened: 871; copy pairs (target reproduces >= half of source): 522; reproduced text: 145,426 chars
```

After screen (same complete 22-file population, final source):

```
declarations screened: 887; copy pairs (target reproduces >= half of source): 524; reproduced text: 145,788 chars
```

The only new directed entries are the two directions of the single pre-disclosed binary-clock pair:

```
   EXPCOM.lean::expcom_bits_two_pow  reproduces  Separation.lean::bits_two_pow: 181/193 = 94%
   Separation.lean::bits_two_pow  reproduces  EXPCOM.lean::expcom_bits_two_pow: 181/216 = 84%
```

No base pair was removed.

All counts below use the committed screen's comment-stripped, whitespace-normalized body and greedy tiling with minimum block length 25. The full before/after outputs and detailed pair measurements are included. The S1210 probe remains evidence, outside the module population.

The three authorized private ledger transcriptions have body lengths 34, 266 and 1,348 characters (normalized whole-declaration lengths 90, 344 and 1,551). Compared with both `Classes.b1_poly_succ_le`/`b1_budget` and every `ExpPoly.lean` declaration, none creates a screen pair. Detailed non-threshold matches are in `logs/copy-measurements.txt`.

The binary-clock forced restatement shares 181 characters with private `Separation.bits_two_pow`: 181/193 = 93.78% of the source, 181/216 = 83.80% of this body. **Promotion request:** expose this fact from `Encoding.lean` or `Build/Convention.lean`; then this private copy can be retired. `Separation` is not imported.

The all-true criterion is the needed direction of the unavailable `MeyerTableau.incFixed_eq_none_iff`. Its body has 247 characters; tiling finds 0 shared characters against that 93-character source body. It is nevertheless disclosed as the brief's forced mathematical restatement. **Promotion request:** move the public overflow/all-true criterion, or the needed empty-output direction, to `Build/Convention.lean`. No circuit module is imported.

The membership lemma has 434 body characters. Against the frozen padding reduction it shares 194/1,462 = 13.27% (44.70% of this body); against just its frozen parse-uniqueness block, 194/501 = 38.72%. It is one private proof, used by the simulator correctness argument. The frozen padding proof is not refactored. A shared triple-uniqueness lemma is a further promotion candidate.

**New in-file pairs: none.** There is no in-file pair at or above 90% requiring factoring. No undisclosed cross-file pair was introduced; the sole new cross-file pair is the forced binary-clock fact above.

The exact summit transcription contributes another 2,063 normalized body characters. For cumulative coverage, a conservative upper count assigns the **whole bodies** of the three ledger lemmas, the summit, and the three forced restatements (bits, unary test, parse uniqueness), plus the prior 322-character CH34-D3 mirror: **4,930/13,500 = 36.52%** of all extracted body characters (base denominator 3,626). This is above one fifth. It excludes frozen structure text from the copied-proof numerator. This accounting is deliberately broader than the text screen; see `logs/copy-coverage.txt`.

**New copies:** the prescribed probe transcriptions and the three pre-disclosed forced restatements listed above. No other new copies.

These disclosed additions are new debt in a file already under CH34-D3. Under the brief and workflow §4 the maintainer must open the required human-review item at integration; this delivery does not edit `backlog.md`. No additional cross-file copy is accepted beyond the brief's pre-disclosures. Parallel batches are outside this checkout and screen.

Escalations: none identified in the statements or construction. The final compilation and both unchanged probes pass; the independent admission walk has exactly the required three sources.

## Frozen status text for maintainer update

The following original header is preserved verbatim, including the now-stale summit status and route. The B5a continuation/maintainer owns its update:

```
## Main results (B5a partial: five bodies filled; the B5b summit remains sorried)

* `Turing.exists_uniformMachineCode` — a uniformly-timed scheme exists.

* `Complexity.EXP_subset_POracle_EXPCOM` — one padded query decides any
  `EXP` language.
* `Complexity.NPOracle_EXPCOM_subset_EXP` — the fill summit: deterministic
  exponential-time simulation of a polynomial-time oracle NDTM, answering its
  queries with the timed universal machine.
* `Complexity.POracle_EXPCOM_eq_EXP`, `Complexity.NPOracle_EXPCOM_eq_EXP`,
  `Complexity.POracle_EXPCOM_eq_NPOracle_EXPCOM` — the chained identities.
  [AB09, Example 3.6(3)]
```

## Verification

Lean 4.25.0 (`cdd38ac5115bdeec5f609e9126cce00f51ae88b3`), pinned mathlib and manifest dependencies. Mathlib cache obtained with `lake exe cache get`; no `lake build`. Every Lean proof check uses the unchanged `scripts/lean_check_tree.sh`, requiring process exit 0, no error diagnostic and a fresh olean.

The sandbox's numeric process namespace differs from its mounted `/proc`, so the compiler's self-path lookup required a small `readlink` compatibility shim redirecting only its own `/proc/<getpid>/exe` request to `/proc/self/exe`. The compiler and kernel were not modified. The downloaded compiler and standard installed compiler have identical checked executable/shared-library hashes; the latter is used to share runtime pages under memory pressure. The interrupted bootstrap attempt is retained separately and is not counted as a pass for module 20. Toolchain details and shim source are included.

The 63-module bootstrap passed with exactly the prescribed ten sorry-warning declarations. After the decider was proved first (the original summit still sorried), the summit was filled and the changed module plus all following modules (58–63) were rechecked, following the check script's incremental rule. The final sweep log combines the byte-unchanged upstream 1–57 with that final recheck. All unowned tracked files are byte-identical to the base.

`logs/final-attestation.txt` confirms the declaration-name set is exactly the baseline minus the summit. The final tail is:

```
TCSlib/Complexity/Diagonalization/NTimeHierarchy.lean:326:8: warning: declaration uses 'sorry'
PASS TCSlib/Complexity/Diagonalization/NTimeHierarchy
CHECK TCSlib/Complexity/Diagonalization
PASS TCSlib/Complexity/Diagonalization
FINAL SUMMARY: 63 modules; 0 errors; 9 authorized sorry warnings; owned module 0 sorry warnings.
```

Both committed probes were rerun unchanged through the check script, with exit 0 and fresh oleans. All six S1210 `rfl` identities hold. Its one probe-local decider admission remains intentional. Detecting controls, quoted verbatim:

```
Complexity.NPOracle_EXPCOM_subset_EXP': [Complexity.exists_EXPCOM_decider,
 Turing.FinOracleTM.exists_plain_simulation,
 Turing.MachineFormat.exists_polyCanonizer,
 Turing.MachineFormat.exists_uniformSimulator]
Complexity.EXP_subset_POracle_EXPCOM: [Turing.MachineFormat.exists_polyCanonizer,
 Turing.MachineFormat.exists_uniformSimulator]
```

SHA-256 comparisons in `logs/probe-identities.txt` confirm the copied probes are unchanged. The full outputs and command-success receipts are included.

The campaign summit's separate axiom print and admission walk, in `logs/axioms.log` (the command is copied unchanged into a scratch file outside `TCSlib/`):

```
'Complexity.NPOracle_EXPCOM_subset_EXP' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
Complexity.NPOracle_EXPCOM_subset_EXP: [Turing.FinOracleTM.exists_plain_simulation,
 Turing.MachineFormat.exists_polyCanonizer,
 Turing.MachineFormat.exists_uniformSimulator]
Complexity.EXP_subset_POracle_EXPCOM: [Turing.MachineFormat.exists_polyCanonizer,
 Turing.MachineFormat.exists_uniformSimulator]
```

Thus the only axioms are `propext`, `Classical.choice`, `Quot.sound` and `sorryAx`; the latter is reached through exactly W2-S and the two §12.11 rows, with no local admission.

Style lint: `python3 scripts/campaign_style_lint.py TCSlib/Complexity/Diagonalization` returned 0:

```
style_lint: 0 FAIL, 0 WARN over 4 files
```

`git diff --check` also returned 0 with no output.

## Delivery and replay

Delivery commit: `7a2ed9ed5fc2f61c27137562da638d952361ea34` on `fill/ch34-b5b`, one commit above the recorded base. The working tree is clean. The patch series contains only the owned file, and the bundle verifies successfully with that base as its sole prerequisite. No push or PR was made.

Source SHA-256: `8b86604daa159c7b0af68d81ba1c5e6729cbe6d141484e745abfe3e673ac28e6`.

The final source, patch, bundle, report and all included evidence are covered by `SHA256SUMS`. The four zero-context diff hunks are exactly those quoted above.

The zip contains the full modified source, this report, a format-patch series against the recorded base, a prerequisite-bearing git bundle, verification and duplication logs, the unmodified check-only probes/admission-walk source, supporting check scripts and `SHA256SUMS`. No generated oleans, toolchain or dependency repositories are required in the delivery. Apply the patch with `git am -3` against the campaign integration branch, or fetch the working branch from the bundle after satisfying its recorded base prerequisite.
