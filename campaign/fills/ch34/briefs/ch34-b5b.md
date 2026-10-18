# Ch3–4 fill campaign — B5b: the `EXPCOM` summit `NP^EXPCOM ⊆ EXP` (`Diagonalization/EXPCOM.lean`, by declaration)

## Repository and branch — read this before anything else

- Clone: `https://github.com/Shilun-Allan-Li/tcslib`
- Check out branch **`complexity/arora-barak-ch3-4`**, this exact branch, NOT `main`.
- Before you start, confirm that `git merge-base --is-ancestor 3ba353460e2d7a877cada66de214dbd3152fe8a7 HEAD`
  succeeds. That commit contains:
  - the closed wave-1 statement gate (PR #43) and its records (`audits/wave1-statements-*`), with
    the §12.10 statement probe `audits/evidence/wave1-statements/S1210StatementsProbe.lean.txt`;
  - W2-C (`FinOracleNDTM.exists_choiceTM`) and W2-V (`FinTM.exists_certificateShell`), both proved;
    W2-S (`FinOracleTM.exists_plain_simulation`) with its statement frozen and its body sorried;
  - the first B5a delivery (`exists_uniformMachineCode`, `EXP_subset_POracle_EXPCOM` and the three
    `EXPCOM` identities, proved modulo the two §12.11 rows) and `audits/fills-4-integration.md`;
  - this brief's order list `briefs/orders/ch34-b5b.txt`, base sorry set, screen base, and the
    pre-ship log of `audits/evidence/ch34-wave5/B5bPreShip.lean.txt`.

  If the check fails, **stop**.
- Create your working branch off the campaign branch: **`fill/ch34-b5b`**. Record the base hash in
  `REPORT.md`. Never rebase.
- **Delivery is by zip, not PR or push** (`workflow.md` §4): `fill-ch34-b5b.zip`, containing
  `REPORT.md`, the full modified source, a `git format-patch` series against your base, a git
  bundle, the final sweep log, the axiom log, and `SHA256SUMS`.

## Parallel batches this round (disjoint files or declarations; never edit another batch's file or declaration)

| Batch | Brief | Owns |
|---|---|---|
| S1b, the configuration-graph summit | `briefs/ch34-s1b.md` | `SpaceComplexity/ConfigGraph.lean` |
| B3a | `briefs/ch34-b3a.md` | `SpaceComplexity/Constructible.lean` |
| B4, TQBF membership | issues later, after a pre-issue promotion | `ClassPSPACE/TQBF.lean` (`TQBF_mem_PSPACE` only) |
| **B5b, the `EXPCOM` summit** | `briefs/ch34-b5b.md` | `Diagonalization/EXPCOM.lean`, **by declaration** (ground rule 1) |

In flight from the previous round:

| Batch | Brief | Owns |
|---|---|---|
| §12.10 W2-S, continuation | `briefs/w2-fill-oraclesim-cont.md` | `TuringMachine/Build/OracleSim.lean` |
| §12.8b record tables, continuation | `briefs/w1-fill-recordtable-cont.md` | `TuringMachine/Build/RecordTable.lean` |
| B5a, continuation | `briefs/b5a-fill-cont.md` | `TuringMachine/CodeSimulator.lean`, and **status text only** in `TuringMachine/Codes2Tape.lean` and `Diagonalization/EXPCOM.lean` |

Also open: maintainer PRs on the facade `TuringMachine.lean` and on `Build/Embed.lean` (one
additive export), and an audit program. A further maintainer PR, B4's pre-issue promotion, will add public CNF-grammar facts to `Formulas/CNFEncoding.lean` and one head-interval lemma to a core file; it is additive. **Not yours (the §12.8 A–C files, gate closed; cite, never edit):**
`Build/Catalog`, `Build/Seam`, `Build/Scan`, `Build/CfgRecord`, `Build/InputCall`.

**You share `EXPCOM.lean` with the B5a continuation**, by the user's decision (2026-10-12). The
continuation may change status text that is outside your regions: the module's "Main results"
heading and its tags, and the `exists_uniformMachineCode` and `expCode` docstrings. Your regions
are listed in ground rule 1. A parallel batch's work is invisible to your base and your screen. The
two patch series are merged by `git am -3` at integration, which is why your hunks must stay
inside your regions.

## What this is

**Batch B5b** (plan §4e, cluster B5's summit; summit 2 of plan §6). Fill
`Complexity.NPOracle_EXPCOM_subset_EXP` ([AB09, Example 3.6(3)], the last inclusion of
`EXP ⊆ P^EXPCOM ⊆ NP^EXPCOM ⊆ EXP`). The user dispatched it on 2026-10-12 with a by-declaration
carve-out of `EXPCOM.lean`, and with the `EXPCOM` decider **private**, so the batch adds no new
public statement.

The route is **already elaborated**. The §12.10 statement probe derives the summit as
`NPOracle_EXPCOM_subset_EXP'` (probe :199–258), `rfl`-identical to the campaign statement, from the
landed §12.10 rows. It does so modulo exactly one probe-local lemma, `exists_EXPCOM_decider`
(probe :170–184), which is **B5's own obligation** (design §12.10, closing paragraph: "the summit's
query dispatcher. It is a B5 obligation, not a §12.10 row"). Your work:
1. write the decider as a `private` declaration in `EXPCOM.lean`, from the probe's statement;
2. transcribe the probe's summit derivation and its ledger lemmas as privates;
3. add a flagged **Fill appendix** to the summit's docstring naming the compositional route.

When you land, the three `EXPCOM` identities and `baker_gill_solovay` rest **only** on the
proved-modulo rows below. They need no file change (they are not yours).

**Proved modulo, exactly:**
- W2-S, `Turing.FinOracleTM.exists_plain_simulation`, through the proved corollary
  `exists_plain_simulation_of_monotone`;
- B5a's two §12.11 rows, `Turing.MachineFormat.exists_polyCanonizer` and
  `Turing.MachineFormat.exists_uniformSimulator`, through `Complexity.expCode`, on which
  `EXPCOM` itself rests.

**Read first:** `Diagonalization/EXPCOM.lean` in full; the S1210 probe in full; design §12.10
(`machine-library-design.md`, "12.10 Oracle-call simulation") and §12.11; the wave-1 findings and
resolutions (`audits/wave1-statements-{findings,resolutions}.md`, note 42 and resolution 17); the
P3.2 round-2 findings (`audits/ch3-p32-r2-findings.md`, the uniform simulator's contract and the
summit's ledger); `policy.md`; `workflow.md` §4.

**Pre-ship check (maintainer, executed at this brief's ancestor):** `audits/evidence/ch34-wave5/B5bPreShip.lean.txt`, a check-only
probe. It imports `EXPCOM` with the two sanctioned imports, and `#check`s the target and every row
the routes cite. The S1210 probe was re-run alongside it at the issue tree. Both gave 0 errors (`audits/logs/ch34-wave5-preship.log`).

## Owned files and targets (modify these and nothing else)

Lines are at the issue commit.

| # | File:line | Target | Route | Uses |
|---|---|---|---|---|
| 1 | `Diagonalization/EXPCOM.lean:351` | `Complexity.NPOracle_EXPCOM_subset_EXP` | S1210 probe `NPOracle_EXPCOM_subset_EXP'`, transcribed; the private decider as dispatcher | — |

- **Owned:** in `Diagonalization/EXPCOM.lean`, the four regions of ground rule 1. Nothing else.
- **Not yours:** every other declaration and every comment in `EXPCOM.lean`, including the module
  header. Also not yours: `Build/OracleSim.lean` (W2-S), `CodeSimulator.lean` (B5a), `Build/CertShell.lean`,
  `ClassOracle/Classes.lean`, `Relativization.lean`, the facades, and the S1210 probe (audit evidence).
- Fill the decider first, then the summit.

### Proof routes (binding)

**A. The private dispatcher.** The probe's statement, verbatim except for the name (and `private`):

```lean
private theorem expcom_decider :
    ∃ (D : FinTM Bool) (A B : ℕ), D.DecidesInTime EXPCOM fun m => A * 2 ^ (B * (m + 1))
```

Do **not** name it `exists_EXPCOM_decider`. The S1210 probe declares that public name
probe-locally (`Complexity.exists_EXPCOM_decider`), and the probe must stay re-runnable unchanged.

Route: parse `z`, rebuild the simulator's input, and run `expCode.simulator` on the image of a
polynomial-time front end.
1. **Validity bit.** Set `tl z := pairSndD (pairSndD z)` and
   `ok z := (pairDecode z).isSome && (pairDecode (pairSndD z)).isSome && decide ((incFixed (tl z)).getD [] = [])`.
   `ok z = true` iff `z = pairEncode α (pairEncode x 1ⁿ)` for some `α, x, n`. For the reverse
   direction use `Turing.eq_pairEncode_of_pairDecode` twice. The third conjunct holds exactly on
   all-`true` tails: `incFixed` overflows (`none`) exactly there, and otherwise returns a word of
   the same, positive length. Polynomial time:
   - `polyTimeComputable_of_linear FinTM.computesFunInTime_pairValid`, also composed after `pairSndD`;
   - `FinTM.computesFunInTime_incFixed` and `FinTM.computesFunInTime_ifEq [] [true] [false]`, after
     `pairSndD` twice;
   - combined with `polyTimeComputable_and` twice, and `convert … using 1; funext` as in
     `polyTimeComputable_and`'s own proof.
2. **The rebuilt input.** Set `bits2 z := (incFixed (tl z ++ [false])).getD []`. On a tail `1ⁿ` this is
   `replicate n false ++ [true] = Nat.bits (2 ^ n)`. Then
   `simIn z := pairEncode (pairEncode (bits2 z) (pairFstD z)) (pairFstD (pairSndD z))`.
   Polynomial time from `FinTM.computesFunInTime_appendBit false`, `FinTM.computesFunInTime_incFixed`,
   `polyTimeComputable_pairFstD`/`_pairSndD`, two applications of `PolyTimeComputable.pairEncode`,
   and `PolyTimeComputable.comp`.
3. **The front end.** `front z := if ok z then simIn z else w₀`, where
   `w₀ := pairEncode (pairEncode [] []) []` is the simulator input for code `[]`, input `[]` and
   deadline `0` (`Nat.bits 0 = []`). It is polynomial by `polyTimeComputable_ite` with
   `polyTimeComputable_const w₀`. Any machine fails `ComputesInTime x [true] 0`, because the
   initial state is `some q₀` (`Cfg.init` is `@[simp]`). So `simulator_rejects [] [] 0` answers
   `[false]` on `w₀`. **The simulator has no promise on malformed inputs**
   (`audits/ch3-p32-r2-findings.md`, the `UniformMachineCode` contract: "the dispatcher constructs
   the specified input"). It is only ever run on `simIn` of a genuine triple, or on `w₀`.
4. **The answer on the image.** With `d := expCode.simDegree` and
   `T₂ m := d * (m + 2 ^ m + 1) ^ d`, prove
   `∀ z, expCode.simulator.ComputesInTime (front z) [MultiTapeTM.indicator EXPCOM z] (T₂ z.length)`.
   - **Genuine triple** `z = pairEncode α (pairEncode x 1ⁿ)`:
     - `front z = pairEncode (pairEncode (Nat.bits (2 ^ n)) α) x`;
     - `UniformMachineCode.simulator_accepts`/`_rejects` give the bit
       `(expCode.decode α).toFinTM.ComputesInTime x [true] (2 ^ n)` within
       `d * (|α| + |x| + 2ⁿ + 1)^d ≤ T₂ |z|`, by `Turing.length_pairEncode` twice and `2ⁿ ≤ 2^|z|`;
     - the bit is the membership bit, by parse uniqueness (`Turing.pairEncode_injective` twice,
       then `List.length` on the replicated tails).
   - **Otherwise** `z ∉ EXPCOM` (a witness would make `ok z = true`), and `w₀` answers `[false]`
     within `d ≤ T₂ |z|`.
5. **Compose.** `Turing.FinTM.exists_comp_on_image M expCode.simulator front (fun z => [indicator EXPCOM z]) T₁ T₂ hM hU`
   gives a machine within `2·T₁ n + T₂ n + 2`, where `T₁ n = C·(n + 1)^c` comes from
   `PolyTimeComputable front`. `exists_comp_on_image` takes `U` correct **on the image** and
   measures `T₂` at the **original** length, with no monotonicity. `FinTM.DecidesInTime`
   (`ClassP/DTIME.lean`) is that statement at `[indicator]`. Absorb the budget with one private
   arithmetic lemma, for instance
   `2·C(m+1)^c + d(m + 2^m + 1)^d + 2 ≤ (2C + d + 2)·2^((c + d)(m + 1))`
   (from `m + 1 ≤ 2^m`); any constants suffice. Close with `FinTM.ComputesInTime.mono`.

**B. The summit.** Transcribe the S1210 probe's `NPOracle_EXPCOM_subset_EXP'` (probe :208–258)
**as is**, replacing `exists_EXPCOM_decider` by `expcom_decider` and the probe's ledger lemmas by
your private copies. In order, the steps are:
1. `FinOracleNDTM.exists_choiceTM N`;
2. the monotone decider budget `hτ`;
3. `FinOracleTM.exists_plain_simulation_of_monotone Mc D EXPCOM _ hτ hD`;
4. the index `jP`, and `hshell` (`FinTM.prefixWords_update`, `MultiTapeTM.runFrom_add`,
   `MultiTapeTM.runFrom_of_halt`);
5. `FinTM.exists_certificateShell`;
6. `exists_proj_decider`;
7. `FinTM.certificateShell_proj`;
8. `FinOracleNDTM.mem_iff_exists_choiceOut`;
9. `ExpPoly.mem_EXP` at the summit's ledger.

The ledger lemmas you transcribe as privates are `probe_expPoly_const` (probe :36–38),
`probe_expPoly_mul_two_pow` (:40–47) and `probe_summit_budget` (:102–145). **Do not** transcribe
`probe_poly_succ_le`, `probe_b1_budget`, `probe_pexpcom_budget` or `POracle_EXPCOM_subset_EXP'`:
the summit does not use them, and B1's copies already live privately in `ClassOracle/Classes.lean`.

**C. The Fill appendix.** The docstring's **Proof sketch** (EXPCOM.lean:307–350) is the
pre-§12.10 hand-built route: one host enumerating choice words, simulating step by step and
dispatching queries with a resume seam. Keep it unchanged (statement freeze). Append a flagged
**"Fill appendix (B5b, the §12.10 compositional route)"** that states:
- the hand-built route is superseded (design §12.10, decision 1; wave-1 note 42);
- enumeration is `exists_proj_decider` around the certificate shell (W2-V);
- the per-step simulation and the resume seam are the choice-word machine (W2-C) simulated by
  the one oracle-call trace (W2-S, via `_of_monotone`);
- query answering is the private `expcom_decider`: parse, the rebuilt input, and
  `expCode.simulator` on the image;
- the ledger is the transcribed `ExpPoly` bound;
- the result is proved modulo W2-S and the two §12.11 rows.

## Gate guidance (binding)

- **Wave-1 note 42** (`audits/wave1-statements-findings.md`, row 42): "Accept the compositional
  route". The choice machine is simulated from a preloaded certificate. The shell and projection
  decider then enumerate only exponentially many words, and the budget stays
  exponential-polynomial. This is the route. A branchwise or hand-built host is not.
- **Resolution 17** (`audits/wave1-statements-resolutions.md`; round-2 note 17): **keep a detecting
  control.** After your fill, re-run the S1210 probe. Its census must still detect an admission:
  - `#sorry_sources Complexity.NPOracle_EXPCOM_subset_EXP'` names the probe-local
    `Complexity.exists_EXPCOM_decider` and W2-S;
  - the live control `#sorry_sources Complexity.EXP_subset_POracle_EXPCOM` names the §12.11 rows
    at your base.

  Quote those lines. In your own evidence, run the same admission walk on the campaign summit
  (copy the probe's `#sorry_sources` command into a scratch file **outside `TCSlib/`**). It must
  list exactly `Turing.FinOracleTM.exists_plain_simulation`,
  `Turing.MachineFormat.exists_polyCanonizer` and `Turing.MachineFormat.exists_uniformSimulator`.
  This walk is the summit's own detecting control.
- **Design §12.10, decisions 1 and 5 (user).** One oracle-call trace, nondeterminism by choice
  words, never a branchwise row. **Time only:** add no space clause.
- **P3.2 round 2** (`audits/ch3-p32-r2-findings.md`): queries are answered by the **uniform**
  simulator, whose cost is one polynomial in code, input and deadline jointly. Never use
  `Turing.timed_universal`'s per-code constant; query codes vary with the branch.

## Cited infrastructure (public and proved at the issue commit, unless marked)

- **Summit:** `Turing.FinOracleNDTM.exists_choiceTM`, `Turing.FinOracleNDTM.choiceOut`,
  `Turing.FinOracleNDTM.mem_iff_exists_choiceOut`, `Turing.FinTM.prefixWords_update`
  (`Build/OracleSim`); `Turing.FinOracleTM.exists_plain_simulation_of_monotone` (`Build/OracleSim`,
  proved from the sorried W2-S); `Turing.FinTM.exists_certificateShell`,
  `Turing.FinTM.certificateShell_proj` (`Build/CertShell`); `Complexity.exists_proj_decider`
  (`ClassNP/EXP`); `Complexity.ExpPoly`, `ExpPoly.mem_EXP`, `ExpPoly.of_le`, `ExpPoly.add`,
  `ExpPoly.mul`, `expPoly_poly` (`ClassNP/ExpPoly`); `Turing.MultiTapeTM.runFrom_add`,
  `runFrom_of_halt` (`Deterministic`); `Turing.Cfg.ofWords` (`Build/Convention`).
- **Decider:** `Turing.FinTM.exists_comp_on_image`, `Turing.FinTM.computesFunInTime_ifEq`
  (`Composition`); `Turing.FinTM.computesFunInTime_pairValid`, `computesFunInTime_incFixed`,
  `computesFunInTime_appendBit` (`Build/Primitives`); `Turing.incFixed` (`Build/Convention`);
  `Complexity.PolyTimeComputable`, `PolyTimeComputable.comp` (`ClassNP/PolyTime`);
  `polyTimeComputable_of_linear`, `polyTimeComputable_const`, `pairFstD`, `pairSndD`,
  `polyTimeComputable_pairFstD`, `polyTimeComputable_pairSndD`, `PolyTimeComputable.pairEncode`,
  `polyTimeComputable_ite`, `polyTimeComputable_and` (`ClassNP/PolyTimePairing`);
  `Turing.pairEncode`, `pairDecode`, `pairDecode_pairEncode`, `pairEncode_injective`,
  `eq_pairEncode_of_pairDecode`, `length_pairEncode` (`Encoding`);
  `Turing.UniformMachineCode.simulator_accepts`, `simulator_rejects`, `simDegree`, and
  `Complexity.expCode`, `Complexity.EXPCOM` (this file); `Turing.FinTM.ComputesInTime.mono`,
  `ComputesInTime.output_unique`, `computesInTime_iff` (`Finite`); `Turing.FinTM.DecidesInTime`
  (`ClassP/DTIME`); `Turing.MultiTapeTM.indicator` (`Deterministic`); Mathlib's
  `Nat.bits_append_bit`, `Nat.bit_val`.
- **Not in your import closure; do not import:** `ClassNP/Transducer`
  (`polyTimeComputable_transduce`), `TimeHierarchy/Separation` (`timeConstructible_two_pow`) and
  `CircuitComplexity/MeyerTableau` (`incFixed_eq_none_iff`). The route above avoids all three.
- **Proved modulo:** W2-S; `exists_polyCanonizer`; `exists_uniformSimulator`, and nothing else.

## Ground rules (binding)

1. **File ownership, by declaration.** In `Diagonalization/EXPCOM.lean`, and nowhere else, you own
   exactly these four regions. Line numbers are at the issue commit.
   - **(a) Imports.** Append exactly two lines after line 11:
     `import TCSlib.Complexity.TuringMachine.Build.CertShell` and
     `import TCSlib.Complexity.ClassNP.ExpPoly`, under one flagged comment line in the style of
     line 10. Lines 6–11 do not change.
   - **(b) New `private` declarations,** inserted in the blank gap at line 300. That is after the
     last line of `EXP_subset_POracle_EXPCOM` (299) and before the summit's docstring (301), inside
     `namespace Complexity`. `private` only: no `public`, `protected` or attribute-bearing
     declaration, and no `section` or `open` that leaks past your region.
   - **(c) The summit's docstring, 301–350.** The existing text does not change. Append the Fill
     appendix (route C) before the closing `-/`. Only that delimiter, on line 350, moves.
   - **(d) The summit's body,** line 352 (`sorry`). The signature on line 351 is frozen.

   **Not yours:**
   - lines 1–5 and 12–299: the module docstring with its "Main results" heading and status
     (69–80), `UniformMachineCode`, `exists_uniformMachineCode` and its tags (118, 147–150),
     `expCode` (171–176), `EXPCOM`, `expcom_padding_bound` and `EXP_subset_POracle_EXPCOM`;
   - lines 353–382: the three identities and `end Complexity`.

   The B5a continuation owns that status text. The maintainer updates the module header at
   integration, including the stale summit bullet at 75–77. **Do not touch it**, even where it now
   reads wrong; report it instead. Any lemma that belongs in a shared file is written privately
   here, flagged in `REPORT.md` as a promotion candidate, and promoted by the maintainer
   (`workflow.md` §4, rule 1).
2. **Statement freeze** over every target and every landed declaration: no renames,
   re-signatures, restatements or attribution edits. Docstrings stay; the flagged
   **"Fill appendix"** is required here (route C).
3. **Status text.** None of the file's status text is yours (rule 1). **No new public
   declaration:** the decider is `private` (user, 2026-10-12).
4. **Escalation** on anything unprovable as stated, including a cited row that does not
   compose as the route says: stop on that item, record the obstruction, and continue with the
   rest.
5. **No touching other sorries.** Cite proved material; never re-prove it.
6. **Imports.** **Sanctioned additions, exactly:** the two of rule 1(a), both acyclic at the issue
   tree (neither closure contains `EXPCOM`). Flag both. No other TCSlib import may be added. A
   Mathlib import is allowed only if a needed lemma requires it; flag it.
7. **One proof per shared argument.** Cite the landed rows the routes name. Never re-walk a landed
   contract inside a target, and never write a second host, loop, trace, shell or enumerator for
   something already public.
8. **Size.** No cap; file size alone is not a driver (user, 2026-10-11). Report the file's final
   line count and its public and private declaration counts.
9. **Continuation budget.** If your budget runs out, deliver a partial zip. Its `REPORT.md` states
   whether the summit is proved, which `private` helpers remain `sorry` (each with a literal
   "Proof sketch"), and what the summit is proved modulo. For example, the summit transcribed over
   a sorried `expcom_decider` is a valid partial. A partial is expected and fine; an unreported gap
   is not.

## Duplication governance (binding)

Run the text-level screen **before and after** (`audits/TEMPLATE.md` failure mode 5; `policy.md`,
**Duplication**). The base, at this brief's issue tree, is `audits/logs/ch34-b5b-screen-base.txt`: **871 declarations, 522 pairs, 145,426 characters**.

```sh
# population: audits/evidence/ch34-wave5/ch34-b5b-screen-population.txt (the S1210 probe is evidence, not a module)
python3 -I audits/evidence/retrofit/copy-text-screen.py <repo-root> \
  TCSlib/Complexity/Diagonalization/EXPCOM.lean \
  TCSlib/Complexity/TuringMachine/Build/OracleSim.lean \
  TCSlib/Complexity/TuringMachine/Build/CertShell.lean \
  TCSlib/Complexity/TuringMachine/ChoiceWords.lean \
  TCSlib/Complexity/ClassNP/Nondeterminism.lean \
  TCSlib/Complexity/ClassNP/EXP.lean \
  TCSlib/Complexity/ClassNP/ExpPoly.lean \
  TCSlib/Complexity/TuringMachine/Composition.lean \
  TCSlib/Complexity/ClassNP/PolyTime.lean \
  TCSlib/Complexity/ClassNP/PolyTimePairing.lean \
  TCSlib/Complexity/ClassNP/Transducer.lean \
  TCSlib/Complexity/TuringMachine/Codes2Tape.lean \
  TCSlib/Complexity/TuringMachine/CodeSimulator.lean \
  TCSlib/Complexity/ClassOracle/Classes.lean \
  TCSlib/Complexity/Diagonalization/Relativization.lean \
  TCSlib/Complexity/TuringMachine/Build/Primitives.lean \
  TCSlib/Complexity/TuringMachine/Build/Convention.lean \
  TCSlib/Complexity/TuringMachine/Encoding.lean \
  TCSlib/Complexity/TuringMachine/OracleNondeterministic.lean \
  TCSlib/Complexity/TimeHierarchy/Separation.lean \
  TCSlib/Complexity/CircuitComplexity/MeyerTableau.lean \
  TCSlib/Complexity/SpaceComplexity/Inclusions.lean
```

- **No new cross-file pair** with an owned-region declaration on one side, except a pair this
  brief pre-discloses (measure it and report it).
- **Known hazards:**
  - **the stale hand-built sketch must not be implemented.** That covers EXPCOM.lean:311–350's
    enumerator, its step-by-step simulation, and its query dispatcher with a resume seam. Each is
    already a landed row (`exists_proj_decider`, W2-C, W2-S). Writing any of them is a second trace;
  - **no second oracle simulation:** never write a host that runs an oracle machine or answers
    queries. W2-S is the one trace, and its private dispatch host is W2-S's own (in flight);
  - **shells and enumerators:** cite `Build/CertShell`'s public shell and `exists_proj_decider`. Never
    copy `Nondeterminism`'s private 2B shell (`cont_choiceVerifier_mem_P`, its loader,
    `choiceCore`), `EXP.lean`'s private enumerator layer (`enumLoop_*`, `a3ShiftTM`), or
    `Nondeterminism`'s `e3ShiftTM`;
  - **pre-disclosed: the transcribed ledger lemmas.** Your copies of `probe_expPoly_const`,
    `probe_expPoly_mul_two_pow` and `probe_summit_budget` are sanctioned transcriptions. The probe
    is not a module, so the screen cannot see that pair; give each lemma's character count. Measure
    them against `Classes.lean`'s private `b1_poly_succ_le`/`b1_budget` and against
    `ExpPoly.lean`, and report any pair;
  - **pre-disclosed: `Nat.bits (2 ^ n)`.** The fact is private in `TimeHierarchy/Separation.lean`
    (`bits_two_pow`, private). Your restatement is a forced pair: measure it, and flag it as a
    promotion candidate (home: `Encoding.lean` or `Build/Convention.lean`);
  - **pre-disclosed: the all-`true` test.** The public `incFixed_eq_none_iff`
    (`CircuitComplexity/MeyerTableau.lean`) is importable only by pulling seven chapter-6 circuit modules into `EXPCOM`'s closure, which is not sanctioned. Prove only the direction you need,
    privately; measure the pair, and flag it as a promotion candidate (home: `Build/Convention.lean`);
  - **pre-disclosed: parse uniqueness.** The decider's membership step repeats the argument that
    `EXP_subset_POracle_EXPCOM` (EXPCOM.lean:283–294, frozen and not yours) carries inline. Put it in
    **one** private lemma used by the decider, measure the in-file pair, and do **not** refactor the
    frozen body;
  - **these forced restatements are new copies in `EXPCOM.lean`,** a file under `backlog.md` CH34-D3 (a later delivery that copies anything into it is new debt). Keep each minimal and measured; the maintainer opens the required human-review item at integration (`workflow.md` §4), and the promotion candidates retire them;
  - **no transducer:** `ClassNP/Transducer` is not a sanctioned import here. Do not hand-build a one-pass
    transducer machine to replace it; use the `incFixed`/`pairValid`/`ifEq` rows above.
- List every new in-file pair with a one-line justification. At 90% or more it is a copy:
  factor it.
- Parallel batches are invisible to your screen. A cross-file pair between your private helpers
  and another batch's, found at integration, is the maintainer's to factor.
- Quote both outputs in `REPORT.md`, which carries **"new copies: none"** (or lists each
  pre-disclosed pair, measured).

## Environment and verification

- Lean 4 v4.25.0, mathlib pinned; `lake exe cache get`; **never `lake build`**. Use
  `scripts/lean_check_tree.sh` for every check.
- **Bootstrap once** from `briefs/orders/ch34-b5b.txt`. It has **63 modules**: the upstream
  closure of `EXPCOM.lean` with its two sanctioned imports, plus every module downstream of it
  (`Diagonalization/Relativization`, the `Diagonalization` facade), at the issue tree.

  ```sh
  ( while read -r m; do bash scripts/lean_check_tree.sh "$m" || exit 1; done \
      < briefs/orders/ch34-b5b.txt )
  ```

  **Base sorry-warning set, 10** (`audits/logs/ch34-b5b-base-sorries.txt`, one entry per declaration). Yours:
  `Diagonalization/EXPCOM` 1, the summit. Record the base list by name first. If anything else has
  landed by your base (a parallel batch, or B5a's continuation), report the difference.
- **Final checks:**
  1. Your owned module: zero errors, zero sorry warnings (or exactly your partial's).
  2. Every other module of the order list: zero errors, and sorry warnings exactly the base's
     minus yours (**10 − 1** for a complete delivery).
  3. Re-run the pre-ship probe `audits/evidence/ch34-wave5/B5bPreShip.lean.txt`: 0 errors.
  4. Re-run `audits/evidence/wave1-statements/S1210StatementsProbe.lean.txt`: 0 errors. Its six
     `rfl` identities hold, and its census still detects an admission (resolution 17, above). Quote
     the census lines.
- **Axiom print** for the summit: within `[propext, Classical.choice, Quot.sound]`, with
  `sorryAx` only through the three named proved-modulo rows. The admission walk (gate guidance)
  lists exactly those three.
- **Lint:** `python3 scripts/campaign_style_lint.py TCSlib/Complexity/Diagonalization`, 0 FAIL.

## Out-of-scope sorries you will see (leave every one untouched)

- `TuringMachine/Build/OracleSim`: FinOracleTM.exists_plain_simulation
- `TuringMachine/CodeSimulator`: exists_polyCanonizer, exists_uniformSimulator
- `Diagonalization/NTimeHierarchy`: exists_timed_universal_NDTM, exists_ndAcceptsWithin_decider, exists_codeNDTM_accepts_linear, ntime_hierarchy, ntime_hierarchy_of_pos, NTIME_linear_ssubset_square


If a proof seems to *need* one of these, that is an escalation, not a license.

## REPORT.md checklist

- [ ] 1/1, or the partial frontier (rule 9); the base hash and the ancestor check.
- [ ] Every new `private` declaration with its role; the flagged Fill appendix; the two flagged
      imports. Confirm explicitly: no public declaration added, and no status text or other
      declaration touched.
- [ ] The diff's hunk headers, showing that every hunk lies in regions 1(a)–(d).
- [ ] Requested shared lemmas: at least the `Nat.bits (2 ^ n)` fact and the `incFixed`
      all-`true` fact as promotion candidates. Escalations, or "none".
- [ ] For the maintainer's header update: the module header text that now reads wrong (69–80,
      including the stale route at 75–77), quoted. Do not edit it.
- [ ] Duplication: both screens, every new pair justified, the pre-disclosed pairs measured
      (including the transcribed ledger lemmas' character counts), "new copies: none" otherwise.
- [ ] File size; the final sweep tail; the re-run pre-ship and S1210 probes (census lines
      quoted); the summit's axiom print and admission walk; the lint line. The diff touches only
      `Diagonalization/EXPCOM.lean`.

## Known pitfalls at this pin (hard-won)

- **Name clash:** the private decider must not be called `exists_EXPCOM_decider`. The S1210 probe
  declares that public name.
- `expCode` is a `Classical.choice`. Use only its structure fields:
  `expCode.simulator_accepts`/`_rejects`/`simDegree`, `expCode.decode`.
- `expCode.simulator` promises nothing on inputs that are not
  `pairEncode (pairEncode (Nat.bits t) α) x`. Never feed it `simIn` of a malformed `z`: route
  every malformed `z` to `w₀`.
- `pairFstD`/`pairSndD` are `((pairDecode z).map …).getD []`. They are `[]` on malformed input, so
  the validity bit, not the projections, carries correctness.
- `Nat.bits` is little-endian: `Nat.bits (2 ^ n) = replicate n false ++ [true]` and
  `Nat.bits 0 = []`. `decide` cannot evaluate `Nat.bits`; the Separation proof's idiom is
  `Nat.bit_val` and `Nat.bits_append_bit`.
- `incFixed` overflows on all-`true` words (`incFixed (replicate n true) = none`, so `getD []` gives
  `[]`). It carries through a leading run, so
  `incFixed (replicate n true ++ [false]) = some (replicate n false ++ [true])`.
- `computesFunInTime_ifEq w₀ u v` compares the **whole** input to `w₀`. `polyTimeComputable_and`
  and `_ite` take the test in the form `fun x => [p x]`; use `convert … using 1; funext x; cases …`
  as `polyTimeComputable_and` does.
- `exists_comp_on_image` measures the second machine's budget at the **original** input length.
  That is why `T₂` is stated in `|z|`, not in `|front z|`.
- `MultiTapeTM.indicator` is classical. Rewrite it with `simp [MultiTapeTM.indicator, h]` against
  the membership iff, as `EXP_subset_POracle_EXPCOM` does.
- The summit's `hshell` uses `Fin.castSucc_ne_last`, `Function.update_of_ne`, `Nat.add_sub_of_le`
  and the `jP` cast `lt_of_lt_of_le jc.castSucc.isLt hk`. Transcribe them; the probe elaborates at
  this tree.
- `omega` with products and powers as atoms (`ring` first to expose them); `nlinarith` is
  rarely needed. The linter needs a literal "Proof sketch" before every `sorry` (partial only).
