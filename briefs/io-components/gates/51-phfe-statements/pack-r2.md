# Gate 51 · io-phfe statements gate · round 2 (statements r2)

Round 2. The auditor is Codex, under the standing ruling of 2026-11-11 (Codex for audits and
reviews). Round 1 (`findings-r1.md`, verdict **HOLD**) audited checkpoint 0, the statements commit of
the io-phfe job. The job has since applied two disclosed statement repairs:
- **statements r1** (PHFE-C0-F01, relayed ahead of the gate by ruling Q-G51-4 (B));
- **statements r2** (every item of `findings-r1.md` that Seyoon relayed).

This round checks statements r2 against round 1's findings. It is a **short reading audit**: the
route Seyoon ruled on 2026-11-19 (decision log `IOComponentsPlan.md`, row "Gate 51 closure route
ruled (Seyoon): Codex round 2").

## Pins

All hashes are full. Take them from this file or `source-head-r2.json`; never retype them.

| Item | Pin |
|---|---|
| **Delivery under audit** | `exchange/pass-shelat-ch5-8` at **`883b51a99a1fbe1e94e5c04f293fc42ec47eec20`** ("fill io-phfe: checkpoint 4 (statements r2)"), folder `inbox/fills/io-phfe/checkpoints/checkpoint-4-r2/` (folder tree `d158eb86ae8f03156888b3a953b1acaa796904d3`, `src/` tree `7ad82c5c61f0dbed944398be29ffd55516d58944`). The commit adds exactly the folder's 138 files and nothing else |
| **Audited source (statements r2)** | the worker's `073d0a5a3ff88d958f94c2ae50a67bc92476f616` ("statements r2: G51-01..11"), tree `d3cbabf22596ab02450f036d8f2cecb42063a533`. It is on no ref. It is delivered as `src/` (88 files, 19,487 lines, 33 `sorry`) and as 37 format-patches. The in-house replay rebuilt it from base + patches with every commit hash equal, and `src/` equals its tree byte for byte (88/88; `verification-r2.md` §1) |
| Statements r1 | worker `a4fe0fd7caaf5fbe5b27f1c2183e539d3b3ba6f8` (tree `ba76832c71a63fc6f3b2339673fef1e2eaa25d0e`), delivered at exchange `503869facd155bb754be8f1281dd77ee7776e3b5`, folder `inbox/fills/io-phfe/checkpoints/checkpoint-3-r1/` (`src/` tree `8f484e61f6d16e660b046802d2df932bbebcc989`, 87 files) |
| Checkpoint 0 (round 1's audited source; the freeze baseline) | worker `70b85f9ba83f27393d98fa5bf88505aea3d22a8d`, delivered at exchange `1e77173a7032b57aa22260787711c6c7a1b7596e`, folder `inbox/fills/io-phfe/` (`src/` tree `5d5d7c61306afcd06ba7d54c0815b7a5c311124b`, 76 files) |
| Base | `iO/phase-a-base` at `5ed465f62e4ae0f93ded1a1ba49e807591b589eb` |
| Round 1's records pin | `8ba55910eafa03c02c39943729c606bb457be60f`: `pack.md`, `intake-r1.md`, `dup-sweep.md`, `source-head.json` |
| Job dispatch records pin | `dbea2807532392781304e004715f3b0190025f5e` (`briefs/io-components/phfe/`) |
| **Records pin of this pack** | the commit on `cryptography/pass-shelat-ch2-4` that files this round's files (`pack-r2.md`, `source-head-r2.json`, `SHA256SUMS-r2`). `dispatch-r2.md` names it; a pack cannot name its own commit. Its parent is the records tip at staging, `c63ee44f47c72a09545235fddccaa765efd64568`. The records this pack cites read the same at both (`source-head-r2.json` `records_sha256_at_staging_tip`) |
| In-house replay of r2 | `verification-r2.md` (SHA-256 `5cd174a84b9c9601b1082a6d0875d10d3839740998f9f58f303ebf15a5c737d2`) and `verification-r2.zip` (SHA-256 **`66f2d29df4b3addf27d07852262cf6cc0f44afd1e75b6a853d4e7cdea379eb2c`**, also in `verification-SHA256SUMS`). The zip has an inner `SHA256SUMS` of 172 rows |
| Round 1's findings | `findings-r1.md`, SHA-256 `5e28af06391d139980fabb9818543516c969d56713f13f6ab03f31d00fafbdae` |
| Lean / Mathlib (reference only; nothing is built) | `leanprover/lean4:v4.25.0`; Mathlib `029db123ddaa7f8fd0d18cea3b1b33bf84dacd1e` |

`FE/` below is `TCSlib/Cryptography/AdvancedEncryption/FunctionalEncryption/`. Line numbers are at
r2 (the delivered `src/`). `REPORT` is the delivered `checkpoint-4-r2/REPORT.md` (SHA-256
`18b69e60ec851a38c59b4ae02e41a7f20af12c786e3bf3a704422b697a3bd501`).

## How this gate runs (standing rules 17 and 18; ruling of 2026-11-18)

- **Cloud, reading only.** Every repository input is reachable from the records branch at the pin
  and from the exchange branch. Fetch blob-filtered; git reads the blobs you open on demand.
- **No Lean replay and no cache.** Gate 52 ruling (1) of 2026-11-18: "the maintainer replays in
  house, auditors do not". Do not run `lean`, `lake` or `lake exe cache get`, and build nothing.
  The in-house replay (`verification-r2`) is the gate's build evidence. You grade it by reading
  its report, logs, probe sources and check outputs (question D).
- **Sources.** The five PDFs are **not** in the repository (pairing ruling Q12 (A)). Seyoon
  attaches the same five files as in round 1, with the same SHA-256 values (the table below).
  - Verify each attached file before reading it.
  - A file that is missing or has a different hash: read nothing from it. Mark every clause that
    needs it **UNVERIFIED-SOURCE**, and audit the rest.
  - Never copy, commit or quote at length a PDF, a page image or an excerpt; cite page and item.
- Python as `python3 -I`; `git`, `sha256sum`, `unzip` and reading tools only.

| File | SHA-256 | What round 2 needs from it |
|---|---|---|
| `gjls21.pdf` | `481f999a0dbea36d6646ccc67b02ea811a50c025d48571dd2a5bdb1c0f386eed` | Def 4.6 (printed p. 22 = PDF p. 26) for R1; Defs 4.2–4.3 (printed pp. 19–20) for G51-01. Printed page = PDF page − 4 |
| `wee20.pdf` | `d4def6b0a9c99c8ff498fc380d41906f63cd3371daa3bd9d3c742312487f112a` | §4.2 (p. 10) and App. B Thm 1 (p. 12) for G51-06 (W6). Printed = PDF |
| `jls26.pdf` | `bb357e8d01cc0932899453f3d877b67b58f33253eabf2564854f8f38721e2f3d` | Thm 5.1 (PDF p. 21): does the consumer need anything of Def 4.6 that R1 omits? |
| `agw20.pdf` | `b74c2ac906cf3f40eb5882abb3921433beebdb9fb020ba09ce8a10035b55d11f` | only to confirm G51-10 (the citations moved off the Pairing facade remain in their FE homes) |
| `iw14.pdf` | `ef6c7c6a0103dfea1d8d9d369e3a7de3a0902fa6138a6bedc4c4df4996e65e77` | as for agw20 |

## What changed since round 1

1. **Statements r1** (worker commit `a4fe0fd7`, patch `0036-statements-r1-PHFE-C0-F01.patch`;
   decision log row "io-phfe checkpoint 3 = statements r1").
   - It adds a fixed-width state to both raw simulators:
     - `stLen : PolyExpr`;
     - `encSt : … → St κ pp → Fin (stLen.eval κ) → Bool`;
     - `encSt_injective`.
     These are in `FE/Defs/Simulator.lean:89–97` and `FE/SemiAdaptive/Simulator.lean:49–58`, and
     `toSim` carries them.
   - The input words `encInputWord`/`keyInputWord` and their readers, `wee20SASim_raw`,
     `SimTargets` and `simTargets_iff` follow.
   - 16 authorized declarations changed.
   - **Round 1 did not see r1** (it audited checkpoint 0). r1 is the state half of G51-03, so it is
     in scope here.
2. **Statements r2** (worker commit `073d0a5a`, patch `0037-statements-r2-G51-01.11.patch`).
   - The diff r1 → r2 is 19 files, +407/−130.
   - There is one new module, `FE/Wee20/Targets/CircuitEfficiency.lean`.
   - REPORT §"Gate 51 round 1: statements r2, all eleven relayed findings" (lines 1620–1788) gives
     the worker's disposition of every item.
   - Its record of the changed declarations is `evidence/changed-headers.tsv`.
3. **The worker ran no Lean for r2.** It read the relay's "the Lean replay is the maintainer's" as
   "do not compile". The maintainer's relay wording caused this; it is disclosed in the decision log
   row "io-phfe checkpoint 4 = statements r2 delivered", and a clarification has since been relayed.
   The in-house replay `verification-r2` is the only elaboration of r2. Do not raise the missing
   worker build as a finding.

Proof work that happened between checkpoint 0 and r2 also sits in `src/`: M1, M2, and 52 proof
helpers. That work is **out of scope** except as question C states.

## Rulings in force

- `briefs/io-components/phfe/rulings.md` (at the pin) and round 1's "Rulings in force"
  (`pack.md` at `8ba55910…`) still apply. Since round 1:
  - **Gate 51 rulings (Seyoon, 2026-11-18)**:
    - G51-02 → **R1**: add `CircuitLinearEfficient G` as the third conjunct of
      `wee20PHFE_gjls21`; keep the TM target `LinearEfficient` as an extra obligation.
    - G51-03 → **R2**.
    - G51-04 → **R3**: κ in `pubGen_eff`'s word, and a κ-prefix on every other sampler map unless
      its word determines κ.
    - Minors G51-01 and G51-05–11: relayed as one `statements r2` commit.
    - **G51-12** is covered by the payload-limit ruling (Q-G51-1 (A)). It is resolved by ruling,
      not by a source change.
  - **Q-G51-3 (A)**: the worker's chat rulings are confirmed and filed in `phfe/rulings.md`
    ("Rulings during the job"): g ∈ G\* in pp with `pubGen_eff`, and κ in its word after R3.
  - **Q-G51-4 (B)**: F01 was relayed ahead as statements r1. The remaining repairs follow in r2.
  - **Q-G51-2 (A)**: continue; a PARTIAL final is allowed.
  - **Q-G52-5 (A)**: the prime schedules (`p`, `hp`) are unified with the sPRG's at landing. Do not
    raise `hp` against r2.
  - **Gate 52 ruling (1)**: no auditor replay.
- **Freeze (design-r3 §6; prompt §6).** After checkpoint 0, statements and their prose change only
  through relayed, disclosed `statements r<k>` commits. Every frozen record that differs from
  checkpoint 0 must be in the authorized set: r1's 16 plus r2's 35, which is 51 names
  (`verification-r2.md` §5).
- Standing rules `briefs/pass-shelat-ch5-8/MAINTAINER-HANDOFF.md` §2: 10, 15, 17 and 18. `policy.md`.

## Scope

**In scope:**
- every declaration of the 51-name authorized set;
- the 8 declarations r2 adds (`CircuitLinearEfficient`, `circuitLinearEfficient_iff`,
  `PHFE.valueEncoding_length_le`, `wee20PHFE_raw_value_bounded`, `wee20Sim_raw_state_bounded`,
  `wee20Sim_raw_value_bounded`, `wee20SASim_raw_state_bounded`, `wee20SASim_raw_value_bounded`);
- the r1 → r2 diff in full;
- the REPORT's r2 section and the fidelity/rule-15 rows that r2 changed;
- `verification-r2`.

**Out of scope:**
- proofs: the 33 `sorry`s are expected; grade a `sorry` only if it sits in a definition or makes a
  statement unprovable;
- Phase B: machines, circuits, samplers, and proofs of the targets;
- the M1/M2 proof bodies and their helpers;
- round 1's settled questions (fidelity of Defs 4.1–4.3, the §9 class, Wee20/AGW20/IW14), unless
  an r1/r2 change touches them;
- the unapplied `patches/PENDING-RESUME.patch` and `RESUME.md`;
- the io-sprg job.

## Questions, in this order

### A. Is each round-1 blocker and major resolved exactly per its replacement spec?

Read `findings-r1.md` "Replacement specifications" R1–R3 beside the r2 source.

**A1. R1 / G51-02:** `CircuitLinearEfficient` (`FE/Wee20/Targets/CircuitEfficiency.lean:55`), its
reader `circuitLinearEfficient_iff` (`:79`), `Targets.circuitLinear` and `targets_iff`
(`FE/Wee20/Targets/Assembly.lean:60–82`), and `wee20PHFE_gjls21`
(`FE/Wee20/PHFE/Headlines.lean:118–131`).
1. **Fidelity to GJLS21 Def 4.6 circuit size** (printed p. 22). Is it a Boolean circuit whose size
   is at most (ℓ+n)·poly(κ), with exactly the source's hard-wired values and inputs?
2. **Quantifier order.**
   - One `q` comes before ℓ, n, d and κ.
   - Then the typed `pp`.
   - Then `pk` with an honest-setup witness (`∃ ρ, (PHFE.setupCore … pp ρ).1 = pk`).
   - Then the guard `0 < ℓ + n`.
   - Then the arity `N` and the circuit `C`, and only after them every `x`, `y` and complete draw
     `ω`.
   Is "every supported pp and honest pk" captured, neither more nor less?
3. **Size convention: "inputs + gates".**
   - `BoolCircuit.MultiDAGCircuit.size = n + gates.length`
     (`TCSlib/Complexity/CircuitComplexity/KarpLiptonSearch.lean:102` at base, citing [AB09,
     Def 6.1]).
   - `IsFaninTwo` (`:105`).
   Does counting inputs make the bound stricter than GJLS21's (never weaker)? Is fan-in two the
   right reading of "Boolean circuit"?
4. **Arity fixed before inputs.** Does `input.length = N` force the complete encoding of x, y and
   the six-scalar draw, so that `getD … false` truncates nothing?
5. **Exact output.** Is the output exactly
   `List.ofFn (PHFE.encCT … (PHFE.encCore … pp pk x y ω))`, with no decoder, no new draw codec and
   no ciphertext other than the honest core's?
6. **The third conjunct.** Is `wee20PHFE_gjls21`'s conclusion `… CorrectExcept 0 ∧ … SimSecure ∧
   CircuitLinearEfficient G`, with `LinearEfficient` retained as a separate `Targets` field?
7. **Docstrings.** Do the docstrings of the new module, the target, the reader, `Targets`,
   `targets_iff`, `wee20PHFE_gjls21` and `LinearEfficient` describe exactly this? The prose of
   `LinearEfficient` changed; check that it no longer claims a Def 4.6 correspondence. Check also
   the REPORT Def 4.6 table (lines 152–163).

**A2. R2 / G51-03**, together with r1's fixed-width state.
1. **The fields.** `state_bounded` and `value_bounded` must be in **both** efficient interfaces, in
   the context `{C : FnClass} (S : FEScheme.Raw C)`:
   - `Simulator`, `FE/Defs/Simulator.lean:237–264`;
   - `SASimulator`, `FE/SemiAdaptive/Simulator.lean:215–242`.
2. **`value_bounded`** should be verbatim R2's text.
3. **`state_bounded`** reads `(List.ofFn (encSt κ pp st)).length ≤ b.eval κ`, because r1 made
   `encSt` a fixed-width `Fin (stLen.eval κ) → Bool` (verification note **N2**). Is this the
   correct adaptation of R2?
4. **r1 itself.** Does r1's fixed width (`stLen` with `encSt_injective`) bound the state over the
   whole polynomial-query run, as R2's last sentence demands? Is it satisfiable for the concrete
   states, that is, an injective encoding into a fixed width?
5. **The targets.**
   - Four `SimTargets` fields (`FE/Wee20/Targets/Sim.lean:100–113`).
   - The reader `simTargets_iff` (`:118`): does it have all ten conjuncts?
   - Pure assembly in `wee20Sim` and `wee20SASim` (`Assembly.lean:113–140`).
6. **The concrete lemmas.**
   - `wee20Sim_raw_state_bounded` and `_value_bounded` (`FE/Wee20/PHFE/CommittedSimulator.lean:57`,
     `:67`).
   - `wee20SASim_raw_state_bounded` and `_value_bounded` (`FE/Wee20/PHFE/Simulator.lean:151`,
     `:161`).
   - `wee20PHFE_raw_value_bounded` (`FE/Wee20/PHFE/Raw.lean:231`), with witness
     `G.wG.add (const 1)`.
   - `PHFE.valueEncoding_length_le` (`FE/Wee20/PHFE/Encodings.lean:575`).
   Are these statements true as stated, with every witness before κ? Proofs are out of scope;
   the replay found them proved and standard-axiom-only.

**A3. R3 / G51-04.**
1. **Every map.** Every `SamplesEfficiently` parameter map must have the form
   `fun κ … => NUPPT.advInput κ (old map)`. There are 20 logical maps and 30 occurrences:
   - `FEScheme`: 4;
   - `Simulator` and `SASimulator`: 3 each;
   - `SchemeTargets` and its reader: 4 + 4;
   - `SimTargets` and its reader: 6 + 6.
   The record is the REPORT table at lines 1662–1668, `evidence/sampler-map-check.tsv`, and
   verification `checks/r3check.txt`/`r3args.txt`.
2. **`pubGen_eff`** must be exactly
   `fun κ (d : GroupDescription G κ) => NUPPT.advInput κ d.val` (`FE/Defs/Efficient.lean:48`).
3. **The other arguments.** Are arguments 2–4 (draw encoding, output encoding, core) unchanged
   from r1 in all 30?
4. **No escape route.** Is there no `DrawSamplable` use, local sampler contract or computed prime
   schedule?
5. **Does the prefix determine κ?** `NUPPT.advInput κ y = pairEncode (List.replicate κ true) y`
   (`TCSlib/Complexity/Randomized/PPT.lean:210` at base). Does it make every word determine κ,
   so that round 1's `pubGen_width_separation` contradiction can no longer arise?

### B. The minors

For each, say **resolved**, **not resolved** or **resolved by ruling**, with evidence.
- **G51-01**: `SimSecureWith`'s prose (`FE/Simulation/Security.lean:46–51`) and the REPORT
  Def 4.2/4.3 rows (lines 120–151) state the familywise reading. Check against GJLS21
  pp. 19–20. Is the formal body unchanged?
- **G51-05**: `MddhPreTargets`, `mddhPreTargets_iff` and `mddhRealizable_of_preTarget`
  (`FE/Wee20/Targets/MatrixDH.lean:46–72`): no `_D` binder, and the witness order is described.
- **G51-06**: REPORT W6 row (line 307). Check it against Wee20 §4.2 p. 10 and App. B Thm 1 p. 12,
  and check 1 − (1−½)(1−¼)(1−⅛) = 43/64 = 344/512.
- **G51-07 and G51-08**: promotion requests recorded in REPORT, with no source change. Check that
  the reuse of `BB1Machine.order_le_two_pow` and the GT laws stands as disclosed.
- **G51-09**: `PrivateKeyScheme.encodeList` replaces every `foldr pairEncode []`.
  - Expect 0 remaining and 29 `encodeList` occurrences, in `WireDraws`, `Simulation/Games`,
    `PHFE/Encodings`, `Defs/Simulator` and `PHFE/Simulator`.
  - `encodeList` is at `TCSlib/Cryptography/Encryption/PrivateKey/EnsembleSecurity.lean:103` at
    base. Is it byte-identical in layout?
  - Is the new import of `EnsembleSecurity` acceptable?
- **G51-10**: `TCSlib/Cryptography/Pairing.lean` no longer cites AGW20/IW14.
- **G51-11**: REPORT names `1e77173a…` as the delivery and freeze start (lines 13–19, 75–80,
  732 and 966). Is earlier prepublication wording marked historical?
- **G51-12**: resolved by the payload ruling. This checkpoint has 0.78 MB and 3,378 lines outside
  `src/` and `patches/` (REPORT, end).

### C. Nothing else changed (the freeze)

1. **The authorized set.** Against checkpoint 0, are the frozen records whose header or opening
   prose changed **exactly** the 51 authorized names, each traced to r1 or to a relayed r2 item?
   Read:
   - `verification-r2.md` §5;
   - zip `checks/freeze-c0-r2.tsv`, `checks/auth51.txt`, `checks/changed-c0-r2.txt`,
     `checks/added60.txt` and `checks/added8.txt`;
   - the worker's `evidence/changed-headers.tsv` and `freeze-verdict.json`.
2. **Read r1 → r2 in full.** The diff is
   `git diff 503869fa…:…/checkpoint-3-r1/src 883b51a9…:…/checkpoint-4-r2/src`, 19 files,
   +407/−130. Is every hunk one of the relayed items, or a proof or sketch change that the items
   entail? Three proof or sketch changes are reported: the bodies of `quadraticSimState_injective`
   and `_length`, and the sketch of `mddhRealizable_of_preTarget`.
3. **Read c0 → r1.** Use patch `0036`, or the tree diff `1e77173a…:inbox/fills/io-phfe/src` →
   `503869fa…:…/checkpoint-3-r1/src`. Restrict it to declaration headers and prose.
4. **Reconcile the counts.** The REPORT's decls2 counts (60 ADDED / 21 CHANGED vs M0; 8 / 17 vs
   r1) should agree with the stronger 51-record freeze; REPORT explains that decls2 omits record
   fields and definition bodies.
5. **The rest of the source.** Spot-check that nothing outside the authorized set changed a
   statement: for example, a definition body in the 56-file c0 → r2 diff (+5,948/−304, mostly M1/M2
   proofs).

### D. Grade the in-house verification (`verification-r2.md` and `.zip`)

1. **Read the evidence.**
   - Read the report and the zip: `PROVENANCE.txt`, `COMMANDS.txt`, `source/`, `checks/`,
     `probes/Heads.lean`, `probes/Census2.lean`, `logs/build/results.jsonl` and
     `logs/probes/final/`.
   - Verify the zip's SHA-256 and its inner `SHA256SUMS`.
2. **Grade each claim:**
   - reconstruction (37/37 hashes, 88/88 blobs);
   - build (89/89 rc 0, 0 errors);
   - 33 `sorry` warnings, per file;
   - axioms (78 targets: 65 standard, 13 `sorryAx`) and census (2,347 / 2,313 / 34 / 0; no
     definition or target through `sorryAx`);
   - each repair verdict (§4);
   - the freeze (§5).
3. **Do the probes test what the report says they test?** For example:
   - do the `example`s restate R2's field forms and R3's `pubGen_eff`?
   - do the `type_of%` probes discharge the four `SimTargets` bounds?
   - does `.2.2` of `wee20PHFE_gjls21` have type `CircuitLinearEfficient G`?
4. **Notes N1–N3.** Grade each, and regrade if warranted:
   - **N1:** the unused `hHonest` binder, 2 warnings;
   - **N2:** `state_bounded` is automatic after r1;
   - **N3:** the four bounds are `SimTargets` fields although proved lemmas discharge them.
5. **The disclosed slips.** Two failed probe attempts, a disk incident, and one extra Mathlib
   olean (`Data.Matrix.ColumnRowPartitioned`) compiled into the replay tree only. Do any of them
   affect what the evidence shows? Necessary evidence that does not bind to `073d0a5a` is a
   **major**.

### E. New issues introduced by the repairs

1. **Is `CircuitLinearEfficient` satisfiable in principle?** If it is false for every reasonable
   `G`, the GJLS21 headline is vacuous.
   - Is `Wire.quadraticEncDraw pp ω` (`FE/Wee20/WireDraws.lean:91`;
     `Encoding.Modular.encodeVector` at width `G.wG.eval κ`, `Encoding/Modular.lean:51` at base;
     `encodeList` framing) the same length for every `ω`? If not, no `N` exists.
   - Can a fan-in-two `MultiDAGCircuit` hard-wire constants? Empty-argument `and`/`or` gates
     (`DAGCircuit.lean:104–135` at base) would do it.
   - Does the bound fit with ℓ·w + n·w input bits plus an O(w) draw, under the guard
     `0 < ℓ + n`?
   - Is the target plausible for a `G` with efficient operations (the separate contract
     `BilinearGen.Ops`, `TCSlib/Cryptography/Pairing/Operations.lean:68`)?
   - Is it right to quantify over every `d` with a `d`-free bound (`phfeClass` `pubLen = ℓ·w`,
     `privLen = n·w`, `FE/Classes.lean:371–372`)?
   - Does a target stated at constant dimensions `PolyExpr.const ℓ` speak about the assembled
     scheme `P` at `ℓ.eval κ`? If it needs a stated link or reader, say so.
2. **Vacuity of the new fields and targets.**
   - `state_bounded` is automatic (N2). Is keeping it harmless?
   - `value_bounded` quantifies over **every** `v : C.Out κ (S.cprm κ pp)`. Does it constrain every
     class value, including values not reachable as an output of `C.eval`? Which classes `C` then
     admit no `Simulator` at all?
   - R2 calls this a deliberate strengthening. Is it acceptable for the consumer (the
     `phfeClass` only)?
   - Is any variable-length simulator input word left unbounded? Consider `Omega.encode` with its
     q functions and values, and the key index `Candidates.natToList (Nat.size count)`.
3. **The R3 class beyond samplers.** Do the uniform deterministic fields omit κ from their input
   words in the way G51-04 describes? These are `FEScheme.dec_eff`, `SchemeTargets.dec_eff`,
   `LinearEfficient`, `PGTargets` and `MddhPreTargets`. R3 covered samplers only.
4. **N3 and the "Phase B obligation" wording.** Are the four `SimTargets` bounds, which are proved
   already, described accurately? Is a headline whose third conjunct is returned from the
   hypothesis `hT.circuitLinear` presented honestly?
5. **The reused circuit model.** `MultiDAGCircuit` is imported from `KarpLiptonSearch` (an
   Arora–Barak course file).
   - Is there a more canonical multi-output circuit API in TCSlib at base?
   - Is the cross-area import acceptable? (Compare G51-07.)
6. **The REPORT's tables after r2.** Does the rule-15 table ("Efficiency is carried by
   interfaces", REPORT lines 430–444) describe r2? Staging noticed rows that read as
   pre-r2. Confirm or refute each, and grade:
   - `SimTargets` is given "six literal propositions" (r2 has ten);
   - the `Targets / Assembly` row lists five fields, without `circuitLinear`;
   - `MddhPreTargets` still shows a `D` binder (G51-05 dropped it);
   - `LinearEfficient` is called "stronger than source circuit/support formulation". G51-02
     found no such bridge, and REPORT line 161 now says no implication is asserted.
7. Anything else the repairs introduced: docstrings, tags (GJLS21 Def 4.6, printed p. 22),
   `policy.md` form, readers (Rule 10 at statement level), and new `@[simp]` or global attributes.

## Evidence binding

| Evidence | Bound to | What it shows | Reaches `073d0a5a` by |
|---|---|---|---|
| Delivery folder `checkpoint-4-r2/` (exchange `883b51a9`) | worker `073d0a5a` | `src/`, 37 patches with `COMMITS.tsv`, REPORT, compact evidence (freeze adjudication, decls2, lint, sampler maps) | `SHA256SUMS` 137/137 (`source-head-r2.json`); `src/` = the replayed tree |
| `verification-r2.md`/`.zip` (records) | the rebuilt `073d0a5a` (tree `d3cbabf2…`), private scratch repository | reconstruction, build, `sorry` count, axioms and census, repairs, freeze | all 37 rebuilt commit hashes equal `COMMITS.tsv`; 88/88 `src/` blobs (`source/replay-am.txt`, `src-blobs.tsv`) |
| `findings-r1.md` (records) | checkpoint 0 `70b85f9b` | the specs R1–R3 and the minors | — |
| This pack and `source-head-r2.json` | the delivery commit and the records tip at staging | pins; file hashes, lines, width and `sorry` per file; r1/c0 presence; `SHA256SUMS` check | git objects only |

`073d0a5a`, `a4fe0fd7` and `70b85f9b` are on no ref. Bind through the delivered `src/` trees and
the replay's records; do not try to fetch them.

## Known dispositions (not findings)

- Verification notes N1–N3. **Grade them** (question D).
- **The worker ran no Lean for r2.** The cause is the maintainer's relay wording. It is disclosed
  and the worker has been corrected. The in-house replay is the build evidence.
- **Promotion requests G51-07/08** carry no source change by design. They go on the landing ledger.
- **G51-12** is resolved by the payload ruling. This checkpoint is within the limit.
- **REPORT points to local raw evidence** (a local path and a tar SHA-256). That is allowed by the
  payload ruling; the files are supplied only on a gate's request. This gate does not request them.
- **The unapplied `PENDING-RESUME.patch` and `RESUME.md`** are proof-continuation material. They
  are not part of `src/` and are out of scope.
- **The replay environment** compiled one extra Mathlib olean (`Data.Matrix.ColumnRowPartitioned`).
  It is a pinned Mathlib source file, compiled into the replay tree only. It is an environment fact,
  not a delivery defect.
- **The prime-schedule unification** waits for landing (Q-G52-5 (A)).

## Severities (as round 1)

- **blocker:** a later phase (the proofs, Phase B, the consumer) would build on a wrong statement.
  That includes:
  - a false, vacuous or unusable statement or definition;
  - a definition too weak for its consumer;
  - a missing or wrong efficiency field;
  - a repair that does not achieve its spec's purpose;
  - a scope violation.
- **major:** fixable but materially misleading. That includes:
  - a repair that deviates from its relayed spec without disclosure;
  - a frozen statement changed outside the authorized set (a blocker if it is also wrong);
  - a mis-stated source correspondence, or a fabricated tag or locator;
  - necessary evidence that does not bind to `073d0a5a`.
- **minor:** documentation or API defects, such as an inaccurate docstring, disclosure, sketch or
  citation, or a missing reader.
- **note:** anything else.

## Findings delivery

Return **`findings-r2.md`** as Markdown in the Codex chat. If you have evidence files (scripts,
search logs), return a ZIP with `findings-r2.md` at its root. Write nothing to the repository, push
nothing, open no PR. The maintainer files the findings verbatim, with their SHA-256, at
`briefs/io-components/gates/51-phfe-statements/findings-r2.md`.

| # | Severity | File · declaration | Claim | Evidence (source page / Lean line / evidence file) | Proposed fix |
|---|---|---|---|---|---|

- Number new findings **G51-201, G51-202, …**, in the order A–E. For every blocker or major that
  changes a statement, give the replacement text, so that it can be relayed as one
  `statements r3` commit.
- Grade round 1's findings in a separate table, G51-01 to G51-12: **resolved**, **not resolved**,
  **partly resolved** or **resolved by ruling**, each with its evidence.
- Grade `verification-r2` in another table: each claim and N1–N3, as **agree** or
  **regrade/reject** with the reason.
- Report:
  - the commits you read;
  - the PDF hashes you verified, or which files were not attached;
  - every clause marked UNVERIFIED-SOURCE;
  - the commands you ran;
  - the counts by severity.
- Give a verdict for **statements r2**:
  - **CLEAR:** zero blockers and zero majors.
  - **HOLD:** otherwise.

## Files of this round

- **`pack-r2.md`** (this file) and **`dispatch-r2.md`**. The dispatch is the Codex prompt; it
  postdates the pin and is not in `SHA256SUMS-r2`.
- **`source-head-r2.json`** holds:
  - the pins, the delivery commit, the folder and `src/` trees;
  - the source head and tree, the base, and round 1's pin;
  - the `verification-r2` hashes and the five PDF hashes;
  - the delivered `SHA256SUMS` check (137 rows, 0 mismatches, no unlisted file, no path outside
    the folder);
  - the SHA-256 of every non-`src/` delivered file;
  - for each of the 88 `src/` files: SHA-256, lines, maximum width, `sorry` count, and presence at
    checkpoint 0 and r1, with an r1 → r2 changed flag;
  - the SHA-256 of every record this pack cites at the records tip at staging.
- **`SHA256SUMS-r2`** covers `pack-r2.md` and `source-head-r2.json`.
- Round 1's files are unchanged. `verification-SHA256SUMS` covers both verification zips.
