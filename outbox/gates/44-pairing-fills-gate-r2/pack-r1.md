# Gate 44 · Pairing fills: T1 `bdhAssumption_of_dbdhAssumption` (#340) and T4 `exists_bb1_distinguisher` (#346) · round 1

Round 1. The auditor is Codex, under the standing ruling of 2026-11-11 (Codex for audits and reviews). This gate audits two
fill PRs of the pairing campaign together, because they merge together and their merged tree is the one the maintainer
replayed.

- **PR #340** (`pair-bdh`, T1): draft [PR #340](https://github.com/Shilun-Allan-Li/tcslib/pull/340) at
  `916afc25c21f5e52b4b01958186ad55d2f615fd1` (branch `fill/pairings-pair-bdh`). One SSH-signed commit on #331's head
  `9e7a96481785d6cac4dea3b2e990c49ac278b060`, which is the merge base with the records branch. It changes
  `Pairing/Assumptions.lean` only (+227/−8). Base `cryptography/pass-shelat-ch2-4` (retargeted after #331 merged).
- **PR #346** (`bb1-machine`, T4): draft [PR #346](https://github.com/Shilun-Allan-Li/tcslib/pull/346) at
  `89a18a8225be1b76166af12a15179da291747783` (branch `land/pairings-bb1-machine`). Seven SSH-signed commits on the merge
  base `7291f6b237fec75add1549c0992c174442180488`: three in-house checkpoints, the external worker's three commits
  (re-signed cherry-picks, authors kept), and the landing edit LE-bb1m. It changes 8 files (+2741/−17).
- **Records pin:** `8f888790b7e40f9e0529967e29a05a72c5ee8ba3`. It descends from the records tip at which the replay was staged,
  `1d1a9bb3aa4d5d28c7c9a2343cb322a39da07821` ("Records: #346 (T4) phase 2 accept; replay on snapshot #4"), which holds both
  maintainer reviews. Every record this pack cites is read at `1d1a9bb3` unless it says otherwise; this pack's own files are
  filed after it. During staging three records-only commits landed (`fc0aa4e1`, `fa8a0529`,
  `8f888790b7e40f9e0529967e29a05a72c5ee8ba3`: the bb1-sim T2/T3 fill staged and dispatched); they change no code path, and
  `8f888790` × #340 × #346 (tree `6ef355bb…`) has T44's code exactly.
- **Lean base.** The records tip's Lean equals `463f224414ab7615e54104be353bfcda9dfceda7` (the merge of #352), which is
  **olean snapshot #4** (map SHA-256 `6607620d725049c90b34a51a2ab891f1520fd0f576aaf3f9d51301222cee41e7`, 1453 files). The diff
  `463f2244..1d1a9bb3` over `TCSlib`, `TCSlib.lean`, `audits`, `scripts`, the lake files and `lean-toolchain` is empty
  (`checks/series.txt`).
- **The merged tree T44** = tip × #340 × #346 = `33681cb8ed893a897ca2028d5ada70ca29237978`. All three merge orders are
  clean and give this tree. Its Lean equals `c7be1301f59ec0f208f2645544abac8ac5cc6626`, the three-way tree that #346's
  phase 2 computed from `463f2244` (0 code paths differ). Against the tip it changes exactly the 9 files of the two PRs,
  each blob-equal to its PR head, and the two PRs share no path (`checks/mergetrees.txt`).
- **Scope:** a **proof audit** of two admitted, frozen statements, the reader insertions that one of them was granted, and
  the joint integration evidence:

  | Target | File · line at T44 | Source |
  |---|---|---|
  | **T1** `BilinearGen.bdhAssumption_of_dbdhAssumption` | `Pairing/Assumptions.lean:426` | folklore (not stated in [BB04] or [Jou00]; ruling Q10); the problems of [BB04, §3.1] |
  | **T4** `exists_bb1_distinguisher` | `AdvancedEncryption/IdentityBased/BonehBoyenMachine.lean:104` | [BB04, §4.2, the algorithm `B` in the proof of Theorem 4.1], depth 1 |
  | consumer `bb1_sidSecure` (proved at the base from T2–T4, unchanged) | `IdentityBased/BonehBoyenSecurity.lean:124` | [BB04, Theorem 4.1] at depth 1 |

  T1–T4 passed Gate 40 (closed on round 2, `e008f3a4…`), which judged T1–T4 true and T2–T4 sufficient for `bb1_sidSecure`.
  T2 `bb1_sim_real` and T3 `bb1_sim_random` (`BonehBoyenSecurity.lean:89`, `:104`) remain admitted; they are the bb1-sim
  fill's, not this gate's.

Lean paths below are under `TCSlib/Cryptography/` unless they start with `TCSlib/`; `IB/` is
`AdvancedEncryption/IdentityBased/` and `BBM/` is `IB/BonehBoyenMachine/`.

## What changed

Lines are tip → T44 (`source-head-r1.json`; every line is at most 100 characters; no tab or trailing space).

| File | PR | Status | Lines |
|---|---|---|---:|
| `Pairing/Assumptions.lean` | #340 | frozen; T1's body and sketch, 4 imports, 10 private helpers | 221 → 440 |
| `IB/Defs.lean` | #346 | frozen; 3 approved readers (pure insertion) | 433 → 476 |
| `IB/BonehBoyen.lean` | #346 | frozen; 4 approved readers (pure insertion) | 677 → 714 |
| `IB/BonehBoyenMachine.lean` | #346 | frozen; 5 helper imports, a `## Contents` section, T4's body and sketch | 85 → 137 |
| `BBM/Draws.lean` | #346 | new | 451 |
| `BBM/Words.lean` | #346 | new | 632 |
| `BBM/Handler.lean` | #346 | new | 899 |
| `BBM/Reduction.lean` | #346 | new | 243 |
| `BBM/Oracles.lean` | #346 | new | 367 |

No other file changes: `IB/BonehBoyenSecurity.lean` (T2, T3, `bb1_sidSecure`), `Pairing/Group.lean`,
`Pairing/Operations.lean`, `KeyExchange/Joux.lean`, the facades and the root are blob-equal at the tip and at T44
(`checks/headers.txt`).

### #340: T1 (maintainer, in-house, under Seyoon's overnight authorization of 2026-11-16)

**The route** (Gate 40's): `D` re-pairs the first five components of its input into the BDH string, runs the solver `A` with
`A`'s own coins and advice, and outputs `[true]` iff the answer equals the last component.
- `D := NUPPT.ofPolyTime` of the raw layout function (`exists_bdhDistinguisher`); the equality test is
  `polyTimeComputable_pairEq`; the projections are `tupleBdh`/`tupleTgt` (compositions of `pairFstD`/`pairSndD`).
- On `P_BDH`, acceptance equals `A`'s success: coins moved by `coinsCongr` and `expect_sample_equiv`, the unused sample of
  `T` by `expect_const`.
- On `R_BDH`, the samples of `T` and of the coins are exchanged (`expect_sample_comm`); for fixed coins the answer is one
  string, which encodes a uniform `T` with probability at most `1/p` by injectivity of `encT` (`prob_eq_encT_le`).
- `1/p ≤ 2^{-κ} + [p < 2^κ]` pointwise, and the bad generator coins cost at most `δ(κ)` (`orderAtLeastExcept_iff`,
  `prob_sample_eq_uprob`), giving `Pr[A wins] ≤ dbdhAdv D κ + 2^{-κ} + δ(κ)` (`accept_bdhGame_le`). No group operation,
  decoding or `Ops`.

Four imports were added: `Complexity.Randomized.Closure`, `Complexity.Randomized.Repetition`,
`Cryptography.Games.Bridges.Experiments` and `Cryptography.OneWayFunctions.Basic`. The ten new declarations are all
`private`, each with a formula docstring; the two with proofs of 15 lines or more carry a `**Proof sketch.**`. The
in-house REPORT's `## Overlap and reuse` has 7 disclosures (§ 5).

### #346: T4 (in-house checkpoints, then an external Claude worker, then the maintainer's landing edit)

**The route** (Gate 40's, with G40-03's sampler): `D_b` is the machine that the handler theorem
`Games.exists_handlerMachine` gives for `BB1Machine.handler … b q`, run on the adversary `A'` from
`Games.exists_toCompOn_of_toComp`.
- The handler is [BB04]'s algorithm `B` on encodings: group operations by `O : G.Ops`, residue arithmetic modulo
  `p = O.orderStr d` by `H : ArithmeticFP` (negation and differences as `(p − x) mod p`, `(x + (p − y)) mod p`, the inverse
  by `xgcdStr` with `0 ↦ 0`).
- With `n = κ + wG(κ) + 1`, the `j`-th exponent is `(sampleBelowL p (Nat.size p) n n w).getD 0` on the `j`-th block of `n²`
  coins (`BBM/Draws.lean`).
- `σ(κ) = (q(κ) + 1) · 2^{−κ}`. Four `ProbComp.abs_expect_sub_le` steps reduce to one tuple
  (`BB1Machine.abs_expect_bb1Sim_sub_distinguisherL_le`, the only new public lemma of `Oracles`); there, call by call,
  `bb1SimImpl` has the law of `drawStep` with fresh uniform exponents (the per-call identity through the **seven
  readers**), the tape lemma `expect_handlerMachine` turns `D_b`'s output into `A`'s guess, and `statClose_sampleBelowL`
  puts each draw within `(1/2)^n` of uniform since `0 < p ≤ 2^{wG} < 2^n`; the total is `q · (1/2)^n ≤ σ(κ)`.

**The seven readers** (Seyoon's ruling of 2026-11-16, minimal form, landing in this PR as pure insertions with `rfl` or
one-line proofs and formula docstrings; the 13-reader variant was not approved):
- `IB/Defs.lean`: `IBEScheme.oracleImpl_zero_onSpec`, `oracleImpl_one_onSpec`, `oracleImpl_two_onSpec` (each
  `(OracleComp.bind_pure _).symm`), inserted after base line 387;
- `IB/BonehBoyen.lean`: `ofFn_bb1Scheme_encPP`, `ofFn_bb1Scheme_encSK`, `bb1Scheme_msgSpace_iff` (after base line 387) and
  `ofFn_bb1SimCt` (after base line 551).

The approved text is `fills/bb1-machine/inhouse-r1/scope-request/BB1ReadersMin.lean.txt` (SHA-256 `8644e722…`, lines 27–68,
74–97, 99–109).

**LE-bb1m** (`89a18a82`, `Oracles.lean` only, +2/−8): removes an unused `have hpp` (BM-F01) and puts the docstring
arguments of `abs_expect_bb1Sim_sub_distinguisherL_le` in Lean order (BM-F02). No statement changes.

**Commits** (`checks/series.txt`; all seven SSH-signed, ed25519, verified with the public key in each signature, the same key
that signs the records tip; a one-byte tamper control fails):

| Commit | What | Files |
|---|---|---|
| `b4d9babc` | checkpoint 1 (in-house): drawn exponents; handler, Init round | `Draws`, `Handler` |
| `b9caa4ad` | checkpoint 2 (in-house): handler rounds and run; reduction lemmas | `Handler`, `Reduction` |
| `8abfa466` | checkpoint 3 (in-house): the handler's string layer split off; facade imports | `BonehBoyenMachine.lean` (+15/−0), `Draws`, `Handler`, `Words` |
| `61720b0e` | worker: the approved readers | `Defs` (+43), `BonehBoyen` (+37) |
| `43887330` | worker: the helper `Oracles` | `Oracles` (new) |
| `0da95f96` | worker: T4's body and sketch, the `Oracles` import, one `## Contents` bullet | `BonehBoyenMachine.lean` (+54/−17) |
| `89a18a82` | LE-bb1m (maintainer) | `Oracles` (+2/−8) |

The worker's three commits were delivered unsigned (exchange `f14ac810…`, `inbox/fills/bb1-machine/`); `git am` at the issue
base `7c0a55e0239c14786612d0cd4462e64238543ca1` reproduced their hashes (`633dcf99`, `b9a242ea`, `c90273fa`), and the landing
cherry-picks are `git range-diff` 6/6 identical (phase 2).

## Rulings and records in force

1. **Gate 40 is closed** (round 2 CLEAR, `findings/gate40-pairings-statements-r2-findings.md`, `e008f3a4…`). Its round-1
   findings (`ceb63bfc…`) judged T1–T4 true and gave the fill routes this gate checks against (§ *Truth and sufficiency
   of T1–T4*), including G40-03's sampler parameters for T4.
2. **Ruling G40-01** (injectivity fields `encPP_inj`, `encSK_inj`, `encCT_inj` on reachable objects; efficiency deferred,
   Q5). T4's per-call identity reads the scheme's encodings only through the four `BonehBoyen` readers.
3. **Ruling Q10** (pairing plan): T1 is attributed as folklore, "not stated in [BB04] or [Jou00]" (LE-gate40, G40-04).
4. **The T4 scope ruling** (Seyoon, 2026-11-16, decision-log row 413): the seven readers, minimal form, in the T4 PR, as with
   sc-yao's SY-3 readers; #331 unchanged; **Gate 44 checks that they are insertions only.**
5. **Rule 10 rulings:** `PolyExpr.eval` is notation (seal **A** canonical; seal B run and attributed); a `CoeFun`/`Coe`
   instance whose body is a projection is notation (**coe-A canonical**, the strict variant run and attributed); reducible
   abbreviations are notation; inside a file its own definitions may be read directly (`rfl`, `show`); each helper module
   is foreign to the others.
6. **The overnight authorization** (2026-11-16): the maintainer filled T1 in-house, to be audited by Codex.
7. **BS-F08** (decision-log row 427): Claude cloud sessions on this account share one commit-signing key, so a signature
   attests a Claude session on the account, not the maintainer; provenance rests on the pinned hashes.
8. **Not in scope:** the bb1-sim fill (T2/T3), its readers and its `Games/Relational.lean`; #351 and #352 (DW-11's combined
   gate).

## What is frozen

- **T1's statement**: its header (keyword to `:= by`) and its statement prose and `**Source:**` paragraph before
  `**Proof sketch.**`; every other declaration of `Pairing/Assumptions.lean` with its docstring, the module docstring, and
  every `variable`, `open`, `section`, option and comment. Permitted: the four imports after the base's last import, the
  two inserted blocks of private helpers, T1's sketch paragraph and body.
- **T4's statement**: header and statement prose; every other part of `IB/BonehBoyenMachine.lean`. Permitted: the
  checkpoint's four helper imports and `## Contents` section (pure insertions, `9e7a9648 → 7c0a55e0`, +15/−0), and then
  exactly the brief's regions (one `Oracles` import, one `## Contents` bullet, T4's sketch paragraph and body).
- **`IB/Defs.lean` and `IB/BonehBoyen.lean`** apart from the seven readers at their positions; **every other frozen file**
  (`BonehBoyenSecurity`, `Pairing/*` apart from T1's file, `KeyExchange/*`, `Games/*`, the facades).

## Questions for the audit

**1. True and sufficient targets, and correct proofs**
- **T1.** Does the body establish the frozen statement for every NUPPT solver `A`, under the stated order hypothesis
  `∃ δ, Negligible δ ∧ G.OrderAtLeastExcept (2^·) δ` and `h : G.DBDHAssumption`, with nothing else assumed? In particular:
  - Is `D` a non-uniform PPT in the library's sense, with `A`'s coins and advice (`exists_bdhDistinguisher`,
    `NUPPT.ofPolyTime`, `coinsCongr`), and polynomial-time on every input string, malformed ones included?
  - On `P_BDH`, is acceptance exactly `A`'s success? Is the coin move `coinsCongr`/`expect_sample_equiv` sound, and is the
    sample of `T` really unused?
  - On `R_BDH`, is the bound `Pr ≤ E_r[1/p]` right: the exchange of the two samples, injectivity of `encT` on the group the
    description `d` names, and `uprob_eq_one_div_card` for the target group's cardinality?
  - Is `1/p ≤ 2^{-κ} + [p < 2^κ]` correct for every `p`, `p = 0` or a degenerate group included, and is the bad-coin charge
    exactly `δ(κ)`? Is the final negligibility argument (`dbdhAssumption_iff`, `negligible_two_pow_neg`, `mono`) sound?
  - Does `accept_bdhGame_le` hold as stated for every `κ` (no "eventually" hidden in the hypotheses)?
- **T4.** Does the body establish the frozen statement for every `H`, `O`, `A`, `q`, both `b`, both tuple distributions and
  every `κ`, with `σ` chosen before `b`, `real`, `κ`?
  - Is `D_b` the [BB04] algorithm `B` on encodings, defined on every input string, malformed tuples and adversary answers
    included? Are the residue arithmetic modulo `p` (truncated subtraction avoided), the inverse with `0 ↦ 0`, and the
    membership tests sound?
  - Is G40-03's sampler used exactly (`n = κ + wG(κ) + 1`, `sampleBelowL p (Nat.size p) n n`, `getD 0`), and does
    `statClose_sampleBelowL`'s premise `p < 2^n` follow from `encG` injective (`0 < p ≤ 2^{wG}`) for **every** generator
    output, not only good ones?
  - Is the per-call identity `bb1SimImpl = castImpl (freshImpl drawStep)` exact for all three oracles, including refused
    and repeated key queries and invalid challenges? Is the tape argument (fresh exponents ≡ a tape drawn in advance;
    `expect_handlerMachine`; `abs_expect_runAccept_sub_le`) sound, with `q(κ)` exponents enough for every run?
  - Is `q · (1/2)^n ≤ (q + 1) · 2^{−κ}` right (`κ ≤ n`), and is `σ` negligible by the cited lemma?
- **Sufficiency.** At T44, `bb1_sidSecure` reaches `sorryAx` only through T2 and T3 (§ 8). Do T1 and T4 as proved leave the
  Gate 40 chain intact (T2–T4 suffice for `bb1_sidSecure`; T1 is not used by it)? Does anything in the T4 proof weaken
  what T2 must later supply?
- **Edge cases:** `κ = 0`; `q(κ) = 0`; `p = 1` or a generator output whose description is not a valid group; identity
  strings that collide modulo `p`; an adversary that never queries or never issues a valid challenge; `A` with zero coins
  or empty advice.

**2. Frozen-statement integrity** (`checks/headers.txt`, `checks/frozen-assumptions.txt`, `checks/frozen-t4.txt`,
`checks/readers.txt`, `replay/statements/touched-after.tsv`)
- **T1:** pair-bdh's `frozen_check.py`, rerun here from git objects (tip → T44): reverting exactly the four imports, the two
  private blocks, T1's sketch paragraph and body gives the tip's file byte for byte; the 10 inserted declarations are all
  `private`; T1's body has no `sorry`. Its six mutation controls (T1 header, another docstring, a public helper, T1 prose,
  a fifth import, another body) each FAIL, and the unmutated head PASSes. Do the permitted regions hold?
- **T4:** the review's `frozen_t4.py`, rerun (issue base `7c0a55e0` → `89a18a82`, blob-equal to T44): everything outside
  the four regions is byte-identical, and its ten controls each FAIL. The checkpoint's change `9e7a9648 → 7c0a55e0` is
  +15/−0 (the four helper imports and the `## Contents` section). T4's header and statement prose are byte-identical at
  `9e7a9648`, `7c0a55e0`, the tip, `89a18a82` and T44, and so are T1's at `9e7a9648`, the tip, `916afc25` and T44, and those
  of T2, T3 and `bb1_sidSecure` at the tip, `89a18a82` and T44. Do these checks show the statements unchanged?
- **Declarations** (`checks/decls2-tip-vs-T44.tsv`; `decls2.py` over the 9 files): 174 public declarations ADDED, 0
  CHANGED, 0 REMOVED. The declaration-level text comparison (`touched-after.tsv`) gives, over the 9 files, 99 UNCHANGED,
  2 CHANGED (exactly T1 and T4: docstring sketch and body), 17 ADDED to existing files (the seven readers and #340's ten
  private helpers) and 246 in the new files. Is any other declaration of a frozen file touched?

**3. The seven readers** (`checks/readers.txt`)
- The review's `readers_check.py`, rerun with base = the tip (whose `Defs`/`BonehBoyen` blobs equal `9e7a9648`'s and
  `7c0a55e0`'s): inserting the approved text (`8644e722…`) after `Defs:387`, `BonehBoyen:387` and `BonehBoyen:551`, each
  block after one blank line, gives the T44 files byte for byte (`4e220ead…`, `da875140…`); removing them restores the base
  (`9af4b773…`, `22caae4f…`); the diffs are +43/−0 and +37/−0. Its nine mutation controls each FAIL.
- Are these exactly the approved readers, verbatim, with `rfl`/one-line proofs and formula docstrings, no attribute? Is
  each needed under the seal (the reader control rows of #346's phase 2, below)? The `onSpec` statements contain
  `cast (show … from rfl)`: is that a definitional read of the file's own `sidSpec`, permitted inside `Defs.lean`, and not a
  hidden unfold for consumers?

**4. The landing edit LE-bb1m** (`89a18a82`): is it proof-only (an unused `have` removed) and doc-only (argument order), with
no statement change? Phase 2 found the request sets unchanged by it.

**5. Duplication** (recent gates graded undisclosed re-proofs of public lemmas as **majors**)
- **#340's 7 disclosures** (`fills/pair-bdh/inhouse-r1/REPORT.md` § *Overlap and reuse*): the machine as
  `NUPPT.ofPolyTime` of a raw function (the `NUPPT.wrap` alternative); `polyTimeComputable_pairEq` reused; the five-fold
  projection written out (there is `polyTimeComputable_iterate_pairFstD` but no iterated-`pairSndD` lemma);
  `prob_eq_encT_le` assembled from published lemmas (near alternative `ProbComp.expect_sample_mem_le`); the verdict identity
  `decide ([decide P] = [true]) = decide P` inline, although the public `decide_singleton_eq_true`
  (`Encryption/PublicKey/TrapdoorPredictor.lean`) states it (not imported, to keep the public-key layer out of the pairing
  closure); the order bound following ElGamal's private `dlc_uprob_bad_le`; the final inequality inline. Are these
  dispositions right? Is the inline verdict identity a re-proof of a public lemma that should be imported or ledgered?
- **#346** (review § *Duplication and reuse*, BM-F08/F09): `ofFn_padFin_ofFn` (a one-line specialization of
  `ofFn_padFin_of_length`), `cast_eq_padFin` (from `padFin_ofFn`, `cast_eq`), `ofFn_decAnswer_some` (`decAnswer_some` +
  `List.ofFn_cons`), the private `sidSpec_rng_one'`/`_two'` (promotion request, BM-F08), and the new public lemma
  `abs_expect_bb1Sim_sub_distinguisherL_le` (glue, BM-F09). The checkpoint helpers `Draws`, `Words`, `Handler` and
  `Reduction` (166 public declarations) were reviewed at the checkpoint (in-house REPORT). Is any part of the 174 new public
  declarations or of the proofs a duplicate of a public TCSlib or Mathlib lemma, or a copy of a private one, beyond these
  disclosures?
- Name clashes: none of the 9 files' declarations (private included) has an exact full-name clash anywhere else in
  TCSlib at T44 (`checks/nameclash-T44.txt`); #340 adds no public name.

**6. Rule 10** (`rule10/`; § 9 has the figures)
- **Seals on the changed owners whose request sets change in T44.** `Pairing/Assumptions` (#340's owner) and #346's five
  owners downstream of it (`BBM/Words`, `BBM/Handler`, `BBM/Reduction`, `BBM/Oracles`, `IB/BonehBoyenMachine`): strict and
  coe, A and B, 24 seals. Are they canonical, closure-complete and bound to T44?
- **The other three #346 owners** (`IB/Defs`, `IB/BonehBoyen`, `BBM/Draws`) do not import `Assumptions`. They were not
  re-sealed: a collector run over all eight #346 owners at T44 gives request sets **row-identical** to phase 2's snapshot-#4
  records (`2ec72515`), whose seals passed. Is request-set identity (with the owner sources and probes byte-identical) a
  sufficient ground?
- **The unchanged Gate 40 owners downstream of the changed files** (`KeyExchange/Joux`, `IB/BonehBoyenSecurity` and the
  facades `AdvancedEncryption/IdentityBased` and `AdvancedEncryption`) were **re-sealed** on T44 (the supplement, by the
  coordinator's ruling): their request sets grew since Gate 40's merged-tree seals, so identity could not be shown. Strict and
  coe, A and B, with Gate 40's paired controls (`supplement/`, § 9). `Pairing/Group` and `Pairing/Operations` are not
  downstream of the changed files. Are these seals canonical and bound to T44?
- **Paired controls on `Assumptions`** (pair-bdh's `mkctl_pbdh.py`: LE-gate40's rows plus nine rows for `distinguisherL`,
  `runAtL`, `layout`, `ofPolyTime`, `advInput`, `accept`, `uprob`, `OrderAtLeastExcept`, `inst`), strict and coe.
- **The explicit-unfold scan** over the 9 changed files. Does any proof read a foreign definition other than through a
  published reader, in particular `encT`, `pairEncode`/`pairFstD`/`pairSndD`, `NUPPT` layouts, `sampleBelowL`, `inLens`,
  `outLens`, `sidSpec`, `oracleImpl`, `bb1SimImpl`, `freshImpl`, `castImpl`, the encodings and `Ops`?

**7. Sources and citations** (`checks/sources.txt`; `sources-r1.zip` `references/`)
- **T1's attribution:** "not stated in [BB04] or [Jou00], which define the two problems ([BB04, §3.1]). The implication is
  independently derived here: the folklore fact that deciding is no harder than computing." Is that accurate against the
  BB04 and Jou00 transcriptions, and is "folklore" an acceptable attribution under ruling Q10?
- **T4 and the helpers:** [BB04, §4.2, the algorithm `B` in the proof of Theorem 4.1, whose cost is the theorem's
  `Θ(τ ℓ q_S)`]; the helpers' `[BB04, proof of Theorem 4.1]`; the module docstring's "[BB04, pp. 7–8]" against the
  References entry "§4.2 (pp. 6–8)". Are the locators right?
- **`BBM/Draws.lean`'s `draw`** cites **[PS10, Theorem 52.3]** for "an exponent of `Z_p` drawn from `n · n` coins" by the
  rejection sampler `sampleBelowL`. `references/pass-shelat-2010-ch2.raw.lines1338-1420.md` has §2.8 with Theorem 52.3
  (the discrete-log collection; its proof says "It is easy to sample the domain `D_i`"). Is this an apt citation, or a
  stretched locator that should name the library's sampler source instead?
- New tags at T44 appear only in the five new helper files (`[BB04]`, `[BB04, proof of Theorem 4.1]`, `[PS10]`,
  `[PS10, Theorem 52.3]`); the four modified files gain no tag. Every key used has a `## References` entry except
  `Assumptions.lean`'s `[Jou00, SOK00, BF01]` (BB04 §3.1's credit line; `SOK00` and `BF01` have no entry), which is at the
  tip already (#331, Gate 40 closed). Is any tag fabricated or wrong?

**8. Docstrings and sketches**
- Every new public declaration has a docstring that states its formula in Lean argument order (BM-F02 fixed by LE-bb1m).
- Every proof of 15 lines or more carries a `**Proof sketch.**` (`lint/sk15-9files.txt`: the only hit is
  `BonehBoyen.lean:631 bb1SimChal_fresh`, pre-existing from #331, BM-F06, outside both PRs).
- Do T1's and T4's sketches describe the delivered proofs? Note that T4's sketch and `Oracles`' module docstring call
  `Games.exists_handlerMachine` "the handler theorem T1", the Games campaign's own label, which is not this campaign's T1
  (`bdhAssumption_of_dbdhAssumption`). Is that confusing enough to fix?

**9. The joint replay and the axioms** (the merge-condition evidence; `replay/`)
- Does the replay bind to T44, and does it show no regression? Is anything necessary missing (a missing necessary piece of
  evidence is a **major**)?

**10. Is anything undisclosed?** Among the two PRs' commits, their descriptions, the two maintainer reviews and the records
after them, is any change, claim or omission undisclosed? The known slips are listed below.

## The joint replay on snapshot #4 (maintainer, 2026-11-17)

Recipe: `briefs/pass-shelat-ch5-8/maintainer/snapshots.md` (job recipe) and `workflow.md` on `main` §6.1. Tools: the
snapshot recipe's (`olean-rebase-dl-oleans-2/…/tools-used/`, as copied into #346's phase-2 `tools-used/`) unmodified; the
seal harness is phase 2's `tools-used/seal` unmodified, plus pair-bdh's `mkctl_pbdh.py` unmodified; the drivers are new
(`replay/tools/run-build-g44.sh`, `replay/tools/rule10_g44.sh`). One Lean process at a time.

- **Copy and overlay.** Snapshot #4 rehashed 0 extra / 0 changed / 0 missing against its map before the copy. `cp -al` gave
  `$SP/olean-replay-g44` (1453 files, all hard links). The Mathlib overlay (3346 symlinks) and NthRootLemmas
  (`c0a9cff0…`) were added to the output only.
- **Plan.** `stateplan.py init` at `463f2244` keys 1422 modules; `downorder.py` gives 9 changed and 16 downstream;
  `fullorder.py` gives the closure of root `TCSlib` and both `audits/*/Checks`, 1427 modules (closure check: 0 missing,
  0 extra). The plan builds **16** and reuses 1411; the queue equals the downstream set: `Pairing/Assumptions`, `Pairing`,
  `KeyExchange/Joux`, `KeyExchange`, `IB/Defs`, `IB/BonehBoyen`, the five helpers, `IB/BonehBoyenMachine`,
  `IB/BonehBoyenSecurity`, the facades `IdentityBased` and `AdvancedEncryption`, and root `TCSlib`.
- **Build** (`runner.py` through `scripts/lean_check_tree.sh`, 03:52–03:53 UTC): **16/16 rc 0, 0 `error:`, 0 `error(`, 0
  occurrences of "error"**. Warnings: exactly 2, both `declaration uses 'sorry'` in `BonehBoyenSecurity` (T2, T3); the 9
  changed modules have 0. All 16 oleans are byte-identical to earlier committed builds of the same sources
  (`replay/checks/olean-vs-refs.txt`): `Assumptions` to int-x-341-340's B and phase 2's cross-build X; the #346 modules to
  346c's.
- **State.** `stateplan update` took 16; `stateplan check` over the 1427-module full closure: **RESULT OK**.
- **No write-through.** All 16 rebuilt oleans have link count 1; no `.ilean`. Snapshot #4 rehashed **0/0/0** after the
  replay and again at the end of the job.
- **Output** `$SP/olean-replay-g44` is **kept**: it becomes snapshot #5 if #340 and #346 both merge and the final merge
  commit's Lean equals T44. Its map without `Mathlib/` (what `snapmap.py make` gives after recipe step 6) has 1458 entries,
  SHA-256 `ded2f64d177fc73a55c8f55e0ad1bc4699392c2a53c7cfb45f9152b55ed4abda`; against snapshot #4: 1449 equal, 4 changed
  (`Assumptions`, `Defs`, `BonehBoyen`, `BonehBoyenMachine`), 5 added (the helpers).
- **Admissions** (`tipcensus.py`, build records of every snapshot generation plus this job's; `replay/admissions/`): tip
  `1d1a9bb3` **198**, T44 **196**: **−2, exactly `Pairing/Assumptions` (T1) and `IB/BonehBoyenMachine` (T4)**; the five
  helpers have 0. No record disagrees; the same 34 modules outside root `TCSlib`'s closure have no record.
- **Axioms** (`replay/probe-src/Axioms44.lean` = phase 2's `Axioms346.lean` plus `Pairing.Assumptions` in the census; rc 0,
  0 errors):
  - **T1** `bdhAssumption_of_dbdhAssumption` and **T4** `exists_bb1_distinguisher`: `[propext, Classical.choice,
    Quot.sound]`; dependency trace: T1's closure 17314 constants and T4's 19638, each reaching **0** sorried constants.
  - The public lemma, the four `BonehBoyen` readers and three `BB1Machine` helpers: the standard three; the three `onSpec`
    readers: `[propext, Quot.sound]`.
  - **`bb1_sidSecure`**: `[propext, sorryAx, Classical.choice, Quot.sound]`, and its closure (19674) reaches **exactly
    `bb1_sim_real` and `bb1_sim_random`** (T2, T3).
  - Census of the 9 owners: **604 constants, 0 non-standard.** The summary differs from 346c's only in T1's row (now
    standard).
- **Rule 10.** Every probe ran through phase 2's `runner_full.py` (`lean -DmaxErrors=0`, no `-o`), on `$SP/olean-replay-g44`;
  both error forms are counted from the raw logs (`rule10/*/error-forms-*.txt`).
  - **`Pairing/Assumptions`** (collector over that owner alone, then `rule10_b.sh` unmodified): strict A/B and coe A/B,
    requests **895 / 896 / 894 / 895**, each rc 0, 0 `error:`, 0 `error(`, install and EOF records, no failing declaration.
    The four request sets are **row-identical** to pair-bdh's in-house seals at `916afc25` (and coe A/B to phase 2's
    cross-build X), and the four probe sources are byte-identical (`rule10/compare/assumptions.txt`).
  - **Paired controls on `Assumptions`** (`mkctl_pbdh.py`): 4 sealed and 4 unsealed probes per variant; the 25 sealed
    negatives per variant (12 in A, 13 in B, which also has `PolyExpr.eval`) each fail exactly once (50 `error:` lines in
    each of strict and coe, 0 `error(`), every reader passes, every unsealed probe has 0 errors: **ALL_OK True** in strict
    and in coe. Both `ctlcheck` results are identical to pair-bdh's.
  - **The five #346 owners downstream of `Assumptions`** (collector over all eight #346 owners): strict A/B and coe A/B,
    **20/20 rc 0, 0 `error:`, 0 `error(`**, install and EOF records, no failing declaration. Requests (strict A / strict B /
    coe A / coe B): `Words` 2243/2244/2242/2243, `Handler` 2276/2277/2275/2276, `Reduction` 2310/2311/2309/2310, `Oracles`
    2311/2312/2310/2311, `BonehBoyenMachine` 2312/2313/2311/2312. Each is phase 2's snapshot-#4 count **+2**, and the added
    rows are exactly #340's private `Pairing.tupleBdh` and `Pairing.tupleTgt`; 0 rows removed. The 20 request sets are
    row-identical, and the probes byte-identical, to phase 2's cross-build X seals (`b90b966b`), which also passed.
  - **Not re-sealed, by request-set identity:** `IB/Defs` (805/806/804/805), `IB/BonehBoyen` (840/841/839/840) and
    `BBM/Draws` (1645/1646/1644/1645). Their records at T44, from the same collector run, are row-identical to phase 2's
    snapshot-#4 records (`2ec72515`), with owner sources and probe sources byte-identical; phase 2 sealed them (32/32,
    0 errors) and reconfirmed coe A on snapshot #4 (`rule10/compare/owners.txt`).
  - **Explicit-unfold scan** over the 9 changed files: 1016 items (750 THEOREM, 166 LOCAL_OR_UNRESOLVED, 98
    OWNED_DEFINITION, 2 SIMPROC), **0 foreign**; it is exactly the union of pair-bdh's 69 items and 346c's 947. The kinds
    probe had rc 0.
  - **Supplement: the unchanged Gate 40 owners downstream of the changed files** (`supplement/README.md`; run 04:35–05:01
    UTC; collector over the four, then `rule10_b.sh` unmodified with LE-gate40's `mkctl_g40.py`): `KeyExchange/Joux`
    904/905/903/904, `IB/BonehBoyenSecurity` 2312/2313/2311/2312, `AdvancedEncryption/IdentityBased` 2312/2313/2311/2312,
    `AdvancedEncryption` 2409/2410/2408/2409 (strict A / strict B / coe A / coe B). **16/16 rc 0, 0 `error:`, 0 `error(`**,
    install and EOF records, no failing declaration. Against Gate 40's merged-tree seals (`9e7a9648`) every record gains rows
    (Joux +253, `BonehBoyenSecurity` and the `IdentityBased` facade +1208, the `AdvancedEncryption` facade +1161) and loses
    none, with the owner sources byte-identical. Paired controls (covering subset: the `IdentityBased` facade and `Joux`):
    24 sealed negatives per variant each fail exactly once, every reader passes, every unsealed probe has 0 errors: **ALL_OK
    True** in strict and in coe. `BonehBoyenSecurity` declares no definition; its request sets equal the facade's row for
    row. Snapshot #4 rehashed 0/0/0 before and after; the output still matches its map `ded2f64d…`.
  - **Name clash** (`checks/nameclash-T44.txt`, phase 1's `nameclash.py` over every declaration of the 9 files, private
    included, against every other TCSlib file at T44): **0 exact full-name clashes**.
- **Lint** (`campaign_style_lint.py TCSlib/Cryptography --check8b`, tip and T44 exports): 92 FAIL / 104 WARN on both sides,
  the non-INFO line sets identical (only the file count of the summary line changes, 519 → 524), so **no new FAIL or
  WARN**. The INFO changes are the size and declaration-count lines of the 9 files (`BonehBoyen` 714, `Handler` 899 and
  `Words` 632 over the 600 target, all under the 1000 cap). `style_lint.py` on the 9 files: 0 findings.

## Known dispositions and slips (not findings)

- **#346's review findings** (`fills/bb1-machine/final-r1/review.md`): BM-F01 (info) and BM-F02 (minor) fixed by LE-bb1m;
  BM-F03 closed by phase 2's `Oracles`-owned controls (ALL_OK); BM-F04 superseded; BM-F05 evidence nits; BM-F06
  (`bb1SimChal_fresh`'s 15-line proof without a sketch, pre-existing, cleanup ledger); BM-F07 sizes; BM-F08 (promotion
  request for `sidSpec_rng_one/_two`, carried to the bb1-sim reader probe); BM-F09 (the public glue lemma). Grade them.
- **#340's in-house "Not yet done"** (REPORT § *Limits*): the downstream owners' seals after `Assumptions`' closure grew.
  Phase 2's cross-build X sealed the five #346 owners downstream of `Assumptions` (20/20, 0 errors, each request set +2
  rows: `tupleBdh`, `tupleTgt`), and this gate's replay seals them on T44.
- **The PR descriptions** were updated by Seyoon on 2026-11-17 (#340 at 04:34:27Z, retitled "Pairing fill pair-bdh: T1
  bdhAssumption_of_dbdhAssumption", base, joint check and seal status corrected; #346 at 04:34:39Z, with phase 2 and the
  joint check). `pr340-description.md` and `pr346-description.md` are those bodies, read with the GitHub MCP tool and the
  REST API (the same text). The REST `base.sha` fields (`b6d977ea…`, `7291f6b2…`) are the tips at retarget and at opening;
  records commits only have landed since.
- **Authorship.** T1 and #346's three checkpoints were written in-house by the maintainer; #346's middle three commits by an
  external Claude worker; LE-bb1m by the maintainer. The signing key is shared by the account's Claude sessions (BS-F08).
- **The 346c replay** (#346 alone on snapshot #4, `$SP/olean-replay-346c`, map `5e63b3cc1a0efd40c3b5875d701b99a7457cc5f2a3b2831d4a7ab8cc7cf35404`,
  rechecked equal at staging) is kept as well, in case #346 merges without #340.
- **Phase 2's seal evidence on snapshot #2** (32 seals, 314 sealed negatives per variant, the `Oracles` controls) is in
  `fills/bb1-machine/final-r1/phase2/phase2-evidence.zip`; it is not copied here (28 MB). A pointer and the cited summaries
  are.

## Merge interaction (maintainer merge conditions, not audit items)

- Merge both PRs together, or #346 first: the replay output `$SP/olean-replay-g44` is adoptable as snapshot #5 only if the
  final merge commit's Lean equals T44 (procedure step 3). If #346 merges alone, `$SP/olean-replay-346c` is adoptable
  instead, and #340 then re-replays.
- #340's base is `cryptography/pass-shelat-ch2-4` (checked with the GitHub tools at staging); it is not stale.

## Evidence files

- **`pack-r1.md`** (this file), **`dispatch-r1.md`** (the Codex prompt; records only).
- **`pr340.diff.txt`** (`git diff 9e7a9648..916afc25`, equal to the three-dot `git diff 1d1a9bb3...916afc25` byte for byte;
  1 file, +227/−8), **`pr346.diff.txt`** (`git diff 7291f6b2..89a18a82`, equal to the three-dot view; 8 files, +2741/−17),
  **`T44.diff.txt`** (`git diff 1d1a9bb3 33681cb8` over the code paths; the 9 files).
- **`pr340-description.md`**, **`pr346-description.md`**: the PR bodies as updated on 2026-11-17 (REST `.body`, raw).
- **`source-head-r1.json`**: the pins and, for each of the 9 files at T44, status, SHA-256, line count and over-width count.
- **`sources-r1.zip`**: `T44-33681cb8/` the source closure at T44 (168 modules: the import closure of the `IdentityBased`,
  `KeyExchange` and `Pairing` facades); `pr340-head-916afc25/` and `pr346-head-89a18a82/` the changed files at each head;
  `tip-1d1a9bb3/` the four changed files at the tip; `references/` the BB04 and Jou00 transcriptions (DW-7), Gate 40's
  excerpts, and the [PS10] §2.8 lines with Theorem 52.3. Its `README.md` gives every entry's SHA-256 and origin.
- **`verification-r1.zip`**: `MANIFEST.md` (the layout and each entry's provenance) and `SHA256SUMS` (every other entry).
  - `replay/`: the joint replay (landing trees, export and copy, orders, state, plan, the build with every module log,
    the Mathlib extra, link counts and base rehashes, the olean comparison, the output map, admissions, axioms with the
    probe source and log, statements, lint) and its drivers and tools;
  - `rule10/`: the `Assumptions` seals and controls, the five owners' seals, the records of the three owners not re-sealed
    (`own/rel/`), the request-set comparisons (`compare/`), the scan, with probe sources, run records and logs;
  - `checks/`: the re-checks from git objects (series and signatures, merge trees, headers, the T1 frozen check, the
    reader-insertion check, the T4 frozen check, decls2, sources, the reviews' evidence integrity), with their scripts;
  - `reviews/`: the two maintainer reviews (#346: `review.md`, phase 2 `README.md`, both `SHA256SUMS`; #340: the in-house
    `REPORT.md` and the int-x-341-340 `README.md` and `SHA256SUMS`), and `POINTERS.md` with the path, size and SHA-256 of
    every review evidence ZIP at the records tip (not copied);
  - `records/`: the pairing plan and its decision-log extract (rows of 2026-11-16 and 2026-11-17 from Gate 40's findings
    to #346's phase 2), Gate 40's round-1 and round-2 findings and round-2 resolutions, the approved reader text, #346's
    issue brief, and `policy.md`;
  - `pr/pr-rest-fields.json`: the REST fields read after the description updates;
  - `supplement/`: the seals and controls of the unchanged Gate 40 owners downstream of the changed files (§ 9).
- **`SHA256SUMS-r1`**: the files of this gate directory.

## Findings delivery

Return `gate44-pairing-fills-findings.md` as Markdown in this chat. If you have several evidence files, return a ZIP. The
user dispatches and merges.

| # | Severity | PR · file · declaration | Claim | Evidence | Proposed fix |
|---|---|---|---|---|---|

Grade BM-F01 to BM-F09 and #340's seven overlap disclosures in a separate table (agree, or regrade with the reason). Report
the audited heads, T44 and the counts by severity. The gate closes at zero blockers and zero majors.

**Severities**
- **blocker:** a false or unusable statement, a proof that does not establish the frozen statement, or a scope violation.
- **major:** any of the following:
  - a changed frozen statement;
  - a reader beyond the approved seven, or a reader that is not a pure verbatim insertion;
  - a forbidden read in a touched declaration not covered by the rulings;
  - an undisclosed copied private lemma, or an undisclosed re-proof of a public one;
  - a fabricated source tag;
  - necessary evidence that cannot be verified.
- **minor:** documentation or API defects, including an inaccurate formula docstring, proof sketch or citation.
- **note:** anything else.
