# Gate 40 · Pairing campaign statements: bilinear groups, Joux, Boneh–Boyen BB1 (statement)

Round 1. The auditor is Codex, under the standing ruling of 2026-11-11 (Codex for audits and reviews). The pairing
campaign keeps its own gate folder (`briefs/pairings/gates/`); the gate number continues the global sequence.

- **PR:** draft [PR #331](https://github.com/Shilun-Allan-Li/tcslib/pull/331) at
  `110c2f9db810d243693b9a5e8976a5ad205f1bab` (branch `stmt/pairings`, tree
  `e0fcac097c5e6e66ff78496c575a417f50e8e9f7`).
- **Target and base:** `cryptography/pass-shelat-ch2-4`, merge base `523d80d2d4dd8e4ed6799358831e5b3806c6187b`. The
  diff `origin/cryptography/pass-shelat-ch2-4...110c2f9d` equals `523d80d2..110c2f9d` byte for byte (`pr.diff.txt`,
  119,848 bytes, SHA-256 `9deba4da…`; `pack-checks/series.txt`). Since the base the records branch has gained #318,
  #319, #323 and (during this staging) #326; their interaction is under **Merge interaction**.
- **Commits:** 3, all by the maintainer (author and committer Claude, `gpgsig` header present on each):
  `8aa11165` modules, `b7ca2547` root exports, `110c2f9d` "move T4 to BonehBoyenMachine (ruling Q11)". Rebased from
  the round-1 head `ce9c3728` with range-diff 2/2 `=` (evidence `git/rebase-range-diff.txt`).
- **Scope:** a **statement audit** before any fill, plus an audit **as proofs** of the results the PR already proves.
  The campaign plan is `PairingCryptographyPlan.md` (scope ruling, location ruling, rulings Q1–Q13 of 2026-11-16, all
  recommendations accepted, Q11 applied).
- **Sources** (PDFs not committed; text excerpts of only the passages used are in `source-excerpts/` and in the
  bundle, ruling Q12): [Jou00] A. Joux, ANTS-IV 2000, LNCS 1838, pp. 385–393 (SHA-256 `dd423b93…f6df9`); [BB04]
  D. Boneh, X. Boyen, ePrint 2004/172, full version December 2004, **its numbering** (SHA-256 `63c1c7b0…35de`). Both
  hashes were re-checked when the excerpts were written.

## What changed

13 files, 2153 insertions, 0 deletions (`pack-checks/files.txt`). Paths under `TCSlib/Cryptography/`. Every line is at
most 100 characters; every file is under 1000 lines.

| File | Lines | Public decls | `sorry` | Content |
|---|---:|---:|---:|---|
| `Pairing/Group.lean` | 299 | 24 | 0 | `BilinearGroup`, `BilinearGen`, `desc`, `inst`, `OrderAtLeastExcept`; group facts (all proved) |
| `Pairing/Assumptions.lean` | 221 | 15 | 1 | `tupleStr`, `bdhStr`, `dbdhGame`, `dbdhAdv`, `DBDHAssumption`, `bdhGame`, `BDHAssumption`; **T1** |
| `Pairing/Operations.lean` | 117 | 1 | 0 | `BilinearGen.Ops` (efficiency contract, Q13) |
| `KeyExchange/Joux.lean` | 193 | 15 | 0 | protocol, correctness, `jouxGame_eq_dbdhGame`, key indistinguishability (all proved) |
| `AdvancedEncryption/IdentityBased/Defs.lean` | 408 | 37 | 0 | `IBEScheme`, `Correct`, `sidImpl` and its 9 case lemmas, `oracleImpl`, `sidGame`, `SIDSecure` |
| `AdvancedEncryption/IdentityBased/BonehBoyen.lean` | 553 | 45 | 0 | BB1, `bb1Scheme`, `bb1_correct` (proved), the simulator `bb1Sim*` |
| `AdvancedEncryption/IdentityBased/BonehBoyenMachine.lean` | 78 | 1 | 1 | **T4** `exists_bb1_distinguisher` (Q11) |
| `AdvancedEncryption/IdentityBased/BonehBoyenSecurity.lean` | 170 | 3 | 2 | **T2**, **T3**, `bb1_sidSecure` (proved from T2–T4) |
| facades `Pairing`, `KeyExchange`, `AdvancedEncryption/IdentityBased`, `AdvancedEncryption` | 31, 23, 32, 25 | — | 0 | each imports and lists every child (`pack-checks/facades.txt`) |
| `TCSlib.lean` (root) | 86 → 89 | — | — | three imports, insertion only |

`pack-checks/decls.txt` lists every declaration (kind, body `rfl` / `Iff.rfl` / proof / `sorry`, docstring, source tag,
sketch); `pack-checks/readers.txt` the reader of every public definition (all present; structures are read through
their fields); `pack-checks/names.txt` finds **no** full-name clash with the 22,173 public names at the tip.

### The four targets

```lean
-- T1  Pairing/Assumptions.lean
theorem BilinearGen.bdhAssumption_of_dbdhAssumption
    (hN : ∃ δ : ℕ → ℝ, Negligible δ ∧ G.OrderAtLeastExcept (fun κ => 2 ^ κ) δ)
    (h : G.DBDHAssumption) : G.BDHAssumption
-- T2  BonehBoyenSecurity.lean
theorem bb1_sim_real (A : NUPPT) (q : ℕ) (b : Bool) (κ : ℕ) :
    advantage ((bb1Scheme G ℓ).sidGame A q b κ) (bb1SimGame G ℓ A q b true κ) ≤
      uprob (fun r : G.gen.Coins κ => (G.inst κ r).order < 2 ^ ℓ.eval κ)
-- T3  BonehBoyenSecurity.lean
theorem bb1_sim_random (A : NUPPT) (q : ℕ) (κ : ℕ) :
    advantage (bb1SimGame G ℓ A q false false κ) (bb1SimGame G ℓ A q true false κ) = 0
-- T4  BonehBoyenMachine.lean
theorem exists_bb1_distinguisher (H : Candidates.ArithmeticFP) (O : G.Ops) (A : NUPPT) (q : PolyExpr) :
    ∃ D : Bool → NUPPT, ∃ σ : ℕ → ℝ, Negligible σ ∧ ∀ (b real : Bool) (κ : ℕ),
      advantage (bb1SimGame G ℓ A (q.eval κ) b real κ) (G.dbdhGame (D b) real κ) ≤ σ κ
```

and the proved headline

```lean
theorem bb1_sidSecure (H : Candidates.ArithmeticFP) (O : G.Ops)
    (hN : ∃ δ : ℕ → ℝ, Negligible δ ∧ G.OrderAtLeastExcept (fun κ => 2 ^ ℓ.eval κ) δ)
    (h : G.DBDHAssumption) : (bb1Scheme G ℓ).SIDSecure
```

`bb1_sidSecure` uses **T2, T3 and T4 only**; T1 (DBDH ⇒ BDH) is a separate result that nothing in the PR uses. Its
proof chains nine games, `sidGame b=0 → sim(0,P) → dbdh(D₀,P) → dbdh(D₀,R) → sim(0,R) → sim(1,R) → dbdh(D₁,R) →
dbdh(D₁,P) → sim(1,P) → sidGame b=1`, giving `2δ + 4σ + dbdhAdv D₀ + dbdhAdv D₁` (`linarith` over
`advantage_triangle` and `advantage_comm`).

## Rulings and records in force

- **Scope (Seyoon, 2026-11-16):** abstract symmetric bilinear groups in the asymptotic/NUPPT framework with BDH and
  DBDH; Joux (protocol, correctness, key indistinguishability under DBDH); BB1 in the standard model (IND-sID-CPA,
  scheme, correctness, security from DBDH). Out: Boneh–Franklin, Type-3 pairings, concrete groups, BB2, HIBE depth > 1,
  BB04 §4.3/§6/§7.
- **Location (Seyoon, 2026-11-16):** `Pairing/`, `KeyExchange/`, and IBE under `AdvancedEncryption/IdentityBased/`
  (namespace `TCSlib.Cryptography.AdvancedEncryption.IdentityBased`). `AdvancedEncryption.lean` is **shared with GSW**;
  the draft facade imports only `IdentityBased`, and whichever statement PR lands second adds its child.
- **Q1–Q13 (Seyoon, 2026-11-16), all (A):** Q1 abstract bundle from a uniform PPT generator with a total description
  map; Q2 `g` uniform in `G^*`; Q3 Joux single-point `F_W`; Q4 Joux key indistinguishability under DBDH only; Q5 typed
  IBE algorithms, "BB1 is PPT" deferred; Q6 `ℓ`-bit identities read in `Z_p`; Q7 one machine with an `Init` oracle;
  Q8 out-of-space challenges refused with `⊥`; Q9 the two-experiment advantage; Q10 keep T1; Q11 three fill units,
  T4 in its own module; Q12 PDFs uncommitted, Markdown transcriptions of only the passages used, ingested later; Q13
  `Ops` as drafted.
- **Plan § Sources, "Where the papers' formulations differ from the draft"** (nine disclosed deviations) and
  **§ Modelling choices for the statement gate** (thirteen items) are the deviation list this gate checks against.
- **Standing rules:** Rule 10 (no proof reads another file's definition except through published readers); policy
  §§1–3 (modularity, attribution with `[Tag, location]`, `**Proof sketch.**` for nontrivial proofs and sorry-stubs);
  the #305 facade rule; lines of at most 100 characters.

## Questions for the audit

1. **Fidelity of the definitions under the rulings.** Compare with `source-excerpts/BB04-excerpts.md` (§2.1, §2.2,
   §3.1, §4.1, §4.2, §4.4) and `Jou00-excerpts.md` (§2, §3, §5).
   - *Bundle and generator* (`BilinearGroup`, `BilinearGen`): bimultiplicative `pair : G →* G →* GT` for
     [BB04, §2.2] item 1 (`bilinear_pow` derives `e(u^a, v^b) = e(u, v)^{ab}` for natural exponents; the paper says
     `a, b ∈ Z`); non-degeneracy at the bundle's `gen` (`pair_ne_one` extends it to `G^*`); equal prime orders; a total
     description map, exact description length, no validity predicate (Q1); large order only through
     `OrderAtLeastExcept N δ`.
   - *BDH and DBDH* (`dbdhGame`, `bdhGame`): `g` uniform in `G^*`, `a, b, c` uniform in `Z_p`, `T` uniform in `G_T`,
     the adversary's coins last; inputs `⟨d, ⟨g, g^a, g^b, g^c, T⟩⟩` with the description in front (D3); the advantage
     `|·|` of [BB04, §3.1]'s signed difference (deviation 6); BDH wins iff the output **is the encoding** of
     `e(g, g)^{abc}`.
   - *IBE interface and selective-ID game* (`IBEScheme`, `sidImpl`, `sidGame`, `SIDSecure`): one `NUPPT` with
     oracles `Init` (0), `KeyGen` (1), `Challenge` (2) (Q7); `Setup` sampled before the run and revealed only at
     `Init` (is this [BB04, §2.1]'s order *in distribution* for every adversary, including one that queries
     `KeyGen`/`Challenge` before `Init` or calls `Init` twice?); `⊥` (`zeroBits`) for `KeyGen(ID*)`, before `Init`,
     and for challenges outside `M` (deviation 7, Q8), with a validity bit on `KeyGen` answers but none on
     `Challenge` answers; fresh `KeyGen` coins per query; the first valid challenge recorded and repeated; one
     polynomial budget for all queries; `ℓ(κ)`-bit identities (Q6); messages as `wT(κ)`-bit strings with
     `MsgSpace` = "is an encoding" (Q9 of the modelling list); two-experiment advantage (Q9), quantifier shape of
     `FixedLengthPKScheme.INDSecure`.
   - *BB1* (`BB1.setup/keyGen/encrypt/decrypt`, `bb1Scheme`): depth-1 [BB04, §4.1] with `Setup`'s sample order
     `g ∈ G^*, α, h, g₂` (`h, g₂` uniform in `G`, as the paper: "random elements `h_1 … ∈ G` and a random element
     `g_2 ∈ G`"); `F(x) = g₁^x h`; `idToZ` = binary value mod `p` (§4.4 with `H` the identity on `ℓ`-bit strings,
     `2^ℓ ≤ p`); description tags and `⊥` across descriptions (modelling choice 12); `decodeT` reading `1` off the
     message space.
   - *The simulator* (`bb1SimParams`, `bb1SimKey`, `bb1SimInit`, `bb1SimKeyQ`, `bb1SimCt`, `bb1SimChal`,
     `bb1SimGame`): against the proof of [BB04, Theorem 4.1] at depth 1 (`g₁ = X`, `g₂ = Y`,
     `h = X^{−ID*} g^{α₁}` with `α₁` drawn at the first `Init`, keys `(Y^{−α₁/(ID−ID*)} F(ID)^r, Y^{−1/(ID−ID*)} g^r)`,
     challenge `(M_b·T, Z, Z^{α₁})`). Note that `ZMod` division by zero is `0`: on colliding residues
     (`ID ≠ ID*` as strings, `idToZ ID = idToZ ID*`, possible only when `p < 2^ℓ`) the simulated key is a defined but
     wrong value; T2 excludes those coins and T4 must reproduce the same value.
2. **Is every target true and sufficient, with no hidden hypothesis?**
   - **T1:** the sketch's distinguisher re-pairs the first five components and compares `A`'s answer with `T`'s
     encoding; on `R_BDH` it accepts with probability `≤ 1/p`, so `Pr[A wins] ≤ dbdhAdv + 2^{−κ} + δ(κ)`. Is
     `OrderAtLeastExcept (2^κ)` the right (and only) extra hypothesis? Is "re-pair" polynomial-time for the
     `pairEncode` layout of `tupleStr`/`bdhStr`?
   - **T2:** is the bound `Pr_r[p < 2^ℓ]` correct for **every** adversary, budget `q` and bit, with the simulator's
     `α₁` drawn at `Init` rather than at `Setup`, the real `h` uniform in `G`, and `MsgSpace` depending only on the
     description? Is the coupling of the two `simulate` runs (different state types: `Option id × Option ct` versus
     `Option (id × Z_p) × Option ct`) expressible with the existing `Games` lemmas, or must the fill request a shared
     state-relation lemma (plan § Risks)?
   - **T3:** exact equality `= 0`: `T` is used only in the challenge's first component; is `T ↦ M_b·T` reindexing
     valid when the challenge is chosen adaptively after `T` is sampled?
   - **T4:** for **all** `b`, `real`, `κ` (including generator coins with `p < 2^ℓ` and colliding residues) is there a
     uniform PPT `D_b` whose DBDH experiment is within negligible `σ` of `bb1SimGame`? It needs `O` (order, `mulG`,
     `powG`, `mulT`, `memT`) and `H` (`ArithmeticFP`: negation, difference, inverse, with `0⁻¹ = 0` to match `ZMod`),
     exponents by `Candidates.sampleBelowL` with `wG(κ)`-bit trials (`p ≤ 2^{wG}` from injectivity of `encG`), and
     the handler theorem `Games.exists_handlerMachine`. Is anything missing from `Ops` (Q13 kept `pairStr`, which the
     reduction does not need)?
   - **Sufficiency:** do T2–T4 imply `bb1_sidSecure` with exactly the hypotheses stated (`H`, `O`, `hN` at `2^ℓ`,
     `h`)? Are `H` and `O` acceptable as hypotheses of a security theorem whose paper version has none (D4)?
3. **Audit the proved results as proofs** (`Pairing/Group.lean`, `KeyExchange/Joux.lean`, `BonehBoyen.lean`,
   `BonehBoyenSecurity.lean`):
   - Joux correctness `jouxKey_eq`, `joux_correct` ([Jou00, p. 388]) and the helper `pow_val_mul_mul`;
   - `jouxGame_eq_dbdhGame` (`rw [jouxGame_eq, dbdhGame_eq]; simp only [jouxKey_eq]; rfl`: the final `rfl` unfolds
     only `jouxMsg`, defined in the same file) and `jouxKeyIndist_of_dbdhAssumption` (through `dbdhAssumption_iff`);
   - `BB1.decrypt_encrypt` (the paper's computation, `pair_comm`, `bilinear_pow`) and `bb1_correct` (through
     `correct_iff`, `honestRun_eq`, the `bb1Scheme` `simps` equations, `allOutputs_true`, `decodeT_encT`);
   - `bb1_sidSecure` from T2–T4 (the nine-game chain above; check the four `σ` and two `δ` terms);
   - the group facts `pair_ne_one`, `pow_val_bijective`, `pair_comm`, `exists_pow_eq`, `pow_val_mul(_GT)`;
   - the case lemmas `sidImpl_*` (9), `oracleImpl_*` (3), `bb1SimInit/KeyQ/Chal_*` (9).
   All compile with standard axioms only (evidence `axioms.txt`: 320 declarations + 52 auxiliary constants;
   `sorryAx` only in T1–T4 and `bb1_sidSecure`).
4. **Rule 10, readers and seals.** Every public definition has a reader (`pack-checks/readers.txt`); none is
   `@[simp]`; `bb1Scheme` has non-simp `simps` equations. Seal coverage (please rate):
   - the canonical whole-file seals (archived Gate 06/10 instrumenter; strict A, `PolyExpr.eval`-sealed B, and the
     coe variants) were run in round 2 on **three** modules: `BonehBoyenMachine`, `BonehBoyenSecurity` and the
     `IdentityBased` facade, 12/12 probes (`rule10/seal-seals-*.tsv`). The PR description's "whole-file seals pass
     12/12" counts these probes, not modules;
   - the other nine new modules (including every module with a proof: `Group`, `Joux`, `Defs`, `BonehBoyen`) rely on
     the **round-1 hand-list seals** (`round1/tools/seal.py`: 2–51 named foreign definitions per module;
     `round1/seal/summary.txt`, whose `rc=1` lines are "unknown constant" for names outside a module's closure), with
     the controls `Control_neg` (sealed read of `Correct` fails) and `Control_pos`. Is that sufficient evidence that
     `bb1_correct`, `jouxGame_eq_dbdhGame`, `jouxKeyIndist_of_dbdhAssumption` and the `simp [sidImpl]` /
     `simp [bb1SimKeyQ]` case lemmas read foreign definitions only through readers, or is a canonical seal of those
     modules a necessary condition (a **major** if necessary evidence is missing)?
5. **Docstrings, tags and sketches** against the papers' numbering (BB04 ePrint numbering throughout): every public
   declaration has a docstring; T1–T4 and `bb1_sidSecure` carry `**Proof sketch.**`. Please rate:
   - `BB1.decrypt_encrypt`, `bb1_correct` and `jouxKeyIndist_of_dbdhAssumption` explain their proofs in prose without
     a `**Proof sketch.**` heading; `jouxGame_eq_dbdhGame` has none (a four-line proof). Policy §3 asks for a sketch
     for proofs over about 20 lines or of difficulty ≥ 3.
   - T1's docstring says DBDH ⇒ BDH is "not stated in [BB04] or [Jou00]" (folklore, Q10); BB04 §3.1 does not call
     the decision form "stronger" either. Is the source line adequate under policy §2?
   - The nine disclosed deviations (plan § Sources) and their docstring counterparts: single-point Joux (D-2), `g`
     uniform (D-3), HIBE depth 1 and `ℓ`-bit identities (D-4), asymptotic (D-5), two-experiment advantage (D-6),
     `⊥` (D-7), one distinguisher per bit (D-8), T1 not in the sources (D-9), and Joux's §5 remark formalized as key
     indistinguishability (D-1, Q4). Is any deviation undisclosed?
6. **The fill-unit split.** `pair-bdh` owns `Pairing/Assumptions.lean` (T1); `bb1-sim` owns `BonehBoyenSecurity.lean`
   (T2, T3); `bb1-machine` owns `BonehBoyenMachine.lean` (T4). The split moved the 21-line T4 block byte-identically
   (evidence `statements/T4-identity.txt`, `T4-block.txt`, `BonehBoyenSecurity-at-ce9c3728.lean`).
   `BonehBoyenSecurity` imports `BonehBoyenMachine` for the proved-modulo headline. Are the files disjoint, and can
   each unit be proved without editing another unit's file (helpers beside the owned file)?
7. **Duplication** against the existing DDH (`Candidates/DDH.lean`, `DiscreteLog.lean`), El Gamal
   (`Encryption/PublicKey/ElGamal.lean`, `GroupPKScheme`) and `Games` layers (`Games/Advantage.lean`,
   `PublicKey/OracleSecurity.lean`): all five are in `verification.zip` `context/` at the tip; `pack-checks/
   dupscan.txt` has the keyword scan (no BDH, IBE or pairing-group notion exists; `bilinear` hits are unrelated
   areas). Is `BilinearGen` a justified sibling of `ExpGroupGen`/`SafePrimeGen` (D1), `dbdhGame` of the DDH
   ensembles (D2 avoids the P8-1 seed distortion), `sidImpl`/`sidGame` of `FixedLengthPKScheme.indGame` (D6), and
   `oracleImpl` a new generic helper that belongs in `Games` instead?
8. **Policy: modularity, sizes, facades.** Layout `Pairing/`, `KeyExchange/`, `AdvancedEncryption/IdentityBased/`
   per the location ruling; the largest file is 553 lines; facades import and list every child; the root gains three
   imports. Are the imports precise (no bare `import Mathlib`)? Is `Operations.lean`'s import of
   `Candidates.Arithmetic` the right layering?

## Known dispositions (not findings)

- **The shared facade.** `AdvancedEncryption.lean` is added by both this PR and #333 (GSW), and both add an import to
  `TCSlib.lean`: an expected add/add conflict, resolved by union by whichever lands second (location ruling). It is a
  merge condition (below), not a finding.
- **The proofs of T1–T4 are out of scope;** the gate asks whether the statements are true, provable on the sketched
  routes and sufficient.
- **Typed honest algorithms** without an efficiency field (Q5) and the efficiency hypotheses `H`, `O` of the security
  theorem (D4) are ruled.
- **The evidence archive** `stmt-pairings-r2.zip` was not in the records when the PR was opened; this gate files it
  (`briefs/pairings/statement-phase/evidence-r2/`, with its manifest and PROVENANCE).
- **Source ingest (policy §2) is deferred** by Q12; the excerpts here are the gate's fidelity material, not the
  ingest.

### Slips noted by the staging (please rate)

- PR description: "the whole-file seals pass 12/12" (three modules × four variants; see Q4).
- `briefs/pairings/README.md` "Current checkpoint" still names the round-1 head `ce9c3728` and "not pushed"; the plan's
  identity table also names `ce9c3728`/`b02e6ce4` and base `e7a9f70f`. The decision log and the Q11 row carry the
  current head.
- The plan's decision-log row for Q11 says "Not pushed: `origin/stmt/pairings` is still `ce9c3728`"; the branch was
  pushed afterwards at `110c2f9d` (PassShelatChapter5-8Plan.md row of 2026-11-16).

## Merge interaction (maintainer merge conditions, not audit items)

From git objects only (`pack-checks/mergetrees.txt`, `pack-checks/mergeall.txt`); the records tip during staging was
`0542dd9210ccdb844ad125cd95f8488c9f553153` (it now contains #326, merged as `7e85f4c0`).

| Merge of #331 with | Result | Modules whose closure meets both sides' Lean changes |
|---|---|---|
| tip (`#318`, `#319`, `#323`, `#326` merged) | clean | 7: `Pairing/Operations` (its closure reaches `ClassP/DTIME.lean`, changed by #326's E1–E3), `Pairing`, `BonehBoyenMachine`, `BonehBoyenSecurity`, `IdentityBased`, `AdvancedEncryption`, `TCSlib` |
| #324 sc-compose `4bd2d80b` | clean | `TCSlib` only |
| #327 seq-zk `bd19c433` | clean | `TCSlib` only |
| #332 DAGCircuit readers `94eae71b` | clean | `TCSlib` only |
| #333 GSW `48d796a8` | **conflict** in `TCSlib.lean` and `AdvancedEncryption.lean` (add/add) | `AdvancedEncryption`, `TCSlib` |

All open heads merged onto the tip in two orders (#324, #326, #327, #331, #332, #333 and the reverse grouping) give the
**same tree** `1fc1b521602bd7ac2f4199accdb7f7245f428198` once the one conflict is resolved by union (`mergeall.txt`
prints the resolved facade: both children imported and listed, both references; `TCSlib.lean` gains `Pairing`,
`KeyExchange`, `AdvancedEncryption` after `Implications`, once each).

**Merge conditions.** (1) Whichever of #331 and #333 merges second resolves the facade and root by that union and
re-checks `AdvancedEncryption` and `TCSlib`. (2) The statement evidence was built at base `523d80d2`; before merging,
rebuild the seven modules above on the merged tree (the #326 change to `DTIME.lean` is in `Operations`' closure), with
the root last. No Lean file changed by #331 is changed by any other open or merged PR.

## Evidence

`verification.zip` (99 entries, SHA-256 `348ce61f7c8f1eb07faa8c1b4cf402fbc4f241d7909c9cd456129c75e0628f70`; its
`SHA256SUMS` lists every other entry; `PROVENANCE.txt` maps each to its source; built at records `0542dd92`):
- `evidence/`: `stmt-pairings-r2.zip` (SHA-256 `83b05fbe…d573d`, 411 files, its inner manifest verified) with its
  manifest `SHA256SUMS` and `PROVENANCE.txt`, byte-identical to the files this gate files in the records;
- `evidence-extracts/`: byte copies of the entries cited here: the build (`build/closure/summary.txt`: 20/20 rc 0, 4
  target `sorry`s; `build/root/summary.txt`: 278/278 rc 0), `axioms.txt`, the seals (`rule10/seal-seals-*.tsv`,
  `rule10/modules.txt`, `seal/summary.txt`), lint (0 findings; 2 check-8 acronym WARNs), the T4 split
  (`statements/`), the series (`git/`), the olean-tree snapshots (`457ba704…` before and after) and the axiom probe;
- `round1/`: the round-1 evidence already in the records (`briefs/pairings/statement-phase/evidence/`), including the
  hand-list seal tool and logs;
- `records/`: the plan, the pairings README, the statement-phase `EVIDENCE.md` (pre-pin versions) and `policy.md`;
- `source-excerpts/`: the two excerpt files;
- `context/`: `Candidates/DDH.lean`, `Candidates/DiscreteLog.lean`, `Encryption/PublicKey/ElGamal.lean`,
  `Games/Advantage.lean`, `Encryption/PublicKey/OracleSecurity.lean` at the tip (question 7);
- `pack-checks/`: `series`, `files`, `decls`, `sorries`, `readers`, `facades`, `names`, `dupscan`, `mergetrees`,
  `mergeall`, with the scripts that produced them (git objects and `python3 -I` only; nothing was built).

Also: `pr.diff.txt`, `pr-description.md` (fetched 2026-11-16), `source-head.json` (hashes, line counts, over-width
counts of the 13 files; SHA-256 `5a52bffe…`) and `sources.zip` (the import closure at the head of every changed module,
86 files, SHA-256 `a08ebc08…`).

## Findings delivery

Return `gate40-pairings-statements-findings.md` as a Markdown file in this chat. If you have several evidence files,
return a ZIP.

| # | Severity | File · declaration | Claim | Evidence | Proposed fix |
|---|---|---|---|---|---|

**Severities**
- **blocker:** a false or unusable statement, a proved result whose proof is unsound, or a scope violation.
- **major:** a missing or wrong hypothesis, a statement too weak or too strong for its consumers (`bb1_sidSecure`, the
  fill routes), an undisclosed deviation from the sources or the rulings, a forbidden read in a proved declaration, a
  duplicate public result, or necessary evidence that cannot be verified.
- **minor:** documentation or API defects, including an inaccurate formula docstring or proof sketch.
- **note:** anything else.

Report the audited head and the counts by severity. The gate closes at zero blockers and zero majors.
