## ===== briefs/pairings/gates/40-pairings-statements/pack.md =====

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

## ===== policy.md =====

# TCSlib Contribution Policy

Standards for all Lean contributions to this repository, whether written by humans or by
agents. This document covers three things: **modularity** (how code is organized),
**attribution** (how every result is traced to a source), and **proof sketches** (how every
formal proof is accompanied by readable mathematics).

It complements, and does not replace:

- `workflow.md` — the campaign formalization process (phases, audit gates, fill epochs)
  that produces code meeting these standards.
- `.github/copilot-instructions.md` — build workflows, import rules, CI integration points.
- `AGENTS.md` / `.claude/CLAUDE.md` — the sorry-ladder proof workflow and agent roster.
- `blueprint/BLUEPRINT_PIPELINE.md` — how blueprint entries are generated and validated.

Where this document names an existing mechanism (blueprint macros, hygiene scripts), the
policy is to *use that mechanism*, not to invent a parallel one.

## 1. Modularity

**Layout.** Content lives at `TCSlib/<Area>/<Topic>/<Piece>.lean`, one coherent concept or
lemma cluster per file, with a facade file `TCSlib/<Area>/<Topic>.lean` that imports every
child and carries a `/-! -/` module docstring with a `## Contents` list (one line per child).
See `TCSlib/Complexity/NPReductions.lean` for the reference example.

**File size.** Target 150–600 lines per math file. A file approaching 1000 lines should be
split unless there is a positive reason not to (e.g. a single long proof that cannot be
usefully decomposed).

**Exports.** Every new topic facade must be imported from `TCSlib.lean`. CI only builds what
is reachable from `TCSlib.lean`; an unexported file is invisible to CI, docs, and the
blueprint.

**Imports.** Precise module imports only. A bare `import Mathlib` fails CI. Import only what
the file uses.

**Namespaces.** Namespaces are area-local: pick one namespace root per topic and use it
consistently within that topic. Do not leak auxiliary definitions into the root namespace;
mark internal helpers `private` or put them in a dedicated inner namespace.
*Model registry exception*: a model-defining **type** (a machine, circuit, formula, or
decision-tree model) may live at the root namespace, Mathlib-style, provided it is
registered in the catalog facade `TCSlib/ComputationalModels.lean`; its operations and
lemmas still live in the type's own namespace. Anything else at root is a leak.

**Layering.** Keep definition files separate from heavyweight theorem files, so that
downstream work can import a model or a class definition without pulling in every proof about
it. When a development has both a "raw/general" layer and a "bundled" layer (e.g. a machine
model that is parametric in its types, plus a bundled version carrying finiteness instances),
headline definitions and theorems are stated against the bundled layer; the raw layer is
internal plumbing.

**Helpers.** Foundational helper lemmas that serve a whole area belong in that area's
`Basic.lean`, not in the file that first needed them.

**Definitions land with their lemmas** (user, 2026-10-16). Every new public `def` is published,
in the same PR and beside the definition, with the lemmas that let a consumer read it without
unfolding:
- a structure-valued definition (a contract, a configuration, zone contents): its field
  equations, generated by `simps` with `(config := { isSimp := false })` and explicit
  projections (`simps!` where the body is another constructor's result);
- any other definition: an equation lemma `<name>_eq` (by `rfl` where that holds), or case
  lemmas that together cover every input (`_of_lt`/`_of_le`, `_true`/`_false`, one per
  constructor);
- a predicate: an `_iff` characterization;
- a machine: its run or contract lemma, the only way consumers read a machine.

None carries `@[simp]` unless a gate approves it, and each docstring states its formula. Consumers
never unfold another file's definition (the no-unfolding rule of the briefs, user 2026-10-16). The
rule binds TCSlib's own definitions: core and Mathlib definitions may reduce in a `rfl`, `decide`
or `show` step, but are never passed to `simp`, `rw` or `unfold`; use their equation lemmas
(`Bool.toNat_true`, not `simp [Bool.toNat]`) (user, 2026-10-23).
**Reducible abbreviations are notation** (user, 2026-10-26). Lean unfolds a TCSlib `abbrev` (such
as `Turing.Cfg.Halted`, `cfg.state = none`) at every step, and the standard seal cannot cover it:
under Lean's default reducibility validation, `attribute [local irreducible]` fails on a reducible
declaration (only the unsafe override `set_option allowUnsafeReducibility true`, which the
campaign's seals do not use, lifts the check). So reading an abbreviation through its body,
for example `¬ c.Halted` as `c.state ≠ none`, is allowed and is not a definitional closure. A
consumer names it in `simp`, `rw` or `unfold` only through a published lemma where one exists, and
a new public `abbrev` still lands with its `_iff` or `_eq` lemma.
They read the machine model's primitives (`MultiTapeTM.step`, `runFrom`, `Action.apply`,
`Cfg.mapState`) through the existing lemmas. The style lint's check 8 reports, per file, every
public `def` with no lemma named after it and no `simps` attribute, so a head-against-base diff
of the lint shows any new definition that lacks one. Definitions that predate the rule are listed
by the same check and covered as consumers need them.

**Construction reuse.** Machines are built from the verified construction layers, not from
scratch: the combinators and routine catalog of `TCSlib/Complexity/TuringMachine/Build/`
(conventions, wrappers, loops, primitives, embeddings, seams, and the catalog rows —
`machine-library-design.md` is the registry), the registered hosts (**Hosts come first**,
below), and the program layers (`LogProg.ARM`, `CounterProg`, and the general programming
layer of `machine-library-design.md` §15 once it lands) where a program-level description
suffices. Before writing a transition
table by hand, check the registry; a routine that exists is cited, not re-derived. A routine
that *almost* exists is the interesting case: do not write a third private variant — either
consume the general form, or commission the missing form into the shared layer (during a
fill batch: a `private` local copy plus a "requested shared lemma" in the report, promoted
at the next shared-file window). A hand-built machine is acceptable only when no layer
covers the need, and its docstring must say so and name what was missing — that sentence is
what turns the gap into the next catalog row. The chapter-1/2 files that predate this layer
re-derived the same bank/relocation/dispatch/frame families four times over (`emitterBank*`,
`clBank*`, `clSlot*`, …); the retrofit paying that debt back is the standing cautionary
tale. The same discipline applies to circuit construction once `CircuitComplexity`'s gadget
layer exists: gadgets, wiring combinators, and size/depth ledgers get one shared home and a
registry, and new circuits are assembled from it.

**Hosts come first.** A *host* is a control structure that drives other routines rather than
computing one value: a search or traversal (BFS, DFS, backtracking, an odometer over
assignments), a recursion or evaluation scheme (AND/OR evaluation, Savitch's midpoint
recursion), an interpreter or simulation step block, a clocked or windowed runner, a dispatcher
over a data structure (tables, records), or an input device. Any routine whose natural contract
does not depend on its first consumer counts as a host; leaf rows (copy, compare, seek,
arithmetic) do not. **A host is never built `private` inside the proof that first needs it.**
Its public contract is designed, statement-gated and placed in the shared construction layer
first, generic in the parts its consumers vary (the leaf test, the step relation, the data
domain), with time and space (head-envelope) clauses. Consumers cite it, under the campaign's
proved-modulo rule while its own fill is still running. The host registry is
`machine-library-design.md` §14. A private host already in the tree is harvested into the
shared layer before a second consumer is briefed against it. The rule exists because private
hosts were the main way the library overfitted to single proofs: four configuration encodings,
three reachability notions and a private search host per theorem, each to be re-derived by the
next consumer (assessment of 2026-10-12, recorded in the design document). (User, binding,
2026-10-12.)

**Duplication.** Some duplication is mechanically forced by the campaign discipline —
exclusive file ownership, the statement freeze, and `private` visibility leave a fill batch
no other legal way to use another file's unexported machinery — and occasionally it is the
right engineering call. It is never silently acceptable: **every instance of duplicated
proved material must be human-approved.** A fill batch discloses each copy in its report;
the maintainer's integration ledger totals copied material per file (`workflow.md` §4); and
the audit template treats accumulated duplication as a major finding that a gate cannot
close over without the human maintainer explicitly accepting the debt and naming where and
when it is paid back (the registry's dedup/refactor queue). Duplication that was never
disclosed is a freeze violation, not debt.

**File header.** Every math file begins with the Mathlib-style copyright block, its imports,
the repo-standard options

```
set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false
```

then a module docstring containing `# Title`, `## Main definitions`, `## Main results`, and
`## References` (see §2).

## 2. Attribution

Every mathematical statement in the library must be traceable to a source, at the level of
precision of a textbook theorem number or a paper section.

**File-level.** Every math file's module docstring contains a `## References` section giving
full citations with short tags, e.g.

```
## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009.
```

**Declaration-level.** Every definition, theorem, and lemma that corresponds to a result in
a source carries the tag with a precise location in its docstring: `[AB09, Claim 1.6]`,
`[AB09, §1.7]`, `[GRS25, Thm 4.2.1]`. Purely technical glue lemmas with no textbook
counterpart may omit the tag; anything a reader would recognize as "a result" may not.

**Deviations.** If the formal statement deviates from the source — different constants,
strengthened or weakened hypotheses, a reformulation — the docstring must say so and briefly
say why (e.g. "stated with explicit constant 5k rather than O(·), following the proof").

**Statement prose.** Every public declaration's docstring begins with a natural-language
statement of what it asserts (for a definition: what it is), precise enough that a reader
could judge the formalization's fidelity without parsing the Lean. The `[Tag, location]`
citation and any deviation note attach to that statement; the proof sketch (§3) follows it.
A bare label ("Unfolding lemma", "Helper for X") is not a statement. Instances are exempt,
as are vendored files (which follow upstream style). `private` declarations should carry
docstrings too, but at reviewer discretion rather than as a hard requirement. The blueprint
remains the cross-referenced informal layer for dependency structure (see **Blueprint**);
the docstring statement is what external audits compare blind restatements against, so it
is part of the trusted surface.

**Blueprint.** When an ingested reference exists under `blueprint/src/references/`, blueprint
entries use `\statementsource{<ref>}{<anchor>}` and `\proofsource{<ref>}{<anchor>}` to cite
it, subject to the existing rule that these are written only after an approved proofmatch
run. When starting a new chapter or paper, ingest it as a reference pair
(`<name>.raw.md` + `<name>.md`) so these citations are possible: put the PDF under
`blueprint/src/references/` in the change that formalizes it and run
`python3 scripts/dataset_pipeline.py --yes`, which ingests it, matches every text the
blueprint does not cite yet, and carries the new statements into the dataset
(`python3 scripts/sources.py add TAG=<pdf or md>` does the ingest and match alone, with
the docstring tag above; `python3 scripts/sources.py` shows which texts are attached and
which are still missing; see `dataset/INSTRUCTIONS.md`). The dataset builder does not
search outside that directory for sources; an unattached text leaves the theorems with
informalized proof notes instead of citations.

**Vendored code.** Lean code adapted from another project keeps the original copyright
header and license notice, and its file docstring names the source project, the commit it
was taken from, and a summary of local modifications.

**Design adaptation.** When a construction, proof architecture, or module design is
adapted from — or materially inspired by — another project's code, the debt is cited even
when no code is transcribed. The module docstring's `## References` section names the
source project, author, module or archive entry, the commit or version consulted, and its
license, with a short tag usable at declaration level; the precedent is
`TuringMachine/Composition.lean`'s `[Balbach22]` for the Isabelle AFP `Cook_Levin`
composition-combinator architecture. Design documents and blueprint entries built on the
adapted design carry the same citation. Examining external code purely for comparison,
with nothing taken, creates no citation duty, but on a campaign it belongs in the
campaign's records (plan decision log or backlog) so the provenance question is answerable
later. (Maintainer guideline, binding, 2026-10-06.)

## 3. Proof sketches

Every nontrivial formal proof is accompanied by a human-readable English proof sketch, kept
next to the Lean it describes.

**What counts as nontrivial.** Rule of thumb: any proof longer than ~20 lines of tactics, or
that would rate difficulty ≥ 3 on the blueprint scale. One-line `simp`/`omega`/`exact`
proofs need no sketch.

**Where sketches live.** In the Lean file itself:

- For most theorems: a `**Proof sketch.**` paragraph at the end of the theorem's docstring,
  written in mathematical English (not Lean identifiers), naming the key intermediate steps.
- For long proofs: additionally, short comments at the major `have`/section boundaries tying
  the tactics back to the sketch's steps.

The named intermediate steps of a sketch should be visible in the formalization as `have`s
or standalone lemmas — if the sketch says "first reduce to the one-tape case", there should
be a lemma that is that reduction.

**Where sketches do not live.** Not in the blueprint. Blueprint statement entries state
claims only; `scripts/dataset_hygiene.py --strict` hard-fails on proof content there. The
blueprint records *what* is true and its dependency structure; the Lean docstrings record
*why* it is true.

**Sketches and the sorry ladder.** When landing a sorry-skeleton, write the sketch at
skeleton time — the sketch *is* the plan, and each `sorry` should correspond to a named step
of it. A skeleton whose sketch cannot be written is not ready to land.

**Synchronization.** When a proof strategy changes, the sketch changes in the same commit.
A sketch that describes a proof the code no longer performs is worse than no sketch.

## Review checklist

Before merging new Lean content, check:

1. Files follow the Area/Topic layout with a facade, and `TCSlib.lean` exports are updated.
2. Imports are precise; no bare `import Mathlib`.
3. Every file has a `## References` section; every source-derived declaration has a
   `[Tag, location]` in its docstring; deviations from sources are noted.
4. Every nontrivial proof (or sorry-stub standing in for one) has a proof sketch.
5. Every public declaration (instances and vendored files excepted) has a docstring
   opening with a natural-language statement of what it asserts
   (`python3 scripts/style_lint.py` checks presence mechanically; statement quality is
   review judgment).
6. `zsh scripts/lean_check.sh <file>` reports zero errors for each touched file.
7. If blueprint content was touched: `python3 scripts/blueprint_validate.py --strict` and
   `python3 scripts/dataset_hygiene.py --strict` pass.
8. No new private host: every search, recursion, interpreter, runner or input device the
   change introduces is a registered public host, or cites one (§1, **Hosts come first**).

## ===== PairingCryptographyPlan.md =====

# Pairing-based cryptography

## Scope and ownership

Seyoon approved this campaign on 2026-11-16 (decision log, first row):

1. **Abstract bilinear groups.** A symmetric bilinear group generator in the existing asymptotic
   and NUPPT framework, with the BDH and Decision BDH (DBDH) assumptions. No concrete curves.
2. **Joux's one-round tripartite Diffie–Hellman** [Jou00]: the protocol, its correctness (the
   three parties derive the same key) and its key indistinguishability under DBDH.
3. **Boneh–Boyen selective-ID IBE (BB1)** [BB04], standard model: IND-sID-CPA security, the
   scheme, its correctness, and security from DBDH.

**Out of scope:** Boneh–Franklin IBE (it needs a random-oracle layer), asymmetric (Type-3)
pairings, concrete groups. BB04's BDHI-based system (BB2, §5), its HIBE at depth > 1, its CCA2
transforms (§4.3, §6) and its full-security transform (§7) are not targets.

**Location (Seyoon, 2026-11-16).** The bilinear-group substrate is `TCSlib/Cryptography/Pairing/`
and Joux is `TCSlib/Cryptography/KeyExchange/`. IBE (interface, IND-sID-CPA game, Boneh–Boyen)
is `TCSlib/Cryptography/AdvancedEncryption/IdentityBased/`, namespace
`TCSlib.Cryptography.AdvancedEncryption.IdentityBased`, behind the facades
`AdvancedEncryption.lean` and `AdvancedEncryption/IdentityBased.lean`. `AdvancedEncryption.lean`
is shared with GSW (`AdvancedEncryption/Homomorphic/`): the draft's facade imports only
`IdentityBased`, and **whichever statement PR lands second adds its child import** to it.

**Home and binding rules.** Records (this file, `briefs/pairings/`) live on the records branch
`cryptography/pass-shelat-ch2-4` and are pushed by the maintainer. Lean reaches that branch only
by PR, opened by the maintainer and merged by Seyoon. Binding: `policy.md` (modularity,
attribution, proof sketches, Rule 10, hosts first), `briefs/pass-shelat-ch5-8/CLAUDE.md` and
`MAINTAINER-HANDOFF.md` §2. Standing worker ruling (2026-11-11): Codex for audits and reviews,
Claude for fills and other external jobs.

| Item | Identity |
|---|---|
| Statement branch (local, not pushed) | `stmt/pairings` |
| Statement worktree | `$SP/wt-stmt-pairings` (sparse, `briefs/` excluded; `.lake/packages` symlinked) |
| Branch base (`origin/cryptography/pass-shelat-ch2-4` when cut) | `e7a9f70f5c1f11c2670f427ef813f2a6d8c53543` |
| Statement commit (modules) | `b02e6ce4a3dcc7c945825d1f1d3b636c5e377a01` |
| Statement head (root exports) | `ce9c3728ec582be45fc33ca68d64b5533701093d`, tree `327612ee0b6689bf371a40e28edaad984226d78e` |
| Records tip checked at commit time | `44e2dc2bd68b3a81eaeebe7acd61fca1fe857917` (records only since the base: no `TCSlib/`, root, lakefile or manifest change) |
| Lean / Mathlib | `leanprover/lean4:v4.25.0` / the pinned manifest |

`$SP` = `/tmp/claude-0/-home-user-tcslib/d0667d12-db8d-5853-b0f7-9833dc0884c6/scratchpad`.

## Sources

| Tag | Reference | Version used | SHA-256 | Committed? |
|---|---|---|---|---|
| Jou00 | A. Joux, *A One Round Protocol for Tripartite Diffie–Hellman*, ANTS-IV, W. Bosma (ed.), LNCS 1838, pp. 385–393, Springer, 2000 | Publisher copy, 9 pp. (Seyoon's upload) | `dd423b93a7e2dbeb87e6210b26f4c3ec022c3d0681a0ce72262b1d45c53f6df9` | No (publisher copy; PSV06/PSV07 precedent) |
| BB04 | D. Boneh, X. Boyen, *Efficient Selective-ID Secure Identity Based Encryption Without Random Oracles*, Cryptology ePrint Archive, Report 2004/172, full version dated December 2004; extended abstract in EUROCRYPT 2004, LNCS 3027, pp. 223–238 | ePrint full version, 20 pp.; **its numbering is used throughout** | `63c1c7b0817f36d6e558107bf281e22d2c454f821fadd533ced653e81a6a35de` | No (ePrint copy; same precedent) |
| PS10 | R. Pass, a. shelat, *A Course in Cryptography*, 3rd ed., 2010 | `Pass–Shelat.pdf` on this branch | `7624556077a7a272ba0b3ddb7cd47b96574fb0b4b4947a25467d1f91bb61bda8` | Yes (existing) |

Both PDFs were read with `pdftotext -layout` (text treated as data). **PDF needed:** both are in
hand; nothing further is needed for the statement phase. **Policy §2 ingest** (reference pair
under `blueprint/src/references/`, `scripts/sources.py add`) is **open**: the PDFs themselves must
not be committed, so the ingest needs a ruling on what is committed instead (Q12).

Anchors used in the Lean (BB04 ePrint pages): §2.1 pp. 2–4 (IBE algorithms; the selective-identity
game; Definitions 2.1, 2.2), §2.2 p. 4 (bilinear groups), §3.1 pp. 4–5 (BDH, Decision BDH,
Definition 3.1), §4.1 pp. 5–6 (the HIBE construction; BB1 is depth 1), §4.2 pp. 6–8 (Theorem 4.1
and its proof), §4.4 p. 8 (arbitrary identities, "`2^b < p` is sufficient"). Jou00: §2 pp. 386–387
(pairings bilinear and non-degenerate), §3 pp. 387–388 (the protocol, `F_W`, `F_T`), §5 pp. 391–392
(security issues).

### Where the papers' formulations differ from the draft

1. **[Jou00] has no security theorem.** §5 says only that "some Diffie–Hellman like problem and
   Diffie–Hellman like decision problem should be hard in order to get security". The draft's
   `jouxKeyIndist_of_dbdhAssumption` is the maintainer's formal version, with Decision BDH taken
   from [BB04, §3.1] (which credits the BDH problem to [Jou00, SOK00, BF01]).
2. **[Jou00]'s protocol uses two points.** With the Weil pairing on one point `e_n(P, P) = 1`, so
   §3 moves to two independent points `P, Q` and the Tate pairing `F_T`. In a symmetric bilinear
   group as defined in [BB04, §2.2], non-degeneracy is `e(g, g) ≠ 1`, so the paper's first formula
   `F_W(x, P, Q) = e(P, Q)^x` works with one point. The draft formalizes that single-point form.
3. **[Jou00] fixes "some point `P`"**; the draft draws the public generator uniformly from `G^*`,
   the distribution under which [BB04, §3.1] states Decision BDH.
4. **[BB04, §4.1] is an HIBE**; BB1 is its depth-1 case ("an IBE system is an HIBE where all
   identities are at depth 1", §2.1). Identities are elements of `Z_p` there; arbitrary identities
   are hashed (§4.4). The draft uses `ℓ(κ)`-bit identities read as their binary value in `Z_p`,
   which is §4.4's sufficient condition (`H : {0,1}^* → {1, …, 2^b}`, `2^b < p`) with `H` the
   identity on `ℓ`-bit strings, under the hypothesis that `p ≥ 2^ℓ` except with negligible
   probability.
5. **[BB04] is concrete** (`(t, ε)` assumptions in a fixed group; Theorem 4.1's
   `t' < t − Θ(τ ℓ q_S)`). The draft is asymptotic, relative to a PPT generator, against
   non-uniform PPT machines.
6. **Advantage.** [BB04, §2.1] measures `|Pr[b = b'] − 1/2|`; the draft uses the two-experiment
   advantage, twice that, as `FixedLengthPKScheme.INDSecure` does. The decision advantage of
   [BB04, §3.1] is written without an absolute value; the draft takes it.
7. **Forbidden queries.** [BB04, §2.1] restricts the adversary (`ID_i ≠ ID*`, `M_0, M_1 ∈ M`);
   the draft's challenger answers such queries with `⊥`.
8. **The proof of Theorem 4.1** has `B` draw the challenge bit and output `[b = b']`; the draft
   fixes the bit and uses one distinguisher per bit, so the bound is a sum of two DBDH advantages.
9. **DBDH ⇒ BDH** is not stated in either source (folklore; Q10).

## Design decisions (and the precedent each mirrors)

### D1. Abstract bundle, generator as a PPT with a total group map

`Pairing.BilinearGroup wG wT` bundles finite commutative groups `G`, `GT` of the same prime order,
a generator `gen ≠ 1`, the pairing as `G →* G →* GT` (bimultiplicative; BB04's
`e(u^a, v^b) = e(u, v)^{ab}` is the proved `bilinear_pow`), non-degeneracy `e(gen, gen) ≠ 1`, and
injective fixed-width encodings `encG`, `encT`. `Pairing.BilinearGen` is a uniform `NUPPT`
`Gen(1^κ)` with exact description length `descLen(κ)`, element widths `wG`, `wT : PolyExpr`, and a
total map `group κ d` from descriptions to bundles.

*Precedent:* `Candidates.ExpGroupGen`/`SafePrimeGen` (an instance generator PPT; adversaries
receive the instance). *Difference:* no validity predicate or threshold `n₀`: every string
describes a group, so no fallback instance (`dlDefaultIndex`) is needed. The large-order condition
is `OrderAtLeastExcept N δ` (probability over the generator's coins), mirroring
`ExpGroupGen.FullLengthExcept` and its run-3 audit P8-2 lesson.

### D2. Experiments as games, sampled in sequence

All experiments are `Games.ProbComp Bool`: generator coins, then `g ∈ G^*`, exponents and `T`
from the group just drawn, then the adversary's coins; advantages are `Games.advantage`.
Exponents are ideal uniform in `Z_p`. *Precedent:* the run-3 audit P8-1 repair of the DDH
ensembles (a uniform seed over a dependent sum distorts the instance law); `dlProb`'s ideal
exponent; LWE's ideal experiments. Sequential sampling avoids P8-1 without coin blocks.

### D3. Adversary input format

A DBDH distinguisher gets `1^κ` and `⟨d, ⟨g, ⟨g^a, ⟨g^b, ⟨g^c, T⟩⟩⟩⟩⟩` (`tupleStr`); a BDH
solver gets the same without `T` (`bdhStr`) and wins iff its output is the encoding of
`e(g, g)^{abc}`. Joux's eavesdropper gets the transcript in the same format, so the Joux
experiments *are* DBDH experiments (`jouxGame_eq_dbdhGame`, proved). *Precedent:* `ddhTuple`'s
nested pairs; `distinguisherL`; `DLWEAssumption`'s "every `NUPPT` has negligible advantage".

### D4. Efficiency as a separate contract

"Efficiently computable" [BB04, §2.2] is `BilinearGen.Ops` (`Pairing/Operations.lean`):
polynomial-time string functions for the order, `G` multiplication and exponentiation by a
numeral, the pairing, `G_T` multiplication and `G_T` membership, specified on generated
descriptions, with numerals read by `NumberTheory.listToNat`. It is a hypothesis only of BB1's
security (whose reduction computes in the group), together with `Candidates.ArithmeticFP` (D11).
*Precedent:* `ArithmeticFP` as a hypothesis bundle; LWE's "`Family` asserts no efficient sampler".

### D5. IBE interface: typed probabilistic algorithms

`IdentityBased.IBEScheme` has, per `κ`, types `PP`, `MSK`, `SK`, `CT`; `setup`, `keyGen`, `enc`
as `ProbComp`s, `dec` deterministic with `⊥`; `idLen`- and `msgLen`-bit identities and messages;
a parameter-dependent message space `MsgSpace` (BB04's `M`); fixed-width encodings for the
adversary. Correctness is `AllOutputs` of an honest run. *Precedent:* the four-algorithm shape of
`PublicKeyScheme` and `GroupPKScheme` (key-dependent message space, El Gamal). *Difference:* the
algorithms are typed `ProbComp`s, not `NUPPT`s, and carry no efficiency field (Q5): with groups
drawn per description, an `NUPPT` interface would require proving BB1's machines PPT in a
definition (no `sorry` in definitions).

### D6. The IND-sID-CPA game: one machine, `Init` as an oracle

As in `FixedLengthPKScheme.indGame`: one `NUPPT` against bit-string oracles (`bitCodec`), budget
`q`, verdict bit. Oracles: `Init` (0; first query fixes `ID*`, answers `params`), `KeyGen` (1;
`⊥` before `Init` or for `ID*`, fresh coins per query), `Challenge` (2; `⊥` before `Init` or on
messages outside `M`; first valid query encrypts `M_b` for `ID*` and is recorded; later queries
repeat it). The machine starts with `1^κ` only, so it learns nothing about `params` before
committing; `Setup` is sampled before the run but revealed only at `Init`, which is [BB04, §2.1]'s
order in distribution. `SIDSecure` copies `INDSecure`'s quantifier shape. `oracleImpl` builds the
three oracles from typed handlers so that simulators in other files never read `inLens`/`outLens`
through their bodies (Rule 10).

### D7. BB1 over the generator

`bb1Scheme G ℓ` tags parameters, keys and ciphertexts with the description (`Σ d, …`); `dec` is
`⊥` on mismatched descriptions. Over one group, `BB1.setup/keyGen/encrypt/decrypt` follow
[BB04, §4.1] at depth 1, including the order of `Setup`'s samples (`g`, `α`, `h`, `g_2`) and a
random generator `g ∈ G^*`. Messages are `G_T` encodings (`decodeT` reads `1` off the message
space; never exercised, the game refuses).

### D8. The security proof as named steps

The paper's simulator `B` is defined beside the scheme as typed handlers (`bb1SimInit`,
`bb1SimKeyQ`, `bb1SimChal`, `bb1SimImpl`, `bb1SimGame`) with ideal exponents. The headline
`bb1_sidSecure` is **proved** by the triangle inequality from three sorried steps: perfect
simulation on `P_BDH` up to identity collisions (`bb1_sim_real`), bit-independence on `R_BDH`
(`bb1_sim_random`), and the machine step (`exists_bb1_distinguisher`). *Precedent:* Gate 12's
`exists_adaptive_cpa` proved from sorried statements.

## Module layout (statement draft)

| Module | Lines | Content |
|---|---|---|
| `Pairing/Group.lean` | 299 | `BilinearGroup`, `BilinearGen`, `desc`, `inst`, `OrderAtLeastExcept`; group facts |
| `Pairing/Assumptions.lean` | 221 | `tupleStr`, `bdhStr`, `dbdhGame`, `dbdhAdv`, `DBDHAssumption`, `bdhGame`, `BDHAssumption`; T1 |
| `Pairing/Operations.lean` | 117 | `BilinearGen.Ops` |
| `Pairing.lean` (facade) | 31 | |
| `KeyExchange/Joux.lean` | 193 | protocol, correctness, key indistinguishability (all proved) |
| `KeyExchange.lean` (facade) | 23 | |
| `AdvancedEncryption/IdentityBased/Defs.lean` | 408 | `IBEScheme`, `Correct`, IND-sID-CPA game, `oracleImpl` |
| `AdvancedEncryption/IdentityBased/BonehBoyen.lean` | 553 | BB1, `bb1Scheme`, correctness (proved), the simulator |
| `AdvancedEncryption/IdentityBased/BonehBoyenMachine.lean` | 78 | T4 (Q11: its own module) |
| `AdvancedEncryption/IdentityBased/BonehBoyenSecurity.lean` | 170 | T2, T3 and `bb1_sidSecure` |
| `AdvancedEncryption/IdentityBased.lean`, `AdvancedEncryption.lean` (facades) | 32, 25 | |
| `TCSlib.lean` | +3 imports | separate commit |

Every file is under 1000 lines and no line exceeds 100 characters. Layout deviation from the
initial proposal: `Operations.lean` (keeps `Group.lean` free of the arithmetic layer's imports)
and `BonehBoyenSecurity.lean` (definitions separate from the heavyweight theorem file, policy §1);
`BonehBoyenMachine.lean` (T4 alone, so that its fill unit owns its own file; ruling Q11).

## Statements

Proof sizes are estimates for the remaining targets.

| Statement | Source | Status | Est. size |
|---|---|---|---|
| `BilinearGroup.bilinear_pow`, `pair_pow_left`, `pair_pow_right` | BB04 §2.2 item 1 | proved | — |
| `BilinearGroup.pair_comm` | BB04 §2.2, remark after item 2 | proved | — |
| `BilinearGroup.exists_pow_eq`, `pow_order(_GT)`, `pow_val_mul(_GT)` | group facts | proved | — |
| `BilinearGroup.pair_ne_one` (`e(x, x) ≠ 1` on `G^*`) | BB04 §2.2 item 2 | proved | — |
| `BilinearGroup.pow_val_bijective` (`a ↦ e(x, x)^a` bijective) | BB04 §3.1 ("`T` uniform") | proved | — |
| **T1** `BilinearGen.bdhAssumption_of_dbdhAssumption` | folklore (Q10) | **sorry** | 150–300 |
| `jouxKey_eq`, `joux_correct` | Jou00 p. 388 | proved | — |
| `jouxGame_eq_dbdhGame`, `jouxKeyIndist_of_dbdhAssumption` | Jou00 §5 + BB04 §3.1 | proved | — |
| `IBEScheme.sidImpl_*` (9), `oracleImpl_*` (3), readers | BB04 §2.1 | proved | — |
| `BB1.decrypt_encrypt` | BB04 §4.1 ("for a valid ciphertext") | proved | — |
| `BB1.decodeT_encT` | — | proved | — |
| `bb1_correct` | BB04 §4.1 | proved | — |
| `bb1Sim*` case lemmas (9) | BB04 §4.2 proof | proved | — |
| **T2** `bb1_sim_real` | BB04 §4.2, proof of Thm 4.1 (P_BDH case) | **sorry** | 400–800 |
| **T3** `bb1_sim_random` | BB04 §4.2, proof of Thm 4.1 (R_BDH case) | **sorry** | 150–350 |
| **T4** `exists_bb1_distinguisher` | BB04 §4.2 (B is efficient) | **sorry** | 700–1400 |
| `bb1_sidSecure` | BB04 Theorem 4.1 at depth 1 | proved from T2–T4 | — |

Definitions (all complete, each with a reader): `BilinearGroup`, `BilinearGen`, `desc`, `inst`,
`OrderAtLeastExcept`, `tupleStr`, `bdhStr`, `dbdhGame`, `dbdhAdv`, `DBDHAssumption`, `bdhGame`,
`BDHAssumption`, `Ops`, `jouxMsg`, `jouxKey`, `jouxGame`, `jouxAdv`, `JouxKeyIndist`, `IBEScheme`,
`honestRun`, `Correct`, `inLens`, `outLens`, `sidSpec`, `SidState`, `sidImpl`, `oracleImpl`,
`sidCodec`, `sidGame`, `SIDSecure`, `BB1.{Params,Key,Ciphertext,F,setup,keyGen,encrypt,decrypt,
idToZ,decodeT}`, `bb1Scheme` (simps field equations, non-simp), `BB1SimState`, `bb1SimParams`,
`bb1SimKey`, `bb1SimInit`, `bb1SimKeyQ`, `bb1SimCt`, `bb1SimChal`, `bb1SimImpl`, `bb1SimGame`.
Instances: `BilinearGroup.factPrime`, `neZeroOrder`, `nonempty_ne_one` and the bundle's field
instances. No `@[simp]`. Abbrevs: `sidSpec`, `SidState`, `BB1SimState` (each with `_eq`).

Every target carries a `**Proof sketch.**` following the paper. The draft also *proves* the Joux
results and BB1 correctness; the statement gate audits those proofs too.

## Unit split for fills

Each unit owns its target's file; helper modules are allowed beside it.

| Unit | Targets | Files | Notes |
|---|---|---|---|
| `pair-bdh` | T1 | `Pairing/Assumptions.lean` | machine composition (`NUPPT` re-pairing and a string-equality test), a `1/p` bound and `OrderAtLeastExcept` |
| `bb1-sim` | T2, T3 | `IdentityBased/BonehBoyenSecurity.lean` | typed coupling of two `simulate` runs (state relation), re-randomization of `h` and `r`, lazy sampling of `T` (`Games.Hopping` eager/lazy lemmas) |
| `bb1-machine` | T4 | `IdentityBased/BonehBoyenMachine.lean` | handler theorem T1 (`Games.exists_handlerMachine`), `Ops`, `ArithmeticFP`, exponent sampling with `Candidates.sampleBelowL` and `statClose_sampleBelowL` |

T2/T3 and T4 are independent statements. T4 is in its own module (Q11, applied on
`stmt/pairings`), so `bb1-sim` and `bb1-machine` own disjoint files and can run in parallel;
`BonehBoyenSecurity` imports `BonehBoyenMachine` for `bb1_sidSecure` (proved-modulo rule).

## Modelling choices for the statement gate

1. The pairing is the field `pair : G →* G →* GT` of a bundle; bilinearity and non-degeneracy
   are fields (non-degeneracy at the bundle's `gen`; `pair_ne_one` extends it to `G^*`).
2. Groups are drawn by a uniform `NUPPT` generator; the group is a total function of the
   description; descriptions have exact polynomial length.
3. Elements are fixed-width injective encodings; decoding of adversary strings is
   `Function.partialInv` (`decodeT`), with membership as the message-space predicate.
4. The generator `g` is uniform in `G^*` in DBDH, BDH, Joux and BB1's `Setup`.
5. Exponents are `ZMod p` and act by `x ^ a.val`; `T` in `R_BDH` and Joux's random key are uniform
   in `G_T`.
6. Large order is `OrderAtLeastExcept N δ` with negligible `δ` (DBDH ⇒ BDH: `N = 2^κ`; BB1:
   `N = 2^ℓ`).
7. Efficiency of group operations is the separate contract `Ops`; honest IBE algorithms carry no
   efficiency requirement.
8. Identities are `ℓ(κ)`-bit strings, embedded in `Z_p` by binary value (BB04 §4.4).
9. Messages are `G_T` encodings; the message space is "is an encoding".
10. Selective-ID shape: one machine, `Init` oracle, `Setup` sampled first and revealed at `Init`,
    forbidden queries answered `⊥`, one polynomial budget for all queries.
11. Advantage: two experiments (twice BB04's guess advantage).
12. Parameters, keys and ciphertexts carry the description `d`; `dec` is `⊥` across descriptions.
13. Joux: single-point `F_W` form; security is the maintainer's formalization of Jou00 §5.

## Questions for Seyoon (recommended option first)

- **Q1. Group model.** (A) Abstract bundle drawn by a PPT generator with a total description map
  (current). (B) A fixed group per `κ` (no generator randomness; simpler types, the non-uniform
  reading of BB04's fixed `G`). (C) Abstract bundle with a validity predicate and threshold, as
  `ExpGroupGen`.
- **Q2. The generator `g`.** (A) Uniform in `G^*` everywhere (BB04 §3.1, §4.1; current). (B) The
  bundle's fixed `gen` everywhere (modern "generator outputs `g`" convention).
- **Q3. Joux's protocol.** (A) Single-point `F_W(x, P, Q) = e(P, Q)^x` over the symmetric bundle
  (current). (B) Joux's two-point form `(P_X, Q_X)` with an abstract pairing allowing
  `e(P, P) = 1`.
- **Q4. Joux's security.** (A) Key indistinguishability under DBDH only (current, proved). (B)
  Also the computational form: the key is hard to compute under BDH. (C) Correctness only.
- **Q5. Efficiency of honest algorithms.** (A) Typed algorithms without an efficiency field; the
  generator's `Ops` only where a reduction needs it; a BB1-is-PPT statement deferred (current).
  (B) Add a string-level `IBEScheme.Efficient` predicate now, with a BB1 efficiency target under
  `Ops` and `ArithmeticFP` (one more unit, machine-heavy). (C) An `NUPPT`-based IBE interface like
  `FixedLengthPKScheme`.
- **Q6. Identities.** (A) `ℓ(κ)`-bit strings by binary value with `p ≥ 2^ℓ` except negligibly
  (BB04 §4.4; current). (B) Identities as elements of `Z_p` in a BB1-specific game. (C) Arbitrary
  identities hashed by a CRH from `Hashing.CollisionResistant`.
- **Q7. Game shape.** (A) One machine with an `Init` oracle (current; mirrors the PK games). (B)
  A two-stage adversary `A₁(1^κ) → (ID*, st)`, `A₂(st, params)` with shared coins.
- **Q8. Messages outside `M`.** (A) The challenge is refused (`⊥`; BB04's "`M_0, M_1 ∈ M`";
  current). (B) Canonicalized to `1`, as El Gamal's `egCanon`.
- **Q9. Advantage.** (A) Two-experiment form, as `INDSecure` (current). (B) Guess-the-bit form
  (`Games.guessAdv`), BB04's literal `|Pr[b = b'] − 1/2|`.
- **Q10. DBDH ⇒ BDH.** (A) Keep T1 as a target, flagged "not in the sources" (current). (B) Drop
  it; BDH stays a definition with its reader.
- **Q11. Fill units.** (A) Three units `pair-bdh`, `bb1-sim`, `bb1-machine`, moving T4 to its own
  module (`IdentityBased/BonehBoyenReduction.lean`) at the statement PR so the two BB1 units run
  in parallel. (B) The same three units, with `bb1-machine` after `bb1-sim` on one file. (C) One
  BB1 unit for T2–T4.
- **Q12. Source ingest (policy §2).** (A) Keep the PDFs uncommitted; ingest later from Markdown
  transcriptions of the consumed passages only (BB04 §2.1–§4.4, Jou00 §3 and §5), as the LWE
  campaign's scoped review. (B) Commit full Markdown transcriptions now. (C) No ingest; the
  docstring tags suffice for this campaign.
- **Q13. Efficiency contract `Ops`.** (A) As drafted: order, `mulG`, `powG`, `pairStr`, `mulT`,
  `memT`, numerals by `listToNat`, specified at generated descriptions. (B) Only what BB1's
  reduction uses (drop `pairStr`). (C) Add `invG`, `powT`, `memG` for future consumers.

## Risks

- **T4 is the largest job**: a polynomial-time handler with group operations through `Ops`,
  modular arithmetic through `ArithmeticFP` (inverse of `ID − ID*`), exponent sampling from coin
  blocks with a statistical hybrid over `q + 1` samples, and T1's state and length bounds.
- **T2 needs a relational simulation argument** (two `simulate` runs with different states and
  re-randomized coins). If `Games.Hopping` lacks a state-relation coupling lemma, the fill should
  request it as a shared lemma rather than proving a private one (policy §1, duplication).
- **Dependent types.** Groups depend on the description; consumers outside `BonehBoyen.lean` must
  move between `(bb1Scheme G ℓ).sidSpec κ` and typed handlers through `oracleImpl_*` and cast
  readers; fills may need `_onSpec` reader variants (as in `OracleSecurity`).
- **Typed honest algorithms** (Q5) may draw an audit finding if the gate expects PPT schemes.
- **Order hypotheses** (`OrderAtLeastExcept`) are assumptions about the generator; whether a given
  generator satisfies them is not formalized (as for `FullLengthExcept`).
- **Root not elaborated.** The three facades and every new module are checked; the library root
  `TCSlib` is not (it needs the whole library on the tree).
- **Shared facade.** `AdvancedEncryption.lean` will conflict with the GSW statement PR on one
  import line; the second PR to land adds its child.

## Verification (statement draft)

Evidence: `briefs/pairings/statement-phase/evidence/` (summary in `EVIDENCE.md` there).

- **Tree.** `$SP/dl-oleans-2` only. Snapshot before: 1230 files, SHA-256
  `457ba704d26757307f14131aa534929ffd70d30a732b0c744b104ca3fc96a15f` (the required value).
- **Base delta.** The tree holds the `eff2dcd0` sources. In the new modules' import closure (73
  modules at the base `e7a9f70f`), only `Foundations/BitLists` changed since (13 added lines). It
  and its 7 downstream closure modules (`Asymptotic/Adversary`, `Games/BitCodec`,
  `Encryption/PrivateKey/{Scheme,OracleSecurity}`, `Asymptotic/CollectionsHelpers`,
  `NumberTheory/Primality`, `Candidates/Arithmetic`) were backed up (hashes equal to the
  snapshot) and rebuilt at the base source: 8/8 rc 0.
- **Checks.** `scripts/lean_check_tree.sh`, one process at a time, final sweep of all 11 new
  modules in order: 11/11 rc 0, 0 errors, warnings only the 4 target `sorry`s (`Assumptions` 1,
  `BonehBoyenSecurity` 3).
- **Axioms** (`#eval` over every constant of the 11 modules, `Lean.collectAxioms`): 320
  declarations and 52 auxiliary constants; every one uses only `propext`, `Quot.sound`,
  `Classical.choice`, except the 4 targets and `bb1_sidSecure` (proved from 3 of them), which add
  `sorryAx`.
- **Rule 10.** Seven whole-file seal probes (`attribute [local irreducible]` on 2–51 foreign
  TCSlib definitions per module; names outside a module's closure are reported "unknown" and
  cannot be read; they are the only diagnostics in three probes): 7/7 with 0 other errors.
  Earlier runs found four reads (`intro` through `Correct` and through `SIDSecure`, and
  `DBDHAssumption` applied as a function in `Joux` and in `BonehBoyenSecurity`), now through
  `correct_iff`, `sidSecure_iff` and `dbdhAssumption_iff`. Controls: sealed `intro` through `Correct` fails;
  the same through `correct_iff` passes.
- **Style.** `scripts/style_lint.py`: 0 findings in 11 files. `campaign_style_lint.py --check8b`:
  0 FAIL, 2 WARN, both the check-8 acronym heuristic (`DBDHAssumption`, `BDHAssumption`,
  `SIDSecure` have readers `dbdhAssumption_iff`, `bdhAssumption_iff`, `sidSecure_iff`; the LWE
  precedent of `dlweAssumption_iff`).
- **Restore.** 8 backups copied back (0 hash failures), 15 new oleans deleted, 4 emptied
  directories pruned; snapshot after: 1230 files, `457ba704…a15f`, byte-identical (SNAPSHOT
  EQUAL).

- **Round 2 (Q11 split, 2026-11-16).** `stmt/pairings` rebased onto `523d80d2` (records only
  since `e7a9f70f`; range-diff identical, Lean sources unchanged) and T4 moved, byte-identical,
  to `BonehBoyenMachine.lean`. 12 modules: 12/12 rc 0, 0 errors, 4 target `sorry`s
  (`Assumptions` 1, `BonehBoyenMachine` 1, `BonehBoyenSecurity` 2). Axioms: 320 declarations and
  52 auxiliary constants, standard only except `sorryAx` in the 4 targets and `bb1_sidSecure`.
  Rule 10: the round-1 seal probes for the two changed modules pass (controls as before), and
  whole-file seals A/B, strict and coe, of `BonehBoyenMachine`, `BonehBoyenSecurity` and the
  `IdentityBased` facade pass 12/12 (`-DmaxErrors=0`). Lint unchanged (0 findings; 0 FAIL,
  2 WARN). Root `TCSlib` builds: 278 modules rebuilt from source on the tree (the closure's
  changed and missing modules and their downstream), 278/278 rc 0, root included. Evidence:
  `briefs/pairings/statement-phase/EVIDENCE.md`, round 2.

## Decision log

| Date | Decision / evidence | Status |
|---|---|---|
| 2026-11-16 | **Ruling (Seyoon): pairing campaign approved.** Abstract symmetric bilinear groups in the asymptotic/NUPPT framework with BDH and DBDH; Joux tripartite DH (protocol, correctness, key indistinguishability under DBDH); Boneh–Boyen BB1 selective-ID IBE in the standard model (IND-sID-CPA, scheme, correctness, security from DBDH). Out: Boneh–Franklin (no random-oracle layer), Type-3 pairings, concrete groups. Records on `cryptography/pass-shelat-ch2-4` in this file and `briefs/pairings/`; Lean by PR into that branch. | Approved scope |
| 2026-11-16 | **Sources received (Seyoon; not committed):** Jou00 publisher copy `dd423b93…f6df9`; BB04 ePrint 2004/172 full version `63c1c7b0…35de` (its numbering used). Both read; formulation differences recorded in § Sources. | Record |
| 2026-11-16 | **Ruling (Seyoon): IBE under `AdvancedEncryption/IdentityBased/`** (namespace `TCSlib.Cryptography.AdvancedEncryption.IdentityBased`); `Pairing/` and `KeyExchange/Joux` stay. `AdvancedEncryption.lean` is shared with GSW; the second statement PR adds its child import. Applied in the draft before commit. | Approved layout |
| 2026-11-16 | **Statement draft committed locally** on `stmt/pairings` (base `e7a9f70f5c1f11c2670f427ef813f2a6d8c53543`): modules `b02e6ce4a3dcc7c945825d1f1d3b636c5e377a01`, root exports `ce9c3728ec582be45fc33ca68d64b5533701093d` (both SSH-signed). 11 modules, 4 sorried targets; Joux and BB1 correctness proved; `bb1_sidSecure` proved from T2–T4. Checks, axioms, seals and style as in § Verification. Not pushed. | Ready for the statement PR (maintainer) and Codex statement gate |
| 2026-11-16 | **`dl-oleans-2` restored** to snapshot `457ba704d26757307f14131aa534929ffd70d30a732b0c744b104ca3fc96a15f` (8 backups restored, 15 new oleans deleted; SNAPSHOT EQUAL). | Done |
| 2026-11-16 | Questions Q1–Q13 (§ Questions) await Seyoon's rulings. | Open |
| 2026-11-16 | **Rulings Q1–Q13 (Seyoon): all recommendations accepted.** Q1: abstract bilinear bundle from a uniform PPT generator with a total description map. Q2: `g` uniform in `G*`. Q3: Joux in the single-point `F_W` form. Q4: Joux key indistinguishability under DBDH only. Q5: typed IBE algorithms; a "BB1 is PPT" statement is deferred. Q6: `ℓ`-bit identities read in `Z_p`. Q7: one machine with an `Init` oracle. Q8: out-of-space challenge messages refused with `⊥`. Q9: the two-experiment advantage. Q10: keep T1 (DBDH ⇒ BDH). Q11: three fill units (`pair-bdh`, `bb1-sim`, `bb1-machine`), with T4 moved to its own module before the statement PR. Q12: PDFs uncommitted, with Markdown transcriptions of only the passages used, ingested later. Q13: `Ops` as drafted. Noted: Joux 2000 states no security theorem, so key indistinguishability under DBDH formalises its §5 remark. Draft branch `stmt/pairings` pushed at `ce9c3728`. | Approved |
| 2026-11-16 | **Q11 applied** on the local `stmt/pairings`: rebased onto `523d80d2d4dd8e4ed6799358831e5b3806c6187b` (records only since `e7a9f70f`; range-diff 2/2 identical: `8aa111658bd0509c0fd204d605538ff440f08d02`, `b7ca25477c1685795f2ea45cd895889f7ecaf1c8`) and T4 `exists_bb1_distinguisher` moved byte-identically to `AdvancedEncryption/IdentityBased/BonehBoyenMachine.lean`: head `110c2f9db810d243693b9a5e8976a5ad205f1bab` (SSH-signed). `bb1-sim` owns `BonehBoyenSecurity.lean` (T2, T3), `bb1-machine` owns `BonehBoyenMachine.lean` (T4). 12/12 modules rc 0 with the 4 target `sorry`s; axioms, seals and lint as in § Verification, round 2; root `TCSlib` builds. `dl-oleans-2` restored (SNAPSHOT EQUAL). Not pushed: `origin/stmt/pairings` is still `ce9c3728`. The records branch then advanced to `a32ad0df` (#318, #319, #323 merged); none of their Lean files is in the pairing closure and `stmt/pairings` merges into it cleanly (`git merge-tree`). | Ready for the statement PR (maintainer) |
| 2026-11-16 | **Gate 40 pack** (Codex statement gate, standing ruling): `briefs/pairings/gates/40-pairings-statements/` for draft [PR #331](https://github.com/Shilun-Allan-Li/tcslib/pull/331) at `110c2f9db810d243693b9a5e8976a5ad205f1bab` (base `523d80d2`; 3 commits, 13 files +2153/−0). Statement audit of the definitions under Q1–Q13 (bundle and generator, BDH/DBDH, IBE interface, selective-ID game, BB1, the simulator), truth and sufficiency of T1–T4 (`bb1_sidSecure` uses T2–T4 only), and the proved results audited as proofs (Joux, `jouxGame_eq_dbdhGame`, BB1 correctness, `bb1_sidSecure`); Rule 10 (canonical seals cover 3 of the 12 modules; the other 9 rest on the round-1 hand-list seals, put to Codex), docstrings and sketches, the Q11 unit split, duplication, policy. Source excerpts of only the passages used ([Jou00] §2, §3, §5; [BB04] §2.1–§3.1, §4.1–§4.2, §4.4), PDF hashes re-checked. Evidence `stmt-pairings-r2.zip` (`83b05fbe`) filed at `statement-phase/evidence-r2/` with its manifest (411/411) and PROVENANCE. Merge interaction (git objects): clean with the tip `0542dd92` (#326 merged), #324, #327, #332; add/add conflict with #333 in `AdvancedEncryption.lean` and `TCSlib.lean`, resolved by union (all open heads in two orders give one tree `1fc1b521`). Merge conditions: union by whichever of #331/#333 lands second; rebuild `Pairing/Operations` and its 6 downstream modules (closure meets #326's `DTIME.lean`) and the root on the merged tree. verification.zip `348ce61f` (99 entries), sources.zip 86 files, pack `278ce323`. | Ready to stage |

## ===== briefs/pairings/statement-phase/EVIDENCE.md =====

# Pairing statement draft: evidence

Draft: `stmt/pairings` at `ce9c3728ec582be45fc33ca68d64b5533701093d` (modules
`b02e6ce4a3dcc7c945825d1f1d3b636c5e377a01`), base `e7a9f70f5c1f11c2670f427ef813f2a6d8c53543`.
`$SP` is the session scratchpad (`/tmp/claude-0/-home-user-tcslib/d0667d12-db8d-5853-b0f7-9833dc0884c6/scratchpad`);
the tools expect it in the environment.

Method. No `lake build`, no cache get. Lean 4.25.0 (`PATH=$HOME/.elan/bin:$PATH`), one process at
a time, only on `TCSLIB_OLEANS=$SP/dl-oleans-2`. Python as `python3 -I`.

| Step | Evidence | Result |
|---|---|---|
| Snapshot before | `tree/snapshot-pre.txt` (`tools/snapshot.py`) | 1230 files, `457ba704d26757307f14131aa534929ffd70d30a732b0c744b104ca3fc96a15f` |
| Closure and base delta | `build/closure.txt` (`tools/closure.py`, 73 modules at the base), `build/rebuilt-base-modules.txt` (`tools/downstream.py`) | only `Foundations/BitLists` changed since `eff2dcd0`; it and 7 downstream modules rebuilt |
| Backups | `tree/backed-up.txt` | 8 oleans, hashes equal to the snapshot |
| Base rebuild | `build/base-rebuild-1.txt`, `build/base-rebuild-2.txt` | 8/8 rc 0 |
| New modules | `build/summary.txt`, `build/*.log` (`tools/ladder.sh`) | 11/11 rc 0, 0 errors, 4 target `sorry` warnings |
| Axioms | `axioms.txt` (`tools/AxiomProbe.lean`) | 320 declarations + 52 auxiliary constants; standard axioms only, except `sorryAx` in the 4 targets and `bb1_sidSecure` |
| Rule 10 | `seal/summary.txt`, `seal/*.log` (`tools/seal.py`, `tools/runprobes.sh`) | 7/7 modules 0 errors besides "unknown constant" for names outside a closure; controls: negative fails, positive passes |
| Restore | `restore/restore-log.txt`, `restore/empty-dirs-before-prune.txt`, `tree/snapshot-post.txt` | 8 restored, 15 new oleans deleted, 4 empty dirs pruned; snapshot byte-identical |

Style: `scripts/style_lint.py` 0 findings in 11 files; `scripts/campaign_style_lint.py --check8b`
0 FAIL, 2 WARN (check-8 acronym heuristic; readers exist). Widths at most 100 characters; files at
most 553 lines.

`SHA256SUMS` lists every file of `evidence/`.

## Round 2: ruling Q11 (T4 in its own module)

Head `110c2f9db810d243693b9a5e8976a5ad205f1bab` on the local `stmt/pairings`, rebased onto
`523d80d2d4dd8e4ed6799358831e5b3806c6187b` (range-diff 2/2 identical: `8aa111658bd0509c0fd204d605538ff440f08d02`,
`b7ca25477c1685795f2ea45cd895889f7ecaf1c8`); not pushed. Evidence: `$SP/dl-review/stmt-pairings-r2.zip`, SHA-256
`83b05fbea2fc14ab47687e6a4222dc7073f74d21cb49f22420cefdc5301d573d` (`PROVENANCE.txt`, `SHA256SUMS` inside; not committed).

| Step | Result |
|---|---|
| Split | T4 `exists_bb1_distinguisher` (21-line block: docstring, statement, `sorry`) byte-identical in the new `AdvancedEncryption/IdentityBased/BonehBoyenMachine.lean` (78 lines); `BonehBoyenSecurity.lean` 170 lines (T2, T3, `bb1_sidSecure`, imports the new module); facade `IdentityBased.lean` 32 lines |
| Snapshot before | 1230 files, `457ba704d26757307f14131aa534929ffd70d30a732b0c744b104ca3fc96a15f` |
| Build | closure 85 modules, 20 rebuilt (8 base, 12 pairing): 20/20 rc 0, 0 errors, 4 target `sorry`s (`Assumptions` 1, `BonehBoyenMachine` 1, `BonehBoyenSecurity` 2) |
| Axioms | 320 declarations + 52 auxiliary constants; standard only except `sorryAx` in the 4 targets and `bb1_sidSecure` |
| Rule 10 | round-1 probes for the 2 changed modules: 0 errors, controls as before; whole-file seals A/B, strict and coe (`-DmaxErrors=0`) of `BonehBoyenMachine`, `BonehBoyenSecurity`, `IdentityBased`: 12/12 pass |
| Lint | `style_lint.py` 0 findings (12 files); `campaign_style_lint.py --check8b` 0 FAIL, 2 WARN (round 1's) |
| Root `TCSlib` | 278 modules rebuilt from source (changed or missing since the tree's `eff2dcd0` sources, and downstream): 278/278 rc 0 |
| Restore | 328 backups restored (0 hash failures), 75 new oleans deleted, 13 emptied directories pruned; snapshot byte-identical |

The records branch advanced to `a32ad0df` during the job (#318, #319, #323); no pairing-closure file changed and
the branch merges cleanly.

**Filed (Gate 40, 2026-11-16).** The round-2 archive is now in the records at `evidence-r2/stmt-pairings-r2.zip`
(SHA-256 `83b05fbea2fc14ab47687e6a4222dc7073f74d21cb49f22420cefdc5301d573d`), byte-identical, with its inner manifest
`evidence-r2/SHA256SUMS` (411 files, all verified) and `evidence-r2/PROVENANCE.txt`.

## ===== briefs/pairings/gates/40-pairings-statements/source-excerpts/Jou00-excerpts.md =====

# Jou00: excerpts of the passages used (Gate 40)

**Reference.** A. Joux, *A One Round Protocol for Tripartite Diffie–Hellman*, ANTS-IV, W. Bosma (ed.), LNCS 1838, pp. 385–393, Springer, 2000 (publisher copy, 9 pp.).

**Extraction.** `pdftotext -layout` (poppler) of the uploaded PDF, SHA-256 `dd423b93a7e2dbeb87e6210b26f4c3ec022c3d0681a0ce72262b1d45c53f6df9` (checked when this file was written); line numbers are those of the extracted text. The PDF itself is not committed (pairing ruling Q12; GSW ruling Q14 and the plan-section provenance). Only the passages below are quoted. Mathematical layout (sub- and superscripts, fraction bars) is flattened by the extraction; read formulas against the Lean statements and the PDF where needed.

**Passages.**

- lines 1–4: title
- lines 97–128: §2, p. 387: the Weil and Tate pairings are bilinear and non-degenerate
- lines 129–195: §3, pp. 387–388: the protocol, F_W, the remark e_n(P, P) = 1, two points and F_T, the summary
- lines 325–367: §5, pp. 391–392: security issues

## Lines 1–4: title

```text
          A One Round Protocol for Tripartite
                   Diffie–Hellman

                                    Antoine Joux
```

## Lines 97–128: §2, p. 387: the Weil and Tate pairings are bilinear and non-degenerate

```text

[page break]
                        A One Round Protocol for Tripartite Diffie–Hellman       387

   Using these notions, we can now define the Weil pairing: it is a bilinear
function from the torsion group E[n] to the multiplicative group µn of n-th
roots of unity in some extension of Fp , say Fpk . Given two n-torsion points P
and Q, we compute their pairing en (P, Q) by finding two functions fP and fQ
such that div(fP ) = n(P )−n(O) and div(fQ ) = n(Q)−n(O), and by evaluating:

                            en (P, Q) = fP (Q)/fQ (P ).

    This pairing en : E[n] × E[n] → µn is bilinear and non-degenerate. This
means that en (aP, bQ) = en (P, Q)ab and that for some values of P and Q, we
have en (P, Q) 6= 1. We can easily see that given a point X “independent” from
P and Q, we can reduce the discrete logarithm problem Q = λP on the elliptic
curve to the discrete logarithm problem en (Q, X) = en (P, X)λ in Fpk .
    The variant of the Tate pairing described in [3] is more complicated, since
it operates on divisors instead of points. The Tate pairing operates on n-fold
divisors, i.e. divisors D such that nD is principal, it takes values in µn and it is
bilinear and non-degenerate. Given two n-fold divisors D1 and D2 defined over
an extension Fpk that contains the n-th roots of unity, we find fD1 and fD2 such
that div(fD1 ) = nD1 and div(fD2 ) = nD2 . The Tate pairing of D1 and D2 is
then defined as:
                                                      k
                           tn (D1 , D2 ) = fD1 (D2 )(p −1)/n .
    This pairing is also bilinear and non-degenerate. Moreover, for the purpose
of discrete logarithm reduction, the Tate pairing tn (D1 , D2 ) can easily be trans-
formed into a pairing that involves points. One can simply fix two points R and
S, and remark that tn ((λP ) − (O), (R) − (S)) = tn ((P ) − (O), (R) − (S))λ .
    For more details about the properties and definitions of the Weil and Tate
pairing, we refer the reader to [8,3,4].
```

## Lines 129–195: §3, pp. 387–388: the protocol, F_W, the remark e_n(P, P) = 1, two points and F_T, the summary

```text
3   A Tripartite Diffie–Hellman Protocol

In this section, we want to build an analog of the Diffie–Hellman protocol, that
involves three participants A, B and C, requires a single pass of communica-
tions and allows the construction of a common secret KA,B,C . By a single pass
of communication, we mean that each participant is allowed to talk once and
broadcast some data to the other two. The main idea is as in ordinary Diffie–
Hellman, we start from some elliptic curve E and some point P . Then A, B
and C each chose a random number (a, b or c) and they respectively compute
PA = aP , PB = bP and PC = cP and broadcast these values. Then they respec-
tively compute F (a, PB , PC ), F (b, PA, PC ) and F (c, PA, PB ), where the function
F is chosen in a way that ensures that these numbers will be equal and that
this common value KA,B,C will be hard to compute given PA, PB and PC . The
problem now is to find such an F .
    Using the Weil pairing, it is seems very easy to define such an F using the
following formula:
                            FW (x, P, Q) = en (P, Q)x.

[page break]
388       Antoine Joux

With this definition, one can easily check that:

        FW (a, PB , PC ) = FW (b, PA, PC ) = FW (c, PA, PB ) = FW (1, P, P )abc.

However, this function is not satisfying because en (P, P ) = 1 and thus KA,B,C
is a constant. Nevertheless, the basic idea is quite sound and can in fact be
implemented if we use two independent points P , and Q and if we have the
three participants compute and broadcast (PA , QA), (PB , QB ) and (PC , QC ).
Then A, B and C can respectively compute FW (a, PB , QC ) = FW (a, QB , PC ),
FW (b, PA, QC ) = FW (b, QA , PC ) and FW (c, PA, QB ) = FW (c, QA, PB ). More-
over, all these values are equal and thanks to the independence of P and Q, they
are not constant.
    Moreover, using two points P and Q, it is easy to use the Tate pairing instead
of the Weil pairing, and to define another function F as:

                            FT (x, D1 , D2 ) = tn (D1 , D2 )x .

Then A, B and C can respectively compute:

            FT (a, (PB ) − (QB ), (PC + QC ) − (O)) =
                                  FT (a, (PC ) − (QC ), (PB + QB ) − (O)),
             FT (b, (PA ) − (QA ), (PC + QC ) − (O)) =
                                   FT (b, (PC ) − (QC ), (PA + QA ) − (O)),
             FT (c, (PB ) − (QB ), (PA + QA ) − (O)) =
                                   FT (c, (PA) − (QA ), (PB + QB ) − (O)).

Because of the bilinearity of the pairing, all these numbers are equal and because
of the non-degeneracy, their common value

                         FT (1, (P ) − (Q), (P + Q) − (O))abc

is not independent from the choice of a, b and c.
    Since FT is based on the Tate pairing, it will be faster to evaluate then FW
(see the general remark about the efficiency of the Tate pairing versus that of
the Weil pairing in [4]). Finally, our tripartite Diffie–Hellman protocol can be
summarized as follows:


              Alice                  Bob                Charlie
           Choose a              Choose b              Choose c
      Compute (PA , QA ) Compute (PB , QB ) Compute (PC , QC )
               Broadcast PA , PB , PC and QA , QB , QC .
                      Compute the common key as:
      FT (a, (PB ) − (QB ), (PC + QC ) − (O))
                 FT (b, (PA ) − (QA ), (PC + QC ) − (O))
                             FT (c, (PB ) − (QB ), (PA + QA ) − (O))

[page break]
                       A One Round Protocol for Tripartite Diffie–Hellman     389
```

## Lines 325–367: §5, pp. 391–392: security issues

```text
5     Security Issues

Clearly in order to be secure the tripartite Diffie–Hellman described here requires
the discrete logarithm on the chosen elliptic curve to be hard, and the discrete
logarithm in the finite field Fpk to be hard. Since we placed ourselves in the cases
where either the MOV or the FR reduction applies, the hardness of the elliptic

[page break]
392     Antoine Joux

curve discrete log implies the hardness of the finite field discrete log and we can
remove the second condition. This is a simple restatement of the fact that when
the finite field discrete log, then to solve the elliptic curve discrete log we simply
transport the problem in the finite field using the pairing and then solve the
problem in the finite field. However, it is not known whether the elliptic curve
discrete logarithm on a weak curve is as hard as the discrete logarithm in the
corresponding finite field (in the sense of the MOV or FR reduction). In fact,
this is a very interesting open problem. Moreover, as in the Diffie–Hellman case
this is not the whole story, some Diffie–Hellman like problem and Diffie–Hellman
like decision problem should be hard in order to get security.
     Quite amusingly, we should note that on curves where either the MOV or FR
reduction applies, the usual Diffie–Hellman decision problem is mostly easy. Re-
member that the usual Diffie–Hellman problem is given a quadruple (g, ga , gb , gc)
to decide whether c = ab. This problem can also be expressed with the following
formulation which is slightly different. Given a quadruple (g, ga , h, hb), decide
whether a = b. Now on an elliptic curve where the MOV reduction applies, we
can easily test for a quadruple (P, aP, Q, bQ) whether a = b, it suffices to com-
pute en (aP, Q) and en (P, bQ) and to compare them. This test works as soon
as P and Q are independent (i.e. when en (P, Q) 6= 1). Of course, in the FR
case, such a test also exists. More precisely, one can test for the equality of
tn ((aP ) − (O), (λQ) − (Q)) and tn ((P ) − (O), (λbQ) − (bQ)), where λ is essen-
tially any constant number (some values of λ are excluded, for example λ = 1
is not allowed). Note than when P and Q are not independent, the test usually
doesn’t work, thus some cases of the usual Diffie–Hellman decision problem are
still hard on these elliptic curves.
     With the current knowledge of elliptic curves, we believe that this system
is secure in practice as soon as the discrete logarithm in Fpk is hard. For the
supersingular case (k = 2), we think that p should be a 512 bits prime. In the
trace 2 case (k = 1), we recommend to choose a 1024 bits prime. Moreover,
the usual precautions should be taken, i.e. some large prime q should divide the
order of the elliptic curve, all the points involved in the computation should be
of order q, and we should use the pairing eq or tq .
```

## ===== briefs/pairings/gates/40-pairings-statements/source-excerpts/BB04-excerpts.md =====

# BB04: excerpts of the passages used (Gate 40)

**Reference.** D. Boneh, X. Boyen, *Efficient Selective-ID Secure Identity Based Encryption Without Random Oracles*, Cryptology ePrint Archive, Report 2004/172, full version dated December 2004 (20 pp.); its numbering is used throughout.

**Extraction.** `pdftotext -layout` (poppler) of the uploaded PDF, SHA-256 `63c1c7b0817f36d6e558107bf281e22d2c454f821fadd533ced653e81a6a35de` (checked when this file was written); line numbers are those of the extracted text. The PDF itself is not committed (pairing ruling Q12; GSW ruling Q14 and the plan-section provenance). Only the passages below are quoted. Mathematical layout (sub- and superscripts, fraction bars) is flattened by the extraction; read formulas against the Lean statements and the PDF where needed.

**Passages.**

- lines 1–11: title
- lines 93–181: §2, §2.1 (IBE, the selective-identity game, Definitions 2.1 and 2.2) and §2.2 (bilinear groups), pp. 2–4
- lines 182–207: §3 and §3.1 (BDH, Decision BDH, P_BDH / R_BDH, Definition 3.1), pp. 4–5
- lines 236–397: §4, §4.1 (the HIBE construction; BB1 is depth 1) and §4.2 (Theorem 4.1 and its proof), pp. 5–8
- lines 405–412: §4.4 (arbitrary identities, "2^b < p is sufficient"), p. 8

## Lines 1–11: title

```text
An extended abstract of this paper appears in C. Cachin and J. Camenisch, editors, Advances in Cryptology—
EUROCRYPT 2004, volume 3027 of Lecture Notes in Computer Science, pages 223–238, Berlin: Springer-
Verlag, 2004. This version is available from the cryptology archive at http://eprint.iacr.org/2004/172/.




             Efficient Selective-ID Secure Identity Based Encryption
                             Without Random Oracles
                                    Dan Boneh∗                     Xavier Boyen
                                Stanford University               Voltage Security
```

## Lines 93–181: §2, §2.1 (IBE, the selective-identity game, Definitions 2.1 and 2.2) and §2.2 (bilinear groups), pp. 2–4

```text
2     Preliminaries
Before presenting our results we briefly review the definition of security for an IBE system. We
also review the definition of groups equipped with a bilinear map.

2.1   Selective Identity Secure IBE and HIBE Systems
Recall that an Identity Based Encryption system (IBE) consists of four algorithms [Sha84, BF01]:
Setup, KeyGen, Encrypt, Decrypt. The Setup algorithm generates system parameters, denoted by
params, and a master key master-key. The KeyGen algorithm uses the master key to generate the
private key corresponding to a given identity. The encryption algorithm encrypts messages for a


                                                  2

[page break]
given identity (using the system parameters) and the decryption algorithm decrypts ciphertexts
using the private key. In a Hierarchical IBE [HL02, GS02] identities are vectors. A vector of
dimension ` represents an identity at depth `. Algorithm KeyGen takes as input an identity
ID = (I1 , . . . , I` ) at depth ` and the private key dID |`−1 of the parent identity ID|`−1 = (I1 , . . . , I`−1 )
at depth ` − 1. It outputs the private key dID for identity ID. We refer to the master-key as the
private key at depth 0 and note that an IBE system is an HIBE where all identities are at depth 1.
    Boneh and Franklin [BF01, BF03] define chosen ciphertext security for IBE systems under a
chosen identity attack. In their model the adversary is allowed to adaptively chose the public
key it wishes to attack (the public key on which it will be challenged). Canetti, Halevi, and
Katz [CHK03, CHK04] define a weaker notion of security in which the adversary commits ahead of
time to the public key it will attack. We refer to this notion as selective identity, chosen ciphertext
secure IBE (IND-sID-CCA). More precisely, selective identity IBE and HIBE security is defined
using the following game:
      Init: The adversary outputs an identity ID∗ where it wishes to be challenged.
      Setup: The challenger runs the Setup algorithm. It gives the adversary the resulting system
          parameters params. It keeps the master-key to itself.
      Phase 1: The adversary issues queries q1 , . . . , qm where query qi is one of:
               – Private key query hIDi i where IDi 6= ID∗ and IDi is not a prefix of ID∗ . The challenger
                 responds by running algorithm KeyGen to generate the private key di corresponding
                 to the public key hIDi i. It sends di to the adversary.
               – Decryption query hCi i for identity ID∗ or any prefix of ID∗ . The challenger responds
                 by running algorithm KeyGen to generate the private key d corresponding to ID∗ (or
                 the relevant prefix thereof as requested). It then runs algorithm Decrypt to decrypt
                 the ciphertext Ci using the private key d. It sends the resulting plaintext to the
                 adversary.
            These queries may be asked adaptively, that is, each query qi may depend on the replies
            to q1 , . . . , qi−1 .
      Challenge: Once the adversary decides that Phase 1 is over it outputs two equal length
          plaintexts M0 , M1 ∈ M on which it wishes to be challenged. The challenger picks a
          random bit b ∈ {0, 1} and sets the challenge ciphertext to C = Encrypt(params, ID∗ , Mb ).
          It sends C as the challenge to the adversary.
      Phase 2: The adversary issues additional queries qm+1 , . . . , qn where qi is one of:
               – Private key query hIDi i where IDi 6= ID∗ and IDi is not a prefix of ID∗ . The challenger
                 responds as in Phase 1.
               – Decryption query hCi i 6= hCi for ID∗ or any prefix of ID∗ . The challenger responds
                 as in Phase 1.
            These queries may be asked adaptively as in Phase 1.
      Guess: Finally, the adversary outputs a guess b0 ∈ {0, 1}. The adversary wins if b = b0 .
We refer to such an adversary A as an IND-sID-CCA adversary. We define the advantage of the
adversary A in attacking the scheme E as
                                                                       1
                                            AdvE,A = Pr[b = b0 ] −
                                                                       2
The probability is over the random bits used by the challenger and the adversary.


                                                         3

[page break]
Definition 2.1. We say that an IBE or HIBE system E is (t, qID , qC , )-selective identity, adaptive
chosen ciphertext secure if for any t-time IND-sID-CCA adversary A that makes at most qID chosen
private key queries and at most qC chosen decryption queries we have that AdvE,A < . As
shorthand, we say that E is (t, qID , qC , ) IND-sID-CCA secure.

Semantic Security. As usual, we define selective identity, chosen plaintext security for an IBE
system as in the preceding game, except that the adversary is not allowed to issue any decryption
queries. The adversary may still issue adaptive private key queries.

Definition 2.2. We say that an IBE or HIBE system E is (t, qID , )-selective identity, chosen
plaintext secure if E is (t, qID , 0, )-selective identity, chosen ciphertext secure. As shorthand, we say
that E is (t, qID , ) IND-sID-CPA secure.

2.2     Bilinear Groups
We briefly review the necessary facts about bilinear maps and bilinear map groups [Jou00, Mil04].
We use the following notation:
    1. G and G1 are two (multiplicative) cyclic groups of prime order p;
    2. g is a generator of G.
    3. e is a bilinear map e : G × G → G1 .
    Let G and G1 be two groups as above. A bilinear map is a map e : G × G → G1 with the
following properties:
    1. Bilinearity: for all u, v ∈ G and a, b ∈ Z, we have e(ua , v b ) = e(u, v)ab .
    2. Non-degeneracy: e(g, g) 6= 1.
     We say that G is a bilinear group if the group action in G can be computed efficiently and there
exists a group G1 and an efficiently computable bilinear map e : G × G → G1 as above. Note that
e(, ) is symmetric since e(g a , g b ) = e(g, g)ab = e(g b , g a ).
     Throughout the paper, for a prime order group G we use G∗ to denote the set G \ {1G } where
1G is the identity of G.
```

## Lines 182–207: §3 and §3.1 (BDH, Decision BDH, P_BDH / R_BDH, Definition 3.1), pp. 4–5

```text
3     Complexity Assumptions
Let G be a bilinear group of prime order p. We review the standard Bilinear Diffie-Hellman (BDH)
assumption and define the Bilinear Diffie-Hellman Inversion (BDHI) assumption.

3.1     Bilinear Diffie-Hellman Assumption
The BDH problem [Jou00, SOK00, BF01] in G is as follows: given a tuple g, g a , g b , g c ∈ G as input,
output e(g, g)abc ∈ G1 . An algorithm A has advantage  in solving BDH in G if
                                    h                                 i
                                Pr A(g, g a , g b , g c ) = e(g, g)abc ≥ 

where the probability is over the random choice of generator g in G∗ , the random choice of a, b, c in
Zp , and the random bits used by A. Similarly, we say that an algorithm B that outputs b ∈ {0, 1}
has advantage  in solving the decision BDH problem in G if
                   h                                       i    h                              i
                 Pr B(g, g a , g b , g c , e(g, g)abc ) = 0 − Pr B(g, g a , g b , g c , T ) = 0 ≥ 

                                                      4

[page break]
where the probability is over the random choice of generator g in G∗ , the random choice of a, b, c in
Zp , the random choice of T ∈ G1 , and the random bits consumed by B. We refer to the distribution
on the left as PBDH and the distribution on the right as RBDH .

Definition 3.1. We say that the (Decision) (t, )-BDH assumption holds in G if no t-time algorithm
has advantage at least  in solving the (Decision) BDH problem in G.

Occasionally we drop the t and  and refer to the BDH and Decision BDH assumptions in G.
```

## Lines 236–397: §4, §4.1 (the HIBE construction; BB1 is depth 1) and §4.2 (Theorem 4.1 and its proof), pp. 5–8

```text
4     Efficient Selective Identity IBE and HIBE Based on BDH
      Without Random Oracles
We construct an efficient HIBE system that is selective identity secure without random oracles
based on the Decision BDH assumption. In particular, this implies an efficient selective identity,
chosen ciphertext secure IBE based on Decision BDH without random oracles.

4.1    Construction
Let G be a bilinear group of prime order p (the security parameter determines the size of G). Let
e : G × G → G1 be the bilinear map. For now, we assume public keys (ID) of depth ` are vectors
of elements in Zp ` . We write ID = (I1 , . . . , I` ) ∈ Zp ` . The j-th component corresponds to the
identity at level j. We later extend the construction to public keys over {0, 1}∗ by first hashing
each component Ij using a collision resistant hash H : {0, 1}∗ → Zp . We also assume messages to
be encrypted are elements in G1 . The HIBE system works as follows:


                                                       5

[page break]
Setup(`): To generate system parameters for an HIBE of maximum depth `, select a random
     generator g in G∗ , a random α ∈ Zp , and set g1 = g α . Next, pick random elements h1 , . . . , h` ∈
     G and a random element g2 ∈ G. The public parameters params and the secret master-key
     are given by
                           params = (g, g1 , g2 , h1 , . . . , h` ) , master-key = g2α

      For j = 1, . . . , `, we define Fj : Zp → G to be the function:                      Fj (x) = g1x hj .

KeyGen(dID |j−1 , ID): To generate the private key dID for an identity ID = (I1 , . . . , Ij ) ∈ Zp j of
    depth j ≤ `, pick random r1 , . . . , rj ∈ Zp and output
                                                         j
                                                                                                  !
                                                         Y
                                     dID =       g2α ·         Fk (Ik )rk , g r1 , . . . , g rj
                                                         k=1

      Note that the private key for ID can be generated just given a private key for ID|j−1 =
      (I1 , . . . , Ij−1 ) ∈ Zp j−1 , as required. Indeed, let dID |j−1 = (d0 , . . . , dj−1 ) be the private key for
      ID|j−1 . To generate dID pick a random rj ∈ Zp and output dID = (d0 ·Fj (Ij )rj , d1 , . . . , dj−1 , g rj ).

Encrypt(params, ID, M): To encrypt a message M ∈ G1 under the public key ID = (I1 , . . . , Ij ) ∈
    Zp j , pick a random s ∈ Zp and output
                                                                               
                                         s      s          s                  s
                          C = e(g1 , g2 ) · M, g , F1 (I1 ) , . . . , Fj (Ij )

      Note that e(g1 , g2 ) can be precomputed once and for all so that encryption does not require
      any pairing computations. Alternatively, e(g1 , g2 ) can be included in the system parameters,
      in which case g2 can be dropped.

Decrypt(dID , C): Consider an identity ID = (I1 , . . . , Ij ). To decrypt a given ciphertext C =
    (A, B, C1 , . . . , Cj ) using the private key dID = (d0 , d1 , . . . , dj ), output
                                                         Qj
                                                           k=1 e(Ck , dk )
                                                  A·                           =M
                                                               e(B, d0 )

      Indeed, for a valid ciphertext, we have
                         Qj                               Qj                 s rk
                           k=1 e(Ck , dk )                 k=1 e(Fk (Ik ), g)                  1
                                             =                   j
                                                                                         =            s
                              e(B, d0 )                    s α                     s r     e(g1 , g2 )
                                                               Q
                                                  e(g, g2 )      k=1 e(g, Fk (Ik ))
                                                                                       k




4.2   Security
The HIBE system above is reminiscent of the Gentry-Silverberg HIBE which is only known to be
secure in the random oracle model. Surprisingly, our choice of functions F1 , . . . , F` enables us to
prove security without random oracles. We prove security of our HIBE system under the standard
Decision BDH assumption in G.

Theorem 4.1. Suppose the (t, )-Decision BDH assumption holds in G. Then the previously defined
`-HIBE system is (t0 , qS , )-selective identity, chosen plaintext (IND-sID-CPA) secure for arbitrary `
and qS , and any t0 < t − Θ(τ ` qS ) where τ is the maximum time for an exponentiation in G.


                                                                 6

[page break]
Proof. Suppose A has advantage  in attacking the HIBE system. We build an algorithm B
that solves the Decision BDH problem in G. Algorithm B is given as input a random 5-tuple
(g, g a , g b , g c , T ) that is either sampled from PBDH (where T = e(g, g)abc ) or from RBDH (where
T is uniform and independent in G1 ). Algorithm B’s goal is to output 1 if T = e(g, g)abc and 0
otherwise. Set g1 = g a , g2 = g b , g3 = g c . Algorithm B works by interacting with A in a selective
identity game as follows:
Initialization. The selective identity game begins with A first outputting an identity ID∗ =
      (I∗1 , . . . , I∗k ) ∈ Zp k of depth k ≤ ` that it intends to attack. If necessary, B appends ran-
      dom elements in Zp to ID∗ so that ID∗ is a vector of length `.
Setup. To generate the system parameters, algorithm B picks α1 , . . . , α` ∈ Zp at random and
                          −I∗
      defines hj = g1 j g αj ∈ G for j = 1, . . . , `. It gives A the system parameters params =
      (g, g1 , g2 , h1 , . . . , h` ). Note that the corresponding master key, which is unknown to B, is
      g2a = g ab ∈ G. As before, for j = 1, . . . , ` we define Fj : Zp → G to be the function
                                                                                       x−I∗j α
                                                          Fj (x) = g1x hj = g1                gj



Phase 1. A issues up to qS private key queries. Consider a query for the private key corresponding
    to ID = (I1 , . . . , Iu ) ∈ Zp u where u ≤ `. The only restriction is that ID is not a prefix of ID∗ .
    Let j be the smallest index such that Ij 6= I∗j . Necessarily 1 ≤ j ≤ u. To respond to the
    query, algorithm B first derives a private key for the identity (I1 , . . . , Ij ) from which it then
    constructs a private key for the requested identity ID = (I1 , . . . , Ij , . . . , Iu ). Algorithm B picks
    random elements r1 , . . . , rj ∈ Zp and sets
                         −αj      j                                                                                             −1
                        Ij −I∗    Y                                                                                           Ij −I∗
                                                   rv                r1                              rj−1
               d0 = g2       j
                                          Fv (Iv ) ,      d1 = g ,              ...,   dj−1 = g             ,       d j = g2       j
                                                                                                                                       g rj
                                  v=1

      We claim that (d0 , d1 , . . . , dj ) is a valid random private key for (I1 , . . . , Ij ). To see this, let
      r̃j = rj − b/(Ij − I∗j ). Then we have that
                      −αj                            −αj
                                                                                                               b
                    (Ij −I∗
                          j)                       (Ij −I∗
                                                         j)     Ij −I∗                    Ij −I∗        rj − I −I∗
                                        rj
                  g2           Fj (Ij )      = g2             (g1    j
                                                                         g αj )rj = g2a (g1    j
                                                                                                   g αj )       j     j   = g2a Fj (Ij )r̃j
      It follows that the private key (d0 , d1 , . . . , dj ) defined above satisfies
                                  j−1
                                  Y
                 d0 = g2a · (             Fv (Iv )rv ) · Fj (Ij )r̃j ,         d1 = g r1 , . . . , dj−1 = g rj−1 ,              dj = g r̃j
                                  v=1

      where r1 , . . . , rj−1 , r̃j are uniform in Zp . This matches the definition for a private key for
      (I1 , . . . , Ij ). Hence, (d0 , d1 , . . . , dj ) is a valid private key for (I1 , . . . , Ij ). Algorithm B derives
      a private key for the requested ID from the private key (d0 , d1 , . . . , dj ) and gives A the result.
Challenge. When A decides that Phase 1 is over, it outputs two messages M0 , M1 ∈ G1 on which
    it wishes to be challenged. Algorithm B picks a random bit b ∈ {0, 1} and responds with the
    ciphertext C = (Mb · T, g3 , g3α1 , . . . , g3αk ). Since Fi (I∗i ) = g αi for all i, we have that
                                              C = (Mb · T, g c , F1 (I∗1 )c , . . . , Fk (I∗k )c )
      Hence, if T = e(g, g)abc = e(g1 , g2 )c then C is a valid encryption of Mb under the public key
      ID∗ = (I∗1 , . . . , I∗k ). On the other hand, when T is uniform and independent in G1 (when the
      input 5-tuple is sampled from RBDH ) then C is independent of b in the adversary’s view.

                                                                           7

[page break]
Phase 2. A continues to issue queries not issued in Phase 1. Algorithm B responds as before.

Guess. Finally, A outputs a guess b0 ∈ {0, 1}. Algorithm B concludes its own game by outputting
    a guess as follows. If b = b0 then B outputs 1 meaning T = e(g, g)abc . Otherwise, it outputs
    0 meaning T 6= e(g, g)abc .

    When the input 5-tuple is sampled from PBDH (where T = e(g, g)abc ) then A’s view is identical
to its view in a real attack game and therefore A must satisfy | Pr[b = b0 ] − 1/2| > . On the
other hand, when the input 5-tuple is sampled from RBDH (where T is uniform in G1 ) then
Pr[b = b0 ] = 1/2. Therefore, with g uniform in G∗ , a, b, c uniform in Zp , and T uniform in G1 we
have that
                                                                                
       h
               a b c            abc
                                      i    h
                                                  a b c
                                                                    i        1       1
     Pr B(g, g , g , g , e(g, g) ) = 0 − Pr B(g, g , g , g , T ) = 0 ≥         ± −      = 
                                                                             2       2

as required. This completes the proof of Theorem 4.1.
```

## Lines 405–412: §4.4 (arbitrary identities, "2^b < p is sufficient"), p. 8

```text
4.4   Arbitrary Identities
We can extend our HIBE above to handle identities ID = (I1 , . . . , I` ) with Ij ∈ {0, 1}∗ (as opposed
to Ij ∈ Zp ) by first hashing each Ij using a collision resistant hash function H : {0, 1}∗ → Zp prior
to key generation and encryption. A standard argument shows that if the scheme above is selective
identity, chosen ciphertext secure then so is the scheme with the additional hash function. We note
that there is no need for a full domain hash into Zp ; for example, a collision resistant hash function
H : {0, 1}∗ → {1, . . . , 2b } where 2b < p is sufficient for the security proof.
```

## ===== TCSlib/Cryptography/Pairing/Group.lean (Lean, at 110c2f9db810d243693b9a5e8976a5ad205f1bab) =====

```lean
/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TCSlib contributors
-/
import TCSlib.Complexity.Randomized.PPT
import TCSlib.Cryptography.Foundations.Probability
import Mathlib.Data.ZMod.Basic
import Mathlib.GroupTheory.OrderOfElement
import Mathlib.GroupTheory.SpecificGroups.Cyclic

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Symmetric bilinear groups and their generators

A *bilinear group* [BB04, §2.2] is a pair of cyclic groups `G`, `G_1` of prime order `p` with a
map `e : G × G → G_1` that is bilinear (`e(u^a, v^b) = e(u, v)^{ab}`) and non-degenerate
(`e(g, g) ≠ 1` for a generator `g`). The pairing is symmetric: `e(u, v) = e(v, u)`. Here the
groups stay abstract. No elliptic curve or concrete pairing (Weil, Tate) is formalized.

**Representation.** A bilinear group is a bundle `BilinearGroup wG wT`: two finite commutative
groups `G` and `GT` (the paper's `G_1`) of the same prime order, a distinguished generator `gen`,
the pairing as a bimultiplicative map `G →* G →* GT`, and injective fixed-width encodings of the
elements of both groups as `wG`- and `wT`-bit strings. A bimultiplicative map is the
multiplicative form of [BB04, §2.2, item 1]: `bilinear_pow` derives `e(u^a, v^b) = e(u, v)^{ab}`.

**The generator.** The asymptotic layer quantifies over non-uniform PPT adversaries
(`Complexity.NUPPT`) and draws the group from a *bilinear group generator*, as the
discrete-logarithm and DDH layers draw theirs from an instance generator
(`Candidates.ExpGroupGen`, `Candidates.SafePrimeGen`). A `BilinearGen` is a PPT `Gen(1^κ)`
whose output string, the *description* `d`, has a fixed polynomial length. The group it describes
is `group κ d`, a total function of the description. So every string describes some bilinear
group, and no validity predicate is needed. Adversaries receive the description.

**Deviation:** [BB04] is concrete (a fixed group `G`, `(t, ε)` bounds); here the group is drawn
by a PPT generator at each security parameter, and security is asymptotic. The efficiency of the
group operations and of the pairing ("efficiently computable", [BB04, §2.2]) is not a field of
the bundle. It is the separate contract `BilinearGen.Ops` (`Pairing/Operations.lean`), assumed
only by the results whose reductions compute in the group.

## Main definitions

* `TCSlib.Cryptography.Pairing.BilinearGroup` — a symmetric bilinear group of prime order with
  fixed-width encodings [BB04, §2.2].
* `TCSlib.Cryptography.Pairing.BilinearGen` — a bilinear group generator; `BilinearGen.desc`,
  `BilinearGen.inst` — the description and the group at the generator's coins;
  `BilinearGen.OrderAtLeastExcept` — the order is large except on a set of coins of small
  probability.

## Main results

* `BilinearGroup.bilinear_pow`, `pair_pow_left`, `pair_pow_right` — bilinearity
  [BB04, §2.2, item 1].
* `BilinearGroup.pair_comm` — the pairing is symmetric [BB04, §2.2, the remark after item 2].
* `BilinearGroup.pow_order`, `BilinearGroup.pow_val_mul` — exponents act through `Z_p`.
* `BilinearGroup.exists_pow_eq` — every element of `G^*` generates `G`.
* `BilinearGroup.pair_ne_one` — every element of `G^*` pairs non-trivially with itself.
* `BilinearGroup.pow_val_bijective` — `a ↦ e(g, g)^a` is a bijection `Z_p → G_1` for `g ∈ G^*`.

## References

* [BB04] D. Boneh, X. Boyen, *Efficient Selective-ID Secure Identity Based Encryption Without
  Random Oracles*, full version, Cryptology ePrint Archive, Report 2004/172, December 2004
  (extended abstract: EUROCRYPT 2004, LNCS 3027, pp. 223–238). §2.2 (bilinear groups).
* [Jou00] A. Joux, *A One Round Protocol for Tripartite Diffie–Hellman*, ANTS-IV, LNCS 1838,
  pp. 385–393, Springer, 2000. §2 (the Weil and Tate pairings are bilinear and non-degenerate).
* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed., January 2010.
  (Definition 26.8, non-uniform PPT; the instance-generator convention of §2.8 and §3.11.)
-/

namespace TCSlib.Cryptography.Pairing

open Complexity

/-- A **symmetric bilinear group of prime order** with fixed-width encodings [BB04, §2.2]: finite
commutative groups `G` and `G_T` (the paper's `G_1`) of the same prime order `p`, a generator `g`
of `G` (`g ≠ 1`; `G` has prime order), a pairing `e : G × G → G_T` that is multiplicative in each
argument, and non-degenerate, `e(g, g) ≠ 1` [BB04, §2.2, items 1–2]. Elements are written as
`wG`-bit (resp. `wT`-bit) strings by injective encodings, the representation handed to machines.

**Deviation:** bilinearity is stated as a bimultiplicative map `G →* G →* G_T`; the paper's
`e(u^a, v^b) = e(u, v)^{ab}` for `a, b ∈ ℤ` is derived (`bilinear_pow`). The fixed generator `gen`
witnesses that `G^* = G ∖ {1}` is not empty; the schemes and assumptions sample their generator
uniformly from `G^*`, as [BB04, §3.1 and §4.1] do. -/
structure BilinearGroup (wG wT : ℕ) where
  /-- The source group `G`. -/
  G : Type
  /-- The target group `G_T` (the paper's `G_1`). -/
  GT : Type
  /-- `G` is a commutative group. -/
  [commGroupG : CommGroup G]
  /-- `G_T` is a commutative group. -/
  [commGroupGT : CommGroup GT]
  /-- `G` is finite. -/
  [fintypeG : Fintype G]
  /-- `G_T` is finite. -/
  [fintypeGT : Fintype GT]
  /-- Equality in `G` is decidable. -/
  [decEqG : DecidableEq G]
  /-- Equality in `G_T` is decidable. -/
  [decEqGT : DecidableEq GT]
  /-- The common prime order `p`. -/
  order : ℕ
  /-- `p` is prime. -/
  order_prime : order.Prime
  /-- `|G| = p`. -/
  card_G : Fintype.card G = order
  /-- `|G_T| = p`. -/
  card_GT : Fintype.card GT = order
  /-- A generator `g` of `G`. -/
  gen : G
  /-- `g ≠ 1`, so `g` generates the group `G` of prime order. -/
  gen_ne_one : gen ≠ 1
  /-- The pairing `e`, multiplicative in each argument. -/
  pair : G →* G →* GT
  /-- Non-degeneracy: `e(g, g) ≠ 1` [BB04, §2.2, item 2]. -/
  pair_gen_ne_one : pair gen gen ≠ 1
  /-- The encoding of `G` as `wG`-bit strings. -/
  encG : G → Fin wG → Bool
  /-- Distinct elements of `G` have distinct encodings. -/
  encG_injective : Function.Injective encG
  /-- The encoding of `G_T` as `wT`-bit strings. -/
  encT : GT → Fin wT → Bool
  /-- Distinct elements of `G_T` have distinct encodings. -/
  encT_injective : Function.Injective encT

attribute [instance] BilinearGroup.commGroupG BilinearGroup.commGroupGT BilinearGroup.fintypeG
  BilinearGroup.fintypeGT BilinearGroup.decEqG BilinearGroup.decEqGT

namespace BilinearGroup

variable {wG wT : ℕ} (B : BilinearGroup wG wT)

/-- The order of a bilinear group is prime, as a `Fact` (so `ZMod B.order` is a field). -/
instance factPrime : Fact B.order.Prime := ⟨B.order_prime⟩

/-- The order of a bilinear group is nonzero (so `ZMod B.order` is finite). -/
instance neZeroOrder : NeZero B.order := ⟨B.order_prime.ne_zero⟩

/-- `G^* = G ∖ {1}` is not empty: it contains the generator `gen`. -/
instance nonempty_ne_one : Nonempty {x : B.G // x ≠ 1} := ⟨⟨B.gen, B.gen_ne_one⟩⟩

/-- **Bilinearity** [BB04, §2.2, item 1]: `e(u^a, v^b) = e(u, v)^{ab}` for natural exponents. -/
theorem bilinear_pow (u v : B.G) (a b : ℕ) : B.pair (u ^ a) (v ^ b) = B.pair u v ^ (a * b) := by
  rw [map_pow (B.pair (u ^ a)) v b, map_pow B.pair u a, MonoidHom.pow_apply, ← pow_mul,
    mul_comm]

/-- Bilinearity in the first argument: `e(u^a, v) = e(u, v)^a`. -/
theorem pair_pow_left (u v : B.G) (a : ℕ) : B.pair (u ^ a) v = B.pair u v ^ a := by
  rw [map_pow, MonoidHom.pow_apply]

/-- Bilinearity in the second argument: `e(u, v^b) = e(u, v)^b`. -/
theorem pair_pow_right (u v : B.G) (b : ℕ) : B.pair u (v ^ b) = B.pair u v ^ b :=
  map_pow (B.pair u) v b

/-- `|G| = p` as a `Nat.card`: `Nat.card B.G = B.order`. -/
theorem natCard_G : Nat.card B.G = B.order := by
  rw [Nat.card_eq_fintype_card, B.card_G]

/-- **Every element of `G^*` generates `G`**: for `g ≠ 1` and any `x`, `x = g^n` for some `n`
(`G` has prime order). -/
theorem exists_pow_eq {g : B.G} (hg : g ≠ 1) (x : B.G) : ∃ n : ℕ, g ^ n = x :=
  (Submonoid.mem_powers_iff _ _).1 (mem_powers_of_prime_card B.natCard_G hg)

/-- **The pairing is symmetric** [BB04, §2.2, the remark after item 2]: `e(u, v) = e(v, u)`,
since `e(g^a, g^b) = e(g, g)^{ab} = e(g^b, g^a)`. -/
theorem pair_comm (u v : B.G) : B.pair u v = B.pair v u := by
  obtain ⟨a, rfl⟩ := B.exists_pow_eq B.gen_ne_one u
  obtain ⟨b, rfl⟩ := B.exists_pow_eq B.gen_ne_one v
  rw [B.bilinear_pow, B.bilinear_pow, mul_comm]

/-- `x^p = 1` in `G`: Lagrange's theorem with `|G| = p`. -/
theorem pow_order (x : B.G) : x ^ B.order = 1 := by
  rw [← B.card_G]
  exact pow_card_eq_one

/-- `y^p = 1` in `G_T`: Lagrange's theorem with `|G_T| = p`. -/
theorem pow_order_GT (y : B.GT) : y ^ B.order = 1 := by
  rw [← B.card_GT]
  exact pow_card_eq_one

/-- Exponents of `G` act through `Z_p`: `x^{(ab mod p)} = (x^a)^b` read in `Z_p`, i.e.
`x ^ (a * b).val = x ^ (a.val * b.val)` for `a, b ∈ Z_p`. -/
theorem pow_val_mul (x : B.G) (a b : ZMod B.order) : x ^ (a * b).val = x ^ (a.val * b.val) := by
  rw [ZMod.val_mul, ← Nat.mod_add_div (a.val * b.val) B.order, pow_add, pow_mul, B.pow_order,
    one_pow, mul_one, Nat.mod_add_div]

/-- Exponents of `G_T` act through `Z_p`: `y ^ (a * b).val = y ^ (a.val * b.val)`. -/
theorem pow_val_mul_GT (y : B.GT) (a b : ZMod B.order) :
    y ^ (a * b).val = y ^ (a.val * b.val) := by
  rw [ZMod.val_mul, ← Nat.mod_add_div (a.val * b.val) B.order, pow_add, pow_mul, B.pow_order_GT,
    one_pow, mul_one, Nat.mod_add_div]

/-- **Non-degeneracy at every generator**: `e(x, x) ≠ 1` for every `x ∈ G^*` (from
`e(g, g) ≠ 1` [BB04, §2.2, item 2], since every `x ∈ G^*` generates `G`).

**Proof sketch.** Write `x = g^k` with `k ≢ 0 (mod p)` (`x ≠ 1`). Then
`e(x, x) = e(g, g)^{k²}` by bilinearity. The element `e(g, g) ≠ 1` of the group `G_T` of prime
order `p` has order `p`, and `p ∤ k²` because `p` is prime and `p ∤ k`. -/
theorem pair_ne_one {x : B.G} (hx : x ≠ 1) : B.pair x x ≠ 1 := by
  obtain ⟨k, rfl⟩ := B.exists_pow_eq B.gen_ne_one x
  rw [B.bilinear_pow]
  intro h
  have ho : orderOf (B.pair B.gen B.gen) = B.order :=
    orderOf_eq_prime (B.pow_order_GT _) B.pair_gen_ne_one
  have hd : B.order ∣ k * k := ho ▸ orderOf_dvd_of_pow_eq_one h
  obtain ⟨j, rfl⟩ : B.order ∣ k := ((Nat.Prime.dvd_mul B.order_prime).1 hd).elim id id
  exact hx (by rw [pow_mul, B.pow_order, one_pow])

/-- **`a ↦ e(x, x)^a` is a bijection `Z_p → G_T`** for every `x ∈ G^*`: the law of `e(x, x)^z`
for uniform `z ∈ Z_p` is uniform on `G_T` (the identification of [BB04, §3.1]'s "`T` uniform in
`G_1`" with `e(g, g)^z`, `z` uniform, used by the proofs).

**Proof sketch.** `e(x, x) ≠ 1` (`pair_ne_one`) has prime order `p` in `G_T`, so
`a ↦ e(x, x)^{a.val}` is injective on `Z_p`; both sides have `p` elements (`card_GT`). -/
theorem pow_val_bijective {x : B.G} (hx : x ≠ 1) :
    Function.Bijective fun a : ZMod B.order => B.pair x x ^ a.val := by
  have ho : orderOf (B.pair x x) = B.order :=
    orderOf_eq_prime (B.pow_order_GT _) (B.pair_ne_one hx)
  rw [Fintype.bijective_iff_injective_and_card]
  refine ⟨fun a b hab => ZMod.val_injective _ ?_, by rw [ZMod.card, B.card_GT]⟩
  have h := pow_eq_pow_iff_modEq.1 hab
  rw [ho] at h
  exact Nat.ModEq.eq_of_lt_of_lt h (ZMod.val_lt a) (ZMod.val_lt b)

end BilinearGroup

/-- A **bilinear group generator**: a PPT `Gen(1^κ)` whose output, the *description* `d` of the
group, has `descLen(κ)` bits, and the bilinear group `group κ d` that `d` describes, with element
widths `wG(κ)` and `wT(κ)`. The form of [BB04, §2.2] ("`G` is a bilinear group") and of
[BB04, §4.1] ("the security parameter determines the size of `G`") in the asymptotic layer.

**Deviation:** the group is a total function of the description (every string describes some
bilinear group), so no validity predicate or threshold appears, unlike `Candidates.ExpGroupGen`;
descriptions have an exact polynomial length (a PPT generator can always pad its output to its
time bound). The order of the group is unconstrained here: results that need a large order
assume `OrderAtLeastExcept`. Efficient group operations are the separate contract
`BilinearGen.Ops`. -/
structure BilinearGen where
  /-- The generator `Gen(1^κ)`, run on the empty argument. -/
  gen : NUPPT
  /-- `Gen` is a PPT. -/
  gen_uniform : gen.Uniform
  /-- The length of a description. -/
  descLen : PolyExpr
  /-- Every description at parameter `κ` has `descLen(κ)` bits. -/
  desc_length : ∀ κ (r : gen.Coins κ), (gen.runAt κ [] r).length = descLen.eval κ
  /-- The width of the encoding of `G`. -/
  wG : PolyExpr
  /-- The width of the encoding of `G_T`. -/
  wT : PolyExpr
  /-- The bilinear group described by a string at parameter `κ`. -/
  group : (κ : ℕ) → List Bool → BilinearGroup (wG.eval κ) (wT.eval κ)

namespace BilinearGen

variable (G : BilinearGen)

/-- The description `d = Gen(1^κ; r)` output by the generator on the coins `r`. -/
def desc (κ : ℕ) (r : G.gen.Coins κ) : List Bool := G.gen.runAt κ [] r

/-- `G.desc κ r = G.gen.runAt κ [] r`. -/
theorem desc_eq (κ : ℕ) (r : G.gen.Coins κ) : G.desc κ r = G.gen.runAt κ [] r := rfl

/-- A description has `descLen(κ)` bits: `(G.desc κ r).length = G.descLen.eval κ`. -/
theorem length_desc (κ : ℕ) (r : G.gen.Coins κ) : (G.desc κ r).length = G.descLen.eval κ :=
  G.desc_length κ r

/-- The bilinear group generated on the coins `r`: `G.inst κ r = G.group κ (G.desc κ r)`. -/
def inst (κ : ℕ) (r : G.gen.Coins κ) : BilinearGroup (G.wG.eval κ) (G.wT.eval κ) :=
  G.group κ (G.desc κ r)

/-- `G.inst κ r = G.group κ (G.desc κ r)`. -/
theorem inst_eq (κ : ℕ) (r : G.gen.Coins κ) : G.inst κ r = G.group κ (G.desc κ r) := rfl

/-- **The order is at least `N(κ)` except with probability `δ(κ)`**: for every `κ`,
`Pr_r[|G| < N(κ)] ≤ δ(κ)` over the generator's coins `r`. With `N(κ) = 2^κ` and a negligible
`δ` this is "the security parameter determines the size of `G`" [BB04, §4.1]; with
`N(κ) = 2^{ℓ(κ)}` it makes `ℓ(κ)`-bit identities distinct in `Z_p` [BB04, §4.4, "`2^b < p`"].

**Deviation:** a strict PPT generator may fail with small probability, so a bound on every coin
string is not demanded (the lesson of `Candidates.ExpGroupGen.FullLengthExcept`, run-3 audit
P8-2). -/
def OrderAtLeastExcept (N : ℕ → ℕ) (δ : ℕ → ℝ) : Prop :=
  ∀ κ, uprob (fun r : G.gen.Coins κ => (G.inst κ r).order < N κ) ≤ δ κ

/-- `G.OrderAtLeastExcept N δ` iff for every `κ` the probability over the generator's coins that
the order is below `N κ` is at most `δ κ`. -/
theorem orderAtLeastExcept_iff (N : ℕ → ℕ) (δ : ℕ → ℝ) :
    G.OrderAtLeastExcept N δ ↔
      ∀ κ, uprob (fun r : G.gen.Coins κ => (G.inst κ r).order < N κ) ≤ δ κ :=
  Iff.rfl

end BilinearGen

end TCSlib.Cryptography.Pairing
```

## ===== TCSlib/Cryptography/Pairing/Assumptions.lean (Lean, at 110c2f9db810d243693b9a5e8976a5ad205f1bab) =====

```lean
/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TCSlib contributors
-/
import TCSlib.Cryptography.Pairing.Group
import TCSlib.Cryptography.Asymptotic.Adversary
import TCSlib.Cryptography.Games.Advantage
import TCSlib.Cryptography.Foundations.Negligible

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# The bilinear Diffie–Hellman assumptions

The *bilinear Diffie–Hellman* (BDH) problem [BB04, §3.1]: given `g, g^a, g^b, g^c ∈ G`, output
`e(g, g)^{abc} ∈ G_1`; and its decisional form (Decision BDH, DBDH): distinguish
`(g, g^a, g^b, g^c, e(g, g)^{abc})` (the distribution `P_BDH`) from `(g, g^a, g^b, g^c, T)` with
`T` uniform in `G_1` (the distribution `R_BDH`). In both, the generator `g` is uniform in
`G^* = G ∖ {1}`, the exponents `a, b, c` are uniform in `Z_p`, and the probability is also over
the adversary's coins. [BB04, §3.1] credits the BDH problem to [Jou00, SOK00, BF01].

**The experiments.** The bilinear group is drawn by the generator (`Pairing.BilinearGen`), and
the adversary is a non-uniform PPT machine (`Complexity.NUPPT`) that receives `1^κ` and the
string `⟨d, ⟨g, ⟨g^a, ⟨g^b, ⟨g^c, T⟩⟩⟩⟩⟩` of the description `d` and the encoded elements
(`tupleStr`; without `T` for BDH, `bdhStr`). The experiments are games of the `Games` framework
(`Games.ProbComp`): the generator's coins are drawn first, then `g`, the exponents and `T` from
the group they describe, then the adversary's coins. Sampling in sequence keeps the law of the
group the generator's law (a uniform seed over a dependent sum would not; run-3 audit P8-1 of
the DDH layer).

**Deviation:** [BB04, Definition 3.1] is concrete ("no `t`-time algorithm has advantage at least
`ε` in `G`"). Here the assumptions are asymptotic: every non-uniform PPT has negligible advantage
(BDH: success probability), relative to the generator. The decision advantage is the absolute
difference of acceptance probabilities (the paper writes the difference of the probabilities of
output `0`, without absolute value; the two are equivalent for the assumption since the negated
machine is a PPT). The adversary receives the group's description `d` and `1^κ`.

## Main definitions

* `TCSlib.Cryptography.Pairing.tupleStr`, `bdhStr` — the strings handed to the adversary.
* `BilinearGen.dbdhGame`, `BilinearGen.dbdhAdv`, `BilinearGen.DBDHAssumption` — the Decision BDH
  experiment, its advantage and the assumption [BB04, §3.1 and Definition 3.1].
* `BilinearGen.bdhGame`, `BilinearGen.BDHAssumption` — the BDH experiment and the assumption
  [BB04, §3.1 and Definition 3.1].

## Main results

* `BilinearGen.bdhAssumption_of_dbdhAssumption` — Decision BDH implies BDH when the order is
  at least `2^κ` except with negligible probability.

## References

* [BB04] D. Boneh, X. Boyen, *Efficient Selective-ID Secure Identity Based Encryption Without
  Random Oracles*, full version, Cryptology ePrint Archive, Report 2004/172, December 2004
  (extended abstract: EUROCRYPT 2004, LNCS 3027, pp. 223–238). §3.1 (pp. 4–5): the BDH and
  Decision BDH problems, Definition 3.1.
* [Jou00] A. Joux, *A One Round Protocol for Tripartite Diffie–Hellman*, ANTS-IV, LNCS 1838,
  pp. 385–393, Springer, 2000. §5 (p. 392): "some Diffie–Hellman like problem and
  Diffie–Hellman like decision problem should be hard in order to get security".
* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed., January 2010.
  (Definition 26.8, non-uniform PPT; Definition 69.4's convention that `A` receives `1^n`.)
-/

namespace TCSlib.Cryptography.Pairing

open Complexity Turing TCSlib.Cryptography.Games

/-- The **Decision BDH string** `⟨d, ⟨g, ⟨X, ⟨Y, ⟨Z, T⟩⟩⟩⟩⟩` of a description `d`, four elements
`g, X, Y, Z` of `G` and an element `T` of `G_T`, each written by its encoding. It is the input
`(g, g^a, g^b, g^c, T)` of a Decision BDH algorithm [BB04, §3.1], with the group's description
in front. -/
def tupleStr {wG wT : ℕ} (B : BilinearGroup wG wT) (d : List Bool) (g x y z : B.G) (t : B.GT) :
    List Bool :=
  pairEncode d (pairEncode (List.ofFn (B.encG g)) (pairEncode (List.ofFn (B.encG x))
    (pairEncode (List.ofFn (B.encG y)) (pairEncode (List.ofFn (B.encG z))
      (List.ofFn (B.encT t))))))

/-- `tupleStr B d g x y z t = ⟨d, ⟨g, ⟨x, ⟨y, ⟨z, t⟩⟩⟩⟩⟩` with the elements encoded. -/
theorem tupleStr_eq {wG wT : ℕ} (B : BilinearGroup wG wT) (d : List Bool) (g x y z : B.G)
    (t : B.GT) :
    tupleStr B d g x y z t =
      pairEncode d (pairEncode (List.ofFn (B.encG g)) (pairEncode (List.ofFn (B.encG x))
        (pairEncode (List.ofFn (B.encG y)) (pairEncode (List.ofFn (B.encG z))
          (List.ofFn (B.encT t)))))) := rfl

/-- The **BDH string** `⟨d, ⟨g, ⟨X, ⟨Y, Z⟩⟩⟩⟩`: the input `(g, g^a, g^b, g^c)` of a BDH algorithm
[BB04, §3.1], with the group's description in front. -/
def bdhStr {wG wT : ℕ} (B : BilinearGroup wG wT) (d : List Bool) (g x y z : B.G) : List Bool :=
  pairEncode d (pairEncode (List.ofFn (B.encG g)) (pairEncode (List.ofFn (B.encG x))
    (pairEncode (List.ofFn (B.encG y)) (List.ofFn (B.encG z)))))

/-- `bdhStr B d g x y z = ⟨d, ⟨g, ⟨x, ⟨y, z⟩⟩⟩⟩` with the elements encoded. -/
theorem bdhStr_eq {wG wT : ℕ} (B : BilinearGroup wG wT) (d : List Bool) (g x y z : B.G) :
    bdhStr B d g x y z =
      pairEncode d (pairEncode (List.ofFn (B.encG g)) (pairEncode (List.ofFn (B.encG x))
        (pairEncode (List.ofFn (B.encG y)) (List.ofFn (B.encG z))))) := rfl

namespace BilinearGen

variable (G : BilinearGen)

/-- **The Decision BDH experiment** [BB04, §3.1] for the distinguisher `D` at parameter `κ`:
draw the generator's coins `r` (group `B = G.inst κ r`, description `d`), a generator
`g ∈ G^*`, exponents `a, b, c ∈ Z_p`, an element `T ∈ G_T` and `D`'s coins `ρ`, all uniform, and
return `D(1^κ, ⟨d, ⟨g, g^a, g^b, g^c, T'⟩⟩; ρ)`, where `T' = e(g, g)^{abc}` when `real` (the
distribution `P_BDH`) and `T' = T` otherwise (`R_BDH`). -/
noncomputable def dbdhGame (D : NUPPT) (real : Bool) (κ : ℕ) : ProbComp Bool :=
  (ProbComp.sample (G.gen.Coins κ)).bind fun r =>
  (ProbComp.sample {x : (G.inst κ r).G // x ≠ 1}).bind fun g =>
  (ProbComp.sample (ZMod (G.inst κ r).order × ZMod (G.inst κ r).order ×
    ZMod (G.inst κ r).order)).bind fun abc =>
  (ProbComp.sample (G.inst κ r).GT).bind fun t =>
  (ProbComp.sample (D.Coins κ)).bind fun ρ =>
    .pure (D.distinguisherL κ (tupleStr (G.inst κ r) (G.desc κ r) g.1 (g.1 ^ abc.1.val)
      (g.1 ^ abc.2.1.val) (g.1 ^ abc.2.2.val)
      (if real then (G.inst κ r).pair g.1 g.1 ^ (abc.1 * abc.2.1 * abc.2.2).val else t)) ρ)

/-- The Decision BDH experiment draws the generator's coins, `g ∈ G^*`, `(a, b, c) ∈ Z_p³`,
`T ∈ G_T` and the distinguisher's coins, and runs the distinguisher on
`tupleStr B d g g^a g^b g^c T'` with `T' = e(g, g)^{abc}` if `real` and `T' = T` otherwise. -/
theorem dbdhGame_eq (D : NUPPT) (real : Bool) (κ : ℕ) :
    G.dbdhGame D real κ =
      (ProbComp.sample (G.gen.Coins κ)).bind fun r =>
      (ProbComp.sample {x : (G.inst κ r).G // x ≠ 1}).bind fun g =>
      (ProbComp.sample (ZMod (G.inst κ r).order × ZMod (G.inst κ r).order ×
        ZMod (G.inst κ r).order)).bind fun abc =>
      (ProbComp.sample (G.inst κ r).GT).bind fun t =>
      (ProbComp.sample (D.Coins κ)).bind fun ρ =>
        .pure (D.distinguisherL κ (tupleStr (G.inst κ r) (G.desc κ r) g.1 (g.1 ^ abc.1.val)
          (g.1 ^ abc.2.1.val) (g.1 ^ abc.2.2.val)
          (if real then (G.inst κ r).pair g.1 g.1 ^ (abc.1 * abc.2.1 * abc.2.2).val else t)) ρ) :=
  rfl

/-- **The Decision BDH advantage** of `D` at `κ`:
`|Pr[D(P_BDH) = 1] − Pr[D(R_BDH) = 1]|` [BB04, §3.1]. -/
noncomputable def dbdhAdv (D : NUPPT) (κ : ℕ) : ℝ :=
  advantage (G.dbdhGame D false κ) (G.dbdhGame D true κ)

/-- `G.dbdhAdv D κ = advantage (G.dbdhGame D false κ) (G.dbdhGame D true κ)`. -/
theorem dbdhAdv_eq (D : NUPPT) (κ : ℕ) :
    G.dbdhAdv D κ = advantage (G.dbdhGame D false κ) (G.dbdhGame D true κ) := rfl

/-- **The Decision BDH assumption** relative to the generator `G` [BB04, §3.1 and
Definition 3.1]: every non-uniform PPT distinguisher has negligible Decision BDH advantage.

**Deviation:** asymptotic, relative to a generator, against non-uniform PPT machines that
receive `1^κ` and the description (module docstring). -/
def DBDHAssumption : Prop := ∀ D : NUPPT, Negligible fun κ => G.dbdhAdv D κ

/-- `G.DBDHAssumption` iff `κ ↦ G.dbdhAdv D κ` is negligible for every non-uniform PPT `D`. -/
theorem dbdhAssumption_iff : G.DBDHAssumption ↔ ∀ D : NUPPT, Negligible fun κ => G.dbdhAdv D κ :=
  Iff.rfl

/-- **The BDH experiment** [BB04, §3.1] for the machine `A` at parameter `κ`: draw the
generator's coins `r`, a generator `g ∈ G^*`, exponents `a, b, c ∈ Z_p` and `A`'s coins `ρ`, all
uniform, and accept iff `A(1^κ, ⟨d, ⟨g, g^a, g^b, g^c⟩⟩; ρ)` is the encoding of `e(g, g)^{abc}`. -/
noncomputable def bdhGame (A : NUPPT) (κ : ℕ) : ProbComp Bool :=
  (ProbComp.sample (G.gen.Coins κ)).bind fun r =>
  (ProbComp.sample {x : (G.inst κ r).G // x ≠ 1}).bind fun g =>
  (ProbComp.sample (ZMod (G.inst κ r).order × ZMod (G.inst κ r).order ×
    ZMod (G.inst κ r).order)).bind fun abc =>
  (ProbComp.sample (A.Coins κ)).bind fun ρ =>
    .pure (decide (A.runAt κ (bdhStr (G.inst κ r) (G.desc κ r) g.1 (g.1 ^ abc.1.val)
      (g.1 ^ abc.2.1.val) (g.1 ^ abc.2.2.val)) ρ =
        List.ofFn ((G.inst κ r).encT
          ((G.inst κ r).pair g.1 g.1 ^ (abc.1 * abc.2.1 * abc.2.2).val))))

/-- The BDH experiment draws the generator's coins, `g ∈ G^*`, `(a, b, c) ∈ Z_p³` and the
machine's coins, and accepts iff the machine's output on `bdhStr B d g g^a g^b g^c` is the
encoding of `e(g, g)^{abc}`. -/
theorem bdhGame_eq (A : NUPPT) (κ : ℕ) :
    G.bdhGame A κ =
      (ProbComp.sample (G.gen.Coins κ)).bind fun r =>
      (ProbComp.sample {x : (G.inst κ r).G // x ≠ 1}).bind fun g =>
      (ProbComp.sample (ZMod (G.inst κ r).order × ZMod (G.inst κ r).order ×
        ZMod (G.inst κ r).order)).bind fun abc =>
      (ProbComp.sample (A.Coins κ)).bind fun ρ =>
        .pure (decide (A.runAt κ (bdhStr (G.inst κ r) (G.desc κ r) g.1 (g.1 ^ abc.1.val)
          (g.1 ^ abc.2.1.val) (g.1 ^ abc.2.2.val)) ρ =
            List.ofFn ((G.inst κ r).encT
              ((G.inst κ r).pair g.1 g.1 ^ (abc.1 * abc.2.1 * abc.2.2).val)))) :=
  rfl

/-- **The BDH assumption** relative to the generator `G` [BB04, §3.1 and Definition 3.1]: every
non-uniform PPT machine solves the BDH problem with negligible probability.

**Deviation:** asymptotic, relative to a generator, against non-uniform PPT machines that
receive `1^κ` and the description; the answer must be the encoding of `e(g, g)^{abc}` exactly. -/
def BDHAssumption : Prop := ∀ A : NUPPT, Negligible fun κ => accept (G.bdhGame A κ)

/-- `G.BDHAssumption` iff `κ ↦ Pr[G.bdhGame A κ = 1]` is negligible for every non-uniform
PPT `A`. -/
theorem bdhAssumption_iff :
    G.BDHAssumption ↔ ∀ A : NUPPT, Negligible fun κ => accept (G.bdhGame A κ) := Iff.rfl

/-- **Decision BDH implies BDH** when the group order is at least `2^κ` except with negligible
probability: a BDH solver `A` gives the Decision BDH distinguisher "run `A` on `(g, g^a, g^b, g^c)`
and accept iff its answer is `T`".

**Source:** not stated in [BB04] or [Jou00]; [BB04, §3.1] defines both problems and calls the
decision form the stronger assumption implicitly by using it. The implication is the standard
remark that deciding is no harder than computing.

**Proof sketch.** Given `A`, let `D(1^κ, ⟨s, T⟩)` run `A(1^κ, s)` with its own coins and accept
iff the answer equals the encoding of `T`, where `s` is re-paired from the first five components
(a polynomial-time string map, so `D` is a non-uniform PPT). On `P_BDH`, `D` accepts exactly when
`A` succeeds, so `Pr[D(P_BDH) = 1] = Pr[A wins]`. On `R_BDH`, `T` is uniform in `G_T` and
independent of `A`'s view, so `Pr[D(R_BDH) = 1] ≤ 1/p` by injectivity of the encoding. Hence
`Pr[A wins] ≤ dbdhAdv D κ + E_r[1/p] ≤ dbdhAdv D κ + 2^{-κ} + δ(κ)` (the coins where `p < 2^κ`
cost at most `δ(κ)`), a sum of negligible functions. -/
theorem bdhAssumption_of_dbdhAssumption
    (hN : ∃ δ : ℕ → ℝ, Negligible δ ∧ G.OrderAtLeastExcept (fun κ => 2 ^ κ) δ)
    (h : G.DBDHAssumption) : G.BDHAssumption := by
  sorry

end BilinearGen

end TCSlib.Cryptography.Pairing
```

## ===== TCSlib/Cryptography/Pairing/Operations.lean (Lean, at 110c2f9db810d243693b9a5e8976a5ad205f1bab) =====

```lean
/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TCSlib contributors
-/
import TCSlib.Cryptography.Pairing.Group
import TCSlib.Cryptography.Candidates.Arithmetic

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Efficient group operations of a bilinear group generator

[BB04, §2.2]: "`G` is a bilinear group if the group action in `G` can be computed efficiently and
there exists a group `G_1` and an efficiently computable bilinear map `e`". A `BilinearGen` keeps
its groups abstract (`Pairing/Group.lean`); this file states the efficiency half of the
definition as a separate contract, `BilinearGen.Ops`: polynomial-time string functions that, on
every generated description `d`, compute on the encodings of the elements of the group `d`
describes.

The contract is a hypothesis only of the results whose reductions compute in the group (the
security of BB1, `AdvancedEncryption.IdentityBased.bb1_sidSecure`). It reads exponents and the
order as binary numerals with `NumberTheory.listToNat`, the convention of the arithmetic bundle
`Candidates.ArithmeticFP` (D11), so that a reduction can do its exponent arithmetic modulo `p`
with that bundle.

## Main definitions

* `TCSlib.Cryptography.Pairing.BilinearGen.Ops` — the order, multiplication and exponentiation in
  `G`, the pairing, multiplication in `G_T` and the membership test of `G_T`, as polynomial-time
  string functions with their specifications at generated descriptions.

## Main results

None: the contract is a hypothesis, read through its fields.

## References

* [BB04] D. Boneh, X. Boyen, *Efficient Selective-ID Secure Identity Based Encryption Without
  Random Oracles*, full version, Cryptology ePrint Archive, Report 2004/172, December 2004
  (extended abstract: EUROCRYPT 2004, LNCS 3027, pp. 223–238). §2.2 (p. 4).
* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed., January 2010.
  (Definition 23.5, polynomial-time computation.)
-/

namespace TCSlib.Cryptography.Pairing

open Complexity Turing TCSlib.Cryptography.NumberTheory

namespace BilinearGen

/-- **Efficient operations of a bilinear group generator** [BB04, §2.2, "the group action in `G`
can be computed efficiently … an efficiently computable bilinear map `e`"]: polynomial-time
string functions that, on every generated description `d = G.desc κ r` and the encodings of
elements `x, y ∈ G`, `u, v ∈ G_T`, compute
* the order `p`, as a binary numeral (`orderStr d`);
* `x · y` from `⟨d, ⟨x, y⟩⟩` (`mulG`) and `x^n` from `⟨d, ⟨x, n⟩⟩` for any numeral `n` (`powG`);
* `e(x, y)` from `⟨d, ⟨x, y⟩⟩` (`pairStr`);
* `u · v` from `⟨d, ⟨u, v⟩⟩` (`mulT`);
* whether a `wT(κ)`-bit string `w` encodes an element of `G_T`, from `⟨d, w⟩` (`memT`).

**Deviation:** the paper asks for efficient group operations and pairing; the order, the
membership test of `G_T` and numeral exponents are the minimal extras a machine needs to sample
exponents in `Z_p` and to read messages of `G_T` sent by an adversary. Inputs that are not of
these forms are unconstrained. Inversion is `x^{p−1}`. -/
structure Ops (G : BilinearGen) where
  /-- The order `p` of the described group, as a binary numeral. -/
  orderStr : List Bool → List Bool
  /-- Multiplication in `G` on `⟨d, ⟨x, y⟩⟩`. -/
  mulG : List Bool → List Bool
  /-- Exponentiation in `G` on `⟨d, ⟨x, n⟩⟩`, `n` a binary numeral. -/
  powG : List Bool → List Bool
  /-- The pairing on `⟨d, ⟨x, y⟩⟩`. -/
  pairStr : List Bool → List Bool
  /-- Multiplication in `G_T` on `⟨d, ⟨u, v⟩⟩`. -/
  mulT : List Bool → List Bool
  /-- The membership test of `G_T` on `⟨d, w⟩`. -/
  memT : List Bool → List Bool
  /-- `orderStr` is polynomial-time. -/
  orderStr_poly : PolyTimeComputable orderStr
  /-- `mulG` is polynomial-time. -/
  mulG_poly : PolyTimeComputable mulG
  /-- `powG` is polynomial-time. -/
  powG_poly : PolyTimeComputable powG
  /-- `pairStr` is polynomial-time. -/
  pairStr_poly : PolyTimeComputable pairStr
  /-- `mulT` is polynomial-time. -/
  mulT_poly : PolyTimeComputable mulT
  /-- `memT` is polynomial-time. -/
  memT_poly : PolyTimeComputable memT
  /-- `orderStr d` reads as the order of the described group. -/
  orderStr_spec : ∀ κ (r : G.gen.Coins κ), listToNat (orderStr (G.desc κ r)) = (G.inst κ r).order
  /-- `mulG ⟨d, ⟨x, y⟩⟩` is the encoding of `x · y`. -/
  mulG_spec : ∀ κ (r : G.gen.Coins κ) (x y : (G.inst κ r).G),
    mulG (pairEncode (G.desc κ r) (pairEncode (List.ofFn ((G.inst κ r).encG x))
      (List.ofFn ((G.inst κ r).encG y)))) = List.ofFn ((G.inst κ r).encG (x * y))
  /-- `powG ⟨d, ⟨x, n⟩⟩` is the encoding of `x^n`, `n` read as a binary numeral. -/
  powG_spec : ∀ κ (r : G.gen.Coins κ) (x : (G.inst κ r).G) (n : List Bool),
    powG (pairEncode (G.desc κ r) (pairEncode (List.ofFn ((G.inst κ r).encG x)) n)) =
      List.ofFn ((G.inst κ r).encG (x ^ listToNat n))
  /-- `pairStr ⟨d, ⟨x, y⟩⟩` is the encoding of `e(x, y)`. -/
  pairStr_spec : ∀ κ (r : G.gen.Coins κ) (x y : (G.inst κ r).G),
    pairStr (pairEncode (G.desc κ r) (pairEncode (List.ofFn ((G.inst κ r).encG x))
      (List.ofFn ((G.inst κ r).encG y)))) = List.ofFn ((G.inst κ r).encT ((G.inst κ r).pair x y))
  /-- `mulT ⟨d, ⟨u, v⟩⟩` is the encoding of `u · v`. -/
  mulT_spec : ∀ κ (r : G.gen.Coins κ) (u v : (G.inst κ r).GT),
    mulT (pairEncode (G.desc κ r) (pairEncode (List.ofFn ((G.inst κ r).encT u))
      (List.ofFn ((G.inst κ r).encT v)))) = List.ofFn ((G.inst κ r).encT (u * v))
  /-- `memT ⟨d, w⟩` is `[true]` iff `w` encodes an element of `G_T`, and `[false]` otherwise. -/
  memT_spec : ∀ κ (r : G.gen.Coins κ) (w : Fin (G.wT.eval κ) → Bool),
    memT (pairEncode (G.desc κ r) (List.ofFn w)) = [decide (∃ u, (G.inst κ r).encT u = w)]

end BilinearGen

end TCSlib.Cryptography.Pairing
```

## ===== TCSlib/Cryptography/KeyExchange/Joux.lean (Lean, at 110c2f9db810d243693b9a5e8976a5ad205f1bab) =====

```lean
/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TCSlib contributors
-/
import TCSlib.Cryptography.Pairing.Assumptions

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Joux's one-round tripartite Diffie–Hellman

[Jou00, §3]: three participants `A`, `B`, `C` share a group with a pairing and a public point.
Each picks a random exponent (`a`, `b`, `c`), broadcasts the multiple of the point once (one round,
`P_A = aP`, `P_B = bP`, `P_C = cP`), and computes the common key with
`F(x, P, Q) = e(P, Q)^x`: `K = F(a, P_B, P_C) = F(b, P_A, P_C) = F(c, P_A, P_B) = F(1, P, P)^{abc}`
[Jou00, p. 388]. In multiplicative notation, with the generator `g`: the messages are `g^a`,
`g^b`, `g^c`, and each key is `e(g^b, g^c)^a = e(g^a, g^c)^b = e(g^a, g^b)^c = e(g, g)^{abc}`.

**The single-point form.** [Jou00, §3] notes that with the Weil pairing on one point
`e_n(P, P) = 1`, so the key would be constant, and therefore uses two independent points `P`, `Q`
and the Tate pairing. In a symmetric bilinear group as defined in [BB04, §2.2], non-degeneracy is
`e(g, g) ≠ 1`, so the paper's first formula `F_W(x, P, Q) = e(P, Q)^x` already gives a
non-constant key, and one point suffices. This file formalizes that single-point form over the
abstract groups of `Pairing.BilinearGroup`.

**Security.** [Jou00, §5] gives no theorem; it says that "some Diffie–Hellman like problem and
Diffie–Hellman like decision problem should be hard in order to get security". The key
indistinguishability theorem here takes that decision problem to be Decision BDH [BB04, §3.1]:
an eavesdropper who sees the public point and the three broadcasts cannot tell the common key
from a uniform element of `G_T`.

**Deviation:** abstract symmetric bilinear groups (no curve, no Weil or Tate pairing); one public
point instead of two; multiplicative notation; the public point `g` is uniform in `G^*` (the
paper fixes "some point `P`"), the distribution under which [BB04, §3.1] states Decision BDH;
exponents in `Z_p`; security is the maintainer's formalization of [Jou00, §5]'s remark.

## Main definitions

* `TCSlib.Cryptography.KeyExchange.jouxMsg` — a participant's broadcast `g^x`.
* `TCSlib.Cryptography.KeyExchange.jouxKey` — the key `F(x, X, Y) = e(X, Y)^x`.
* `jouxGame`, `jouxAdv`, `JouxKeyIndist` — key indistinguishability for an eavesdropper.

## Main results

* `TCSlib.Cryptography.KeyExchange.jouxKey_eq` — every participant's key is `e(g, g)^{abc}`.
* `TCSlib.Cryptography.KeyExchange.joux_correct` — the three participants agree.
* `TCSlib.Cryptography.KeyExchange.jouxGame_eq_dbdhGame` — the eavesdropper's experiments are
  Decision BDH experiments.
* `TCSlib.Cryptography.KeyExchange.jouxKeyIndist_of_dbdhAssumption` — key indistinguishability
  under Decision BDH.

## References

* [Jou00] A. Joux, *A One Round Protocol for Tripartite Diffie–Hellman*, ANTS-IV, LNCS 1838,
  pp. 385–393, Springer, 2000. §3 (pp. 387–388): the protocol and `F_W`; §5 (pp. 391–392):
  security issues.
* [BB04] D. Boneh, X. Boyen, *Efficient Selective-ID Secure Identity Based Encryption Without
  Random Oracles*, full version, Cryptology ePrint Archive, Report 2004/172, December 2004
  (extended abstract: EUROCRYPT 2004, LNCS 3027, pp. 223–238). §2.2 (bilinear groups), §3.1
  (Decision BDH).
-/

namespace TCSlib.Cryptography.KeyExchange

open Complexity Turing TCSlib.Cryptography.Games TCSlib.Cryptography.Pairing

variable {wG wT : ℕ} (B : BilinearGroup wG wT)

/-- **A participant's broadcast** [Jou00, §3, `P_A = aP`]: the power `g^x` of the public
generator `g` by the participant's secret exponent `x ∈ Z_p`. -/
def jouxMsg (g : B.G) (x : ZMod B.order) : B.G := g ^ x.val

/-- `jouxMsg B g x = g ^ x.val`. -/
theorem jouxMsg_eq (g : B.G) (x : ZMod B.order) : jouxMsg B g x = g ^ x.val := rfl

/-- **A participant's key** [Jou00, §3, `F_W(x, P, Q) = e_n(P, Q)^x`]: from its secret exponent
`x` and the two other broadcasts `X`, `Y`, the key `e(X, Y)^x`. Participant `A` computes
`jouxKey B a P_B P_C`, `B` computes `jouxKey B b P_A P_C`, `C` computes `jouxKey B c P_A P_B`. -/
def jouxKey (x : ZMod B.order) (X Y : B.G) : B.GT := B.pair X Y ^ x.val

/-- `jouxKey B x X Y = e(X, Y) ^ x.val`. -/
theorem jouxKey_eq_pow (x : ZMod B.order) (X Y : B.G) : jouxKey B x X Y = B.pair X Y ^ x.val :=
  rfl

/-- Exponents of `G_T` multiply through `Z_p`: `u^{(abc mod p)} = u^{a b c}` with the
representatives `a.val, b.val, c.val`. -/
theorem pow_val_mul_mul (u : B.GT) (a b c : ZMod B.order) :
    u ^ (a * b * c).val = u ^ (a.val * b.val * c.val) := by
  rw [B.pow_val_mul_GT, pow_mul, B.pow_val_mul_GT, ← pow_mul]

/-- **The common key** [Jou00, p. 388, `F_W(a, P_B, P_C) = F_W(1, P, P)^{abc}`]: participant `A`'s
key `e(g^b, g^c)^a` is `e(g, g)^{abc}`. -/
theorem jouxKey_eq (g : B.G) (a b c : ZMod B.order) :
    jouxKey B a (jouxMsg B g b) (jouxMsg B g c) = B.pair g g ^ (a * b * c).val := by
  rw [jouxKey_eq_pow, jouxMsg_eq, jouxMsg_eq, B.bilinear_pow, pow_val_mul_mul, ← pow_mul]
  congr 1
  ring

/-- **Correctness: the three participants agree** [Jou00, p. 388,
`F_W(a, P_B, P_C) = F_W(b, P_A, P_C) = F_W(c, P_A, P_B)`]: `e(g^b, g^c)^a = e(g^a, g^c)^b` and
`e(g^a, g^c)^b = e(g^a, g^b)^c`. -/
theorem joux_correct (g : B.G) (a b c : ZMod B.order) :
    jouxKey B a (jouxMsg B g b) (jouxMsg B g c) = jouxKey B b (jouxMsg B g a) (jouxMsg B g c) ∧
      jouxKey B b (jouxMsg B g a) (jouxMsg B g c) =
        jouxKey B c (jouxMsg B g a) (jouxMsg B g b) := by
  refine ⟨?_, ?_⟩ <;> rw [jouxKey_eq, jouxKey_eq] <;> congr 2 <;> ring

/-- **The key-indistinguishability experiment** for the eavesdropper `A` at parameter `κ`: draw
the generator's coins `r` (group `B`, description `d`), the public generator `g ∈ G^*`, the
secret exponents `a, b, c ∈ Z_p`, a uniform `K ∈ G_T` and `A`'s coins `ρ`; give `A` the
description, the public generator, the three broadcasts and either the common key
`e(g^b, g^c)^a` (`real`) or `K`, in the string format of Decision BDH (`tupleStr`). -/
noncomputable def jouxGame (G : BilinearGen) (A : NUPPT) (real : Bool) (κ : ℕ) : ProbComp Bool :=
  (ProbComp.sample (G.gen.Coins κ)).bind fun r =>
  (ProbComp.sample {x : (G.inst κ r).G // x ≠ 1}).bind fun g =>
  (ProbComp.sample (ZMod (G.inst κ r).order × ZMod (G.inst κ r).order ×
    ZMod (G.inst κ r).order)).bind fun abc =>
  (ProbComp.sample (G.inst κ r).GT).bind fun K =>
  (ProbComp.sample (A.Coins κ)).bind fun ρ =>
    .pure (A.distinguisherL κ (tupleStr (G.inst κ r) (G.desc κ r) g.1
      (jouxMsg (G.inst κ r) g.1 abc.1) (jouxMsg (G.inst κ r) g.1 abc.2.1)
      (jouxMsg (G.inst κ r) g.1 abc.2.2)
      (if real then jouxKey (G.inst κ r) abc.1 (jouxMsg (G.inst κ r) g.1 abc.2.1)
        (jouxMsg (G.inst κ r) g.1 abc.2.2) else K)) ρ)

/-- The key-indistinguishability experiment draws the generator's coins, `g ∈ G^*`,
`(a, b, c) ∈ Z_p³`, `K ∈ G_T` and the eavesdropper's coins, and runs the eavesdropper on the
transcript `g, g^a, g^b, g^c` with `A`'s key if `real` and `K` otherwise. -/
theorem jouxGame_eq (G : BilinearGen) (A : NUPPT) (real : Bool) (κ : ℕ) :
    jouxGame G A real κ =
      (ProbComp.sample (G.gen.Coins κ)).bind fun r =>
      (ProbComp.sample {x : (G.inst κ r).G // x ≠ 1}).bind fun g =>
      (ProbComp.sample (ZMod (G.inst κ r).order × ZMod (G.inst κ r).order ×
        ZMod (G.inst κ r).order)).bind fun abc =>
      (ProbComp.sample (G.inst κ r).GT).bind fun K =>
      (ProbComp.sample (A.Coins κ)).bind fun ρ =>
        .pure (A.distinguisherL κ (tupleStr (G.inst κ r) (G.desc κ r) g.1
          (jouxMsg (G.inst κ r) g.1 abc.1) (jouxMsg (G.inst κ r) g.1 abc.2.1)
          (jouxMsg (G.inst κ r) g.1 abc.2.2)
          (if real then jouxKey (G.inst κ r) abc.1 (jouxMsg (G.inst κ r) g.1 abc.2.1)
            (jouxMsg (G.inst κ r) g.1 abc.2.2) else K)) ρ) :=
  rfl

/-- **Each key-indistinguishability experiment is a Decision BDH experiment**: with the key
`e(g^b, g^c)^a = e(g, g)^{abc}` (`jouxKey_eq`) the transcript and key are drawn from `P_BDH`, and
with a uniform `K` from `R_BDH`, in the same string format, so
`jouxGame G A real κ = G.dbdhGame A real κ`. -/
theorem jouxGame_eq_dbdhGame (G : BilinearGen) (A : NUPPT) (real : Bool) (κ : ℕ) :
    jouxGame G A real κ = G.dbdhGame A real κ := by
  rw [jouxGame_eq, BilinearGen.dbdhGame_eq]
  simp only [jouxKey_eq]
  rfl

/-- **The eavesdropper's advantage** at `κ`: `|Pr[A(transcript, K) = 1] − Pr[A(transcript,
key) = 1]|`. -/
noncomputable def jouxAdv (G : BilinearGen) (A : NUPPT) (κ : ℕ) : ℝ :=
  advantage (jouxGame G A false κ) (jouxGame G A true κ)

/-- `jouxAdv G A κ = advantage (jouxGame G A false κ) (jouxGame G A true κ)`. -/
theorem jouxAdv_eq (G : BilinearGen) (A : NUPPT) (κ : ℕ) :
    jouxAdv G A κ = advantage (jouxGame G A false κ) (jouxGame G A true κ) := rfl

/-- **Key indistinguishability of Joux's protocol** relative to the generator `G`: every
non-uniform PPT eavesdropper has negligible advantage in telling the common key from a uniform
element of `G_T`, given the public generator and the three broadcasts. The security goal of
[Jou00, §3] ("this common value `K_{A,B,C}` will be hard to compute given `P_A`, `P_B` and `P_C`"),
in its decisional form [Jou00, §5]. -/
def JouxKeyIndist (G : BilinearGen) : Prop := ∀ A : NUPPT, Negligible fun κ => jouxAdv G A κ

/-- `JouxKeyIndist G` iff `κ ↦ jouxAdv G A κ` is negligible for every non-uniform PPT `A`. -/
theorem jouxKeyIndist_iff (G : BilinearGen) :
    JouxKeyIndist G ↔ ∀ A : NUPPT, Negligible fun κ => jouxAdv G A κ := Iff.rfl

/-- **Joux's protocol has indistinguishable keys under Decision BDH** ([Jou00, §5] with the
decision problem of [BB04, §3.1]).

**Source:** [Jou00] states no theorem; this is the formal version of its §5 requirement
(module docstring).

The eavesdropper is itself the Decision BDH distinguisher: `jouxAdv G A κ = G.dbdhAdv A κ`
(`jouxGame_eq_dbdhGame`). -/
theorem jouxKeyIndist_of_dbdhAssumption (G : BilinearGen) (h : G.DBDHAssumption) :
    JouxKeyIndist G := by
  intro A
  have hfun : (fun κ => jouxAdv G A κ) = fun κ => G.dbdhAdv A κ := funext fun κ => by
    rw [jouxAdv_eq, BilinearGen.dbdhAdv_eq, jouxGame_eq_dbdhGame, jouxGame_eq_dbdhGame]
  rw [hfun]
  exact G.dbdhAssumption_iff.1 h A

end TCSlib.Cryptography.KeyExchange
```

## ===== TCSlib/Cryptography/AdvancedEncryption/IdentityBased/Defs.lean (Lean, at 110c2f9db810d243693b9a5e8976a5ad205f1bab) =====

```lean
/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TCSlib contributors
-/
import TCSlib.Cryptography.Encryption.PrivateKey.OracleSecurity
import TCSlib.Cryptography.Games.Machines

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Identity-based encryption and selective-identity security

An *identity-based encryption* (IBE) system [BB04, §2.1] consists of four algorithms: `Setup`
generates the system parameters `params` and a master key; `KeyGen` uses the master key to
generate the private key `d_ID` of an identity `ID`; `Encrypt` encrypts a message for an identity
using the parameters; `Decrypt` decrypts with a private key.

*Selective-identity chosen-plaintext security* (IND-sID-CPA, [BB04, §2.1, the game and
Definition 2.2]): the adversary first commits to the identity `ID*` it will attack (**Init**);
the challenger runs `Setup` and gives it `params` (**Setup**); the adversary adaptively asks for
the private keys of identities `ID ≠ ID*` (**Phase 1**); it outputs two messages `M₀, M₁` of the
message space and receives `Encrypt(params, ID*, M_b)` (**Challenge**); it asks more private-key
queries (**Phase 2**) and outputs a guess `b'` (**Guess**). There are no decryption queries.

**The scheme interface.** The algorithms are probabilistic computations of the `Games` framework
over typed parameters, keys and ciphertexts (`IBEScheme`). Identities are `idLen(κ)`-bit strings
and messages arrive as `msgLen(κ)`-bit strings; a scheme declares which strings are messages for
given parameters (`MsgSpace`, the paper's message space `M`). For the adversary, parameters,
private keys and ciphertexts are written as fixed-width strings (`encPP`, `encSK`, `encCT`).

**The game's encoding.** As in the public-key games (`Encryption.PublicKey.OracleSecurity`), one
non-uniform PPT machine plays every phase against bit-string oracles (`Games.bitCodec`):
* `Init` (oracle 0) takes `ID*` and answers `params`. The first query fixes `ID*`; later queries
  repeat `params` and leave `ID*` unchanged.
* `KeyGen` (oracle 1) takes `ID` and answers `⟨1, d_ID⟩` with fresh `KeyGen` coins when `ID*` is
  fixed and `ID ≠ ID*`, and `⊥` (all `false`) otherwise.
* `Challenge` (oracle 2) takes `⟨M₀, M₁⟩` and answers `Encrypt(params, ID*, M_b)` the first time
  it is asked with `ID*` fixed and `M₀, M₁ ∈ M`, recording it; later it repeats the recorded
  challenge; it answers `⊥` before `Init` and on messages outside `M`.
The machine starts with input `1^κ` only, so the only information it has before committing is
its coins. `Setup` is run before the machine starts; since nothing about `params` reaches the
machine before its `Init` query, this is the order of [BB04, §2.1] in distribution.

**Deviation:** [BB04, Definition 2.2] is concrete (`(t, q_ID, ε)`) and measures
`|Pr[b = b'] − 1/2|`; here security is asymptotic, for every non-uniform PPT and every polynomial
query budget, and the advantage is `|Pr[b' = 1 | b = 0] − Pr[b' = 1 | b = 1]|`, twice the
paper's (`Games.guessAdv_eq_half_advantage`). Queries to `KeyGen` for `ID*` and challenges outside
`M` are answered `⊥` instead of being forbidden. The algorithms are typed probabilistic
computations; their efficiency is not part of the interface (per-scheme contracts).

## Main definitions

* `TCSlib.Cryptography.AdvancedEncryption.IdentityBased.IBEScheme` — an IBE system [BB04, §2.1].
* `IBEScheme.Correct` — perfect correctness on the message space.
* `IBEScheme.sidSpec`, `IBEScheme.sidImpl`, `IBEScheme.sidGame`, `IBEScheme.SIDSecure` — the
  IND-sID-CPA game and security [BB04, §2.1 and Definition 2.2].
* `IBEScheme.oracleImpl` — the three oracles from typed handlers (for simulators).

## Main results

* `IBEScheme.sidImpl_init_none`, `sidImpl_init_some`, `sidImpl_keyGen_none`,
  `sidImpl_keyGen_target`, `sidImpl_keyGen_ne`, `sidImpl_challenge_none`,
  `sidImpl_challenge_repeat`, `sidImpl_challenge_fresh`, `sidImpl_challenge_invalid` — the
  oracles case by case; `oracleImpl_zero`, `oracleImpl_one`, `oracleImpl_two`.
* `IBEScheme.honestRun_eq`, `correct_iff`, `sidGame_eq`, `sidSecure_iff` — the experiments and
  predicates through their published equations.

## References

* [BB04] D. Boneh, X. Boyen, *Efficient Selective-ID Secure Identity Based Encryption Without
  Random Oracles*, full version, Cryptology ePrint Archive, Report 2004/172, December 2004
  (extended abstract: EUROCRYPT 2004, LNCS 3027, pp. 223–238). §2.1 (pp. 2–4): IBE systems, the
  selective identity game, Definitions 2.1 and 2.2.
* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed., January 2010.
  (Definition 26.8, non-uniform PPT; the one-machine encoding of the games of §7.1.4.)
-/

namespace TCSlib.Cryptography.AdvancedEncryption.IdentityBased

open Complexity Turing TCSlib.Cryptography.Games TCSlib.Cryptography.Composability

/-- An **identity-based encryption system** [BB04, §2.1]: at each security parameter `κ`, types of
system parameters `PP κ`, master keys `MSK κ`, private keys `SK κ` and ciphertexts `CT κ`, and
* `setup κ`, a probabilistic computation of `(params, master-key)`;
* `keyGen κ msk ID`, a probabilistic computation of the private key `d_ID` of the `idLen(κ)`-bit
  identity `ID`;
* `enc κ params ID M`, a probabilistic computation of a ciphertext of the `msgLen(κ)`-bit message
  `M` for `ID`;
* `dec κ d_ID C`, the deterministic decryption, `none` for `⊥`;
* the message space `MsgSpace κ params` (the paper's `M`), and fixed-width encodings of
  parameters, private keys and ciphertexts for the adversary.

**Deviation:** messages are strings with a parameter-dependent message space (as for El Gamal,
`Candidates.GroupPKScheme`); the algorithms are typed probabilistic computations, without an
efficiency requirement in the interface. -/
structure IBEScheme where
  /-- The identity length. -/
  idLen : PolyExpr
  /-- The message length. -/
  msgLen : PolyExpr
  /-- The width of encoded parameters. -/
  ppLen : PolyExpr
  /-- The width of encoded private keys. -/
  skLen : PolyExpr
  /-- The width of encoded ciphertexts. -/
  ctLen : PolyExpr
  /-- System parameters. -/
  PP : ℕ → Type
  /-- Master keys. -/
  MSK : ℕ → Type
  /-- Private keys. -/
  SK : ℕ → Type
  /-- Ciphertexts. -/
  CT : ℕ → Type
  /-- `Setup`: system parameters and a master key. -/
  setup : (κ : ℕ) → ProbComp (PP κ × MSK κ)
  /-- `KeyGen`: the private key of an identity. -/
  keyGen : (κ : ℕ) → MSK κ → (Fin (idLen.eval κ) → Bool) → ProbComp (SK κ)
  /-- `Encrypt`: a ciphertext of a message for an identity. -/
  enc : (κ : ℕ) → PP κ → (Fin (idLen.eval κ) → Bool) → (Fin (msgLen.eval κ) → Bool) →
    ProbComp (CT κ)
  /-- `Decrypt`: the message of a ciphertext under a private key, or `⊥`. -/
  dec : (κ : ℕ) → SK κ → CT κ → Option (Fin (msgLen.eval κ) → Bool)
  /-- The message space for given parameters. -/
  MsgSpace : (κ : ℕ) → PP κ → (Fin (msgLen.eval κ) → Bool) → Prop
  /-- The encoding of parameters. -/
  encPP : (κ : ℕ) → PP κ → Fin (ppLen.eval κ) → Bool
  /-- The encoding of private keys. -/
  encSK : (κ : ℕ) → SK κ → Fin (skLen.eval κ) → Bool
  /-- The encoding of ciphertexts. -/
  encCT : (κ : ℕ) → CT κ → Fin (ctLen.eval κ) → Bool

namespace IBEScheme

variable (S : IBEScheme)

/-- One honest run for the identity `ID` and the message `M`: `Setup`, then `KeyGen` for `ID`
and `Encrypt(params, ID, M)`, returning the parameters, the private key and the ciphertext. -/
noncomputable def honestRun (κ : ℕ) (id : Fin (S.idLen.eval κ) → Bool)
    (m : Fin (S.msgLen.eval κ) → Bool) : ProbComp (S.PP κ × S.SK κ × S.CT κ) :=
  (S.setup κ).bind fun k =>
  (S.keyGen κ k.2 id).bind fun sk =>
  (S.enc κ k.1 id m).bind fun c => .pure (k.1, sk, c)

/-- `S.honestRun κ id m` runs `Setup`, `KeyGen` for `id` and `Encrypt` of `m` for `id`, and
returns `(params, d_id, C)`. -/
theorem honestRun_eq (κ : ℕ) (id : Fin (S.idLen.eval κ) → Bool)
    (m : Fin (S.msgLen.eval κ) → Bool) :
    S.honestRun κ id m =
      (S.setup κ).bind fun k =>
      (S.keyGen κ k.2 id).bind fun sk =>
      (S.enc κ k.1 id m).bind fun c => .pure (k.1, sk, c) := rfl

/-- **Perfect correctness** [BB04, §2.1, "the decryption algorithm decrypts ciphertexts using the
private key"; §4.1's verification for BB1]: for every identity `ID` and every message `M`, every
possible outcome `(params, d_ID, C)` of an honest run with `M` in the message space of `params`
has `Decrypt(d_ID, C) = M`. -/
def Correct : Prop :=
  ∀ κ (id : Fin (S.idLen.eval κ) → Bool) (m : Fin (S.msgLen.eval κ) → Bool),
    (S.honestRun κ id m).AllOutputs fun x => S.MsgSpace κ x.1 m → S.dec κ x.2.1 x.2.2 = some m

/-- `S.Correct` iff every possible outcome of every honest run with a message of the message
space decrypts to that message. -/
theorem correct_iff :
    S.Correct ↔ ∀ κ (id : Fin (S.idLen.eval κ) → Bool) (m : Fin (S.msgLen.eval κ) → Bool),
      (S.honestRun κ id m).AllOutputs fun x =>
        S.MsgSpace κ x.1 m → S.dec κ x.2.1 x.2.2 = some m := Iff.rfl

/-! ### The selective-identity game -/

/-- The query lengths of the three oracles: `Init` and `KeyGen` take an identity, `Challenge`
takes two messages. -/
def inLens (κ : ℕ) : Fin 3 → ℕ
  | 0 => S.idLen.eval κ
  | 1 => S.idLen.eval κ
  | 2 => S.msgLen.eval κ + S.msgLen.eval κ

/-- `Init` queries are identities: `S.inLens κ 0 = S.idLen.eval κ`. -/
theorem inLens_zero (κ : ℕ) : S.inLens κ 0 = S.idLen.eval κ := rfl

/-- `KeyGen` queries are identities: `S.inLens κ 1 = S.idLen.eval κ`. -/
theorem inLens_one (κ : ℕ) : S.inLens κ 1 = S.idLen.eval κ := rfl

/-- `Challenge` queries are two messages: `S.inLens κ 2 = S.msgLen.eval κ + S.msgLen.eval κ`. -/
theorem inLens_two (κ : ℕ) : S.inLens κ 2 = S.msgLen.eval κ + S.msgLen.eval κ := rfl

/-- The answer lengths of the three oracles: `Init` answers the parameters, `KeyGen` a validity
bit and a private key, `Challenge` a ciphertext. -/
def outLens (κ : ℕ) : Fin 3 → ℕ
  | 0 => S.ppLen.eval κ
  | 1 => S.skLen.eval κ + 1
  | 2 => S.ctLen.eval κ

/-- `Init` answers parameters: `S.outLens κ 0 = S.ppLen.eval κ`. -/
theorem outLens_zero (κ : ℕ) : S.outLens κ 0 = S.ppLen.eval κ := rfl

/-- `KeyGen` answers a validity bit and a key: `S.outLens κ 1 = S.skLen.eval κ + 1`. -/
theorem outLens_one (κ : ℕ) : S.outLens κ 1 = S.skLen.eval κ + 1 := rfl

/-- `Challenge` answers a ciphertext: `S.outLens κ 2 = S.ctLen.eval κ`. -/
theorem outLens_two (κ : ℕ) : S.outLens κ 2 = S.ctLen.eval κ := rfl

/-- The three oracles of the IND-sID-CPA game at parameter `κ`. -/
abbrev sidSpec (κ : ℕ) : OracleSpec (Fin 3) := bitSpec (S.inLens κ) (S.outLens κ)

/-- The IND-sID-CPA oracle specification is the bit specification at the scheme's query and
answer lengths: `S.sidSpec κ = bitSpec (S.inLens κ) (S.outLens κ)`. -/
theorem sidSpec_eq (κ : ℕ) : S.sidSpec κ = bitSpec (S.inLens κ) (S.outLens κ) := rfl

/-- The state of the IND-sID-CPA game: the committed identity `ID*` (once `Init` is asked) and
the challenge ciphertext (once issued). -/
abbrev SidState (κ : ℕ) : Type :=
  Option (Fin (S.idLen.eval κ) → Bool) × Option (Fin (S.ctLen.eval κ) → Bool)

/-- The game state is the optional committed identity and the optional encoded challenge:
`S.SidState κ = Option (Fin (S.idLen.eval κ) → Bool) × Option (Fin (S.ctLen.eval κ) → Bool)`. -/
theorem sidState_eq (κ : ℕ) :
    S.SidState κ =
      (Option (Fin (S.idLen.eval κ) → Bool) × Option (Fin (S.ctLen.eval κ) → Bool)) := rfl

open Classical in
/-- **The oracles of the IND-sID-CPA game** [BB04, §2.1] with hidden bit `b`, at parameter `κ`,
for the parameters `pp` and the master key `msk`:
- `Init` on `ID`: answers `params`; records `ID*` = `ID` if none is recorded yet.
- `KeyGen` on `ID`: when `ID*` is recorded and `ID ≠ ID*`, answers `⟨1, d_ID⟩` with
  `d_ID ← KeyGen(msk, ID)`; otherwise `⊥`.
- `Challenge` on `⟨M₀, M₁⟩`: with `ID*` recorded and no challenge yet, if `M₀, M₁ ∈ M`, answers
  and records `C ← Encrypt(params, ID*, M_b)`, and otherwise `⊥`; once a challenge is recorded,
  repeats it; before `Init`, `⊥`. -/
noncomputable def sidImpl (b : Bool) (κ : ℕ) (pp : S.PP κ) (msk : S.MSK κ) :
    QueryImpl (S.sidSpec κ) (S.SidState κ) unifSpec
  | 0, id, s =>
    match s.1 with
    | none => .pure (S.encPP κ pp, (some id, s.2))
    | some _ => .pure (S.encPP κ pp, s)
  | 1, id, s =>
    match s.1 with
    | some t =>
      if id = t then .pure (zeroBits _, s)
      else (S.keyGen κ msk id).bind fun sk =>
        .pure (FixedLengthScheme.decAnswer (some (S.encSK κ sk)), s)
    | none => .pure (zeroBits _, s)
  | 2, mm, s =>
    match s.1, s.2 with
    | some _, some c => .pure (c, s)
    | some t, none =>
      if S.MsgSpace κ pp (FixedLengthScheme.splitHalf mm).1 ∧
          S.MsgSpace κ pp (FixedLengthScheme.splitHalf mm).2 then
        (S.enc κ pp t (if b then (FixedLengthScheme.splitHalf mm).2
          else (FixedLengthScheme.splitHalf mm).1)).bind fun c =>
          .pure (S.encCT κ c, (some t, some (S.encCT κ c)))
      else .pure (zeroBits _, s)
    | none, _ => .pure (zeroBits _, s)

/-- `Init` before any commitment answers the parameters and records the identity. -/
theorem sidImpl_init_none (b : Bool) (κ : ℕ) (pp : S.PP κ) (msk : S.MSK κ)
    (id : Fin (S.idLen.eval κ) → Bool) (c : Option (Fin (S.ctLen.eval κ) → Bool)) :
    S.sidImpl b κ pp msk 0 id (none, c) = .pure (S.encPP κ pp, (some id, c)) := rfl

/-- `Init` after a commitment answers the parameters and keeps the state. -/
theorem sidImpl_init_some (b : Bool) (κ : ℕ) (pp : S.PP κ) (msk : S.MSK κ)
    (id t : Fin (S.idLen.eval κ) → Bool) (c : Option (Fin (S.ctLen.eval κ) → Bool)) :
    S.sidImpl b κ pp msk 0 id (some t, c) = .pure (S.encPP κ pp, (some t, c)) := rfl

/-- `KeyGen` before `Init` answers `⊥`. -/
theorem sidImpl_keyGen_none (b : Bool) (κ : ℕ) (pp : S.PP κ) (msk : S.MSK κ)
    (id : Fin (S.idLen.eval κ) → Bool) (c : Option (Fin (S.ctLen.eval κ) → Bool)) :
    S.sidImpl b κ pp msk 1 id (none, c) = .pure (zeroBits _, (none, c)) := rfl

/-- `KeyGen` for the committed identity answers `⊥`. -/
theorem sidImpl_keyGen_target (b : Bool) (κ : ℕ) (pp : S.PP κ) (msk : S.MSK κ)
    (t : Fin (S.idLen.eval κ) → Bool) (c : Option (Fin (S.ctLen.eval κ) → Bool)) :
    S.sidImpl b κ pp msk 1 t (some t, c) = .pure (zeroBits _, (some t, c)) := by
  simp [sidImpl]

/-- `KeyGen` for an identity other than the committed one answers `⟨1, d_ID⟩` with
`d_ID ← KeyGen(msk, ID)` and keeps the state. -/
theorem sidImpl_keyGen_ne (b : Bool) (κ : ℕ) (pp : S.PP κ) (msk : S.MSK κ)
    (id t : Fin (S.idLen.eval κ) → Bool) (c : Option (Fin (S.ctLen.eval κ) → Bool))
    (h : id ≠ t) :
    S.sidImpl b κ pp msk 1 id (some t, c) =
      (S.keyGen κ msk id).bind fun sk =>
        .pure (FixedLengthScheme.decAnswer (some (S.encSK κ sk)), (some t, c)) := by
  simp [sidImpl, h]

/-- `Challenge` before `Init` answers `⊥`. -/
theorem sidImpl_challenge_none (b : Bool) (κ : ℕ) (pp : S.PP κ) (msk : S.MSK κ)
    (mm : Fin (S.msgLen.eval κ + S.msgLen.eval κ) → Bool)
    (c : Option (Fin (S.ctLen.eval κ) → Bool)) :
    S.sidImpl b κ pp msk 2 mm (none, c) = .pure (zeroBits _, (none, c)) := rfl

/-- `Challenge` after a recorded challenge repeats it. -/
theorem sidImpl_challenge_repeat (b : Bool) (κ : ℕ) (pp : S.PP κ) (msk : S.MSK κ)
    (mm : Fin (S.msgLen.eval κ + S.msgLen.eval κ) → Bool) (t : Fin (S.idLen.eval κ) → Bool)
    (c : Fin (S.ctLen.eval κ) → Bool) :
    S.sidImpl b κ pp msk 2 mm (some t, some c) = .pure (c, (some t, some c)) := rfl

/-- The first `Challenge` with both messages in the message space answers and records
`C ← Encrypt(params, ID*, M_b)`. -/
theorem sidImpl_challenge_fresh (b : Bool) (κ : ℕ) (pp : S.PP κ) (msk : S.MSK κ)
    (mm : Fin (S.msgLen.eval κ + S.msgLen.eval κ) → Bool) (t : Fin (S.idLen.eval κ) → Bool)
    (h : S.MsgSpace κ pp (FixedLengthScheme.splitHalf mm).1 ∧
      S.MsgSpace κ pp (FixedLengthScheme.splitHalf mm).2) :
    S.sidImpl b κ pp msk 2 mm (some t, none) =
      (S.enc κ pp t (if b then (FixedLengthScheme.splitHalf mm).2
        else (FixedLengthScheme.splitHalf mm).1)).bind fun c =>
        .pure (S.encCT κ c, (some t, some (S.encCT κ c))) := by
  simp only [sidImpl]
  rw [if_pos h]

/-- The first `Challenge` with a message outside the message space answers `⊥`. -/
theorem sidImpl_challenge_invalid (b : Bool) (κ : ℕ) (pp : S.PP κ) (msk : S.MSK κ)
    (mm : Fin (S.msgLen.eval κ + S.msgLen.eval κ) → Bool) (t : Fin (S.idLen.eval κ) → Bool)
    (h : ¬ (S.MsgSpace κ pp (FixedLengthScheme.splitHalf mm).1 ∧
      S.MsgSpace κ pp (FixedLengthScheme.splitHalf mm).2)) :
    S.sidImpl b κ pp msk 2 mm (some t, none) = .pure (zeroBits _, (some t, none)) := by
  simp only [sidImpl]
  rw [if_neg h]

/-- **The three oracles from typed handlers**: an implementation of `S.sidSpec κ` whose `Init`,
`KeyGen` and `Challenge` oracles are the handlers `init`, `key` and `chal`, which take and return
strings of the scheme's lengths. Simulators and reductions describe their oracles this way, so
that they never read the oracle lengths `inLens`, `outLens` through their bodies. -/
def oracleImpl {σ : Type} (κ : ℕ)
    (init : (Fin (S.idLen.eval κ) → Bool) → σ → ProbComp ((Fin (S.ppLen.eval κ) → Bool) × σ))
    (key : (Fin (S.idLen.eval κ) → Bool) → σ → ProbComp ((Fin (S.skLen.eval κ + 1) → Bool) × σ))
    (chal : (Fin (S.msgLen.eval κ + S.msgLen.eval κ) → Bool) → σ →
      ProbComp ((Fin (S.ctLen.eval κ) → Bool) × σ)) :
    QueryImpl (S.sidSpec κ) σ unifSpec
  | 0, x, s => init x s
  | 1, x, s => key x s
  | 2, x, s => chal x s

/-- Oracle `0` of `S.oracleImpl κ init key chal` is the handler `init`. -/
theorem oracleImpl_zero {σ : Type} (κ : ℕ)
    (init : (Fin (S.idLen.eval κ) → Bool) → σ → ProbComp ((Fin (S.ppLen.eval κ) → Bool) × σ))
    (key : (Fin (S.idLen.eval κ) → Bool) → σ → ProbComp ((Fin (S.skLen.eval κ + 1) → Bool) × σ))
    (chal : (Fin (S.msgLen.eval κ + S.msgLen.eval κ) → Bool) → σ →
      ProbComp ((Fin (S.ctLen.eval κ) → Bool) × σ))
    (x : Fin (S.idLen.eval κ) → Bool) (s : σ) :
    S.oracleImpl κ init key chal 0 x s = init x s := rfl

/-- Oracle `1` of `S.oracleImpl κ init key chal` is the handler `key`. -/
theorem oracleImpl_one {σ : Type} (κ : ℕ)
    (init : (Fin (S.idLen.eval κ) → Bool) → σ → ProbComp ((Fin (S.ppLen.eval κ) → Bool) × σ))
    (key : (Fin (S.idLen.eval κ) → Bool) → σ → ProbComp ((Fin (S.skLen.eval κ + 1) → Bool) × σ))
    (chal : (Fin (S.msgLen.eval κ + S.msgLen.eval κ) → Bool) → σ →
      ProbComp ((Fin (S.ctLen.eval κ) → Bool) × σ))
    (x : Fin (S.idLen.eval κ) → Bool) (s : σ) :
    S.oracleImpl κ init key chal 1 x s = key x s := rfl

/-- Oracle `2` of `S.oracleImpl κ init key chal` is the handler `chal`. -/
theorem oracleImpl_two {σ : Type} (κ : ℕ)
    (init : (Fin (S.idLen.eval κ) → Bool) → σ → ProbComp ((Fin (S.ppLen.eval κ) → Bool) × σ))
    (key : (Fin (S.idLen.eval κ) → Bool) → σ → ProbComp ((Fin (S.skLen.eval κ + 1) → Bool) × σ))
    (chal : (Fin (S.msgLen.eval κ + S.msgLen.eval κ) → Bool) → σ →
      ProbComp ((Fin (S.ctLen.eval κ) → Bool) × σ))
    (x : Fin (S.msgLen.eval κ + S.msgLen.eval κ) → Bool) (s : σ) :
    S.oracleImpl κ init key chal 2 x s = chal x s := rfl

/-- The codec of the adversary: the three oracles and a one-bit guess. -/
def sidCodec (κ : ℕ) : MachineCodec (S.sidSpec κ) (Fin 1 → Bool) :=
  bitCodec (S.inLens κ) (S.outLens κ) 1

/-- The adversary codec is a bit codec: `S.sidCodec κ = bitCodec (S.inLens κ) (S.outLens κ) 1`. -/
theorem sidCodec_eq (κ : ℕ) : S.sidCodec κ = bitCodec (S.inLens κ) (S.outLens κ) 1 := rfl

/-- **The experiment `IND-sID-CPA_b(A, κ)`** [BB04, §2.1] with query budget `q`: run `Setup`,
draw `A`'s coins, run `A(1^κ)` against the three oracles from the empty state (no identity
committed, no challenge), and return its one-bit guess. -/
noncomputable def sidGame (A : NUPPT) (q : ℕ) (b : Bool) (κ : ℕ) : ProbComp Bool :=
  (S.setup κ).bind fun k =>
  (ProbComp.sample (A.Coins κ)).bind fun r =>
  (simulate (S.sidImpl b κ k.1 k.2) (A.toComp (S.sidCodec κ) κ q r) (none, none)).bind
    fun res => .pure (res.1 0)

/-- The IND-sID-CPA experiment runs `Setup`, samples the adversary's coins, simulates the
oracles from the empty state, and returns the guess bit. -/
theorem sidGame_eq (A : NUPPT) (q : ℕ) (b : Bool) (κ : ℕ) :
    S.sidGame A q b κ =
      (S.setup κ).bind fun k =>
      (ProbComp.sample (A.Coins κ)).bind fun r =>
      (simulate (S.sidImpl b κ k.1 k.2) (A.toComp (S.sidCodec κ) κ q r) (none, none)).bind
        fun res => .pure (res.1 0) := rfl

/-- **IND-sID-CPA security** [BB04, §2.1 and Definition 2.2]: for every non-uniform PPT `A` and
every polynomial query budget `q`, `A`'s advantage between the experiments with `b = 0` and
`b = 1` is negligible.

**Deviation:** asymptotic, with a polynomial budget `q(κ)` on all queries (the paper's `q_ID`
bounds private-key queries); the advantage is twice the paper's (module docstring). -/
def SIDSecure : Prop :=
  ∀ (A : NUPPT) (q : PolyExpr), ∃ ε : ℕ → ℝ, Negligible ε ∧
    ∀ κ, advantage (S.sidGame A (q.eval κ) false κ) (S.sidGame A (q.eval κ) true κ) ≤ ε κ

/-- IND-sID-CPA security is negligible advantage, uniformly in `κ`, for every non-uniform PPT
adversary and polynomial query budget. -/
theorem sidSecure_iff :
    S.SIDSecure ↔ ∀ (A : NUPPT) (q : PolyExpr), ∃ ε : ℕ → ℝ, Negligible ε ∧
      ∀ κ, advantage (S.sidGame A (q.eval κ) false κ) (S.sidGame A (q.eval κ) true κ) ≤ ε κ :=
  Iff.rfl

end IBEScheme

end TCSlib.Cryptography.AdvancedEncryption.IdentityBased
```

## ===== TCSlib/Cryptography/AdvancedEncryption/IdentityBased/BonehBoyen.lean (Lean, at 110c2f9db810d243693b9a5e8976a5ad205f1bab) =====

```lean
/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TCSlib contributors
-/
import TCSlib.Cryptography.AdvancedEncryption.IdentityBased.Defs
import TCSlib.Cryptography.Pairing.Group
import TCSlib.Cryptography.Asymptotic.Sampling
import Mathlib.Algebra.Field.ZMod

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# The Boneh–Boyen selective-identity IBE (BB1)

[BB04, §4.1] with depth `ℓ = 1` (an IBE system is an HIBE whose identities have depth 1,
[BB04, §2.1]). In a bilinear group `G` of prime order `p` with pairing `e`:
* **Setup**: a random generator `g ∈ G^*`, `α ∈ Z_p`, `g_1 = g^α`, random `h, g_2 ∈ G`;
  `params = (g, g_1, g_2, h)`, `master-key = g_2^α`; `F(x) = g_1^x h`.
* **KeyGen**(`ID ∈ Z_p`): a random `r ∈ Z_p`, `d_ID = (g_2^α · F(ID)^r, g^r)`.
* **Encrypt**(`params`, `ID`, `M ∈ G_1`): a random `s ∈ Z_p`,
  `C = (e(g_1, g_2)^s · M, g^s, F(ID)^s)`.
* **Decrypt**(`d_ID = (d_0, d_1)`, `C = (A, B, C_1)`): `A · e(C_1, d_1) / e(B, d_0)`.

It is IND-sID-CPA secure under Decision BDH [BB04, Theorem 4.1], without random oracles; the
security statement and its simulation are in `AdvancedEncryption.IdentityBased.BonehBoyenSecurity`.

**Identities and messages.** The generic interface (`IBEScheme`) has `ℓ(κ)`-bit identities.
BB1 reads an identity as the residue of its binary value in `Z_p` (`idToZ`), the injective
"hash" `{0,1}^ℓ → {0, …, 2^ℓ − 1}` of [BB04, §4.4] ("a collision resistant hash function
`H : {0,1}^* → {1, …, 2^b}` where `2^b < p` is sufficient"); distinct identities stay distinct in
`Z_p` when `2^ℓ ≤ p`, which the security theorem assumes except with negligible probability.
Messages are elements of `G_T` (the paper's `G_1`), sent as their `wT(κ)`-bit encodings; the
message space is the set of encodings, and `Encrypt` reads a string through `decodeT` (strings
outside the message space read as `1`, a choice that is never exercised by the game, which
refuses them).

**Groups from the generator.** Parameters, keys and ciphertexts carry the description `d` of the
group they live in (a dependent pair), since the group is drawn by `Setup` from the generator
(`Pairing.BilinearGen`). Decryption of a ciphertext whose description differs from the key's is
`⊥`.

**Deviation:** abstract bilinear groups drawn by a generator; depth-1 identities given as
`ℓ(κ)`-bit strings and embedded into `Z_p` by their binary value; messages as encodings of `G_T`;
parameters, keys and ciphertexts tagged with the group's description.

## Main definitions

* `BB1.Params`, `BB1.Key`, `BB1.Ciphertext` — `params`, `d_ID` and `C`.
* `BB1.F`, `BB1.setup`, `BB1.keyGen`, `BB1.encrypt`, `BB1.decrypt` — the
  algorithms of [BB04, §4.1] over one bilinear group.
* `BB1.idToZ`, `BB1.decodeT` — identities in `Z_p` and messages in `G_T`.
* `bb1Scheme` — BB1 as an `IBEScheme` over a generator.
* `BB1SimState`, `bb1SimParams`, `bb1SimKey`, `bb1SimInit`, `bb1SimKeyQ`,
  `bb1SimCt`, `bb1SimChal`, `bb1SimImpl`, `bb1SimGame` — the simulator of
  [BB04, proof of Theorem 4.1] and its game, with ideal exponents.

## Main results

* `BB1.decrypt_encrypt` — decryption inverts encryption [BB04, §4.1, "for a valid
  ciphertext"].
* `bb1_correct` — BB1 is perfectly correct.
* `bb1SimInit_none`, …, `bb1SimChal_invalid` — the simulator's handlers case by case.

## References

* [BB04] D. Boneh, X. Boyen, *Efficient Selective-ID Secure Identity Based Encryption Without
  Random Oracles*, full version, Cryptology ePrint Archive, Report 2004/172, December 2004
  (extended abstract: EUROCRYPT 2004, LNCS 3027, pp. 223–238). §2.1 (pp. 2–4), §4.1 (pp. 5–6:
  the construction), §4.2 (pp. 6–8: the simulator in the proof of Theorem 4.1), §4.4 (p. 8:
  arbitrary identities).
-/

namespace TCSlib.Cryptography.AdvancedEncryption.IdentityBased

open Complexity Turing TCSlib.Cryptography.Games TCSlib.Cryptography.Pairing
  TCSlib.Cryptography.Composability

namespace BB1

variable {wG wT : ℕ} (B : BilinearGroup wG wT)

/-- **System parameters** `params = (g, g_1, g_2, h)` of BB1 [BB04, §4.1, `Setup` at depth 1]. -/
structure Params where
  /-- The generator `g ∈ G^*`. -/
  g : B.G
  /-- `g_1 = g^α`. -/
  g1 : B.G
  /-- The random element `g_2`. -/
  g2 : B.G
  /-- The random element `h = h_1`. -/
  h : B.G

/-- **A private key** `d_ID = (d_0, d_1)` of BB1 [BB04, §4.1, `KeyGen` at depth 1]. -/
structure Key where
  /-- `d_0 = g_2^α · F(ID)^r`. -/
  d0 : B.G
  /-- `d_1 = g^r`. -/
  d1 : B.G

/-- **A ciphertext** `C = (A, B, C_1)` of BB1 [BB04, §4.1, `Encrypt` at depth 1]. -/
structure Ciphertext where
  /-- `A = e(g_1, g_2)^s · M`. -/
  a : B.GT
  /-- `B = g^s`. -/
  b : B.G
  /-- `C_1 = F(ID)^s`. -/
  c : B.G

variable {B}

/-- **The function** `F(x) = g_1^x h` [BB04, §4.1, `F_1 : Z_p → G`]. -/
def F (pp : Params B) (x : ZMod B.order) : B.G := pp.g1 ^ x.val * pp.h

/-- `F pp x = pp.g1 ^ x.val * pp.h`. -/
theorem F_eq (pp : Params B) (x : ZMod B.order) : F pp x = pp.g1 ^ x.val * pp.h := rfl

variable (B)

/-- **Setup** [BB04, §4.1, depth 1]: a uniform generator `g ∈ G^*`, a uniform `α ∈ Z_p`, uniform
`h, g_2 ∈ G`; returns `params = (g, g^α, g_2, h)` and `master-key = g_2^α`. -/
noncomputable def setup : ProbComp (Params B × B.G) :=
  (ProbComp.sample {x : B.G // x ≠ 1}).bind fun g =>
  (ProbComp.sample (ZMod B.order)).bind fun α =>
  (ProbComp.sample B.G).bind fun h =>
  (ProbComp.sample B.G).bind fun g2 =>
    .pure (⟨g.1, g.1 ^ α.val, g2, h⟩, g2 ^ α.val)

/-- `setup B` draws `g ∈ G^*`, `α ∈ Z_p`, `h, g_2 ∈ G` and returns
`((g, g^α, g_2, h), g_2^α)`. -/
theorem setup_eq :
    setup B =
      (ProbComp.sample {x : B.G // x ≠ 1}).bind fun g =>
      (ProbComp.sample (ZMod B.order)).bind fun α =>
      (ProbComp.sample B.G).bind fun h =>
      (ProbComp.sample B.G).bind fun g2 =>
        .pure (⟨g.1, g.1 ^ α.val, g2, h⟩, g2 ^ α.val) := rfl

variable {B}

/-- **KeyGen** [BB04, §4.1, depth 1]: from the parameters, the master key `mk = g_2^α` and an
identity `ID ∈ Z_p`, a uniform `r ∈ Z_p` and `d_ID = (mk · F(ID)^r, g^r)`. -/
noncomputable def keyGen (pp : Params B) (mk : B.G) (id : ZMod B.order) : ProbComp (Key B) :=
  (ProbComp.sample (ZMod B.order)).bind fun r => .pure ⟨mk * F pp id ^ r.val, pp.g ^ r.val⟩

/-- `keyGen pp mk id` draws `r ∈ Z_p` and returns `(mk · F(id)^r, g^r)`. -/
theorem keyGen_eq (pp : Params B) (mk : B.G) (id : ZMod B.order) :
    keyGen pp mk id =
      (ProbComp.sample (ZMod B.order)).bind fun r => .pure ⟨mk * F pp id ^ r.val, pp.g ^ r.val⟩ :=
  rfl

/-- **Encrypt** [BB04, §4.1, depth 1]: for an identity `ID ∈ Z_p` and a message `M ∈ G_T`, a
uniform `s ∈ Z_p` and `C = (e(g_1, g_2)^s · M, g^s, F(ID)^s)`. -/
noncomputable def encrypt (pp : Params B) (id : ZMod B.order) (M : B.GT) :
    ProbComp (Ciphertext B) :=
  (ProbComp.sample (ZMod B.order)).bind fun s =>
    .pure ⟨B.pair pp.g1 pp.g2 ^ s.val * M, pp.g ^ s.val, F pp id ^ s.val⟩

/-- `encrypt pp id M` draws `s ∈ Z_p` and returns `(e(g_1, g_2)^s · M, g^s, F(id)^s)`. -/
theorem encrypt_eq (pp : Params B) (id : ZMod B.order) (M : B.GT) :
    encrypt pp id M =
      (ProbComp.sample (ZMod B.order)).bind fun s =>
        .pure ⟨B.pair pp.g1 pp.g2 ^ s.val * M, pp.g ^ s.val, F pp id ^ s.val⟩ := rfl

/-- **Decrypt** [BB04, §4.1, depth 1]: `A · e(C_1, d_1) / e(B, d_0)` for `d_ID = (d_0, d_1)` and
`C = (A, B, C_1)`. -/
def decrypt (d : Key B) (C : Ciphertext B) : B.GT := C.a * B.pair C.c d.d1 / B.pair C.b d.d0

/-- `decrypt d C = C.a * e(C.c, d.d1) / e(C.b, d.d0)`. -/
theorem decrypt_eq (d : Key B) (C : Ciphertext B) :
    decrypt d C = C.a * B.pair C.c d.d1 / B.pair C.b d.d0 := rfl

/-- **Decryption inverts encryption** [BB04, §4.1, "for a valid ciphertext, we have
`e(C_1, d_1) / e(B, d_0) = 1 / e(g_1, g_2)^s`"]: for the parameters `(g, g^α, g_2, h)`, the
master key `g_2^α`, the private key with exponent `r` and the ciphertext with exponent `s` of
`M` for the same identity, `Decrypt(d_ID, C) = M`.

The proof is the paper's computation: `e(F(ID)^s, g^r) = e(g, F(ID))^{sr}` (bilinearity and
symmetry) and `e(g^s, g_2^α F(ID)^r) = e(g, g_2)^{αs} · e(g, F(ID))^{sr}`, while the mask of `A`
is `e(g^α, g_2)^s = e(g, g_2)^{αs}`. -/
theorem decrypt_encrypt (g g2 h : B.G) (α r s id : ZMod B.order) (M : B.GT) :
    decrypt (⟨g2 ^ α.val * F ⟨g, g ^ α.val, g2, h⟩ id ^ r.val, g ^ r.val⟩ : Key B)
      ⟨B.pair (g ^ α.val) g2 ^ s.val * M, g ^ s.val, F ⟨g, g ^ α.val, g2, h⟩ id ^ s.val⟩ = M := by
  rw [decrypt_eq]
  dsimp only
  have h1 : B.pair (g ^ α.val) g2 ^ s.val = B.pair g g2 ^ (α.val * s.val) := by
    rw [B.pair_pow_left, ← pow_mul]
  have h2 : B.pair (F ⟨g, g ^ α.val, g2, h⟩ id ^ s.val) (g ^ r.val) =
      B.pair g (F ⟨g, g ^ α.val, g2, h⟩ id) ^ (s.val * r.val) := by
    rw [B.bilinear_pow, B.pair_comm (F ⟨g, g ^ α.val, g2, h⟩ id) g]
  have h3 : B.pair (g ^ s.val) (g2 ^ α.val * F ⟨g, g ^ α.val, g2, h⟩ id ^ r.val) =
      B.pair g g2 ^ (α.val * s.val) * B.pair g (F ⟨g, g ^ α.val, g2, h⟩ id) ^ (s.val * r.val) := by
    rw [map_mul (B.pair (g ^ s.val)), B.bilinear_pow, B.bilinear_pow, mul_comm s.val α.val]
  rw [h1, h2, h3, mul_right_comm]
  exact mul_div_cancel_left _ _

variable (B)

/-- **An identity as an element of `Z_p`**: the residue of the binary value of an `ℓ`-bit string,
the injective encoding `{0,1}^ℓ → {0, …, 2^ℓ − 1}` of [BB04, §4.4] read in `Z_p`. -/
def idToZ {ℓ : ℕ} (id : Fin ℓ → Bool) : ZMod B.order := (bitsToNat id : ZMod B.order)

/-- `idToZ id` is the cast of `bitsToNat id` into `Z_p`. -/
theorem idToZ_eq {ℓ : ℕ} (id : Fin ℓ → Bool) :
    idToZ B id = (bitsToNat id : ZMod B.order) := rfl

/-- **A message from its encoding**: the element of `G_T` with encoding `w`, and `1` when `w`
encodes none. -/
noncomputable def decodeT (w : Fin wT → Bool) : B.GT := (Function.partialInv B.encT w).getD 1

/-- `decodeT B w = (Function.partialInv B.encT w).getD 1`. -/
theorem decodeT_eq (w : Fin wT → Bool) : decodeT B w = (Function.partialInv B.encT w).getD 1 :=
  rfl

/-- Decoding an encoding returns the element: `decodeT B (B.encT u) = u`. -/
theorem decodeT_encT (u : B.GT) : decodeT B (B.encT u) = u := by
  rw [decodeT_eq, Function.partialInv_left B.encT_injective, Option.getD_some]

end BB1

/-- **The BB1 IBE system** over the bilinear group generator `G`, for `ℓ(κ)`-bit identities
[BB04, §4.1 at depth 1, with the identity encoding of §4.4]: `Setup` runs the generator and BB1's
`Setup` in the group it describes; the parameters are `⟨d, (g, g_1, g_2, h)⟩`, the master key
also carries the parameters; `KeyGen` and `Encrypt` read the identity through `idToZ` and the
message through `decodeT`; `Decrypt` returns the encoding of BB1's decryption, or `⊥` if the key
and the ciphertext name different descriptions. The message space at `⟨d, params⟩` is the set
of encodings of `G_T` of the group `d` describes. Parameters are encoded as `d` followed by the
four elements, keys as two elements, ciphertexts as `A, B, C_1`. -/
noncomputable def bb1Scheme (G : BilinearGen) (ℓ : PolyExpr) : IBEScheme where
  idLen := ℓ
  msgLen := G.wT
  ppLen := .add G.descLen (.mul (.const 4) G.wG)
  skLen := .mul (.const 2) G.wG
  ctLen := .add G.wT (.mul (.const 2) G.wG)
  PP κ := Σ d : List Bool, BB1.Params (G.group κ d)
  MSK κ := Σ d : List Bool, BB1.Params (G.group κ d) × (G.group κ d).G
  SK κ := Σ d : List Bool, BB1.Key (G.group κ d)
  CT κ := Σ d : List Bool, BB1.Ciphertext (G.group κ d)
  setup κ :=
    (ProbComp.sample (G.gen.Coins κ)).bind fun r =>
    (BB1.setup (G.group κ (G.desc κ r))).bind fun k =>
      .pure (⟨G.desc κ r, k.1⟩, ⟨G.desc κ r, k⟩)
  keyGen _ msk id :=
    (BB1.keyGen msk.2.1 msk.2.2 (BB1.idToZ _ id)).bind fun d => .pure ⟨msk.1, d⟩
  enc _ pp id m :=
    (BB1.encrypt pp.2 (BB1.idToZ _ id) (BB1.decodeT _ m)).bind fun c => .pure ⟨pp.1, c⟩
  dec κ sk c :=
    if h : c.1 = sk.1 then
      some ((G.group κ sk.1).encT (BB1.decrypt sk.2 (h ▸ c.2)))
    else none
  MsgSpace κ pp m := ∃ u, (G.group κ pp.1).encT u = m
  encPP κ pp := padFin _ (pp.1 ++ List.ofFn ((G.group κ pp.1).encG pp.2.g) ++
    List.ofFn ((G.group κ pp.1).encG pp.2.g1) ++ List.ofFn ((G.group κ pp.1).encG pp.2.g2) ++
    List.ofFn ((G.group κ pp.1).encG pp.2.h))
  encSK κ sk := padFin _ (List.ofFn ((G.group κ sk.1).encG sk.2.d0) ++
    List.ofFn ((G.group κ sk.1).encG sk.2.d1))
  encCT κ c := padFin _ (List.ofFn ((G.group κ c.1).encT c.2.a) ++
    List.ofFn ((G.group κ c.1).encG c.2.b) ++ List.ofFn ((G.group κ c.1).encG c.2.c))

attribute [simps (config := { isSimp := false }) idLen msgLen ppLen skLen ctLen PP MSK SK CT
  setup keyGen enc dec MsgSpace encPP encSK encCT] bb1Scheme

/-- **BB1 is perfectly correct** [BB04, §4.1, "Indeed, for a valid ciphertext …"]: every
honest run with a message of the message space decrypts to that message.

Every possible outcome of an honest run has parameters
`⟨d, (g, g^α, g_2, h)⟩`, key `⟨d, (g_2^α F(ID)^r, g^r)⟩` and ciphertext
`⟨d, (e(g^α, g_2)^s · M', g^s, F(ID)^s)⟩` with the same description `d` and
`M' = decodeT M`, so `Decrypt` takes its first branch and returns the encoding of `M'` by
`BB1.decrypt_encrypt`. A message of the message space is an encoding `encT u`, so
`M' = u` (`decodeT_encT`) and its encoding is `M`. -/
theorem bb1_correct (G : BilinearGen) (ℓ : PolyExpr) : (bb1Scheme G ℓ).Correct := by
  rw [IBEScheme.correct_iff]
  intro κ id m
  rw [IBEScheme.honestRun_eq, bb1Scheme_setup]
  simp only [OracleComp.bind_assoc, OracleComp.pure_bind, BB1.setup_eq, bb1Scheme_keyGen,
    bb1Scheme_enc, BB1.keyGen_eq, BB1.encrypt_eq]
  refine (OracleComp.allOutputs_true _).bind fun r _ => ?_
  refine (OracleComp.allOutputs_true _).bind fun g _ => ?_
  refine (OracleComp.allOutputs_true _).bind fun α _ => ?_
  refine (OracleComp.allOutputs_true _).bind fun h _ => ?_
  refine (OracleComp.allOutputs_true _).bind fun g2 _ => ?_
  refine (OracleComp.allOutputs_true _).bind fun ρ _ => ?_
  refine (OracleComp.allOutputs_true _).bind fun σ _ => ?_
  refine OracleComp.allOutputs_pure.2 fun hm => ?_
  obtain ⟨u, hu⟩ := hm
  rw [bb1Scheme_dec, dif_pos rfl]
  dsimp only
  rw [← hu, BB1.decodeT_encT, BB1.decrypt_encrypt]

/-! ### The simulator of [BB04, proof of Theorem 4.1]

The Decision BDH algorithm `B` of the proof, as typed oracle handlers over the parameters of
`bb1Scheme`, with ideal uniform exponents; `bb1SimGame` runs the adversary against them. The
security argument is in `AdvancedEncryption.IdentityBased.BonehBoyenSecurity`. -/

section Simulator

variable (G : BilinearGen) (ℓ : PolyExpr)

/-- The simulator's state at parameter `κ` in the group described by `d`: the committed identity
with the simulator's exponent `α_1` (once `Init` is asked), and the issued challenge. -/
abbrev BB1SimState (κ : ℕ) (d : List Bool) : Type :=
  Option ((Fin ((bb1Scheme G ℓ).idLen.eval κ) → Bool) × ZMod (G.group κ d).order) ×
    Option (Fin ((bb1Scheme G ℓ).ctLen.eval κ) → Bool)

/-- `BB1SimState G ℓ κ d` is the optional pair of the committed identity and `α_1`, with the
optional encoded challenge. -/
theorem bb1SimState_eq (κ : ℕ) (d : List Bool) :
    BB1SimState G ℓ κ d =
      (Option ((Fin ((bb1Scheme G ℓ).idLen.eval κ) → Bool) × ZMod (G.group κ d).order) ×
        Option (Fin ((bb1Scheme G ℓ).ctLen.eval κ) → Bool)) := rfl

/-- The simulated parameters `(g, X, Y, X^{−ID*} g^{α_1})` for the committed identity `ID*` and
the exponent `α_1` [BB04, proof of Theorem 4.1, *Setup*]. -/
noncomputable def bb1SimParams {κ : ℕ} {d : List Bool} (g X Y : (G.group κ d).G)
    (t : Fin ((bb1Scheme G ℓ).idLen.eval κ) → Bool) (α₁ : ZMod (G.group κ d).order) :
    BB1.Params (G.group κ d) :=
  ⟨g, X, Y, X ^ (-BB1.idToZ (G.group κ d) t).val * g ^ α₁.val⟩

/-- `bb1SimParams G ℓ g X Y t α₁ = (g, X, Y, X ^ (−idToZ t).val · g ^ α₁.val)`. -/
theorem bb1SimParams_eq {κ : ℕ} {d : List Bool} (g X Y : (G.group κ d).G)
    (t : Fin ((bb1Scheme G ℓ).idLen.eval κ) → Bool) (α₁ : ZMod (G.group κ d).order) :
    bb1SimParams G ℓ g X Y t α₁ =
      ⟨g, X, Y, X ^ (-BB1.idToZ (G.group κ d) t).val * g ^ α₁.val⟩ := rfl

/-- The simulated private key of `ID ≠ ID*` with exponent `r` [BB04, proof of Theorem 4.1,
*Phase 1*]: `(Y^{−α_1/(ID − ID*)} F(ID)^r, Y^{−1/(ID − ID*)} g^r)`, with `F` of the simulated
parameters and the identities read in `Z_p`. -/
noncomputable def bb1SimKey {κ : ℕ} {d : List Bool} (g X Y : (G.group κ d).G)
    (t : Fin ((bb1Scheme G ℓ).idLen.eval κ) → Bool) (α₁ : ZMod (G.group κ d).order)
    (id : Fin ((bb1Scheme G ℓ).idLen.eval κ) → Bool) (r : ZMod (G.group κ d).order) :
    BB1.Key (G.group κ d) :=
  ⟨Y ^ (-α₁ / (BB1.idToZ (G.group κ d) id - BB1.idToZ (G.group κ d) t)).val *
      BB1.F (bb1SimParams G ℓ g X Y t α₁) (BB1.idToZ (G.group κ d) id) ^ r.val,
    Y ^ (-1 / (BB1.idToZ (G.group κ d) id - BB1.idToZ (G.group κ d) t)).val * g ^ r.val⟩

/-- `bb1SimKey G ℓ g X Y t α₁ id r` is
`(Y^{(−α₁/(id − t)).val} · F(id)^{r.val}, Y^{(−1/(id − t)).val} · g^{r.val})`. -/
theorem bb1SimKey_eq {κ : ℕ} {d : List Bool} (g X Y : (G.group κ d).G)
    (t : Fin ((bb1Scheme G ℓ).idLen.eval κ) → Bool) (α₁ : ZMod (G.group κ d).order)
    (id : Fin ((bb1Scheme G ℓ).idLen.eval κ) → Bool) (r : ZMod (G.group κ d).order) :
    bb1SimKey G ℓ g X Y t α₁ id r =
      ⟨Y ^ (-α₁ / (BB1.idToZ (G.group κ d) id - BB1.idToZ (G.group κ d) t)).val *
          BB1.F (bb1SimParams G ℓ g X Y t α₁) (BB1.idToZ (G.group κ d) id) ^ r.val,
        Y ^ (-1 / (BB1.idToZ (G.group κ d) id - BB1.idToZ (G.group κ d) t)).val * g ^ r.val⟩ :=
  rfl

/-- **The simulator's `Init`** [BB04, proof of Theorem 4.1, *Initialization* and *Setup*] on the
description `d` and `g, X = g^a, Y = g^{b'}`: before any commitment, draw `α_1 ∈ Z_p`, record
`(ID, α_1)` and answer the simulated parameters; afterwards answer the recorded identity's. -/
noncomputable def bb1SimInit (κ : ℕ) (d : List Bool) (g X Y : (G.group κ d).G)
    (id : Fin ((bb1Scheme G ℓ).idLen.eval κ) → Bool) (s : BB1SimState G ℓ κ d) :
    ProbComp ((Fin ((bb1Scheme G ℓ).ppLen.eval κ) → Bool) × BB1SimState G ℓ κ d) :=
  match s.1 with
  | none => (ProbComp.sample (ZMod (G.group κ d).order)).bind fun α₁ =>
      .pure ((bb1Scheme G ℓ).encPP κ ⟨d, bb1SimParams G ℓ g X Y id α₁⟩, (some (id, α₁), s.2))
  | some (t, α₁) => .pure ((bb1Scheme G ℓ).encPP κ ⟨d, bb1SimParams G ℓ g X Y t α₁⟩, s)

/-- `Init` before any commitment draws `α_1` and answers the simulated parameters. -/
theorem bb1SimInit_none (κ : ℕ) (d : List Bool) (g X Y : (G.group κ d).G)
    (id : Fin ((bb1Scheme G ℓ).idLen.eval κ) → Bool)
    (c : Option (Fin ((bb1Scheme G ℓ).ctLen.eval κ) → Bool)) :
    bb1SimInit G ℓ κ d g X Y id (none, c) =
      (ProbComp.sample (ZMod (G.group κ d).order)).bind fun α₁ =>
        .pure ((bb1Scheme G ℓ).encPP κ ⟨d, bb1SimParams G ℓ g X Y id α₁⟩, (some (id, α₁), c)) :=
  rfl

/-- `Init` after a commitment answers the recorded identity's simulated parameters. -/
theorem bb1SimInit_some (κ : ℕ) (d : List Bool) (g X Y : (G.group κ d).G)
    (id t : Fin ((bb1Scheme G ℓ).idLen.eval κ) → Bool) (α₁ : ZMod (G.group κ d).order)
    (c : Option (Fin ((bb1Scheme G ℓ).ctLen.eval κ) → Bool)) :
    bb1SimInit G ℓ κ d g X Y id (some (t, α₁), c) =
      .pure ((bb1Scheme G ℓ).encPP κ ⟨d, bb1SimParams G ℓ g X Y t α₁⟩, (some (t, α₁), c)) :=
  rfl

/-- **The simulator's `KeyGen`** [BB04, proof of Theorem 4.1, *Phase 1*]: when `ID*` is recorded
and `ID ≠ ID*`, draw `r ∈ Z_p` and answer `⟨1, bb1SimKey … ID r⟩`; otherwise `⊥`. -/
noncomputable def bb1SimKeyQ (κ : ℕ) (d : List Bool) (g X Y : (G.group κ d).G)
    (id : Fin ((bb1Scheme G ℓ).idLen.eval κ) → Bool) (s : BB1SimState G ℓ κ d) :
    ProbComp ((Fin ((bb1Scheme G ℓ).skLen.eval κ + 1) → Bool) × BB1SimState G ℓ κ d) :=
  match s.1 with
  | some (t, α₁) =>
    if id = t then .pure (zeroBits _, s)
    else (ProbComp.sample (ZMod (G.group κ d).order)).bind fun r =>
      .pure (FixedLengthScheme.decAnswer
        (some ((bb1Scheme G ℓ).encSK κ ⟨d, bb1SimKey G ℓ g X Y t α₁ id r⟩)), s)
  | none => .pure (zeroBits _, s)

/-- `KeyGen` before `Init` answers `⊥`. -/
theorem bb1SimKeyQ_none (κ : ℕ) (d : List Bool) (g X Y : (G.group κ d).G)
    (id : Fin ((bb1Scheme G ℓ).idLen.eval κ) → Bool)
    (c : Option (Fin ((bb1Scheme G ℓ).ctLen.eval κ) → Bool)) :
    bb1SimKeyQ G ℓ κ d g X Y id (none, c) = .pure (zeroBits _, (none, c)) := rfl

/-- `KeyGen` for the committed identity answers `⊥`. -/
theorem bb1SimKeyQ_target (κ : ℕ) (d : List Bool) (g X Y : (G.group κ d).G)
    (t : Fin ((bb1Scheme G ℓ).idLen.eval κ) → Bool) (α₁ : ZMod (G.group κ d).order)
    (c : Option (Fin ((bb1Scheme G ℓ).ctLen.eval κ) → Bool)) :
    bb1SimKeyQ G ℓ κ d g X Y t (some (t, α₁), c) = .pure (zeroBits _, (some (t, α₁), c)) := by
  simp [bb1SimKeyQ]

/-- `KeyGen` for `ID ≠ ID*` draws `r` and answers the simulated key. -/
theorem bb1SimKeyQ_ne (κ : ℕ) (d : List Bool) (g X Y : (G.group κ d).G)
    (id t : Fin ((bb1Scheme G ℓ).idLen.eval κ) → Bool) (α₁ : ZMod (G.group κ d).order)
    (c : Option (Fin ((bb1Scheme G ℓ).ctLen.eval κ) → Bool)) (h : id ≠ t) :
    bb1SimKeyQ G ℓ κ d g X Y id (some (t, α₁), c) =
      (ProbComp.sample (ZMod (G.group κ d).order)).bind fun r =>
        .pure (FixedLengthScheme.decAnswer
          (some ((bb1Scheme G ℓ).encSK κ ⟨d, bb1SimKey G ℓ g X Y t α₁ id r⟩)),
          (some (t, α₁), c)) := by
  simp [bb1SimKeyQ, h]

/-- The simulated challenge `(M · T, Z, Z^{α_1})` [BB04, proof of Theorem 4.1, *Challenge*] of the
message string `m`, encoded. -/
noncomputable def bb1SimCt (κ : ℕ) (d : List Bool) (Z : (G.group κ d).G) (T : (G.group κ d).GT)
    (α₁ : ZMod (G.group κ d).order) (m : Fin ((bb1Scheme G ℓ).msgLen.eval κ) → Bool) :
    Fin ((bb1Scheme G ℓ).ctLen.eval κ) → Bool :=
  (bb1Scheme G ℓ).encCT κ ⟨d, ⟨BB1.decodeT _ m * T, Z, Z ^ α₁.val⟩⟩

/-- `bb1SimCt G ℓ κ d Z T α₁ m` is the encoding of `(decodeT m · T, Z, Z ^ α₁.val)`. -/
theorem bb1SimCt_eq (κ : ℕ) (d : List Bool) (Z : (G.group κ d).G) (T : (G.group κ d).GT)
    (α₁ : ZMod (G.group κ d).order) (m : Fin ((bb1Scheme G ℓ).msgLen.eval κ) → Bool) :
    bb1SimCt G ℓ κ d Z T α₁ m =
      (bb1Scheme G ℓ).encCT κ ⟨d, ⟨BB1.decodeT _ m * T, Z, Z ^ α₁.val⟩⟩ := rfl

open Classical in
/-- **The simulator's `Challenge`** [BB04, proof of Theorem 4.1, *Challenge*] with challenge bit
`b`, on `Z = g^c` and `T`: with `ID*` recorded and no challenge yet, if `M₀, M₁` are in the
message space, answer and record `(M_b · T, Z, Z^{α_1})`, and otherwise `⊥`; once a challenge is
recorded, repeat it; before `Init`, `⊥`. -/
noncomputable def bb1SimChal (b : Bool) (κ : ℕ) (d : List Bool) (g X Y Z : (G.group κ d).G)
    (T : (G.group κ d).GT)
    (mm : Fin ((bb1Scheme G ℓ).msgLen.eval κ + (bb1Scheme G ℓ).msgLen.eval κ) → Bool)
    (s : BB1SimState G ℓ κ d) :
    ProbComp ((Fin ((bb1Scheme G ℓ).ctLen.eval κ) → Bool) × BB1SimState G ℓ κ d) :=
  match s.1, s.2 with
  | some _, some c => .pure (c, s)
  | some (t, α₁), none =>
    if (bb1Scheme G ℓ).MsgSpace κ ⟨d, bb1SimParams G ℓ g X Y t α₁⟩
          (FixedLengthScheme.splitHalf mm).1 ∧
        (bb1Scheme G ℓ).MsgSpace κ ⟨d, bb1SimParams G ℓ g X Y t α₁⟩
          (FixedLengthScheme.splitHalf mm).2 then
      .pure (bb1SimCt G ℓ κ d Z T α₁ (if b then (FixedLengthScheme.splitHalf mm).2
          else (FixedLengthScheme.splitHalf mm).1),
        (s.1, some (bb1SimCt G ℓ κ d Z T α₁ (if b then (FixedLengthScheme.splitHalf mm).2
          else (FixedLengthScheme.splitHalf mm).1))))
    else .pure (zeroBits _, s)
  | none, _ => .pure (zeroBits _, s)

/-- `Challenge` before `Init` answers `⊥`. -/
theorem bb1SimChal_none (b : Bool) (κ : ℕ) (d : List Bool) (g X Y Z : (G.group κ d).G)
    (T : (G.group κ d).GT)
    (mm : Fin ((bb1Scheme G ℓ).msgLen.eval κ + (bb1Scheme G ℓ).msgLen.eval κ) → Bool)
    (c : Option (Fin ((bb1Scheme G ℓ).ctLen.eval κ) → Bool)) :
    bb1SimChal G ℓ b κ d g X Y Z T mm (none, c) = .pure (zeroBits _, (none, c)) := rfl

/-- `Challenge` after a recorded challenge repeats it. -/
theorem bb1SimChal_repeat (b : Bool) (κ : ℕ) (d : List Bool) (g X Y Z : (G.group κ d).G)
    (T : (G.group κ d).GT)
    (mm : Fin ((bb1Scheme G ℓ).msgLen.eval κ + (bb1Scheme G ℓ).msgLen.eval κ) → Bool)
    (t : (Fin ((bb1Scheme G ℓ).idLen.eval κ) → Bool) × ZMod (G.group κ d).order)
    (w : Fin ((bb1Scheme G ℓ).ctLen.eval κ) → Bool) :
    bb1SimChal G ℓ b κ d g X Y Z T mm (some t, some w) = .pure (w, (some t, some w)) := rfl

/-- The first `Challenge` with both messages in the message space answers and records
`(M_b · T, Z, Z^{α_1})`. -/
theorem bb1SimChal_fresh (b : Bool) (κ : ℕ) (d : List Bool) (g X Y Z : (G.group κ d).G)
    (T : (G.group κ d).GT)
    (mm : Fin ((bb1Scheme G ℓ).msgLen.eval κ + (bb1Scheme G ℓ).msgLen.eval κ) → Bool)
    (t : Fin ((bb1Scheme G ℓ).idLen.eval κ) → Bool) (α₁ : ZMod (G.group κ d).order)
    (h : (bb1Scheme G ℓ).MsgSpace κ ⟨d, bb1SimParams G ℓ g X Y t α₁⟩
          (FixedLengthScheme.splitHalf mm).1 ∧
        (bb1Scheme G ℓ).MsgSpace κ ⟨d, bb1SimParams G ℓ g X Y t α₁⟩
          (FixedLengthScheme.splitHalf mm).2) :
    bb1SimChal G ℓ b κ d g X Y Z T mm (some (t, α₁), none) =
      .pure (bb1SimCt G ℓ κ d Z T α₁ (if b then (FixedLengthScheme.splitHalf mm).2
          else (FixedLengthScheme.splitHalf mm).1),
        (some (t, α₁), some (bb1SimCt G ℓ κ d Z T α₁ (if b then (FixedLengthScheme.splitHalf mm).2
          else (FixedLengthScheme.splitHalf mm).1)))) := by
  simp only [bb1SimChal]
  rw [if_pos h]

/-- The first `Challenge` with a message outside the message space answers `⊥`. -/
theorem bb1SimChal_invalid (b : Bool) (κ : ℕ) (d : List Bool) (g X Y Z : (G.group κ d).G)
    (T : (G.group κ d).GT)
    (mm : Fin ((bb1Scheme G ℓ).msgLen.eval κ + (bb1Scheme G ℓ).msgLen.eval κ) → Bool)
    (t : Fin ((bb1Scheme G ℓ).idLen.eval κ) → Bool) (α₁ : ZMod (G.group κ d).order)
    (h : ¬ ((bb1Scheme G ℓ).MsgSpace κ ⟨d, bb1SimParams G ℓ g X Y t α₁⟩
          (FixedLengthScheme.splitHalf mm).1 ∧
        (bb1Scheme G ℓ).MsgSpace κ ⟨d, bb1SimParams G ℓ g X Y t α₁⟩
          (FixedLengthScheme.splitHalf mm).2)) :
    bb1SimChal G ℓ b κ d g X Y Z T mm (some (t, α₁), none) =
      .pure (zeroBits _, (some (t, α₁), none)) := by
  simp only [bb1SimChal]
  rw [if_neg h]

/-- **The simulator's oracles** [BB04, proof of Theorem 4.1] with challenge bit `b`, at
parameter `κ`, on the description `d` and the Decision BDH tuple `(g, X, Y, Z, T)`: the three
handlers `bb1SimInit`, `bb1SimKeyQ`, `bb1SimChal` as an implementation of the game's oracles. -/
noncomputable def bb1SimImpl (b : Bool) (κ : ℕ) (d : List Bool) (g X Y Z : (G.group κ d).G)
    (T : (G.group κ d).GT) :
    QueryImpl ((bb1Scheme G ℓ).sidSpec κ) (BB1SimState G ℓ κ d) unifSpec :=
  (bb1Scheme G ℓ).oracleImpl κ (bb1SimInit G ℓ κ d g X Y) (bb1SimKeyQ G ℓ κ d g X Y)
    (bb1SimChal G ℓ b κ d g X Y Z T)

/-- `bb1SimImpl` is `oracleImpl` of the three simulator handlers. -/
theorem bb1SimImpl_eq (b : Bool) (κ : ℕ) (d : List Bool) (g X Y Z : (G.group κ d).G)
    (T : (G.group κ d).GT) :
    bb1SimImpl G ℓ b κ d g X Y Z T =
      (bb1Scheme G ℓ).oracleImpl κ (bb1SimInit G ℓ κ d g X Y) (bb1SimKeyQ G ℓ κ d g X Y)
        (bb1SimChal G ℓ b κ d g X Y Z T) := rfl

/-- **The simulation game** [BB04, proof of Theorem 4.1] for the adversary `A` with budget `q`,
challenge bit `b`, on `P_BDH` (`real`) or `R_BDH`: draw the generator's coins `r`, `g ∈ G^*`,
`a, b', c ∈ Z_p`, `T ∈ G_T` and `A`'s coins, run `A(1^κ)` against the simulator's oracles on
`(g, g^a, g^{b'}, g^c, T')` with `T' = e(g, g)^{ab'c}` if `real` and `T` otherwise, and return
`A`'s guess. -/
noncomputable def bb1SimGame (A : NUPPT) (q : ℕ) (b real : Bool) (κ : ℕ) : ProbComp Bool :=
  (ProbComp.sample (G.gen.Coins κ)).bind fun r =>
  (ProbComp.sample {x : (G.group κ (G.desc κ r)).G // x ≠ 1}).bind fun g =>
  (ProbComp.sample (ZMod (G.group κ (G.desc κ r)).order × ZMod (G.group κ (G.desc κ r)).order ×
    ZMod (G.group κ (G.desc κ r)).order)).bind fun abc =>
  (ProbComp.sample (G.group κ (G.desc κ r)).GT).bind fun t =>
  (ProbComp.sample (A.Coins κ)).bind fun ρ =>
  (simulate (bb1SimImpl G ℓ b κ (G.desc κ r) g.1 (g.1 ^ abc.1.val) (g.1 ^ abc.2.1.val)
      (g.1 ^ abc.2.2.val)
      (if real then (G.group κ (G.desc κ r)).pair g.1 g.1 ^ (abc.1 * abc.2.1 * abc.2.2).val
        else t))
    (A.toComp ((bb1Scheme G ℓ).sidCodec κ) κ q ρ) (none, none)).bind fun res => .pure (res.1 0)

/-- The simulation game draws the generator's coins, `g ∈ G^*`, `(a, b', c)`, `T` and `A`'s
coins, and simulates `A` against `bb1SimImpl` on the Decision BDH tuple. -/
theorem bb1SimGame_eq (A : NUPPT) (q : ℕ) (b real : Bool) (κ : ℕ) :
    bb1SimGame G ℓ A q b real κ =
      (ProbComp.sample (G.gen.Coins κ)).bind fun r =>
      (ProbComp.sample {x : (G.group κ (G.desc κ r)).G // x ≠ 1}).bind fun g =>
      (ProbComp.sample (ZMod (G.group κ (G.desc κ r)).order × ZMod (G.group κ (G.desc κ r)).order ×
        ZMod (G.group κ (G.desc κ r)).order)).bind fun abc =>
      (ProbComp.sample (G.group κ (G.desc κ r)).GT).bind fun t =>
      (ProbComp.sample (A.Coins κ)).bind fun ρ =>
      (simulate (bb1SimImpl G ℓ b κ (G.desc κ r) g.1 (g.1 ^ abc.1.val) (g.1 ^ abc.2.1.val)
          (g.1 ^ abc.2.2.val)
          (if real then (G.group κ (G.desc κ r)).pair g.1 g.1 ^ (abc.1 * abc.2.1 * abc.2.2).val
            else t))
        (A.toComp ((bb1Scheme G ℓ).sidCodec κ) κ q ρ) (none, none)).bind
        fun res => .pure (res.1 0) := rfl

end Simulator

end TCSlib.Cryptography.AdvancedEncryption.IdentityBased
```

## ===== TCSlib/Cryptography/AdvancedEncryption/IdentityBased/BonehBoyenMachine.lean (Lean, at 110c2f9db810d243693b9a5e8976a5ad205f1bab) =====

```lean
/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TCSlib contributors
-/
import TCSlib.Cryptography.AdvancedEncryption.IdentityBased.BonehBoyen
import TCSlib.Cryptography.Pairing.Assumptions
import TCSlib.Cryptography.Pairing.Operations

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# The BB1 simulator as a Decision BDH distinguisher

Step 3 of the security proof of [BB04, Theorem 4.1] at depth `ℓ = 1`; the other steps and the
assembled theorem `bb1_sidSecure` are in
`AdvancedEncryption/IdentityBased/BonehBoyenSecurity.lean`. The paper's algorithm `B`
[BB04, pp. 7–8] is efficient: given `(g, g^a, g^b, g^c, T)` it runs the adversary with the
simulated `Setup`, private keys and challenge, using only group operations, exponent arithmetic
modulo `p` and fresh random exponents. Here the simulation game
`bb1SimGame` (defined beside the scheme in `AdvancedEncryption/IdentityBased/BonehBoyen.lean`)
uses ideal uniform exponents, and the step shows that it is, up to a negligible statistical term,
the Decision BDH experiment of a non-uniform PPT distinguisher (the machine step: handler theorem
T1 with exponents drawn from coin blocks).

This step is its own module so that it can be filled independently of the coupling steps
`bb1_sim_real` and `bb1_sim_random` (ruling Q11 of `PairingCryptographyPlan.md`).

## Main definitions

None.

## Main results

* `exists_bb1_distinguisher` — the simulation is a Decision BDH distinguisher (step 3).

## References

* [BB04] D. Boneh, X. Boyen, *Efficient Selective-ID Secure Identity Based Encryption Without
  Random Oracles*, full version, Cryptology ePrint Archive, Report 2004/172, December 2004
  (extended abstract: EUROCRYPT 2004, LNCS 3027, pp. 223–238). §4.2 (pp. 6–8): Theorem 4.1 and
  its proof.
* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed., January 2010.
  (Definition 26.8, non-uniform PPT.)
-/

namespace TCSlib.Cryptography.AdvancedEncryption.IdentityBased

open Complexity Turing TCSlib.Cryptography.Games TCSlib.Cryptography.Pairing
  TCSlib.Cryptography.Composability

variable (G : BilinearGen) (ℓ : PolyExpr)

/-- **Step 3: the simulation is a Decision BDH distinguisher**: with efficient group operations
`O` and the arithmetic bundle `H`, for every adversary `A` and polynomial budget `q` there are
non-uniform PPT distinguishers `D_b` and a negligible `σ` with
`|Pr[bb1SimGame … b real = 1] − Pr[dbdhGame (D_b) real = 1]| ≤ σ(κ)` for both tuple
distributions.

**Proof sketch.** `D_b` parses `⟨d, ⟨g, ⟨X, ⟨Y, ⟨Z, T⟩⟩⟩⟩⟩` and runs `A` with the handler of
`bb1SimImpl`: group operations by `O.mulG`, `O.powG`, `O.mulT`, membership by `O.memT`, exponent
arithmetic modulo `p = O.orderStr d` with `H` (negation, difference, inverse via `xgcd`,
product), and `α_1` and every `r` read from its own coin blocks by the rejection sampler
`Candidates.sampleBelowL` with `wG(κ)`-bit trials (`p ≤ 2^{wG}`, as `encG` is injective). The
handler is polynomial-time with polynomial state, so the handler theorem
`Games.exists_handlerMachine` (T1) makes the run a machine whose output is exactly `A`'s guess
in a game equal to `bb1SimGame` with sampled instead of ideal exponents. The at most `q(κ) + 1`
sampled exponents are each within `2^{−κ}` of uniform (`statClose_sampleBelowL`), so
`σ(κ) = (q(κ) + 1) · 2^{−κ}` works (hybrid over the samples). -/
theorem exists_bb1_distinguisher (H : Candidates.ArithmeticFP) (O : G.Ops) (A : NUPPT)
    (q : PolyExpr) :
    ∃ D : Bool → NUPPT, ∃ σ : ℕ → ℝ, Negligible σ ∧ ∀ (b real : Bool) (κ : ℕ),
      advantage (bb1SimGame G ℓ A (q.eval κ) b real κ) (G.dbdhGame (D b) real κ) ≤ σ κ := by
  sorry

end TCSlib.Cryptography.AdvancedEncryption.IdentityBased
```

## ===== TCSlib/Cryptography/AdvancedEncryption/IdentityBased/BonehBoyenSecurity.lean (Lean, at 110c2f9db810d243693b9a5e8976a5ad205f1bab) =====

```lean
/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TCSlib contributors
-/
import TCSlib.Cryptography.AdvancedEncryption.IdentityBased.BonehBoyen
import TCSlib.Cryptography.AdvancedEncryption.IdentityBased.BonehBoyenMachine
import TCSlib.Cryptography.Pairing.Assumptions

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Selective-identity security of BB1 under Decision BDH

[BB04, Theorem 4.1] at depth `ℓ = 1`: if Decision BDH holds in `G`, the BB1 system is
IND-sID-CPA secure. The proof [BB04, pp. 7–8] builds a Decision BDH algorithm `B` that, given
`(g, g^a, g^b, g^c, T)`, plays the selective-identity game with the adversary without knowing the
master key `g^{ab}`:
* **Setup**, once `ID*` is committed: a random `α_1 ∈ Z_p`, `h = g_1^{−ID*} g^{α_1}`,
  `params = (g, g_1 = g^a, g_2 = g^b, h)`, so that `F(x) = g_1^{x − ID*} g^{α_1}`;
* **private keys** for `ID ≠ ID*`: a random `r ∈ Z_p`,
  `(g_2^{−α_1/(ID − ID*)} F(ID)^r, g_2^{−1/(ID − ID*)} g^r)`;
* **the challenge**: `(M_b · T, g^c, (g^c)^{α_1})`.

**The simulation game.** `bb1SimGame` (defined beside the scheme in
`AdvancedEncryption/IdentityBased/BonehBoyen.lean`) is that simulator as a game of the `Games`
framework, with ideal uniform exponents, run against the adversary machine on a Decision BDH
tuple drawn from `P_BDH` (`real`) or `R_BDH`. The security proof has three named steps:
1. `bb1_sim_real`: on `P_BDH`, the simulation is the real game, except when distinct
   identities collide in `Z_p` (the generator's coins with `p < 2^ℓ`);
2. `bb1_sim_random`: on `R_BDH`, the simulation does not depend on the challenge bit;
3. `exists_bb1_distinguisher`: the simulation is, up to a negligible statistical term, the
   Decision BDH experiment of a non-uniform PPT distinguisher (the machine step: handler theorem
   T1 with exponents drawn from coin blocks). It is stated in its own module,
   `AdvancedEncryption/IdentityBased/BonehBoyenMachine.lean`, so that it can be filled
   independently of steps 1 and 2 (ruling Q11 of `PairingCryptographyPlan.md`).
`bb1_sidSecure` assembles them by the triangle inequality.

**Deviation:** the paper's `B` draws the challenge bit itself and outputs `[b = b']`; here there
is one simulation per value of `b`, and the advantage of the two-experiment form is bounded by
the sum of two Decision BDH advantages; the paper's statement is concrete (`t' < t − Θ(τ ℓ q_S)`).

## Main definitions

None: the simulator (`bb1SimImpl`, `bb1SimGame`) is defined beside the scheme, in
`AdvancedEncryption.IdentityBased.BonehBoyen`.

## Main results

* `bb1_sim_real`, `bb1_sim_random` — steps 1 and 2 (step 3, `exists_bb1_distinguisher`, is in
  `AdvancedEncryption.IdentityBased.BonehBoyenMachine`).
* `bb1_sidSecure` — [BB04, Theorem 4.1] at depth 1.

## References

* [BB04] D. Boneh, X. Boyen, *Efficient Selective-ID Secure Identity Based Encryption Without
  Random Oracles*, full version, Cryptology ePrint Archive, Report 2004/172, December 2004
  (extended abstract: EUROCRYPT 2004, LNCS 3027, pp. 223–238). §4.2 (pp. 6–8): Theorem 4.1 and
  its proof; §4.4 (p. 8).
* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed., January 2010.
  (Definition 26.8, non-uniform PPT.)
-/

namespace TCSlib.Cryptography.AdvancedEncryption.IdentityBased

open Complexity Turing TCSlib.Cryptography.Games TCSlib.Cryptography.Pairing
  TCSlib.Cryptography.Composability

variable (G : BilinearGen) (ℓ : PolyExpr)

/-- **Step 1: on `P_BDH` the simulation is the real game** [BB04, proof of Theorem 4.1, "When
the input 5-tuple is sampled from `P_BDH` … `A`'s view is identical to its view in a real attack
game"], except on the generator's coins where `p < 2^ℓ`, where distinct identities may collide
in `Z_p`.

**Proof sketch.** Fix coins with `2^ℓ ≤ p`, so `idToZ` is injective on `ℓ`-bit strings
(`bitsToNat_lt`, `bitsToNat_injective`). Couple the two games: the real `Setup` draws
`(g, α, h, g_2)`, the simulation `(g, a, b', c)` and, at `Init`, `α_1`. Map `α ↦ a`,
`g_2 ↦ g^{b'}` and `h ↦ g_1^{−ID*} g^{α_1}` (a bijection in `α_1` for each `ID*`, so `h` is uniform
and independent; `expect_sample_equiv`). Answers to `Init` agree. For `ID ≠ ID*` the simulated
key with exponent `r` is the real key with exponent `r̃ = r − b'/(ID − ID*)`, a bijection of
`Z_p` (the paper's computation, `pow_val_mul`, `bilinear_pow`). The challenge is `Encrypt` with
`s = c`, since `F(ID*) = g^{α_1}` and `e(g, g)^{ab'c} = e(g_1, g_2)^c`. The state machines agree
step by step (`simulate` with matched implementations, `Games.expect_simulate_congr`), so the
acceptance probabilities differ only on the excluded coins, of probability
`Pr_r[p < 2^ℓ]`. -/
theorem bb1_sim_real (A : NUPPT) (q : ℕ) (b : Bool) (κ : ℕ) :
    advantage ((bb1Scheme G ℓ).sidGame A q b κ) (bb1SimGame G ℓ A q b true κ) ≤
      uprob (fun r : G.gen.Coins κ => (G.inst κ r).order < 2 ^ ℓ.eval κ) := by
  sorry

/-- **Step 2: on `R_BDH` the simulation does not depend on the challenge bit** [BB04, proof of
Theorem 4.1, "when `T` is uniform and independent in `G_1` … `C` is independent of `b` in the
adversary's view"].

**Proof sketch.** In the `R_BDH` game, `T` is uniform in `G_T` and is used only in the first
component `M_b · T` of the challenge. For each fixed run up to the challenge, `T ↦ M_b · T` is a
bijection of `G_T`, so exchanging the sample of `T` with the rest of the game
(`expect_expect_sample`) and reindexing it by `T ↦ M_b^{−1} M_{1−b} · T`
(`expect_sample_equiv`) turns the game with `b = 0` into the game with `b = 1`. Challenges
outside the message space are refused in both games. -/
theorem bb1_sim_random (A : NUPPT) (q : ℕ) (κ : ℕ) :
    advantage (bb1SimGame G ℓ A q false false κ) (bb1SimGame G ℓ A q true false κ) = 0 := by
  sorry

/-- **BB1 is IND-sID-CPA secure under Decision BDH** [BB04, Theorem 4.1, at depth `ℓ = 1`]: if
the generator's groups have efficient operations, the arithmetic bundle holds, the order is at
least `2^{ℓ(κ)}` except with negligible probability, and Decision BDH holds, then the BB1 system
for `ℓ(κ)`-bit identities is IND-sID-CPA secure.

**Deviation:** asymptotic form of the paper's concrete bound (`(t', q_S, ε)`-security from
`(t, ε)`-Decision BDH); the efficiency hypotheses `O` and `H` make the paper's simulator a
non-uniform PPT; `hN` makes distinct `ℓ`-bit identities distinct in `Z_p` (the condition
`2^b < p` of [BB04, §4.4]); the advantage is bounded by two Decision BDH advantages, one per
challenge bit, instead of one.

**Proof sketch.** By the triangle inequality through the simulation games and the Decision BDH
experiments of the two distinguishers `D_0`, `D_1` of step 3,
`advantage (sidGame … false) (sidGame … true)` is at most
`2 Pr_r[p < 2^ℓ] + 4σ(κ) + dbdhAdv D_0 κ + dbdhAdv D_1 κ` (steps 1 and 3 for each bit, step 2
in the middle). Each term is negligible (`hN`, step 3, `h`). -/
theorem bb1_sidSecure (H : Candidates.ArithmeticFP) (O : G.Ops)
    (hN : ∃ δ : ℕ → ℝ, Negligible δ ∧ G.OrderAtLeastExcept (fun κ => 2 ^ ℓ.eval κ) δ)
    (h : G.DBDHAssumption) : (bb1Scheme G ℓ).SIDSecure := by
  rw [IBEScheme.sidSecure_iff]
  intro A q
  obtain ⟨δ, hδ, hN⟩ := hN
  obtain ⟨D, σ, hσ, hD⟩ := exists_bb1_distinguisher G ℓ H O A q
  refine ⟨fun κ => 2 * δ κ + 4 * σ κ + (G.dbdhAdv (D false) κ + G.dbdhAdv (D true) κ),
    ((hδ.const_mul 2).add (hσ.const_mul 4)).add
      ((G.dbdhAssumption_iff.1 h (D false)).add (G.dbdhAssumption_iff.1 h (D true))), fun κ => ?_⟩
  have hu := (G.orderAtLeastExcept_iff _ δ).1 hN κ
  have t := fun G₀ G₁ G₂ : ProbComp Bool => advantage_triangle G₀ G₁ G₂
  have hc := fun G₀ G₁ : ProbComp Bool => advantage_comm G₀ G₁
  have s0 := bb1_sim_real G ℓ A (q.eval κ) false κ
  have s1 := bb1_sim_real G ℓ A (q.eval κ) true κ
  have s2 := bb1_sim_random G ℓ A (q.eval κ) κ
  have d0T := hD false true κ
  have d0F := hD false false κ
  have d1T := hD true true κ
  have d1F := hD true false κ
  have a0 := G.dbdhAdv_eq (D false) κ
  have a1 := G.dbdhAdv_eq (D true) κ
  set S0 := (bb1Scheme G ℓ).sidGame A (q.eval κ) false κ
  set S1 := (bb1Scheme G ℓ).sidGame A (q.eval κ) true κ
  set M0T := bb1SimGame G ℓ A (q.eval κ) false true κ
  set M0F := bb1SimGame G ℓ A (q.eval κ) false false κ
  set M1T := bb1SimGame G ℓ A (q.eval κ) true true κ
  set M1F := bb1SimGame G ℓ A (q.eval κ) true false κ
  set E0T := G.dbdhGame (D false) true κ
  set E0F := G.dbdhGame (D false) false κ
  set E1T := G.dbdhGame (D true) true κ
  set E1F := G.dbdhGame (D true) false κ
  have := t S0 M0T S1
  have := t M0T E0T S1
  have := t E0T E0F S1
  have := t E0F M0F S1
  have := t M0F M1F S1
  have := t M1F E1F S1
  have := t E1F E1T S1
  have := t E1T M1T S1
  have := hc E0T E0F
  have := hc E0F M0F
  have := hc E1T M1T
  have := hc M1T S1
  linarith

end TCSlib.Cryptography.AdvancedEncryption.IdentityBased
```

## ===== TCSlib/Cryptography/Pairing.lean (Lean, at 110c2f9db810d243693b9a5e8976a5ad205f1bab) =====

```lean
/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TCSlib.Cryptography.Pairing.Group
import TCSlib.Cryptography.Pairing.Assumptions
import TCSlib.Cryptography.Pairing.Operations

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Symmetric bilinear groups and the bilinear Diffie–Hellman assumptions

## Contents

* `Group`: abstract symmetric bilinear groups of prime order, their generators, bilinearity and
  non-degeneracy facts.
* `Assumptions`: the BDH and Decision BDH experiments and assumptions; Decision BDH implies BDH.
* `Operations`: the efficiency contract of a generator (group operations and pairing as
  polynomial-time string functions).

## References

* [BB04] D. Boneh, X. Boyen, *Efficient Selective-ID Secure Identity Based Encryption Without
  Random Oracles*, full version, Cryptology ePrint Archive, Report 2004/172, December 2004,
  §2.2 and §3.1.
* [Jou00] A. Joux, *A One Round Protocol for Tripartite Diffie–Hellman*, ANTS-IV, LNCS 1838,
  pp. 385–393, Springer, 2000.
-/
```

## ===== TCSlib/Cryptography/KeyExchange.lean (Lean, at 110c2f9db810d243693b9a5e8976a5ad205f1bab) =====

```lean
/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TCSlib.Cryptography.KeyExchange.Joux

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Key exchange

## Contents

* `Joux`: Joux's one-round tripartite Diffie–Hellman over a symmetric bilinear group, its
  correctness and its key indistinguishability under Decision BDH.

## References

* [Jou00] A. Joux, *A One Round Protocol for Tripartite Diffie–Hellman*, ANTS-IV, LNCS 1838,
  pp. 385–393, Springer, 2000.
-/
```

## ===== TCSlib/Cryptography/AdvancedEncryption/IdentityBased.lean (Lean, at 110c2f9db810d243693b9a5e8976a5ad205f1bab) =====

```lean
/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TCSlib.Cryptography.AdvancedEncryption.IdentityBased.Defs
import TCSlib.Cryptography.AdvancedEncryption.IdentityBased.BonehBoyen
import TCSlib.Cryptography.AdvancedEncryption.IdentityBased.BonehBoyenMachine
import TCSlib.Cryptography.AdvancedEncryption.IdentityBased.BonehBoyenSecurity

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Identity-based encryption

## Contents

* `Defs`: IBE systems, perfect correctness and selective-identity chosen-plaintext security
  (IND-sID-CPA).
* `BonehBoyen`: the Boneh–Boyen BDH-based system (BB1) over a bilinear group generator and its
  correctness.
* `BonehBoyenMachine`: the simulator as a non-uniform PPT Decision BDH distinguisher (step 3 of
  the security proof).
* `BonehBoyenSecurity`: the coupling steps of the security proof, and IND-sID-CPA security of
  BB1 under Decision BDH.

## References

* [BB04] D. Boneh, X. Boyen, *Efficient Selective-ID Secure Identity Based Encryption Without
  Random Oracles*, full version, Cryptology ePrint Archive, Report 2004/172, December 2004.
-/
```

## ===== TCSlib/Cryptography/AdvancedEncryption.lean (Lean, at 110c2f9db810d243693b9a5e8976a5ad205f1bab) =====

```lean
/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TCSlib.Cryptography.AdvancedEncryption.IdentityBased

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Advanced encryption primitives

Encryption primitives beyond private-key and public-key encryption.

## Contents

* `IdentityBased`: identity-based encryption, selective-identity security and the Boneh–Boyen
  system (BB1).

## References

* [BB04] D. Boneh, X. Boyen, *Efficient Selective-ID Secure Identity Based Encryption Without
  Random Oracles*, full version, Cryptology ePrint Archive, Report 2004/172, December 2004.
-/
```
