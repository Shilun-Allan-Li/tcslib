# Claude fill · simulation-based and indistinguishability-based non-malleability (`nmSecure_of_simNMSecure`, `simNMSecure_of_nmSecure_cpa`)

**Issue base** `262d6e9ae526c82eb68fe5a6169156bd1504e6d8` on `cryptography/pass-shelat-ch2-4` (the merge of #294).
**Unit** `nm-sim`. **Worker** Claude (standing ruling, 2026-11-11). **Lean** 4.25.0 and the Mathlib revision in that
commit's `lake-manifest.json`.

Prove the two admitted theorems of [PS10, Theorem 174.8], in the form of [PSV07] (SIM-NME′ at one message), in
`TCSlib/Cryptography/Encryption/PublicKey/NonMalleability/Simulation.lean`. With them,
`simNMSecure_cpa_iff_nmSecure_cpa` (already proved from the two) becomes admission-free, and the non-malleability
chapter has no admissions left. The statements passed their Gate 06 audit (#232).

**This fill runs in parallel with the landing of the `dl-consolidation` job**, which moves the generic lemmas of
duplication-ledger rows DL-30 to DL-34. Read the duplication rule below.

## Checkout and delivery

- Fetch `cryptography/pass-shelat-ch2-4`. Start a local branch `fill/nm-sim` at the exact issue base, and record
  the base in `REPORT.md`. Keep the proof branch local.
- Read `policy.md`, the attached environment addendum and `README.md`.
- Deliver every checkpoint and the final payload under `inbox/fills/nm-sim/` on `exchange/pass-shelat-ch5-8`:
  - `REPORT.md`;
  - `patches/`: the whole `git format-patch` series from the issue base;
  - `src/`: the changed files;
  - `evidence/`;
  - `SHA256SUMS` over the whole payload.
- Commit as `fill nm-sim: checkpoint N` and `fill nm-sim: final`.
- Pull with rebase before pushing, push only your delivery path, and never force-push. Campaign changes land by
  a maintainer PR for Seyoon's approval.

## Targets (frozen; quoted from the issue base)

```lean
theorem nmSecure_of_simNMSecure (atk : Attack) (h : S.SimNMSecure atk) : S.NMSecure atk := by
  sorry

theorem simNMSecure_of_nmSecure_cpa (h : S.NMSecure .cpa) : S.SimNMSecure .cpa := by
  sorry
```

They live in namespace `TCSlib.Cryptography.Composability.FixedLengthPKScheme`, with `S : FixedLengthPKScheme`.
- **`SimNMSecure atk`** (`SimNMSecure_iff`): for every sampler `M : MsgSampler`, adversary `A` and polynomials
  `q`, `r`, `sl`, there is a simulator `Sim` such that every distinguisher `D` has negligible advantage between
  `snmReal atk M A q r sl D` and `snmIdeal M Sim r sl D`.
  - In `snmIdeal` the simulator runs through `simCodec` **with query budget 1** (`Sim.toCompOn … n 1 …`).
- **`NMSecure atk`** (`NMSecure_iff`, `nmGame_eq`, in `NonMalleability/Indistinguishability.lean`): for all `A`,
  `q`, `ℓ` and `D`, negligible advantage between `nmGame atk A q ℓ D false` and `true`.

Each target's docstring sketch is the maintainer's route. You may edit a sketch to describe the delivered proof.

## Published interfaces

| Interface | Provider |
|---|---|
| `MsgSampler` and `draw_eq`, `histAt_eq`, `simSpec_eq`; `snmInLens_*`, `snmOutLens_*`, `snmSpec_eq`, `SnmState_eq`, `snmImpl_dec`, `snmImpl_challenge`, `snmImpl_dec_cpa`, `snmCodec_*`, `snmCt_eq`, `snmSigma_eq`, `snmEntry_eq`, `snmView_eq`, `snmReal_eq`, `simImpl_eq`, `simCodec_*`, `simEntry_fst/_snd`, `snmIdeal_eq`, `SimNMSecure_iff` | `NonMalleability/Simulation.lean` (owned; the statement-phase readers) |
| `nmCodec_*`, `nthCt_eq`, `nmDecrypt_eq`, `nmDecrypt_challenge`, `nmOutput_eq`, `nmGame_eq`, `NMSecure_iff`, and the proved Theorem 175.9 | `NonMalleability/Indistinguishability.lean` |
| Public helpers of Theorem 175.9: `fwdHandler`, `fwdHandler_impl`, `simulate_fwdHandler_impl`, the `fin*` readers, `logEmit` and its lemmas (`Forward`); `cntRead`, `ansRead`, `exists_withAdviceOn`, the decrypting finalization (`Decrypt`); `encHandler`, `guessBit`, `guessBit_valid`, `guessBit_refused`, `guessDist_nmOutput`, `indImpl_eq_of_msgLen_eq_zero` (`Encrypt`) | `NonMalleability/Indistinguishability/{Forward,Decrypt,Encrypt}.lean` (models and reusable lemmas; import them, do not copy) |
| `FixedLengthPKScheme` fields (`correct`, `enc_length`, `gen_uniform`, …), `inLens_*`, `outLens_*`, `indSpec_*` (incl. `indSpec_decRng`), `indImpl_dec_onSpec(_cast)`, `indImpl_challenge_*`, `indCodec_*`, `indGame_eq`, `INDSecure_iff` | `PublicKey/OracleSecurity.lean` |
| `FixedLengthScheme.decAnswer`, `decOpen_*` and their readers | `PrivateKey/OracleSecurity.lean` |
| T1 `Games.exists_handlerMachine`, T2 `Games.exists_interactiveHandlerMachine`, `exists_toCompOn_of_toComp`, T4 `exists_toOracleAdversary_of_bitCodec`, the `PolyHandler`/`InteractiveHandler` readers (`call`: **at most** `perCall(n)` outer queries per inner call) | `Games/Efficiency.lean` |
| `buildComp_*` (incl. `buildComp_costBoundedBy`), `CostBoundedBy` (`.mono`, `.bind`), `bitCodec_*`, `decodeBitMove`, `simulate` equations, `OracleComp` laws, `advantage_eq`, `accept_eq` | `Games/*` |
| `NUPPT.exists_comp`, `exists_compParam`, `exists_withAdvice`, `exists_seq`, `exists_reparam`; `NUPPT` run/coin readers; `distinguisherL_eq`; `Negligible` closure (`Negligible.add`, scalar multiples) | `Complexity/Randomized/Closure.lean`, `Asymptotic/*`, `Foundations/Negligible.lean` |

## Proof route and checkpoints

1. **SIM ⇒ IND, every attack** (`nmSecure_of_simNMSecure`; the target's sketch). Given an NM adversary `A`
   (budget `q`, `ℓ` ciphertexts) and a distinguisher `D`:
   - the sampler `M` with parameter `⟨m₀, m₁⟩` (`paramLen = msgLen + msgLen`, the IND challenge layout) that
     outputs `m_β` for its first coin bit `β`, with a constant history (`histLen = 0`);
   - the SIM adversary `A'` forwards `A`'s `Dec` and challenge queries (a T2 handler with one outer call per
     inner query, like `fwdHandler`), outputs `A`'s `ℓ` ciphertexts, `r = ℓ`, `sl = 0`;
   - take `Sim` from `h M A' q ℓ 0`;
   - `D'` reads `a = ⟨m₀, m₁⟩` and `m` from the view, outputs `0` when `m₀ = m₁`, and otherwise whether `D`'s
     verdict on the entries (with `COPY` read as `nmDecrypt`'s `⊥`) equals the `β` with `m = m_β`; `D''` tests
     `m₀ ≠ m₁`.
   - **Real:** given `β`, `snmReal` is `NM_β` (the `Dec` and challenge oracles agree with `indImpl`, refusal and
     `⊥` included). So `NM`'s advantage is `2·(Pr_real[D' = 1] − ½·Pr_real[m₀ ≠ m₁])`.
   - **Ideal:** the simulator's view is independent of `β` (constant history; `β` is a coin of the sampler only),
     so `Pr_ideal[D' = 1] = ½·Pr_ideal[m₀ ≠ m₁]`.
   - Hence `NM`'s advantage is at most `2·adv(D') + adv(D'')`, both negligible (one `Sim` for all
     distinguishers).

   Send checkpoint 1.
2. **IND ⇒ SIM under CPA** (`simNMSecure_of_nmSecure_cpa`; the target's sketch). Fix `M`, `A`, `q`, `r`, `sl`.
   - **The simulator** runs `A` on `pk`, answering `Dec` with `⊥` (`snmImpl_dec_cpa`). On `A`'s first challenge `a`
     it makes its **only** outer query `a`, gets `h(m)`, draws `m̃ ← M(a)` with its own coins (it runs `M`, with
     `M`'s advice hard-wired as in `exists_withAdviceOn`), encrypts `ỹ ← Enc_pk(m̃)` and answers `⟨ỹ, h(m)⟩`;
     repeated challenges get the recorded answer without an outer query. It outputs `A`'s `r` ciphertexts, each
     flagged `COPY` iff it equals `ỹ`, and `σ`. If `A` never asks, it never queries.
   - **The query budget.** T2 gives the simulator's machine at budget `q·perCall + finCall`; `snmIdeal` runs it at
     budget 1. The handler makes at most one outer query on every path, so prove the generic budget reduction:
     a machine whose computation at budget `K ≥ j` is `CostBoundedBy` `j` has the same computation at budget `j`
     (induction on `buildComp` with `buildComp_succ_of_ret/_of_query`). Put it in a helper and list it as a
     promotion request for `Games/Machines.lean`.
   - **The NM adversary** `B`: on `a` it draws `m, m̃ ← M(a)`, asks its challenge on `⟨m, m̃⟩`, answers `A` with
     `⟨y, h(m)⟩`; it outputs `A`'s ciphertexts, then for each bit `x` of `a`, `m`, `σ` and the copy flags
     `[c_i = y]` the pair `Enc_pk(x^{msgLen})`, `Enc_pk((¬x)^{msgLen})` (reuse `guessBit`, `guessBit_valid`,
     `guessBit_refused` and the encryption lemmas of `Indistinguishability/Encrypt.lean`).
   - The NM distinguisher reconstructs `(a, m, (d_i)_i, σ)` and runs `D`: `NM_0` is the real experiment and `NM_1`
     the ideal one with the simulator above. So the SIM advantage equals `B`'s NM advantage at each `n` with
     `msgLen(n) > 0`.
   - At `msgLen(n) = 0`, `m = m̃` and the real and ideal experiments coincide, so the advantage is 0.
   - If `A` never asks, both experiments use `a = 0^{paramLen(n)}`.

   Send checkpoint 2.
3. **Final.** Both targets proved; `simNMSecure_cpa_iff_nmSecure_cpa` admission-free. Send the final delivery.

Check the edge cases:
- budget 0;
- `r = 0`, `sl = 0`;
- `msgLen(n) = 0`;
- no challenge asked;
- repeated challenges;
- `A` outputting the challenge itself, or a malformed or invalid ciphertext;
- the codecs' timeout outputs, in every direction;
- `m₀ = m₁` (SIM ⇒ IND).

If either sketch is wrong, or a target is false as stated, stop and escalate with the exact obligation (a
checkpoint with the counterexample or the missing fact). Do not weaken a statement.

## Scope and proof discipline

- **Owned file.** You own `NonMalleability/Simulation.lean`: replace the two proof bodies, edit their sketches,
  and update the module title (drop "(statement phase)") and the `## Main results` status.
- **Helper modules.** Permitted under `TCSlib/Cryptography/Encryption/PublicKey/NonMalleability/Simulation/`. The
  owned file imports them precisely and gets a `## Contents` list.
- **Size.** Keep every file below 1000 lines.
- **Frozen.** Do not edit any other file. `PublicKey/OracleSecurity.lean` is at 999 lines and will be split at the
  consolidation's landing: request any reader for it in `REPORT.md`, with its exact statement. If a lemma belongs
  in an existing file, put it in your helper module and list it as a promotion request. If a reader of another
  file's definition is missing, escalate: record the exact obligation and the reader you need, and push a
  checkpoint.
- **Duplication (binding).**
  - Do not copy public lemmas: import them where they are at the issue base (including the Theorem 175.9 helpers
    above). The maintainer re-points them at landing if the consolidation has moved them.
  - Do not copy private lemmas from `AdaptiveCPA/`, `BitwiseCPA/`, `OracleFromPRF/` or
    `NonMalleability/Indistinguishability/`. If you need one, re-derive it from published readers in your helper
    module, disclose it in `REPORT.md` as **"DL-30–36 overlap: <item>"**, and keep its statement in the general
    form.
  - Any other generic probability, simulation, machine or list fact goes on your promotion list. Grep first.
- **Statements.** Preserve both target statements, every other declaration, the statement prose and the global
  simp attributes.
- **Docstrings.** Public helpers get docstrings with their formulas, and proof sketches when nontrivial (policy §3).
  No `@[simp]`; a new public `abbrev` needs an `_eq`/`_iff` lemma.
- **Rule 10.** Use only published readers for other files' definitions, including generated matchers and
  projections. Your helper modules count as foreign to each other and to the owned file.

## Checks and report

- **Bootstrap.** Bootstrap from `order.txt` (252 modules) and the narrow `roots.txt` (97) per the addendum. Check
  one module per `scripts/lean_check_tree.sh` call, with one Lean process per olean tree. Insert helper modules
  before their consumers.
- **Sweep.** Recheck the owned modules, then sweep the supplied order. Compare the `sorry` warnings with
  `base-sorries.txt` (26): the only change must be the removal of the two targets.
- **Axioms.**
  - Print the axioms of both targets and of `simNMSecure_cpa_iff_nmSecure_cpa`. Expect only `propext`,
    `Classical.choice` and `Quot.sound`.
  - Print them for every stored constant of the changed and new files.
- **Rule 10 evidence.**
  - Run whole-file seals of every changed or new file over its full TCSlib import closure, with base controls and
    paired controls that pass unsealed and fail sealed.
  - Run the explicit-unfold scan.
  - Report the seal both with `PolyExpr.eval` excluded as notation and with it sealed.
- **Lint.** Run `python3 -I scripts/campaign_style_lint.py TCSlib/Cryptography/Encryption/PublicKey --check8b`.
- **Report.** Give:
  - the base and the targets' status;
  - the changed files and the sketch edits;
  - the new declarations;
  - the promotion and reader requests, and every "DL-30–36 overlap" item;
  - the evidence.
