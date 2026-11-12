# Fill `nm-cca2` — final

**Worker:** Claude (external). **Issue base:** `b96ab3ccc1915497ea3138df499eec00b6581db0` on
`cryptography/pass-shelat-ch2-4` (the merge of #293). **Local proof branch:** `fill/nm-cca2`, head
`9bd89494b`, never pushed; the whole series from the base is in `patches/` (4 patches). **Pack:** read
at exchange `3f6d6783a1e4527e5287c63a9f1a0075fb6d0369`; `SHA256SUMS` 7/7 OK; all 249 entries of
`SOURCE-SHA256SUMS` match the base. **Checkpoints on the exchange:**
- `f3878eb2b`, checkpoint 1: (⇒) and escalation E-READER;
- `bd936f02c`, checkpoint 2: (⇐) and the target.

## 1. Target status

`TCSlib.Cryptography.Composability.FixedLengthPKScheme.indSecure_cca2_iff_nmSecure_cca2`
[PS10, Theorem 175.9] is **proved**. Its statement is byte-identical to the base (`… := by`), and
the body is `exact ⟨S.nmSecure_cca2_of_indSecure_cca2, S.indSecure_cca2_of_nmSecure_cca2⟩`.

`#print axioms` (`evidence/logs/axioms.log`, probe `evidence/seal/Axioms.lean`):
- `indSecure_cca2_iff_nmSecure_cca2`: `[propext, Classical.choice, Quot.sound]`;
- `simNMSecure_cpa_iff_nmSecure_cpa`: `[propext, sorryAx, Classical.choice, Quot.sound]`. It still depends on the two
  `Simulation.lean` targets.
- **Every stored constant** of the five changed or new files (170 constants, auxiliary
  declarations included) depends on a subset of `[propext, Classical.choice, Quot.sound]`;
  0 fall outside it.

**One open item: escalation E-READER (§2).** A reader of `PublicKey/OracleSecurity.lean` is missing.
The proof states it in one helper module, and its proof is the fill's only definitional reading
of a foreign definition (`outLens`). It must move to its home file at landing.

## 2. Escalation E-READER: the public-key decryption answer has no cast reader

(First reported at checkpoint 1; unchanged.)

**Obligation.** In (⇒) the CCA2 adversary asks its decryption oracle for each of `A`'s ciphertexts
and must show that the answers, read as strings, are `NM_b`'s decryptions. On T2's codec the
oracle's answer to a query `x` in state `st` is (`castImpl_eq`, then `indImpl_dec_onSpec`,
`decOpen_cca2`):

```
padFin ((acDout S 0).eval n) (List.ofFn p.1),   p.1 = FixedLengthScheme.decAnswer X   (valid branch)
```

where `X = decodeFin _ (S.dec ⟨sk, c⟩)`. `FixedLengthPKScheme.indImpl_dec_onSpec` states this
`decAnswer X` (`: Fin (S.msgLen.eval n + 1) → Bool`) at the oracle's answer type
`(S.indSpec n).rng 0 = Fin (S.outLens n 0) → Bool` **without a cast**: the types agree only by
unfolding `outLens`. So `List.ofFn p.1` is `List.ofFn` at width `S.outLens n 0`. Relating it to
`⟦S.nmDecrypt sk st c⟧` (width `msgLen + 1`) leaves, after every published reader, the goal

```
HEq ((decAnswer X, st).1 : Fin (S.outLens n 0) → Bool) (decAnswer X : Fin (S.msgLen.eval n + 1) → Bool)
```

With `outLens` sealed this cannot be closed. `HEq.rfl`, `cast_eq` and rewriting under `Prod.mk`
(`decAnswer_some`/`_none`, `outLens_zero`) all need the two widths to be definitionally equal
(`evidence/probes/EscNoReader.lean`, `logs/escalation-EscNoReader.log`, which shows the state).

**Reader requested** for `PublicKey/OracleSecurity.lean`. This is the public-key analogue of what
not-cca2 r2 added to `PrivateKey/OracleSecurity.lean`:

```lean
/-- The decryption oracle answers a validity flag and a message. -/
theorem FixedLengthPKScheme.indSpec_decRng (n : ℕ) :
    (S.indSpec n).rng 0 = (Fin (S.msgLen.eval n + 1) → Bool) := by
  rw [S.indSpec_rng, S.outLens_zero]

/-- `indImpl_dec_onSpec` with the valid answer read through `indSpec_decRng`. -/
theorem FixedLengthPKScheme.indImpl_dec_onSpec (atk) (b) (n) (pk sk) (c : (S.indSpec n).dom 0) (s) :
    S.indImpl atk b n pk sk 0 c s =
      if FixedLengthScheme.decOpen atk s.isSome && !decide (s = some (cast (S.indSpec_decDom n) c))
      then .pure (cast (S.indSpec_decRng n).symm (FixedLengthScheme.decAnswer
        (decodeFin _ (S.dec (pairEncode sk (List.ofFn (cast (S.indSpec_decDom n) c)))))), s)
      else .pure (zeroBits _, s) := by
  simpa only [cast_eq] using S.indImpl_dec_onSpec atk b n pk sk c s   -- (the current statement)
```

I recommend adding the second **beside** `indImpl_dec_onSpec` under a new name (for example
`indImpl_dec_onSpec_cast`), which leaves every consumer untouched. `indImpl_dec_onSpec` is used at
the base by `AdaptiveSecurity` (`adaptiveIndImpl_one`, which rewrites both sides with it), and by
`AdaptiveCPA/Games` and `BitwiseCPA/Eager` (the refused branch under CPA). Replacing its statement
instead would require rechecking those three files. Its proof unfolds `outLens`, which is legitimate
only in `OracleSecurity.lean`.

**What the fill does.** `Indistinguishability/Readers.lean` states both readers exactly as above,
as `NMCCA2.indSpec_decRng` and `NMCCA2.indImpl_dec_onSpec_cast`.
- The first is proved from published readers (`indSpec_rng`, `outLens_zero`).
- The second has its one-line home-file proof. It is a **disclosed Rule-10 exception, confined to
  that one lemma**. Every consumer uses only the cast form.

Evidence:
- **Seal A and seal B of `Readers.lean`** fail with exactly one error, at
  `indImpl_dec_onSpec_cast` (`logs/seal/seal-{A,B}-Readers.log`).
- **The same seal with `FixedLengthPKScheme.outLens` alone exempt** compiles
  (`seal/SealAReadersOutLensExempt.lean`, `logs/seal/seal-A-ReadersOutLensExempt.log`), so `outLens` is
  the only obstruction.
- **Probe (b)** (`EscWithReader.lean`): with the cast reader, the consumer obligation compiles
  under a seal of `outLens` and the other definitions involved.
- **Probe (c)** (`EscReaderSealed.lean`): the reader's own proof fails once `outLens` is sealed.
- **Every other file of the fill passes both seals (§7).**

**At landing:**
1. Add the two readers to `OracleSecurity.lean`.
2. Delete `Readers.lean` and its import in the owned file.
3. Re-point two names in the owned file's `castImpl_indImpl_dec`: `NMCCA2.indSpec_decRng` → `S.indSpec_decRng`, and
   `indImpl_dec_onSpec_cast` → the published cast form.

**Please confirm this route, or rule otherwise.**

## 3. The proof

### (⇒) IND-CCA2 ⇒ NM-CCA2 (brief step 1; `nmSecure_cca2_of_indSecure_cca2`)

- **Forwarding handler** (`Forward.lean`). `fwdHandler din dout …` is a `Games.InteractiveHandler`
  with empty state and `perCall = 1`, whose round forwards each inner query to the outer oracle of
  the same index and returns its answer. It is generic in the lengths, the seed, the adversary
  input and the finalization. `fwdHandler_impl` gives `impl i x s = query i x (fun y => pure (y, s))`,
  and `simulate_fwdHandler_impl` gives `simulate impl c s = c.bind (fun a => pure (a, s))`.
- **Log readers** (`Forward.lean`). `logEmit G L` concatenates `G` over the suffixes
  `pairSndD^[i] L`, `i ≤ |L|`. It is polynomial-time by `polyTimeComputable_iterateEmit`, and on an
  encoded log it is `h.flatMap g` (`logEmit_encodeLog`). With `cntRead` it counts entries; with
  `ansRead` it collects the answers.
- **The reduction** (`Decrypt.lean`). `decHandler S ℓ D` is `fwdHandler` on `acDin S`/`acDout S`,
  with:
  - seed `D.coins`;
  - the adversary run on `pk = fst z`, where `z = ⟨pk, α⟩`;
  - `finCall = ℓ`, `outLen = 1`.

  Its finalization round counts the decryptions asked so far, `j`, in the log.
  - If `j < ℓ(n)`, it asks `Dec` (index 0) on block `j` of `A`'s output, `padL ctLen (a.drop
    (j·ctLen))`, using unary multiplication, prefix dropping and `padL`.
  - Otherwise it returns `[D.output(layout 1^n answers α ω) = [true]]`
    (`polyTimeComputable_pairEq`).

  `simulate_decHandler_finish` proves its equation against *any* outer oracle whose `Dec` answers
  are deterministic and keep the state. The proof is by induction on the remaining budget along
  the log.
- **Advice** (`exists_withAdviceOn`, general form): `NUPPT.exists_comp` re-pairs
  `⟨⟨x, L⟩, β⟩ ↦ ⟨⟨x, β⟩, L⟩`, then `NUPPT.exists_withAdvice` hard-wires `β n = D.advice n`. So
  `B'.toCompOn codec n q pk (coinsCongr h n r) = B.toCompOn codec n q ⟨pk, D.advice n⟩ r`.
- **The game identity** (owned file, `accept_indGame_decRed`): `accept (Ind_b(B')) = accept (NM_b(A, D))` at every `n`.
  1. `B'`'s coins are `(ω, r)` through `φ` and `coinsCongr`; `ω` is `D`'s coins through
     `coinsEquivPoly`.
  2. Transport the run to T2's codec (`indCodec_eq_bitCodec`, `expect_simulate_castImpl_toCompOn`)
     and apply T2's equation.
  3. The handler forwards, so the run is `A` against the CCA2 oracles, then the finalization in
     the final state `st` (`simulate_bind`).
  4. `castImpl_indImpl_dec`: CCA2's `Dec` on T2's codec answers `⟦nmDecrypt sk st c⟧`, refusing the
     recorded challenge with `0` exactly as `nmDecrypt` does. This uses the requested reader.
  5. `decBlock_eq_nthCt`: the reduction's block `i` is `nthCt` `i`.
  6. `decAnswers_eq_nmOutput`: the answers are `S.nmOutput sk st a`.
  7. Transport `A`'s run back to `nmCodec` (`nmCodec_eq_bitCodec`).
- **The bound.** `B'` has budget `(q · perCall) + finCall = q·1 + ℓ`. CCA2 security gives `ε`, and
  the NM advantage equals `B'`'s IND advantage at every `n`.

### (⇐) NM-CCA2 ⇒ IND-CCA2 (brief step 2; `indSecure_cca2_of_nmSecure_cca2`)

- **The reduction** (`Encrypt.lean`). `encHandler S` is `fwdHandler` on `acDin S`/`acDout S`, with:
  - a seed of two encryption tapes, `ρ + ρ` bits (`encTape` reads them as `Enc` coins);
  - the adversary run on the reduction input `pk`;
  - `finCall = 0`, `outLen = ctLen + ctLen`.

  Its finalization reads `A`'s guess `g` (the first output bit) and outputs
  `padL ctLen (Enc(1^n, ⟨pk, b^{msgLen}⟩; tape))` for `b = g` with the first tape and `b = ¬g` with
  the second (`polyTimeComputable_eFin`). By `encHandler_finish`, the finalization is
  `pure (c₁ ‖ c₂)` and asks nothing.
- **The distinguisher** `guessDist` is uniform, without coins:
  `guessBit w = if w[0] then w[1] else ¬(last w)`.
  - `guessBit_valid`: a valid first decryption of `g^m`, `m > 0`, gives `g`.
  - `guessBit_refused`: `⊥` followed by a valid decryption of `(¬g)^m` gives `g`.
- **The guess is recovered** (`guessDist_nmOutput`), for any recorded challenge `st`.
  1. By `S.correct` (with `S.enc_length` for the padding), `c₁` decrypts to `g^m` and `c₂` to
     `(¬g)^m`.
  2. So `c₁ ≠ c₂` (bit 0 differs, `m > 0`), and at most one is the challenge.
  3. If `st ≠ some c₁`, use `guessBit_valid`; otherwise `st ≠ some c₂` and use `guessBit_refused`.

  The output's two blocks are `c₁` and `c₂` (`ofFn_nthCt`). `flatten_ofFn_two`, derived from
  `OneWay.flatten_ofFn_two`, handles `Fin ((const 2).eval n)` without reading `PolyExpr.eval`.
- **The game identity** (`accept_nmGame_encRed`, for `msgLen(n) > 0`):
  `accept (NM_b(B, 2, guessDist)) = accept (Ind_b(A))`. The structure is that of (⇒):
  1. coins `(ω, r)` through `φ`;
  2. transport and T2's equation;
  3. forwarding, `simulate_bind` and the finalization;
  4. pointwise `guessDist_nmOutput`;
  5. transport back.

  The result does not depend on `ω` or on the distinguisher's coins (`expect_const`).
- **`msgLen(n) = 0`** (`indImpl_eq_of_msgLen_eq_zero`): both halves of a challenge are `[]`, so
  `indImpl .cca2 false = indImpl .cca2 true` query by query (published `_onSpec` readers only), the
  two games are equal, and the advantage is `0 ≤ ε(n)`.
- **The bound.** `B` has budget `q·1 + 0` and `ℓ = 2`. Non-malleability gives `ε`, and the IND
  advantage is at most the NM advantage at every `n`.

### Assembly (brief step 3)

The target is the pair of the two directions. The budgets are the polynomials
`(q.mul perCall).add finCall` of each direction, read through `PolyExpr.eval_add`/`eval_mul` and
the handlers' `_perCall`/`_finCall` readers.

### Edge cases

- **Budget 0:** every lemma is for an arbitrary budget, by induction on computations or on the
  remaining budget.
- **`ℓ = 0`:** (⇒)'s finalization induction starts at `j = ℓ` and returns `D`'s verdict on `[]`.
- **`msgLen(n) = 0`:**
  - (⇐) is handled separately (above);
  - (⇒) needs no case split, since `decAnswer` at width 1 is uniform.
- **No challenge asked (`st = none`):**
  - in (⇒), `Dec` answers everything, and so does `nmDecrypt` (`none ≠ some c`);
  - in (⇐), both ciphertexts decrypt validly.
- **Repeated challenges:** the state records the first. In (⇒) both sides read the same `st`;
  (⇐) is uniform in `st`.
- **`A` outputs the challenge itself, or a malformed or invalid ciphertext (⇒):** both sides answer
  `nmDecrypt sk st c`, whatever `c` is: `⊥ = 0` on a copy, `decAnswer none = 0` on an invalid one,
  and blocks are read by position whatever their content.
- **The codec's timeout output:**
  - in (⇒), `A`'s timeout output is part of `toCompOn` on both sides and is transported with it;
    the reduction's own budget is never short, by T2's equation;
  - in (⇐), `A`'s timeout output `zeroBits 1` is the guess `g = false`, which the reduction
    encrypts and the distinguisher recovers like any other.

## 4. Changed files and the sketch edit

| File | Change |
|---|---|
| `NonMalleability/Indistinguishability.lean` (owned, 660 lines) | 5 imports added (the 4 helpers, `AdaptiveCPA.Games`); a `## Contents` list; the status line in `## Main results`; a `section Proof` with both directions; the target's sketch rewritten to describe the delivered proof; the target's body. Unchanged: the statement, every other declaration, the statement prose and the global simp attributes. |
| `…/Indistinguishability/Readers.lean` (new, 71 lines) | the two requested readers (escalation, §2) |
| `…/Indistinguishability/Forward.lean` (new, 349 lines) | forwarding handler; finalization-input readers; `logEmit` |
| `…/Indistinguishability/Decrypt.lean` (new, 350 lines) | (⇒): `decHandler`, its finalization equation, `exists_withAdviceOn` |
| `…/Indistinguishability/Encrypt.lean` (new, 332 lines) | (⇐): `encHandler`, `encTape`, `encCt`, `guessDist`, `indImpl_eq_of_msgLen_eq_zero` |

No other file is touched; `Simulation.lean` is unchanged. The owned file imports its four children
precisely and lists them under `## Contents`. Every file is below 1000 lines and no line exceeds
100 characters.

**The sketch edit.** The target's sketch keeps the source's two steps and the closing paragraph.
- Step (⇒) now also says that the adversary forwards every query, and that `Dec` decrypts every
  other ciphertext as `NM` does. It names the handler (`NMCCA2.decHandler`) and the advice route
  (`NMCCA2.exists_withAdviceOn` from `exists_withAdvice`/`exists_comp`).
- Step (⇐) names `NMCCA2.encHandler` and `NMCCA2.guessDist` and states that at `msgLen(n) = 0` the
  CCA2 games coincide.
- Both steps cite their theorems.

## 5. New declarations

Every public declaration has a docstring with its formula, and the nontrivial ones have a proof
sketch. No `@[simp]` attribute was added. `simps` readers carry `isSimp := false`.

- **Readers:** `NMCCA2.indSpec_decRng`, `NMCCA2.indImpl_dec_onSpec_cast`.
- **Forward:**
  - `fwdHandler`, with `simps` readers `_stateLen`, `_seedLen`, `_perCall`, `_init`, `_advIn`,
    `_outLen`, `_finCall` and `_finRun`;
  - `fwdHandler_impl`, `simulate_fwdHandler_impl`;
  - `finU`/`finZ`/`finW`/`finA`/`finL` with their `_eq` lemmas, `fields_finInput`,
    `polyTimeComputable_finFields`;
  - `logEmit` with `_eq`, `polyTimeComputable_logEmit`, `logEmit_encodeLog`;
  - private: `rState`, `rIdx`, `rQuery`, `rLog`, `rAns`, `fields_input`, `fwdRun`,
    `polyTimeComputable_fwdRun`, `length_iterate_pairSndD_le`, `iterate_pairSndD_encodeLog`,
    `flatMap_range_drop`, `length_le_length_encodeLog`.
- **Decrypt:**
  - `cntRead` and `ansRead`, each with `_eq` and `polyTimeComputable_`;
  - `length_logEmit_cntRead`, `logEmit_ansRead`;
  - `decHandler` with `_seedLen`, `_perCall`, `_finCall`, `_outLen` and `_advInput`;
  - `simulate_decHandler_impl`, `decBlock` with `_eq`, `simulate_decHandler_finish`,
    `exists_withAdviceOn`;
  - private: `dCnt`, `dCt`, `dIn`, `dFin`, `polyTimeComputable_dFin`, `polyTimeComputable_decAdvIn`.
- **Encrypt:**
  - `encHandler` with `_seedLen`, `_perCall`, `_finCall`, `_outLen` and `_advInput`;
  - `simulate_encHandler_impl`;
  - `encTape` with `_eq`, `ofFn_encTape`; `encCt` with `_eq`; `encHandler_finish`;
  - `guessBit` with `_eq`, `guessDist`, `guessDist_distinguisherL`, `guessBit_valid`,
    `guessBit_refused`;
  - `indImpl_eq_of_msgLen_eq_zero`;
  - private: `eBit`, `eMsg`, `eTape`, `eCt`, `eFin`, `polyTimeComputable_eFin`,
    `polyTimeComputable_encAdvIn`, `guessFun`, `polyTimeComputable_guessFun`.
- **Owned file:**
  - `nmCodec_eq_bitCodec`, `ofFn_nthCt`;
  - `nmSecure_cca2_of_indSecure_cca2`, `indSecure_cca2_of_nmSecure_cca2`;
  - private: `castImpl_indImpl_dec`, `decBlock_eq_nthCt`, `decAnswers_eq_nmOutput`,
    `accept_indGame_decRed`, `flatten_ofFn_two`, `guessDist_nmOutput`,
    `accept_nmGame_encRed`.

## 6. Promotion and reader requests, duplication

- **Reader request (blocking for Rule 10):** `FixedLengthPKScheme.indSpec_decRng` and the cast form
  of `indImpl_dec_onSpec`, both for `PublicKey/OracleSecurity.lean` (§2).
- **Promotion requests (generic):**
  - `NMCCA2.fwdHandler` with `fwdHandler_impl` and `simulate_fwdHandler_impl` →
    `Games/Efficiency.lean`. This is the forwarding interactive handler; `AdaptiveCPA`'s
    `acHandler_impl_forward` is one branch of it.
  - `finU`…`finL` and `fields_finInput` → `Games/Efficiency.lean`, beside
    `InteractiveHandler.finInput`.
  - `logEmit`, `polyTimeComputable_logEmit` and `logEmit_encodeLog` → `Games/Efficiency` or
    `Games/Machines.lean`. They are readers of an encoded query log.
  - `cntRead`, `ansRead`, `length_logEmit_cntRead` and `logEmit_ansRead` → `Games/BitCodec.lean`.
  - `exists_withAdviceOn` (hard-wiring a second input component, for every codec and budget) →
    `Games/Efficiency.lean`, beside `exists_toCompOn_of_toComp`, or `Randomized/Closure.lean`.
  - `indImpl_eq_of_msgLen_eq_zero` → `PublicKey/OracleSecurity.lean`.
- **DL-30–34 overlaps:**
  - **The round-input readers.** `Forward.lean` re-derives private readers (`rState`, `rIdx`,
    `rQuery`, `rLog`, `rAns`, `fields_input`) from `InteractiveHandler.input_eq`, in the general
    form; they play the role of `AdaptiveCPA`'s private `rS`, `rI`, `rX`, `rL`, `rFwd`.
  - **`impl_of_ret`.** `fwdHandler_impl` does its own two-round `buildComp` argument (query, then
    return); it is not a copy of `impl_of_ret`.
  - **`ofFn_padFin_eq_padL`.** `Decrypt.lean` rewrites `ofFn_padFin_eq_take` and
    `EnsembleLemmas.padL_eq` inline (no lemma).

  Nothing was copied from `AdaptiveCPA/`, `BitwiseCPA/` or `OracleFromPRF/`.
- **Public lemmas imported, not copied:**
  - `AdaptiveCPA.castImpl`, `castImpl_eq`, `expect_simulate_castImpl_toCompOn`,
    `indCodec_eq_bitCodec`, `acDin`/`acDout` with `_zero`, `acDin_eval`/`acDout_eval`, `ofFn_cast`,
    `headD_ofFn_one`;
  - `ChallengeSim.expect_sample_equiv`/`_prod`/`_comm`;
  - `OneWay.flatten_ofFn_two`, `OneWay.polyTimeComputable_unaryMulPair`;
  - `GGMRed.ofFn_padFin_of_length`, `ofFn_padFin_eq_take`;
  - `EnsembleLemmas.padL_eq`/`length_padL`/`polyTimeComputable_padL`/`polyTimeComputable_zeros`;
  - `Complexity.polyTimeComputable_iterateEmit`, `polyTimeComputable_pairEq`.

  The maintainer re-points any of these that the parallel `dl-consolidation` moves.

## 7. Checks

- **Preflight** (`logs/preflight.log`, before any cache or Lean work):
  - `nproc` 4;
  - cgroup v1 with no effective limit (`memory.limit_in_bytes` 9223372036854771712), so the
    headroom is `MemAvailable` = 16,021,256 kB = 15.27 GiB (floor 4 GiB: PASS). Memory in use
    (`usage − total_cache + total_shmem`) was 178,421,760 B;
  - the clone (`/workspace/fill`, a worktree of the session's clone), the payload and `/tmp` are on
    ext4 `/dev/vda`, with 25,602,281,472 B free (floor 12 GiB: PASS). No tmpfs was used.
- **Toolchain:** Lean 4.25.0 (`cdd38ac5115b…`) installed by `elan` after the preflight. Disk
  re-check before the cache: 23.0 GB free (floor 8 GiB: PASS; `logs/cache-store.log`).
- **Cache:**
  - The archive store `~/.cache/mathlib` was absent before the fetch.
  - The narrowed `lake exe cache get` over the 97 roots (`logs/mathlib-roots.txt`, identical to the
    pack's `roots.txt`) downloaded 2,370 files, decompressed 2,370 and exited 0
    (`logs/cache-get.log`).
  - Package pins: 11 present match, 0 mismatch; `doc-gen4`, `UnicodeBasic`, `BibtexQuery` and
    `MD4Lean` are ABSENT, and the order imports none of them (`logs/packages-check.log`).
  - No zero-size `.olean`; the root probe passed (`logs/cache-probe.log`).
  - The helpers import no Mathlib module directly, so the roots are unchanged.
- **Bootstrap** (addendum item 5; `logs/bootstrap-*.tsv`, `logs/bootstrap/`):
  - first the owned file's 151-module upstream closure, in `order.txt` order (all pass);
  - then the owned file at the base and `AdaptiveCPA/Hybrid`, `/Handler`, `AdaptiveSecurity`,
    `AdaptiveCPA/Games` (all pass);
  - the remaining modules were built by the sweep.

  The pack's order is `evidence/bootstrap-order.txt`.
- **Order:** `evidence/order.txt` is the issued 249-module order with the four helpers inserted
  directly before `NonMalleability/Indistinguishability` (253 modules). Every helper's imports
  precede it. Its new dependency `AdaptiveCPA/Games` and that file's closure already precede the
  target in the issued order (positions 140–161 against 173).
- **Sweep** (final head, fresh olean tree `.lake/sweep-oleans`, one `lean_check_tree.sh` call per
  module): **253 passed, 0 failed**, 888.8 s of Lean time, peak child RSS 2,941 MiB. The sweep started at `62644213d`. The last commit (`9bd89494b`, owned file only) landed before the sweep reached the owned file (module 177), so every module was checked at the final head's content (`logs/sweep.tsv`, `logs/sweep/`).
- **Admissions** (`logs/sorry-census.txt`): **26** `sorry` declarations against 27 in `base-sorries.txt`. Removed: exactly `NonMalleability/Indistinguishability: indSecure_cca2_iff_nmSecure_cca2`. Added: none.
- **Axioms:** §1.
- **Rule 10: whole-file seals over the full TCSlib import closure.**
  - **Census** (`seal/Scan*.lean`, `logs/seal/scan-*.log`). For each file, a module with exactly
    the file's imports lists every seal candidate of its full TCSlib import closure: every TCSlib
    definition that is neither reducible nor already irreducible, not an instance, not a structure
    projection or auxiliary recursor, and not private or internal. Generated matchers are
    included. The helper modules are foreign to each other and to the owned file, since the census
    sees only the file's imports.
  - **Seals** (`seal/Seal{A,B}*.lean`, `logs/seal/seal-*.log`). Each is a verbatim copy of the file
    with `attribute [local irreducible]` on all its candidates, after the first `open` of its first
    namespace, so the whole file is sealed. Seal A exempts `PolyExpr.eval` as notation; seal B
    seals it too.

    | File | Candidates (A / B) | Seal A | Seal B |
    |---|---|---|---|
    | owned file | 1277 / 1278 | pass | pass |
    | `Readers` | 1232 / 1233 | **fails**: 1 error, at `indImpl_dec_onSpec_cast` (the requested reader) | **fails**: 1 error, at `indImpl_dec_onSpec_cast` (the requested reader) |
    | `Forward` | 1140 / 1141 | pass | pass |
    | `Decrypt` | 1249 / 1250 | pass | pass |
    | `Encrypt` | 1249 / 1250 | pass | pass |
    | base owned file (control) | 1232 / 1233 | pass | pass |
  - **Base control:** the base owned file under the same seals compiles (A and B).
  - **Paired controls** (`seal/Controls{Unsealed,SealedA,SealedB}.lean`, `logs/seal/Controls*.log`).
    There are 13 readings through definition bodies: `inLens`, `outLens`, `PolyExpr.eval`, `seedIn`,
    `padFin`, `acDin`, the helpers' `finU`, `fwdHandler`, `cntRead`, `decHandler`, `encHandler` and
    `guessBit`, and the owned file's `nmCodec`.
    - Unsealed: all 13 pass.
    - Seal A: 12/13 fail; only the `PolyExpr.eval` control passes, as designed.
    - Seal B: 13/13 fail.
  - **Findings and fixes.** The first seal run, at `60b4ad5bf`, failed in two files besides the
    expected `Readers`. Commit `62644213d` fixed them:
    - `Forward`'s empty-log bound read `MachineCodec.encodeLog []` (now `Nat.zero_le`);
    - `Decrypt`'s `ansRead [] = []` read `pairFstD []`/`pairSndD []` (now `pairFstD_nil` and
      `pairSndD_of_pairDecode_eq_none`);
    - `Decrypt`'s verdict round matched `decodeBitMove_ret` through `padFin` (now on the left only).

    Checkpoints 1 and 2 carry the unfixed versions.
- **Explicit-unfold scan** (`seal/RwIds*.lean`, `logs/rwids.log`, `logs/rwids-classified.tsv`,
  `logs/rwids-summary.log`). The scan collects every identifier that the added lines pass to `rw`,
  `rwa`, `erw`, `simp`, `simp only`, `simp_rw`, `simpa`, `dsimp`, `unfold` or `delta`. Each is resolved
  in its file's namespace with the file's `open`s; `S.foo` is read as `FixedLengthPKScheme.foo`.
  317 entries over the five files. **No foreign definition is passed.** The definitions passed are each file's own:
  - `Forward`: `finU`…`finZ` and the private `rState`…`rAns`, `fwdRun`;
  - `Decrypt`: `decHandler` and the private `dCnt`, `dCt`, `dIn`, `dFin`;
  - `Encrypt`: `encHandler` and the private `eBit`, `eMsg`, `eTape`, `eCt`, `eFin`, `guessFun`.
- **Lint** (`logs/lint-final.log`, `logs/lint-base.log`):
  `python3 -I scripts/campaign_style_lint.py TCSlib/Cryptography/Encryption/PublicKey --check8b`
  gives **0 FAIL, 6 WARN over 30 files**. The six warnings are identical to the base's (0 FAIL,
  6 WARN over 26 files), all on untouched files. The five fill files have no warning.
  `git diff --check` is clean.
- **Patch replay** (`logs/patch-replay.log`): `git am` of `patches/` on the base in a clean worktree
  reproduces all five files of `src/` byte for byte; the tree hash equals the proof branch's.
- **Process discipline:**
  - One Lean process at a time, every module check through `scripts/lean_check_tree.sh`, wrapped by
    `tools/chk.py` (UTC start and end, wall time, max child RSS).
  - No `lake build`, no unfiltered cache get, no timeouts.
  - A first final sweep was stopped at module 98 to fix line widths before the seals
    (`logs/dev/sweep-aborted.tsv`); the reported sweep ran once at the final head.
  - The proof branch stayed local.
  - AGENTS.md says to use the VS Code LeanInfoView instead of running `lean`. The brief and the
    dispatch require `scripts/lean_check_tree.sh`, which is what I used.

## 8. For the maintainer

1. **E-READER** (§2) needs a ruling and the two readers in `OracleSecurity.lean`. After that,
   `Readers.lean` goes away and every file of the fill passes the seal.
2. **Stale module title.** The owned file's module docstring is still titled
   "Non-malleable encryption (statement phase)". The brief allows changing only the target's
   sketch and status line, and I updated the status line in `## Main results`.
3. **Order.** `evidence/order.txt` (253 modules) is the issued order plus the four helpers.
4. The owned file now imports `AdaptiveCPA.Games` (with `Hybrid`, `Handler` and `AdaptiveSecurity`)
   for the public transport lemmas. `Simulation.lean` sees them transitively.

## Payload

- `REPORT.md` and `patches/` (the whole `format-patch` series from the base);
- `src/`, the five files at their repository paths;
- `evidence/`:
  - `inputs/`: the pack, the exchange README and `policy.md`;
  - `logs/`: preflight, cache store, cache get, packages, probe, bootstrap, sweep, admissions,
    axioms, escalation probes, seal censuses, seals, controls, unfold scan, lint, patch replay
    and `dev/`;
  - `seal/`, `probes/`, `tools/`;
  - `order.txt`, `bootstrap-order.txt`;
- `SHA256SUMS` over the payload.
