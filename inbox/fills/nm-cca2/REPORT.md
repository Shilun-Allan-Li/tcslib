# Fill `nm-cca2` — checkpoint 1: (⇒) proved; escalation E-READER (missing reader)

**Worker:** Claude (external). **Issue base:** `b96ab3ccc1915497ea3138df499eec00b6581db0` on
`cryptography/pass-shelat-ch2-4` (the merge of #293). **Local proof branch:** `fill/nm-cca2`, head
`aae1d6541`, never pushed; the whole series from the base is in `patches/`. **Pack:** read at
exchange `3f6d6783a1e4527e5287c63a9f1a0075fb6d0369`; `SHA256SUMS` 7/7 OK; all 249 entries of
`SOURCE-SHA256SUMS` match the base.

## Status

- **(⇒) IND-CCA2 ⇒ NM-CCA2 is proved:** `FixedLengthPKScheme.nmSecure_cca2_of_indSecure_cca2` in the
  owned file, axioms `[propext, Classical.choice, Quot.sound]`.
- **Escalation E-READER.** One reader of `PublicKey/OracleSecurity.lean` is missing (below). The
  proof isolates it in one helper module (`Indistinguishability/Readers.lean`) in the requested
  form. That module's second lemma is the only place in the fill that reads a foreign
  definition (`outLens`) definitionally, so the final seal will fail there and nowhere else
  until the reader lands in its home file.
- The target `indSecure_cca2_iff_nmSecure_cca2` is still admitted; (⇐) is next (checkpoint 2).

## Escalation E-READER: the decryption answer has no cast reader

**Obligation.** In (⇒) the CCA2 adversary asks its decryption oracle for each of `A`'s ciphertexts
and must show that the answers, read as strings, are `NM_b`'s decryptions. On T2's codec the
oracle's answer to a query `x` in state `st` is (`castImpl_eq`, then `indImpl_dec_onSpec`,
`decOpen_cca2`):

```
padFin ((acDout S 0).eval n) (List.ofFn p.1),   p.1 = FixedLengthScheme.decAnswer X   (valid branch)
```

where `X = decodeFin _ (S.dec ⟨sk, c⟩)`. `indImpl_dec_onSpec` states this `decAnswer X`
(`: Fin (S.msgLen.eval n + 1) → Bool`) at the oracle's answer type `(S.indSpec n).rng 0 =
Fin (S.outLens n 0) → Bool` **without a cast**: the types agree only by unfolding `outLens`. So
`List.ofFn p.1` is `List.ofFn` at width `S.outLens n 0`. Relating it to
`⟦S.nmDecrypt sk st c⟧` (width `msgLen + 1`) leaves, after every published reader, the goal

```
HEq ((decAnswer X, st).1 : Fin (S.outLens n 0) → Bool) (decAnswer X : Fin (S.msgLen.eval n + 1) → Bool)
```

With `outLens` sealed this cannot be closed. `HEq.rfl`, `cast_eq` and rewriting under `Prod.mk`
(`decAnswer_some`/`_none`, `outLens_zero`) all need the two widths to be definitionally equal.
`evidence/probes/EscNoReader.lean` (log `logs/escalation-EscNoReader.log`) shows the state.

**Reader needed** (the public-key analogue of what not-cca2 r2 added to `PrivateKey/OracleSecurity.lean`):

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

The second either replaces the current statement of `indImpl_dec_onSpec` (its only consumer at the
base is `AdaptiveCPA`, which uses the refused branch under CPA and is unaffected) or is added beside
it under a new name. Its proof unfolds `outLens`, which is legitimate only in `OracleSecurity.lean`.

**What the fill does meanwhile.** `Indistinguishability/Readers.lean` states both readers exactly as
above, under `NMCCA2.indSpec_decRng` and `NMCCA2.indImpl_dec_onSpec_cast`. The first is proved from
published readers. The second has the one-line proof it would have in its home file, so it reads
`outLens` definitionally. That is a **disclosed Rule-10 exception, confined to that one lemma**. Every
consumer uses only the cast form.
- `EscWithReader.lean` (exit 0): with the cast reader, the consumer obligation (my
  `castImpl_indImpl_dec`) compiles with `outLens`, `inLens`, `indImpl`, `nmDecrypt`, `decAnswer`,
  `decOpen`, `castImpl`, `padFin`, `PolyExpr.eval`, `acDin` and `acDout` all sealed.
- `EscReaderSealed.lean` (exit 1): the reader's own proof fails as soon as `outLens` is sealed.

At landing the maintainer adds the reader to `OracleSecurity.lean`, deletes `Readers.lean` and
re-points two names (`NMCCA2.indSpec_decRng` → `S.indSpec_decRng`, `indImpl_dec_onSpec_cast` → the cast
form). **Please confirm this route, or rule otherwise.**

## (⇒) The proof (brief step 1)

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
  - If `j < ℓ(n)`, it asks `Dec` (index 0) on block `j` of `A`'s output. The block is
    `padL ctLen (a.drop (j·ctLen))`, using unary multiplication, prefix dropping and `padL`.
  - Otherwise it returns `[D.output(layout 1^n answers α ω) = [true]]`
    (`polyTimeComputable_pairEq`).

  `simulate_decHandler_finish` proves its equation against *any* outer oracle whose `Dec` answers
  are deterministic and keep the state. The proof is by induction on the remaining budget along
  the log.
- **Advice** (`exists_withAdviceOn`, general form): `NUPPT.exists_comp` re-pairs
  `⟨⟨x, L⟩, β⟩ ↦ ⟨⟨x, β⟩, L⟩`, then `NUPPT.exists_withAdvice` hard-wires `β n = D.advice n`. So
  `B'.toCompOn codec n q pk (coinsCongr h n r) = B.toCompOn codec n q ⟨pk, D.advice n⟩ r`.
- **The game identity** (owned file, `accept_indGame_decRed`): `accept (Ind_b(B')) = accept (NM_b(A, D))` at every `n`.
  1. `B'`'s coins become `(ω, r)` through `φ` and `coinsCongr`; `ω` is `D`'s coins through
     `coinsEquivPoly`.
  2. Transport the run to T2's codec (`indCodec_eq_bitCodec`, `expect_simulate_castImpl_toCompOn`)
     and apply T2's equation.
  3. The handler forwards, so the run is `A` against the CCA2 oracles, then the finalization in
     the final state `st` (`simulate_bind`).
  4. `castImpl_indImpl_dec`: CCA2's `Dec` on T2's codec answers `⟦nmDecrypt sk st c⟧`, refusing the
     recorded challenge with `0` exactly as `nmDecrypt` does.
  5. `decBlock_eq_nthCt`: the reduction's block `i` is `nthCt` `i`.
  6. `decAnswers_eq_nmOutput`: the answers are `S.nmOutput sk st a`.
  7. Transport `A`'s run back to `nmCodec` (`nmCodec_eq_bitCodec`).
- **The bound.** `B'` has budget `(q · perCall) + finCall = q·1 + ℓ`. CCA2 security gives `ε`, and
  the NM advantage equals `B'`'s IND advantage at every `n`.

**Edge cases (⇒):**
- **Budget 0:** every lemma is for an arbitrary budget.
- **`ℓ = 0`:** the finalization's induction starts at `j = ℓ` and returns `D`'s verdict on `[]`.
- **No challenge asked (`st = none`):** `Dec` answers everything, and so does `nmDecrypt`
  (`if none = some c`).
- **Repeated challenges:** the state records the first, and both sides read the same `st`.
- **`A` outputting the challenge, or a malformed or invalid ciphertext:** both sides answer
  `nmDecrypt sk st c`, whatever `c` is (`⊥ = 0` on a copy, `decAnswer none = 0` on an invalid one).
- **Codec timeout:** `A`'s timeout output is part of `toCompOn` on both sides and is transported
  with it. The reduction's own budget is never short, by T2's equation.

## Changed files

| File | Change |
|---|---|
| `NonMalleability/Indistinguishability.lean` (owned) | 4 imports added (the 3 helpers, `AdaptiveCPA.Games`); `## Contents` list; status line; a `section Proof` with the (⇒) declarations. Statement, other declarations, statement prose and simp attributes unchanged; target still `sorry`. |
| `…/Indistinguishability/Readers.lean` (new, 71 lines) | the two requested readers (escalation) |
| `…/Indistinguishability/Forward.lean` (new, 349 lines) | forwarding handler; finalization-input readers; `logEmit` |
| `…/Indistinguishability/Decrypt.lean` (new, 347 lines) | `decHandler`, its finalization equation, `exists_withAdviceOn` |

## New declarations (checkpoint 1)

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
- **Owned file:**
  - `nmCodec_eq_bitCodec`, `ofFn_nthCt`, `nmSecure_cca2_of_indSecure_cca2`;
  - private: `castImpl_indImpl_dec`, `decBlock_eq_nthCt`, `decAnswers_eq_nmOutput`,
    `accept_indGame_decRed`.

**DL-30–34 overlap: the round-input readers.** `Forward.lean` re-derives private round-input
readers (`rState`, `rIdx`, `rQuery`, `rLog`, `rAns`, `fields_input`) from `InteractiveHandler.input_eq`. They
play the role of `AdaptiveCPA`'s private `rS`, `rI`, `rX`, `rL`, `rFwd`. Nothing was copied.
**Public imports used, not copied:** `AdaptiveCPA.castImpl`, `expect_simulate_castImpl_toCompOn`,
`indCodec_eq_bitCodec`, `acDin`/`acDout` with `_zero`, `acDin_eval`/`acDout_eval`, `ofFn_cast`,
`headD_ofFn_one`, and `ChallengeSim.expect_sample_*`.

## Environment and checks so far

- **Preflight** (`logs/preflight.log`, before any cache or Lean work):
  - `nproc` 4;
  - cgroup v1 with no effective limit (`memory.limit_in_bytes` 9223372036854771712), so the
    headroom is `MemAvailable` = 16,021,256 kB = 15.27 GiB (floor 4 GiB: PASS). Memory in use
    (`usage − total_cache + total_shmem`) was 178,421,760 B;
  - the clone (`/workspace/fill`, a worktree of the session's clone), the payload and `/tmp` are on
    ext4 `/dev/vda`, with 25,602,281,472 B free (floor 12 GiB: PASS). No tmpfs was used.
- **Toolchain:** Lean 4.25.0 (`cdd38ac5115b…`) installed by `elan` (`--default-toolchain none`,
  then the pinned toolchain) after the preflight. Disk re-check before the cache: 23.0 GB free
  (floor 8 GiB: PASS; `logs/cache-store.log`).
- **Cache:**
  - The archive store `~/.cache/mathlib` was absent before the fetch.
  - The narrowed `lake exe cache get` over the 97 roots (`logs/mathlib-roots.txt`, identical to the
    pack's `roots.txt`) downloaded 2,370 files, decompressed 2,370 and exited 0
    (`logs/cache-get.log`).
  - Package pins: 11 present match, 0 mismatch; `doc-gen4`, `UnicodeBasic`, `BibtexQuery` and
    `MD4Lean` are ABSENT, and the order imports none of them (`logs/packages-check.log`).
  - No zero-size `.olean`; the root probe passed (`logs/cache-probe.log`).
- **Bootstrap** (item 5's partial order, one module per `scripts/lean_check_tree.sh` call):
  - the owned file's upstream closure in `order.txt` order (151 modules, all pass,
    `logs/bootstrap-upstream.tsv`);
  - then the owned file at the base and `AdaptiveCPA/Hybrid`, `AdaptiveCPA/Handler`,
    `AdaptiveSecurity`, `AdaptiveCPA/Games` (all pass, `logs/bootstrap-extra1.tsv`). These four
    already precede the target in `order.txt` (positions 140–161 against 173), so the helpers go
    directly before `NonMalleability/Indistinguishability`.

  Peak RSS was 2,740 MiB. The remaining modules of the order are built before the final sweep.
- **Development checks:** each new module, then the owned file, through `scripts/lean_check_tree.sh`
  (`logs/dev/`); the owned file compiles with exactly one `sorry` (the target).
- **AGENTS.md** says to use the VS Code LeanInfoView instead of running `lean`. The brief and the
  dispatch instead require `scripts/lean_check_tree.sh`, one module at a time, which is what I
  did. No `lake build` was run.

## Next

(⇐), checkpoint 2:
- an NM adversary that forwards `A`'s queries and outputs `Enc_pk(g^L)`, `Enc_pk((¬g)^L)` under its own seed;
- a uniform distinguisher;
- the `msgLen(n) = 0` case.

Then the assembly, the full sweep, axioms, seals, unfold scan and lint.
