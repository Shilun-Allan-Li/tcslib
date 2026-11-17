# Sub-agent `probe` (Deliverable 3): notes

Worktree `/home/user/fill/wt-probe`, local branch `probe/bb1-sim-readers` at
`c90273fad3511ada7c9c1a53e1abdd8478237cee` (T4's head; `clash/head.txt`). Olean tree P
`/home/user/fill/treeP` (bootstrapped by the lead: `evidence/build/bootstrap-P/`, 189 modules,
rc 0, 0 errors, `done` 2026-11-16T23:04:34Z). Every Lean run went through the lead's runners, which
take `flock /home/user/fill/tcslib/.lean.lock` per module. No `lake`, no commit, nothing under
`TCSlib/` edited; tree S untouched.

## Tools (`tools/`)

- `devseal.py`: T4's development seal, copied; its header records the changes (one harness line
  split for widths, 2026-11-17).
- `scratch.sh` (one `runner_full.py` check of a scratch module), `devcheck.sh` (devseal and check
  of the consumer during development), `final_checks.sh` (the recorded checks, in order).

## Log (UTC; the `start` fields of each `results.jsonl`)

- 2026-11-16 22:57. Read the brief (Deliverable 3, Multi-agent, Checks, Sources), design §1.4,
  §3.1–3.3, T4's `REPORT.md` and issued brief, `Defs.lean`, `BonehBoyen.lean`, `Oracles.lean`.
  Copied `devseal.py`. Waited for the bootstrap of tree P.
- 23:04 `native-readers-v1-wholefn/`: readers probe v1 (only `IBEScheme.sidImpl_eq_oracleImpl`;
  source copy `BB1SimReaders.v1.lean.txt`): rc 0, 0 errors.
- 23:04 `scratch/explore1/` (`PlProbe/Scratch/Explore1.lean`): `#check` of the `simps` lemmas of
  `bb1Scheme`: binders typed at `Σ …`, identities at `Fin (ℓ.eval κ) → Bool`, messages at
  `Fin (G.wT.eval κ) → Bool`.
- 23:05 `scratch/explore2A/` (`Explore2.lean`, devseal A): `⟨d, P⟩ : PP κ` does not elaborate (T4's
  finding, reproduced); P-1 through `sidImpl_eq_oracleImpl` fails at `oracleImpl_zero_onSpec`; the
  setup map cannot be extracted from `bb1Scheme_setup` (type mismatch `Σ …` against `PP κ`).
- 23:07 `scratch/explore3A/` (`Explore3.lean`, A): after `rw [bb1Scheme_setup]` nothing composes
  (`bind_assoc` cannot instantiate: the right side is typed at `Σ … × Σ …`); the explicit
  instance of `oracleImpl_zero_onSpec` at `init := S.sidImpl b κ pp msk 0` is a type mismatch.
- 23:09–23:10 `scratch/owner1/` (`Owner1.lean`, native) and `scratch/explore4A/`
  (`Explore4.lean`, A): a binder `pp : (bb1Scheme G ℓ).PP κ` cannot be instantiated with a
  `Σ`-typed `⟨d, P⟩` (E9); a setup reader typed at `PP κ × MSK κ` composes (E10); E12 named a
  constant wrongly (no information).
- 23:15–23:20 `alternatives/whole-fn/`: `AltWhole.lean` (the whole-function and pointwise
  `sidImpl = oracleImpl …` readers, owner side, native rc 0) and `AltWholeUse.lean` (P-1 `Init`
  through each): native rc 0; devseal A rc 1, 3 errors (the `oracleImpl_zero_onSpec` rewrite finds
  no instance after either reader; the explicit instance is an application type mismatch).
  **The Q7 reader fails.**
- 23:20–23:24 readers v2/v3 (three `sidImpl_{zero,one,two}_onSpec`, the Q7(B) form); `dev-v1-A`
  (12 errors: the query cast was elaborated `dom → dom`; fixed by an ascription) and `dev-v2-A`
  (9 errors). Copies in `alternatives/q7b-three-onSpec/`. **Q7(B)'s three readers fail** for the
  four `⊥` cases (the typed readers answer `zeroBits (S.outLens κ i)`, which the answer cast from
  `Fin (…) → Bool` cannot take under the seals) and for `KeyGen` with `ID ≠ ID*` and the fresh
  `Challenge` (the typed readers' right sides are binds typed at `(Fin (…) → Bool) × σ` inside
  a bind typed at `rng i × σ`: `bind_assoc` cannot instantiate).
- 23:24–23:29 `scratch/explore5`, `explore5b`: `pp.explicit` prints (native). The first version
  printed `sidImpl_init_none` and `sidImpl_zero_onSpec` (SHA-256 `2217c777…`, source not kept);
  the second is `Explore5.lean`.
- 23:32 readers v4: six `Defs` readers (`sidImpl_zero_onSpec`, `sidImpl_two_onSpec`,
  `sidImpl_one_onQuery`, `sidImpl_two_onQuery`, `sidImpl_keyGen_ne_onSpec`,
  `sidImpl_challenge_fresh_onSpec`) and `BonehBoyen` readers `bb1Scheme_setup_eq`,
  `bb1Scheme_keyGen_mk`, `bb1Scheme_enc_mk`. `dev-v3-A`: all nine P-1 cases pass; 3 errors in
  `setup_out` (goal order; the setup reader's pair not yet typed).
- 23:33 readers v5 (the setup reader's pair typed at `PP κ × MSK κ`): `dev-v4-A`, `dev-v5-A`: the
  `_mk` forms of `KeyGen`/`Encrypt` leave `.pure ⟨d, k⟩` (a `Σ`-typed value at `SK κ`), on which
  `pure_bind` cannot instantiate. Copies in `alternatives/bb1-mk-readers/`. Replaced by the bind
  forms `bb1Scheme_keyGen_bind`, `bb1Scheme_enc_bind`.
- 23:35–23:40 readers v6; `dev-v6-A`, `dev-v7-A`, `dev-v8-A`, `scratch/stepmdev1`, `stepmdev2` (a
  scratch copy of the consumer with `congr`, `trace_state` and `sorry` to print the goal; its source
  was not kept: it is superseded by `alternatives/encCT-congrArg/`): the `congrArg` comparison of
  the real ciphertext with `bb1SimCt` fails, because `bb1SimCt_eq` reads `decodeT _ m` in
  `BilinearGroup _ ((bb1Scheme G ℓ).msgLen.eval κ)` and `Encrypt` in `BilinearGroup _ (G.wT.eval κ)`.
- 23:41 readers v7 (`bb1Scheme_enc_bind` reads the message as `padFin _ ⟦m⟧`, as `ofFn_bb1SimCt`
  does; new word reader `ofFn_bb1Scheme_encCT`): `dev-v9-A` rc 0 (P-1 and `setup_out`).
- 23:46–23:52 P-2 and P-3: `dev-v10-A` … `dev-v14-A` (the last: rc 0, 0 errors); `dev-v14-B` rc 0;
  `dev-v14-N` rc 0.
- 23:53–23:54 `alternatives/simps-lemmas/` (`AltSimpsUse.lean`: `setup_out` with the generated
  `simps` lemmas): devseal A rc 1, 8 errors (setup: `rfl` and type mismatches; `KeyGen`/`Encrypt`:
  no instance found). Natively only the last `Encrypt` step differs (the `simps` lemma reads
  `decodeT m`, not `decodeT (padFin _ ⟦m⟧)`).
- 23:55–23:56 first run of `final_checks.sh` (all rc 0, 0 errors); superseded below.
- 23:57 `insertion/`: the two reader blocks inserted at their anchors into copies of `Defs.lean`
  and `BonehBoyen.lean` (`PlProbe/Scratch/InsDefs.lean`, `InsBonehBoyen.lean`; removing the blocks
  restores the originals byte for byte): native rc 0, 0 errors each.
- 23:58 `alternatives/encCT-congrArg/` (`AltEncCTCongr.lean`, `AltEncCTCongrUse.lean`): owner
  native rc 0; consumer native rc 0; consumer devseal A rc 1, 1 error (unsolved goal: the two
  ciphertexts differ only in the `msgLen`/`wT` index).
- 2026-11-17 00:00–00:03. `devseal.py`'s harness line split (widths); `final_checks.sh` rerun.
- 00:04–00:06. Formula docstrings for the six `Defs` readers (text only); `final_checks.sh` rerun
  (all rc 0, 0 errors; superseded below).
- 00:06. `insertion/` redone with `tools/insert_check.py` on the final blocks (`insert_check.out`):
  `Defs.lean` 476 → 563 lines, `BonehBoyen.lean` 714 → 760 lines, removal restores both bases
  byte for byte; `in-situ-native/`: both copies rc 0, 0 errors.
- 00:07 `scratch/dev-v15-A`: P-2's hypotheses made free of IBE definitions (`p2_init_none`: a
  family `e z : G ≃ Z_p` with `h = X^{−z} g^{e z h}`; `p2_keyGen_ne`: `hinj`, injectivity of
  `bitsToNat` into `Z_p` on `idLen`-bit strings): rc 0.
- 00:08–00:10. **Final recorded checks** (`final_checks.sh`, `final_checks.out`): `native-readers/`
  (readers source `1045ea4b…`), `native-stepm/` (`941bd4bd…`), `devseal-A/` (DEVSEAL A sealed 868),
  `devseal-B/` (DEVSEAL B sealed 869), `axioms/` (`summary.tsv`: 37 constants, 0 non-standard): all
  rc 0, 0 errors in both forms, 0 warnings. The readers did not change after 00:04, so `insertion/`
  stands.

- 00:11–00:13. `probe/READERS-TO-INSERT.md` written by `tools/mk_readers_md.py` from the
  `insertion/` blocks (embedded verbatim, checked). A first attempt used an unquoted shell
  heredoc, so the shell tried to run some back-quoted words (all "command not found" or refused;
  nothing changed on disk except that file, which was then rewritten).

`scratch/` keeps every development log; `scratch/readers-v*` are the native builds of each readers
version. The `alternatives/` copies of `q7b-three-onSpec` and `bb1-mk-readers` duplicate the
corresponding `scratch/` runs, with the sources of that moment as `.lean.txt`. `widths.txt` gives
lines and widths of every probe file; `sources.sha256` the final hashes.
