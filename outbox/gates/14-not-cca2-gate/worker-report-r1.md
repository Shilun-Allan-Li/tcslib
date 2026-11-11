# not-cca2 — escalation at checkpoint 2 (final partial delivery)

**The target remains admitted. This is not a completed fill.** Checkpoint 1 was
returned separately as `not-cca2-checkpoint1.zip`. Work stops at the issued brief's
missing-reader escalation route. The mathematical target has not been refuted.

## Escalation and requested correction

The published `FixedLengthScheme.indImpl_challenge_none` equation relies on implicit
identifications of its query and answer widths. A minimal client passes before
sealing `inLens` and `outLens`, but fails when those two foreign definitions are
irreducible, even when the client merely applies `heq_of_eq` to the published
reader. Direct application, an explicit query cast, and a heterogeneous-equality
consumer were tried; the width conversion remained blocked under the required seal.

The exact failing client, diagnostic, attempted consumer and smallest proposed
provider correction are in **`evidence/READER-REQUEST.md`**. This records failure of
the tested clean reader-only routes, not a proof that all possible transport
arguments are impossible.

The proposed `indImpl_challenge_none_cast` reader spells both input and output
casts explicitly. Its provider-side prototype and a client under sealed `inLens`,
`outLens` and `indImpl` compile with only the three permitted axioms. See
`evidence/ReaderProposal.lean` and `evidence/logs/reader-proposal.log`.
The proposal is review evidence only: it is absent from the production patches and
owned source. The issued scope authorizes no addition to OracleSecurity.lean, so
that file was not edited. A maintainer can publish the additional reader and issue
a continuation base.

## Exact source status and checked frontier

- Issue base: `4a09f3993eb9344fc5714610e41ab141a0144db8`.
- Exchange pin: `20ca57c15da54342358b27ae2fee359acf06560d`.
- Repository: `Shilun-Allan-Li/tcslib`; fresh separate checkout; local branch
  `fill/not-cca2`. No branch was pushed. The delivery head is in `evidence/delivery.json`.
- Lean 4.25.0; Mathlib `029db123ddaa7f8fd0d18cea3b1b33bf84dacd1e`.
- Only two tracked files changed, both under
  `TCSlib/Cryptography/Encryption/PrivateKey/`: `FromPRF.lean` adds exactly the
  authorized public `prfScheme_dec` reader, with its formula and proof `rfl`;
  `OracleFromPRF.lean` adds 28 private helpers and is 460 lines long.
- All original declarations, statements, statement prose, proof sketches and global
  simp attributes are preserved. There are no sketch edits and no new source admissions.
- The target `prfFixedScheme_not_cca2` still has its original `sorry`. The existing
  CPA/CCA1 admissions remain. The target and its corollary therefore still include
  `sorryAx`; the final axiom requirement has **not** been met.

The checked adversary is `NUPPT.ofPolyTimeUniform cca2Next_poly (.const 0)`. Its raw
activation equations ask Challenge on `0^n ++ 1^n`, then Dec on the last-bit-flipped
challenge answer, then output the negation of the last bit of the second answer.
Its polynomial-time proof uses the existing closure combinators. The intended
query budget is `.const 2`; its complete codec/`toComp` and simulation proof remains
pending. No new machine host was built.

The encryption frontier is checked for every key/coin string:

1. The selected half of the challenge query is the constant message `b`.
2. Every generated key and encryption nonce is an `n`-bit word.
3. The actual encryption word is `pairEncode (List.ofFn x) (List.ofFn (m + F n k x))`;
   its width is exactly `3*n+2`.
4. For `n>0`, modifying its last bit preserves the nonce and pairing prefix, keeps
   the width, and gives a distinct ciphertext with the last masked bit flipped.
5. At the list/vector algebra level, XOR-unmasking that payload gives the message
   with its last bit flipped.

The actual challenge-oracle assembly, CCA2 decryption-oracle proof, and final
probability/advantage calculation are not delivered. The failed challenge consumer
was removed from production source and retained verbatim in `evidence/attempts/`.

## Verification and limits

All seven issued pack entries match both their SHA-256 values and committed Git
bytes at the exchange pin. All 232 issued source hashes passed before editing.

The 129-module prerequisite closure was checked serially in supplied order. The
first target-file attempt exposed local proof errors, then the repaired target
passed. Both owned modules were rechecked at the final partial source; see
`logs/from-prf-final.log` and `logs/oracle-from-prf-final.log`. Every Lean check,
including probes, ran through `scripts/lean_check_tree.sh`, one module and one
Lean process at a time. The remaining 103 supplied downstream modules were not
swept after this escalation. The checked frontier is therefore the prerequisite
closure and the explicit probes, not the full 232-module acceptance sweep.

`logs/source-admissions.log` compares source admissions across all 232 supplied
modules: **33 at base, 33 now**, unchanged module by module. This is a source
comparison, not a replacement for the pending full warning sweep. The final
`#print axioms` output is in `logs/axioms-final-partial.log`; the elaborated helper
axiom census is in `logs/refs-final-partial.log`. New proved helpers use only
`propext`, `Classical.choice`, and `Quot.sound` (subsets allowed).

The type-and-value reference census includes generated helper declarations and
foreign definitions; the oracle input/output length definitions are explicitly
included as interface dependencies. `seal-candidates.json` lists every candidate,
its home module, instance/projection status and any exclusion. Reducible notation,
abbreviations and primitive structure projections are recorded separately; no
unsafe reducibility override is used. The seal harness also handles registered
instances by forwarding through an alias while sealing the original definition;
this frontier has no active foreign instance candidate. The retained production
frontier passes the final seal; its control passes before sealing and fails after
sealing at the intended `inArg` definitional equality. The unretained challenge
consumer's seal failure is the reported escalation, not hidden by that passing
frontier seal.

`logs/explicit-unfold-scan.log` finds only the owned `cca2Adversary` as an explicit
unfold target and no foreign explicit unfold/delta target. The required command
`python3 -I scripts/campaign_style_lint.py TCSlib/Cryptography/Encryption/PrivateKey --check8b`
returns **0 FAIL, 5 WARN over 10 files**. The warnings name existing public definitions;
none of the new definitions is public. `git diff --check` passes.

## Environment and cache

Initial preflight: `nproc=9`; overlay disk free **59,564,011,520 bytes**; memory
headroom **9,525,805,056 bytes**, using `/proc/meminfo`'s `MemAvailable` fallback
because `/sys` and cgroup counters are not exposed. Both issued floors pass.
The clone, toolchain, cache, temporary files and oleans use the disk-backed overlay;
`/tmp` is tmpfs and was not used as `TMPDIR`.

The official Lean archive was freshly downloaded and extracted for this task;
its URL and SHA-256 are in `logs/toolchain-provenance.log`. No other session's
scratch dependency tree, package build, toolchain or olean store was reused.
The task-local cache store initially did not exist (0 files, 0 bytes). Only the
98 supplied direct Mathlib roots were requested. The initial cache fetch had 603
HTTP 429 failures; the allowed retry fetched those 603 and successfully unpacked
all **2,381 files**. No cleaned retry was needed. All present package URLs/revisions
match the manifest; the four unneeded documentation packages are ABSENT. Last pin
check: **PASS (all present packages match; order imports no absent package)**.
There are no zero-size package oleans, and the Mathlib-root import probe passed.

`/usr/bin/time` is absent. `time_check.py` records each module's UTC start/end,
elapsed/user/system times, exit status and maximum child RSS using Python's
`resource.getrusage`. All Python invocations used `python3 -I`. No project
`lake build` or unfiltered cache fetch was run; the cache tool's prescribed
internal bootstrap was left to Lake.

## New declarations and payload

The one new public declaration is **`prfScheme_dec`**. All following helpers are
private in the owned target file:

- List/vector operations: `cca2FlipLast`, `cca2FlipLast_poly`, `cca2FlipLast_snoc`,
  `cca2FlipLast_append`, `cca2FlipLast_pair`, `cca2FlipLast_length`, `cca2FlipLast_ne`,
  `cca2FlipBits`, `cca2FlipLast_ofFn`, `cca2FlipBits_unmask`, `cca2Unmask`,
  `cca2OfFn_padFin`.
- Adversary: `cca2Next`, `cca2Next_poly`, `cca2Adversary`, `cca2Adversary_run`,
  `cca2Adversary_one`, `cca2Adversary_two`.
- Encryption/challenge preparation: `cca2Encrypt`, `cca2Messages`,
  `cca2Messages_ofFn`, `cca2Messages_choice`, `cca2Alter`, `cca2Alter_ofFn`,
  `cca2Alter_ne`, `cca2CtLen`, `cca2Gen`, `cca2Cipher`.

No copied private proof or private machine implementation was introduced. Existing
published XOR and machine-reader lemmas are used directly.

`patches/` is the complete local `git format-patch` series from the issue base;
`src/` is the exact committed owned source. `evidence/` includes the issued inputs,
hashes, cache/bootstrap logs, final checks, census/seal/controls, failed attempts,
minimal interface reproducer and checked reader proposal. `evidence/delivery.json`
records the delivery head, source hashes and patch replay at the exact base using
a separate Git index. Checkpoint 1 remains a separate immutable chat artifact.
