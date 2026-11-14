# hash-sign — checkpoint 2

Issue base: `eff2dcd0a63f0c371118a17c67b9a5dfc046f4e9`.
Issued exchange pack: `b436d19a0310265b214447ea6710deba32df6dd8`.
Local proof branch: `fill/hash-sign`, never pushed.
Checkpoint source commit: `15f43fd73` (full revision in evidence).

**Status:** checkpoints 1 and 2 are proved. The frozen `hashAndSign_oneTimeSecure`
statement is unchanged and its original admission remains. This is an intermediate
delivery, not a claim that the final security theorem is proved.

The T1 collision finder samples original signature keys and a signing tape,
answers the adversary's single query on its hash, remembers that message, and
emits the remembered message followed by the forged message. The shared-transcript
theorem identifies this execution with the original fixed-tape oracle execution.
The conditional collision theorem proves exactly the CRH game's membership,
distinctness and equal-hash predicate when the source message is fresh and a
logged query has the same hash. Full domain membership is supplied by `hdom`.
Empty logs cannot satisfy the equal-hash witness. Decoded defaults and exhausted
budgets are already included in the arbitrary one-query computation contract.

The T2 forger is also proved. It samples one hash index, forwards at most one
hashed signing query, and hashes the message component of the final output.
Its exact original-scheme forgery probability equals the common transcript's
acceptance-and-hash-freshness probability. Thus source success gives a valid
original-scheme forgery when there was no query or every queried hash differs
from the final message's hash. The final union and complete final checks remain
outside this checkpoint snapshot.

## Source and declarations

Changed owned facade: `TCSlib/Cryptography/Authentication/Signatures/HashAndSign.lean`.
New helpers under its owned `HashAndSign/` directory:

- `CodecReaders.lean`: codec extensionality, signature codec identification,
  and split/concatenation readers.
- `CollisionHandler.lean`: the T1 construction, tape and transcript coupling,
  conditional collision soundness, and the machine/transcript wrapper.
- `ForwardHandler.lean`: the T2 construction and its typed call/finalization readers;
  used by the second checkpoint's game comparison.
- `ForwardGame.lean`: fixed-tape original signer, mapped transcript/output readers,
  forwarded freshness and exact original-game probability equality.
- `FixedGame.lean`: fixed/fresh-tape signing oracles, common transcript and success predicate.
- `OneQuery.lean`: zero/one-query normal forms.
- `OneQuerySampling.lean`: moving a single oracle answer tape before the computation.

`evidence/logs/checkpoint1-declarations.txt` enumerates source declarations.
Generated stored-constant inventories and all-constant axioms are part of the final
evidence workflow. The owned facade currently adds hash-width, oracle-expectation,
acceptance and combined-generator tape readers; the target sketch/title/status
will be updated together with its completed proof.

## Discipline and promotion requests

No other library file is changed. No new simp attribute or admission is added.
The seven pack hashes and all 150 source hashes passed verification at the issue base.
All Python commands use `python3 -I`; all module checks use
`scripts/lean_check_tree.sh`, one module per invocation. No project `lake build`
or unfiltered cache command was run.

Promotion requests:

- `MachineCodec.ext_of_fields` to `Games/Machines.lean`;
- `SignatureScheme.forgerCodec_eq_bitCodec` to `Authentication/Signatures/Defs.lean`;
- `splitBits_append` and `splitBits_pad_concat` to `Authentication/Encoding.lean`;
- `eq_pure_of_cost_zero` and `one_query_cases` to `Games/OracleComp.lean`;
- `expect_simulate_sample_once` to `Games/Hopping.lean`.
- Original-signature fixed-tape helpers `origFixedSign`, `OriginalSuccess`, and
  `forgeGame_eq_fixed` to a signature-game helper module.

Searches are recorded in the evidence logs. Existing public facts are used,
including `expect_sample_pair`, `seedEquiv`, coin/list readers and
`EffFill.ofFn_take_drop_add`. No missing foreign reader has been identified.

overlap: `TCSlib/Cryptography/Games/Forwarding.lean` `fwdRun` and
`polyTimeComputable_fwdRun`: the specialized hashing round follows the same
two-round forwarding pattern, rederived using the published round-input readers.
No private lemma was copied.

overlap: `TCSlib/Cryptography/Authentication/Signatures/HashAndSign.lean`
`polyTimeComputable_hsHashList`: the new reduction hash word pads to `S.msgLen`
rather than `H.rangeLen`, so its polynomial-time wrapper is derived from the
published evaluator/padding combinators. Importing the owned facade into its
helpers would create a cycle. These specialized wrappers are disclosed for review.

## Environment and checks

The isolated checkout is `/private/tmp/hash-sign-fill/repo` on disk-backed APFS.
Native macOS substitutes are recorded because Linux `nproc`, cgroups, `/proc`
and GNU `df` options are unavailable. Initial measurements were 12 CPUs,
19,327,352,832 physical bytes, 11,676,270,592 non-file bytes used,
7,651,082,240 bytes of memory headroom, and 271,874,621,440 bytes of disk free.
Both resource floors passed. Direct user authorization overrides the original
single-host-process rule; from 06:02 UTC the worker caps concurrent checks at three.
The shared checker now also enforces a conservative two-slot semaphore.

The issued 82 Mathlib roots suffice after adding the T1/T2 prerequisites.
The narrowed cache command exited 0 and unpacked 2,339 files, with no download
needed because its hash-checked archive store already held them. Before this
session that store held 32,667 files totaling 1,595,387,830 bytes (origin unknown).
Every present package matches its manifest URL/revision; absent documentation
packages are listed explicitly. No empty olean was found; the Mathlib-root probe passed.

The supplied bootstrap plus ten T1/T2 prerequisites passed through all 158 upstream
modules, and the unchanged base-owned module passed separately. The bridge
experiment module was subsequently checked for its public product-sampling lemma.
The checkpoint helpers and owned-module support lemmas compile without new admissions.
The target's base admission is the sole warning in the owned module.

Base whole-file seals A and B both pass over the complete TCSlib import closure:
1,546 requests with `PolyExpr.eval` exempt, 1,547 with it sealed. Both have zero
failing declarations. Raw inventories, seal sources, requests, logs and tools are
included. All seven paired controls pass: unsealed probes have zero errors;
each sealed negative fails exactly once and each published-reader positive passes.
The first predicate pair used the full request set, and remaining controls use
singleton target sets. Their complete workflow, raw results and superseded
preparations are retained in the baseline evidence.

The final sweep, admission delta, target/all-constant final axioms, final A/B seals,
explicit-unfold scan and style comparison remain required for the final delivery.
They are not claimed complete by this checkpoint.

## Delivery

`patches/` contains the complete format-patch series from the issue base through
this checkpoint. `src/` contains exactly those committed owned source files.
`evidence/SHA256SUMS` covers the delivered evidence, excluding the manifest itself.
The final report will replace this intermediate status, and the final ZIP will have
`hash-sign/` at its root as requested.
