#!/usr/bin/env python3
"""Assemble and verify the complete, explicitly partial checkpoint-1 payload."""
import hashlib
import json
import os
from pathlib import Path
import re
import shutil
import subprocess

BASE='fbd37f447596d4207c8d08b7ef7602f57fe95198'
PIN='7d85785c2e98f0bfdec081a875a9343f06043a8a'
root=Path.cwd()
payload=Path('/private/tmp/sc-garble-runtime/checkpoint1/sc-garble')
replay=Path('/private/tmp/sc-garble-runtime/replay-checkpoint1')
signature_results=Path('evidence/logs/checkpoint1-signatures/results.jsonl')
assert signature_results.exists(), 'signature check is still waiting/running'
last_signature=json.loads(signature_results.read_text().splitlines()[-1])
assert last_signature['exit']==0 and last_signature['errors']==0,last_signature
head=subprocess.check_output(['git','rev-parse','HEAD'],text=True).strip()
assert head=='13f745ed00e49924631c89c00dae2bb110eca6e2'
assert not subprocess.check_output(['git','diff','--name-only','--','TCSlib'])
assert not subprocess.check_output(['git','diff','--cached','--name-only'])
if payload.exists(): shutil.rmtree(payload)
(payload/'patches').mkdir(parents=True)
subprocess.run(['git','format-patch','--full-index','--output-directory',str(payload/'patches'),
                BASE+'..HEAD'],check=True)
commits=subprocess.check_output(['git','rev-list','--reverse',BASE+'..HEAD'],text=True).splitlines()
rows=[]
for commit in commits:
    fields=subprocess.check_output(['git','show','-s',
        '--format=%H%x09%an%x09%ae%x09%aI%x09%cn%x09%ce%x09%cI',commit],text=True).strip().split('\t')
    raw=subprocess.check_output(['git','cat-file','commit',commit])
    assert b'\ngpgsig ' not in raw
    rows.append(fields+['none'])
(payload/'patches/COMMITS.tsv').write_text(
    'hash\tauthor_name\tauthor_email\tauthor_date\tcommitter_name\tcommitter_email\tcommitter_date\tsigning\n'+
    ''.join('\t'.join(row)+'\n' for row in rows))

# Replay in an isolated Git clone without any Lean or dependency cache.
can_reuse_replay = replay.exists() and Path('evidence/replay/checkpoint1.log').exists()
if can_reuse_replay:
    can_reuse_replay = subprocess.check_output(['git','rev-parse','HEAD'],cwd=replay,text=True).strip()==head
    can_reuse_replay = can_reuse_replay and 'PASS: every unsigned commit hash reproduced exactly.' in Path('evidence/replay/checkpoint1.log').read_text()
if can_reuse_replay:
    print('REPLAY PASS retained for unchanged source head',head)
else:
    if replay.exists(): shutil.rmtree(replay)
    replaylog=Path('evidence/replay/checkpoint1.log')
    replaylog.parent.mkdir(parents=True,exist_ok=True)
    with replaylog.open('w') as log:
        subprocess.run(['git','clone','--shared','--no-checkout',str(root),str(replay)],
                       check=True,stdout=log,stderr=subprocess.STDOUT)
        subprocess.run(['git','checkout','--detach',BASE],cwd=replay,
                       check=True,stdout=log,stderr=subprocess.STDOUT)
        patches=sorted((payload/'patches').glob('*.patch'))
        assert len(patches)==len(rows)
        for row,patch in zip(rows,patches):
            env=os.environ.copy()
            env.update(GIT_COMMITTER_NAME=row[4],GIT_COMMITTER_EMAIL=row[5],GIT_COMMITTER_DATE=row[6])
            subprocess.run(['git','-c','commit.gpgsign=false','am',str(patch)],cwd=replay,env=env,
                           check=True,stdout=log,stderr=subprocess.STDOUT)
            actual=subprocess.check_output(['git','rev-parse','HEAD'],cwd=replay,text=True).strip()
            log.write('EXPECTED '+row[0]+' ACTUAL '+actual+'\n')
            assert actual==row[0]
        log.write('PASS: every unsigned commit hash reproduced exactly.\n')

files=subprocess.check_output(['git','diff','--name-only',BASE,head,'--','TCSlib'],text=True).splitlines()
line_rows=[]
for file in files:
    data=subprocess.check_output(['git','show',head+':'+file])
    dest=payload/'src'/file
    dest.parent.mkdir(parents=True,exist_ok=True)
    dest.write_bytes(data)
    old=subprocess.run(['git','show',BASE+':'+file],stdout=subprocess.PIPE,stderr=subprocess.DEVNULL)
    line_rows.append((file,len(old.stdout.decode().splitlines()) if old.returncode==0 else 0,
                      len(data.decode().splitlines())))
    assert all(len(line)<=100 for line in data.decode().splitlines()) and line_rows[-1][2]<=1000
for kind in ['FAIL','WARN']:
    before={s for s in Path('evidence/logs/lint-base.log').read_text().splitlines() if s.startswith(kind)}
    after={s for s in Path('evidence/logs/lint-checkpoint1-final.log').read_text().splitlines() if s.startswith(kind)}
    assert before==after,(kind,before-after,after-before)

# Record the actual scoped slot traffic without altering any host lock.
slotlog=Path('/Users/seyoonr/.lean-slots/slots.log')
Path('evidence/logs/slots.log').write_text(''.join(
    line for line in slotlog.read_text().splitlines(True) if 'tag=sc-garble ' in line))
shutil.copytree('evidence',payload/'evidence',ignore=shutil.ignore_patterns('__pycache__','*.pyc'))
signatures=Path('evidence/declarations/checkpoint1-signatures.txt').read_text()
table='\n'.join('| `'+path+'` | '+str(a)+' | '+str(b)+' |' for path,a,b in line_rows)
report=f'''# sc-garble — checkpoint 1

This is a partial unit delivery, not a final fill. The wrong-key checkpoint is proved;
the direct multi-message result was also completed early because it uses the same readers.
The remaining B1, B2 and Yao work continues on the local branch.

## Pins, identity and transport

- Issued exchange pin: `{PIN}`; both issued packs pass `shasum -a 256 -c`.
- Proof base: `{BASE}`, PR #315's prf-long head, not the records tip.
- Local-only branch: `fill/sc-garble`; checkpoint head: `{head}`.
- Worker: Codex on Seyoon's Mac, in the role called “Claude” by the brief.
- Proof worktree: `/Users/seyoonr/.codex/worktrees/sc-garble/tcslib-exchange`.
- Delivery worktree: `/Users/seyoonr/.codex/worktrees/exchange-sc-garble/tcslib-exchange`.
- Git author and committer: Seyoon Ragavan <complexzetaprime@gmail.com>, the checkout's
  resolved identity. Signing is disabled with `commit.gpgsign=false`; `COMMITS.tsv` says `none`.
- A separate scratch Git clone reproduces every patch commit hash exactly; see
  `evidence/replay/checkpoint1.log`. No proof branch is pushed and no campaign PR is opened.

## Target status

| Declaration | Checkpoint status |
|---|---|
| `spDecStr_wrongKey` | Proved; standard axioms only |
| `specialScheme_wrongKey` | Proved; standard axioms only |
| `nestedSpecial_wrongKeyBot` | Proved; standard axioms only |
| `specialScheme_multiMessageSecure` | Proved directly from D4; standard axioms only |
| `uprob_not_good_le` | Pending B2 |
| `yaoSeed_good_whp` | Pending disjoint-block push-forward and B2 |
| `sliceMultiMessageSecure_of_prfOut` | Pending slice post-processor and maximizing advice |
| Required `uprob_not_good_le_of_perm` | Pending; not claimed or published by this checkpoint |

The source admission comparison is exactly 32 → 28, with only the four completed targets
removed and no added admission. The 28 remaining admissions are in 13 modules. The full final
target remains 25 admissions in 11 modules.

## Proofs and edge cases

The efficient prefix test uses the evaluator of `hG'.easy`, not a polynomial-time assumption
on `E'`. D3 supplies the one-query machine; D1 supplies its negligible budget-one advantage.
Its real acceptance is prefix collision. Uniform evaluation, restriction and point probability
give random acceptance exactly `(2⁻¹)^n`. Honest ciphertexts pass the length guard and fail
decryption exactly when their pad prefixes differ. One further positive `(2⁻¹)^n` gives the
strict lower bound even at `n=0`.

The scheme theorem relabels the two key coin strings and nonce, averages away decryption
coins, and uses monotonicity: string failure produces `1^{{n+1}}`, which decodes to `none`.
It does not need a converse about successful decryption.

The nesting theorem handles zero positions by impossibility of distinct assignments, one
position by the inner marginal, two positions with the first key different by conditioning
on the inner ciphertext, and two positions with the first key equal by outer correctness
followed by the inner marginal. The two errors are nonnegative and their sum is negligible.
Key values may coincide; only the sampled coordinates, not the values, must be distinct.

The direct multi-message proof uses masks `0^n ++ m_i`, the full `2n`-bit answer, and D4.
It has no import from `SpecialEncryptionMulti` and no repeated PRF hybrid or collision proof.
The proofs are uniform in the messages and work at `n=0`, `q(n)=0`, and zero message length
where those types occur. Slice-specific edge cases remain for B1; no claim about them is made here.

## Files and sketches

All changed source files have at most 1000 lines and every line has at most 100 Python
characters. No new `@[simp]` attribute is introduced. Yao and Garbling are byte-identical to
the issue base at this checkpoint.

| Repository path | Base lines | Checkpoint lines |
|---|---:|---:|
{table}

The three security target sketches describe the delivered proofs. The nesting sketch's
three cases are realized by `GarblingCoins.nestedSpecial_wrongKeyBot_of_string_bounds`.
Each proof of at least 15 lines has a sketch and the longer proofs have step structure.
The public coin equivalences have both equation and string-preservation readers.

## Gate 27 hand-off

1. Maximizing slice advice and the empty-fit-set convention: pending B1.
2. Slice post-processor: pending B1. The shared zero-prefix pad identity is already published
   as `spEncStr_eq_zeroPrefixMask` and used by the direct scheme proof.
3. Random-function slice law: D2/D4 provide full uniform pads; the eventual B1 proof must
   identify its reliance on their uniform windows. The current direct proof consumes D4.
4. Triangle and collision bounds: consumed inside D4, not rebuilt by this unit.
5. Frozen `specialScheme_multiMessageSecure`: proved directly from D4. The downstream
   `specialScheme_multiMessageSecure_of_joint` remains proved through the new public readers.
6. B2: pending. The approved circuit reader is planned for that checkpoint.

## Overlap and reuse

The pre-implementation statement-shape searches were run in the chat. Their key families
are re-captured in `evidence/reuse/searches.log` against the pinned base and pinned Mathlib.
The search covers probability, expectation, advantage, push-forward, point probability,
list windows, XOR and encoded-list identities before their use.

- **SG-1 replacement, no ledger debt.** The six private helpers in
  `SpecialEncryptionMulti.lean` are removed. `specialScheme_gen_runAt` and
  `specialScheme_enc_runAt` are published upstream; `specialKeyEq`/`ofFn_specialKeyEq` become
  `specialScheme_keyCoinsEquiv`/`specialScheme_keyCoinsEquiv_ofFn`, and the nonce pair becomes
  `specialScheme_nonceCoinsEquiv`/`specialScheme_nonceCoinsEquiv_ofFn`. The two equivalences
  additionally have `_eq` readers. The corollary's only proof change is reader-name replacement
  and line wrapping. Its header and entire docstring stay byte-identical. Old/new proofs and
  their diff, and the base search showing the private helpers occur only in their source file,
  are under `evidence/headers/`. The surviving private XOR lemma is untouched.
- The scheme relabelling is also near `prfScheme_coinsEquiv` in
  `Encryption/PrivateKey/FromPRF.lean`; that equivalence is for a different scheme and cannot
  type the special scheme's coins. The public NUPPT coin equivalences and string readers are reused.
- `specialScheme_dec_runAt` specializes the public `runAt_spDec` activation theorem to the
  special scheme, exposing its overlong failure word without unfolding a foreign definition.
- `spEncStr_eq_zeroPrefixMask` specializes the pad splitting of Algorithm 157.2. Its nearest
  string relatives are `MultiMsg.zipWith_xor_histBlockOut_maskBlockOut`
  (`FromPRF/ReductionMachine.lean:263`) and `zipWith_xor_replicate_false` (line 241).
  It reuses that zero-mask identity, `List.zipWith_append`, and `List.zipWith_comm_of_comm`;
  it concerns the special ciphertext format rather than the query-history encoding.
- The prefix test's efficient composition is near the prefix comparison in
  `SpecialEncryption.polyTimeComputable_spDecFun`; its input is an oracle answer and independent
  key, so it is a different adapter. It consumes the published efficient string operations.
- `uprob_random_prefix` is a specialization and composition of
  `HardcoreBit.pushesUniform_eval` (Basic:250), `pushesUniform_restrict` (Basic:220),
  `OneWay.uprob_eq_one_div_card` (Basic:144), and `take_ofFn_castLE`
  (`Asymptotic/ReductionSupport.lean:288`). None of those laws is re-proved.
- The collision advantage reads `prfAdv_eq` (`Functions/Defs.lean:87`) directly. It does not
  re-prove `prfAdv_eq_expect`, and does not import the post-base #314 promotion.
- The position/nonce marginal composes `pushesUniform_eval`, `pushesUniform_eval_pair`,
  `PushesUniform.prodMap` and the standard product associator. The conditional two-layer case
  uses `piFinTwoEquiv` and `Equiv.prodProdProdComm`; probability is averaged by `uprob_prod`.
- `uprob_isSome_lt_of_none` is the option-valued corollary of `uprob_not`
  (`Foundations/Probability.lean:109`) and `Option.isSome_iff_ne_none`, rather than a new
  complement proof. It is a candidate for promotion to the shared probability layer.
- `length_nestedInner` packages the length fact previously proved inline in
  `GarblingSpecial.nestedSpecial_decCorrect` (its `hc`, around base line 122). That inline
  fact has no reusable declaration. The helper re-derives the corollary only from the public
  `length_spEncStr`, evaluator reader and `innerLen_eq`; promotion to `GarblingSpecial` is requested.
  This overlap is disclosed explicitly; that frozen file is not changed in this checkpoint.
- No D1–D4 machine, hybrid, random-function law, collision bound, or `encodeList` identity is copied.

## Scope requests and exceptions

Seyoon explicitly approved the single `DAGCircuit.isFaninTwo_iff` reader proposed in
`evidence/scope-request/fanin-reader.patch`; the exact request and answer are preserved.
Its implementation was prepared and temporarily restored while collecting baseline evidence;
the reader is not part of this checkpoint's source commit and is planned for B2.
No other frozen-file exception is used in this checkpoint.

Seyoon subsequently authorized best judgment on exceptions while asleep, with full disclosure,
and authorized messages coordinating the shared Mac resources. The instruction is preserved in
`evidence/scope-request/autonomy.md`.

**Evidence sequencing at this partial checkpoint.** Complete A/B seals (strict and coe), paired
negative controls, the explicit-unfold scan and the final full-order sweep are deferred until
the remaining proofs stabilize. They are mandatory final-delivery work, not waived checks.
The pilot whole-file strict A seal of Pad passes with 1618 sealed definitions and 633 notation
exclusions. Failed seal-harness setup runs are retained; they are not counted as proof results.
The unmodified base's full bootstrap, current seven-module checks, source freeze controls,
name scan, admissions, axioms and lint are complete. This checkpoint is not represented as a
fully validated final unit.

## Host resources and coordination

The binding host-wide cap is **3 Lean processes**. Every command of this worker that starts
Lean, Lake or `lean_check_tree.sh` uses the issued wrapper, default `~/.lean-slots`, tag
`sc-garble`. The sole narrowed cache command holds `-k 3`; module checks release the slot
between modules. No `lake build`, unfiltered cache fetch, RAM disk, copied dependency tree,
or Python invocation without `python3 -I` was used.

The Mac has 12 CPUs and 19,327,352,832 bytes of physical memory. The worktree preflight's
headroom computation and APFS disk figures are in `evidence/logs/preflight.log`; it passed
the 4 GiB memory and 12 GiB disk floors. The toolchain is the shared host Lean 4.25.0 install.
All packages are this worktree's fresh `.lake/packages`, at exact manifest URLs and revisions;
the four documentation packages are correctly reported ABSENT. Package verification passes.
The 71-root narrowed fetch unpacked 2066 already-cached archives with zero download failures.
The archive store pre-existed this run (32,667 files, 1,623,212 KiB; origin unknown), and is not
claimed as a download by this session.

The Ladner worker initially reported a different lock directory. I asked it to join the
issued slot domain, notified derand, and coordinated one gap with seq-zk when the wrapper's
five-second poll was starved by short modules. Ladner released its temporary legacy-runner
reservation at 09:12:38 UTC and finished Lean at 09:32:16 UTC. No other worker's process or
lock was edited or killed. I do not certify aggregate global scheduling before all workers
joined the same lock domain; my observed process snapshot had three native Lean processes.
Scoped wrapper traffic is delivered in `evidence/logs/slots.log`.

## Evidence and checks

- Base bootstrap: all 166 issued modules, zero errors, exactly 32 admission warnings.
- Checkpoint source checks: all seven changed modules/helpers pass; no new helper admission.
- Four completed targets: only `propext`, `Classical.choice`, `Quot.sound`.
- Changed-file inventory: 69 stored constants, 67 standard-only; the known pending B1 target
  and `garbling_good_whp` retain `sorryAx` through the pending work. The latter must become
  standard-only after B2. The two Yao end-to-end consumers retain their baseline admissions.
- Frozen headers/definitions: 139 base declarations, six expected SG-1 removals, zero other
  differences. One-character and seventh-removal controls each detect exactly one violation.
- Name scan: 1,275 base source files, 29,518 resolved explicit names; 20 additions,
  two authorized SG-1 replacements, no clash. Generated descendants also receive the final sweep.
- Lint: 92 FAIL / 101 WARN at base and checkpoint; the exact FAIL and WARN line sets agree.
- Width/length: all seven changed/new source files satisfy 100 characters and 1000 lines.
- Signature inventory: `evidence/declarations/checkpoint1-signatures.txt` and the authoritative
  Lean `#check` output in `evidence/logs/checkpoint1-signatures/`.
- Every current evidence file, including failed probe/seal setup sources and raw logs, is
  included. The evidence and top-level SHA-256 manifests have exact relative path sets,
  without leading `./`. Transient Python bytecode is excluded.

## New declarations: source signatures

Section parameters `G E hE hGE` have their original types from the base file. Lean's full
elaboration, including those parameters and implicit binders, is recorded by the signature probe.

```lean
{signatures.rstrip()}
```
'''
(payload/'REPORT.md').write_text(report)

def manifest(folder):
    paths=sorted(p for p in folder.rglob('*') if p.is_file() and p!=folder/'SHA256SUMS')
    (folder/'SHA256SUMS').write_text(''.join(hashlib.sha256(p.read_bytes()).hexdigest()+'  '+
        p.relative_to(folder).as_posix()+'\n' for p in paths))
    listed=[line[66:] for line in (folder/'SHA256SUMS').read_text().splitlines()]
    assert listed==[p.relative_to(folder).as_posix() for p in paths]
    result=subprocess.run(['shasum','-a','256','-c','SHA256SUMS'],cwd=folder,
                          text=True,stdout=subprocess.PIPE,stderr=subprocess.STDOUT)
    assert result.returncode==0,result.stdout
    print('MANIFEST PASS',folder,len(paths),'files')

manifest(payload/'evidence')
manifest(payload)
print('PAYLOAD',payload)
print('SOURCE_HEAD',head)
