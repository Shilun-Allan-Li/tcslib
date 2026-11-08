"""File Gate06C dispositions and the conservative no-eligible-proof result."""
from pathlib import Path
import hashlib
import json
import subprocess
import zipfile

PREP = Path(__file__).resolve().parent
MAIN = Path('/Users/seyoonr/phd_experiments/tcslib_all_branches/tcslib-pass-shelat-ch2-4')
BASE = MAIN / 'briefs/pass-shelat-ch5-8'
GATE = BASE / 'gates/06-ch5-8-statements'
DEST = GATE / 'review-r1-c'
SCREEN = BASE / 'maintainer/proof-dependency-screen-2026-11-08'


def sha(raw):
    return hashlib.sha256(raw).hexdigest()


def git(*args):
    return subprocess.check_output(['git', '-C', str(MAIN), *args], text=True).strip()


def load(path):
    return json.loads(path.read_text())


def archive(source, target):
    members = []
    for file in sorted(source.rglob('*')):
        assert not file.is_symlink(), file
        if file.is_file() and '__pycache__' not in file.parts:
            members.append((file.relative_to(source).as_posix(), file.read_bytes()))
    with zipfile.ZipFile(target, 'x', zipfile.ZIP_DEFLATED, compresslevel=9) as zipped:
        for name, raw in members:
            info = zipfile.ZipInfo(name, date_time=(2026, 11, 8, 0, 0, 0))
            info.external_attr = 0o100644 << 16
            info.compress_type = zipfile.ZIP_DEFLATED
            zipped.writestr(info, raw)
    return {'archive': target.name, 'sha256': sha(target.read_bytes()),
            'files': [{'path': name, 'bytes': len(raw), 'sha256': sha(raw)}
                      for name, raw in members]}


def sums(root):
    rows = [f'{sha(file.read_bytes())}  {file.relative_to(root).as_posix()}'
            for file in sorted(root.rglob('*')) if file.is_file()]
    (root / 'SHA256SUMS').write_text('\n'.join(rows) + '\n')


def main():
    assert git('branch', '--show-current') == 'cryptography/pass-shelat-ch2-4'
    assert not git('status', '--porcelain')
    git('pull', '--ff-only', 'origin', 'cryptography/pass-shelat-ch2-4')
    assert not git('status', '--porcelain') and not DEST.exists() and not SCREEN.exists()
    assert sha((GATE / 'findings/gate06C-r1-findings.md').read_bytes()) == '577621ca9f6fa665dbc6bd3150f4625ddf2b05d19b9f6021bf652c30c8580ac4'
    assert sha((PREP / 'review-cca/report.md').read_bytes()) == 'd2b9ad26f14e34fe6abd2b10b4641abb1506238bd37a8c28127e92b51009cff3'
    assert sha((PREP / 'review-seqzk/report.md').read_bytes()) == '2e74b5a77d78647b32f567e8a25bf6076da098100a569f10afb8023bec56f472'
    validation = load(PREP / 'combined-comment-proposals-r2/validation.json')
    assert validation['file_count'] == 13 and validation['all_exact_noncomment_bytes_identical']
    assert validation['patch_sha256'] == 'ff7cd28cb4b92d83702f3aba81718c742a7c4f3167d19f5b6becbc62c50e018d'
    screen = load(PREP / 'dependency-screen/summary.json')
    assert screen['direct_sorry_targets'] == 33 and screen['eligible'] == 0
    # The separately frozen supplement has its own inventory and exact-source validation.
    supplement = (PREP / 'dependency-screen-campaign-supplement/report.md').read_text()
    assert '39 targets were screened and 0 are eligible' in supplement
    exchange = load(PREP / 'exchange-archive.json')
    assert exchange['sha256'] == '577621ca9f6fa665dbc6bd3150f4625ddf2b05d19b9f6021bf652c30c8580ac4'
    DEST.mkdir()
    artifacts = []
    for directory in ['review-cca', 'review-seqzk']:
        artifacts.append(archive(PREP / directory, DEST / (directory + '.zip')))
        for name in ['report.md', 'report.json']:
            (DEST / (directory + '-' + name)).write_bytes((PREP / directory / name).read_bytes())
    for directory in ['combined-comment-proposals-r2', 'combined-comment-proposals', 'combined-source-preview']:
        artifacts.append(archive(PREP / directory, DEST / (directory + '.zip')))
    for original, name in [
        ('combined-comment-proposals-r2/all-minor-prose-corrections.patch', 'all-minor-prose-corrections.patch'),
        ('combined-comment-proposals-r2/validation.json', 'combined-proposal-validation.json'),
        ('exchange-archive.json', 'exchange-archive.json'),
        ('validate_comment_proposals.py', 'validate_comment_proposals.py'),
        ('record_resolutions.py', 'record_resolutions.py'),
    ]:
        (DEST / name).write_bytes((PREP / original).read_bytes())
    (DEST / 'artifacts.json').write_text(json.dumps({'archives': artifacts,
        'gate06C': {'blockers': 0, 'majors': 0, 'minors': 4, 'state': 'CLOSED'},
        'all_four_statement_gates_closed': True, 'all_minor_findings': 15,
        'combined_comment_files': 13, 'comment_proposals_applied': False,
        'proofs_started': False, 'new_external_job': False, 'new_branch': False,
        'native_rerun': False, 'PR232_clear_to_merge': False,
    }, indent=2) + '\n')
    (DEST / 'README.md').write_text('''# Gate06C reviewed dispositions and combined comment proposal

06C is CLOSED at the frozen audited source,0blockers/0majors/4minors. The separate
resolutions-06C-r1.md records all dispositions. Three bounded internal reviews
checked the CCA findings, phase normalization, and the audit's exact source/receipt
integrity. Their source/model/version/native limitations remain explicit.

The combined proposal covers all15 A/B/C/D minor dispositions in13 files. Its
SHA-256 is ff7cd28cb4b92d83702f3aba81718c742a7c4f3167d19f5b6becbc62c50e018d.
All patches pass git apply --check jointly; scratch application proves exact
noncomment-byte equality in every file. All code, algorithms, costs, statements,
attributes, imports, proofs and admissions are unchanged. No tracked Lean source
was edited, no proof filled and no native run performed. The proposals remain
unapplied on draft PR #232.

One early own combined-proposal check encountered an input hash mismatch before
the internal CCA proposal was frozen. It stopped before application. That empty
attempt's failure metadata and exact old validator are preserved separately;
the final frozen hashes were checked using a new output directory. No attempt
was overwritten or presented as a native failure/pass.

The merge-tree preview against target records636609a032bd48899dd5adbc3752353a3b2efc66
is textually clean. It writes only temporary Git objects and includes accepted
S2's five disjoint source changes; it excludes the comment proposals and is not
a combined-source build or seal pass. No ref/index/working source was changed.
Later records-only updates do not turn that preview into native evidence.

The processed user-supplied C report is archived on the exchange; see the exact
exchange-archive.json. The local inbox copy was removed only after remote blob
verification;27 other untracked paths were preserved. No auditor push is claimed.

The strict full-role proof screen is filed separately under
maintainer/proof-dependency-screen-2026-11-08/:0eligible of39 direct crypto targets.
No proof fill or temporary branch is started. The user confirms that accepted
proofs belong on cryptography/pass-shelat-ch2-4 through reviewed PRs; temporary
branches should be retired after the user's merge, not become lasting forks.

**Not yet clear to merge — all four statement gates close, but comment application and combined-source verification remain before #232 lands.**
''')
    sums(DEST)
    resolution = GATE / 'resolutions-06C-r1.md'
    assert not resolution.exists()
    resolution.write_text('''# Gate06C round1 resolutions

**CLOSED: PASS WITH MINORS,0blockers/0majors/4minors**, at frozen source
`3f6db40e1688c4a0bb922c9575dd3bd2157a650b`. Verbatim findings were committed first
at records636609a032bd48899dd5adbc3752353a3b2efc66:67,052bytes, SHA-256
`577621ca9f6fa665dbc6bd3150f4625ddf2b05d19b9f6021bf652c30c8580ac4`.
They arrived as user-supplied untracked local Codex Markdown; no auditor push
identity is invented. Issued records/exchange remain c81baa7712ab1b43357276ef5df138d02616c9d0 /
5928e06c02b382b63b9b384db89d0458b520f351. The incoming report remains unchanged.

| Finding | Maintainer disposition |
| --- | --- |
| C-01, minor | Accept a prose qualification, preserving the algorithm and all statements. For generated keys and n>0, both length checks force successful canonical pair parsing and the valid2n-bit tag. At n=0, the malformed four-bit0000 decrypts to the valid empty message; explicitly disclose this finite-prefix behavior. There is only one plaintext at zero. No new parsing guard is commissioned. |
| C-02, minor | Accept the first-discrepancy coupling with an always-reject-fresh-pair game. Rejected guesses reveal no random tag there; each candidate succeeds with probability at most2^(-2n), giving q/2^(2n) per bit-game. Repeated failed guesses in the real game do not have constant conditional success probability. Combining both bit-games can introduce fixed factors, so the sketch no longer promises an unjustified coefficient-one final advantage bound. The negligible-security statement is unchanged. |
| C-03, minor | Accept count-and-length phase normalization with canonical metadata/fallback. With k original moves and p=proverMoves, retain exactly p bounded real prover messages and append k-p honest-prover empty fillers. Do not force a cheating verifier's replies empty. This fixes real views and bounds every simulated prefix including pairing/index overhead. Handle k=0 or Q=0 by the exact empty-history view. Statistical post-processing gives Q times delta; no new simulator-shape premise is assumed. In3COL each padded six-move phase contains two real prover messages and one prover filler. |
| C-04, minor | Accept explicit equality testing in the hypothetical short-tag counterattack. Skip the refused challenge-equality branch and charge nonce/masked-message coincidences to the negligible failure probability (at most2/2^n in the random-pad model, plus PRF error). The attack is overwhelmingly successful; it is not unconditionally query-distinct. The actual whole-ciphertext tag algorithm is unchanged. |

The concrete proposals and frozen internal reviews are in review-r1-c/. The
combined A/B/C/D patch covers15 minor dispositions across13 files; it passes
joint application checking and exact noncomment-byte preservation. It remains
unapplied. No theorem/header/body/hypothesis/algorithm/cost/import/attribute or
admission was changed, and no new Lean check or proof completion is claimed.
The report's table says the private XOR lemma lacks a docstring; source already
has its formula docstring. This nonmaterial report inaccuracy is recorded without
editing the original or introducing a new source finding.

## Preserved scope and evidence limits

This is a statement/sketch/correctness gate. All13 direct Composability admissions
and their six derived admitted-dependent results remain; the3COL numerical
negligibility proof does not discharge generic repetition. No public-key CCA2
construction or many-challenge bridge follows. Fixed-length padded games retain
their explicit query-domain restrictions. CPA-only converses and distinct COPY/
bottom conventions remain as stated. Strict aborting simulation concludes the
stated statistical error, not a truncation theorem for expected-time simulation.

The bounded integrity review reproduces171 exact source sections,20 records,
all14 listed pack leaves,3,419 archived entries and eight recorded Composability
source-pass receipts. These are source/historical-run identity checks, not new
kernel runs. Common17 source failures,46 admitted-dependent identities and legacy
C3 observations remain disclosed. Root-export elaboration and combined post-S2
verification are not granted by this audit.

The auditor compared the exact supplied PS10 PDF and author PSV versions. Historical
publisher-byte/text identity is unverified. Official Goldreich reader content was
accessed, but its recorded raw PDF hash and published-edition comparison were not
verified; draft pagination is not transferred to the published book. Deferred
paper proofs were reviewed as maintainer sketches. No fresh primary-PDF access
or native run is claimed by these maintainer dispositions. Internal finite models
illustrate boundary cases only and do not supply Lean or hardness proofs.

All four gates now close at the frozen source: A0B/0M/2m, B0B/0M/5m,
C0B/0M/4m, D0B/0M/4m. Existing PR #232 still needs the comment proposals and
source-matched reconciliation/checks with merged S2 before landing. A clean
merge-tree preview is not verification. Cleanup remains deferred, and the strict
full221-path dependency screen finds no eligible direct crypto proof among39
targets; no new fill, audit or proof branch is prepared by this closure.

**Not yet clear to merge — 06C and all statement gates are closed; #232 still needs comment application and combined-source checks.**
''')

    SCREEN.mkdir()
    screen_archives = [archive(PREP / 'dependency-screen', SCREEN / 'gate06-screen.zip'),
                       archive(PREP / 'dependency-screen-campaign-supplement', SCREEN / 'campaign-base-screen.zip')]
    for original, name in [('dependency-screen/report.md', 'gate06-report.md'),
                           ('dependency-screen/summary.json', 'gate06-summary.json'),
                           ('dependency-screen-campaign-supplement/report.md', 'campaign-base-report.md')]:
        (SCREEN / name).write_bytes((PREP / original).read_bytes())
    (SCREEN / 'artifacts.json').write_text(json.dumps({'archives': screen_archives,
        'direct_targets_screened': 39, 'eligible': 0, 'cleanup_role_paths': 221,
        'cleanup_roles': {'CONSUMER': 97, 'PROVIDER_ONLY': 124},
        'method': 'Conservative complete local source-import closures, not declaration-level usage',
        'no_new_proof_or_branch': True, 'no_external_job': True,
    }, indent=2) + '\n')
    (SCREEN / 'README.md').write_text('''# Proof progress under the deferred-cleanup boundary

The user authorizes proof work avoiding cleanup-targeted dependencies, erring on
caution. Use all221 issued CONSUMER/PROVIDER_ONLY files, not merely the122 actual
changed paths in the partial delivery. This conservative file-level screen finds
**0eligible targets among39 direct cryptography admissions**:33 in Gate06's four
prongs and six on the accepted campaign base. Full declarations, source hashes,
complete import closures, role intersections and blocker chains are archived.

Garbling's tiny closure still imports two PROVIDER_ONLY files, DAGCircuit and
Foundations/Probability. The earlier no-overlap comparison against122 changed
files was insufficient for this stricter screen. Extraction and all other named
prongs intersect still more scope. Games/Efficiency's four targets share112 local
sources and108 cleanup intersections. The two Universal targets are themselves
cleanup CONSUMER files.

These are overapproximated import dependencies; this does not prove that every
possible implementation would actually break or read a changed definition.
No declaration-level waiver is inferred. Respecting the user's cautious boundary,
park these proofs rather than manufacture a disconnected helper/primitive. No
new proof, fill or branch is created. Gate06 audit dispositions and existing-PR
verification are separate maintainer work; all proof/algorithm statements stay
unchanged. Cleanup continuation and its pending worker/scope choices remain
deferred until the user resumes them.

The user also confirms that accepted proof work should land through PRs targeting
cryptography/pass-shelat-ch2-4, with the user approving/merging. Temporary review
branches should be retired after merge. No lasting parallel campaign fork is
introduced by this screen or by the already-existing #232/#248 drafts.

**Not yet clear to merge — no direct proof meets the current dependency boundary; existing PR acceptance checks remain separate.**
''')
    sums(SCREEN)

    plan = GATE / 'PLAN.md'
    text = plan.read_text()
    first = text.index('**Current status,')
    end = text.index('**Round 1:', first)
    text = text[:first] + '''**Current status,2026-11-08 PST:** all four user-dispatched Codex statement audits are CLOSED:
06A0B/0M/2m,06B0B/0M/5m,06C0B/0M/4m,06D0B/0M/4m. Verbatim findings and
separate resolutions-06A/B/C/D-r1.md preserve their pins and evidence limits.
The combined unapplied comment proposal in review-r1-c/ covers15 minors/13 files,
jointly applies and preserves exact noncomment bytes. No proof is completed.
PR #232 remains draft at3f6db40e1688c4a0bb922c9575dd3bd2157a650b; accepted S2 is
absent from that head. A clean merge-tree preview is not a combined-source check.
Final comment application/current-source verification remain before landing.
Under the user's cautious full221-path cleanup screen, all39 direct crypto proof
targets are currently blocked; no new fill or proof branch is prepared. The issued
round1 account below is historical and unchanged in the pinned Git snapshot.

''' + text[end:]
    text = text.replace('**Not yet clear to merge — external statement audits and their resolutions remain.**',
        '**Not yet clear to merge — all statement gates close; comment application and combined-source verification remain.**')
    plan.write_text(text)
    handoff = BASE / 'MAINTAINER-HANDOFF.md'
    text = handoff.read_text()
    old = '**User dispatch confirmed for all four (2026-11-07 PST). 06A CLOSED (0B/0M/2 minors), 06B CLOSED (0B/0M/5 minors), 06D CLOSED (0B/0M/4 minors); 06C findings pending.**'
    new = '**All four user-dispatched statement gates CLOSED:** 06A0B/0M/2m,06B0B/0M/5m,06C0B/0M/4m,06D0B/0M/4m (C resolved2026-11-08 PST).'
    assert old in text
    text = text.replace(old, new)
    text = text.replace('Ten comment-only file corrections are prepared/unapplied in `review-r1-ad/` and `review-r1-b/`; no PR merge clearance.',
        'All15 minor dispositions have a joint13-file comment-only proposal in `review-r1-c/`; exact noncomment equality/application checks pass, proposal unapplied. No PR merge clearance.')
    text = text.replace('Gate06C and frozen3f6 head remain independent;13-conflict preview excludes local repairs.',
        'All Gate06 statement gates now close, including C; the3f6 head remains unchanged pending combined-source checks. The older13-conflict cleanup preview excludes local repairs.')
    text = text.replace('Narrow independent Gate06B/D options and continued blockers are in `maintainer/cleanup-deferral-2026-11-08.md`.',
        'The stricter full221-file dependency screen now finds0eligible among39 direct crypto targets; earlier narrow B/D suggestions are superseded. Details: `maintainer/proof-dependency-screen-2026-11-08/`.')
    text = text.replace('precise CPA waits for Gate 06C and concrete RSA/Rabin need a real encoding bridge.',
        'Gate06C statements are now closed, but precise CPA still waits for its admitted bridge proof; concrete RSA/Rabin need a real encoding bridge.')
    handoff.write_text(text)
    deferral = BASE / 'maintainer/cleanup-deferral-2026-11-08.md'
    text = deferral.read_text()
    marker = '**Not yet clear to merge — independent narrow work is available; cleanup acceptance and Gate06 landing remain open.**'
    assert marker in text
    text = text.replace(marker, '''## Latest cautious screen and branch policy

The user authorizes only proof work avoiding cleanup-targeted dependencies, erring
on caution. The full221-file screen in [the recorded inventory](proof-dependency-screen-2026-11-08/README.md)
supersedes the earlier122-changed-path recommendation:0eligible of39 direct crypto
proof targets, including garbling and all four Games/Efficiency targets. No new
proof/fill/branch is started. This file-level overapproximation is not a claim
that every possible proof would break. All Gate06 statement audits now close;
their comment application and combined-source checks remain separate maintainer work.
Accepted proof PRs target cryptography/pass-shelat-ch2-4; temporary branches retire
after the user's merge. Cleanup continuation stays deferred until user resumption.

**Not yet clear to merge — no proof passes the cautious screen; existing PR integration checks remain.**''')
    deferral.write_text(text)
    implications = BASE / 'implications'
    readme = implications / 'README.md'
    text = readme.read_text().replace('are not yet landed or externally statement-gated.',
        'are not yet landed; all four Gate06 statement gates now close at their frozen source, but the designated proofs remain admitted.')
    readme.write_text(text)
    public = implications / 'public-key-draft.md'
    text = public.read_text().replace('## Exact CPA bridge: waiting on Gate 06C',
        '## Exact CPA bridge: statement-gated, proof still missing')
    text = text.replace('Its statement gate and fill precede any claim of a completed exact CPA implication.',
        'Gate06C is now closed at the frozen statement source; its admitted bridge still needs a fill before any claim of a completed exact CPA implication.')
    public.write_text(text)
    log = MAIN / 'PassShelatChapter5-8Plan.md'
    log.write_text(log.read_text() + '| 2026-11-08 (PST) | **Gate06C CLOSED0B/0M/4minors; all four statement gates now closed.** '
        'Verbatim C findings were intaken first at636609a032bd48899dd5adbc3752353a3b2efc66, SHA577621ca9f6fa665dbc6bd3150f4625ddf2b05d19b9f6021bf652c30c8580ac4. '
        'C01 positive-n parsing/zero-prefix prose; C02 first-discrepancy coupling/fixed-factor precision; C03 phase count+length/metadata normalization with only honest-P fillers; C04 equality/collision branch. '
        'No algorithm/statement/premise/admission change. Three bounded internal reviews and combined13-file/15-minor comment proposal archived under review-r1-c; joint apply/exact noncomment checks pass, unapplied/no native replay. '
        'Early mutable-proposal hash-guard abort retained, final frozen retry separate. S2/Gate06 source paths disjoint, merge-tree preview clean but not native verification. '
        'Processed local C report archived at exchange '+exchange['exchange_archive_commit']+',27 other untracked files preserved; no auditor push inferred. '
        '**User cautious proof boundary:** full221-role-path screen excludes all33 Gate06 plus6 accepted-base direct crypto admissions (0/39 eligible); no new proof/fill/branch. '
        'User confirms accepted proof PRs target campaign base, temporary branches retire after user merge. Cleanup remains deferred; #232 requires comments/current-source checks, no merge clearance. | resolutions / scope |\n')
    assert not any(file.suffix == '.lean' for root in [DEST, SCREEN] for file in root.rglob('*'))
    check = subprocess.run(['git', '-C', str(MAIN), 'diff', '--check'], capture_output=True, text=True)
    assert check.returncode == 0, check.stdout
    print(json.dumps({'review_root': str(DEST), 'screen_root': str(SCREEN),
                      'gate06C': 'CLOSED_0B_0M_4m', 'proof_targets': 39,
                      'eligible': 0, 'source_changed': False,
                      'status': 'WRITTEN_NOT_COMMITTED'}, indent=2))


if __name__ == '__main__':
    main()
