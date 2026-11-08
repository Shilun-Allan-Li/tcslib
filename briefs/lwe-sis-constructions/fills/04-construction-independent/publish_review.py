"""Update only draft PR #250 and owned Codex proof-review inputs; never merge."""

import argparse
import hashlib
import json
from pathlib import Path
import subprocess


HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[3]
REPO = 'Shilun-Allan-Li/tcslib'
REMOTE = 'https://github.com/' + REPO + '.git'
TOPIC = 'cryptography/lwe-sis-construction-statements'
CENTRAL = 'cryptography/lwe-sis-constructions'
EXCHANGE = 'exchange/pass-shelat-ch5-8'
SOURCE = (HERE / 'evidence/source-pin.txt').read_text().strip()


def git(checkout, *args, capture=True):
    result = subprocess.run(['git', '-C', str(checkout), *args],
        capture_output=capture, text=True, check=True)
    return result.stdout.strip() if capture else ''


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--worker', choices=['codex'], default='codex')
    parser.add_argument('--check-only', action='store_true')
    args = parser.parse_args()
    record = json.loads((HERE / 'review-publication.json').read_text())
    summary = json.loads((HERE / 'evidence/summary.json').read_text())
    publisher = Path(record['publisher_checkout'])
    assert publisher == ROOT.parent / 'tcslib-exchange-lwe-sis-publish'
    assert (publisher / '.git').is_dir()
    assert Path(git(ROOT, 'rev-parse', '--show-toplevel')) == ROOT
    assert git(ROOT, 'branch', '--show-current') == TOPIC
    assert not git(ROOT, 'status', '--porcelain'), 'Own checkout must be clean.'
    assert git(ROOT, 'remote', 'get-url', '--push', '--all', 'origin') == REMOTE
    assert record['source_pin'] == SOURCE == summary['source_pin']
    assert summary['filled_proofs'] == 31 and summary['selected_filled_targets_with_sorryAx'] == 0
    assert record['selected_worker'] == args.worker == 'codex'
    assert record['reviewer_selected'] and record['local_extraction_verified']
    assert not git(ROOT, 'diff', '--name-only', SOURCE, 'HEAD', '--',
        'TCSlib', 'TCSlib.lean', 'lean-toolchain', 'lake-manifest.json')
    assert git(ROOT, 'merge-base', '--is-ancestor', record['records_pin'], 'HEAD') == ''
    for row in record['source_files']:
        assert hashlib.sha256((ROOT / row['path']).read_bytes()).hexdigest() == row['sha256'], row['path']

    def check_exchange():
        assert git(publisher, 'branch', '--show-current') == record['publisher_branch']
        assert not git(publisher, 'status', '--porcelain'), 'Private publisher must be clean.'
        assert git(publisher, 'remote', 'get-url', '--push', '--all', 'origin') == REMOTE
        for row in record['files']:
            assert row['path'].startswith('lwe-sis-constructions/')
            assert hashlib.sha256((publisher / row['path']).read_bytes()).hexdigest() == row['sha256'], row['path']

    check_exchange()
    if args.check_only:
        print(f"Clean own draft/private publisher; {len(record['source_files'])} source hashes, {len(record['files'])} payload hashes, {record['sections']} extracted sections. Codex selected; no network, push, merge or dispatch.")
        return

    def gh(*values):
        return subprocess.check_output(['gh', *values], cwd=ROOT, text=True).strip()

    pr = json.loads(gh('pr', 'view', '250', '--repo', REPO, '--json',
        'headRefName,baseRefName,state,isDraft'))
    assert pr['headRefName'] == TOPIC and pr['baseRefName'] == CENTRAL
    assert pr['state'] == 'OPEN' and pr['isDraft'], 'Inspect a closed or non-draft PR first.'
    head = git(ROOT, 'rev-parse', 'HEAD')
    git(ROOT, 'push', '--no-follow-tags', 'origin', head + ':refs/heads/' + TOPIC, capture=False)
    gh('pr', 'edit', '250', '--repo', REPO,
        '--title', 'Prove independent LWE sampling, generators and Regev correctness',
        '--body-file', str(HERE / 'PR_BODY.md'))
    git(publisher, '-c', 'rebase.autoStash=false', 'pull', '--rebase', 'origin', EXCHANGE, capture=False)
    check_exchange()
    pending = git(publisher, 'diff', '--name-only', '--no-renames', 'FETCH_HEAD', 'HEAD').splitlines()
    assert all(p.startswith('lwe-sis-constructions/') for p in pending), pending
    git(publisher, 'push', '--no-follow-tags', 'origin', 'HEAD:refs/heads/' + EXCHANGE, capture=False)
    pin = git(publisher, 'rev-parse', 'HEAD')
    print('\nPR #250 updated: https://github.com/' + REPO + '/pull/250')
    print('Exchange commit: ' + pin)
    print('\nPaste into a fresh Codex auditor chat:\n')
    print('Audit the independent LWE/SIS construction proof fill, round 1, in ' + REPO + '.')
    print('Read ' + EXCHANGE + ' at exact commit ' + pin + '.')
    print('Read README.md, lwe-sis-constructions/README.md, then ' + record['gate_path'] + '/README.md.')
    print('Verify SHA256SUMS and both ordered revision-qualified indexes; follow the first-section pack.')
    print('Statement freeze: ' + record['statement_freeze'] + '; passed-gate/doc-repair baseline: ' + record['proof_baseline'] + '.')
    print('Filled Lean/root: ' + SOURCE + '; bundled records: ' + record['records_pin'] + '.')
    print('Bundle SHA-256: ' + record['bundle_sha256'] + '; sections: ' + str(record['sections']) + '; bytes: ' + str(record['bundle_bytes']) + '.')
    print('Review all 31 filled proofs in seven modules, all 220 unchanged source declarations, 62 earlier closed source readers, the complete ' + str(summary['owned_constants']) + '-constant inventory and 48 backing contracts. Seventy owned admissions remain outside this proof gate.')
    print('Preserve the statement audit N01–N04 holds and verify its comment-only F01 repair. PR #250 targets ' + CENTRAL + '.')
    print('Return lwe-sis-independent-proofs-findings.md as Markdown in chat. No ZIP is needed.')
    print('Do not edit, fill, dispatch workers, push or merge.')
    print('\nOnly the own draft and owned exchange inputs were pushed. The user dispatches. No merge was performed.')


if __name__ == '__main__':
    try:
        main()
    except subprocess.CalledProcessError as error:
        raise SystemExit('Publication stopped after exit ' + str(error.returncode)
            + '; inspect the failure and any completed step. No force, stash, reset, merge or dispatch was attempted.') from None
