"""Publish this own draft PR and its Codex audit inputs; never merge or dispatch.

Adapted from this campaign's earlier client helpers. --check-only is local/read-only.
Actual publication uses the client's Git/gh credentials and prints a pinned kickoff.
"""

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
TITLE = 'State LWE/SIS samplers, Regev PKE, generators and cryptographic trapdoors'
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
    publisher = Path(record['publisher_checkout'])
    assert publisher == ROOT.parent / 'tcslib-exchange-lwe-sis-publish'
    assert (publisher / '.git').is_dir(), 'Use the separate private publisher clone.'
    assert Path(git(ROOT, 'rev-parse', '--show-toplevel')) == ROOT
    assert git(ROOT, 'branch', '--show-current') == TOPIC
    assert not git(ROOT, 'status', '--porcelain'), 'Own PR checkout must be clean.'
    assert git(ROOT, 'remote', 'get-url', '--push', '--all', 'origin') == REMOTE
    assert record['source_pin'] == SOURCE
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
        print(f"Clean own draft and private publisher; {len(record['source_files'])} frozen source hashes, {len(record['files'])} payload hashes and {record['sections']} extracted sections pass. Codex selected; no network, push, merge or dispatch.")
        return

    def gh(*values):
        return subprocess.check_output(['gh', *values], cwd=ROOT, text=True).strip()

    existing = json.loads(gh('pr', 'list', '--repo', REPO, '--head', TOPIC,
        '--state', 'all', '--json', 'number,headRefName,baseRefName,state,isDraft,url'))
    assert len(existing) <= 1, 'Inspect multiple PRs for this exact topic branch.'
    if existing:
        pr = existing[0]
        assert pr['headRefName'] == TOPIC and pr['baseRefName'] == CENTRAL
        assert pr['state'] == 'OPEN' and pr['isDraft'], 'Inspect a closed or non-draft PR first.'
    head = git(ROOT, 'rev-parse', 'HEAD')
    git(ROOT, 'push', '--no-follow-tags', 'origin', head + ':refs/heads/' + TOPIC, capture=False)
    if existing:
        gh('pr', 'edit', str(pr['number']), '--repo', REPO, '--title', TITLE,
           '--body-file', str(HERE / 'PR_BODY.md'))
    else:
        url = gh('pr', 'create', '--draft', '--repo', REPO, '--head', TOPIC,
            '--base', CENTRAL, '--title', TITLE, '--body-file', str(HERE / 'PR_BODY.md'))
        pr = json.loads(gh('pr', 'view', url, '--repo', REPO, '--json',
            'number,url,headRefName,baseRefName,state,isDraft'))
        assert pr['headRefName'] == TOPIC and pr['baseRefName'] == CENTRAL
        assert pr['state'] == 'OPEN' and pr['isDraft']

    # This is our sparse publisher, never the shared exchange checkout. Rebase
    # before each push; disable automatic stashing. A conflict stops publication.
    git(publisher, '-c', 'rebase.autoStash=false', 'pull', '--rebase', 'origin', EXCHANGE,
        capture=False)
    check_exchange()
    pending = git(publisher, 'diff', '--name-only', '--no-renames', 'FETCH_HEAD', 'HEAD').splitlines()
    assert all(p.startswith('lwe-sis-constructions/') for p in pending), pending
    git(publisher, 'push', '--no-follow-tags', 'origin', 'HEAD:refs/heads/' + EXCHANGE,
        capture=False)
    pin = git(publisher, 'rev-parse', 'HEAD')
    print('\nDraft PR #' + str(pr['number']) + ': ' + pr['url'])
    print('Exchange commit: ' + pin)
    print('\nPaste into a fresh Codex auditor chat:\n')
    print('Audit the LWE/SIS combined construction statements, round 1, in ' + REPO + '.')
    print('Read ' + EXCHANGE + ' at exact commit ' + pin + '.')
    print('Read README.md, lwe-sis-constructions/README.md, then ' + record['gate_path'] + '/README.md.')
    print('Verify SHA256SUMS and both ordered revision-qualified BUNDLE-FILES indexes; follow the first-section pack.')
    print('Frozen Lean/root: ' + SOURCE + '; bundled records: ' + record['records_pin'] + '.')
    print('Bundle SHA-256: ' + record['bundle_sha256'] + '; sections: ' + str(record['sections']) + '; bytes: ' + str(record['bundle_bytes']) + '.')
    print('Review all 19 mathematical modules, 220 source declarations, 101 admitted obligations/sketches, 62 closed source readers, 40 generated readers, 13 compiler auxiliaries, all 575 owned constants and 48 backing contracts.')
    print('Inspect the two unapplied shared reader/catalogue proposals and retain source-policy and consumer limits.')
    print('PR #' + str(pr['number']) + ' targets ' + CENTRAL + '. The audited dependencies are #236/#237/#238/#239.')
    print('Return lwe-sis-constructions-statements-findings.md as Markdown in chat. No ZIP is needed.')
    print('Do not edit, fill, dispatch workers, push or merge.')
    print('\nOnly the own draft branch and owned exchange inputs were pushed. The user dispatches the audit. No merge was performed.')


if __name__ == '__main__':
    try:
        main()
    except subprocess.CalledProcessError as error:
        raise SystemExit('Publication stopped after exit ' + str(error.returncode)
                         + '; inspect the error and any completed publication step. No force, stash, reset or merge was attempted.') from None
