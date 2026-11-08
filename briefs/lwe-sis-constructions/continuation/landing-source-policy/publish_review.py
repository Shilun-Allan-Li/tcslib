"""Publish source-policy inputs and the checked #250 comment repair; never merge."""

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


def git(checkout, *args, capture=True):
    result = subprocess.run(['git', '-C', str(checkout), *args], capture_output=capture,
        text=True, check=True)
    return result.stdout.strip() if capture else ''


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--worker', choices=['codex'], default='codex')
    parser.add_argument('--check-only', action='store_true')
    args = parser.parse_args()
    record = json.loads((HERE / 'review-publication.json').read_text())
    publisher = Path(record['publisher_checkout'])
    assert publisher == ROOT.parent / 'tcslib-exchange-lwe-sis-publish'
    assert (publisher / '.git').is_dir()
    assert Path(git(ROOT, 'rev-parse', '--show-toplevel')) == ROOT
    assert git(ROOT, 'branch', '--show-current') == TOPIC
    assert not git(ROOT, 'status', '--porcelain'), 'Own code/records checkout must be clean.'
    assert git(ROOT, 'remote', 'get-url', '--push', '--all', 'origin') == REMOTE
    assert record['selected_worker'] == args.worker == 'codex'
    assert record['local_extraction_verified'] and record['primary_assets_verified']
    assert not git(ROOT, 'diff', '--name-only', record['publication_lean_pin'], 'HEAD', '--',
        'TCSlib', 'TCSlib.lean', 'lean-toolchain', 'lake-manifest.json',
        'blueprint/src/references/sources.json')
    assert git(ROOT, 'merge-base', '--is-ancestor', record['records_pin'], 'HEAD') == ''
    for row in record['publication_source_files']:
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
        print(f"Clean own draft/private publisher; {len(record['publication_source_files'])} code hashes, {len(record['files'])} payload hashes, {record['sections']} extracted sections and four primary assets pass. No network, push, merge or dispatch.")
        return

    def gh(*values):
        return subprocess.check_output(['gh', *values], cwd=ROOT, text=True).strip()

    pr = json.loads(gh('pr', 'view', '250', '--repo', REPO, '--json',
        'headRefName,baseRefName,state,isDraft'))
    assert pr['headRefName'] == TOPIC and pr['baseRefName'] == CENTRAL
    assert pr['state'] == 'OPEN' and pr['isDraft'], 'Inspect a closed or non-draft PR first.'
    head = git(ROOT, 'rev-parse', 'HEAD')
    git(ROOT, 'push', '--no-follow-tags', 'origin', head + ':refs/heads/' + TOPIC, capture=False)
    gh('pr', 'edit', '250', '--repo', REPO, '--body-file', str(HERE / 'PR_BODY.md'))
    git(publisher, '-c', 'rebase.autoStash=false', 'pull', '--rebase', 'origin', EXCHANGE, capture=False)
    check_exchange()
    pending = git(publisher, 'diff', '--name-only', '--no-renames', 'FETCH_HEAD', 'HEAD').splitlines()
    assert all(p.startswith('lwe-sis-constructions/') for p in pending), pending
    git(publisher, 'push', '--no-follow-tags', 'origin', 'HEAD:refs/heads/' + EXCHANGE, capture=False)
    pin = git(publisher, 'rev-parse', 'HEAD')
    print('\n#250 updated with the checked comment repair/intake; source-policy exchange: ' + pin)
    print('\nPaste into a fresh Codex source-validator chat:\n')
    print('Validate and prepare source-policy artifacts for the earlier LWE/SIS stack in ' + REPO + '.')
    print('Read ' + EXCHANGE + ' at exact commit ' + pin + '.')
    print('Read README.md, lwe-sis-constructions/README.md, then ' + record['job_path'] + '/README.md.')
    print('Verify SHA256SUMS, PRIMARY-SOURCES.json and both ordered revision-qualified bundle indexes; follow first-section JOB.md.')
    print('Lean source to match: ' + record['lean_source_to_match'] + '; bundled records: ' + record['records_pin'] + '.')
    print('Scope: 161 declarations/20 modules for PRs #236–#239; Pei16 and Wu24, 196 pages. Later #250/PW10 source scope is deferred.')
    print('Bundle SHA-256: ' + record['bundle_sha256'] + '; sections: ' + str(record['sections']) + '; bytes: ' + str(record['bundle_bytes']) + '.')
    print('Use the four frozen PDF/raw inputs in the job folder. Return a Markdown report in chat plus a ZIP of the proposed validated reference pairs, page checks and existing-format matching records.')
    print('One agent; no helpers, paid/model subprocesses, broad pipeline, Lean/code edit, shared registry/blueprint/dataset mutation, worker dispatch, push, approval or merge.')
    print('Keep matches proposed and unapproved; disclose incomplete coverage and ambiguities. No input ZIP is needed.')
    print('\nOnly the own #250 feature branch and owned source-policy inputs were pushed. The user dispatches; no merge was performed.')


if __name__ == '__main__':
    try:
        main()
    except subprocess.CalledProcessError as error:
        raise SystemExit('Publication stopped after exit ' + str(error.returncode)
            + '; inspect the failure and any completed step. No force, stash, reset, merge or dispatch was attempted.') from None
