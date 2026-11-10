"""Publish the checked Regev proof head and its owned exchange audit packet."""
import argparse
from hashlib import sha256
import json
from pathlib import Path
import subprocess


HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[3]
PUBLISHER = ROOT.parent / 'tcslib-exchange-lwe-sis-publish'
TOPIC = 'cryptography/lwe-sis-construction-statements'
CENTRAL = 'cryptography/lwe-sis-constructions'
EXCHANGE = 'exchange/pass-shelat-ch5-8'
REPO = 'Shilun-Allan-Li/tcslib'
REMOTE = f'https://github.com/{REPO}.git'
GATE = 'lwe-sis-constructions/outbox/gates/10-regev-hybrids-proofs-r1'
NAMESPACE_README = 'lwe-sis-constructions/README.md'


def git(checkout, *args, capture=True):
    result = subprocess.run(['git', '-C', str(checkout), *args],
                            text=True, check=True, capture_output=capture)
    return result.stdout.strip() if capture else ''


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--check-only', action='store_true')
    args = parser.parse_args()
    receipt = json.loads((HERE / 'review-publication.json').read_bytes())
    freeze = json.loads((HERE / 'evidence/freeze.json').read_bytes())
    assert receipt['gate_path'] == GATE
    assert receipt['worker'] == 'codex' and receipt['local_extraction_verified']
    assert git(ROOT, 'branch', '--show-current') == TOPIC
    assert git(ROOT, 'remote', 'get-url', '--push', '--all', 'origin') == REMOTE
    assert not git(ROOT, 'status', '--porcelain'), 'The #250 worktree must be clean.'
    source = receipt['source_pin']
    assert not git(ROOT, 'diff', '--name-only', source, 'HEAD', '--', 'TCSlib', 'TCSlib.lean',
                   'lean-toolchain', 'lake-manifest.json', 'lakefile.lean')
    assert git(ROOT, 'merge-base', '--is-ancestor', receipt['records_pin'], 'HEAD') == ''
    for entry in freeze['source_files']:
        assert sha256((ROOT / entry['path']).read_bytes()).hexdigest() == entry['sha256'], entry['path']

    def check_payload():
        assert git(PUBLISHER, 'branch', '--show-current') == receipt['publisher_branch']
        assert git(PUBLISHER, 'remote', 'get-url', '--push', '--all', 'origin') == REMOTE
        assert not git(PUBLISHER, 'status', '--porcelain'), 'The private publisher must be clean.'
        for entry in receipt['files']:
            path = entry['path']
            assert path == NAMESPACE_README or path.startswith(GATE + '/')
            assert sha256((PUBLISHER / path).read_bytes()).hexdigest() == entry['sha256'], path

    check_payload()
    if args.check_only:
        print(f"Verified {len(freeze['source_files'])} frozen source hashes and {len(receipt['files'])} owned payload hashes.")
        return

    pr = json.loads(subprocess.check_output(['gh', 'pr', 'view', '250', '--repo', REPO, '--json',
        'headRefName,baseRefName,state,isDraft'], text=True, cwd=ROOT))
    assert pr == {'headRefName': TOPIC, 'baseRefName': CENTRAL, 'state': 'OPEN', 'isDraft': True}, pr
    head = git(ROOT, 'rev-parse', 'HEAD')
    git(ROOT, 'push', '--no-follow-tags', 'origin', head + ':refs/heads/' + TOPIC, capture=False)
    git(PUBLISHER, '-c', 'rebase.autoStash=false', 'pull', '--rebase', '--no-tags', 'origin', EXCHANGE, capture=False)
    check_payload()
    allowed = {entry['path'] for entry in receipt['files']}
    pending = set(git(PUBLISHER, 'diff', '--name-only', '--no-renames', 'FETCH_HEAD', 'HEAD').splitlines())
    assert pending <= allowed, pending - allowed
    git(PUBLISHER, 'push', '--no-follow-tags', 'origin', 'HEAD:refs/heads/' + EXCHANGE, capture=False)
    exchange = git(PUBLISHER, 'rev-parse', 'HEAD')
    print(f'Published PR #250 head {head} and exchange commit {exchange}.\n')
    print('Paste into a fresh Codex auditor chat.\n')
    print(f'Audit the six Regev PKE hybrid support proofs in {REPO}, draft PR #250.')
    print(f'Read {EXCHANGE} at exact commit {exchange}.')
    print(f'Read README.md, {NAMESPACE_README}, then {GATE}/README.md.')
    print('Verify SHA256SUMS and both ordered revision-qualified indexes. Follow the first-section pack.')
    print(f"Filled Lean/root {source}. Bundled records {receipt['records_pin']}.")
    print(f"Bundle SHA-256 {receipt['bundle_sha256']}. {receipt['sections']} sections, {receipt['bundle_bytes']} bytes.")
    print('Return lwe-sis-regev-hybrids-proofs-findings.md as Markdown in chat.')


if __name__ == '__main__':
    main()
