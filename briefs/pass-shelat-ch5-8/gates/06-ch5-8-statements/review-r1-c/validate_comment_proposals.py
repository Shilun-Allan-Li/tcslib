"""Validate all closed Gate06 minor proposals without changing tracked source."""
from pathlib import Path
import hashlib
import json
import re
import subprocess

WORK = Path('/Users/seyoonr/.codex/worktrees/ps-gate06-integration/tcslib-pass-shelat-ch2-4')
MAIN = Path('/Users/seyoonr/phd_experiments/tcslib_all_branches/tcslib-pass-shelat-ch2-4')
PREP = Path(__file__).resolve().parent
HEAD = '3f6db40e1688c4a0bb922c9575dd3bd2157a650b'


def sha(raw):
    return hashlib.sha256(raw).hexdigest()


def git(*args):
    return subprocess.check_output(['git', '-C', str(WORK), *args])


def without_comments(text):
    result = []
    i = 0
    depth = 0
    string = False
    while i < len(text):
        if depth:
            if text.startswith('/-', i):
                depth += 1
                i += 2
            elif text.startswith('-/', i):
                depth -= 1
                i += 2
            else:
                i += 1
        elif string:
            result.append(text[i])
            if text[i] == '\\' and i + 1 < len(text):
                result.append(text[i + 1])
                i += 2
            else:
                if text[i] == '"':
                    string = False
                i += 1
        elif text.startswith('/-', i):
            depth = 1
            i += 2
        elif text.startswith('--', i):
            j = text.find('\n', i)
            i = len(text) if j < 0 else j
        else:
            result.append(text[i])
            if text[i] == '"':
                string = True
            i += 1
    assert depth == 0 and not string
    return ''.join(result).encode()


def main():
    assert git('rev-parse', 'HEAD').decode().strip() == HEAD
    assert not git('status', '--porcelain').strip()
    gate = MAIN / 'briefs/pass-shelat-ch5-8/gates/06-ch5-8-statements'
    inputs = [
        (gate / 'review-r1-ad/minor-prose-corrections.patch',
         '3c5c98acb21f7e252105a1f64be04fea760d2388b60d1fd22dfa954b25c5987a'),
        (gate / 'review-r1-b/minor-prose-corrections.patch',
         '20126e560e0c9a4f8fff67026ca892a5257d7890576045909cba50ff81be76ea'),
        (PREP / 'review-cca/CCA2Scheme-comment-only.patch',
         '6d28cf9661af55905c96874123c33698464507896ae0d48e21a82f73114677e2'),
        (PREP / 'review-seqzk/seqzk-phase-normalization-comments.patch',
         '5292416d91d6c1be5b06307d130a601f2b8e0d5b58e264e9c453e37c48e3099e'),
    ]
    out = PREP / 'combined-comment-proposals-r2'
    assert not out.exists()
    out.mkdir()
    pieces = []
    paths = []
    bindings = []
    for source, digest in inputs:
        raw = source.read_bytes()
        assert sha(raw) == digest and raw.endswith(b'\n'), source
        pieces.append(raw)
        found = re.findall(r'^\+\+\+ b/(TCSlib/[^\n]+\.lean)$', raw.decode(), re.M)
        assert found and not set(found) & set(paths), source
        paths.extend(found)
        bindings.append({'path': str(source), 'sha256': digest, 'source_paths': found})
    assert len(paths) == len(set(paths)) == 13
    patch = out / 'all-minor-prose-corrections.patch'
    patch.write_bytes(b''.join(pieces))
    git('apply', '--check', str(patch))
    src = out / 'src'
    before = {}
    for path in paths:
        raw = git('show', HEAD + ':' + path)
        assert raw == (WORK / path).read_bytes()
        before[path] = raw
        dest = src / path
        dest.parent.mkdir(parents=True, exist_ok=True)
        dest.write_bytes(raw)
    directory = str(src.relative_to(WORK))
    git('apply', '--directory=' + directory, str(patch))
    rows = []
    for path in paths:
        old = before[path]
        new = (src / path).read_bytes()
        oldcode = without_comments(old.decode())
        newcode = without_comments(new.decode())
        assert oldcode == newcode, path
        assert old == (WORK / path).read_bytes(), path
        rows.append({'path': path, 'original_sha256': sha(old),
                     'proposed_sha256': sha(new),
                     'exact_noncomment_sha256': sha(oldcode),
                     'exact_noncomment_bytes_identical': True,
                     'original_lines': len(old.splitlines()),
                     'proposed_lines': len(new.splitlines())})
    assert not git('status', '--porcelain').strip()
    result = {'audited_source_head': HEAD, 'input_bindings': bindings,
              'patch_sha256': sha(patch.read_bytes()), 'files': rows,
              'file_count': 13, 'all_fifteen_minor_dispositions': True,
              'joint_git_apply_check': True, 'scratch_patch_application': True,
              'all_exact_noncomment_bytes_identical': True,
              'tracked_source_changed': False, 'native_run': False,
              'merge_clearance': False, 'validator_sha256': sha(Path(__file__).read_bytes())}
    (out / 'validation.json').write_text(json.dumps(result, indent=2) + '\n')
    print(json.dumps({key: value for key, value in result.items() if key not in ['files', 'input_bindings']}, indent=2))


if __name__ == '__main__':
    main()
