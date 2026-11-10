"""Verify a proposed source-policy delivery; never approve or integrate its data."""

import argparse
from collections import Counter
import hashlib
import json
from pathlib import Path, PurePosixPath
import re
import stat
import subprocess
import sys
from zipfile import ZipFile


HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[4]
SCOPE_DIR = HERE.parent
CODE = 'ec72ed773a690c17ac253707350935cc9e0acb34'
RECORDS = 'e88f9ecc36033e468f8c345f2d1088b59ba50e08'
EXCHANGE = 'a4e19bd3cf029b9bf5fb2e53989ddc0d61006ac1'
PUBLISHER = ROOT.parent / 'tcslib-exchange-lwe-sis-publish'
JOB_PATH = 'lwe-sis-constructions/outbox/source-policy/01-earlier-stack-r1'
DELIVERY = 'lwe-sis-earlier-stack-source-policy-r1'


def digest(data):
    return hashlib.sha256(data).hexdigest()


def git(checkout, *args):
    return subprocess.check_output(['git', '-C', str(checkout), *args])


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--zip', type=Path, required=True)
    parser.add_argument('--extracted', type=Path, required=True)
    parser.add_argument('--output', type=Path, required=True)
    args = parser.parse_args()
    with ZipFile(args.zip) as archive:
        entries = archive.infolist()
        assert len({x.filename for x in entries}) == len(entries) == 59
        assert sum(x.file_size for x in entries) < 100_000_000
        for x in entries:
            p = PurePosixPath(x.filename)
            assert not p.is_absolute() and '..' not in p.parts
            assert '\\' not in x.filename and not stat.S_ISLNK(x.external_attr >> 16)
        assert archive.testzip() is None
        for x in entries:
            assert args.extracted.joinpath(*PurePosixPath(x.filename).parts).read_bytes() == archive.read(x)
    base = args.extracted / DELIVERY
    files = {str(p.relative_to(base)) for p in base.rglob('*') if p.is_file()}
    checksums = {}
    for line in (base / 'SHA256SUMS').read_text().splitlines():
        h, name = line.split('  ', 1)
        assert name not in checksums and re.fullmatch('[0-9a-f]{64}', h)
        assert digest((base / name).read_bytes()) == h, name
        checksums[name] = h
    assert set(checksums) == files - {'SHA256SUMS'}
    manifest = json.loads((base / 'MANIFEST.json').read_text())
    assert manifest['exchange_commit'] == EXCHANGE
    assert manifest['lean_source_pin'] == CODE and manifest['records_pin'] == RECORDS
    assert manifest['status'] == 'PARTIAL_PROPOSED_UNAPPROVED'
    for key in ['approved_matching', 'shared_registry_applied', 'source_policy_closed',
                'complete_reference_validation', 'merge_approval']:
        assert manifest[key] is False
    listed = manifest['files']
    assert len({x['path'] for x in listed}) == len(listed)
    assert {x['path'] for x in listed} == files - {'MANIFEST.json', 'SHA256SUMS'}
    for row in listed:
        data = (base / row['path']).read_bytes()
        assert len(data) == row['bytes'] and digest(data) == row['sha256'], row['path']

    for p in (base / 'evidence/frozen-packet').iterdir():
        assert p.read_bytes() == git(PUBLISHER, 'show', EXCHANGE + ':' + JOB_PATH + '/' + p.name)
    input_checksum_count = 0
    for line in (base / 'evidence/frozen-packet/SHA256SUMS').read_text().splitlines():
        h, name = line.split('  ', 1)
        assert digest(git(PUBLISHER, 'show', EXCHANGE + ':' + JOB_PATH + '/' + name)) == h
        input_checksum_count += 1
    assert input_checksum_count == 10
    scope_bytes = git(ROOT, 'show', RECORDS + ':' + str(SCOPE_DIR.relative_to(ROOT) / 'scope.json'))
    assert (base / 'evidence/scope.json').read_bytes() == scope_bytes
    assert (base / 'evidence/JOB.md').read_bytes() == git(ROOT, 'show', RECORDS + ':' + str(SCOPE_DIR.relative_to(ROOT) / 'JOB.md'))
    scope = json.loads(scope_bytes)
    names, modules, source = [], {}, {}
    for mod in scope['modules']:
        data = git(ROOT, 'show', CODE + ':' + mod['path'])
        assert len(data) == mod['bytes'] and digest(data) == mod['sha256']
        for row in mod['declarations']:
            names.append(row['name']); modules[row['name']] = row['source_module']
            source[row['name']] = data.decode()
    assert len(names) == len(set(names)) == 161 and len(scope['modules']) == 20
    frozen = json.loads((base / 'evidence/frozen-packet/BUNDLE-FILES.json').read_text())
    lines = (base / 'evidence/frozen-packet/BUNDLE-FILES.txt').read_text().splitlines()
    assert len(frozen) == len(lines) == 191
    for row, line in zip(frozen, lines):
        assert line == f"{row['revision']}:{row['path']}\t{row['bytes']}\t{row['sha256']}"
        data = git(ROOT, 'show', row['revision'] + ':' + row['path'])
        assert len(data) == row['bytes'] and digest(data) == row['sha256']
    primary = json.loads((SCOPE_DIR / 'primary-inputs.json').read_text())
    for row in primary:
        data = (base / 'references' / Path(row['relative_payload_path']).name).read_bytes()
        assert len(data) == row['bytes'] and digest(data) == row['sha256']
    for name in ['proposed-source-registry.patch', 'registry-proposal.json']:
        path = 'briefs/lwe-sis-constructions/continuation/source-ingestion/' + name
        assert (base / 'proposals' / name).read_bytes() == git(ROOT, 'show', RECORDS + ':' + path)

    for path in ['proofmatch/models.py', 'proofmatch/document.py']:
        assert (ROOT / path).read_bytes() == git(ROOT, 'show', CODE + ':' + path)
    sys.path.insert(0, str(ROOT))
    from proofmatch.document import parse_validated_markdown
    from proofmatch.models import (Candidate, ComparisonVerdict, DocumentAmbiguity,
        DocumentIndex, RelevanceDecision, _from_mapping, load_typed)

    totals = Counter(); documents = {}
    profiles = [('peikert2016-lattice-survey', 90, {20, 21, 24}),
                ('wu2024-topics-cryptography', 106, {39, 65, 75, 82, 83, 85, 91})]
    for doc, pages, repaired in profiles:
        pdf_hash = digest((base / 'references' / (doc + '.pdf')).read_bytes())
        raw = (base / 'references' / (doc + '.raw.md')).read_text()
        assert pdf_hash in raw
        assert list(map(int, re.findall(r'<!-- pdf-page: (\d+) -->', raw))) == list(range(1, pages + 1))
        idx = load_typed(base / 'validation' / doc / 'index.json', DocumentIndex)
        parsed = parse_validated_markdown(base / 'references' / (doc + '.md'))
        assert idx.source_fingerprint == parsed.source_fingerprint == pdf_hash
        assert idx.blocks == parsed.blocks
        assert len({b.block_id for b in idx.blocks}) == len(idx.blocks) == pages
        assert [b.page for b in idx.blocks] == list(range(1, pages + 1))
        for b in idx.blocks:
            assert b.block_id == f'pdf-{pdf_hash[:12]}-p{b.page:03d}-b{b.sequence:03d}'
            assert b.sequence == 1 and b.markdown.strip() and 0 <= b.confidence <= 1
        blocks = {b.block_id: b for b in idx.blocks}
        review = json.loads((base / 'validation' / doc / 'page-review.json').read_text())
        assert [x['page'] for x in review] == list(range(1, pages + 1))
        assert {x['page'] for x in review if x['transcription_validated']} == repaired
        for x in review:
            assert set(x['block_ids']) <= blocks.keys()
            if x['render_reviewed']:
                assert x['rendered'] and x['render_path']
            if x['render_path']:
                assert digest((base / x['render_path']).read_bytes()) == x['render_sha256']
        ambiguity = tuple(_from_mapping(x, DocumentAmbiguity, 'DocumentAmbiguity')
            for x in json.loads((base / 'validation' / doc / 'ambiguities.json').read_text()))
        assert ambiguity == idx.ambiguities
        assert all(x.block_id in blocks for x in ambiguity)
        for relative in re.findall(r'!\[[^\]]*\]\(([^)]+)\)', (base / 'references' / (doc + '.md')).read_text()):
            assert (base / 'references' / relative).is_file(), relative
        data = {}
        for filename, cls in [('relevance.jsonl', RelevanceDecision),
                              ('comparisons.jsonl', ComparisonVerdict), ('candidates.jsonl', Candidate)]:
            rows = [_from_mapping(json.loads(line), cls, cls.__name__) for line in
                (base / 'matching' / doc / filename).read_text().splitlines()]
            assert len({x.lean_name for x in rows}) == len(rows)
            if filename != 'candidates.jsonl': assert [x.lean_name for x in rows] == names
            for x in rows:
                assert x.lean_name in modules and set(x.document_blocks) <= blocks.keys()
                if isinstance(x, Candidate):
                    assert x.source_module == modules[x.lean_name]
                    assert x.formal_statement in source[x.lean_name]
                    assert x.proof in source[x.lean_name]
                    assert x.document_blocks
                    for anchor in x.document_blocks:
                        page = blocks[anchor].page
                        assert page in repaired and review[page - 1]['render_reviewed']
            data[filename] = rows
            totals['typed_jsonl_rows'] += len(rows)
        documents[doc] = dict(pages=pages, repaired_pages=sorted(repaired),
            unrepaired_pages=pages - len(repaired),
            render_reviewed_pages=[x['page'] for x in review if x['render_reviewed']],
            rendered_without_retained_image=[x['page'] for x in review if x['rendered'] and not x['render_path']],
            candidates=len(data['candidates.jsonl']),
            verdicts=dict(Counter(x.verdict for x in data['comparisons.jsonl'])),
            unresolved_ambiguities=sum(not x.resolved for x in ambiguity))
        totals['candidates'] += len(data['candidates.jsonl'])
    dispositions = json.loads((base / 'matching/dispositions.json').read_text())
    assert [x['lean_name'] for x in dispositions] == names
    assert all(x['approved'] is False for x in dispositions)
    kinds = dict(Counter(x['category'] for x in dispositions))
    assert kinds == {'implementation_or_context_only': 124, 'disclosed_adaptation': 31, 'source_result': 6}
    for x in json.loads((base / 'evidence/rounding-boundaries.json').read_text()):
        q, e = x['modulus'], x['integer_error']
        point = q // 2; residue = (point + e) % q
        dist = lambda a, b: min((a-b) % q, (b-a) % q)
        assert x['codepoint'] == point and x['received_residue'] == residue
        assert x['distance_to_false'] == dist(residue, 0)
        assert x['distance_to_true'] == dist(residue, point)
        assert x['decoded'] == int(dist(residue, point) < dist(residue, 0))
        assert x['source_strict_real_quarter_bound_holds'] == (4 * abs(e) < q)
        assert x['formal_strict_floor_separation_holds'] == (2 * abs(e) < q // 2)
    report = dict(status='VERIFIED_PARTIAL_DELIVERY', zip_bytes=args.zip.stat().st_size,
        zip_sha256=digest(args.zip.read_bytes()), archive_members=len(files),
        checksum_entries=len(checksums), manifest_file_entries=len(listed),
        original_input_checksum_entries=input_checksum_count,
        frozen_git_blobs_verified=len(frozen), exact_scope_names=len(names),
        primary_assets_verified=len(primary), documents=documents,
        typed_jsonl_rows=totals['typed_jsonl_rows'], candidates=totals['candidates'],
        dispositions=kinds, complete_reference_validation=False, matching_approved=False,
        source_policy_closed=False, merge_approved=False, lean_executions=0,
        paid_model_calls=0, worker_dispatches=0)
    args.output.write_text(json.dumps(report, indent=2) + '\n')
    print(json.dumps(report, indent=2))


if __name__ == '__main__':
    main()
