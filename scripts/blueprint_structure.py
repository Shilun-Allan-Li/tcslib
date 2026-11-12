"""Shared publication structure, heading-only normalization, and preservation audit.

Module files stay in chapter/; generated wrappers live in the reserved textbook/ tree.
Only standalone presentation headings are editable. Everything between them is hashed
byte-for-byte, including prose, declaration order, labels and dependency metadata.
"""
from __future__ import annotations

import hashlib
import json
import re
from collections import Counter
from pathlib import Path

INPUT_RE = re.compile(r"\\input\{chapter/([^}]+)\}")
HEAD_RE = re.compile(r"(?m)^\\(chapter|section|subsection|subsubsection|paragraph)(\*?)(?:\[[^\]\n]*\])?\{")
ENTRY_RE = re.compile(r"\\begin\{(definition|theorem|lemma|proposition|corollary|remark|example|sublemma)\}.*?\\end\{\1\}", re.S)


def uncomment(text: str) -> str:
    return re.sub(r"(?m)(?<!\\)%[^\n]*", "", text)


def headings(text: str):
    """Balanced heading spans (including nested TeX groups); reject malformed input."""
    for match in HEAD_RE.finditer(text):
        depth, end = 1, match.end()
        while end < len(text) and depth:
            if text[end] in '{}' and (end == 0 or text[end - 1] != '\\'):
                depth += 1 if text[end] == '{' else -1
            end += 1
        if depth:
            raise ValueError(f"Unbalanced {match.group(1)} heading at offset {match.start()}")
        yield match.start(), end, match.group(1), match.group(2), text[match.end():end - 1]


def without_headings(text: str) -> str:
    for start, end, *_ in reversed(list(headings(text))):
        text = text[:start] + text[end:]
    return text


def digest(text: str) -> str:
    return hashlib.sha256(text.encode('utf-8')).hexdigest()


def module_title(rel: str) -> str:
    pieces = rel.removesuffix('.tex').split('/')[1:]
    words = [re.sub(r'(?<=[a-z0-9])(?=[A-Z])', ' ', p) for p in pieces]
    if words[-1] == 'Basic':
        words[-1] = 'Foundations'
    return ' --- '.join(words)


def normalize_headings(text: str, rel: str) -> str:
    """One module section, then subsections, subsubsections and paragraphs.

    Generic navigation headings acquire the module context. Introductory prose is
    untouched; formerly generic Overview/Declarations headings are unnumbered.
    Already normalized sources are a no-op.
    """
    hs = list(headings(text))
    if not any(h[2] == 'chapter' for h in hs):
        return text
    title = module_title(rel)
    levels = {'chapter': 'section', 'section': 'subsection',
              'subsection': 'subsubsection', 'subsubsection': 'paragraph', 'paragraph': 'paragraph'}
    for start, end, level, star, old in reversed(hs):
        new_title = title if level == 'chapter' else old
        if old in {'Overview', 'Declarations', 'Additional declarations', 'Basic'}:
            new_title = f"{title}: " + {'Overview': 'Introduction', 'Declarations': 'Results',
                                        'Additional declarations': 'Further results', 'Basic': 'Foundations'}[old]
            star = '*'
        text = text[:start] + f"\\{levels[level]}{star}{{{new_title}}}" + text[end:]
    return text


def resolve_inputs(root: Path, entry: str = 'main.tex') -> dict:
    sequence, missing, repeated, cycles = [], [], [], []
    def walk(rel: str, stack: tuple[str, ...]):
        if rel in stack:
            cycles.append(list(stack + (rel,)))
            return
        path = root / rel
        if not path.is_file():
            missing.append(rel)
            return
        if rel in sequence:
            repeated.append(rel)
        sequence.append(rel)
        for child in INPUT_RE.findall(uncomment(path.read_text())):
            child = child if child.endswith('.tex') else child + '.tex'
            if Path(child).is_absolute() or '..' in Path(child).parts:
                raise ValueError(f'Unsafe input path: {child}')
            walk(child, stack + (rel,))
    walk(entry, ())
    return dict(sequence=sequence[1:], missing=missing, repeated=repeated, cycles=cycles)


def file_record(text: str) -> dict:
    entries = ENTRY_RE.findall(text)
    return {'sha256': digest(text), 'payload_sha256': digest(without_headings(text)),
            'headings': dict(Counter(h[2] for h in headings(text))),
            'declarations': len(entries),
            'entry_hashes': dict(Counter(digest(m.group()) for m in ENTRY_RE.finditer(text))),
            'lean_bindings': len(re.findall(r'(?m)^\s*\\lean\{', text))}


def snapshot(root: Path) -> dict:
    publication = resolve_inputs(root)
    files = {rel: file_record((root / rel).read_text()) for rel in publication['sequence']
             if not rel.startswith('textbook/')}
    return {'schema_version': 1, 'publication': publication, 'files': files}


def verify_snapshot(root: Path, baseline: dict) -> dict:
    current = snapshot(root)
    before, after = baseline['files'], current['files']
    errors = []
    if before.keys() != after.keys():
        errors.append(f"Published modules changed: removed={sorted(before.keys()-after.keys())}, added={sorted(after.keys()-before.keys())}")
    for rel in before.keys() & after.keys():
        for key in ('payload_sha256', 'entry_hashes', 'declarations', 'lean_bindings'):
            if before[rel][key] != after[rel][key]:
                errors.append(f'{rel}: changed {key}')
    for key in ('missing', 'repeated', 'cycles'):
        if current['publication'][key]:
            errors.append(f"Publication {key}: {current['publication'][key]}")
    if errors:
        raise ValueError('\n'.join(errors))
    return {'modules': len(after), 'declarations': sum(r['declarations'] for r in after.values()),
            'heading_only': True, 'publication_exactly_once': True}
