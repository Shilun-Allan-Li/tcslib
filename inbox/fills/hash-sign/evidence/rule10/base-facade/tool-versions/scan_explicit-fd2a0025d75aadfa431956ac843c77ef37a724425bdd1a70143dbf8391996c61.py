#!/usr/bin/env python3
"""Own continuation-list inventory and frozen primary-evidence reconciliation; no native."""
from pathlib import Path
from collections import Counter, defaultdict, deque
import ast
import bisect
import hashlib
import json
import re
import subprocess

ROOT = Path('/Users/seyoonr/.codex/worktrees/ps-gate06-integration/tcslib-pass-shelat-ch2-4')
OUT = Path(__file__).resolve().parent
R = ROOT / '.lake/ps-maintainer/gate06/repairs'
PRIOR = '3f6db40e1688c4a0bb922c9575dd3bd2157a650b'
BASE = '067c5d8d6dd436e62681d7dc607984c705dc80a2'
HEAD = 'a495f3953afff46ad5dec2d29ac8a7f55bd8ae37'
INPUTS = {}


def need(ok, why):
    if not ok: raise RuntimeError(why)
def sha(raw): return hashlib.sha256(raw).hexdigest()
def read(path):
    raw = path.read_bytes(); INPUTS[str(path)] = {'sha256': sha(raw), 'bytes': len(raw)}; return raw
def load(path): return json.loads(read(path))
def save(name, value):
    raw = value if isinstance(value, bytes) else (json.dumps(value, indent=2, ensure_ascii=False) + '\n').encode()
    with (OUT / name).open('xb') as handle: handle.write(raw)


def blank(src):
    """Own literal/comment masker; keeps every line and character offset."""
    out = list(src); i = 0
    def hide(a, b):
        for k in range(a, b):
            if out[k] != '\n': out[k] = ' '
    while i < len(src):
        if src.startswith('--', i):
            end = src.find('\n', i); end = len(src) if end < 0 else end
            hide(i, end); i = end
        elif src.startswith('/-', i):
            end = i + 2; depth = 1
            while depth:
                need(end < len(src), 'unterminated comment')
                if src.startswith('/-', end): depth += 1; end += 2
                elif src.startswith('-/', end): depth -= 1; end += 2
                else: end += 1
            hide(i, end); i = end
        elif src[i] == '«':
            end = src.find('»', i + 1); need(end >= 0, 'unterminated quoted name'); i = end + 1
        elif (match := re.match(r'r(#+)?"', src[i:])) and (i == 0 or not (src[i-1].isalnum() or src[i-1] in "_'")):
            ending = '"' + (match[1] or ''); end = src.find(ending, i + len(match[0]))
            need(end >= 0, 'unterminated raw string'); end += len(ending); hide(i, end); i = end
        elif src[i] == '"':
            end = i + 1
            while end < len(src):
                if src[end] == '\\': end += 2
                elif src[end] == '"': end += 1; break
                else: end += 1
            hide(i, end); i = end
        elif src[i] == "'" and (i == 0 or not (src[i-1].isalnum() or src[i-1] in "_'")) and (match := re.match(r"'(?:\\(?:u\{[0-9a-fA-F]+\}|[^\n])|[^'\\\n])'", src[i:])):
            end = i + len(match[0]); hide(i, end); i = end
        else: i += 1
    return ''.join(out)


TACTIC = re.compile(r"(?<![\w.'])(unfold|delta|rw|rwa|rewrite|erw|nth_rw|nth_rewrite|simp_rw|simp_all|simpa|simp|dsimp|norm_num|field_simp|simp_arith|push_cast|rw_mod_cast)(\??!?)(?![\w'])")
HEADWORD = re.compile(r"[^\s,\[\]()⟨⟩:;{}←]+")


def closing(text, start):
    depth = 0
    for pos in range(start, len(text)):
        if text[pos] == '[': depth += 1
        elif text[pos] == ']':
            depth -= 1
            if depth == 0: return pos
    raise RuntimeError('unclosed explicit list')


def list_start(text, pos):
    while True:
        while pos < len(text) and text[pos].isspace(): pos += 1
        if re.match(r'only\b', text[pos:]): pos += 4; continue
        if pos < len(text) and text[pos] == '(':
            depth = 1; pos += 1
            while depth:
                need(pos < len(text), 'unclosed tactic configuration')
                if text[pos] == '(': depth += 1
                elif text[pos] == ')': depth -= 1
                pos += 1
            continue
        match = re.match(r'\d+\s*', text[pos:])
        if match: pos += len(match[0]); continue
        return pos if pos < len(text) and text[pos] == '[' else None


def inventory(raw):
    src = blank(raw); starts = [0] + [m.end() for m in re.finditer('\n', src)]
    lineof = lambda pos: bisect.bisect_right(starts, pos)
    rows = []
    for match in TACTIC.finditer(src):
        tac = match[1]; line = lineof(match.start())
        if tac in {'unfold', 'delta'}:
            column = match.start() - starts[line-1]; cur = line; begin = match.end()
            while True:
                end = src.find('\n', begin); end = len(src) if end < 0 else end
                cut = re.split(r'\bat\b|;|<;>|\)|\||=>|·', src[begin:end])
                for token in cut[0].split():
                    if not HEADWORD.fullmatch(token) or token[0].isdigit(): break
                    rows.append({'line': cur, 'tactic_line': line, 'tactic': tac, 'item': token, 'head': token.rstrip('.')})
                if len(cut) > 1 or end >= len(src): break
                nxt = end + 1
                while nxt < len(src):
                    stop = src.find('\n', nxt); stop = len(src) if stop < 0 else stop
                    if src[nxt:stop].strip(): break
                    nxt = stop + 1
                if nxt >= len(src): break
                stop = src.find('\n', nxt); stop = len(src) if stop < 0 else stop
                segment = src[nxt:stop]
                if len(segment) - len(segment.lstrip()) <= column: break
                begin = nxt; cur = lineof(nxt)
        else:
            begin = list_start(src, match.end())
            if begin is None: continue
            end = closing(src, begin); begin += 1; depth = 0; item_start = begin
            for pos in range(begin, end + 1):
                char = src[pos] if pos < end else ','
                if pos < end and char in '([⟨{': depth += 1
                elif pos < end and char in ')]⟩}': depth -= 1
                if char == ',' and depth == 0:
                    item = src[item_start:pos].strip()
                    prefix = re.sub(r'^(?:←|<-|↓|-|@|\(|\s)+', '', item)
                    word = HEADWORD.match(prefix)
                    if word:
                        first = item_start
                        while first < pos and src[first].isspace(): first += 1
                        rows.append({'line': lineof(first), 'tactic_line': line, 'tactic': tac,
                                     'item': item, 'head': word[0].rstrip('.')})
                    item_start = pos + 1
    return rows


def complete_declarations(rows, raw):
    """Top-level boundaries only: tactic-local `open ... in` is part of the proof."""
    lines = raw.splitlines(keepends=True); code = blank(raw).splitlines()
    rows = list(rows); stack = []; namespace = ''; anonymous = 0
    for i, line in enumerate(code):
        if re.match(r'^(?:@\[[^\n]*?\]\s*)*(?:(?:noncomputable|private|protected)\s+)*instance\s*(?=[({\[:])', line):
            anonymous += 1
            rows.append({'canonical': namespace + '.<instance#' + str(anonymous) + '>',
                         'name': '<instance#' + str(anonymous) + '>', 'kind': 'instance',
                         'start': i + 1, 'lexical_placeholder_not_actual_Lean_Name': True})
        if line.startswith('namespace '):
            for part in line.split()[1].split('.'):
                stack.append(namespace); namespace = '.'.join(x for x in [namespace, part] if x)
        elif re.match(r'^(?:noncomputable\s+)?section(?:\s|$)', line): stack.append(namespace)
        elif re.match(r'^end(?:\s|$)', line):
            label = line[3:].strip(); count = len(label.split('.')) if label else 1
            for _ in range(count):
                need(stack, 'unbalanced lexical namespace'); namespace = stack.pop()
    rows.sort(key=lambda d: d['start'])
    boundaries = {d['start'] - 1 for d in rows}
    command = re.compile(r'^(?:namespace|section|end|open|variable|variables|include|omit|set_option|attribute|export|mutual|syntax|macro|elab|initialize|notation|infix[lr]?|prefix|postfix)\b|^@\[')
    boundaries.update(i for i, line in enumerate(code) if command.match(line))
    result = []
    for d in rows:
        first = d['start'] - 1
        end = min((i for i in boundaries if i > first), default=len(lines))
        result.append({**d, 'end': end, 'raw': ''.join(lines[first:end])})
    return result


def main():
    need(not (OUT / 'explicit-inventory.json').exists(), 'no overwrite')
    scope = load(OUT / 'scope.json'); head_decls = load(OUT / 'declarations-head.json'); base_decls = load(OUT / 'declarations-base.json')
    prior_decls = load(OUT / 'declarations-prior.json')
    for path in scope['math_paths']:
        head_decls[path] = complete_declarations(head_decls[path], read(OUT / 'snapshots/head' / path).decode())
        if path in base_decls:
            base_decls[path] = complete_declarations(base_decls[path], read(OUT / 'snapshots/base' / path).decode())
    old = load(R / 'final-explicit-static-inventory-v2.json')
    old_resolution = load(R / 'final-explicit-tcslib-resolution.json')
    old_classification = load(R / 'final-explicit-classification.json')
    source_catalog = load(R / 'final-explicit-primary-source-catalog.json')
    supplement = load(R / 'final-explicit-primary-supplement.json')
    need(set(old['math_files']) == set(scope['math_paths']), 'math scope changed')
    # This is own prior literal-sensitive comparison code, selected as pure definitions only.
    own = ROOT / '.lake/ps-maintainer/gate06-combined-20261108/source-review/verify.py'
    syntax = ast.parse(read(own)); ns = {'re': re, 'json': json, 'sha': sha}
    defs = [n for n in syntax.body if isinstance(n, ast.FunctionDef) and n.name in {'comment_projection', 'code_hash'}]
    exec(compile(ast.Module(body=defs, type_ignores=[]), '<own code comparison>', 'exec'), ns)
    old_by_file = defaultdict(list)
    for row in old['items']: old_by_file[row['path']].append(row)
    old_resolved = defaultdict(deque)
    fingerprint = lambda row: (row['path'], row['tactic'], ' '.join(row['item'].split()), row['head'])
    for row in old_resolution['items']: old_resolved[fingerprint(row)].append(row)
    old_touched = defaultdict(deque)
    for row in old_classification['items']: old_touched[fingerprint(row)].append(row)
    fresh = []; transfers = []; unmapped = []
    for path in scope['math_paths']:
        raw = read(OUT / 'snapshots/head' / path).decode()
        prior = subprocess.check_output(['git', '--no-optional-locks', '-C', str(ROOT), 'show', PRIOR + ':' + path]).decode()
        need(ns['code_hash'](raw) == ns['code_hash'](prior), 'current math code differs from prior audited source: ' + path)
        items = inventory(raw)
        expect = old_by_file[path]
        a = [(r['tactic'], ' '.join(r['item'].split()), r['head']) for r in items]
        b = [(r['tactic'], ' '.join(r['item'].split()), r['head']) for r in expect]
        need(a == b, 'fresh complete item sequence differs: ' + path + ' ' + str((len(a), len(b))))
        before = {(d['canonical'], d['kind']): d for d in base_decls.get(path, [])}
        for row, prior_row in zip(items, expect):
            row['path'] = path
            owners = [d for d in head_decls[path] if d['start'] <= row['line'] <= d['end']]
            need(len(owners) == 1, 'ambiguous explicit owner: ' + str((path, row, [d['canonical'] for d in owners])))
            owner = owners[0]; baseline = before.get((owner['canonical'], owner['kind']))
            row['declaration'] = owner['canonical']
            row['declaration_status'] = 'NEW' if baseline is None else 'SAME' if ns['code_hash'](owner['raw']) == ns['code_hash'](baseline['raw']) else 'CHANGED'
            row['namespace'] = prior_row['namespace']; row['opens'] = prior_row['opens']
            need(owner['canonical'] == prior_row['declaration'], 'owner identity differs: ' + str((path, row['line'], owner['canonical'], prior_row['declaration'])))
            key = fingerprint(row); evidence = old_resolved[key].popleft()
            row['tcslib_source_candidates'] = evidence['tcslib_source_candidates']
            if row['declaration_status'] != 'SAME':
                if old_touched[key]:
                    prior_evidence = old_touched[key].popleft()
                    row['classification'] = prior_evidence['classification']; row['primary_evidence'] = prior_evidence.get('primary_evidence')
                    transfers.append(row)
                else: unmapped.append(row)
            fresh.append(row)
    need(not unmapped and not any(old_resolved.values()) and not any(old_touched.values()), 'unmatched classification/complete item rows')
    # Revalidate every cited source/generator file; TCS comment-only hash changes are explicit.
    provenance = {}; candidates = []
    for row in transfers:
        evidence = row.get('primary_evidence')
        if isinstance(evidence, list): candidates.extend(evidence)
        elif isinstance(evidence, dict): candidates.append(evidence)
    candidates += list(supplement['interfaces'].values())
    generators = supplement.get('generator_evidence', [])
    candidates += list(generators.values()) if isinstance(generators, dict) else generators
    for evidence in candidates:
        p = evidence.get('primary_path') or evidence.get('path')
        digest = evidence.get('source_sha256')
        if not p or not digest: continue
        path = Path(p); path = ROOT / path if not path.is_absolute() else path
        if str(path) in provenance: continue
        content = read(path); equal = sha(content) == digest
        status = 'EXACT_PRIMARY_SOURCE_SHA'
        if not equal:
            need(path.is_relative_to(ROOT / 'TCSlib'), 'non-TCS primary source changed: ' + str(path))
            previous = subprocess.check_output(['git', '--no-optional-locks', '-C', str(ROOT), 'show', PRIOR + ':' + path.relative_to(ROOT).as_posix()])
            need(sha(previous) == digest and ns['code_hash'](content.decode()) == ns['code_hash'](previous.decode()), 'primary evidence changed substantively')
            status = 'PRIOR_SOURCE_SHA_MATCH_CURRENT_CODE_EXACT_COMMENT_ONLY_DELTA'
        provenance[str(path)] = {'recorded_sha256': digest, 'current_sha256': sha(content), 'status': status}
    native = read(R / 'final-explicit-native-table-r1/native-kinds.tsv').decode()
    kinds = {}; homes = {}
    for line in native.splitlines():
        name, kind, home = line.split('\t'); need(name not in kinds, 'duplicate native catalog name')
        kinds[name] = kind; homes[name] = home
    def resolve(token, row):
        if token.startswith('_root_.'): return [token[7:]] if token[7:] in kinds else []
        pieces = row['namespace'].split('.') if row['namespace'] else []
        module = row['path'][:-5].replace('/', '.')
        for n in range(len(pieces), 0, -1):
            prefix = '.'.join(pieces[:n])
            found = [name for name in (prefix + '.' + token, '_private.' + module + '.0.' + prefix + '.' + token) if name in kinds]
            if found: return found
        found = [name for name in (token, '_private.' + module + '.0.' + token) if name in kinds]
        for opened in row['opens']:
            name = opened + '.' + token
            if name in kinds and name not in found: found.append(name)
        return found
    raw_hits = []
    for row in fresh:
        for name in resolve(row['head'], row):
            module = row['path'][:-5].replace('/', '.')
            if kinds[name].startswith('def') and homes[name] != module:
                raw_hits.append({**row, 'foreign_name': name, 'foreign_kind': kinds[name], 'foreign_home': homes[name]})
    # Preserve the selected-open supplement independently of the historical text resolver.
    inherited = []
    for old_row in old_resolution['foreign_source_candidates']:
        candidates = [r for r in fresh if r['path'] == old_row['path'] and r['declaration'] == old_row['declaration']
                      and r['tactic'] == old_row['tactic'] and r['head'] == old_row['head']]
        same_old = [r for r in old_resolution['foreign_source_candidates'] if r['path'] == old_row['path']
                    and r['declaration'] == old_row['declaration'] and r['tactic'] == old_row['tactic'] and r['head'] == old_row['head']]
        index = same_old.index(old_row); row = candidates[index]
        need(row['declaration_status'] == 'SAME', 'inherited foreign definition now touched')
        foreign = old_row['foreign_candidate']; current = read(OUT / 'snapshots/head' / foreign['path']).decode().splitlines()
        matching = [i+1 for i, line in enumerate(current) if line.strip() == foreign['source_line'].strip()]
        need(len(matching) == 1, 'foreign source definition location ambiguous')
        inherited.append({**row, 'foreign_name': foreign['name'], 'foreign_home': foreign['path'],
                          'foreign_line': matching[0], 'definition_source_kind': foreign['kind'],
                          'recorded_notation': foreign['name'] == 'Complexity.PolyExpr.eval', 'source_failure_exclusion': False})
    save('explicit-inventory.json', {'base': BASE, 'head': HEAD, 'items': fresh, 'count': len(fresh),
                                     'method': 'Own fresh continuation-list lexer; exact prior full-item sequence and current/prior formal code matching; classifications revalidated against primary sources.'})
    save('explicit-touched-dispositions.json', transfers)
    save('explicit-raw-c1.json', raw_hits)
    save('explicit-inherited-tcs-debt.json', inherited)
    save('explicit-primary-evidence.json', provenance)
    summary = {'status': 'FRESH_STATIC_C1_WITH_REVALIDATED_PRIOR_CLASSIFICATION_NOT_NATIVE', 'base': BASE, 'head': HEAD,
               'complete_items': len(fresh), 'new_touched_items': len(transfers), 'classification_counts': dict(Counter(r['classification'] for r in transfers)),
               'new_touched_foreign_definition_items': sum(r['declaration_status'] != 'SAME' for r in raw_hits),
               'raw_c1_hits_with_historical_native_kinds': len(raw_hits), 'inherited_TCS_candidates': len(inherited),
               'exact_notation_items': sum(r['recorded_notation'] for r in inherited), 'unresolved_touched_items': len(unmapped),
               'C2': 'NOT_MEASURED_NO_FRESH_SEAL_INPUT', 'C3': 'NOT_MEASURED_NO_FRESH_PROOF_TERM_INPUT',
               'native_kind_catalog_epoch': PRIOR, 'input_bindings': INPUTS,
               'limits': ['No received scanner executed; hardened Gate04 source read as reference only.',
                          'Current proof/declaration code matches the old audited source; current-base touched status is recomputed independently.',
                          'Native kind table is historical metadata, not a current native census.',
                          'All inherited observations retained; no source failure exclusion or merge clearance.']}
    save('explicit-summary.json', summary)
    print(json.dumps({k: v for k, v in summary.items() if k != 'input_bindings'}))


if __name__ == '__main__': main()
