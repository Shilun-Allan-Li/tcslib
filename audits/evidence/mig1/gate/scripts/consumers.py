"""Code citations of named declarations across all TCSlib modules. Read-only.

Usage: python3 -I consumers.py <worktree> <names.json> <out.json>

names.json: list of [home module, short name]. For each name: every identifier occurrence
(bare or qualified, last component equal to the name, not followed by an identifier character)
in the comment-stripped code of every `TCSlib` module, minus the declaration's own header
line; reported per file with line numbers, split into the home file (internal) and the others
(external). The script also checks that each name is declared exactly once in the tree, so
that the textual matches are unambiguous. Docstring and comment mentions are counted
separately ("doc").
"""
import glob
import json
import os
import re
import sys

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from namescreen import strip, index_file  # noqa: E402


def main():
    wt, names_json, out = sys.argv[1:4]
    names = json.load(open(names_json, encoding='utf-8'))
    files = sorted(glob.glob(os.path.join(wt, 'TCSlib', '**', '*.lean'), recursive=True))
    src = {}
    code = {}
    idx = []
    for f in files:
        mod = os.path.relpath(f, wt)[:-5].replace(os.sep, '.')
        s = open(f, encoding='utf-8').read()
        src[mod] = s.split('\n')
        code[mod] = strip(s).split('\n')
        idx.extend(index_file(f, mod))
    res = {}
    for home, name in names:
        decl = [d for d in idx if d['short'] == name]
        pat = re.compile(r'(?<![\w\'])(?:[\w\']+\.)*' + re.escape(name) + r'(?![\w\'])')
        ext, internal, doc = [], [], []
        for mod in code:
            for i, l in enumerate(code[mod], 1):
                if any(d['mod'] == mod and d['line'] == i for d in decl):
                    continue
                n = len(pat.findall(l))
                if n:
                    (internal if mod == home else ext).append([mod, i, n])
                raw = src[mod][i - 1]
                nd = len(pat.findall(raw)) - n
                if nd > 0:
                    doc.append([mod, i, nd])
        res[name] = dict(home=home, declared=[[d['mod'], d['line'], d['private']] for d in decl],
                         internal=internal, external=ext, doc=doc)
    json.dump(res, open(out, 'w', encoding='utf-8'), indent=1)
    tot = sum(sum(n for _, _, n in r['external']) for r in res.values())
    files_ext = {m for r in res.values() for m, _, _ in r['external']}
    for name, r in res.items():
        e = sum(n for _, _, n in r['external'])
        fs = sorted({m.split('.')[-1] for m, _, _ in r['external']})
        print(f"{name}: declared {len(r['declared'])}; internal "
              f"{sum(n for _, _, n in r['internal'])}; external {e} in {len(fs)} files"
              f"{': ' + ', '.join(fs) if fs else ''}; doc {sum(n for _, _, n in r['doc'])}")
    print(f'total external citations: {tot} in {len(files_ext)} files')


if __name__ == '__main__':
    main()
