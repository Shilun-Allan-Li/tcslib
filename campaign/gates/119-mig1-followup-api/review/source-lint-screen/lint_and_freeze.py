from pathlib import Path
import contextlib, difflib, hashlib, importlib.util, io, json, re, sys

sys.dont_write_bytecode = True
OUT = Path(__file__).resolve().parent
ROOT = OUT.parents[4]
capture = json.loads((OUT / 'capture.json').read_text())
changed = capture['changed_files']

def load_module(name, path):
    spec = importlib.util.spec_from_file_location(name, path)
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module

style = load_module('gate119_style', ROOT / 'scripts/style_lint.py')
campaign = load_module('gate119_campaign', ROOT / 'scripts/campaign_style_lint.py')
result = dict(method='Unmodified canonical lint functions, ROOT redirected to inert exact Git archive trees, same five changed files; check8b enabled.', tools=capture['tools'], sides={})
for side in ['base', 'head']:
    tree = Path(capture['temporary_trees'][side])
    style.ROOT = tree
    sf = [message for path in changed for message in style.lint(tree / path)]
    (OUT / ('style-' + side + '.out')).write_text('\n'.join(sf) + f'\n{len(sf)} findings in {len(changed)} files\n')
    campaign.ROOT = tree; campaign.CHECK8B = True; campaign.findings = []
    for path in changed:
        f = tree / path; campaign.check_file(f)
        if campaign.is_facade(f): campaign.check_facade(f)
    cf = campaign.findings
    text = '\n'.join(f'{level} {path}: {message}' for level, path, message in cf)
    counts = {level:sum(1 for row in cf if row[0] == level) for level in ['FAIL','WARN','INFO']}
    (OUT / ('campaign-' + side + '.out')).write_text(text + '\n' + str(counts) + '\n')
    result['sides'][side] = dict(style=dict(exit=1 if sf else 0, findings=sf),
        campaign=dict(exit=1 if counts['FAIL'] else 0, counts=counts, findings=cf))

normalize = lambda text: re.sub(r'\b\d+ lines', '<LINES> lines', re.sub(r':\d+:', ':LINE:', text))
for tool in ['style', 'campaign']:
    a = result['sides']['base'][tool]['findings']; b = result['sides']['head'][tool]['findings']
    if tool == 'campaign':
        a = ['|'.join(row) for row in a]; b = ['|'.join(row) for row in b]
    aa = [normalize(t) for t in a]; bb = [normalize(t) for t in b]
    result[tool + '_normalized_new'] = sorted(set(bb) - set(aa))
    result[tool + '_normalized_gone'] = sorted(set(aa) - set(bb))
(OUT / 'lint-results.json').write_text(json.dumps(result, indent=2) + '\n')

freeze = []
for path in changed:
    before = (OUT / 'inputs/base' / (path + '.txt')).read_text()
    after = (OUT / 'inputs/head' / (path + '.txt')).read_text()
    a = before.splitlines(keepends=True); b = after.splitlines(keepends=True)
    ops = [dict(tag=t, before_start=i, before_end=j, after_start=k, after_end=l,
                old_text=''.join(a[i:j]), new_text=''.join(b[k:l]))
           for t, i, j, k, l in difflib.SequenceMatcher(None, a, b, autojunk=False).get_opcodes() if t != 'equal']
    assert len(ops) == 1
    expected = 'delete' if path.endswith('/Catalog.lean') else 'insert'
    assert ops[0]['tag'] == expected
    freeze.append(dict(path=path, delta=ops[0]))
(OUT / 'whole-source-delta.json').write_text(json.dumps(freeze, indent=2) + '\n')
print(json.dumps(dict(lint={s:{'style':len(result['sides'][s]['style']['findings']),
    'campaign':result['sides'][s]['campaign']['counts']} for s in ['base','head']},
    style_new=result['style_normalized_new'], campaign_new=result['campaign_normalized_new'],
    source_scope='Exactly four insertion blocks and one Catalog deletion; every other line unchanged.'), indent=2))
