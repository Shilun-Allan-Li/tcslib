r"""frozen_check_bb1m.py <base-file> <head-file> (fill-bb1-machine): frozen-header check of the owned
AdvancedEncryption/IdentityBased/BonehBoyenMachine.lean. Reverts exactly the permitted edits in the head file and requires the
result to equal the base file byte for byte:
  (1) added import lines, each `import TCSlib.Cryptography.AdvancedEncryption.IdentityBased.BonehBoyenMachine.<Name>`
      with <Name> one of the fill's helper modules Draws, Handler, Reduction, Words;
  (2) one `## Contents` section of the module docstring, inserted right after the base's `## Main definitions\n\nNone.\n`
      and ending before the next `## ` heading;
  (3) in T4 (`exists_bb1_distinguisher`): the `**Proof sketch.**` paragraph (to the docstring's end) and the body after
      the header's last line `      advantage (bb1SimGame G ℓ A (q.eval κ) b real κ) (G.dbdhGame (D b) real κ) ≤ σ κ := by`
      (to `end TCSlib...`) are replaced by the base's; the head's body must be indented (no top-level line, so no
      declaration can be added there). Everything else (T4's header and statement prose, the rest of the
      module docstring, the other imports) must be byte-identical. Prints PASS or FAIL with the first differing line."""
import sys, re
base = open(sys.argv[1], encoding='utf-8').read(); head = open(sys.argv[2], encoding='utf-8').read()
def fail(msg): print('FAIL:', msg); sys.exit(1)
HP = 'import TCSlib.Cryptography.AdvancedEncryption.IdentityBased.BonehBoyenMachine.'
bi = re.findall(r'^import \S+\n', base, re.M); hi = re.findall(r'^import \S+\n', head, re.M)
added = [l for l in hi if l not in bi]
for l in added:
    if not (l.startswith(HP) and l[len(HP):].strip() in ('Draws', 'Handler', 'Reduction', 'Words')):
        fail(f'added import not a helper: {l!r}')
if [l for l in hi if l in bi] != bi: fail('base imports changed or reordered')
h = head
for l in added: h = h.replace(l, '', 1)
anchor = '## Main definitions\n\nNone.\n'
if anchor not in h: fail('Main definitions anchor missing')
i = h.index(anchor) + len(anchor)
if h[i:].startswith('\n## Contents\n'):
    j = h.index('\n## ', i + 1)
    h = h[:i] + h[j:]
# (3) T4 sketch and body
HL = '      advantage (bb1SimGame G ℓ A (q.eval κ) b real κ) (G.dbdhGame (D b) real κ) ≤ σ κ := by\n'
END = '\nend TCSlib.Cryptography.AdvancedEncryption.IdentityBased\n'
def cut(s, tag):
    if s.count(HL) != 1: fail(f'{tag}: T4 header end line not found exactly once')
    if not s.endswith(END): fail(f'{tag}: file end changed')
    a = s.index(HL) + len(HL); body = s[a:len(s) - len(END)]
    t4 = s.index('theorem exists_bb1_distinguisher')
    ds = s.rfind('/--', 0, t4); ps = s.find('**Proof sketch.**', ds, t4)
    if ps < 0: fail(f'{tag}: no proof sketch in T4 docstring')
    pe = s.index('-/\n', ps)
    return s[:ps], s[pe:a], body
b0, b1, bb = cut(base, 'base'); h0, h1, hb = cut(h, 'head')
if hb.strip() == '': fail('T4 body empty')
for ln in hb.split('\n'):
    if ln and not ln.startswith(' '): fail(f'top-level line in T4 body: {ln!r}')
if 'sorry' not in bb: fail('base T4 body not sorry')
for x, y, nm in ((b0, h0, 'before T4 sketch'), (b1, h1, 'T4 header')):
    if x != y:
        xl, yl = x.split('\n'), y.split('\n')
        k = next((n for n in range(min(len(xl), len(yl))) if xl[n] != yl[n]), min(len(xl), len(yl)))
        fail(f'{nm} differs at line {k + 1}: base {xl[k] if k < len(xl) else None!r} head {yl[k] if k < len(yl) else None!r}')
rebuilt = h0 + base[len(b0):]  # base sketch + header + body
if rebuilt.replace(base[len(b0):], '') != b0: fail('internal')
print(f'PASS: {len(added)} helper import(s) added; Contents section {"present" if "## Contents" in head else "absent"}; '
      f'T4 header byte-identical; T4 body {"unchanged (sorry)" if hb == bb else "replaced"}')
