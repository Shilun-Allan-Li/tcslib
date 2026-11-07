from pathlib import Path
import difflib
import hashlib
import json
import subprocess

ROOT = Path('/Users/seyoonr/.codex/worktrees/ps-gate06-integration/tcslib-pass-shelat-ch2-4')
OUT = ROOT / '.lake/ps-maintainer/gate06-audit-intake-r1/b-corrections'
OUT.mkdir(parents=True, exist_ok=True)
head = subprocess.check_output(['git', '-C', str(ROOT), 'rev-parse', 'HEAD'], text=True).strip()
assert head == '3f6db40e1688c4a0bb922c9575dd3bd2157a650b'

def uncomment(s):
    out, i, depth, string = [], 0, 0, False
    while i < len(s):
        if depth:
            if s.startswith('/-', i): depth += 1; i += 2
            elif s.startswith('-/', i): depth -= 1; i += 2
            else: i += 1
        elif string:
            out.append(s[i])
            if s[i] == '\\' and i + 1 < len(s): i += 1; out.append(s[i])
            elif s[i] == '"': string = False
            i += 1
        elif s.startswith('/-', i): depth = 1; i += 2
        elif s.startswith('--', i):
            while i < len(s) and s[i] != '\n': i += 1
        else:
            if s[i] == '"': string = True
            out.append(s[i]); i += 1
    assert depth == 0 and not string
    return ''.join(out)

updates = {}
def replace(name, old, new):
    path = 'TCSlib/Cryptography/SecureComputation/' + name + '.lean'
    s = updates.get(path, (ROOT / path).read_text())
    assert s.count(old) == 1, (path, old[:90], s.count(old))
    updates[path] = s.replace(old, new)

replace('ObliviousTransfer',
'''**On the ch. 2–4 layer.** The collection is a `TrapdoorCollection`, used as Algorithm 104.3 uses it:
`Gen`, the domain sampler, the evaluator `eval`, and the trapdoor inverter run on the all-`true`
coin string. The hard-core predicate is evaluated by a polynomial-time `H`, specified by''',
'''**On the ch. 2–4 layer.** The collection is a `TrapdoorCollection`, used as Algorithm 104.3 uses it.
`Gen` uses Alice's fresh generator coins, and the two domain samples use separate fresh blocks
of Bob's tape. The evaluator `eval` is deterministic. Only the trapdoor inverter uses a fixed
all-`true` tape, justified by its correctness on every inverter tape. The hard-core predicate
is evaluated by a polynomial-time `H`, specified by''')
replace('ObliviousTransfer',
'''  even given the sampler's coins. This is the standard repair of this protocol (enhanced trapdoor
  permutations, [Gol04, Appendix C.1]).''',
'''  even given the sampler's coins. Enhanced inversion is motivated in [Gol04, Appendix C.1];
  the predicate and OT argument are in [Gol04, §7.3.2]. The Boolean prediction experiment here
  is an explicit hypothesis, not a literal transcription of the inversion condition C.1.1.''')
replace('ObliviousTransfer',
'''  2004, Appendix C.1 (enhanced trapdoor permutations).''',
'''  2004, Appendix C.1 (enhanced inversion) and §7.3.2 (enhanced predicates and OT). The audit
  consulted the author drafts: Appendix revised third version, 15 June 2003; Chapter 7
  version 3.2, 2 July 2003, draft pp. 639–641 for the predicate/OT argument. No text/page
  identity with the published edition is asserted.''')
replace('ObliviousTransfer',
'''/-- **An enhanced hard-core predicate** [Gol04, Appendix C.1] (a declared strengthening of
[PS10, Proposition 161.5]'s hypothesis; see the module docstring): for every non-uniform PPT `A`,''',
'''/-- **An enhanced hard-core predicate**, the explicit Boolean prediction hypothesis used for
the OT argument of [Gol04, §7.3.2] (a declared strengthening of [PS10, Proposition 161.5]'s
hypothesis; see the module docstring). Appendix C.1 motivates enhanced inversion; its
Definition C.1.1 is an inversion condition, not this prediction definition. For every
non-uniform PPT `A`,''')
replace('ObliviousTransfer',
'''   - The predictor depends on `(b, a_{1−b})`, four cases, so the bound is uniform over the
     inputs: take the maximum of the four negligible functions.''',
'''   - Building the selected mask also uses `a_b`, so take all eight triples `(b,a₀,a₁)`.
     The maximum of their eight negligible bounds is negligible and uniform over the inputs;
     fixing only the choice and unselected sender bit would not specify the complete view.''')

replace('SpecialEncryption',
'''- `Dec` refuses malformed ciphertexts and keys (length checks first). The evaluator `E` agrees
  with `f` only on `n`-bit keys and inputs, the lesson of Algorithm 99.1's guard.''',
'''- `Dec` checks the key, nonce-component and body-component lengths before evaluating `E`,
  then checks the pad prefix. It uses total pair projections and does not separately require
  successful pair parsing. At `n = ℓ = 0`, the malformed empty ciphertext with an empty key
  therefore returns `some []`. The length checks protect the stated `n`-bit evaluator domain;
  universal malformed-input rejection is not claimed.''')
replace('SpecialEncryption',
'''message `c₂,_{≥n} ⊕ p_{≥n}` if `c₂,_{<n} = p_{<n}` ("`m₀ = 0^n`"), and `⊥` otherwise. -/''',
'''message `c₂,_{≥n} ⊕ p_{≥n}` if `c₂,_{<n} = p_{<n}` ("`m₀ = 0^n`"), and `⊥` otherwise.
Here `r` and `c₂` are the total pair projections; successful parsing is not an additional
test. In particular `n = ℓ = 0`, `k = c = []` returns `some []`. -/''')

replace('Garbling',
'''- **The evaluator** opens the first row that decrypts (`List.findSome?`).''',
'''- **The evaluator** opens the first row that decrypts (`List.findSome?`). The formal `Good`
  invariant and the probability theorems below assert correctness of that first opening for
  every assignment. They do not assert the source's stronger unique-opening conclusion.
  Several rows may open to the same correct label, for example when wire labels coincide.
  The cross-opening union-bound sketch proves a sufficient stronger event for this target.''')
replace('Garbling',
'''* `SecureComputation.Good`: every table opens, under every assignment's keys, to the right key.''',
'''* `SecureComputation.Good`: every table's first successful opening, under every assignment's
  keys, gives the right key; uniqueness is not part of this invariant.''')
replace('Garbling',
'''first row of the table that decrypts gives the key of the gate's output on that assignment. -/''',
'''first row of the table that decrypts gives the key of the gate's output on that assignment.
This is first-success correctness, not uniqueness of the row that can decrypt. -/''')
replace('Garbling',
'''to be good with probability at most `12 · |gates| · δ`.

**Proof sketch.**''',
'''to be good with probability at most `12 · |gates| · δ`. The formal conclusion bounds failure
of first-success correctness; it does not state the source's stronger unique-opening claim.

**Proof sketch.**''')
replace('GarblingSecurity',
'''probability at most `12 · |gates| · δ(n)`. -/''',
'''probability at most `12 · |gates| · δ(n)`. Goodness here concerns the first successful opening
for every assignment; the stronger source assertion of unique opening is not this conclusion. -/''')

rows, patch = [], []
for path, after in sorted(updates.items()):
    raw = subprocess.check_output(['git', '-C', str(ROOT), 'show', f'{head}:{path}'])
    before = raw.decode()
    assert (ROOT / path).read_bytes() == raw
    assert uncomment(before) == uncomment(after), path
    target = OUT / 'src' / path
    target.parent.mkdir(parents=True, exist_ok=True)
    target.write_text(after)
    patch.extend(difflib.unified_diff(before.splitlines(keepends=True), after.splitlines(keepends=True),
                                     fromfile='a/' + path, tofile='b/' + path))
    rows.append({'path': path, 'before_sha256': hashlib.sha256(raw).hexdigest(),
                 'after_sha256': hashlib.sha256(after.encode()).hexdigest(),
                 'exact_noncomment_bytes_equal': True})
data = ''.join(patch).encode()
(OUT / 'minor-prose-corrections.patch').write_bytes(data)
(OUT / 'manifest.json').write_text(json.dumps({'source_head': head, 'applied': False,
    'native_check_claim': False, 'files': rows, 'patch_sha256': hashlib.sha256(data).hexdigest(),
    'status': 'Unapplied comment-only proposal, no algorithm/statement/source-branch advance.'}, indent=2) + '\n')
print(json.dumps({'files': len(rows), 'patch_sha256': hashlib.sha256(data).hexdigest(),
                  'exact_noncomment_bytes_equal': True, 'applied': False}, indent=2))
