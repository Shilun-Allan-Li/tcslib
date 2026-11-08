"""Compare the two authorized native equation probes as exact data, without normalization."""
from pathlib import Path
import hashlib
import json
import re

OUT = Path(__file__).resolve().parent
NAMES = {'Turing.splitAtLastTrue', 'Turing.splitAtLastTrue.eq_1'}


def sha(data):
    return hashlib.sha256(data).hexdigest()


def read(stage):
    p = OUT / ('Equation' + stage)
    source = p.with_suffix('.lean.txt').read_bytes()
    output = p.with_suffix('.out').read_bytes()
    receipt = json.loads((OUT / ('Equation' + stage + '-run.json')).read_text())
    assert (receipt['exit'], receipt['errors'], receipt['warnings']) == (0, 0, 0)
    assert sha(source) == receipt['input_sha256'] and sha(output) == receipt['output_sha256']
    assert Path(receipt['command'][-1]).read_bytes() == source
    assert receipt['local_slots'] == '3' and receipt['plain_managed']
    text = output.decode()
    markers = list(re.finditer(r'(?m)^(DETAIL|TYPE_REPR|VALUE_REPR|PRETTY_TYPE|AXIOMS)\|([^|\n]+)\|', text))
    data = {name: {} for name in NAMES}
    for i, marker in enumerate(markers):
        tag, name = marker.groups()
        assert name in data and tag not in data[name]
        stop = markers[i + 1].start() if i + 1 < len(markers) else len(text)
        value = text[marker.end():stop].rstrip('\n')
        assert '...' not in value and '⋯' not in value
        data[name][tag] = value
    for name, row in data.items():
        assert set(row) == {'DETAIL', 'TYPE_REPR', 'VALUE_REPR', 'PRETTY_TYPE', 'AXIOMS'}
        owner, kind, private, internal, simp, unfold = row['DETAIL'].split('|')
        row['attributes'] = dict(owner=owner, kind=kind, private=private == 'private=true',
                                  internal=internal == 'internal=true', simp=simp == 'simp=true',
                                  unfold=unfold == 'unfold=true')
        assert row['AXIOMS'] == '[]'
        row['type_repr_sha256'] = sha(row['TYPE_REPR'].encode())
        row['value_repr_sha256'] = sha(row['VALUE_REPR'].encode())
    return data


base, head = read('Base'), read('Head')
assert (OUT / 'EquationBase.lean.txt').read_bytes() == (OUT / 'EquationHead.lean.txt').read_bytes()
for label, rows in [('base', base), ('head', head)]:
    census = json.loads((OUT / ('map-' + label + '.json')).read_text())
    actual = rows['Turing.splitAtLastTrue.eq_1']['attributes']
    recorded = census['census']['Turing.splitAtLastTrue.eq_1']
    assert all(actual[key] == recorded[key] for key in ['owner', 'kind', 'private', 'internal'])
    assert census['all_axioms']['Turing.splitAtLastTrue.eq_1']['axioms'] == []
comparison = {}
for name in sorted(NAMES):
    for field in ['TYPE_REPR', 'VALUE_REPR', 'PRETTY_TYPE', 'AXIOMS']:
        assert base[name][field] == head[name][field], (name, field)
    changes = [key for key, value in base[name]['attributes'].items() if value != head[name]['attributes'][key]]
    assert changes == ([] if name == 'Turing.splitAtLastTrue' else ['owner'])
    assert not base[name]['attributes']['simp'] and not head[name]['attributes']['simp']
    assert not base[name]['attributes']['unfold'] and not head[name]['attributes']['unfold']
    comparison[name] = dict(type_repr_byte_equal=True, value_repr_byte_equal=True,
                           pretty_formula_byte_equal=True, axioms_empty_both=True,
                           no_binder_or_private_ID_normalization=True,
                           changed_attributes=changes, base=base[name], head=head[name])
context = json.loads((OUT / 'equation-source-context.json').read_text())
assert context['source_equal'] and not context['olean_equal']
assert (OUT / 'Convention-Base.lean.txt').read_bytes() == (OUT / 'Convention-Head.lean.txt').read_bytes()
result = dict(status='Two authorized actual-context probes PASS; function and eq_1 formula/value unchanged; only generated eq_1 owner differs.',
              comparison=comparison, context=context,
              source_definition_formula='splitAtLastTrue v = match v.reverse.dropWhile (fun b => !b) with | true :: rest => some rest.reverse | _ => none',
              limits='Direct raw type/value representations and full defining source text are equal. This is not recursive equality checking of every referenced constant, binary olean identity, a generated-home design ruling or an API approval.')
(OUT / 'equation-comparison.json').write_text(json.dumps(result, indent=2, sort_keys=True) + '\n')
print(json.dumps({name: {key: value for key, value in row.items() if key not in ['base', 'head']}
                  for name, row in comparison.items()}, indent=2))
