"""Losslessly verify/decode native metadata and compare exact compiler names, never normalized."""
from pathlib import Path
import base64
import collections
import gzip
import hashlib
import json
import re
import sys

OUT = Path(__file__).resolve().parent
CONTEXT = json.loads((OUT / "context.json").read_text())
STANDARD = {"propext", "Classical.choice", "Quot.sound"}


def sha(data):
    return hashlib.sha256(data).hexdigest()


def write(name, data):
    (OUT / name).write_text(json.dumps(data, indent=2, ensure_ascii=False, sort_keys=True) + "\n")


def parse(label, version):
    stem = label + "-" + version
    receipt = json.loads((OUT / (stem + "-run.json")).read_text())
    assert receipt["exit"] == receipt["errors"] == 0
    payload = OUT / (stem + ".out.gz.b64")
    assert sha(payload.read_bytes()) == receipt["base64_sha256"]
    gz = Path(CONTEXT["scratch"]) / (stem + "-verified.out.gz")
    with payload.open("rb") as encoded, gz.open("wb") as binary:
        base64.decode(encoded, binary)
    assert sha(gz.read_bytes()) == receipt["gzip_sha256"]
    names = {}
    roots = {}
    proof_axes = {}
    public_axes = {}
    cited = []
    simprules = collections.defaultdict(list)
    digest = hashlib.sha256()
    context = complete = None
    values_omitted = False
    extras = []
    with gzip.open(gz, "rb") as raw:
        for line_no, raw_line in enumerate(raw, 1):
            digest.update(raw_line)
            line = raw_line.decode("utf-8").rstrip("\n")
            if line.startswith("CONSTANT "):
                match = re.fullmatch(r"CONSTANT (\S+) module=(\S+) kind=(\S+) private=(true|false) internal=(true|false)", line)
                assert match
                n, owner, kind, private, internal = match.groups()
                assert n not in names
                names[n] = dict(owner=owner, kind=kind, private=private == "true", internal=internal == "true", census_line=line_no)
            elif line.startswith(("CI|", "TYPE_REPR|", "VALUE_REPR|", "ATTR|", "ALLAX|", "PUBLICAX|", "SIMP_RULE|")):
                tag, n, raw_data = line.split("|", 2)
                value = json.loads(raw_data)
                assert n in names, (tag, n)
                row = names[n]
                if tag == "SIMP_RULE":
                    simprules[n].append(value)
                elif tag == "PUBLICAX":
                    assert n not in public_axes and not row["private"]
                    public_axes[n] = value
                elif tag in {"TYPE_REPR", "VALUE_REPR"}:
                    assert isinstance(value, str)
                    field = "type_repr" if tag == "TYPE_REPR" else "value_repr"
                    assert field not in row
                    row[field] = dict(bytes=len(value.encode()), sha256=sha(value.encode()), raw_line=line_no)
                else:
                    field = {"CI": "ci", "ATTR": "attributes", "ALLAX": "axioms"}[tag]
                    assert field not in row
                    row[field] = value
            elif line.startswith("ROOT|"):
                _, n, flag = line.split("|")
                assert flag == "private=true" and n not in roots
                roots[n] = dict(private=True)
            elif line.startswith("PROOFAX|"):
                _, n, kind, raw_data = line.split("|", 3)
                assert n not in proof_axes
                proof_axes[n] = dict(kind=kind.removeprefix("kind="), axioms=json.loads(raw_data))
            elif line.startswith("CITED|"):
                _, n, part, used, owner, kind, private = line.split("|")
                cited.append(dict(name=n, part=part, cited=used, owner=owner,
                                  kind=kind.removeprefix("kind="), private=private == "private=true", raw_line=line_no))
            elif line.startswith("CONTEXT|"):
                assert context is None
                context = line
            elif line == "VALUES_OMITTED|all_constant_values|retained_fields_are_uncapped":
                assert not values_omitted
                values_omitted = True
            elif line.startswith("COMPLETE|"):
                assert complete is None
                complete = line
            elif line:
                extras.append(dict(line=line_no, text=line))
    assert digest.hexdigest() == receipt["raw_utf8_sha256"]
    assert context == "CONTEXT|owners=9|roots=16|simp_environment_unchanged=true"
    assert values_omitted, "This parser version expects structural CI/types without constant value expansion"
    assert complete == f"COMPLETE|constants={len(names)}|roots=16"
    owners = set((OUT / "original9-owners.txt").read_text().splitlines())
    assert {r["owner"] for r in names.values()} == owners
    assert len(roots) == 16 and all(n in names and names[n]["private"] and names[n]["kind"] == "theorem" for n in roots)
    for n, row in names.items():
        assert set(row) == {"owner", "kind", "private", "internal", "census_line", "ci", "attributes", "axioms", "type_repr"}, n
        assert isinstance(row["axioms"], list) and len(row["axioms"]) == len(set(row["axioms"]))
    assert set(public_axes) == {n for n, row in names.items() if not row["private"]}
    assert all(public_axes[n] == names[n]["axioms"] for n in public_axes)
    expected = {n for n in names if any(n == root or n.startswith(root + ".") for root in roots)}
    assert set(proof_axes) == expected
    assert all(names[n]["kind"] == r["kind"] and names[n]["axioms"] == r["axioms"] for n, r in proof_axes.items())
    for n in roots:
        roots[n].update(owner=names[n]["owner"], axioms=names[n]["axioms"],
                        descendants=sorted(x for x in expected if x.startswith(n + ".")))
    assert all(row["name"] in expected for row in cited)
    for row in cited:
        row["same_home"] = row["owner"] == names[row["name"]]["owner"]
    counts = dict(total=len(names), private=sum(r["private"] for r in names.values()),
                  nonprivate=sum(not r["private"] for r in names.values()),
                  roots=len(roots), generated_root_descendants=len(proof_axes)-len(roots),
                  nonstandard_axiom_constants=sum(bool(set(r["axioms"])-STANDARD) for r in names.values()),
                  all_selected_standard=all(set(r["axioms"]) <= STANDARD for r in proof_axes.values()),
                  direct_cited_different_home_private=sum(r["private"] and not r["same_home"] for r in cited))
    result = dict(label=label, version=version, context_commit=receipt["context_commit"], counts=counts,
                  names=names, roots=roots, proof_axes=proof_axes, cited=cited,
                  simp_rules=dict(simprules), complete_ALLAX_coverage=True,
                  complete_PUBLICAX_coverage=True, raw_payload=payload.name, raw_extras=extras,
                  all_constant_values_omitted=True, retained_fields_uncapped=True)
    write("map-"+label+".json", result)
    print(label, json.dumps(counts, sort_keys=True))
    return result


def compare(base, head):
    a, b = base["names"], head["names"]
    common = set(a) & set(b)
    added = sorted(set(b)-set(a))
    removed = sorted(set(a)-set(b))
    assert base["all_constant_values_omitted"] and head["all_constant_values_omitted"]
    fields = ["owner", "kind", "private", "internal", "ci", "attributes", "axioms", "type_repr"]
    changes = {}
    for field in fields:
        if field.endswith("_repr"):
            changes[field] = sorted(n for n in common if a[n][field]["sha256"] != b[n][field]["sha256"])
        elif field == "axioms":
            changes[field] = sorted(n for n in common if set(a[n][field]) != set(b[n][field]))
        else:
            changes[field] = sorted(n for n in common if a[n][field] != b[n][field])
    public = {n for n in common if not a[n]["private"] and not b[n]["private"]}
    public_changes = {k: sorted(set(v)&public) for k,v in changes.items()}
    def rules(rows):
        return sorted(json.dumps(r,sort_keys=True,ensure_ascii=False) for r in rows)
    simp_changed = sorted(n for n in common if rules(base["simp_rules"].get(n,[])) != rules(head["simp_rules"].get(n,[])))
    ax_regression = {n: dict(before=a[n]["axioms"], after=b[n]["axioms"])
                     for n in common if (set(b[n]["axioms"])-STANDARD) - (set(a[n]["axioms"])-STANDARD)}
    added_nonstandard = {n:b[n]["axioms"] for n in added if set(b[n]["axioms"])-STANDARD}
    delta = dict(base=CONTEXT["base"],head=CONTEXT["head"],base_counts=base["counts"],head_counts=head["counts"],
                 added={n:b[n] for n in added},removed={n:a[n] for n in removed},
                 common_field_changes=changes,nonprivate_common_field_changes=public_changes,
                 simp_rule_changes=simp_changed,nonprivate_simp_rule_changes=sorted(set(simp_changed)&public),
                 axiom_regressions=ax_regression,added_nonstandard_axiom_constants=added_nonstandard,
                 added_private=sum(b[n]["private"] for n in added),removed_private=sum(a[n]["private"] for n in removed),
                 no_private_ID_normalization=True,
                 constant_values_omitted=True,
                 limits="Raw full type representations are retained losslessly in native gz/base64 logs. Hash indexes avoid duplicating large expressions. Constant values/proof values are omitted in both successful contexts, not truncated; no value-equality assertion is made. CI includes all structural kind-specific fields (including recursor rules); attributes include reflected simp rules/membership, instances, reducibility, protected, class, noncomputable, inline and match_pattern, plus source attribute commands separately. No assertion about arbitrary third-party custom attributes, unchanged legacy seals or post-MSG5 changes.")
    write("comparison.json",delta)
    print(json.dumps(dict(added=len(added),removed=len(removed),added_private=delta["added_private"],removed_private=delta["removed_private"],
                          common_change_counts={k:len(v) for k,v in changes.items()},nonprivate_change_counts={k:len(v) for k,v in public_changes.items()},
                          simp_rule_changes=len(simp_changed),axiom_regressions=len(ax_regression),added_nonstandard=len(added_nonstandard)),indent=2))


if sys.argv[1] == "compare":
    compare(json.loads((OUT/"map-Base.json").read_text()),json.loads((OUT/"map-Head.json").read_text()))
else:
    parse(*sys.argv[1:])
