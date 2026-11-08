"""Strictly verify all successful staged metadata, retaining exact compiler identities."""
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


def read(label, version):
    stem = label + "-" + version
    receipt = json.loads((OUT / (stem + "-run.json")).read_text())
    assert receipt["exit"] == receipt["errors"] == receipt["warnings"] == 0
    assert receipt["owner_artifacts_unchanged"] and receipt["input_still_exact"]
    payload = (OUT / (stem + ".out.gz.b64")).read_bytes()
    assert sha(payload) == receipt["base64_sha256"]
    compressed = base64.decodebytes(payload)
    assert sha(compressed) == receipt["gzip_sha256"]
    raw = gzip.decompress(compressed)
    assert len(raw) == receipt["raw_utf8_bytes"] and sha(raw) == receipt["raw_utf8_sha256"]
    assert sha((OUT / ("Metadata-" + version + ".lean.txt")).read_bytes()) == receipt["input_sha256"]
    return raw.decode("utf-8"), receipt


def axmap(raw, tag, proof=False):
    pattern = r"^" + tag + (r"\|([^|\n]+)\|kind=([^|\n]+)\|\[([^\]]*)\]" if proof else r"\|([^|\n]+)\|\[([^\]]*)\]")
    result = {}
    for match in re.finditer(pattern, raw, re.M):
        n = match[1]
        assert n not in result
        ax = [x.strip() for x in match[3 if proof else 2].split(",") if x.strip()]
        assert len(ax) == len(set(ax))
        result[n] = dict(kind=match[2], axioms=ax) if proof else ax
    return result


def primary(label):
    raw, receipt = read(label, "census-v1")
    census = {}
    for match in re.finditer(r"^CONSTANT (\S+) module=(\S+) kind=(\S+) private=(true|false) internal=(true|false)$", raw, re.M):
        n, owner, kind, private, internal = match.groups()
        assert n not in census
        census[n] = dict(owner=owner, kind=kind, private=private == "true", internal=internal == "true")
    allax = axmap(raw, "ALLAX")
    publicax = axmap(raw, "PUBLICAX")
    proofax = axmap(raw, "PROOFAX", True)
    roots = {}
    for match in re.finditer(r"^ROOT\|([^|\n]+)\|private=(true|false)$", raw, re.M):
        n, private = match.groups()
        assert n not in roots and private == "true"
        roots[n] = dict(private=True)
    assert len(roots) == 16
    assert set(allax) == set(census)
    assert set(publicax) == {n for n, r in census.items() if not r["private"]}
    assert all(publicax[n] == allax[n] for n in publicax)
    selected = {n for n in census if any(n == r or n.startswith(r + ".") for r in roots)}
    assert set(proofax) == selected
    assert f"COMPLETE|constants={len(census)}|roots=16" in raw.splitlines()
    assert {r["owner"] for r in census.values()} == set((OUT / "original9-owners.txt").read_text().splitlines())
    for n, row in census.items():
        row["axioms"] = allax[n]
    for n, row in roots.items():
        assert census[n]["kind"] == "theorem" and census[n]["private"]
        row.update(owner=census[n]["owner"], axioms=allax[n],
                   descendants=sorted(x for x in proofax if x.startswith(n + ".")))
    assert all(proofax[n]["kind"] == census[n]["kind"] and proofax[n]["axioms"] == allax[n] for n in proofax)
    nonstandard = {n:r for n,r in census.items() if set(r["axioms"])-STANDARD}
    counts = dict(total=len(census), private=sum(r["private"] for r in census.values()),
                  nonprivate=sum(not r["private"] for r in census.values()), roots=len(roots),
                  root_descendants=len(proofax)-len(roots), nonstandard_axiom_constants=len(nonstandard),
                  selected_standard=all(set(r["axioms"]) <= STANDARD for r in proofax.values()))
    data = dict(label=label, commit=receipt["context_commit"], census=census, roots=roots, proof_axes=proofax,
                nonstandard_axioms=nonstandard, counts=counts, allax_exact_coverage=True, publicax_exact_coverage=True,
                owner_artifacts=receipt["owner_artifacts_before"])
    write("primary-"+label+".json",data)
    print(label, "primary", json.dumps(counts,sort_keys=True))
    return data


def complete(label):
    data = primary(label)
    census = data["census"]
    raw, receipt = read(label, "types-v1")
    markers = list(re.finditer(r"^(TYPE_REPR|TYPECOMPLETE)\|([^|\n]+)(?:\|)?", raw, re.M))
    assert markers and markers[-1][1] == "TYPECOMPLETE"
    assert markers[-1][2] == "constants="+str(len(census))
    types = {}
    for i, marker in enumerate(markers[:-1]):
        assert marker[1] == "TYPE_REPR"
        n = marker[2]
        assert n in census and n not in types
        value = raw[marker.end():markers[i+1].start()].removesuffix("\n")
        types[n] = dict(sha256=sha(value.encode()), utf8_bytes=len(value.encode()), block=i,
                        raw_payload=label+"-types-v1.out.gz.b64")
    assert set(types) == set(census)
    raw, receipt = read(label, "ciattrs-v1")
    ci, attrs, rules = {}, {}, collections.defaultdict(list)
    for line in raw.splitlines():
        if line.startswith(("CI|","ATTR|","SIMP_RULE|")):
            tag,n,value = line.split("|",2)
            assert n in census
            value = json.loads(value)
            if tag == "SIMP_RULE":
                rules[n].append(value)
            else:
                target = ci if tag == "CI" else attrs
                assert n not in target
                target[n] = value
    assert set(ci) == set(attrs) == set(census)
    assert f"CICOMPLETE|constants={len(census)}|simp_environment_unchanged=true" in raw.splitlines()
    assert "SIMPCOMPLETE" in raw.splitlines()
    for n, row in census.items():
        row.update(ci=ci[n], attributes=attrs[n], type_repr=types[n])
    data.update(simp_rules=dict(rules), complete_type_coverage=True, complete_CI_coverage=True,
                complete_reflected_attribute_coverage=True, constant_value_bodies_omitted=True,
                retained_fields_uncapped=True, private_names_not_normalized=True)
    data["counts"]["simp_rules"] = sum(map(len,rules.values()))
    data["counts"]["raw_type_utf8_bytes"] = sum(r["utf8_bytes"] for r in types.values())
    write("map-"+label+".json",data)
    print(label,"complete",json.dumps(data["counts"],sort_keys=True))
    return data


def compare():
    base=json.loads((OUT/"map-Base.json").read_text());head=json.loads((OUT/"map-Head.json").read_text())
    a,b=base["census"],head["census"];common=set(a)&set(b)
    added=sorted(set(b)-set(a));removed=sorted(set(a)-set(b))
    fields=["owner","kind","private","internal","ci","attributes","type_repr","axioms"]
    changes={}
    for field in fields:
        if field=="type_repr": changes[field]=sorted(n for n in common if a[n][field]["sha256"]!=b[n][field]["sha256"])
        elif field=="axioms": changes[field]=sorted(n for n in common if set(a[n][field])!=set(b[n][field]))
        else: changes[field]=sorted(n for n in common if a[n][field]!=b[n][field])
    public={n for n in common if not a[n]["private"] and not b[n]["private"]}
    public_changes={k:sorted(set(v)&public) for k,v in changes.items()}
    norm=lambda rows: sorted(json.dumps(r,sort_keys=True,ensure_ascii=False) for r in rows)
    simpchanges=sorted(n for n in common if norm(base["simp_rules"].get(n,[]))!=norm(head["simp_rules"].get(n,[])))
    axgrowth={n:sorted(set(b[n]["axioms"])-set(a[n]["axioms"])) for n in common if set(b[n]["axioms"])-set(a[n]["axioms"])}
    badgrowth={n:axes for n,axes in axgrowth.items() if set(axes)-STANDARD}
    badadd={n:b[n]["axioms"] for n in added if set(b[n]["axioms"])-STANDARD}
    owner_counts={}
    for owner in (OUT/"original9-owners.txt").read_text().splitlines():
        owner_counts[owner]={label:dict(total=sum(r["owner"]==owner for r in rows.values()),
                                        private=sum(r["owner"]==owner and r["private"] for r in rows.values()),
                                        nonprivate=sum(r["owner"]==owner and not r["private"] for r in rows.values()),
                                        kinds=dict(collections.Counter(r["kind"] for r in rows.values() if r["owner"]==owner)))
                             for label,rows in [("base",a),("head",b)]}
    result=dict(base=CONTEXT["base"],head=CONTEXT["head"],base_counts=base["counts"],head_counts=head["counts"],
                added={n:b[n] for n in added},removed={n:a[n] for n in removed},owner_counts=owner_counts,
                added_private=sum(b[n]["private"] for n in added),removed_private=sum(a[n]["private"] for n in removed),
                common_field_changes=changes,nonprivate_common_field_changes=public_changes,
                simp_rule_changes=simpchanges,nonprivate_simp_rule_changes=sorted(set(simpchanges)&public),
                axiom_set_growth=axgrowth,nonstandard_axiom_regressions=badgrowth,added_nonstandard_axioms=badadd,
                nonstandard_name_sets_equal=set(base["nonstandard_axioms"])==set(head["nonstandard_axioms"]),
                retained_fields_uncapped=True,constant_value_bodies_omitted=True,private_names_not_normalized=True,
                limits="ConstantInfo value/proof bodies are omitted. Raw types are complete, including cache/hygiene fields, retained losslessly as UTF-8 gzip/base64. CI retains structural fields including recursor rules. Reflected attribute scope is explicit in probe, with source attributes separately frozen; arbitrary custom extension state is not claimed. Source exports are distinct from generated nonprivate compiler constants. No new legacy seal or gate closure is claimed.")
    write("comparison-staged.json",result)
    print(json.dumps(dict(added=len(added),removed=len(removed),added_private=result["added_private"],removed_private=result["removed_private"],
                          common_change_counts={k:len(v) for k,v in changes.items()},nonprivate_change_counts={k:len(v) for k,v in public_changes.items()},
                          nonprivate_simp_rule_changes=len(result["nonprivate_simp_rule_changes"]),axiom_set_growth=len(axgrowth),
                          nonstandard_axiom_regressions=len(badgrowth),added_nonstandard_axioms=len(badadd)),indent=2))


if sys.argv[1]=="primary": primary(sys.argv[2])
elif sys.argv[1]=="complete": complete(sys.argv[2])
elif sys.argv[1]=="compare": compare()
else: raise ValueError(sys.argv[1:])
