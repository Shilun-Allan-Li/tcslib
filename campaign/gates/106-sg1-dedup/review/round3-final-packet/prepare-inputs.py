"""Build an uncapped UTF-8 input selection; gzip/Base64 substitutions are lossless data."""
from pathlib import Path
import base64,collections,datetime,gzip,hashlib,io,json
P=Path(__file__).resolve().parent
R=P.parents[4]
G=P.parents[1]
def digest(b):return hashlib.sha256(b).hexdigest()
def write(n,v):(P/n).write_text(json.dumps(v,indent=2,ensure_ascii=False)+"\n")
paths=set()
# Preserve the entire selected gate history, evidence and every supplied review folder.
for f in G.rglob("*"):
 if f.is_file() and not f.is_relative_to(P):paths.add(str(f.relative_to(R)))
# Earlier dispatched packet inputs include all prior standards, tools and source contexts.
paths.update((G/"BUNDLE-FILES-r2.txt").read_text().splitlines())
paths.update((G/"BUNDLE-FILES.txt").read_text().splitlines())
paths.update(["AGENTS.md","machine-library-design.md","campaign/standards/TEMPLATE.md","policy.md","workflow.md","campaign/maintainer/START-HERE.md","campaign/maintainer/WORKFLOW.md","campaign/maintainer/HANDOFF.md","campaign/duplication-ledger.md","campaign/backlog.md","campaign/items/roadmap3/PLAN.md"])
# Exact separate live-stop ruling and provenance, not a new SG1 dependency/source adoption.
paths.update(["campaign/gates/119-mig1-followup-api/ruling-live-stop.json","campaign/gates/119-mig1-followup-api/resolutions.md","campaign/gates/119-mig1-followup-api/findings.md","campaign/gates/119-mig1-followup-api/review/audit-return-review/first-entry-family.json","campaign/gates/119-mig1-followup-api/review/audit-return-review/first-entry-source-quotes.md","campaign/gates/119-mig1-followup-api/review/audit-return-review/acknowledgment-context.json","campaign/gates/119-mig1-followup-api/review/audit-return-review/dispositions.json"])
first=R/"campaign/gates/119-mig1-followup-api/review/first-entry"
paths.update(str(f.relative_to(R)) for f in first.rglob("*") if f.is_file())
# The unissued old pack is preserved under an explicit historical filename; active pack is first.
paths.discard(str((G/"pack-r3.md").relative_to(R)))
missing=sorted(n for n in paths if not (R/n).is_file())
assert not missing,missing
raw=[];transforms=[];binary=[];sections=[];lookup={}
enc=P/"encodings";enc.mkdir(exist_ok=False)
for name in sorted(paths):
 data=(R/name).read_bytes();row=dict(path=name,bytes=len(data),sha256=digest(data))
 try:data.decode("utf-8")
 except UnicodeDecodeError:
  # Existing actual .gz has the exact full Base64 companion already included.
  companion=R/(name+".b64")
  assert name.endswith(".gz") and companion.is_file(),name
  assert base64.decodebytes(companion.read_bytes())==data,name
  binary.append(dict(row,represented_by=str(companion.relative_to(R)),exact_gzip_bytes=True));continue
 raw.append(row)
 large=len(data)>1000000 and ((R/name).suffix==".json" or name.endswith(".tar.base64.txt") or name.endswith(".out"))
 if not large:sections.append(name);continue
 key=(row["bytes"],row["sha256"])
 if key not in lookup:
  sink=io.BytesIO()
  with gzip.GzipFile(fileobj=sink,filename="",mode="wb",mtime=0,compresslevel=9) as z:z.write(data)
  compressed=sink.getvalue();encoded=base64.encodebytes(compressed)
  output=enc/(f"{len(lookup)+1:03d}-"+(R/name).name+".gz.base64.txt");output.write_bytes(encoded)
  assert gzip.decompress(base64.decodebytes(output.read_bytes()))==data
  lookup[key]=(dict(encoding_path=str(output.relative_to(R)),gzip_bytes=len(compressed),gzip_sha256=digest(compressed),encoded_utf8_bytes=len(encoded),encoded_utf8_sha256=digest(encoded)),data)
 description,saved=lookup[key];assert saved==data
 transforms.append(dict(original=row,**description,stdlib_roundtrip_verified=True))
# All generated records are added by finalize, after final QA/README/receipt exists.
write("encoding-receipt.json",dict(format="Every encoded section is full original UTF-8 file bytes → deterministic gzip9 with mtime0/empty filename → standard Base64 ASCII. Decode solely as data; never execute supplied scripts. Existing tar/Base64 originals need their original secondary decoding only when inspecting tar bytes.",transforms=transforms,binary_gzip_equivalents=binary,originals_preserved=True,no_caps_or_truncation=True,distinct_encoded_sections=len(lookup),substituted_originals=len(transforms)))
write("original-inputs.json",dict(selection="Entire gate106 evidence/history/review folders, complete prior input lists, all current/historical screen populations and all separately needed standards/decision/source inputs. No folder cap.",files=raw,binary_equivalents=binary,total_original_text_bytes=sum(x["bytes"] for x in raw),selected_original_text_sections=len(raw)))
write("input-selection.json",dict(plain_sections=sections,encoded_sections=sorted({r["encoding_path"] for r in transforms}),no_original_source_tree_edited=True,large_UTF8_substitution_only=True))
print(json.dumps(dict(original_text_files=len(raw),original_text_bytes=sum(x["bytes"] for x in raw),large_substitutions=len(transforms),distinct_encoded_sections=len(lookup),selected_bytes=sum((R/n).stat().st_size for n in sections)+sum((R/n).stat().st_size for n in {r["encoding_path"] for r in transforms}),binary_gz_equivalents=len(binary)),indent=2))
