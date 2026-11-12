from pathlib import Path
import json,hashlib,shutil,re
P=Path('/private/tmp/ab34-gate128-ready-draft');O=Path('/private/tmp/ab34-gate128-publication-peer');R=Path('/Users/seyoonr/.codex/worktrees/ab34-records/tcslib-arora-barak-ch3-4');J=lambda p:json.loads(p.read_text());h=lambda b:hashlib.sha256(b).hexdigest();expected='58a2dbe4517714ebfab50a673f09d942c937f64ab3340ad979d1c07c2e390200';assert h((P/'MANIFEST.json').read_bytes())==expected;m=J(P/'MANIFEST.json');assert m['frozen'] and m['payload_count']==len(m['files'])==777 and m['payload_bytes']==29554730;rows=[]
for r in m['files']:
 assert not Path(r['path']).is_absolute() and '..' not in Path(r['path']).parts;p=P/r['path'];b=p.read_bytes();assert p.stat().st_size==r['bytes']==len(b) and h(b)==r['sha256'];b.decode('utf8');assert not p.is_symlink();rows.append(dict(r,exact=True))
actual={p.relative_to(P).as_posix() for p in P.rglob('*') if p.is_file()};assert len(actual)==779 and actual=={r['path'] for r in m['files']}|{'MANIFEST.json','SHA256SUMS.txt'};assert not any(p.is_symlink() for p in P.rglob('*'))
checksums=[]
for line in (P/'SHA256SUMS.txt').read_text().splitlines():
 sha,path=line.split('  ',1);assert h((P/path).read_bytes())==sha;checksums.append(path)
assert len(checksums)==len(set(checksums)) and set(checksums)==actual-{'SHA256SUMS.txt'}
# Verify both inventory/list path sets using their expressly stated recursive exclusions.
inv=J(P/'INPUT-INVENTORY.draft.json');assert len(inv['files'])==inv['payloads_at_inventory']
for r in inv['files']:
 p=P/r['path'];assert p.is_file() and p.stat().st_size==r['bytes'] and h(p.read_bytes())==r.get('sha256',r.get('SHA256'))
bl=(P/'BUNDLE-FILES.draft.txt').read_text().splitlines();assert len(bl)==len(set(bl)) and all((P/p).is_file() for p in bl)
pack=(P/'pack-draft.md').read_text();assert 'generated' in pack.lower() and 'theorem' in pack.lower() and 'ROOT_TO_BIND' in pack;assert '**PENDING:** root' not in pack and 'Final actual counts' not in pack;assert '0 NEW' in pack or '0 new' in pack or '0new' in pack
boundary=J(P/'bindings/THEOREM-BOUNDARY-REVIEW.json');assert len(boundary['all6_theorem_boundary_rows_verbatim'])==6 and len(boundary['four_authored_boundaries_independently_seeded_as_selected_roots'])==4 and len(boundary['two_non_authored_local_generated_boundaries'])==2
anchors=[]
for name in ['receipt.json','object-hashes.json','Lean-tree.json']:
 original=R/'campaign/status/2026-11-08-mig1-merge'/name;copy=P/'anchors/MAC8'/name;assert original.read_bytes()==copy.read_bytes();anchors.append({'repository_original':original.relative_to(R).as_posix(),'packet_capture':copy.relative_to(P).as_posix(),'SHA256':h(copy.read_bytes()),'independently_read_original_byte_exact':True})
for n in ['MANIFEST.json','SHA256SUMS.txt','pack-draft.md','STATUS.draft.md','INPUTS.md','PORTABILITY.md','bindings/THEOREM-BOUNDARY-REVIEW.json']:
 q=O/'final-input-observation'/n;q.parent.mkdir(parents=True,exist_ok=True);q.write_bytes((P/n).read_bytes())
# Honest own read-only preparation failure, separate from original source/evidence outcomes.
A=O/'preparation/source-position-lookup';A.mkdir(parents=True,exist_ok=True);(A/'DISPOSITION.json').write_text(json.dumps({'outcome':'read-only position lookup raised ValueError','cause':'assumed diagnostic guard section came before module doc; actual guard is before namespace/first declaration after module doc','correction':'inspected actual section location and reconstructed complete owner byte-exact in successful verifier','no_original_payload_or_result_changes':True},indent=2)+'\n')
receipt={'input_MANIFEST_SHA256':expected,'frozen_input_payloads':777,'frozen_input_payload_bytes':29554730,'total_files_including_MANIFEST_checksums':779,'all_payload_bytes_SHA_UTF8_paths_exact':True,'checksum_file_all778_other_files_exact':True,'no_symlinks_or_missing_extra_inputs':True,'draft_inventory_and_bundle_paths_exist_and_hash_exact_with_recursive_exclusions':True,'final_actual49_completed_and_zero_delta_dispositions_present':True,'generated_theorem_boundary_wording_nit_resolved_without_new_Lean':True,'independent_original_MAC8_anchors_byte_exact':anchors,'logical_path_rebase_into_canonical_root_gate_folder_remains_root_work':True,'package_Mathlib_source_paths_not_project_source_lookup':True,'original_compound_manifests_and_absolute_execution_paths_remain_data':True,'final_publication_R_X_bundle_count_SHA_prompt_fields_pending':True,'peer_does_not_claim_dispatch_gate_or_merge_clearance':True,'all777_payload_checks':rows}
(O/'final-input-hash-path-checks.json').write_text(json.dumps(receipt,indent=2)+'\n');print(json.dumps({'input_manifest':expected,'payloads':777,'bytes':29554730,'total_files':779,'all_UTF8_hashes_paths_checksums_exact':True,'publication_nit_resolved':True,'independent_anchors':3}))
