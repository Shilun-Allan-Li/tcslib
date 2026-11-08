from pathlib import Path
import json,hashlib,shutil,subprocess,datetime
O=Path(__file__).parent;P=Path('/private/tmp/ab34-first-halt-full-boundary');pin=json.loads((O/'PIN.json').read_text());W=Path(pin['source_worktree']);g=lambda *a:subprocess.check_output(['git','-C',str(W),*a]);assert g('rev-parse','HEAD').decode().strip()==pin['HEAD'];assert not g('status','--porcelain','--untracked-files=no');assert g('rev-parse','refs/remotes/origin/codex/ab34-first-halt-reuse').decode().strip()==pin['HEAD']
for r in pin['owners']:assert hashlib.sha256((W/r['path']).read_bytes()).hexdigest()==r['HEAD_sha256']
foot=json.loads((O/'HEAD-FOOTPRINTS10.json').read_text());heads={q['name'] for r in foot for q in r['foreign_definition_mentions'] if q['ordinary_guard_target']};controls={r['name'] for r in json.loads((O/'boundary/ORDINARY-UNION22.json').read_text())};guards=json.loads((O/'boundary/CURRENT-GUARD-RECEIPTS10.json').read_text());assert len(heads)==22 and heads==controls=={n for r in guards for n in r['ordinary_heads']}
for f in ['DEFINITION-CATALOG.json','READER-CATALOG.json','FOREIGN-SOURCE-MAP.json']:
 shutil.copyfile(P/f,O/'boundary'/f)
prior=[]
for path,count,expected in [(Path('/private/tmp/ab34-first-halt-reuse-remaining/EXPORT'),710,'5941f738b0cbce46955b1ae6e7b6fb221805a713359a40b01466d9a0b3a457f1'),(P/'EXPORT-SAFE7',285,'8f3bd833c1931cee3fda456978da76a49560fd0cb552ff03f70567912d9cf7a4'),(P/'EXPORT-REPAIRS3',173,'b8f0997fa0c0a509afe3a9f04837f41e2f74c3ed319a2f0270a831d747e58f4c')]:
 digest=hashlib.sha256((path/'MANIFEST.json').read_bytes()).hexdigest();assert digest==expected;prior.append({'path':str(path),'payloads':count,'manifest_sha256':digest,'still_immutable':True})
(O/'IMMUTABLE-PRIOR-PACKETS.json').write_text(json.dumps(prior,indent=2)+'\n')
summary=f'''# Final FH ten-source QA and gate122 draft

PASS within the recorded source/selected-metadata/boundary scope at actual pushed clean HEAD {pin['HEAD']}, BASE {pin['BASE']}. This is not a gate verdict or merge-ready claim. Root owns the downstream replay,43-file final screen/lint, canonical adoption and publication; those results are not asserted here.

Actual final8 complete owner sources elaborate against whole MAC8 with zero errors and zero sorry warnings, capturing fresh full type/AX/footprints for10 roots. An actual independent BASE query reads the10 existing roots from the exact whole MAC8 input. Every selected full type Expr, universe parameter list and axiom set is exactly equal; all axiom sets are subsets of propext/Classical.choice/Quot.sound. Full expressions and pretty types are supplied, not only hashes. This is selected10 metadata, not whole-library/all-public-type/all-axiom equality.

All10 literal complete headers are exact, including statement-level lets and outer proof delimiters. The8 changed owners preserve all non-target code tokens and every import line. Source declaration census is106 public→106 and1288 private→1288, no names added/removed. Only8 of1003 Lean blobs differ. The seven held targets are restored in six entire owner files byte-exact BASE. Complete43-file BASE/HEAD population sources are retained, covering all current/canonical/helper/held sources and ordinary foreign-definition homes cited by this gate.

Current10 proof boundaries use actual previous guard executions and a fresh literal final-source context validity check; no historical execution is relabeled as newly run at finalHEAD. All preceding source, attrs/scoped opens and complete proof/header prefixes match exactly through each target; all current fresh ordinary footprints fit the guard sets. Root16's Nondeterminism owner later changes at17, so its binding correctly compares the entire prefix through16 rather than the whole later owner file. All8 final owners do literally match the previously frozen private final10 candidate owner map.

Footprint limits: start with each complete root type and proof, follow all reached constant types and same-owner ordinary definition helper values; do not follow imported/other local theorem proof values or foreign definition values. Guards cover ordinary reached foreign TCSlib heads, excluding kernel abbreviations/projections. Core/Mathlib explicit arguments are reviewed independently. Guard irreducibility and removal of registered definition simp/unfold rows are witnessed; source explicit simp/rw/unfold/delta arguments are independently reviewed. There is no global opacity/absence/legacy-waiver claim.

Retained union22 ordinary heads equals the44-control union. All44 positive reflected identities are kernel checked; all44 paired sealed rfl controls fail, with exactly44 expected errors and complete markers. Both controls disable smart unfolding for recursive runWith/body identities and erase Cfg.init/MultiTapeTM.initCfg definition simp rows. No transparency override. Initial42positive attempt is honestly retained. Final17/47/54 reader repairs use existing published theorem readers only; exact before/after bodies and original native receipts remain. ClockMachine is a mechanical colleague-file repair; Seyoon sends the FYI without @mention. No message has been sent by this agent.

CURRENT-DISPOSITIONS17 keeps all original fronts explicit: ten current PASS within scope, seven restored BASE fronts HOLD. Bounded census18 supplies17 inspected consumers plus canonical, without an exhaustive absence claim. Full old held source scopes/logs are supplied; no new public API/import/header/home/route or debt acknowledgment is inferred. No sorries were filled, no new mathematical result/host introduced, and no actual source/Git/canonical/cache/snapshot mutation was performed by this agent. Plain approved helper invocations requested no compiled output. Whole MAC8 remains895 objects with identical post-check hashes.

Source-only helper scripts, exact inputs and complete logs are retained. Failed BASE-query syntax and initial read-only context-binding assumptions are separately preserved; neither is a proof failure. Original710, safe285 and repair173 payload packets remain immutable with manifest hashes reverified.

Gate draft is in gate-draft/pack.DRAFT.md with scope10 and all current anchor/helper source inputs. Required final root-owned replay/screen/lint/publication fields are explicit staging placeholders. It is not dispatched and must not be issued until root fills those complete current records. The draft chooses no new user decision; all morning audits were assigned Codex by Seyoon.

Frozen UTC: {datetime.datetime.now(datetime.timezone.utc).isoformat()}. All own Lean jobs are complete.
''';(O/'REVIEW.md').write_text(summary)
E=O/'EXPORT';assert not E.exists();E.mkdir()
for f in sorted(O.iterdir()):
 if f.name in {'live','EXPORT'}:continue
 if f.is_dir():shutil.copytree(f,E/f.name)
 elif f.is_file():shutil.copyfile(f,E/f.name)
assert not any(f.is_symlink() or f.name.endswith('.lean') for f in E.rglob('*'))
files=sorted(f for f in E.rglob('*') if f.is_file());m=[{'path':str(f.relative_to(E)),'bytes':f.stat().st_size,'sha256':hashlib.sha256(f.read_bytes()).hexdigest()} for f in files];(E/'MANIFEST.json').write_text(json.dumps({'payloads':len(m),'bytes':sum(r['bytes'] for r in m),'files':m},indent=2)+'\n');(E/'SHA256SUMS').write_text(''.join(r['sha256']+'  '+r['path']+'\n' for r in m))
for r in m:
 f=E/r['path'];assert f.stat().st_size==r['bytes'] and hashlib.sha256(f.read_bytes()).hexdigest()==r['sha256']
print(json.dumps({'export':str(E),'payloads':len(m),'bytes':sum(r['bytes'] for r in m),'review_sha256':hashlib.sha256((E/'REVIEW.md').read_bytes()).hexdigest(),'manifest_sha256':hashlib.sha256((E/'MANIFEST.json').read_bytes()).hexdigest(),'sha256sums_sha256':hashlib.sha256((E/'SHA256SUMS').read_bytes()).hexdigest(),'gate_draft_sha256':hashlib.sha256((E/'gate-draft/pack.DRAFT.md').read_bytes()).hexdigest(),'all_payload_hashes_verified':True},indent=2))
