"""Classify saved search logs individually. No Lean, processes, git or evidence edits."""
from pathlib import Path
from collections import Counter
from datetime import datetime,timezone
import hashlib,json,re,csv
repo=Path('/Users/seyoonr/.codex/worktrees/io-sprg/tcslib-exchange')
out=Path('/private/tmp/io-sprg-proof-notes/M1CheckpointDraft')
rows=[]
for p in sorted((repo/'evidence/overlap/probes').glob('*/search.json')):
 s=json.loads(p.read_text())
 for item in s['searches']:
  mode=item['mode'];log=p.parent/(mode+'.log');source=p.parent/(mode+'.lean.txt')
  if not log.exists()or not source.exists():continue
  text=log.read_text();r=item['run']
  source_text=source.read_text()
  proof_start=re.search(r':=\s*by\b',source_text)
  proof_line=source_text.count('\n',0,proof_start.end())+1 if proof_start else None
  error_lines=[(int(m[1]),m[3]) for m in re.finditer(r'^.*?:(\d+):(\d+):\s*error:\s*(.*)$',text,re.M)]
  header_errors=[(n,msg) for n,msg in error_lines if proof_line is not None and n<proof_line and not any(t in msg for t in ('timeout','heartbeats','maximum recursion depth'))]
  flags={
   'goal_or_header_elaboration_error':bool(header_errors),
   'harness_unknown_scope':bool(re.search(r'unknown (namespace|scope).*BigOperators',text)),
   'heartbeat_or_search_timeout':any(t in text for t in(
      'maximum number of heartbeats','deterministic timeout','running out of time',
      'maximum recursion depth')),
   'suggestion_elaboration_failed':'found a partial proof, but the corresponding tactic failed'in text,
   'clean_apply_no_hit':"apply? didn't find any relevant lemmas"in text,
   'exact_did_not_close':'`exact?` could not close the goal'in text,
   'has_suggestion':'Try this:'in text,
  }
  if flags['harness_unknown_scope']:kind='HARNESS_SCOPE_ERROR'
  elif flags['goal_or_header_elaboration_error']:kind='HARNESS_STATEMENT_ELABORATION_ERROR'
  elif r['rc']==r['errors']==r['sorry']==0:kind='CLOSED'
  elif flags['heartbeat_or_search_timeout']:kind='BOUNDED_SEARCH_TIMEOUT_NOT_ABSENCE'
  elif mode=='apply'and r['rc']==r['errors']==0 and r['sorry']:kind='PARTIAL_SUGGESTION_NOT_PROOF'
  elif flags['suggestion_elaboration_failed']:kind='SUGGESTION_ELABORATION_FAILED_NOT_ABSENCE'
  elif flags['clean_apply_no_hit']:kind='COMPLETED_APPLY_NO_HIT_NOT_GLOBAL_ABSENCE'
  elif flags['exact_did_not_close']:kind='COMPLETED_EXACT_NO_CLOSING_PROOF'
  elif mode=='apply'and r['rc']==r['errors']==0 and r['sorry']:kind='PARTIAL_SUGGESTION_NOT_PROOF'
  else:kind='OTHER_DIAGNOSTIC_REVIEW_REQUIRED'
  rows.append({'goal':s.get('goal',p.parent.name),'mode':mode,'automatic_status':item['status'],
   'semantic_status':kind,'flags':flags,'proof_start_line':proof_line,'header_errors':header_errors,'rc':r['rc'],'errors':r['errors'],'sorry':r['sorry'],
   'log':str(log.relative_to(repo)),
   'saved_log_sha256_matches':hashlib.sha256(log.read_bytes()).hexdigest()==r['log_sha256'],
   'saved_source_sha256_matches':hashlib.sha256(source.read_bytes()).hexdigest()==r['source_sha256']})
result={'status':'STATIC_LOG_REVIEW_NOT_NEW_SEARCH','captured_utc':datetime.now(timezone.utc).isoformat(),
 'saved_search_count':len(rows),'semantic_counts':dict(Counter(r['semantic_status']for r in rows)),
 'caveat':'Pattern classification is per immutable saved log. Unknown diagnostics require manual review; automatic DIAGNOSTIC_FAILURE is not one mathematical outcome.',
 'rows':rows}
(out/'overlap-log-review.json').write_text(json.dumps(result,indent=2)+'\n')
with(out/'overlap-log-review.tsv').open('w')as f:
 w=csv.writer(f,delimiter='\t');w.writerow(['goal','mode','automatic_status','semantic_status','rc','errors','sorry','log','hashes_match'])
 for r in rows:w.writerow([r[k]for k in('goal','mode','automatic_status','semantic_status','rc','errors','sorry','log')]+[r['saved_log_sha256_matches']and r['saved_source_sha256_matches']])
print(json.dumps({'saved_search_count':len(rows),'semantic_counts':result['semantic_counts'],
 'hash_mismatches':sum(not(r['saved_log_sha256_matches']and r['saved_source_sha256_matches'])for r in rows)}))
