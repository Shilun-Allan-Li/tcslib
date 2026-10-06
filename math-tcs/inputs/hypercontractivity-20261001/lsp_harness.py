"""Use the shared harness with fresh, hash-bound Lean LSP check evidence.
No Lean subprocess is launched. All checks are supplied by lean_diagnostic_messages
and lean_verify on separate candidate files before task attempt / task apply.
"""
import argparse, json, sys
from pathlib import Path
sys.path.insert(0, '/home/owenm/.codex/plugins/cache/math-tcs-local/math-tcs/0.2.0/scripts')
from mathtcs import harness
from mathtcs.axioms import DEFAULT_ALLOWLIST, verdict
from mathtcs.util import sha256_text, MathTcsError
parser = argparse.ArgumentParser()
parser.add_argument('action', choices=['prepare', 'attempt', 'apply'])
parser.add_argument('task')
parser.add_argument('--input', type=Path)
parser.add_argument('--evidence', type=Path)
parser.add_argument('--output', type=Path)
args = parser.parse_args()
root = Path.cwd()
state = harness.status(root, args.task)
if args.action == 'prepare':
    candidate = state['template'].replace(harness.SLOT, harness.proof_term(args.input.read_text())) if args.input else state['attempts'][-1]['candidate']
    args.output.write_text(candidate)
    print(json.dumps({'file_path':str(args.output.resolve()), 'source_sha256':sha256_text(candidate), 'declaration':state['declaration']}))
else:
    evidence = json.loads(args.evidence.read_text())
    def lsp_check(check_root, candidate, names, timeout=120):
        path = Path(evidence['file_path'])
        if check_root != root or names != [state['declaration']] or evidence['declaration'] != names[0] or sha256_text(candidate) != evidence['source_sha256'] or path.read_text() != candidate:
            raise MathTcsError('LSP evidence does not match the exact candidate')
        if evidence['phase'] != args.action:
            raise MathTcsError('acceptance requires a separate LSP check')
        diag_response = evidence['diagnostics']
        axiom_response = evidence['verification']
        diagnostics = diag_response.get('structuredContent', {}).get('result', {})
        verification = axiom_response.get('structuredContent', {})
        messages = diagnostics.get('items', [])
        compiled = not diag_response.get('isError', False) and diagnostics.get('success') is True and not diagnostics.get('partial', False) and not diagnostics.get('timed_out', False) and not diagnostics.get('failed_dependencies') and not any(d['severity']=='error' for d in messages)
        axioms = verification.get('axioms')
        verified = compiled and not axiom_response.get('isError', False) and isinstance(axioms,list) and verdict(axioms)['trusted']
        return {'schema':'plain-check/v1','backend':'lean-lsp','ok':verified,'compiled':compiled,'source_sha256':sha256_text(candidate),'declarations':{names[0]:{'axioms':axioms,'verified':verified}},'allowlist':list(DEFAULT_ALLOWLIST),'diagnostics':messages,'timeout':diagnostics.get('timed_out', False),'evidence_file':str(args.evidence.resolve()),'source_file':str(path),'phase':args.action}
    harness.check_text = lsp_check
    if args.action == 'attempt':
        result = harness.attempt(root, args.task, args.input.read_text())
    else:
        result = harness.apply(root, args.task)
    print(json.dumps({'id':result['id'],'status':result['status'],'attempts':len(result['attempts']),'axioms':result.get('acceptance_check',result['attempts'][-1]['check'])['declarations'][state['declaration']]['axioms']}))
