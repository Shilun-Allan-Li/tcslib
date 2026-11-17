import json
import tempfile
import time
import unittest
from dataclasses import replace
from pathlib import Path
from threading import Barrier, Lock
from unittest.mock import patch

from proofmatch.agents import AgentInvocationError
from proofmatch.budget import Budget
from proofmatch.chapter import map_upstream_candidates
from proofmatch.models import Candidate, DocumentBlock, DocumentIndex, UpstreamDeclaration
from proofmatch.upstream import UpstreamDeclarationLoader, map_upstream_batches


BLOCK = 'pdf-abcdef123456-p001-b001'


def declaration(name):
    return UpstreamDeclaration(name, 'lemma', 'True', 'T', (), 'by trivial')


def response(payload):
    return {'assignments': [dict(lean_name=row['lean_name'], relation='context',
                                document_blocks=[BLOCK], rationale='Used here.')
                            for row in payload['declarations']]}


class Agent:
    model = 'gpt-6-luna'
    backend = 'codex'

    def __init__(self):
        self.calls = 0

    def run(self, prompt, payload):
        self.calls += 1
        return response(payload)


class UpstreamOptimizationTests(unittest.TestCase):
    def setUp(self):
        self.block = DocumentBlock(BLOCK, 1, 1, 'prose', 'Title', 'Proof text', 1.)
        self.index = DocumentIndex('a' * 64, (self.block,), ())

    def test_four_workers_stable_order_and_cached_resume(self):
        barrier = Barrier(4)
        lock = Lock()
        active = peak = calls = 0

        class Worker(Agent):
            def run(worker, prompt, payload):
                nonlocal active, peak, calls
                with lock:
                    active += 1
                    calls += 1
                    peak = max(peak, active)
                barrier.wait(timeout=5)
                time.sleep(.01)
                with lock:
                    active -= 1
                return response(payload)

        candidates = [Candidate(f'T{i}', 'Title', 'T', 'Claim', 'True',
                                'by trivial', 1, 0., (BLOCK,)) for i in range(8)]
        inputs = {c.lean_name: ((declaration(f'{c.lean_name}.dep'),), (self.block,), ())
                  for c in candidates}
        with tempfile.TemporaryDirectory() as tmp:
            def run():
                return map_upstream_candidates(candidates, inputs, 'book.md', self.index,
                    Budget(), jobs=4, cache_dir=Path(tmp), agent_factory=Worker)
            results = run()
            self.assertEqual([r.theorem for r in results], [c.lean_name for c in candidates])
            self.assertEqual(peak, 4)
            self.assertEqual(calls, 8)
            self.assertEqual(run(), results)
            self.assertEqual(calls, 8)

    def test_partial_batches_survive_failed_request(self):
        declarations = (declaration('T.a'), declaration('T.b'))
        class Failing(Agent):
            def run(worker, prompt, payload):
                if payload['declarations'][0]['lean_name'] == 'T.b':
                    raise AgentInvocationError('quota')
                return super().run(prompt, payload)
        with tempfile.TemporaryDirectory() as tmp:
            cache = Path(tmp)
            with self.assertRaises(AgentInvocationError):
                map_upstream_batches(declarations, (self.block,), Failing(), Budget(),
                                     max_characters=1, cache_dir=cache)
            self.assertEqual(len(list(cache.glob('*.json'))), 1)
            agent = Agent()
            result = map_upstream_batches(declarations, (self.block,), agent, Budget(),
                                         max_characters=1, cache_dir=cache)
            self.assertEqual([r.lean_name for r in result], ['T.a', 'T.b'])
            self.assertEqual(agent.calls, 1)

    def test_cache_invalidates_for_inputs_model_backend_prompt_and_schema(self):
        import shutil
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            agent = Agent()
            agent.resource_root = root / 'resources'
            resources = Path(__file__).resolve().parents[2] / 'proofmatch'
            for directory in ['prompts', 'schemas']:
                (agent.resource_root / directory).mkdir(parents=True)
                shutil.copy(resources / directory / f'map_upstream.{"md" if directory == "prompts" else "json"}',
                            agent.resource_root / directory)
            cache = root / 'cache'
            def run(decl=None, block=None):
                return map_upstream_batches((decl or declaration('T.a'),),
                    (block or self.block,), agent, Budget(), cache_dir=cache)
            run(); run()
            self.assertEqual(agent.calls, 1)
            run(replace(declaration('T.a'), statement='False'))
            run(block=replace(self.block, markdown='Changed text'))
            agent.model = 'other-model'; run()
            agent.backend = 'other-backend'; run()
            prompt = agent.resource_root / 'prompts/map_upstream.md'
            prompt.write_text(prompt.read_text() + '\nNew instructions.')
            run()
            schema = agent.resource_root / 'schemas/map_upstream.json'
            schema.write_text(schema.read_text() + '\n')
            run()
            self.assertEqual(agent.calls, 7)

    def test_invalid_outputs_are_not_cached_and_corruption_is_recomputed(self):
        with tempfile.TemporaryDirectory() as tmp:
            cache = Path(tmp)
            agent = Agent()
            with patch.object(agent, 'run', return_value={'assignments': []}):
                with self.assertRaisesRegex(ValueError, 'missing declarations'):
                    map_upstream_batches((declaration('T.a'),), (self.block,), agent,
                                         Budget(), cache_dir=cache)
            self.assertEqual(list(cache.glob('*.json')), [])
            def run():
                return map_upstream_batches((declaration('T.a'),), (self.block,), agent,
                                            Budget(), cache_dir=cache)
            run()
            path = next(cache.glob('*.json'))
            path.write_text('{broken')
            run()
            self.assertEqual(agent.calls, 2)
            value = json.loads(path.read_text())
            value['assignments'][0]['document_blocks'] = ['unavailable']
            path.write_text(json.dumps(value))
            run()
            self.assertEqual(agent.calls, 3)

    def test_failure_stops_dispatch_but_saves_other_inflight_results(self):
        barrier = Barrier(4)
        class Worker(Agent):
            def run(worker, prompt, payload):
                barrier.wait(timeout=5)
                if payload['declarations'][0]['lean_name'] == 'T0.dep':
                    raise AgentInvocationError('quota')
                time.sleep(.03)
                return response(payload)
        candidates = [Candidate(f'T{i}', 'Title', 'T', 'Claim', 'True',
                                'by trivial', 1, 0., (BLOCK,)) for i in range(8)]
        inputs = {c.lean_name: ((declaration(f'{c.lean_name}.dep'),), (self.block,), ())
                  for c in candidates}
        with tempfile.TemporaryDirectory() as tmp:
            results = map_upstream_candidates(candidates, inputs, 'book.md', self.index,
                Budget(), jobs=4, cache_dir=Path(tmp), agent_factory=Worker)
            self.assertIsInstance(results[0], AgentInvocationError)
            self.assertEqual(len(list(Path(tmp).glob('*.json'))), 3)
            self.assertTrue(all(isinstance(r, Exception) for r in results[4:]))

    def test_loader_scans_dataset_and_builds_index_once(self):
        from io import StringIO
        rows = [dict(lean_name='T.a', proof_upstream_decls=['T.second', 'T.first']),
                dict(id='T.b', proof_upstream_decls=['T.first']),
                dict(lean_name='T.empty', proof_upstream_decls=[])]
        records = {name: dict(slice=['lemma dep : True :=', 'by trivial'], kind='lemma',
                             module='T', all_deps=[]) for name in ['T.first', 'T.second']}
        with tempfile.TemporaryDirectory() as tmp:
            graph = Path(tmp) / 'graph.json'
            graph.write_text('{"modules": {}}')
            with patch('proofmatch.upstream.open_dataset',
                       return_value=StringIO('\n'.join(map(json.dumps, rows)))) as opened, \
                    patch('scripts.build_dataset.build_index', return_value=records) as built:
                loader = UpstreamDeclarationLoader(Path('dataset'), graph,
                                                    ['T.a', 'T.b', 'T.empty'])
                for _ in range(3):
                    self.assertEqual([d.lean_name for d in loader.load('T.a')],
                                     ['T.second', 'T.first'])
                    self.assertEqual([d.lean_name for d in loader.load('T.b')], ['T.first'])
                with self.assertRaisesRegex(ValueError, 'has no proof_upstream_decls'):
                    loader.load('T.empty')
                with self.assertRaisesRegex(ValueError, 'absent'):
                    loader.load('missing')
                self.assertEqual(opened.call_count, 1)
                self.assertEqual(built.call_count, 1)
