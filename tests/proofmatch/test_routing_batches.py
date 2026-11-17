import json
import subprocess
from pathlib import Path
import tempfile
import unittest
from unittest.mock import patch

from proofmatch.agents import Agent, AgentInvocationError, AgentOutputError
from proofmatch.budget import Budget
from proofmatch.models import Candidate, DocumentBlock, DocumentIndex
from proofmatch.routing import ChapterNode, route_chapters, route_declarations
from proofmatch.routing_batches import MAX_ROUTING_CHARS, cached_route, payload_chars, routing_payloads


class FakeRouter:
    backend = 'codex'
    model = 'test'
    def __init__(self):
        self.calls = []
        self.fail_at = None
        self.omit = False
    def run(self, prompt, payload):
        self.calls.append(payload)
        if len(self.calls) == self.fail_at:
            raise RuntimeError('interrupted')
        positive = any(block['block_id'] == 'late' for block in payload['document']['blocks'])
        if prompt == 'route_chapters':
            rows = [{'chapter_key': row['chapter_key'], 'selected': positive,
                     'confidence': .9, 'rationale': 'Shared mathematics.'}
                    for row in payload['chapters']]
            return {'chapters': rows[:-1] if self.omit else rows}
        return {'declarations': [
            {'lean_name': row['lean_name'], 'tier': 'proves' if positive else 'unrelated',
             'document_blocks': ['late'] if positive else [], 'rationale': 'An argument.'}
            for row in payload['declarations']]}


def small_payloads(*args, **kwargs):
    kwargs['max_chars'] = 4500
    return routing_payloads(*args, **kwargs)


class RoutingBatchTests(unittest.TestCase):
    def document(self):
        return DocumentIndex('a' * 64, tuple(
            DocumentBlock('late' if i == 11 else f'b{i}', i + 1, 1, 'prose', '',
                          'Mathematics. ' * 60, 1.) for i in range(12)), ())

    def nodes(self):
        return tuple(ChapterNode(Path(f'chapter-{i}.tex'), 'Area', f'Title {i}',
                                 'Overview. ' * 50, (f'T{i}',), ()) for i in range(7))

    def test_oversized_document_and_catalog_cover_every_pair_with_bounded_envelopes(self):
        profile = {'headings': ['A document'], 'omitted_block_count': 0,
                   'blocks': [{'block_id': str(i), 'text': 'α' * 700} for i in range(700)]}
        rows = [{'chapter_key': str(i), 'overview': 'A' * 700} for i in range(1200)]
        self.assertGreater(payload_chars({'document': profile, 'chapters': rows}), 1_048_576)
        seen = set()
        agent = Agent(model='test', backend='codex')
        for payload in routing_payloads(profile, rows, 'chapters'):
            self.assertLessEqual(payload_chars(payload), MAX_ROUTING_CHARS)
            envelope = agent._envelope((agent.resource_root / 'prompts/route_chapters.md').read_text(), payload, ())
            self.assertLess(len(envelope), 1_048_576)
            for block in payload['document']['blocks']:
                for row in payload['chapters']:
                    pair = (block['block_id'], row['chapter_key'])
                    self.assertNotIn(pair, seen)
                    seen.add(pair)
        self.assertEqual(len(seen), 700 * 1200)

    def test_late_matches_survive_and_successful_batches_resume_without_repeating_calls(self):
        agent = FakeRouter()
        agent.fail_at = 2
        with tempfile.TemporaryDirectory() as tmp, patch('proofmatch.routing.routing_payloads', small_payloads):
            cache = Path(tmp)
            with self.assertRaisesRegex(RuntimeError, 'interrupted'):
                route_chapters(self.document(), self.nodes(), agent, Budget(), model='test', cache_dir=cache)
            completed = agent.calls[0]
            agent.calls = []
            agent.fail_at = None
            selected = route_chapters(self.document(), self.nodes(), agent, Budget(), model='test', cache_dir=cache)
            self.assertEqual(set(selected), set(self.nodes()))
            self.assertNotIn(completed, agent.calls)
            agent.calls = []
            budget = Budget()
            again = route_chapters(self.document(), self.nodes(), agent, budget, model='test', cache_dir=cache)
            self.assertEqual(again, selected)
            self.assertEqual(agent.calls, [])
            self.assertEqual(budget.spent_usd, 0)

    def test_declaration_matches_are_merged_across_all_segments(self):
        agent = FakeRouter()
        node = self.nodes()[0]
        catalog = {'T0': Candidate('T0', 'Title', 'T', 'Statement', 'Formal', 'Proof', 1, 0., ())}
        with patch('proofmatch.routing.routing_payloads', small_payloads):
            routed, rejected = route_declarations(self.document(), node, catalog, lambda: agent,
                                                   Budget(), model='test')
        self.assertEqual(rejected, ())
        self.assertEqual(len(routed), 1)
        self.assertEqual(routed[0].tier, 'proves')
        self.assertEqual(routed[0].document_blocks, ('late',))

    def test_persistently_incomplete_answers_stop_without_caching_a_complete_batch(self):
        agent = FakeRouter(); agent.omit = True
        with tempfile.TemporaryDirectory() as tmp:
            cache = Path(tmp)
            with self.assertRaisesRegex(AgentOutputError, 'remain unresolved'):
                route_chapters(self.document(), self.nodes()[:1], agent, Budget(), model='test', cache_dir=cache)
            self.assertEqual(len(agent.calls), 2)
            self.assertEqual(len(list(cache.glob('*.partial.json'))), 1)
            self.assertEqual(len(list(cache.glob('*.json'))), 1)

    def test_omitted_duplicate_and_unknown_block_rows_are_retried_individually(self):
        class RecoveringRouter(FakeRouter):
            def run(self, prompt, payload):
                result = super().run(prompt, payload)
                if len(self.calls) == 1:
                    result['declarations'] = [
                        {'lean_name': 'T0', 'tier': 'states', 'document_blocks': ['late'], 'rationale': 'Valid.'},
                        {'lean_name': 'T2', 'tier': 'proves', 'document_blocks': ['invented'], 'rationale': 'Bad block.'},
                        {'lean_name': 'T3', 'tier': 'unrelated', 'document_blocks': [], 'rationale': 'Duplicate.'},
                        {'lean_name': 'T3', 'tier': 'unrelated', 'document_blocks': [], 'rationale': 'Duplicate.'}]
                return result
        node = ChapterNode(Path('test.tex'), 'Area', 'Test', '', tuple(f'T{i}' for i in range(4)), ())
        catalog = {name: Candidate(name, 'Title', 'T', 'Statement', 'Formal', 'Proof', 1, 0., ())
                   for name in node.lean_names}
        agent = RecoveringRouter()
        with tempfile.TemporaryDirectory() as tmp:
            cache = Path(tmp)
            routed, rejected = route_declarations(self.document(), node, catalog, lambda: agent,
                                                   Budget(), model='test', cache_dir=cache)
            self.assertEqual(rejected, ())
            self.assertEqual(len(routed), 4)
            self.assertEqual(routed[0].tier, 'states')
            self.assertEqual([[r['lean_name'] for r in p['declarations']] for p in agent.calls],
                             [['T0', 'T1', 'T2', 'T3'], ['T1'], ['T2'], ['T3']])
            self.assertTrue(all(r.document_blocks == ('late',) for r in routed))
            agent.calls = []
            again = route_declarations(self.document(), node, catalog, lambda: agent,
                                        Budget(), model='test', cache_dir=cache)
            self.assertEqual(again, (routed, rejected))
            self.assertEqual(agent.calls, [])

    def test_interruption_preserves_valid_rows_and_resume_requests_only_missing_rows(self):
        class PartialRouter(FakeRouter):
            def run(self, prompt, payload):
                result = super().run(prompt, payload)
                if len(self.calls) == 1:
                    result['chapters'] = result['chapters'][:1]
                return result
        agent = PartialRouter(); agent.fail_at = 2
        with tempfile.TemporaryDirectory() as tmp:
            cache = Path(tmp)
            with self.assertRaisesRegex(RuntimeError, 'interrupted'):
                route_chapters(self.document(), self.nodes()[:3], agent, Budget(), model='test', cache_dir=cache)
            saved = json.loads(next(cache.glob('*.partial.json')).read_text())
            self.assertEqual(len(saved['rows']), 1)
            original_calls = len(agent.calls)
            agent.fail_at = None
            selected = route_chapters(self.document(), self.nodes()[:3], agent, Budget(), model='test', cache_dir=cache)
            self.assertEqual(set(selected), set(self.nodes()[:3]))
            retried = [row['chapter_key'] for payload in agent.calls[original_calls:] for row in payload['chapters']]
            self.assertNotIn(self.nodes()[0].key, retried)

    def test_quota_errors_are_never_retried(self):
        class UnavailableRouter(FakeRouter):
            def run(self, prompt, payload):
                self.calls.append(payload)
                raise AgentInvocationError('spend cap')
        agent = UnavailableRouter()
        with self.assertRaisesRegex(AgentInvocationError, 'spend cap'):
            route_chapters(self.document(), self.nodes(), agent, Budget(), model='test')
        self.assertEqual(len(agent.calls), 1)

    def test_real_adapter_requires_exact_keys_and_restricts_evidence_in_shared_schema(self):
        observed = []
        def runner(command, **kwargs):
            schema = json.loads(Path(command[command.index('--output-schema') + 1]).read_text())
            observed.append(schema)
            keys = schema['properties']['decisions']['required']
            allowed = schema['$defs']['decision']['properties']['document_blocks']['items']['enum']
            answer = {'decisions': {key: {'tier': 'states', 'document_blocks': [allowed[0]],
                                         'rationale': 'Corresponding statement.'} for key in keys}}
            Path(command[command.index('--output-last-message') + 1]).write_text(json.dumps(answer))
            return subprocess.CompletedProcess(command, 0, '{"type":"turn.completed"}\n', '')
        agent = Agent(model='gpt-6-luna', backend='codex', runner=runner)
        node = self.nodes()[0]
        catalog = {'T0': Candidate('T0', 'Title', 'T', 'Statement', 'Formal', 'Proof', 1, 0., ())}
        routed, rejected = route_declarations(self.document(), node, catalog, lambda: agent, Budget(), model='gpt-6-luna')
        self.assertEqual(rejected, ())
        self.assertEqual(routed[0].document_blocks, ('b0',))
        self.assertEqual(observed[0]['properties']['decisions']['required'], ['T0'])
        self.assertEqual(observed[0]['properties']['decisions']['additionalProperties'], False)
        self.assertEqual(observed[0]['properties']['decisions']['properties']['T0'], {'$ref': '#/$defs/decision'})


if __name__ == '__main__':
    unittest.main()
