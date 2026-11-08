from concurrent.futures import ThreadPoolExecutor
from decimal import Decimal
from pathlib import Path
from threading import Barrier, Lock
import tempfile
import time
import unittest
from unittest.mock import patch

from proofmatch.budget import Budget, BudgetExceeded, StageEstimate
from proofmatch.parallel import bounded_map
from proofmatch.routing import ChapterNode, RoutedDeclaration, route_chapters
from proofmatch.chapter import compare_relevant_candidates, routed_candidates
from proofmatch.models import Candidate, DocumentBlock, DocumentIndex, RelevanceDecision


class ParallelTests(unittest.TestCase):
    def test_worker_limit_order_and_fail_fast(self):
        lock=Lock(); barrier=Barrier(4); active=0; peak=0; calls=[]
        def work(i):
            nonlocal active,peak
            with lock: active+=1; peak=max(peak,active); calls.append(i)
            barrier.wait(timeout=5)
            time.sleep(.005*(4-i%4))
            with lock: active-=1
            return i*2
        self.assertEqual(bounded_map(work,range(8),4),[i*2 for i in range(8)])
        self.assertEqual(peak,4)
        calls=[]; barrier=Barrier(4)
        def fail(i):
            calls.append(i); barrier.wait(timeout=5)
            if i==0: raise RuntimeError('terminal failure')
            time.sleep(.03)
            return i
        with self.assertRaisesRegex(RuntimeError,'terminal failure'):
            bounded_map(fail,range(30),4)
        self.assertEqual(set(calls),{0,1,2,3})

    def test_budget_reservations_are_atomic(self):
        budget=Budget(Decimal('3'))
        estimate=StageEstimate('request',1,1,Decimal('1'))
        def reserve(_):
            try: budget.require(estimate); return True
            except BudgetExceeded: return False
        with ThreadPoolExecutor(max_workers=16) as pool:
            successes=list(pool.map(reserve,range(100)))
        self.assertEqual(sum(successes),3)
        self.assertEqual(budget.spent_usd,Decimal('3'))

    def test_chapter_routing_really_uses_four_concurrent_workers(self):
        barrier=Barrier(4); lock=Lock(); active=0; peak=0
        class Router:
            def run(self,prompt,payload):
                nonlocal active,peak
                with lock: active+=1; peak=max(peak,active)
                barrier.wait(timeout=5)
                with lock: active-=1
                return {'chapters':[{'chapter_key':r['chapter_key'],'selected':True,
                                     'confidence':1.,'rationale':'Shared mathematics.'}
                                    for r in payload['chapters']]}
        nodes=tuple(ChapterNode(Path(f'{i}.tex'),'Area','Title','',(),()) for i in range(480))
        index=DocumentIndex('a'*64,(DocumentBlock('b',1,1,'prose','','Text',1.),),())
        result=route_chapters(index,nodes,Router(),Budget(),model='test',jobs=4)
        self.assertEqual(set(result),set(nodes)); self.assertEqual(peak,4)

    def test_comparisons_use_four_workers_then_reuse_validated_results(self):
        barrier=Barrier(4); lock=Lock(); active=0; peak=0; calls=[]
        class Comparer:
            model='test'; backend='codex'
            def run(self,prompt,payload):
                nonlocal active,peak
                name=payload['lean']['lean_name']
                with lock: active+=1; peak=max(peak,active); calls.append(name)
                barrier.wait(timeout=5)
                with lock: active-=1
                return dict(lean_name=name,document_blocks=['b'],verdict='same',confidence=1.,
                            differences=[],evidence=[],pdf_outline=[],lean_outline=[])
        index=DocumentIndex('a'*64,(DocumentBlock('b',1,1,'prose','','Text',1.),),())
        candidates=tuple(Candidate(f'T{i}','Title','T','Claim','True','by trivial',1,0.,('b',)) for i in range(8))
        decisions=tuple(RelevanceDecision(c.lean_name,'relevant',('b',),'Claim') for c in candidates)
        with tempfile.TemporaryDirectory() as tmp:
            result=compare_relevant_candidates(candidates,decisions,index,Comparer,Budget(),jobs=4,cache_dir=Path(tmp))
            self.assertEqual([r.lean_name for r in result],[c.lean_name for c in candidates])
            self.assertEqual(peak,4); self.assertEqual(len(calls),8)
            budget=Budget(); again=compare_relevant_candidates(candidates,decisions,index,Comparer,budget,jobs=4,cache_dir=Path(tmp))
            self.assertEqual(again,result); self.assertEqual(len(calls),8); self.assertEqual(budget.spent_usd,0)

    def test_declaration_routing_parallelizes_chapters_without_nested_pools(self):
        barrier=Barrier(4); lock=Lock(); active=0; peak=0
        index=DocumentIndex('a'*64,(DocumentBlock('b',1,1,'prose','','Text',1.),),())
        nodes=tuple(ChapterNode(Path(f'{i}.tex'),'Area','Title','',(f'T{i}',),()) for i in range(4))
        candidates=tuple(Candidate(f'T{i}','Title','T','Claim','True','by trivial',1,0.,('b',)) for i in range(4))
        def route(index,node,*args,**kwargs):
            nonlocal active,peak
            with lock: active+=1; peak=max(peak,active)
            barrier.wait(timeout=5)
            with lock: active-=1
            return (RoutedDeclaration(node.lean_names[0],'proves',('b',),'Proof'),), ()
        with patch('proofmatch.chapter.build_blueprint_tree',return_value=nodes), \
             patch('proofmatch.chapter.load_blueprint_entries',return_value={}), \
             patch('proofmatch.chapter.route_chapters',return_value=nodes), \
             patch('proofmatch.chapter.route_declarations',side_effect=route):
            routed,_,_,_=routed_candidates(index,candidates,Path('/repo/blueprint/src/chapter'),Budget(),jobs=4)
        self.assertEqual(peak,4)
        self.assertEqual([c.lean_name for c in routed],[c.lean_name for c in candidates])

    def test_comparison_cache_invalidates_changed_proof_text_and_prompt(self):
        import shutil
        from dataclasses import replace
        from proofmatch.compare import compare_candidate
        calls=[]
        class Comparer:
            model='test'; backend='codex'
            def run(self,prompt,payload):
                calls.append(payload)
                return dict(lean_name='T',document_blocks=['b'],verdict='same',confidence=1.,
                            differences=[],evidence=[],pdf_outline=[],lean_outline=[])
        index=DocumentIndex('a'*64,(DocumentBlock('b',1,1,'prose','','Text',1.),),())
        candidate=Candidate('T','Title','T','Claim','True','by trivial',1,0.,('b',))
        with tempfile.TemporaryDirectory() as tmp:
            root=Path(tmp); agent=Comparer(); agent.resource_root=root/'resources'
            source=Path(__file__).resolve().parents[2]/'proofmatch'
            for directory in ['prompts','schemas']:
                (agent.resource_root/directory).mkdir(parents=True)
                shutil.copy2(source/directory/'compare.md' if directory=='prompts' else source/directory/'compare.json',
                             agent.resource_root/directory/('compare.md' if directory=='prompts' else 'compare.json'))
            options={'cache_dir':root/'cache'}
            compare_candidate(candidate,index,agent,Budget(),**options)
            compare_candidate(candidate,index,agent,Budget(),**options)
            self.assertEqual(len(calls),1)
            changed=replace(candidate,proof='by exact True.intro')
            compare_candidate(changed,index,agent,Budget(),**options)
            self.assertEqual(len(calls),2)
            (agent.resource_root/'prompts/compare.md').write_text('Revised comparison instructions')
            compare_candidate(changed,index,agent,Budget(),**options)
            self.assertEqual(len(calls),3)


if __name__ == '__main__': unittest.main()
