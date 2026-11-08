import gzip
from pathlib import Path
import tempfile
import unittest
from scripts.dataset_extraction_cache import ensure_extraction, publish_mirror


class ExtractionCacheTests(unittest.TestCase):
    def test_input_changes_corruption_modes_and_resume(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp); external = root / 'upstream'
            paths = [root/'TCSlib/Test.lean', external/'FABL/Test.lean', root/'dep_graph.json',
                     root/'blueprint/src/chapter/FABL/Test.tex', root/'blueprint/src/references/book.md',
                     root/'blueprint/src/references/informalized/Test.md', root/'scripts/build_dataset.py',
                     root/'proofmatch/blueprint.py', external/'lean-toolchain', external/'lake-manifest.json']
            for path in paths:
                path.parent.mkdir(parents=True, exist_ok=True); path.write_text('original')
            calls = []
            def build(path):
                calls.append(path)
                raw = b'{"id":"T.foo"}\n'
                path.write_bytes(raw)
                with gzip.open(str(path)+'.gz', 'wb') as out: out.write(raw)
            def ensure(flags=()):
                return ensure_extraction(root, {'TCSlib':root,'FABL':external}, root/'cache', flags, build)
            output = ensure(); self.assertEqual(len(calls),1)
            ensure(); self.assertEqual(len(calls),1)
            for path in paths:
                before = len(calls); path.write_text(path.read_text()+' changed')
                ensure(); ensure()
                self.assertEqual(len(calls),before+1, str(path))
            # Outputs must be content-verified, not trusted by size or timestamp.
            before = len(calls); output.write_bytes(b'{"id":"T.bar"}\n')
            ensure(); self.assertEqual(len(calls),before+1)
            statements = ensure(['--no-proof'])
            self.assertNotEqual(output, statements)
            before = len(calls); ensure(); self.assertEqual(len(calls),before)
            # Raw OCR and rejected notes are not read by the builder.
            for path in [root/'blueprint/src/references/book.raw.md',
                         root/'blueprint/src/references/informalized/rejected/Test.md']:
                path.parent.mkdir(parents=True,exist_ok=True); path.write_text('ignored')
            ensure(); self.assertEqual(len(calls),before)
            publish_mirror(output, root/'pass1.jsonl')
            self.assertEqual((root/'pass1.jsonl').read_bytes(),output.read_bytes())
            with gzip.open(root/'pass1.jsonl.gz','rb') as stream:
                self.assertEqual(stream.read(),output.read_bytes())
            ensure(['--only','T.foo']); self.assertEqual(len(calls),before+1)

    def test_interrupted_or_changing_input_build_is_never_cached(self):
        with tempfile.TemporaryDirectory() as tmp:
            root=Path(tmp); (root/'TCSlib').mkdir(); source=root/'TCSlib/Test.lean'; source.write_text('v1')
            def interrupted(path):
                path.write_text('partial')
                raise RuntimeError('interrupted')
            with self.assertRaisesRegex(RuntimeError,'interrupted'):
                ensure_extraction(root,{'TCSlib':root},root/'cache',[],interrupted)
            self.assertFalse(list((root/'cache').glob('*.receipt.json')))
            def changed(path):
                path.write_text('data')
                with gzip.open(str(path)+'.gz','wt') as out: out.write('data')
                source.write_text('v2')
            with self.assertRaisesRegex(RuntimeError,'changed during extraction'):
                ensure_extraction(root,{'TCSlib':root},root/'cache',[],changed)
            self.assertFalse(list((root/'cache').glob('*.receipt.json')))

    def test_headless_citation_stage_forwards_workers_and_skips_redundant_dry_run(self):
        from types import SimpleNamespace
        from unittest.mock import patch
        from scripts.dataset_pipeline import stage_citations
        class Runner:
            args=SimpleNamespace(jobs=4,yes=True,estimate=False,dry_run=False,max_cost=None,allow_weak_models=False)
            env={}
            calls=[]
            def stage_model(self,stage): return 'gpt-6-luna'
            def run(self,stage,command,**kwargs): self.calls.append(command); return 0
            def confirm(self,*args): return True
            def py(self,*args,**kwargs): return 0
            def mark(self,*args,**kwargs): pass
        runner=Runner()
        with patch('scripts.dataset_pipeline.documents_to_match',return_value=([Path('book.md')],[])), \
             patch('scripts.dataset_pipeline.pass1'), patch('scripts.dataset_pipeline.coverage'):
            stage_citations(runner,[])
        self.assertEqual(len(runner.calls),1)
        self.assertIn('--jobs',runner.calls[0])
        self.assertEqual(runner.calls[0][runner.calls[0].index('--jobs')+1],'4')
        self.assertNotIn('--dry-run',runner.calls[0])


if __name__ == '__main__': unittest.main()
