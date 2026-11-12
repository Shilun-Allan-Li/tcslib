"""Publication structure and byte-preservation regressions (no LLM/cache writes)."""
import json
from pathlib import Path
import tempfile
import unittest
from unittest.mock import patch

from scripts import blueprint_assemble as a
from scripts import blueprint_structure as s
from scripts import blueprint_stub as stub
from scripts.blueprint_enumerate import organization_metadata


class OrganizationTests(unittest.TestCase):
    def setUp(self):
        self.tmp = tempfile.TemporaryDirectory()
        self.addCleanup(self.tmp.cleanup)
        self.root = Path(self.tmp.name)
        self.manifest = self.root / 'organization.json'
        self.data = {'schema_version': 1, 'parts': [
            {'id': 'analysis', 'title': 'Analysis', 'chapters': [
                {'id': 'fourier', 'title': 'Fourier analysis',
                 'modules': ['A/Basic.tex', 'A/More.tex']}]}]}
        for rel in ['A/Basic.tex', 'A/More.tex']:
            p = self.root / rel
            p.parent.mkdir(exist_ok=True)
            p.write_text('\\chapter{Old}\n\\section{Overview}\nIntro.\n'
                         '\\section{Declarations}\n\\begin{lemma}\n'
                         f'\\lean{{{p.stem}}}\n\\label{{{p.stem}}}\n'
                         '\\leanok\n\\uses{upstream}\nClaim.\n\\end{lemma}\n')
        self.save()
        self.patches = [patch.object(a, 'CHAPTER_DIR', self.root),
                        patch.object(a, 'MAIN_TEX', self.root / 'main.tex'),
                        patch.object(a.dp, 'projects', return_value={'TCSlib': self.root, 'FABL': self.root / 'external'})]
        for p in self.patches:
            p.start()
            self.addCleanup(p.stop)

    def save(self):
        self.manifest.write_text(json.dumps(self.data))

    def load(self):
        return a.load_manifest(self.manifest)

    def test_completeness_and_duplicate_rejection(self):
        self.assertEqual(len(a.module_chapters(self.load())), 2)
        modules = self.data['parts'][0]['chapters'][0]['modules']
        modules.pop()
        self.save()
        with self.assertRaisesRegex(ValueError, 'Unassigned published module A/More.tex'):
            self.load()
        modules.extend(['A/More.tex', 'A/Basic.tex'])
        self.save()
        with self.assertRaisesRegex(ValueError, 'Duplicate module A/Basic.tex'):
            self.load()

    def test_missing_file_and_duplicate_ids(self):
        self.data['parts'][0]['chapters'][0]['modules'].append('A/Missing.tex')
        self.data['parts'][0]['chapters'][0]['id'] = 'analysis'
        self.save()
        with self.assertRaisesRegex(ValueError, 'duplicate stable id'):
            self.load()
        with self.assertRaisesRegex(ValueError, 'missing or excluded module A/Missing.tex'):
            self.load()

    def test_new_module_requires_explicit_assignment(self):
        (self.root / 'A/New.tex').write_text('New module')
        with self.assertRaisesRegex(ValueError, 'add it to a chapter'):
            self.load()
        self.assertFalse((self.root / 'main.tex').exists())

    def test_order_idempotency_and_heading_only_preservation(self):
        original = {rel: (self.root / rel).read_text() for rel in a.all_chapter_files()}
        self.assertEqual(a.assemble(False, self.manifest), 0)
        output = {p: p.read_bytes() for p in self.root.rglob('*.tex')}
        self.assertEqual(a.assemble(False, self.manifest), 0)
        self.assertEqual(a.assemble(True, self.manifest), 0)
        self.assertEqual(output, {p: p.read_bytes() for p in self.root.rglob('*.tex')})
        publication = s.resolve_inputs(self.root)
        self.assertEqual(publication['sequence'], ['textbook/fourier.tex', 'A/Basic.tex', 'A/More.tex'])
        self.assertFalse(publication['repeated'])
        self.assertEqual(a.all_chapter_files(), sorted(original))
        for rel, text in original.items():
            after = (self.root / rel).read_text()
            self.assertEqual(s.without_headings(text), s.without_headings(after))
            self.assertEqual(s.file_record(text)['entry_hashes'], s.file_record(after)['entry_hashes'])
            self.assertNotIn('\\chapter', after)
            self.assertNotIn('\\subsection{Overview}', after)

    def test_manifest_order_overrides_alphabetical_order(self):
        self.data['parts'][0]['chapters'][0]['modules'].reverse()
        self.save()
        a.assemble(False, self.manifest)
        self.assertEqual(s.resolve_inputs(self.root)['sequence'],
                         ['textbook/fourier.tex', 'A/More.tex', 'A/Basic.tex'])

    def test_nested_inputs_are_published_once(self):
        parent = self.root / 'A/Basic.tex'
        parent.write_text(parent.read_text() + '\\input{chapter/A/More}\n')
        a.assemble(False, self.manifest)
        published = s.resolve_inputs(self.root)
        self.assertEqual(published['sequence'], ['textbook/fourier.tex', 'A/Basic.tex', 'A/More.tex'])
        self.assertFalse(published['repeated'])
        self.assertNotIn('A/More.tex', (self.root / 'textbook/fourier.tex').read_text())

    def test_nested_cycle_rejected_before_writes(self):
        for src, dest in [('Basic', 'More'), ('More', 'Basic')]:
            p = self.root / f'A/{src}.tex'
            p.write_text(p.read_text() + f'\\input{{chapter/A/{dest}.tex}}\n')
        with self.assertRaisesRegex(ValueError, 'cycles'):
            a.assemble(False, self.manifest)
        self.assertFalse((self.root / 'main.tex').exists())

    def test_cross_chapter_nested_input_is_actionable(self):
        chapter = self.data['parts'][0]['chapters'][0]
        chapter['modules'].pop()
        self.data['parts'][0]['chapters'].append(
            {'id': 'second', 'title': 'Second chapter', 'modules': ['A/More.tex']})
        self.save()
        p = self.root / 'A/Basic.tex'
        p.write_text(p.read_text() + '\\input{chapter/A/More.tex}\n')
        with self.assertRaisesRegex(ValueError, 'same chapter'):
            a.assemble(False, self.manifest)

    def test_external_metadata_excluded_and_untouched(self):
        external = self.root / 'FABL/Chapter01.tex'
        external.parent.mkdir()
        external.write_text('Dataset only: \\chapter{External}')
        a.assemble(False, self.manifest)
        self.assertNotIn('FABL/Chapter01.tex', s.resolve_inputs(self.root)['sequence'])
        self.assertEqual(external.read_text(), 'Dataset only: \\chapter{External}')
        self.data['parts'][0]['chapters'][0]['modules'].append('FABL/Chapter01.tex')
        self.save()
        with self.assertRaisesRegex(ValueError, 'excluded module'):
            self.load()

    def test_balanced_headings_and_prose_preservation(self):
        text = ('\\chapter{A {nested} title}\nIntro $x$.\n'
                '\\section{Results $\\{x\\}$}\n\\subsection{Details}\nMore.\n')
        normalized = s.normalize_headings(text, 'A/Topic/Basic.tex')
        self.assertEqual(s.without_headings(text), s.without_headings(normalized))
        self.assertIn('\\section{Topic --- Foundations}', normalized)
        self.assertIn('\\subsubsection{Details}', normalized)
        self.assertEqual(normalized, s.normalize_headings(normalized, 'A/Topic/Basic.tex'))

    def test_preservation_audit_detects_prose_and_metadata_changes(self):
        (self.root / 'main.tex').write_text('\\input{chapter/A/Basic.tex}\n\\input{chapter/A/More.tex}\n')
        baseline = s.snapshot(self.root)
        a.assemble(False, self.manifest)
        self.assertEqual(s.verify_snapshot(self.root, baseline)['modules'], 2)
        for before, after in [('Claim.', 'Changed claim.'), ('upstream', 'different'), ('Basic}', 'Other}')]:
            p = self.root / 'A/Basic.tex'
            text = p.read_text()
            p.write_text(text.replace(before, after))
            with self.assertRaisesRegex(ValueError, 'changed'):
                s.verify_snapshot(self.root, baseline)
            p.write_text(text)

    def test_generated_module_and_appended_headings(self):
        unit = {'area': 'A', 'module': 'TCSlib.A.New', 'chapter_title': 'New',
                'target_tex': 'blueprint/src/chapter/A/New.tex',
                'decls': [{'name': 'new', 'env': 'lemma'}]}
        header = stub.chapter_header(unit)
        self.assertIn('\\section{New}', header)
        self.assertNotIn('\\chapter', header)
        self.assertNotIn('Overview', header)
        # Exercise the actual writer, not just its template.
        with patch.object(stub, 'BASE', self.root):
            stub.write_unit(unit, False)
            path = self.root / unit['target_tex']
            unit['decls'] = [{'name': 'another', 'env': 'lemma'}]
            stub.write_unit(unit, False)
            unit['decls'] = [{'name': 'third', 'env': 'lemma'}]
            stub.write_unit(unit, False)
            text = path.read_text()
            self.assertEqual(text.count('\\section{'), 1)
            self.assertEqual(text.count('\\subsection*{'), 1)
            self.assertEqual(text.count('\\lean{'), 3)

    def test_current_checkout_manifest_and_preservation(self):
        # Restore the real checkout paths while checking the shipped artifact.
        root = a.BASE / 'blueprint/src/chapter'
        with patch.object(a, 'CHAPTER_DIR', root):
            data = a.load_manifest(a.MANIFEST)
        assigned = a.module_chapters(data)
        self.assertEqual(len(assigned), len(set(assigned)))
        publication = s.resolve_inputs(root)
        self.assertFalse(publication['missing'] + publication['repeated'] + publication['cycles'])
        self.assertEqual(set(assigned), {r for r in publication['sequence'] if not r.startswith('textbook/')})
        hyper = next(p for p in data['parts'] if p['id'] == 'hypercontractivity')
        self.assertEqual(len(hyper['chapters']), 6)
        metadata = organization_metadata('blueprint/src/chapter/BooleanAnalysis/Hypercontractivity/Parameters.tex')
        self.assertEqual(metadata['organization_chapter'], 'sharp-hypercontractivity')
        self.assertIsNone(organization_metadata('blueprint/src/chapter/A/New.tex')['organization_chapter'])


if __name__ == '__main__':
    unittest.main()
