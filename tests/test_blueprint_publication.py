from pathlib import Path
import tempfile
import unittest
from unittest.mock import patch
from scripts import blueprint_assemble as assemble


class PublicationTests(unittest.TestCase):
    @patch.object(assemble.dp, 'projects', return_value={'TCSlib': Path('/repo'), 'FABL': Path('/external')})
    def test_external_metadata_is_retained_but_never_published(self, _):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            (root / 'FABL').mkdir()
            external = root / 'FABL' / 'Chapter01.tex'
            external.write_text('Upstream dataset metadata')
            (root / 'BooleanAnalysis').mkdir()
            (root / 'BooleanAnalysis' / 'Basic.tex').write_text('TCSlib chapter')
            original = ('\\input{chapter/BooleanAnalysis/Basic.tex}\n'
                        '\\input{chapter/FABL/Chapter01.tex}\n')
            with patch.object(assemble, 'CHAPTER_DIR', root):
                self.assertEqual(assemble.all_chapter_files(), ['BooleanAnalysis/Basic.tex'])
            published = assemble.published_inputs(original)
            self.assertNotIn('chapter/FABL/', published)
            self.assertIn('chapter/BooleanAnalysis/Basic.tex', published)
            self.assertEqual(assemble.published_inputs(published), published)
            self.assertEqual(external.read_text(), 'Upstream dataset metadata')

    def test_current_publication_has_no_external_project_inputs(self):
        text = assemble.MAIN_TEX.read_text()
        self.assertFalse(any(assemble.dataset_only(rel) for rel in assemble.existing_inputs(text)))


if __name__ == '__main__':
    unittest.main()
