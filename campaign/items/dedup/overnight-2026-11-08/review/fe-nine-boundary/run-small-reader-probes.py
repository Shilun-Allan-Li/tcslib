from pathlib import Path
import subprocess,sys
B=Path(__file__).resolve().parent
for label,file,scope in [
 ('17-Cfg-id-existing-reader-sealed','CfgIdFieldReader.lean','Routine Cfg identity solely through existing mapState_eq_of_fields, with Cfg.mapState hidden'),
 ('18-OfWords-existing-readers-sealed','OfWordsFieldReaders.lean','Routine canonical seam record reconstruction through existing five field readers, with Cfg.ofWords hidden'),
 ('19-InputLength-input-symbol-native','InputLengthInputSymbolReader.lean','Full exact owner copy with only endSymbol body changed to existing inputSymbol_of_end; no header/import/API changes'),
 ('20-InputLength-input-symbol-sealed','InputLengthInputSymbolReaderSealed.lean','Same hypothetical InputLength repair under whole target11-head boundary; returnScan remains expected unresolved')]:
    subprocess.run([sys.executable,'-I',str(B/'run-check.py'),label,file,scope],check=True)
