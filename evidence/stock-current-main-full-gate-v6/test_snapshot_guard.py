from pathlib import Path
import importlib.util,subprocess,tempfile,unittest,json,hashlib
D=Path(__file__).resolve().parent
spec=importlib.util.spec_from_file_location('mixed_snapshot',D/'harness-patches/scripts/check-stock-mixed-integration.py');module=importlib.util.module_from_spec(spec);spec.loader.exec_module(module)
class SnapshotGuard(unittest.TestCase):
    def test_real_tree_blob_and_altered_source(self):
        repository=Path('/home/lee/clifv');revision='45a70ee6e405d0a5e590603c320ec28799595f45';relative='README.md'
        blob=subprocess.check_output(['git','rev-parse',revision+':'+relative],cwd=repository,text=True).strip()
        source=subprocess.check_output(['git','cat-file','blob',blob],cwd=repository)
        with tempfile.TemporaryDirectory(prefix='fv-snapshot-guard-test-') as tmp:
            root=Path(tmp);path=root/relative;path.write_bytes(source)
            module.verify_snapshot_files(root,{relative:blob},{})
            path.write_bytes(source+b'\naltered source\n')
            with self.assertRaisesRegex(AssertionError,'Snapshot source changed'):module.verify_snapshot_files(root,{relative:blob},{})
    def test_revision_tree_manifest_mismatch_rejected(self):
        repository=Path('/home/lee/clifv');revision='45a70ee6e405d0a5e590603c320ec28799595f45'
        harness=D/'harness-patches/scripts/check-stock-mixed-integration.py'
        with tempfile.TemporaryDirectory(prefix='fv-snapshot-tree-test-') as tmp:
            root=Path(tmp);manifest=root/'manifest.json'
            manifest.write_text(json.dumps({'view':str(root),'source_repository':str(repository),
                'revision':revision,'tree':'0'*40,'execution_harness':{'path':str(harness),
                'sha256':hashlib.sha256(harness.read_bytes()).hexdigest()}}))
            with self.assertRaisesRegex(AssertionError,'Snapshot revision/tree mismatch'):
                module.snapshot_revision(root,manifest)
    def test_compiler_source_exception_rejected(self):
        with self.assertRaisesRegex(AssertionError,'Unexpected operational'):module.verify_snapshot_files(Path('/unused'),{}, {'FV/Backend.lean':{}})
if __name__=='__main__':unittest.main()
