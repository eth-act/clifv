"""Checks the experimental oracle's renaming and refusal boundary."""
import copy,importlib.util,pathlib,unittest
spec=importlib.util.spec_from_file_location('probe',pathlib.Path(__file__).with_name('register-alignment-probe.py'));p=importlib.util.module_from_spec(spec);spec.loader.exec_module(p)
def fixture():
 return {'name':'f','entry':0,'vregs':'ifii','blocks':[{'insts':[0,2],'succs':[1],'preds':[],'params':[0]},{'insts':[2,3],'succs':[],'preds':[0],'params':[2]}], 'insts':[{'kind':'other','clobbers':[],'ops':[{'v':0,'k':'def','p':'late','c':'fixed:x0'}]}, {'kind':'branch','clobbers':['x30'],'ops':[{'v':1,'k':'use','p':'early','c':'reg'},{'v':3,'k':'def','p':'late','c':'reuse:0'}],'args':[[3]]}, {'kind':'ret','clobbers':[],'ops':[{'v':2,'k':'use','p':'early','c':'fixed:x0'}]}]}
class NumberingTests(unittest.TestCase):
 def test_identity(self):
  f=fixture();self.assertEqual(p.remap(f,dict(enumerate(range(4)))),f)
 def test_class_params_edge_reuse_and_constraints(self):
  f=fixture();m={0:192,1:196,2:193,3:195};g=p.remap(f,m)
  self.assertEqual(g['vregs'][196],'f');self.assertEqual(g['blocks'][1]['params'],[193]);self.assertEqual(g['insts'][1]['args'],[[195]])
  self.assertEqual(g['insts'][1]['ops'][1]['c'],'reuse:0');self.assertEqual(g['insts'][1]['clobbers'],['x30']);self.assertEqual(f,fixture())
 def test_duplicate_or_incomplete_mapping_refused(self):
  for m in [{0:0,1:1},{0:0,1:0,2:2,3:3},{0:0,1:-1,2:2,3:3}]:
   with self.assertRaises(AssertionError):p.remap(fixture(),m)
 def test_shape_mapping(self):
  f=fixture();g=p.remap(f,{0:192,1:196,2:193,3:195});m=p.shape_map(f,g);self.assertEqual([m[i] for i in range(4)],[192,196,193,195])
 def test_reused_vreg_conflicting_alias_refused(self):
  f=fixture();g=copy.deepcopy(f);g['insts'][0]['ops'][0]['v']=2
  with self.assertRaises(ValueError):p.shape_map(f,g)
 def test_constraints_and_graph_refused(self):
  for field in ['constraint','graph','class']:
   f=fixture();g=copy.deepcopy(f)
   if field=='constraint':g['insts'][1]['ops'][0]['c']='fixed:v1'
   elif field=='graph':g['blocks'][0]['succs']=[]
   else:g['vregs']='iiii'
   with self.assertRaises(ValueError):p.shape_map(f,g)
 def test_unused_sparse_slots_extended(self):
  f=fixture();f['vregs']+='ii';g=p.remap(f,{i:192+i for i in range(6)});m=p.shape_map(f,g)
  self.assertEqual(set(m),set(range(6)));self.assertEqual(len(set(m.values())),6)
 def test_reverse_keeps_parameter_prefix(self):
  f=fixture();m=p.reverse_map(f);self.assertEqual(m[0],0);self.assertEqual(m[2],2);self.assertEqual(len(set(m.values())),4)
if __name__=='__main__':unittest.main()
