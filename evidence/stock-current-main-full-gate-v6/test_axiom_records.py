import importlib.util
from pathlib import Path
import unittest
import sys
sys.path.insert(0, str(Path(__file__).resolve().parent/'helpers'))
from axiom_records import parse_records
spec=importlib.util.spec_from_file_location('audit_helper',Path(__file__).resolve().parent/'helpers/axiom-audit-j2.py')
helper=importlib.util.module_from_spec(spec);spec.loader.exec_module(helper)

class AxiomRecords(unittest.TestCase):
    def test_zero_then_dependent(self):
        text="'E2E.ReturnPinMode.pins_of_valid' does not depend on any axioms\n'E2E.CompiledSemanticReturnPins.erase' depends on axioms: [propext, Classical.choice, Quot.sound]\n"
        self.assertEqual(parse_records(text), [('E2E.ReturnPinMode.pins_of_valid',[]),('E2E.CompiledSemanticReturnPins.erase',['propext','Classical.choice','Quot.sound'])])
    def test_prime_and_wrapped_report(self):
        text="'Foo.bar'' depends on axioms: [propext,\n Classical.choice, Quot.sound]\n'Foo.«name'»' does not depend on any axioms\n"
        self.assertEqual(parse_records(text),[("Foo.bar'",['propext','Classical.choice','Quot.sound']),("Foo.«name'»",[])])
    def test_marked_native_policy(self):
        native="Foo.helper'._native.native_decide.ax_1✝"
        records=parse_records("'Foo.fixture'' depends on axioms: [propext, "+native+"]\n")
        marked={"Foo.fixture'"}
        rejected=lambda marks:{x for name,values in records for x in values if x not in helper.STANDARD and not(name in marks and helper.NATIVE.fullmatch(x))}
        self.assertEqual(rejected(marked),set());self.assertEqual(rejected(set()),{native})
    def test_truncated_report_rejected(self):
        with self.assertRaises(ValueError):parse_records("'Foo.broken' depends on axioms: [propext\n'Foo.next' does not depend on any axioms\n")
    def test_duplicate_records_retained(self):
        self.assertEqual(parse_records("'Foo.x' does not depend on any axioms\n'Foo.x' does not depend on any axioms"),[('Foo.x',[]),('Foo.x',[])])

if __name__=='__main__':unittest.main()
