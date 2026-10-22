from pathlib import Path
root=Path('/tmp/stock-div-next-staged');old=Path('FVTest/Backend/Lowering/StockDivProductionRuntime.lean').read_text();s=old.replace('import FV.E2E.StockDivFixtures','import FV.E2E.StockDivFixtures\nimport FV.E2E.StockMixedDivFixtures\nimport FVTest.Backend.Lowering.StockDivProductionRuntime',1).replace('namespace FVTest.StockDivProductionRuntime','namespace FVTest.StockMixedDivProductionRuntime').replace('end FVTest.StockDivProductionRuntime','end FVTest.StockMixedDivProductionRuntime').replace('FVTest.StockDivProductionRuntime.main','FVTest.StockMixedDivProductionRuntime.main')
a=s.index('def input (config :');b=s.index('/-- Export the actual Lean-encoded',a)
s=s[:a]+'''def input (config : Stock.D0.Configuration) : String :=
  String.join (E2E.StockDivNIWitness.operations.flatMap fun op =>
    [false,true].map fun safe => (E2E.StockMixedDivNIWitness.function config op safe).print ++ "\\n") ++
  FVTest.StockDivProductionRuntime.input config

'''+s[b:]
s=s.replace('STOCK_DIV_NATIVE_OUT','STOCK_MIXED_DIV_NATIVE_OUT').replace('== 21','== 29').replace('E2E.StockDivNIWitness.function config .sdiv','E2E.StockMixedDivNIWitness.function config .sdiv false')
a=s.index('  for op in E2E.StockDivNIWitness.operations do');b=s.index('  for cleanup in [false,true] do',a);lines=s[a:b].splitlines(True);block=lines[0]+'    for safe in [false,true] do\n'+''.join('  '+line if line.strip() else line for line in lines[1:]);block=block.replace('E2E.StockDivNIWitness.function config op','E2E.StockMixedDivNIWitness.function config op safe');s=s[:a]+block+s[b:];s=s.replace('Stock div {label}','Stock mixed div {label}')
p=root/'FVTest/Backend/Lowering/StockMixedDivProductionRuntime.lean';p.parent.mkdir(parents=True,exist_ok=True);p.write_text(s)
s=Path('FVTest/Backend/Lowering/StockDivProductionLinked.lean').read_text().replace('import FV.E2E.StockDivWitness','import FV.E2E.StockMixedDivWitness').replace('StockDivProductionLinkedFixture','StockMixedDivProductionLinkedFixture').replace('StockDivProduction','StockMixedDivProduction').replace('actual_stock_div_','actual_stock_mixed_div_').replace('STOCK_DIV','STOCK_MIXED_DIV')
s=s.replace('E2E.StockDivNIWitness.function c (E2E.StockDivNIWitness.operations[(i : Nat) % 4]!)','E2E.StockMixedDivNIWitness.function c (E2E.StockMixedDivNIWitness.operations[(i : Nat) % 4]!) (i / 4 % 2 == 1)')
p=root/'FVTest/Backend/Lowering/StockMixedDivProductionLinked.lean';p.write_text(s)
p=root/'lakefile-additions.toml';p.write_text('''\n[[lean_exe]]
name = "stock-mixed-div-runtime"
root = "FVTest.Backend.Lowering.StockMixedDivProductionRuntime"

[[lean_exe]]
name = "stock-mixed-div-linked"
root = "FVTest.Backend.Lowering.StockMixedDivProductionLinked"
''');print('Prepared runtime29functions and linked/source reconstruction fixtures; Lean validation pending')
