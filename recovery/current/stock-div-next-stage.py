from pathlib import Path
import re,json,hashlib
src=Path('/tmp/stock-div-next-prefix-normal.lean').read_text().splitlines(True);root=Path('/tmp/stock-div-next-staged');root.mkdir(exist_ok=True)
base=''.join(src[:13]);parts=[
('StockScanTrapSemantics',[(14,113),(654,689)],[]),
('StockLocalSourceTrap',[(116,241)],['StockScanTrapSemantics']),
('StockLocalTrapRefines',[(245,324)],['StockLocalSourceTrap']),
('StockQuietSourceRecords',[(326,562)],[]),
('StockLastDivReturnDemand',[(565,652)],[]),
('StockMixedDivBodyRefines',[(692,983)],['StockScanTrapSemantics','StockLocalTrapRefines','StockQuietSourceRecords','StockLastDivReturnDemand']),
('StockScalarMixedDivDomain',[(988,1015)],['StockMixedDivBodyRefines'])]
records=[]
for name,ranges,deps in parts:
 s=base+''.join('import FV.Backend.Proof.'+d+'\n' for d in deps)+'\n'
 for a,b in ranges:s+=''.join(line for line in src[a-1:b] if not line.startswith('#print'))+'\n'
 p=root/'FV/Backend/Proof'/(name+'.lean');p.parent.mkdir(parents=True,exist_ok=True);p.write_text(s);records.append({'path':str(p.relative_to(root)),'sha256':hashlib.sha256(s.encode()).hexdigest(),'draft_lines':ranges})
audit='import FV.Backend.Proof.StockScalarMixedDivDomain\n'+''.join(line for line in src if line.startswith('#print'))
p=root/'scripts/audit/stock-mixed-div-production.lean';p.parent.mkdir(parents=True,exist_ok=True);p.write_text(audit)
(root/'partition.json').write_text(json.dumps({'status':'prepared from compiled combined draft; split module imports not validated yet; no production activation claim','parts':records},indent=2)+'\n');print('Prepared',len(parts),'split proof modules; original compiled draft untouched')
