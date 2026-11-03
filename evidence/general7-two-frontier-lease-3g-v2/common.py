from pathlib import Path
import datetime,json,os
D=Path(__file__).resolve().parent
E=D.parent
def restore(reason):
    data={'status':'restored','source_GiB':2,'acquire_GiB':1,'reason':reason,'utc':datetime.datetime.now(datetime.timezone.utc).isoformat()}
    for p in [D/'shares-restored.json',E/'140-acquire-fused810-packet-v1/share-restored-after-three-leaves-v2.json',E/'general7-main-candidate-v1/complete-two-frontier-repair-proposal-v1/source-share-restored-v2.json']:
        q=p.with_suffix('.tmp');q.write_text(json.dumps(data,indent=2)+'\n');os.replace(q,p)
