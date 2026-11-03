from pathlib import Path
import datetime,json,time
D=Path(__file__).resolve().parent
end=datetime.datetime(2026,11,3,8,42,tzinfo=datetime.timezone.utc)
(D/'state.json').write_text(json.dumps({'status':'active','start_utc':'2026-11-03T08:32:00+00:00','automatic_end_utc':end.isoformat(),'head':'b59b569cf788c0be0cb829f0909d5fc0d2125231','coord_message':6461})+'\n')
while not (D/'released.json').exists():
 remaining=(end-datetime.datetime.now(datetime.timezone.utc)).total_seconds()
 if remaining<=0:
  print('PR944 merge window expired automatically at08:42UTC. Send the explicit release notice if delivery did not close it earlier.',flush=True)
  raise SystemExit(0)
 time.sleep(min(remaining,5))
print('PR944 merge window released before automatic expiry',flush=True)
