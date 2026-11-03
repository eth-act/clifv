from common import *
s=json.loads((D/'state.json').read_text());save(D/'guard-armed.json',{'pid':os.getpid(),'birth':psutil.Process().create_time(),'owner':s['owner'],'owner_birth':s['owner_birth']})
while not (D/'allocation-finished.json').exists():
 s=json.loads((D/'state.json').read_text())
 if not live(s['owner'],s['owner_birth']) and not busy(s):restore('independent all-exit guard after owner and all consumers exit');break
 time.sleep(.2)
save(D/'guard-receipt.json',{'status':'ordinary_allocation_finished','source_share_borrowed':False,'acquire_GiB':1,'owner':s['owner'],'owner_alive_at_restore':live(s['owner'],s['owner_birth']),'compiler_signals':[]})
