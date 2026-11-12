import FV.Clif.NotrapLoad

-- #970: the CLIF justification of the stock-configured driver's drop of unused `notrap` loads
-- (`StockConfig.dropDeadNotrapLoads`, unproved, outside backend_correct).
#print axioms Clif.evalInst_notrap_load
