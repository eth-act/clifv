import FV.Clif.Parse
import FV.Clif.Print

/-! #1071: the `; data:` line parser and printer in constant stack depth and linear time. Each
`@[csimp]` lemma states that the compiled replacement equals the original definition (the kernel
and every theorem see the original). -/

#print axioms Clif.hexBytes?_eq_TR
#print axioms Clif.printDataItems_eq_TR
