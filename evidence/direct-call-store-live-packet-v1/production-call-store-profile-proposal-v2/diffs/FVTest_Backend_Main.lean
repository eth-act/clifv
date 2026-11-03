--- current/FVTest/Backend/Main.lean
+++ candidate/FVTest/Backend/Main.lean
@@ -1,5 +1,5 @@
 import FV.Backend
-import FV.Backend.ReturnPinProduction
+import FV.Backend.General7CallStoreProduction
 import FV.Opt.Legalize128Pass
 import FV.Opt.LegalExn
 import FVTest.Opt.Common
@@ -270,7 +270,7 @@
     pure afs
   let fa ← match stock with
     | none => (if pipelineT then compileFileWith allocNone pf (unv128 ++ unvTry) false
-        else compileFileReturnPinWhen (!o.opt.isSome &&
+        else compileFileGeneral7CallStoreWhen (!o.opt.isSome &&
           !(pf.funcs.any fun p => p.func.toOption.any fun f => f.blocks.any (·.term.isTry)))
           allocNone pf (unv128 ++ unvTry) o.deadCleanup)
     | some c => do
@@ -280,7 +280,7 @@
         -- A whole-file retry replaces the previous attempt's configuration receipt.
         rejected.set #[]
         StockConfig.allocateWith c clif rejected allocNone (I128Native.replace native vcs)
-      compileFileReturnPinWhen (!pipelineT && !o.opt.isSome &&
+      compileFileGeneral7CallStoreWhen (!pipelineT && !o.opt.isSome &&
           !(pf.funcs.any fun p => p.func.toOption.any fun f => f.blocks.any (·.term.isTry)))
         configuredAlloc pf
         (unv128 ++ unvTry ++ pf.funcs.map (fun p => (p.name, "experimental stock-configured driver (outside backend_correct)"))) o.deadCleanup
