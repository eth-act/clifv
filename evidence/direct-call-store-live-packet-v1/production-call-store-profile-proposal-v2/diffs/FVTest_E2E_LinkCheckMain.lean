--- current/FVTest/E2E/LinkCheckMain.lean
+++ candidate/FVTest/E2E/LinkCheckMain.lean
@@ -1,3 +1,6 @@
+import FV.Backend.General7CallStoreProduction
+import FV.E2E.CallStoreChecks
+import FVTest.E2E.CallStoreLinkProofWith
 import FV.E2E.ProductionPipelineWith
 import FV.Backend.Lowering.StockVoidCallNI
 import FV.E2E.ReturnPinChecksWith
@@ -30,6 +33,11 @@
   -- names whose address is in a data object the program reaches (vtable methods)
   let dataSyms : List String := A.data.flatMap (·.refs)
   let I0 : LinkInput := { funcs := fis.toList, addrs, syms := [], raStar := 8, D := 0 }
+  -- Derive the mode from every actual raw artifact. A typed file retains its previous mode.
+  let callStoreMode := I0.funcs.all fun fi =>
+    match Stock.GeneralLoopCfg7.CallStoreNI.lowerValidated fi.func with
+    | .error _ => false
+    | .ok raw => SemanticABI.checkCallStores fi.func raw
   -- Other supported compiler modes and whole-file retries can retain earlier
   -- artifacts. Recover their routing from actual bytes, then validate every
   -- selected artifact normally. These are data choices, not source assumptions.
@@ -40,28 +48,30 @@
       let rd := fileRd file
       let route (fi : FnInput) : Option (String × Nat) :=
         let f := fi.func
-        if (Stock.MemorySretCopy.eligible f || (Stock.VoidCall.sourceData? f).isSome || Stock.Arithmetic.eligible f || Stock.Mixed.activationEligible f ||
-            Stock.Logical.activationEligible f || Stock.Scalar.activationEligible f || (((((((Stock.MemoryCapturedCopy.eligible f || Stock.MemoryLoadStore.eligible f) || Stock.MemoryStoreCfg.eligible f) || Stock.MemoryStore.eligible f) || Stock.MemoryExtending.eligible f) || Stock.MemoryUnsigned.eligible f || Stock.MemoryCfg.eligible f || Stock.Memory.eligible f || Stock.ParameterCfg.leafEligible f || Stock.ConditionalForwardCfg.leafEligible f) || Stock.ConditionalCfg.leafEligible f) || Stock.ForwardCfg.leafEligible f || Stock.LinearCfg.eligible f || Stock.TwoBlock.Entry.eligible f)) &&
-            !(Stock.D0.eligible f || Stock.ScalarAdd.activationEligible f) then
-          -- Probe each complete route before its transactional retry. A retained
-          -- logical/mixed artifact must not be skipped directly to legacy.
-          let routes := Stock.VoidCall.NI.lowerRoutes.zipIdx
+        let routeMatches (lower : Clif.Function → Except String VCode) : Bool :=
+          match I0.pipeOfWithLowering lower (productionStage o.deadCleanup) fi with
+          | .error _ => false
+          | .ok a => (checkAlloc a.vcp a.rf).toBool &&
+              Backend.Proof.Driver.prepCheck (productionStage o.deadCleanup f a.vc) a.vcp &&
+              ((if callStoreMode then SemanticABI.checkCallStores f a.vc
+                else SemanticABI.checkCalls f a.vc) || lowerOkTSB f a.vc) && artB I0 rd phs a
+        if callStoreMode && routeMatches Stock.GeneralLoopCfg7.CallStoreNI.lowerValidated then none
+        else
+          let routes := Stock.GeneralLoopCfg7.NI.lowerRoutes.zipIdx
           let probes := if Stock.MemorySretCopy.eligible f || (Stock.VoidCall.sourceData? f).isSome then
               routes.drop 21 ++ routes.take 21
             else routes
-          let found := probes.find? fun (lower, _) =>
-            match I0.pipeOfWithLowering lower (productionStage o.deadCleanup) fi with
-            | .error _ => false
-            | .ok a => (checkAlloc a.vcp a.rf).toBool &&
-                Backend.Proof.Driver.prepCheck (productionStage o.deadCleanup f a.vc) a.vcp &&
-                (SemanticABI.checkCalls f a.vc || lowerOkTSB f a.vc) && artB I0 rd phs a
-          let idx := (found.map (·.2)).getD 4
-          if idx != 0 || Stock.MemorySretCopy.eligible f || (Stock.VoidCall.sourceData? f).isSome || (((((((Stock.MemoryCapturedCopy.eligible f || Stock.MemoryLoadStore.eligible f) || Stock.MemoryStoreCfg.eligible f) || Stock.MemoryStore.eligible f) || Stock.MemoryExtending.eligible f) || Stock.MemoryUnsigned.eligible f || Stock.MemoryCfg.eligible f || Stock.Memory.eligible f || Stock.ParameterCfg.leafEligible f || Stock.ConditionalForwardCfg.leafEligible f) || Stock.ConditionalCfg.leafEligible f) || Stock.ForwardCfg.leafEligible f || Stock.LinearCfg.eligible f || Stock.TwoBlock.Entry.eligible f) then some (f.name, idx) else none
-        else none
+          -- An explicit route0 retains legacy artifacts when the new default differs.
+          (probes.find? fun (lower,_) => routeMatches lower).map fun (_,index) => (f.name,index)
       (Link.parMap route I0.funcs).filterMap id
-  let actualLower := Stock.VoidCall.NI.lowerWithRoutes choices
-  let lowerName := "(Backend.Stock.VoidCall.NI.lowerWithRoutes [" ++
+  let actualLower := if callStoreMode then Stock.GeneralLoopCfg7.CallStoreNI.lowerWithRoutes choices
+    else Stock.GeneralLoopCfg7.NI.lowerWithRoutes choices
+  let lowerName := (if callStoreMode then "(Backend.Stock.GeneralLoopCfg7.CallStoreNI.lowerWithRoutes ["
+    else "(Backend.Stock.GeneralLoopCfg7.NI.lowerWithRoutes [") ++
     ", ".intercalate (choices.map fun (name,idx) => "(" ++ leanStr name ++ ", " ++ toString idx ++ ")") ++ "])"
+  let lowerImport := if callStoreMode then "FV.Backend.General7CallStoreProduction"
+    else "FV.Backend.Lowering.StockGeneralLoopCfg7NI"
+  let admissionExtra := if callStoreMode then returnPinCallStoresExtra else returnPinCallsExtra
   if o.profile then
     -- the slowest functions: the pipeline, the lowering validator, the allocation checker
     let mut tot : Array (Nat × String × Nat × Nat × Nat) := #[]
@@ -72,7 +82,8 @@
       let ok := r.toBool
       let t1 ← IO.monoMsNow
       let a := getOk r
-      let lc := Backend.SemanticABI.checkCalls f a.vc
+      let lc := if callStoreMode then Backend.SemanticABI.checkCallStores f a.vc
+        else Backend.SemanticABI.checkCalls f a.vc
       let t2 ← IO.monoMsNow
       let ca := (checkAlloc a.vcp a.rf).toBool
       let t3 ← IO.monoMsNow
@@ -88,7 +99,7 @@
   -- the checks that do not depend on the rest of the program, once (`staticChks`: the
   -- validators); then `diagR` with them (`chks = staticChks ++ linkChks`)
   let D0 := (R0I.map fun e => frameDrop (getOk e.2).af).foldl max 0
-  let statI := Link.parMap (fun e => (e.1.name, staticChksSemanticFor returnPinCallsExtra (productionStage o.deadCleanup) { I0 with D := D0 } e.1 e.2)) R0I
+  let statI := Link.parMap (fun e => (e.1.name, staticChksSemanticFor admissionExtra (productionStage o.deadCleanup) { I0 with D := D0 } e.1 e.2)) R0I
   let failI := statI.filterMap fun e => if (bad e.2).isEmpty then none else some e.1
   -- the typed checks on the Stock route's results (#722, `Link.SemanticCompilerWith.attemptT`'s
   -- output, typed `--verified` when the units hold Stock code): the results `R0I` with
@@ -409,8 +420,9 @@
       else none
     let proofFiles := if typed then
         FVTest.E2E.TypedLinkProofWith.leanFilesTypedWith
-          (if typedS then lowerName else "Backend.lowerFunction") I' (funcs.map (·.2)) entries out o.module exe o.deadCleanup noTls stackS stackGood bg (lowerImport := "FV.Backend.Lowering.StockVoidCallNI")
-      else FVTest.E2E.ReturnPinLinkProofWith.leanFilesReturnPinWith lowerName I' (funcs.map (·.2)) entries out o.module exe o.deadCleanup noTls stackS stackGood bg (lowerImport := "FV.Backend.Lowering.StockVoidCallNI")
+          (if typedS then lowerName else "Backend.lowerFunction") I' (funcs.map (·.2)) entries out o.module exe o.deadCleanup noTls stackS stackGood bg (lowerImport := lowerImport)
+      else if callStoreMode then FVTest.E2E.CallStoreLinkProofWith.leanFilesCallStoreWith lowerName I' (funcs.map (·.2)) entries out o.module exe o.deadCleanup noTls stackS stackGood bg (lowerImport := lowerImport)
+      else FVTest.E2E.ReturnPinLinkProofWith.leanFilesReturnPinWith lowerName I' (funcs.map (·.2)) entries out o.module exe o.deadCleanup noTls stackS stackGood bg (lowerImport := lowerImport)
     for (p, t) in proofFiles do
       if let some pd := (p : System.FilePath).parent then IO.FS.createDirAll pd
       IO.FS.writeFile p t
