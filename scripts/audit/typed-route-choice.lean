import FVTest.E2E.TypedRouteChoiceWitness

-- #1040: link-check's route for the typed Stock checker (witness of the shape)
#print axioms E2E.TypedRouteChoiceWitness.same_bytes -- witness: native_decide
#print axioms E2E.TypedRouteChoiceWitness.stock_route_typed_rejected -- witness: native_decide
#print axioms E2E.TypedRouteChoiceWitness.typed_route -- witness: native_decide
#print axioms E2E.TypedRouteChoiceWitness.crate_correct -- witness: native_decide
