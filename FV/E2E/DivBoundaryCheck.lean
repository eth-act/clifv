import FV.Backend.ABIReadDiv

/-! `DivBoundary.check`, the read-only division boundary check the division witnesses decide.
Its own module, so that those (long `native_decide`) witnesses need not wait for the boundary
proof `ABIReadDiv`. -/
namespace E2E.DivBoundary

abbrev check := Backend.ABIReadDiv.check

end E2E.DivBoundary
