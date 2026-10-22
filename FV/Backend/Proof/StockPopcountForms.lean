import FV.Backend.Proof.StockScopedPopcountRhs
namespace Backend.Stock.Proof.Popcount
open Backend.Proof Backend.Proof.Driver
set_option autoImplicit false
set_option Elab.async false

def popcountCode (w d x : Nat) : List MInst :=
  [.movToFpu (.vreg d .float) (.vreg x .int) (if w = 64 then .size64 else .size32),
   .vecMisc .cnt (.vreg (d+1) .float) (.vreg d .float) .size8x8] ++
  if w = 8 then [.movFromVec (.vreg (d+2) .int) (.vreg (d+1) .float) 0 .size8]
  else
    [(if w = 16 then
       .vecRRR .addp (.vreg (d+2) .float) (.vreg (d+1) .float) (.vreg (d+1) .float) .size8x8
      else .vecLanes .addv (.vreg (d+2) .float) (.vreg (d+1) .float) .size8x8),
     .movFromVec (.vreg (d+3) .int) (.vreg (d+2) .float) 0 .size8]

theorem base_code {w : Nat} (width : IW w) (st : LState) (x : Nat) :
    (popcountBase w st (.vreg x .int)).emitted = st.emitted ++ (popcountCode w st.nextVreg x).toArray ∧
    (popcountBase w st (.vreg x .int)).nextVreg = st.nextVreg+popcountAlloc w := by
  rcases width with rfl | rfl | rfl | rfl
  all_goals
    constructor
    · apply Array.ext'
      simp [popcountBase,popcountCode,LState.fresh,LState.emit]
    · rfl
end Backend.Stock.Proof.Popcount
