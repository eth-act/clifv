import FV.Backend.Proof.IselPrgCtorSound

namespace Backend.Proof.Prg
open Backend Backend.Proof Isle Isle.Aarch64

example {f : Clif.Function} {ctx : Ctx} (hP : PInv f ctx) :
    ∀ (term : Term) (as : List PA) (a : PA) (must : Bool) (vs : List V) (st : LState),
      actor term.id as = some (a, must) → γL f ctx as vs →
        (∃ w st', externCtor ctx term vs st = .ok (w, st') ∧ γ f ctx a w) ∨
        (externCtor ctx term vs st = .fail ∧ must = false) :=
  fun term as a must vs st h hv => actor_sound hP term as a must vs st h hv

#check @ofvOk_sound
#check @actor_sound
#print axioms ofvOk_sound
#print axioms actor_sound
end Backend.Proof.Prg
