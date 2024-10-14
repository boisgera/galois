import Mathlib.Order.Monotone.Basic
import Mathlib.Order.OrdContinuous

-- NOTA: I had issues with concrete spaces, such as [0, 1]
--       where the set vs subtypes issue comes up.
--       Avoided this stuff ATM by going abstract, but will
--       needed to reconsider how to glue thislater (concrete case as an
--       application of the general result).


universe u

variable {X : Type u} [LinearOrder X] [BoundedOrder X]
variable {Y : Type u} [LinearOrder Y] [BoundedOrder Y]

def monotone_galois_connection (f : X -> Y) (g : Y -> X) : Prop :=
    ∀ (x : X), ∀ (y : Y), f x <= y <-> x <= g y

section

  variable (f : X -> Y) (g : Y -> X)
  variable (mgc : monotone_galois_connection f g)

  theorem mgc_bounds : f ⊥ = ⊥ ∧ g ⊤ = ⊤ :=
    sorry

  theorem mgc_monotone : Monotone f ∧ Monotone g :=
    sorry

  theorem mgc_continuous : LeftOrdContinuous f ∧ RightOrdContinuous g :=
    sorry

end
