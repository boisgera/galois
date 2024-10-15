import Mathlib.Order.Monotone.Basic
import Mathlib.Order.OrdContinuous

-- NOTA: I had issues with concrete spaces, such as [0, 1]
--       where the set vs subtypes issue comes up.
--       Avoided this stuff ATM by going abstract, but will
--       needed to reconsider how to glue thislater (concrete case as an
--       application of the general result).


universe u

class LinearBoundedOrder (α: Type u) extends LinearOrder α, BoundedOrder α

variable {X : Type u} [LinearBoundedOrder X]
variable {Y : Type u} [LinearBoundedOrder Y]

-- Monotone Galois Connection
def mgc (f : X -> Y) (g : Y -> X) : Prop :=
    ∀ (x : X), ∀ (y : Y), f x <= y <-> x <= g y


section

  variable (f : X -> Y) (g : Y -> X)
  -- variable (m : mgc f g) -- Why can't I put this stuff here and
  -- do I need to put the arg as an explicit argument of the function
  -- instead?

  theorem mgc_bounds (m : mgc f g) : f ⊥ = ⊥ ∧ g ⊤ = ⊤ := by
    apply And.intro
    . rw[mgc] at m
      have h₁ : f ⊥ ≤ ⊥ ↔ ⊥ ≤ g ⊥ := m ⊥ ⊥
      have h₂ : ⊥ ≤ g ⊥ := bot_le
      have f_bot_le_bot : f ⊥ ≤ ⊥ := h₁.mpr h₂
      have bot_le_f_bot : ⊥ ≤ f ⊥ := bot_le
      exact le_antisymm f_bot_le_bot bot_le_f_bot
    . rw[mgc] at m
      have := m ⊤ ⊤
      have := this.mp le_top
      exact le_antisymm le_top this

  theorem mgc_monotone (m : mgc f g) : Monotone f ∧ Monotone g := by
    apply And.intro
    . unfold Monotone
      intro a b a_le_b
      rw[mgc] at m
      -- nota : we could make this sequence as a calc.
      -- But partially only(?), see below.7
      -- Nah, transformations are allowed, that may fly (?).
      have : f b ≤ f b := le_rfl
      have : b ≤ g (f b) := (m b (f b)).mp this
      have : a ≤ g (f b) := le_trans a_le_b this
      have : f a ≤ f b := (m a (f b)).mpr this
      exact this
    . unfold Monotone
      intro a b a_le_b
      rw[mgc] at m
      have g_a_le_g_a: g a ≤ g a := le_rfl
      have : f (g a) ≤ b := calc f (g a)
        _ ≤ a := (m (g a) a).mpr g_a_le_g_a
        _ ≤ b := a_le_b
      exact (m (g a) b).mp this

  theorem mgc_continuous (m : mgc f g) : LeftOrdContinuous f ∧ RightOrdContinuous g :=
    sorry

end
