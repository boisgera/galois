import Mathlib.Order.Monotone.Basic
import Mathlib.Order.OrdContinuous

-- NOTA: I had issues with concrete spaces, such as [0, 1]
--       where the set vs subtypes issue comes up.
--       Avoided this stuff ATM by going abstract, but will
--       needed to reconsider how to glue this later of course
--       (concrete case as an application of the general result).

universe u

class LinearBoundedOrder (α: Type u) extends LinearOrder α, BoundedOrder α

variable {X : Type u} [LinearBoundedOrder X]
variable {Y : Type u} [LinearBoundedOrder Y]

-- Monotone Galois Connection
def mgc (f : X → Y) (g : Y → X) : Prop :=
    ∀ (x : X), ∀ (y : Y), f x <= y ↔ x <= g y

section

  variable (f : X → Y) (g : Y → X)
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
    . rw[Monotone]
      intro a b a_le_b
      rw[mgc] at m
      -- nota : we could make this sequence as a calc, but only partially,
      -- see below (reason: transformation are not allowed AFAICT).
      have : f b ≤ f b := le_rfl
      have : b ≤ g (f b) := (m b (f b)).mp this
      have : a ≤ g (f b) := le_trans a_le_b this
      have : f a ≤ f b := (m a (f b)).mpr this
      exact this
    . rw[Monotone]
      intro a b a_le_b
      rw[mgc] at m
      have g_a_le_g_a: g a ≤ g a := le_rfl
      have : f (g a) ≤ b := calc f (g a)
        _ ≤ a := (m (g a) a).mpr g_a_le_g_a
        _ ≤ b := a_le_b
      exact (m (g a) b).mp this

-- NB: in most of these iff proof, AFAICT, we could get away with the proof of
--     a single implication, and use the reversed order to prove the equivalence.

  theorem mgc_continuous (m : mgc f g) :
    LeftOrdContinuous f ∧ RightOrdContinuous g := by
    apply And.intro
    . rw[LeftOrdContinuous]
      intro s x is_lub_s_x
      rw[IsLUB, IsLeast] at is_lub_s_x
      let ⟨x_in_ub_s, x_in_lb_ub_s⟩ := is_lub_s_x
      rw[IsLUB, IsLeast]
      constructor
      . rw[upperBounds, Set.mem_setOf_eq] at x_in_ub_s
        rw[Set.image, upperBounds]
        simp only [
          Set.mem_setOf_eq,
          forall_exists_index,
          and_imp, forall_apply_eq_imp_iff₂
        ]
        intro a a_in_s
        have a_le_x : a ≤ x := x_in_ub_s a_in_s
        have f_non_decreasing := (mgc_monotone f g m).left
        exact f_non_decreasing a_le_x
      . rw[lowerBounds, upperBounds]
        simp only [
          Set.mem_image,
          forall_exists_index,
          and_imp,
          forall_apply_eq_imp_iff₂,
          Set.mem_setOf_eq]
        intro ub
        intro f_s_le_ub
        have s_le_g_ub : ∀ a ∈ s, a ≤ g ub := by
          intro a a_in_s
          exact (m a ub).mp (f_s_le_ub a a_in_s)
        rw[m x ub]
        rw[upperBounds, lowerBounds] at is_lub_s_x
        simp only [Set.mem_setOf_eq] at is_lub_s_x
        apply is_lub_s_x.right
        assumption
    . -- VERY similar to the previous block.
      -- a high-order argument with the reversed inequality would be nice.
      rw[RightOrdContinuous]
      intro s x is_glb_s_x
      rw[IsGLB, IsGreatest] at is_glb_s_x
      let ⟨x_in_lb_s, x_in_ub_lb_s⟩ := is_glb_s_x
      rw[IsGLB, IsGreatest]
      constructor
      . rw[lowerBounds, Set.mem_setOf_eq] at x_in_lb_s
        rw[Set.image, lowerBounds]
        simp only [
          Set.mem_setOf_eq,
          forall_exists_index,
          and_imp, forall_apply_eq_imp_iff₂
        ]
        intro a a_in_s
        have x_le_a : x ≤ a := x_in_lb_s a_in_s
        have g_non_decreasing := (mgc_monotone f g m).right
        exact g_non_decreasing x_le_a
      . rw[lowerBounds, upperBounds]
        simp only [
          Set.mem_image,
          forall_exists_index,
          and_imp,
          forall_apply_eq_imp_iff₂,
          Set.mem_setOf_eq]
        intro lb
        intro lb_le_g_s
        have f_lb_le_s : ∀ a ∈ s, f lb ≤ a := by
          intro a a_in_s
          exact (m lb a).mpr (lb_le_g_s a a_in_s)
        rw[<- m lb x]
        rw[upperBounds, lowerBounds] at is_glb_s_x
        simp only [Set.mem_setOf_eq] at is_glb_s_x
        apply is_glb_s_x.right
        assumption

  theorem f_from_g (m : mgc f g) :
    ∀ (x : X), IsLeast { y : Y | x ≤ g y } (f x) :=
    sorry

end
