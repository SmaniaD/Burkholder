import Mathlib.Analysis.Convex.Function
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.Analysis.Convex.SpecificFunctions.Pow
import Mathlib.Analysis.InnerProductSpace.NormPow
import Mathlib.Analysis.MeanInequalities
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Burkholder.Majorants.Definitions


noncomputable section



namespace Burkholder

theorem exists_majorant_p_eq_2 (p : ℝ) (hp : p=2) :
    ∃ u : ℝ → ℝ → ℝ,
      (∀ x y, ∃ d_u_dx d_u_dy : ℝ,
        ∀ h k, h * k = 0 →
          u (x + h) (y + k) ≤ u x y + d_u_dx * h + d_u_dy * k) ∧
      (∀ x y, v p x y ≤ u x y) ∧
      (∀ x y, x * y ≤ 0 → u x y ≤ 0) ∧
      (∀ x y, x*y = 0 → u x y ≤ 0) := by
  use fun x y => x * y
  constructor
  · intro x y
    refine ⟨y, x, ?_⟩
    intro h k hk
    rw [mul_eq_zero] at hk
    rcases hk with rfl | rfl
    · ring_nf
      exact le_rfl
    · ring_nf
      exact le_rfl
  constructor
  · intro x y
    calc
      v p x y = x * y := by
        subst p
        unfold v
        norm_num [pStar, q]
        ring
      _ ≤ x * y := le_rfl
  constructor
  · intro x y hxy
    exact hxy
  · intro x y hxy
    rw [hxy]

    end Burkholder
