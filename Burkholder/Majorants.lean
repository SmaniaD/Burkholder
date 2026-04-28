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
import Burkholder.Majorants.Majorant_p_l_2
import Burkholder.Majorants.Majorant_p_g_2
import Burkholder.Majorants.Majorant_p_eq_2

noncomputable section



namespace Majorants


/- Final result: majorant exists for p > 1 -/

theorem exists_majorant_p_g_1 (p : ℝ) (hp : p> 1) :
    ∃ u : ℝ → ℝ → ℝ,
      (∀ x y, ∃ d_u_dx d_u_dy : ℝ,
        ∀ h k, h * k = 0 →
          u (x + h) (y + k) ≤ u x y + d_u_dx * h + d_u_dy * k) ∧
      (∀ x y, v p x y ≤ u x y) ∧
      (∀ x y, x * y ≤ 0 → u x y ≤ 0) ∧
      (∀ x y, x*y = 0 → u x y ≤ 0) := by
        by_cases hp2 : p = 2
        · -- Case p = 2
          exact exists_majorant_p_eq_2 p hp2
        by_cases hp_gt_2 : 2 < p
        · -- Case p > 2
          exact exists_majorant_geTwo p hp_gt_2
        -- Case 1 < p < 2
        have hp1 : 1 < p := hp
        have hp_lt_2 : p < 2 := lt_of_le_of_ne (le_of_not_gt hp_gt_2) hp2
        exact exists_majorant_leTwo p ⟨hp1, hp_lt_2⟩





end Majorants
