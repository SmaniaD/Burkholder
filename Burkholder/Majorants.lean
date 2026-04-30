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
    ∃ u du_dx du_dy : ℝ → ℝ → ℝ, ∃ C : ℝ,
      0 ≤ C ∧
      ContinuousOn (fun z : ℝ × ℝ => u z.1 z.2) Set.univ ∧
      ContinuousOn (fun z : ℝ × ℝ => du_dx z.1 z.2) Set.univ ∧
      ContinuousOn (fun z : ℝ × ℝ => du_dy z.1 z.2) Set.univ ∧
      (∀ x y,
       |u x y| ≤ C * (Real.rpow |x| p + Real.rpow |y| p)) ∧
      (∀ x y,
        |du_dx x y| ≤ C * (Real.rpow |x| (p - 1) + Real.rpow |y| (p - 1))) ∧
      (∀ x y,
        |du_dy x y| ≤ C * (Real.rpow |x| (p - 1) + Real.rpow |y| (p - 1))) ∧
      (∀ x y h k, h * k ≤  0 →
          u (x + h) (y + k) ≤ u x y + du_dx x y * h + du_dy x y * k) ∧
      (∀ x y, v p x y ≤ u x y) ∧
      (∀ x y, x * y ≤ 0 → u x y ≤ 0) ∧
      (∀ x y, p ≠ 2∧ x*y = 0 ∧ (x,y) ≠ (0,0) → u x y < 0)  := by
        by_cases hp2 : p = 2
        · -- Case p = 2
          rcases exists_majorant_p_eq_2 p hp2 with
            ⟨u, du_dx, du_dy, C, hC_nonneg, hu_cont, hdu_dx_cont, hdu_dy_cont,
              hu_growth, hdu_dx_growth, hdu_dy_growth, htangent, hmajor, hnonpos, _haxis⟩
          refine ⟨u, du_dx, du_dy, C, hC_nonneg, hu_cont, hdu_dx_cont, hdu_dy_cont,
            hu_growth, hdu_dx_growth, hdu_dy_growth, htangent, hmajor, hnonpos, ?_⟩
          intro x y hxy
          exact False.elim (hxy.1 hp2)
        by_cases hp_gt_2 : 2 < p
        · -- Case p > 2
          rcases exists_majorant_geTwo p hp_gt_2 with
            ⟨u, du_dx, du_dy, C, hC_nonneg, hu_cont, hdu_dx_cont, hdu_dy_cont,
              hu_growth, hdu_dx_growth, hdu_dy_growth, htangent, hmajor, hnonpos, haxis⟩
          refine ⟨u, du_dx, du_dy, C, hC_nonneg, hu_cont, hdu_dx_cont, hdu_dy_cont,
            hu_growth, hdu_dx_growth, hdu_dy_growth, htangent, hmajor, hnonpos, ?_⟩
          intro x y hxy
          exact haxis x y ⟨hxy.2.1, hxy.2.2⟩
        -- Case 1 < p < 2
        have hp1 : 1 < p := hp
        have hp_lt_2 : p < 2 := lt_of_le_of_ne (le_of_not_gt hp_gt_2) hp2
        rcases exists_majorant_leTwo p ⟨hp1, hp_lt_2⟩ with
          ⟨u, du_dx, du_dy, C, hC_nonneg, hu_cont, hdu_dx_cont, hdu_dy_cont,
            hu_growth, hdu_dx_growth, hdu_dy_growth, htangent, hmajor, hnonpos, haxis⟩
        refine ⟨u, du_dx, du_dy, C, hC_nonneg, hu_cont, hdu_dx_cont, hdu_dy_cont,
          hu_growth, hdu_dx_growth, hdu_dy_growth, htangent, hmajor, hnonpos, ?_⟩
        intro x y hxy
        exact haxis x y ⟨hxy.2.1, hxy.2.2⟩





end Majorants
