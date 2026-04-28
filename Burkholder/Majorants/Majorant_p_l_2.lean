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

namespace Majorants

namespace  Majorant_p_l_2

/-!
# Burkholder majorant candidate

This file builds and studies the piecewise candidate `uCandidate`.

The proof architecture is organized as follows.

1. **Definitions.**  We define the Burkholder parameters, the two local formulas
   `uA1` and `vLeTwo`, their first partial derivatives, the first quadrant
   auxiliary function `auxFunction1`, and finally the four-quadrant function
   `uCandidate`.
2. **Continuity and boundary compatibility.**  We prove that the local formulas,
   their first partials, and the glued functions agree continuously across the
   sector boundaries.
3. **Differentiability and local concavity.**  Inside each smooth sector we
   identify first derivatives and prove the relevant second derivatives are
   non-positive.
4. **Tangent inequalities.**  Local concavity gives tangent inequalities on
   single sectors.  The remaining work is geometric: split horizontal/vertical
   segments at sector boundaries and glue the local tangent estimates while
   comparing derivatives at the break points.

Most of the long lemmas near the end are not new analytic facts; they are
bookkeeping lemmas that move a segment through the sector decomposition of
`uCandidate`.
-/

/-! ## 1. Basic parameters and local formulas -/





theorem pStar_eq_q_of_one_lt_of_lt_two (p : ℝ) (hp1 : 1 < p) (hp2 : p < 2) :
    pStar p = q p := by
  unfold pStar
  apply max_eq_right
  unfold q
  have hp_ne_one : p ≠ 1 := by linarith
  simp [hp_ne_one]
  have hp_pos : 0 < p := by linarith
  have hden_pos : 0 < p - 1 := by linarith
  rw [le_div_iff₀ hden_pos]
  nlinarith

theorem pStar_eq_self_of_two_le (p : ℝ) (hp : 2 ≤ p) : pStar p = p := by
  unfold pStar
  apply max_eq_left
  unfold q
  by_cases h : p = 1
  · simp [h]
  · simp [h]
    have hden_pos : 0 < p - 1 := by linarith
    rw [div_le_iff₀ hden_pos]
    nlinarith






/-- The same expression specialized to the `1< p < 2` regime. -/
def coeffLeTwo (p : ℝ) : ℝ :=
  Real.rpow ((p - 1)⁻¹) p

def vLeTwo (p x y : ℝ) : ℝ :=
  Real.rpow (|((x + y) / 2)|) p
    - coeffLeTwo p * Real.rpow (|((x - y) / 2)|) p





def A2 (p x y : ℝ) : Prop :=
  0 < x ∧ (a p) * x < y ∧ y < x

/-- Closed version of the upper sector. -/
def closureA2 (p x y : ℝ) : Prop :=
  0 ≤ x ∧ (a p) * x ≤ y ∧ y ≤ x

/-- Lower first-quadrant sector. In the regime `1 < p < 2`,
the affine formula `uA1` is used on this sector. -/
def A1 (p x y : ℝ) : Prop :=
  0 < x ∧ -x < y ∧ y < (a p) * x

/-- Closed version of the lower sector. -/
def closureA1 (p x y : ℝ) : Prop :=
  0 ≤ x ∧ -x ≤ y ∧ y ≤ (a p) * x


/-- Local majorant formula on `A1`; outside `x > 0` it is set to zero. -/
def uA1 (p x y : ℝ) : ℝ :=
  if x > 0 then
     alpha p * Real.rpow x (p-1) * (x - (pStar p) * (x - y) /2)
     else 0




def DxuA1  (p x y : ℝ) : ℝ :=
  if x > 0 then
    alpha p * (p / 2) * Real.rpow x (p - 2) *
      (((p - 2) / (p - 1)) * x + y)
  else 0



def DyuA1 (p x _y : ℝ) : ℝ :=
  if x > 0 then
     alpha p * Real.rpow x (p - 1) * (pStar p / 2)
     else 0



def DxvLeTwo (p x y : ℝ) : ℝ :=
  if x > 0 then
     Real.rpow (|((x + y) / 2)|) (p - 1) * (p / 2)
     - coeffLeTwo p * Real.rpow (|((x - y) / 2)|) (p - 1) * (p / 2)
  else 0

def DyvLeTwo (p x y : ℝ) : ℝ :=
  if x > 0 then
     Real.rpow (|((x + y) / 2)|) (p - 1) * (p / 2)
     + coeffLeTwo p * Real.rpow (|((x - y) / 2)|) (p - 1) * (p / 2)
  else 0

/-- Closed `A1` as a subset of `ℝ²`. -/
def closureA1Set (p : ℝ) : Set (ℝ × ℝ) :=
  {z | closureA1 p z.1 z.2}

/-- Closed `A2` as a subset of `ℝ²`. -/
def closureA2Set (p : ℝ) : Set (ℝ × ℝ) :=
  {z | closureA2 p z.1 z.2}

def DxuA1Fun (p : ℝ) : ℝ × ℝ → ℝ :=
  fun z => DxuA1 p z.1 z.2

def DyuA1Fun (p : ℝ) : ℝ × ℝ → ℝ :=
  fun z => DyuA1 p z.1 z.2

def DxuA1Formula (p : ℝ) : ℝ × ℝ → ℝ :=
  fun z =>
    alpha p * (p / 2) * Real.rpow z.1 (p - 2) *
      (((p - 2) / (p - 1)) * z.1 + z.2)

def DyuA1Formula (p : ℝ) : ℝ × ℝ → ℝ :=
  fun z => alpha p * Real.rpow z.1 (p - 1) * (pStar p / 2)

def DxvLeTwoFun (p : ℝ) : ℝ × ℝ → ℝ :=
  fun z => DxvLeTwo p z.1 z.2

def DyvLeTwoFun (p : ℝ) : ℝ × ℝ → ℝ :=
  fun z => DyvLeTwo p z.1 z.2

def DxvLeTwoFormula (p : ℝ) : ℝ × ℝ → ℝ :=
  fun z =>
    Real.rpow (|((z.1 + z.2) / 2)|) (p - 1) * (p / 2) -
      coeffLeTwo p * Real.rpow (|((z.1 - z.2) / 2)|) (p - 1) * (p / 2)

def DyvLeTwoFormula (p : ℝ) : ℝ × ℝ → ℝ :=
  fun z =>
    Real.rpow (|((z.1 + z.2) / 2)|) (p - 1) * (p / 2) +
      coeffLeTwo p * Real.rpow (|((z.1 - z.2) / 2)|) (p - 1) * (p / 2)

open Topology

/-! ## 2. Continuity of the local first partials -/



def auxFunction1 (p x y : ℝ) : ℝ :=
    by
    classical
    exact
      if  closureA1 p x y then
         uA1 p x y
      else if closureA2 p x y then
          vLeTwo p x y
        else 0

def DxauxFunction1 (p x y : ℝ) : ℝ :=
    by
    classical
    exact
      if closureA1 p x y then
        DxuA1 p x y
      else if closureA2 p x y then
        DxvLeTwo p x y
      else 0

def DyauxFunction1 (p x y : ℝ) : ℝ :=
    by
    classical
    exact
      if closureA1 p x y then
        DyuA1 p x y
      else if closureA2 p x y then
        DyvLeTwo p x y
      else 0

/-! ## 3. Quadrants and the global candidate -/

/-
`auxFunction1` lives in the first quadrant cone.  The global candidate is built
by reflecting this auxiliary function into the other three cones.  The order of
the `if` branches is important on shared boundaries; later boundary lemmas prove
that the chosen formulas agree where they need to.
-/

def QuarterPlane (x y : ℝ) : Prop := 0 ≤ x ∧ y ≤ x ∧ -x ≤ y

def QuarterPlaneOpen (x y : ℝ) : Prop := 0 < x ∧ y < x ∧ -x < y

def QuarterPlane2 (x y : ℝ) : Prop := x ≤ 0 ∧ y ≤ -x ∧ x ≤ y

def QuarterPlane2Open (x y : ℝ) : Prop := x < 0 ∧ y < -x ∧ x < y

def QuarterPlane3 (x y : ℝ) : Prop := y ≥  0 ∧ -y ≤ x ∧ x ≤ y

def QuarterPlane3Open (x y : ℝ) : Prop := 0 < y ∧ -y < x ∧ x < y

def QuarterPlane4 (x y : ℝ) : Prop := y ≤ 0 ∧ y ≤ x ∧ x ≤ -y

def QuarterPlane4Open (x y : ℝ) : Prop := y < 0 ∧ y < x ∧ x < -y



def uCandidate (p x y : ℝ) : ℝ :=
  by
    classical
    exact
      if QuarterPlane  x y then
        auxFunction1  p x y
      else  if QuarterPlane2 x y then
        auxFunction1  p (-x) (-y)
      else if QuarterPlane3 x y then
        auxFunction1  p y x
      else if QuarterPlane4 x y then
        auxFunction1  p (-y) (-x)
      else 0

def DxuCandidate (p x y : ℝ) : ℝ :=
  by
    classical
    exact
      if QuarterPlane x y then
        DxauxFunction1 p x y
      else if QuarterPlane2 x y then
        -DxauxFunction1 p (-x) (-y)
      else if QuarterPlane3 x y then
        DyauxFunction1 p y x
      else if QuarterPlane4 x y then
        -DyauxFunction1 p (-y) (-x)
      else 0

def DyuCandidate (p x y : ℝ) : ℝ :=
  by
    classical
    exact
      if QuarterPlane x y then
        DyauxFunction1 p x y
      else if QuarterPlane2 x y then
        -DyauxFunction1 p (-x) (-y)
      else if QuarterPlane3 x y then
        DxauxFunction1 p y x
      else if QuarterPlane4 x y then
        -DxauxFunction1 p (-y) (-x)
      else 0


/-! ## 4. Boundary compatibility and continuity of the glued functions -/



/-! 13. Majorant existence statement -/

/-
This final theorem packages the candidate with the axis-supported tangent
inequality, pointwise majorization, and negativity on the opposing-sign region.
-/

lemma v_eq_vLeTwo_of_one_lt_of_lt_two
    (p x y : ℝ) (hp1 : 1 < p) (hp2 : p < 2) :
    v p x y = vLeTwo p x y := by
  have hp_ne_one : p ≠ 1 := by linarith
  have hpden_pos : 0 < p - 1 := by linarith
  have hpStar : pStar p = q p :=
    pStar_eq_q_of_one_lt_of_lt_two p hp1 hp2
  have hq : q p = p / (p - 1) := by
    simp [q, hp_ne_one]
  have hcoeff_abs : |pStar p - 1| = (p - 1)⁻¹ := by
    rw [hpStar, hq]
    have hcalc : p / (p - 1) - 1 = (p - 1)⁻¹ := by
      field_simp [hpden_pos.ne']
      ring
    rw [hcalc]
    exact abs_of_pos (inv_pos.mpr hpden_pos)
  simp [v, vLeTwo, coeffLeTwo, hcoeff_abs]

lemma one_le_coeffLeTwo_of_one_lt_of_lt_two
    (p : ℝ) (hp1 : 1 < p) (hp2 : p < 2) :
    1 ≤ coeffLeTwo p := by
  have hp_nonneg : 0 ≤ p := by linarith
  have hbase : 1 ≤ (p - 1)⁻¹ := by
    have hp1_pos : 0 < p - 1 := by linarith
    rw [show (p - 1)⁻¹ = 1 / (p - 1) by rw [one_div]]
    rw [le_div_iff₀ hp1_pos]
    linarith
  simpa [coeffLeTwo, Real.one_rpow] using
    Real.rpow_le_rpow (by norm_num : (0 : ℝ) ≤ 1) hbase hp_nonneg

lemma coeffLeTwo_nonneg_of_one_lt_of_lt_two
    (p : ℝ) (_hp1 : 1 < p) (_hp2 : p < 2) :
    0 ≤ coeffLeTwo p := by
  unfold coeffLeTwo
  exact Real.rpow_nonneg (inv_nonneg.mpr (by linarith : 0 ≤ p - 1)) p

lemma pStar_pos_of_one_lt_of_lt_two
    (p : ℝ) (hp1 : 1 < p) (hp2 : p < 2) :
    0 < pStar p := by
  have hpStar : pStar p = q p :=
    pStar_eq_q_of_one_lt_of_lt_two p hp1 hp2
  have hp_ne_one : p ≠ 1 := by linarith
  have hp_pos : 0 < p := by linarith
  have hpden_pos : 0 < p - 1 := by linarith
  rw [hpStar]
  simp [q, hp_ne_one]
  exact div_pos hp_pos hpden_pos

lemma a_nonneg_of_one_lt_of_lt_two
    (p : ℝ) (hp1 : 1 < p) (hp2 : p < 2) :
    0 ≤ a p := by
  have hpStar : pStar p = q p :=
    pStar_eq_q_of_one_lt_of_lt_two p hp1 hp2
  have hp_ne_one : p ≠ 1 := by linarith
  have hpden_pos : 0 < p - 1 := by linarith
  rw [a, hpStar]
  simp [q, hp_ne_one]
  field_simp [hpden_pos.ne']
  linarith

lemma one_le_half_pStar_of_one_lt_of_lt_two
    (p : ℝ) (hp1 : 1 < p) (hp2 : p < 2) :
    1 ≤ pStar p / 2 := by
  have hpStar : pStar p = q p :=
    pStar_eq_q_of_one_lt_of_lt_two p hp1 hp2
  have hp_ne_one : p ≠ 1 := by linarith
  have hpden_pos : 0 < p - 1 := by linarith
  rw [hpStar]
  simp [q, hp_ne_one]
  rw [le_div_iff₀ (by norm_num : (0 : ℝ) < 2)]
  rw [le_div_iff₀ hpden_pos]
  ring_nf
  linarith

lemma alpha_nonneg_of_one_lt_of_lt_two
    (p : ℝ) (hp1 : 1 < p) (hp2 : p < 2) :
    0 ≤ alpha p := by
  have hpStar_eq : pStar p = q p :=
    pStar_eq_q_of_one_lt_of_lt_two p hp1 hp2
  have hp_ne_one : p ≠ 1 := by linarith
  have hp_pos : 0 < p := by linarith
  have hpden_pos : 0 < p - 1 := by linarith
  have hps_pos : 0 < pStar p := by
    rw [hpStar_eq]
    simp [q, hp_ne_one]
    exact div_pos hp_pos hpden_pos
  have hpsm_pos : 0 < pStar p - 1 := by
    rw [hpStar_eq]
    simp [q, hp_ne_one]
    field_simp [hpden_pos.ne']
    nlinarith
  unfold alpha
  exact mul_nonneg hp_pos.le (Real.rpow_nonneg (div_nonneg hps_pos.le hpsm_pos.le) _)

lemma vLeTwo_le_zero_of_mul_nonpos_leTwo
    (p x y : ℝ) (hp1 : 1 < p) (hp2 : p < 2) (hxy : x * y ≤ 0) :
    vLeTwo p x y ≤ 0 := by
  have hp_nonneg : 0 ≤ p := by linarith
  have hsq : ((x + y) / 2) ^ 2 ≤ ((x - y) / 2) ^ 2 := by
    nlinarith
  have habs : |(x + y) / 2| ≤ |(x - y) / 2| := sq_le_sq.mp hsq
  have hpow :
      Real.rpow (|(x + y) / 2|) p ≤ Real.rpow (|(x - y) / 2|) p :=
    Real.rpow_le_rpow (abs_nonneg _) habs hp_nonneg
  have hcoef : 1 ≤ coeffLeTwo p :=
    one_le_coeffLeTwo_of_one_lt_of_lt_two p hp1 hp2
  have hdiff_nonneg : 0 ≤ Real.rpow (|(x - y) / 2|) p :=
    Real.rpow_nonneg (abs_nonneg _) _
  have hmul :
      Real.rpow (|(x - y) / 2|) p ≤
        coeffLeTwo p * Real.rpow (|(x - y) / 2|) p := by
    simpa [one_mul] using mul_le_mul_of_nonneg_right hcoef hdiff_nonneg
  exact sub_nonpos.mpr (hpow.trans hmul)

lemma uA1_le_zero_of_y_nonpos_leTwo
    (p x y : ℝ) (hp1 : 1 < p) (hp2 : p < 2)
    (hx : 0 ≤ x) (hy : y ≤ 0) :
    uA1 p x y ≤ 0 := by
  rcases hx.eq_or_lt with rfl | hxpos
  · simp [uA1]
  · have hx_nonneg : 0 ≤ x := le_of_lt hxpos
    have halpha : 0 ≤ alpha p :=
      alpha_nonneg_of_one_lt_of_lt_two p hp1 hp2
    have hrpow : 0 ≤ x ^ (p - 1) := Real.rpow_nonneg hx_nonneg _
    have hhalf : 1 ≤ pStar p / 2 :=
      one_le_half_pStar_of_one_lt_of_lt_two p hp1 hp2
    have hhalf_nonneg : 0 ≤ pStar p / 2 := le_trans zero_le_one hhalf
    have hxy_le : x ≤ x - y := by linarith
    have hx_le_halfx : x ≤ (pStar p / 2) * x := by
      simpa [one_mul] using mul_le_mul_of_nonneg_right hhalf hx_nonneg
    have hhalf_mono :
        (pStar p / 2) * x ≤ (pStar p / 2) * (x - y) :=
      mul_le_mul_of_nonneg_left hxy_le hhalf_nonneg
    have hbracket : x - pStar p * (x - y) / 2 ≤ 0 := by
      have hmain : x ≤ (pStar p / 2) * (x - y) :=
        hx_le_halfx.trans hhalf_mono
      have hrewrite : (pStar p / 2) * (x - y) = pStar p * (x - y) / 2 := by ring
      linarith
    have hprod_nonneg : 0 ≤ alpha p * x ^ (p - 1) :=
      mul_nonneg halpha hrpow
    simp [uA1, hxpos]
    exact mul_nonpos_of_nonneg_of_nonpos hprod_nonneg hbracket

lemma mem_some_QuarterPlane_leTwo (x y : ℝ) :
    QuarterPlane x y ∨ QuarterPlane2 x y ∨ QuarterPlane3 x y ∨ QuarterPlane4 x y := by
  by_cases hxy : |x| ≤ |y|
  · by_cases hy : 0 ≤ y
    · have habs : |x| ≤ y := by simpa [abs_of_nonneg hy] using hxy
      rcases abs_le.mp habs with ⟨h1, h2⟩
      exact Or.inr (Or.inr (Or.inl ⟨hy, h1, h2⟩))
    · have hy' : y < 0 := lt_of_not_ge hy
      have habs : |x| ≤ -y := by simpa [abs_of_neg hy'] using hxy
      rcases abs_le.mp habs with ⟨h1, h2⟩
      have h1' : y ≤ x := by simpa using h1
      exact Or.inr (Or.inr (Or.inr ⟨le_of_lt hy', h1', h2⟩))
  · have hyx : |y| ≤ |x| := le_of_lt (not_le.mp hxy)
    by_cases hx : 0 ≤ x
    · have habs : |y| ≤ x := by simpa [abs_of_nonneg hx] using hyx
      rcases abs_le.mp habs with ⟨h1, h2⟩
      exact Or.inl ⟨hx, h2, h1⟩
    · have hx' : x < 0 := lt_of_not_ge hx
      have habs : |y| ≤ -x := by simpa [abs_of_neg hx'] using hyx
      rcases abs_le.mp habs with ⟨h1, h2⟩
      have h1' : x ≤ y := by simpa using h1
      exact Or.inr (Or.inl ⟨le_of_lt hx', h2, h1'⟩)

lemma uCandidate_eq_Q1_leTwo
    (p : ℝ) {x y : ℝ} (hQ : QuarterPlane x y) :
    uCandidate p x y = auxFunction1 p x y := by
  simp [uCandidate, hQ]

lemma uCandidate_eq_Q2_leTwo
    (p : ℝ) {x y : ℝ} (hQ : QuarterPlane2 x y) :
    uCandidate p x y = auxFunction1 p (-x) (-y) := by
  by_cases hQ1 : QuarterPlane x y
  · obtain ⟨hx0, hyx, _⟩ := hQ1
    obtain ⟨hx1, _, hxy⟩ := hQ
    have hx : x = 0 := le_antisymm hx1 hx0
    have hy : y = 0 := by
      have hy_le : y ≤ 0 := by simpa [hx] using hyx
      have hy_ge : 0 ≤ y := by simpa [hx] using hxy
      exact le_antisymm hy_le hy_ge
    subst x
    subst y
    simp [uCandidate, auxFunction1, QuarterPlane, closureA1, uA1]
  · simp [uCandidate, hQ1, hQ]

lemma uCandidate_eq_Q3_leTwo
    (p : ℝ) {x y : ℝ} (hQ : QuarterPlane3 x y) :
    uCandidate p x y = auxFunction1 p y x := by
  by_cases hQ1 : QuarterPlane x y
  · have hbranch := uCandidate_eq_Q1_leTwo p (hQ := hQ1)
    obtain ⟨_, hyx, _⟩ := hQ1
    obtain ⟨_, _, hxy⟩ := hQ
    have hxy' : x = y := le_antisymm hxy hyx
    calc
      uCandidate p x y = auxFunction1 p x y := hbranch
      _ = auxFunction1 p y x := by rw [hxy']
  · by_cases hQ2 : QuarterPlane2 x y
    · have hbranch := uCandidate_eq_Q2_leTwo p (hQ := hQ2)
      obtain ⟨_, hynegx, _⟩ := hQ2
      obtain ⟨_, hnegyx, _⟩ := hQ
      have hx : x = -y := le_antisymm (by linarith [hynegx]) hnegyx
      calc
        uCandidate p x y = auxFunction1 p (-x) (-y) := hbranch
        _ = auxFunction1 p y x := by rw [hx]; simp
    · simp [uCandidate, hQ1, hQ2, hQ]

lemma uCandidate_eq_Q4_leTwo
    (p : ℝ) {x y : ℝ} (hQ : QuarterPlane4 x y) :
    uCandidate p x y = auxFunction1 p (-y) (-x) := by
  by_cases hQ1 : QuarterPlane x y
  · have hbranch := uCandidate_eq_Q1_leTwo p (hQ := hQ1)
    obtain ⟨_, _, hnegxy⟩ := hQ1
    obtain ⟨_, _, hxnegy⟩ := hQ
    have hy : y = -x := by linarith
    calc
      uCandidate p x y = auxFunction1 p x y := hbranch
      _ = auxFunction1 p (-y) (-x) := by rw [hy]; simp
  · by_cases hQ2 : QuarterPlane2 x y
    · have hbranch := uCandidate_eq_Q2_leTwo p (hQ := hQ2)
      obtain ⟨_, _, hxy⟩ := hQ2
      obtain ⟨_, hyx, _⟩ := hQ
      have hxy' : x = y := le_antisymm hxy hyx
      calc
        uCandidate p x y = auxFunction1 p (-x) (-y) := hbranch
        _ = auxFunction1 p (-y) (-x) := by rw [hxy']
    · by_cases hQ3 : QuarterPlane3 x y
      · have hbranch := uCandidate_eq_Q3_leTwo p (hQ := hQ3)
        obtain ⟨hy0, hnegyx, _⟩ := hQ3
        obtain ⟨hy1, _, hxnegy⟩ := hQ
        have hy : y = 0 := le_antisymm hy1 hy0
        have hx : x = 0 := by
          have hx_le : x ≤ 0 := by simpa [hy] using hxnegy
          have hx_ge : 0 ≤ x := by simpa [hy] using hnegyx
          exact le_antisymm hx_le hx_ge
        calc
          uCandidate p x y = auxFunction1 p y x := hbranch
          _ = auxFunction1 p (-y) (-x) := by rw [hx, hy]; simp
      · simp [uCandidate, hQ1, hQ2, hQ3, hQ]

lemma uCandidate_swap_leTwo
    (p : ℝ) (x y : ℝ) :
    uCandidate p x y = uCandidate p y x := by
  rcases mem_some_QuarterPlane_leTwo x y with hQ1 | hrest
  · have hswap : QuarterPlane3 y x := ⟨hQ1.1, hQ1.2.2, hQ1.2.1⟩
    rw [uCandidate_eq_Q1_leTwo p hQ1, uCandidate_eq_Q3_leTwo p hswap]
  rcases hrest with hQ2 | hrest
  · have hswap : QuarterPlane4 y x := ⟨hQ2.1, hQ2.2.2, hQ2.2.1⟩
    rw [uCandidate_eq_Q2_leTwo p hQ2, uCandidate_eq_Q4_leTwo p hswap]
  rcases hrest with hQ3 | hQ4
  · have hswap : QuarterPlane y x := ⟨hQ3.1, hQ3.2.2, hQ3.2.1⟩
    rw [uCandidate_eq_Q3_leTwo p hQ3, uCandidate_eq_Q1_leTwo p hswap]
  · have hswap : QuarterPlane2 y x := ⟨hQ4.1, hQ4.2.2, hQ4.2.1⟩
    rw [uCandidate_eq_Q4_leTwo p hQ4, uCandidate_eq_Q2_leTwo p hswap]

lemma axis_tangent_inequality_of_coordinate_tangents_leTwo
    (u ux uy : ℝ → ℝ → ℝ)
    (hx_tangent : ∀ x y h, u (x + h) y ≤ u x y + ux x y * h)
    (hy_tangent : ∀ x y k, u x (y + k) ≤ u x y + uy x y * k)
    (x y h k : ℝ) (hk : h * k = 0) :
    u (x + h) (y + k) ≤ u x y + ux x y * h + uy x y * k := by
  rcases mul_eq_zero.mp hk with hh | hk'
  · subst h
    simpa [add_assoc] using hy_tangent x y k
  · subst k
    simpa [add_assoc] using hx_tangent x y h

lemma DxuCandidate_eq_Q1_leTwo
    (p : ℝ) {x y : ℝ} (hQ : QuarterPlane x y) :
    DxuCandidate p x y = DxauxFunction1 p x y := by
  simp [DxuCandidate, hQ]

lemma DyuCandidate_eq_Q1_leTwo
    (p : ℝ) {x y : ℝ} (hQ : QuarterPlane x y) :
    DyuCandidate p x y = DyauxFunction1 p x y := by
  simp [DyuCandidate, hQ]

lemma DxuCandidate_eq_Q2_leTwo
    (p : ℝ) {x y : ℝ} (hQ : QuarterPlane2 x y) :
    DxuCandidate p x y = -DxauxFunction1 p (-x) (-y) := by
  by_cases hQ1 : QuarterPlane x y
  · obtain ⟨hx0, hyx, _⟩ := hQ1
    obtain ⟨hx1, _, hxy⟩ := hQ
    have hx : x = 0 := le_antisymm hx1 hx0
    have hy : y = 0 := by
      have hy_le : y ≤ 0 := by simpa [hx] using hyx
      have hy_ge : 0 ≤ y := by simpa [hx] using hxy
      exact le_antisymm hy_le hy_ge
    subst x
    subst y
    simp [DxuCandidate, DxauxFunction1, QuarterPlane, closureA1, DxuA1]
  · simp [DxuCandidate, hQ1, hQ]

lemma DyuCandidate_eq_Q2_leTwo
    (p : ℝ) {x y : ℝ} (hQ : QuarterPlane2 x y) :
    DyuCandidate p x y = -DyauxFunction1 p (-x) (-y) := by
  by_cases hQ1 : QuarterPlane x y
  · obtain ⟨hx0, hyx, _⟩ := hQ1
    obtain ⟨hx1, _, hxy⟩ := hQ
    have hx : x = 0 := le_antisymm hx1 hx0
    have hy : y = 0 := by
      have hy_le : y ≤ 0 := by simpa [hx] using hyx
      have hy_ge : 0 ≤ y := by simpa [hx] using hxy
      exact le_antisymm hy_le hy_ge
    subst x
    subst y
    simp [DyuCandidate, DyauxFunction1, QuarterPlane, closureA1, DyuA1]
  · simp [DyuCandidate, hQ1, hQ]

lemma auxFunction1_le_zero_of_QuarterPlane_mul_nonpos_leTwo
    (p x y : ℝ) (hp1 : 1 < p) (hp2 : p < 2)
    (hQ : QuarterPlane x y) (hxy : x * y ≤ 0) :
    auxFunction1 p x y ≤ 0 := by
  have ha_nonneg : 0 ≤ a p := a_nonneg_of_one_lt_of_lt_two p hp1 hp2
  have hy_nonpos : y ≤ 0 := by
    by_contra hy_not
    have hy_pos : 0 < y := lt_of_not_ge hy_not
    have hx_pos : 0 < x := lt_of_lt_of_le hy_pos hQ.2.1
    have hprod_pos : 0 < x * y := mul_pos hx_pos hy_pos
    linarith
  have hA1 : closureA1 p x y := by
    refine ⟨hQ.1, hQ.2.2, ?_⟩
    exact le_trans hy_nonpos (mul_nonneg ha_nonneg hQ.1)
  rw [auxFunction1]
  simp [hA1]
  exact uA1_le_zero_of_y_nonpos_leTwo p x y hp1 hp2 hQ.1 hy_nonpos

lemma uCandidate_le_zero_of_mul_nonpos_leTwo
    (p x y : ℝ) (hp1 : 1 < p) (hp2 : p < 2) (hxy : x * y ≤ 0) :
    uCandidate p x y ≤ 0 := by
  rcases mem_some_QuarterPlane_leTwo x y with hQ1 | hrest
  · rw [uCandidate_eq_Q1_leTwo p hQ1]
    exact auxFunction1_le_zero_of_QuarterPlane_mul_nonpos_leTwo p x y hp1 hp2 hQ1 hxy
  rcases hrest with hQ2 | hrest
  · have hQ : QuarterPlane (-x) (-y) :=
      ⟨by linarith [hQ2.1], by linarith [hQ2.2.2], by linarith [hQ2.2.1]⟩
    have hxy' : (-x) * (-y) ≤ 0 := by nlinarith
    rw [uCandidate_eq_Q2_leTwo p hQ2]
    exact auxFunction1_le_zero_of_QuarterPlane_mul_nonpos_leTwo p (-x) (-y) hp1 hp2 hQ hxy'
  rcases hrest with hQ3 | hQ4
  · have hQ : QuarterPlane y x := ⟨hQ3.1, hQ3.2.2, hQ3.2.1⟩
    have hxy' : y * x ≤ 0 := by nlinarith
    rw [uCandidate_eq_Q3_leTwo p hQ3]
    exact auxFunction1_le_zero_of_QuarterPlane_mul_nonpos_leTwo p y x hp1 hp2 hQ hxy'
  · have hQ : QuarterPlane (-y) (-x) :=
      ⟨by linarith [hQ4.1], by linarith [hQ4.2.1], by linarith [hQ4.2.2]⟩
    have hxy' : (-y) * (-x) ≤ 0 := by nlinarith
    rw [uCandidate_eq_Q4_leTwo p hQ4]
    exact auxFunction1_le_zero_of_QuarterPlane_mul_nonpos_leTwo p (-y) (-x) hp1 hp2 hQ hxy'

lemma uCandidate_le_zero_of_xy_zero_leTwo
    (p x y : ℝ) (hp1 : 1 < p) (hp2 : p < 2) (hxy : x * y = 0) :
    uCandidate p x y ≤ 0 :=
  uCandidate_le_zero_of_mul_nonpos_leTwo p x y hp1 hp2 (le_of_eq hxy)

lemma a_eq_leTwo (p : ℝ) (hp1 : 1 < p) (hp2 : p < 2) :
    a p = (2 - p) / p := by
  have hpStar : pStar p = q p :=
    pStar_eq_q_of_one_lt_of_lt_two p hp1 hp2
  have hp_ne_one : p ≠ 1 := by linarith
  have hp_pos : 0 < p := by linarith
  have hpden_pos : 0 < p - 1 := by linarith
  rw [a, hpStar]
  simp [q, hp_ne_one]
  field_simp [hp_pos.ne', hpden_pos.ne']
  ring

lemma alpha_eq_leTwo (p : ℝ) (hp1 : 1 < p) (hp2 : p < 2) :
    alpha p = p * p ^ (1 - p) := by
  have hpStar : pStar p = q p :=
    pStar_eq_q_of_one_lt_of_lt_two p hp1 hp2
  have hp_ne_one : p ≠ 1 := by linarith
  have hp_pos : 0 < p := by linarith
  have hpden_pos : 0 < p - 1 := by linarith
  rw [alpha, hpStar]
  simp [q, hp_ne_one]
  have hbase : (p / (p - 1)) / (p / (p - 1) - 1) = p := by
    field_simp [hp_pos.ne', hpden_pos.ne']
    ring
  simp [hbase]

lemma a_lt_one_of_one_lt_of_lt_two
    (p : ℝ) (hp1 : 1 < p) (hp2 : p < 2) :
    a p < 1 := by
  rw [a_eq_leTwo p hp1 hp2]
  have hp_pos : 0 < p := by linarith
  rw [div_lt_iff₀ hp_pos]
  linarith

lemma DxauxFunction1_eq_DyauxFunction1_on_diag_leTwo
    (p : ℝ) (hp1 : 1 < p) (hp2 : p < 2) (x : ℝ)
    (hx : 0 ≤ x) :
    DxauxFunction1 p x x = DyauxFunction1 p x x := by
  rcases hx.lt_or_eq with hxpos | hxeq
  · have hlt : a p < 1 := a_lt_one_of_one_lt_of_lt_two p hp1 hp2
    have hax : a p * x ≤ x :=
      (mul_le_mul_of_nonneg_right hlt.le hx).trans_eq (one_mul x)
    have hcl2 : closureA2 p x x := ⟨hx, hax, le_rfl⟩
    have hnot1 : ¬ closureA1 p x x := by
      intro h
      have hax_lt : a p * x < x := by
        simpa using mul_lt_mul_of_pos_right hlt hxpos
      exact not_le_of_gt hax_lt h.2.2
    have hp1_ne : p - 1 ≠ 0 := by linarith
    simp [DxauxFunction1, DyauxFunction1, hnot1, hcl2, DxvLeTwo, DyvLeTwo,
      hxpos, Real.zero_rpow hp1_ne]
  · subst x
    simp [DxauxFunction1, DyauxFunction1, closureA1, DxuA1, DyuA1]

lemma DxauxFunction1_eq_neg_DyauxFunction1_on_antidiag_leTwo
    (p : ℝ) (hp1 : 1 < p) (hp2 : p < 2) (x : ℝ)
    (hx : 0 ≤ x) :
    DxauxFunction1 p x (-x) = -DyauxFunction1 p x (-x) := by
  rcases hx.lt_or_eq with hxpos | hxeq
  · have ha_nonneg : 0 ≤ a p := a_nonneg_of_one_lt_of_lt_two p hp1 hp2
    have hcl1 : closureA1 p x (-x) := by
      refine ⟨hx, le_rfl, ?_⟩
      exact le_trans (neg_nonpos.mpr hx) (mul_nonneg ha_nonneg hx)
    have hpStar : pStar p = q p :=
      pStar_eq_q_of_one_lt_of_lt_two p hp1 hp2
    have hp_ne_one : p ≠ 1 := by linarith
    have hpden_ne : p - 1 ≠ 0 := by linarith
    have hpow : x ^ (p - 1) = x ^ (p - 2) * x := by
      calc
        x ^ (p - 1) = x ^ ((p - 2) + (1 : ℝ)) := by ring_nf
        _ = x ^ (p - 2) * x ^ (1 : ℝ) := by rw [Real.rpow_add hxpos]
        _ = x ^ (p - 2) * x := by rw [Real.rpow_one]
    simp [DxauxFunction1, DyauxFunction1, hcl1, DxuA1, DyuA1, hxpos,
      hpStar, q, hp_ne_one]
    rw [hpow]
    field_simp [hpden_ne]
    ring
  · subst x
    simp [DxauxFunction1, DyauxFunction1, closureA1, DxuA1, DyuA1]

lemma DxuCandidate_eq_Q3_leTwo
    (p : ℝ) (hp1 : 1 < p) (hp2 : p < 2) {x y : ℝ} (hQ : QuarterPlane3 x y) :
    DxuCandidate p x y = DyauxFunction1 p y x := by
  by_cases hQ1 : QuarterPlane x y
  · have hbranch := DxuCandidate_eq_Q1_leTwo p (hQ := hQ1)
    obtain ⟨_, hyx, _⟩ := hQ1
    obtain ⟨hy0, _, hxy⟩ := hQ
    have hxy' : x = y := le_antisymm hxy hyx
    subst x
    calc
      DxuCandidate p y y = DxauxFunction1 p y y := hbranch
      _ = DyauxFunction1 p y y :=
        DxauxFunction1_eq_DyauxFunction1_on_diag_leTwo p hp1 hp2 y hy0
  · by_cases hQ2 : QuarterPlane2 x y
    · have hbranch := DxuCandidate_eq_Q2_leTwo p (hQ := hQ2)
      obtain ⟨_, hynegx, _⟩ := hQ2
      obtain ⟨hy0, hnegyx, _⟩ := hQ
      have hx : x = -y := le_antisymm (by linarith [hynegx]) hnegyx
      subst x
      have hrel :=
        DxauxFunction1_eq_neg_DyauxFunction1_on_antidiag_leTwo p hp1 hp2 y hy0
      have h' : -DxauxFunction1 p y (-y) = DyauxFunction1 p y (-y) := by
        linarith
      calc
        DxuCandidate p (-y) y = -DxauxFunction1 p (-(-y)) (-y) := hbranch
        _ = -DxauxFunction1 p y (-y) := by simp
        _ = DyauxFunction1 p y (-y) := h'
    · simp [DxuCandidate, hQ1, hQ2, hQ]

lemma DxuCandidate_eq_Q4_leTwo
    (p : ℝ) (hp1 : 1 < p) (hp2 : p < 2) {x y : ℝ} (hQ : QuarterPlane4 x y) :
    DxuCandidate p x y = -DyauxFunction1 p (-y) (-x) := by
  by_cases hQ1 : QuarterPlane x y
  · have hbranch := DxuCandidate_eq_Q1_leTwo p (hQ := hQ1)
    obtain ⟨hx0, _, hnegxy⟩ := hQ1
    obtain ⟨_, _, hxnegy⟩ := hQ
    have hy : y = -x := by linarith
    subst y
    calc
      DxuCandidate p x (-x) = DxauxFunction1 p x (-x) := hbranch
      _ = -DyauxFunction1 p x (-x) :=
        DxauxFunction1_eq_neg_DyauxFunction1_on_antidiag_leTwo p hp1 hp2 x hx0
      _ = -DyauxFunction1 p (-(-x)) (-x) := by simp
  · by_cases hQ2 : QuarterPlane2 x y
    · have hbranch := DxuCandidate_eq_Q2_leTwo p (hQ := hQ2)
      obtain ⟨hx0, _, hxy⟩ := hQ2
      obtain ⟨_, hyx, _⟩ := hQ
      have hxy' : x = y := le_antisymm hxy hyx
      subst x
      have hnonneg : 0 ≤ -y := by linarith
      have hdiag :=
        DxauxFunction1_eq_DyauxFunction1_on_diag_leTwo p hp1 hp2 (-y) hnonneg
      calc
        DxuCandidate p y y = -DxauxFunction1 p (-y) (-y) := hbranch
        _ = -DyauxFunction1 p (-y) (-y) := by rw [hdiag]
    · by_cases hQ3 : QuarterPlane3 x y
      · have hbranch := DxuCandidate_eq_Q3_leTwo p hp1 hp2 (hQ := hQ3)
        obtain ⟨hy0, hnegyx, _⟩ := hQ3
        obtain ⟨hy1, _, hxnegy⟩ := hQ
        have hy : y = 0 := le_antisymm hy1 hy0
        have hx : x = 0 := by
          have hx_le : x ≤ 0 := by simpa [hy] using hxnegy
          have hx_ge : 0 ≤ x := by simpa [hy] using hnegyx
          exact le_antisymm hx_le hx_ge
        subst x
        subst y
        simpa [DyauxFunction1, closureA1, DyuA1] using hbranch
      · simp [DxuCandidate, hQ1, hQ2, hQ3, hQ]

lemma DyuCandidate_eq_Q3_leTwo
    (p : ℝ) (hp1 : 1 < p) (hp2 : p < 2) {x y : ℝ} (hQ : QuarterPlane3 x y) :
    DyuCandidate p x y = DxauxFunction1 p y x := by
  by_cases hQ1 : QuarterPlane x y
  · have hbranch := DyuCandidate_eq_Q1_leTwo p (hQ := hQ1)
    obtain ⟨_, hyx, _⟩ := hQ1
    obtain ⟨hy0, _, hxy⟩ := hQ
    have hxy' : x = y := le_antisymm hxy hyx
    subst x
    calc
      DyuCandidate p y y = DyauxFunction1 p y y := hbranch
      _ = DxauxFunction1 p y y :=
        (DxauxFunction1_eq_DyauxFunction1_on_diag_leTwo p hp1 hp2 y hy0).symm
  · by_cases hQ2 : QuarterPlane2 x y
    · have hbranch := DyuCandidate_eq_Q2_leTwo p (hQ := hQ2)
      obtain ⟨_, hynegx, _⟩ := hQ2
      obtain ⟨hy0, hnegyx, _⟩ := hQ
      have hx : x = -y := le_antisymm (by linarith [hynegx]) hnegyx
      subst x
      have hrel :=
        DxauxFunction1_eq_neg_DyauxFunction1_on_antidiag_leTwo p hp1 hp2 y hy0
      calc
        DyuCandidate p (-y) y = -DyauxFunction1 p (-(-y)) (-y) := hbranch
        _ = -DyauxFunction1 p y (-y) := by simp
        _ = DxauxFunction1 p y (-y) := hrel.symm
    · simp [DyuCandidate, hQ1, hQ2, hQ]

lemma DyuCandidate_eq_Q4_leTwo
    (p : ℝ) (hp1 : 1 < p) (hp2 : p < 2) {x y : ℝ} (hQ : QuarterPlane4 x y) :
    DyuCandidate p x y = -DxauxFunction1 p (-y) (-x) := by
  by_cases hQ1 : QuarterPlane x y
  · have hbranch := DyuCandidate_eq_Q1_leTwo p (hQ := hQ1)
    obtain ⟨hx0, _, hnegxy⟩ := hQ1
    obtain ⟨_, _, hxnegy⟩ := hQ
    have hy : y = -x := by linarith
    subst y
    have hrel :=
      DxauxFunction1_eq_neg_DyauxFunction1_on_antidiag_leTwo p hp1 hp2 x hx0
    have h' : DyauxFunction1 p x (-x) = -DxauxFunction1 p x (-x) := by
      linarith
    calc
      DyuCandidate p x (-x) = DyauxFunction1 p x (-x) := hbranch
      _ = -DxauxFunction1 p x (-x) := h'
      _ = -DxauxFunction1 p (-(-x)) (-x) := by simp
  · by_cases hQ2 : QuarterPlane2 x y
    · have hbranch := DyuCandidate_eq_Q2_leTwo p (hQ := hQ2)
      obtain ⟨hx0, _, hxy⟩ := hQ2
      obtain ⟨_, hyx, _⟩ := hQ
      have hxy' : x = y := le_antisymm hxy hyx
      subst x
      have hnonneg : 0 ≤ -y := by linarith
      have hdiag :=
        DxauxFunction1_eq_DyauxFunction1_on_diag_leTwo p hp1 hp2 (-y) hnonneg
      calc
        DyuCandidate p y y = -DyauxFunction1 p (-y) (-y) := hbranch
        _ = -DxauxFunction1 p (-y) (-y) := by rw [hdiag]
    · by_cases hQ3 : QuarterPlane3 x y
      · have hbranch := DyuCandidate_eq_Q3_leTwo p hp1 hp2 (hQ := hQ3)
        obtain ⟨hy0, hnegyx, _⟩ := hQ3
        obtain ⟨hy1, _, hxnegy⟩ := hQ
        have hy : y = 0 := le_antisymm hy1 hy0
        have hx : x = 0 := by
          have hx_le : x ≤ 0 := by simpa [hy] using hxnegy
          have hx_ge : 0 ≤ x := by simpa [hy] using hnegyx
          exact le_antisymm hx_le hx_ge
        subst x
        subst y
        simpa [DxauxFunction1, closureA1, DxuA1] using hbranch
      · simp [DyuCandidate, hQ1, hQ2, hQ3, hQ]

lemma DyuCandidate_eq_DxuCandidate_swap_leTwo
    (p : ℝ) (hp1 : 1 < p) (hp2 : p < 2) (x y : ℝ) :
    DyuCandidate p x y = DxuCandidate p y x := by
  rcases mem_some_QuarterPlane_leTwo x y with hQ1 | hrest
  · have hswap : QuarterPlane3 y x := ⟨hQ1.1, hQ1.2.2, hQ1.2.1⟩
    rw [DyuCandidate_eq_Q1_leTwo p hQ1,
      DxuCandidate_eq_Q3_leTwo p hp1 hp2 hswap]
  rcases hrest with hQ2 | hrest
  · have hswap : QuarterPlane4 y x := ⟨hQ2.1, hQ2.2.2, hQ2.2.1⟩
    rw [DyuCandidate_eq_Q2_leTwo p hQ2,
      DxuCandidate_eq_Q4_leTwo p hp1 hp2 hswap]
  rcases hrest with hQ3 | hQ4
  · have hswap : QuarterPlane y x := ⟨hQ3.1, hQ3.2.2, hQ3.2.1⟩
    rw [DyuCandidate_eq_Q3_leTwo p hp1 hp2 hQ3,
      DxuCandidate_eq_Q1_leTwo p hswap]
  · have hswap : QuarterPlane2 y x := ⟨hQ4.1, hQ4.2.2, hQ4.2.1⟩
    rw [DyuCandidate_eq_Q4_leTwo p hp1 hp2 hQ4,
      DxuCandidate_eq_Q2_leTwo p hswap]

lemma uA1_eq_zero_on_boundary_leTwo
    (p x : ℝ) (hp1 : 1 < p) (hp2 : p < 2) (hx : 0 < x) :
    uA1 p x ((a p) * x) = 0 := by
  have hpStar : pStar p = q p :=
    pStar_eq_q_of_one_lt_of_lt_two p hp1 hp2
  have hp_ne_one : p ≠ 1 := by linarith
  have hp_pos : 0 < p := by linarith
  have hpden_pos : 0 < p - 1 := by linarith
  unfold uA1
  rw [if_pos hx]
  have hfactor : x - pStar p * (x - a p * x) / 2 = 0 := by
    rw [hpStar, a_eq_leTwo p hp1 hp2]
    simp [q, hp_ne_one]
    field_simp [hp_pos.ne', hpden_pos.ne']
    ring
  rw [hfactor, mul_zero]

lemma vLeTwo_eq_zero_on_boundary_leTwo
    (p x : ℝ) (hp1 : 1 < p) (hp2 : p < 2) (hx : 0 < x) :
    vLeTwo p x ((a p) * x) = 0 := by
  have hp_pos : 0 < p := by linarith
  have hpden_pos : 0 < p - 1 := by linarith
  have hpden_nonneg : 0 ≤ p - 1 := le_of_lt hpden_pos
  have hx_nonneg : 0 ≤ x := le_of_lt hx
  rw [a_eq_leTwo p hp1 hp2]
  simp only [vLeTwo, coeffLeTwo]
  have hsum : (x + (2 - p) / p * x) / 2 = x / p := by
    field_simp [hp_pos.ne']
    ring
  have hdiff : (x - (2 - p) / p * x) / 2 = ((p - 1) / p) * x := by
    field_simp [hp_pos.ne']
    ring
  rw [hsum, hdiff, abs_of_pos (div_pos hx hp_pos),
    abs_of_pos (mul_pos (div_pos hpden_pos hp_pos) hx)]
  have hmul :
      (((p - 1) / p) * x) ^ p = ((p - 1) / p) ^ p * x ^ p := by
    rw [Real.mul_rpow (div_nonneg hpden_nonneg hp_pos.le) hx_nonneg]
  change (x / p) ^ p - (p - 1)⁻¹ ^ p * ((((p - 1) / p) * x) ^ p) = 0
  rw [hmul]
  have hdiv : (x / p) ^ p = x ^ p / p ^ p := by
    rw [Real.div_rpow hx_nonneg hp_pos.le]
  rw [hdiv]
  have hcoef :
      (p - 1)⁻¹ ^ p * (((p - 1) / p) ^ p * x ^ p) = x ^ p / p ^ p := by
    rw [Real.div_rpow hpden_nonneg hp_pos.le]
    have hinv_mul : (p - 1)⁻¹ ^ p * ((p - 1) ^ p * (p ^ p)⁻¹ * x ^ p)
        = x ^ p * (p ^ p)⁻¹ := by
      have hcancel : (p - 1)⁻¹ ^ p * (p - 1) ^ p = 1 := by
        rw [← Real.mul_rpow (inv_nonneg.mpr hpden_nonneg) hpden_nonneg]
        simp [hpden_pos.ne']
      calc
        (p - 1)⁻¹ ^ p * ((p - 1) ^ p * (p ^ p)⁻¹ * x ^ p)
            = ((p - 1)⁻¹ ^ p * (p - 1) ^ p) * (p ^ p)⁻¹ * x ^ p := by ring
        _ = x ^ p * (p ^ p)⁻¹ := by
          rw [hcancel]
          ring
    simpa [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using hinv_mul
  rw [hcoef]
  ring

lemma uA1_eq_vLeTwo_on_inter_leTwo
    (p : ℝ) (hp1 : 1 < p) (hp2 : p < 2) (x y : ℝ)
    (h1 : closureA1 p x y) (h2 : closureA2 p x y) :
    uA1 p x y = vLeTwo p x y := by
  obtain ⟨hx, _hneg, hy_ax⟩ := h1
  obtain ⟨_, hax_y, _hyx⟩ := h2
  have heq : y = a p * x := le_antisymm hy_ax hax_y
  rcases hx.lt_or_eq with hxpos | hxeq
  · rw [heq]
    exact (uA1_eq_zero_on_boundary_leTwo p x hp1 hp2 hxpos).trans
      (vLeTwo_eq_zero_on_boundary_leTwo p x hp1 hp2 hxpos).symm
  · have hx0 : x = 0 := hxeq.symm
    subst x
    have hy0 : y = 0 := by linarith
    subst y
    simp [uA1, vLeTwo, Real.zero_rpow (by linarith : p ≠ 0)]

lemma auxFunction1_eq_vLeTwo_leTwo
    (p : ℝ) (hp1 : 1 < p) (hp2 : p < 2) (x y : ℝ)
    (h2 : closureA2 p x y) :
    auxFunction1 p x y = vLeTwo p x y := by
  simp only [auxFunction1]
  by_cases h1 : closureA1 p x y
  · simp only [h1, ite_true]
    exact uA1_eq_vLeTwo_on_inter_leTwo p hp1 hp2 x y h1 h2
  · simp only [h1, ite_false, h2, ite_true]

lemma DxuA1_eq_DxvLeTwo_on_A1A2_boundary_leTwo
    (p x : ℝ) (hp1 : 1 < p) (hp2 : p < 2) (hx : 0 < x) :
    DxuA1 p x ((a p) * x) = DxvLeTwo p x ((a p) * x) := by
  have hp_pos : 0 < p := by linarith
  have hpden_pos : 0 < p - 1 := by linarith
  have hpden_nonneg : 0 ≤ p - 1 := hpden_pos.le
  have hx_nonneg : 0 ≤ x := hx.le
  simp [DxuA1, DxvLeTwo, hx, a_eq_leTwo p hp1 hp2, alpha_eq_leTwo p hp1 hp2]
  have hsum : (x + (2 - p) / p * x) / 2 = x / p := by
    field_simp [hp_pos.ne']
    ring
  have hdiff : (x - (2 - p) / p * x) / 2 = ((p - 1) / p) * x := by
    field_simp [hp_pos.ne']
    ring
  rw [hsum, hdiff, abs_of_pos (div_pos hx hp_pos),
    abs_of_pos (mul_pos (div_pos hpden_pos hp_pos) hx)]
  have hmul_diff :
      (((p - 1) / p) * x) ^ (p - 1) =
        ((p - 1) / p) ^ (p - 1) * x ^ (p - 1) := by
    rw [Real.mul_rpow (div_nonneg hpden_nonneg hp_pos.le) hx_nonneg]
  have hdiv_x : (x / p) ^ (p - 1) = x ^ (p - 1) / p ^ (p - 1) := by
    rw [Real.div_rpow hx_nonneg hp_pos.le]
  have hdiv_coeff :
      ((p - 1) / p) ^ (p - 1) =
        (p - 1) ^ (p - 1) / p ^ (p - 1) := by
    rw [Real.div_rpow hpden_nonneg hp_pos.le]
  rw [hmul_diff, hdiv_x, hdiv_coeff]
  have hbr :
      (p - 2) / (p - 1) * x + (2 - p) / p * x =
        ((p - 2) / (p * (p - 1))) * x := by
    field_simp [hp_pos.ne', hpden_pos.ne']
    ring
  rw [hbr]
  have hxpow : x ^ (p - 2) * x = x ^ (p - 1) := by
    calc
      x ^ (p - 2) * x = x ^ (p - 2) * x ^ (1 : ℝ) := by rw [Real.rpow_one]
      _ = x ^ ((p - 2) + 1) := by rw [← Real.rpow_add hx]
      _ = x ^ (p - 1) := by ring_nf
  have hxpow' :
      x ^ (p - 2) * (((p - 2) / (p * (p - 1))) * x) =
        ((p - 2) / (p * (p - 1))) * x ^ (p - 1) := by
    calc
      x ^ (p - 2) * (((p - 2) / (p * (p - 1))) * x)
          = ((p - 2) / (p * (p - 1))) * (x ^ (p - 2) * x) := by ring
      _ = ((p - 2) / (p * (p - 1))) * x ^ (p - 1) := by rw [hxpow]
  rw [show
    p * p ^ (1 - p) * (p / 2) * x ^ (p - 2) *
        (((p - 2) / (p * (p - 1))) * x) =
      p * p ^ (1 - p) * (p / 2) *
        (x ^ (p - 2) * (((p - 2) / (p * (p - 1))) * x)) by ring]
  rw [hxpow']
  have hcancel :
      Real.rpow ((p - 1)⁻¹) p *
          ((p - 1) ^ (p - 1) / p ^ (p - 1) * x ^ (p - 1)) =
        ((p - 1)⁻¹ / p ^ (p - 1)) * x ^ (p - 1) := by
    have hpow : (p - 1)⁻¹ ^ p * (p - 1) ^ (p - 1) = (p - 1)⁻¹ := by
      have hcancel0 :
          (p - 1)⁻¹ ^ (p - 1) * (p - 1) ^ (p - 1) = 1 := by
        rw [← Real.mul_rpow (inv_nonneg.mpr hpden_nonneg) hpden_nonneg]
        simp [hpden_pos.ne']
      have hsplit :
          (p - 1)⁻¹ ^ p =
            (p - 1)⁻¹ ^ (p - 1) * (p - 1)⁻¹ := by
        calc
          (p - 1)⁻¹ ^ p = (p - 1)⁻¹ ^ ((p - 1) + 1) := by
            congr 1
            ring
          _ = (p - 1)⁻¹ ^ (p - 1) * (p - 1)⁻¹ ^ (1 : ℝ) := by
            rw [Real.rpow_add (inv_pos.mpr hpden_pos)]
          _ = (p - 1)⁻¹ ^ (p - 1) * (p - 1)⁻¹ := by
            rw [Real.rpow_one]
      rw [hsplit]
      calc
        ((p - 1)⁻¹ ^ (p - 1) * (p - 1)⁻¹) * (p - 1) ^ (p - 1)
            = ((p - 1)⁻¹ ^ (p - 1) * (p - 1) ^ (p - 1)) * (p - 1)⁻¹ := by ring
        _ = (p - 1)⁻¹ := by
          rw [hcancel0]
          ring
    rw [div_eq_mul_inv]
    calc
      (p - 1)⁻¹ ^ p * ((p - 1) ^ (p - 1) * (p ^ (p - 1))⁻¹ * x ^ (p - 1))
          = ((p - 1)⁻¹ ^ p * (p - 1) ^ (p - 1)) * (p ^ (p - 1))⁻¹ *
              x ^ (p - 1) := by ring
      _ = (p - 1)⁻¹ * (p ^ (p - 1))⁻¹ * x ^ (p - 1) := by rw [hpow]
  rw [coeffLeTwo]
  rw [hcancel]
  have hp_pow_cancel : p ^ (1 - p) * p ^ (-1 + p) = 1 := by
    calc
      p ^ (1 - p) * p ^ (-1 + p) = p ^ ((1 - p) + (-1 + p)) := by
        rw [← Real.rpow_add hp_pos]
      _ = p ^ (0 : ℝ) := by ring_nf
      _ = 1 := by rw [Real.rpow_zero]
  have hp_pow_cancel' : p ^ (1 - p) * p ^ (p - 1) = 1 := by
    simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using hp_pow_cancel
  field_simp [hp_pos.ne', hpden_pos.ne']
  rw [show p ^ (1 - p) * (p - 2) * p ^ (p - 1) =
      (p - 2) * (p ^ (1 - p) * p ^ (p - 1)) by ring]
  rw [hp_pow_cancel']
  ring

lemma DyuA1_eq_DyvLeTwo_on_A1A2_boundary_leTwo
    (p x : ℝ) (hp1 : 1 < p) (hp2 : p < 2) (hx : 0 < x) :
    DyuA1 p x ((a p) * x) = DyvLeTwo p x ((a p) * x) := by
  have hp_pos : 0 < p := by linarith
  have hpden_pos : 0 < p - 1 := by linarith
  have hpden_nonneg : 0 ≤ p - 1 := hpden_pos.le
  have hx_nonneg : 0 ≤ x := hx.le
  have hpStar : pStar p = q p := pStar_eq_q_of_one_lt_of_lt_two p hp1 hp2
  have hp_ne_one : p ≠ 1 := by linarith
  simp [DyuA1, DyvLeTwo, hx, hpStar, q, hp_ne_one,
    a_eq_leTwo p hp1 hp2, alpha_eq_leTwo p hp1 hp2]
  have hsum : (x + (2 - p) / p * x) / 2 = x / p := by
    field_simp [hp_pos.ne']
    ring
  have hdiff : (x - (2 - p) / p * x) / 2 = ((p - 1) / p) * x := by
    field_simp [hp_pos.ne']
    ring
  rw [hsum, hdiff, abs_of_pos (div_pos hx hp_pos),
    abs_of_pos (mul_pos (div_pos hpden_pos hp_pos) hx)]
  have hmul_diff :
      (((p - 1) / p) * x) ^ (p - 1) =
        ((p - 1) / p) ^ (p - 1) * x ^ (p - 1) := by
    rw [Real.mul_rpow (div_nonneg hpden_nonneg hp_pos.le) hx_nonneg]
  have hdiv_x : (x / p) ^ (p - 1) = x ^ (p - 1) / p ^ (p - 1) := by
    rw [Real.div_rpow hx_nonneg hp_pos.le]
  have hdiv_coeff :
      ((p - 1) / p) ^ (p - 1) =
        (p - 1) ^ (p - 1) / p ^ (p - 1) := by
    rw [Real.div_rpow hpden_nonneg hp_pos.le]
  rw [hmul_diff, hdiv_x, hdiv_coeff]
  have hcancel :
      Real.rpow ((p - 1)⁻¹) p *
          ((p - 1) ^ (p - 1) / p ^ (p - 1) * x ^ (p - 1)) =
        ((p - 1)⁻¹ / p ^ (p - 1)) * x ^ (p - 1) := by
    have hpow : (p - 1)⁻¹ ^ p * (p - 1) ^ (p - 1) = (p - 1)⁻¹ := by
      have hcancel0 :
          (p - 1)⁻¹ ^ (p - 1) * (p - 1) ^ (p - 1) = 1 := by
        rw [← Real.mul_rpow (inv_nonneg.mpr hpden_nonneg) hpden_nonneg]
        simp [hpden_pos.ne']
      have hsplit :
          (p - 1)⁻¹ ^ p =
            (p - 1)⁻¹ ^ (p - 1) * (p - 1)⁻¹ := by
        calc
          (p - 1)⁻¹ ^ p = (p - 1)⁻¹ ^ ((p - 1) + 1) := by
            congr 1
            ring
          _ = (p - 1)⁻¹ ^ (p - 1) * (p - 1)⁻¹ ^ (1 : ℝ) := by
            rw [Real.rpow_add (inv_pos.mpr hpden_pos)]
          _ = (p - 1)⁻¹ ^ (p - 1) * (p - 1)⁻¹ := by
            rw [Real.rpow_one]
      rw [hsplit]
      calc
        ((p - 1)⁻¹ ^ (p - 1) * (p - 1)⁻¹) * (p - 1) ^ (p - 1)
            = ((p - 1)⁻¹ ^ (p - 1) * (p - 1) ^ (p - 1)) * (p - 1)⁻¹ := by ring
        _ = (p - 1)⁻¹ := by
          rw [hcancel0]
          ring
    rw [div_eq_mul_inv]
    calc
      (p - 1)⁻¹ ^ p * ((p - 1) ^ (p - 1) * (p ^ (p - 1))⁻¹ * x ^ (p - 1))
          = ((p - 1)⁻¹ ^ p * (p - 1) ^ (p - 1)) * (p ^ (p - 1))⁻¹ *
              x ^ (p - 1) := by ring
      _ = (p - 1)⁻¹ * (p ^ (p - 1))⁻¹ * x ^ (p - 1) := by rw [hpow]
  rw [coeffLeTwo]
  rw [hcancel]
  have hp_pow_cancel : p ^ (1 - p) * p ^ (-1 + p) = 1 := by
    calc
      p ^ (1 - p) * p ^ (-1 + p) = p ^ ((1 - p) + (-1 + p)) := by
        rw [← Real.rpow_add hp_pos]
      _ = p ^ (0 : ℝ) := by ring_nf
      _ = 1 := by rw [Real.rpow_zero]
  have hp_pow_cancel' : p ^ (1 - p) * p ^ (p - 1) = 1 := by
    simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using hp_pow_cancel
  field_simp [hp_pos.ne', hpden_pos.ne']
  rw [show p * p ^ (1 - p) * p ^ (p - 1) =
      p * (p ^ (1 - p) * p ^ (p - 1)) by ring]
  rw [hp_pow_cancel']
  ring

lemma DxuA1_eq_DxvLeTwo_on_inter_leTwo
    (p : ℝ) (hp1 : 1 < p) (hp2 : p < 2) (x y : ℝ)
    (h1 : closureA1 p x y) (h2 : closureA2 p x y) :
    DxuA1 p x y = DxvLeTwo p x y := by
  obtain ⟨hx, _hneg, hy_ax⟩ := h1
  obtain ⟨_, hax_y, _hyx⟩ := h2
  have heq : y = a p * x := le_antisymm hy_ax hax_y
  rcases hx.lt_or_eq with hxpos | hxeq
  · rw [heq]
    exact DxuA1_eq_DxvLeTwo_on_A1A2_boundary_leTwo p x hp1 hp2 hxpos
  · have hx0 : x = 0 := hxeq.symm
    subst x
    have hy0 : y = 0 := by linarith
    subst y
    simp [DxuA1, DxvLeTwo]

lemma DyuA1_eq_DyvLeTwo_on_inter_leTwo
    (p : ℝ) (hp1 : 1 < p) (hp2 : p < 2) (x y : ℝ)
    (h1 : closureA1 p x y) (h2 : closureA2 p x y) :
    DyuA1 p x y = DyvLeTwo p x y := by
  obtain ⟨hx, _hneg, hy_ax⟩ := h1
  obtain ⟨_, hax_y, _hyx⟩ := h2
  have heq : y = a p * x := le_antisymm hy_ax hax_y
  rcases hx.lt_or_eq with hxpos | hxeq
  · rw [heq]
    exact DyuA1_eq_DyvLeTwo_on_A1A2_boundary_leTwo p x hp1 hp2 hxpos
  · have hx0 : x = 0 := hxeq.symm
    subst x
    have hy0 : y = 0 := by linarith
    subst y
    simp [DyuA1, DyvLeTwo]

lemma auxFunction1_Dx_eq_DxvLeTwo_leTwo
    (p : ℝ) (hp1 : 1 < p) (hp2 : p < 2) (x y : ℝ) (h2 : closureA2 p x y) :
    DxauxFunction1 p x y = DxvLeTwo p x y := by
  simp only [DxauxFunction1]
  by_cases h1 : closureA1 p x y
  · simp only [h1, ite_true]
    exact DxuA1_eq_DxvLeTwo_on_inter_leTwo p hp1 hp2 x y h1 h2
  · simp only [h1, ite_false, h2, ite_true]

lemma auxFunction1_Dy_eq_DyvLeTwo_leTwo
    (p : ℝ) (hp1 : 1 < p) (hp2 : p < 2) (x y : ℝ) (h2 : closureA2 p x y) :
    DyauxFunction1 p x y = DyvLeTwo p x y := by
  simp only [DyauxFunction1]
  by_cases h1 : closureA1 p x y
  · simp only [h1, ite_true]
    exact DyuA1_eq_DyvLeTwo_on_inter_leTwo p hp1 hp2 x y h1 h2
  · simp only [h1, ite_false, h2, ite_true]

lemma horizontal_boundary_closureA1_closureA2_leTwo
    (p y : ℝ) (hp1 : 1 < p) (hp2 : p < 2) (hy : 0 < y) :
    closureA1 p (y / a p) y ∧ closureA2 p (y / a p) y := by
  have ha_pos : 0 < a p := by
    rw [a_eq_leTwo p hp1 hp2]
    exact div_pos (by linarith) (by linarith)
  have ha_lt : a p < 1 := a_lt_one_of_one_lt_of_lt_two p hp1 hp2
  have hboundary : a p * (y / a p) = y := by
    field_simp [ha_pos.ne']
  have hx_pos : 0 < y / a p := div_pos hy ha_pos
  have hyx : y < y / a p := by
    rw [div_eq_mul_inv]
    have hinv : 1 < (a p)⁻¹ := by
      rw [one_lt_inv₀ ha_pos]
      exact ha_lt
    nlinarith
  have hneg : -(y / a p) < y := by
    linarith [hx_pos, hy]
  constructor
  · exact ⟨hx_pos.le, le_of_lt hneg, hboundary.ge⟩
  · exact ⟨hx_pos.le, hboundary.le, hyx.le⟩

lemma vLeTwo_neg_neg_leTwo (p x y : ℝ) :
    vLeTwo p (-x) (-y) = vLeTwo p x y := by
  have hsum : ((-x + -y) / 2 : ℝ) = -((x + y) / 2) := by ring
  have hdiff : ((-x + y) / 2 : ℝ) = -((x - y) / 2) := by ring
  simp [vLeTwo, hsum, hdiff]

lemma vLeTwo_swap_leTwo (p x y : ℝ) :
    vLeTwo p y x = vLeTwo p x y := by
  have hsum : ((y + x) / 2 : ℝ) = (x + y) / 2 := by ring
  have hdiff : ((y - x) / 2 : ℝ) = -((x - y) / 2) := by ring
  simp [vLeTwo, hsum, hdiff]

lemma vLeTwo_le_auxFunction1_on_QuarterPlane_of_A1_leTwo
    (p : ℝ) (hp1 : 1 < p) (hp2 : p < 2)
    (hA1 : ∀ ⦃x y : ℝ⦄, closureA1 p x y → vLeTwo p x y ≤ uA1 p x y)
    {x y : ℝ} (hQ : QuarterPlane x y) :
    vLeTwo p x y ≤ auxFunction1 p x y := by
  by_cases h1 : closureA1 p x y
  · exact (hA1 h1).trans_eq (by simp [auxFunction1, h1])
  · have h2 : closureA2 p x y := by
      rcases hQ with ⟨hx, hyx, hnegx_y⟩
      have hy_ge_ax : a p * x ≤ y := by
        by_contra hy_not
        exact h1 ⟨hx, hnegx_y, le_of_not_ge hy_not⟩
      exact ⟨hx, hy_ge_ax, hyx⟩
    exact le_of_eq (auxFunction1_eq_vLeTwo_leTwo p hp1 hp2 x y h2).symm

lemma vLeTwo_le_uCandidate_of_A1_leTwo
    (p : ℝ) (hp1 : 1 < p) (hp2 : p < 2)
    (hA1 : ∀ ⦃x y : ℝ⦄, closureA1 p x y → vLeTwo p x y ≤ uA1 p x y)
    (x y : ℝ) :
    vLeTwo p x y ≤ uCandidate p x y := by
  rcases mem_some_QuarterPlane_leTwo x y with hQ1 | hrest
  · rw [uCandidate_eq_Q1_leTwo p hQ1]
    exact vLeTwo_le_auxFunction1_on_QuarterPlane_of_A1_leTwo p hp1 hp2 hA1 hQ1
  rcases hrest with hQ2 | hrest
  · have hQ : QuarterPlane (-x) (-y) :=
      ⟨by linarith [hQ2.1], by linarith [hQ2.2.2], by linarith [hQ2.2.1]⟩
    rw [uCandidate_eq_Q2_leTwo p hQ2, ← vLeTwo_neg_neg_leTwo p x y]
    exact vLeTwo_le_auxFunction1_on_QuarterPlane_of_A1_leTwo p hp1 hp2 hA1 hQ
  rcases hrest with hQ3 | hQ4
  · have hQ : QuarterPlane y x := ⟨hQ3.1, hQ3.2.2, hQ3.2.1⟩
    rw [uCandidate_eq_Q3_leTwo p hQ3, ← vLeTwo_swap_leTwo p x y]
    exact vLeTwo_le_auxFunction1_on_QuarterPlane_of_A1_leTwo p hp1 hp2 hA1 hQ
  · have hQ : QuarterPlane (-y) (-x) :=
      ⟨by linarith [hQ4.1], by linarith [hQ4.2.1], by linarith [hQ4.2.2]⟩
    have hv : vLeTwo p (-y) (-x) = vLeTwo p x y := by
      rw [vLeTwo_neg_neg_leTwo p y x, vLeTwo_swap_leTwo p y x]
    rw [uCandidate_eq_Q4_leTwo p hQ4, ← hv]
    exact vLeTwo_le_auxFunction1_on_QuarterPlane_of_A1_leTwo p hp1 hp2 hA1 hQ

set_option maxHeartbeats 800000 in
lemma scalar_deriv_sum_lower_leTwo
    (p t : ℝ) (hp1 : 1 < p) (hp2 : p < 2)
    (ht_lower : (p - 1) / p ≤ t) (ht_upper : t ≤ 1) :
    alpha p * pStar p / p ≤
      (1 - t) ^ (p - 1) + coeffLeTwo p * t ^ (p - 1) := by
  let lam : ℝ := p * (1 - t)
  let mu : ℝ := p * t - (p - 1)
  have hp_pos : 0 < p := by linarith
  have hp_nonneg : 0 ≤ p := le_of_lt hp_pos
  have hpden_pos : 0 < p - 1 := by linarith
  have hp_ne : p ≠ 0 := by linarith
  have hpden_nonneg : 0 ≤ p - 1 := le_of_lt hpden_pos
  have hp_ne_one : p ≠ 1 := by linarith
  have hr_nonneg : 0 ≤ p - 1 := by linarith
  have hr_le_one : p - 1 ≤ 1 := by linarith
  have hlam_nonneg : 0 ≤ lam := by
    dsimp [lam]
    exact mul_nonneg hp_nonneg (sub_nonneg.mpr ht_upper)
  have hmu_nonneg : 0 ≤ mu := by
    dsimp [mu]
    rw [sub_nonneg]
    have h := (div_le_iff₀ hp_pos).mp ht_lower
    simpa [mul_comm] using h
  have hsum : lam + mu = 1 := by
    dsimp [lam, mu]
    ring
  have hpow_conc := Real.concaveOn_rpow hr_nonneg hr_le_one
  have hfirst :
      lam * (1 / p) ^ (p - 1) + mu * (0 : ℝ) ^ (p - 1) ≤
        (1 - t) ^ (p - 1) := by
    have hmem₁ : (1 / p : ℝ) ∈ Set.Ici 0 := by
      exact div_nonneg zero_le_one hp_nonneg
    have hmem₀ : (0 : ℝ) ∈ Set.Ici 0 := by simp
    have h :=
      hpow_conc.2 hmem₁ hmem₀ hlam_nonneg hmu_nonneg hsum
    have hcombo :
        lam • (1 / p : ℝ) + mu • (0 : ℝ) = 1 - t := by
      dsimp [lam, mu]
      field_simp [hp_ne]
      ring
    have hcombo' : lam * p⁻¹ = 1 - t := by
      dsimp [lam]
      field_simp [hp_ne]
    simpa [smul_eq_mul, one_div, hcombo'] using h
  have hsecond :
      lam * ((p - 1) / p) ^ (p - 1) + mu ≤
        t ^ (p - 1) := by
    have hmem₁ : ((p - 1) / p : ℝ) ∈ Set.Ici 0 := by
      exact div_nonneg hpden_nonneg hp_nonneg
    have hmem₂ : (1 : ℝ) ∈ Set.Ici 0 := by simp
    have h :=
      hpow_conc.2 hmem₁ hmem₂ hlam_nonneg hmu_nonneg hsum
    have hcombo :
        lam • ((p - 1) / p : ℝ) + mu • (1 : ℝ) = t := by
      dsimp [lam, mu]
      field_simp [hp_ne]
      ring
    have hcombo' : lam * ((p - 1) / p) + mu = t := by
      dsimp [lam, mu]
      field_simp [hp_ne]
      ring
    simpa [smul_eq_mul, one_div, hcombo'] using h
  have hzero : (0 : ℝ) ^ (p - 1) = 0 := Real.zero_rpow (by linarith)
  have hB :
      alpha p * pStar p / p =
        (1 / p) ^ (p - 1) + coeffLeTwo p * ((p - 1) / p) ^ (p - 1) := by
    have hpStar : pStar p = q p :=
      pStar_eq_q_of_one_lt_of_lt_two p hp1 hp2
    have halpha : alpha p = p * p ^ (1 - p) :=
      alpha_eq_leTwo p hp1 hp2
    have hp_inv_pow :
        (p ^ (p - 1))⁻¹ = p ^ (1 - p) := by
      rw [show 1 - p = -(p - 1) by ring]
      rw [Real.rpow_neg hp_nonneg]
    have hone_div_pow :
        (1 / p) ^ (p - 1) = p ^ (1 - p) := by
      rw [one_div, Real.inv_rpow hp_nonneg]
      exact hp_inv_pow
    have hcoeff_piece :
        coeffLeTwo p * ((p - 1) / p) ^ (p - 1) =
          (p - 1)⁻¹ * p ^ (1 - p) := by
      rw [coeffLeTwo, Real.div_rpow hpden_nonneg hp_nonneg]
      rw [div_eq_mul_inv, hp_inv_pow]
      change (p - 1)⁻¹ ^ p * ((p - 1) ^ (p - 1) * p ^ (1 - p)) =
          (p - 1)⁻¹ * p ^ (1 - p)
      have hcancel :
          (p - 1)⁻¹ ^ (p - 1) * (p - 1) ^ (p - 1) = 1 := by
        rw [← Real.mul_rpow (inv_nonneg.mpr hpden_nonneg) hpden_nonneg]
        simp [hpden_pos.ne']
      have hsplit :
          (p - 1)⁻¹ ^ p =
            (p - 1)⁻¹ ^ (p - 1) * (p - 1)⁻¹ := by
        calc
          (p - 1)⁻¹ ^ p = (p - 1)⁻¹ ^ ((p - 1) + 1) := by
              congr 1
              ring
          _ = (p - 1)⁻¹ ^ (p - 1) * (p - 1)⁻¹ ^ (1 : ℝ) := by
              rw [Real.rpow_add (inv_pos.mpr hpden_pos)]
          _ = (p - 1)⁻¹ ^ (p - 1) * (p - 1)⁻¹ := by
              rw [Real.rpow_one]
      rw [hsplit]
      calc
        ((p - 1)⁻¹ ^ (p - 1) * (p - 1)⁻¹) *
            ((p - 1) ^ (p - 1) * p ^ (1 - p))
            = ((p - 1)⁻¹ ^ (p - 1) * (p - 1) ^ (p - 1)) *
                ((p - 1)⁻¹ * p ^ (1 - p)) := by ring
        _ = (p - 1)⁻¹ * p ^ (1 - p) := by
          rw [hcancel]
          ring
    rw [halpha, hpStar, q]
    simp [hp_ne_one]
    rw [show p⁻¹ ^ (p - 1) = p ^ (1 - p) by
      simpa [one_div] using hone_div_pow, hcoeff_piece]
    field_simp [hp_ne, hpden_pos.ne']
    ring
  have hend :
      (1 / p) ^ (p - 1) + coeffLeTwo p * ((p - 1) / p) ^ (p - 1)
        ≤ coeffLeTwo p := by
    rw [← hB]
    have htwo_sub_nonneg : 0 ≤ 2 - p := by linarith
    have hweights : (p - 1) + (2 - p) = 1 := by ring
    have hamgm :
        (p - 1) ^ (p - 1) * p ^ (2 - p) ≤ 1 := by
      have h := Real.geom_mean_le_arith_mean2_weighted
        hpden_nonneg htwo_sub_nonneg hpden_nonneg hp_nonneg hweights
      calc
        (p - 1) ^ (p - 1) * p ^ (2 - p)
            ≤ (p - 1) * (p - 1) + (2 - p) * p := h
        _ = 1 := by ring
    have hdenpow_pos : 0 < (p - 1) ^ (p - 1) :=
      Real.rpow_pos_of_pos hpden_pos _
    have hp_pow_le_inv :
        p ^ (2 - p) ≤ ((p - 1) ^ (p - 1))⁻¹ := by
      rw [show ((p - 1) ^ (p - 1))⁻¹ = 1 / ((p - 1) ^ (p - 1)) by
        rw [one_div]]
      rw [le_div_iff₀ hdenpow_pos]
      simpa [mul_assoc, mul_left_comm, mul_comm] using hamgm
    have hinv_eq :
        ((p - 1) ^ (p - 1))⁻¹ = (p - 1) ^ (1 - p) := by
      rw [← Real.rpow_neg hpden_nonneg]
      congr 1
      ring
    have hp_pow :
        p ^ (2 - p) ≤ (p - 1) ^ (1 - p) := by
      rwa [hinv_eq] at hp_pow_le_inv
    have hleft_eq :
        alpha p * pStar p / p = p ^ (2 - p) / (p - 1) := by
      have hpStar : pStar p = q p :=
        pStar_eq_q_of_one_lt_of_lt_two p hp1 hp2
      rw [alpha_eq_leTwo p hp1 hp2, hpStar, q]
      simp [hp_ne_one]
      have hpow_shift : p * p ^ (1 - p) = p ^ (2 - p) := by
        calc
          p * p ^ (1 - p) = p ^ (1 : ℝ) * p ^ (1 - p) := by
              rw [Real.rpow_one]
          _ = p ^ ((1 : ℝ) + (1 - p)) := by
              rw [Real.rpow_add hp_pos]
          _ = p ^ (2 - p) := by ring
      rw [← hpow_shift]
      field_simp [hp_ne, hpden_pos.ne']
    have hcoeff_eq :
        coeffLeTwo p = (p - 1) ^ (-p) := by
      rw [coeffLeTwo]
      exact (Real.rpow_neg_eq_inv_rpow (p - 1) p).symm
    have hdiv_eq :
        (p - 1) ^ (1 - p) / (p - 1) = (p - 1) ^ (-p) := by
      rw [div_eq_mul_inv]
      rw [show (p - 1)⁻¹ = (p - 1) ^ (-1 : ℝ) by
        rw [Real.rpow_neg_one]]
      rw [← Real.rpow_add hpden_pos]
      congr 1
      ring
    calc
      alpha p * pStar p / p = p ^ (2 - p) / (p - 1) := hleft_eq
      _ ≤ (p - 1) ^ (1 - p) / (p - 1) :=
          div_le_div_of_nonneg_right hp_pow hpden_pos.le
      _ = (p - 1) ^ (-p) := hdiv_eq
      _ = coeffLeTwo p := hcoeff_eq.symm
  have hmul_second :
      coeffLeTwo p *
        (lam * ((p - 1) / p) ^ (p - 1) + mu)
        ≤ coeffLeTwo p * t ^ (p - 1) := by
    exact mul_le_mul_of_nonneg_left hsecond
      (coeffLeTwo_nonneg_of_one_lt_of_lt_two p hp1 hp2)
  calc
    alpha p * pStar p / p
        = lam * (alpha p * pStar p / p) + mu * (alpha p * pStar p / p) := by
            rw [← add_mul, hsum, one_mul]
    _ ≤ lam *
          ((1 / p) ^ (p - 1) + coeffLeTwo p * ((p - 1) / p) ^ (p - 1)) +
        mu * coeffLeTwo p := by
          rw [hB]
          exact add_le_add le_rfl (mul_le_mul_of_nonneg_left hend hmu_nonneg)
    _ = (lam * (1 / p) ^ (p - 1) + mu * (0 : ℝ) ^ (p - 1)) +
        coeffLeTwo p *
          (lam * ((p - 1) / p) ^ (p - 1) + mu) := by
          rw [hzero]
          ring
    _ ≤ (1 - t) ^ (p - 1) + coeffLeTwo p * t ^ (p - 1) := by
          exact add_le_add hfirst hmul_second

lemma burkholder_scalar_gap_antitone_leTwo
    (p : ℝ) (hp1 : 1 < p) (hp2 : p < 2) :
    AntitoneOn
      (fun t : ℝ =>
        (1 - t) ^ p - coeffLeTwo p * t ^ p -
          alpha p * (1 - pStar p * t))
      (Set.Icc ((p - 1) / p) 1) := by
  let F : ℝ → ℝ := fun t =>
    (1 - t) ^ p - coeffLeTwo p * t ^ p -
      alpha p * (1 - pStar p * t)
  let F' : ℝ → ℝ := fun t =>
    p * (alpha p * pStar p / p -
      ((1 - t) ^ (p - 1) + coeffLeTwo p * t ^ (p - 1)))
  have hp_pos : 0 < p := by linarith
  have hp_nonneg : 0 ≤ p := le_of_lt hp_pos
  have hpden_pos : 0 < p - 1 := by linarith
  have hp_ne : p ≠ 0 := by linarith
  have hcont : ContinuousOn F (Set.Icc ((p - 1) / p) 1) := by
    dsimp [F]
    apply ContinuousOn.sub
    · apply ContinuousOn.sub
      · exact ((continuousOn_const.sub continuousOn_id).rpow_const
          (by intro t ht; exact Or.inr (by linarith : 0 ≤ p)))
      · exact continuousOn_const.mul
          (continuousOn_id.rpow_const
            (by intro t ht; exact Or.inr (by linarith : 0 ≤ p)))
    · exact continuousOn_const.mul
        (continuousOn_const.sub (continuousOn_const.mul continuousOn_id))
  have hderiv :
      ∀ t ∈ interior (Set.Icc ((p - 1) / p) 1),
        HasDerivWithinAt F (F' t) (interior (Set.Icc ((p - 1) / p) 1)) t := by
    intro t ht
    have htI : t ∈ Set.Ioo ((p - 1) / p) 1 := by
      simpa [interior_Icc] using ht
    have ht_pos : 0 < t := by
      have hbase : 0 < (p - 1) / p := div_pos hpden_pos hp_pos
      exact lt_trans hbase htI.1
    have h1t_pos : 0 < 1 - t := sub_pos.mpr htI.2
    have hone_sub :
        HasDerivAt (fun s : ℝ => 1 - s) (-1) t := by
      simpa using (hasDerivAt_const (c := (1 : ℝ)) t).sub (hasDerivAt_id t)
    have hpow1 :
        HasDerivAt (fun s : ℝ => (1 - s) ^ p)
          (p * (1 - t) ^ (p - 1) * (-1)) t := by
      have hbase :
          HasDerivAt (fun u : ℝ => u ^ p)
            (p * (1 - t) ^ (p - 1)) (1 - t) :=
        Real.hasDerivAt_rpow_const (Or.inl (ne_of_gt h1t_pos))
      exact hbase.comp t hone_sub
    have hpow2 :
        HasDerivAt (fun s : ℝ => s ^ p)
          (p * t ^ (p - 1)) t :=
      Real.hasDerivAt_rpow_const (Or.inl (ne_of_gt ht_pos))
    have hlin :
        HasDerivAt (fun s : ℝ => alpha p * (1 - pStar p * s))
          (alpha p * (-pStar p)) t := by
      have hbase :
          HasDerivAt (fun s : ℝ => 1 - pStar p * s) (-pStar p) t := by
        simpa using (hasDerivAt_const (c := (1 : ℝ)) t).sub
          ((hasDerivAt_id t).const_mul (pStar p))
      exact hbase.const_mul (alpha p)
    have hmain :
        HasDerivAt F
          ((p * (1 - t) ^ (p - 1) * (-1)) -
            coeffLeTwo p * (p * t ^ (p - 1)) -
            alpha p * (-pStar p)) t := by
      dsimp [F]
      exact (hpow1.sub (hpow2.const_mul (coeffLeTwo p))).sub hlin
    refine (hmain.congr_deriv ?_).hasDerivWithinAt
    dsimp [F']
    field_simp [hp_ne]
    ring
  have hderiv_nonpos :
      ∀ t ∈ interior (Set.Icc ((p - 1) / p) 1), F' t ≤ 0 := by
    intro t ht
    have htI : t ∈ Set.Ioo ((p - 1) / p) 1 := by
      simpa [interior_Icc] using ht
    have hsum := scalar_deriv_sum_lower_leTwo p t hp1 hp2
      (le_of_lt htI.1) (le_of_lt htI.2)
    dsimp [F']
    have hbracket :
        alpha p * pStar p / p -
          ((1 - t) ^ (p - 1) + coeffLeTwo p * t ^ (p - 1)) ≤ 0 := by
      linarith
    exact mul_nonpos_of_nonneg_of_nonpos hp_nonneg hbracket
  simpa [F] using
    antitoneOn_of_hasDerivWithinAt_nonpos
      (convex_Icc ((p - 1) / p) 1) hcont hderiv hderiv_nonpos

lemma burkholder_scalar_A1_leTwo
    (p t : ℝ) (hp1 : 1 < p) (hp2 : p < 2)
    (ht_lower : (p - 1) / p ≤ t) (ht_upper : t ≤ 1) :
    (1 - t) ^ p - coeffLeTwo p * t ^ p ≤
      alpha p * (1 - pStar p * t) := by
  let H : ℝ → ℝ := fun s =>
    (1 - s) ^ p - coeffLeTwo p * s ^ p -
      alpha p * (1 - pStar p * s)
  have hanti : AntitoneOn H (Set.Icc ((p - 1) / p) 1) := by
    simpa [H] using burkholder_scalar_gap_antitone_leTwo p hp1 hp2
  have ht_mem : t ∈ Set.Icc ((p - 1) / p) 1 := ⟨ht_lower, ht_upper⟩
  have hb_mem : ((p - 1) / p) ∈ Set.Icc ((p - 1) / p) 1 := by
    constructor
    · rfl
    · have hp_pos : 0 < p := by linarith
      rw [div_le_iff₀ hp_pos]
      linarith
  have hle : H t ≤ H ((p - 1) / p) :=
    hanti hb_mem ht_mem ht_lower
  have hb : H ((p - 1) / p) = 0 := by
    have hp_pos : 0 < p := by linarith
    have hp_nonneg : 0 ≤ p := le_of_lt hp_pos
    have hpden_pos : 0 < p - 1 := by linarith
    have hpden_nonneg : 0 ≤ p - 1 := le_of_lt hpden_pos
    have hp_ne : p ≠ 0 := by linarith
    have hp_ne_one : p ≠ 1 := by linarith
    have h1 :
        1 - (p - 1) / p = 1 / p := by
      field_simp [hp_ne]
      ring
    have hps :
        pStar p * ((p - 1) / p) = 1 := by
      rw [pStar_eq_q_of_one_lt_of_lt_two p hp1 hp2]
      simp [q, hp_ne_one]
      field_simp [hp_ne, hpden_pos.ne']
    have hfirst : (1 / p) ^ p = (p ^ p)⁻¹ := by
      rw [one_div, Real.inv_rpow hp_nonneg]
    have hsecond :
        coeffLeTwo p * ((p - 1) / p) ^ p = (p ^ p)⁻¹ := by
      rw [coeffLeTwo, Real.div_rpow hpden_nonneg hp_nonneg]
      have hcancel : (p - 1)⁻¹ ^ p * (p - 1) ^ p = 1 := by
        rw [← Real.mul_rpow (inv_nonneg.mpr hpden_nonneg) hpden_nonneg]
        simp [hpden_pos.ne']
      calc
        (p - 1)⁻¹ ^ p * ((p - 1) ^ p / p ^ p)
            = ((p - 1)⁻¹ ^ p * (p - 1) ^ p) * (p ^ p)⁻¹ := by
                ring
        _ = (p ^ p)⁻¹ := by rw [hcancel]; ring
    dsimp [H]
    rw [h1, hfirst, hsecond, hps]
    ring
  have hH_nonpos : H t ≤ 0 := by
    rwa [hb] at hle
  dsimp [H] at hH_nonpos
  linarith

lemma vLeTwo_le_uA1_on_closureA1_leTwo
    (p : ℝ) (hp1 : 1 < p) (hp2 : p < 2) {x y : ℝ}
    (hA1 : closureA1 p x y) :
    vLeTwo p x y ≤ uA1 p x y := by
  rcases hA1 with ⟨hx_nonneg, hlow, hyup⟩
  rcases hx_nonneg.eq_or_lt with rfl | hxpos
  · have hy0 : y = 0 := by linarith
    subst y
    simp [vLeTwo, uA1, Real.zero_rpow (by linarith : p ≠ 0)]
  · have hx_nonneg' : 0 ≤ x := le_of_lt hxpos
    have hp_pos : 0 < p := by linarith
    have hp_ne : p ≠ 0 := by linarith
    have hpden_pos : 0 < p - 1 := by linarith
    have hpStar : pStar p = q p := pStar_eq_q_of_one_lt_of_lt_two p hp1 hp2
    have hp_ne_one : p ≠ 1 := by linarith
    have ha_eq : a p = (2 - p) / p := a_eq_leTwo p hp1 hp2
    let t : ℝ := (x - y) / (2 * x)
    have ht_upper : t ≤ 1 := by
      dsimp [t]
      have hxy : x - y ≤ 2 * x := by linarith
      have hden_pos : 0 < 2 * x := mul_pos (by norm_num) hxpos
      have h := div_le_div_of_nonneg_right hxy hden_pos.le
      calc
        (x - y) / (2 * x) ≤ (2 * x) / (2 * x) := h
        _ = 1 := by field_simp [hxpos.ne']
    have ht_lower : (p - 1) / p ≤ t := by
      dsimp [t]
      rw [ha_eq] at hyup
      have hxy : 2 * x * ((p - 1) / p) ≤ x - y := by
        have htmp : x - (2 - p) / p * x = 2 * x * ((p - 1) / p) := by
          field_simp [hp_ne]
          ring
        linarith
      have hden_pos : 0 < 2 * x := mul_pos (by norm_num) hxpos
      rw [le_div_iff₀ hden_pos]
      simpa [mul_assoc, mul_comm, mul_left_comm] using hxy
    have ht_nonneg : 0 ≤ t := by
      have hbase : 0 ≤ (p - 1) / p := div_nonneg (le_of_lt hpden_pos) hp_pos.le
      exact hbase.trans ht_lower
    have h1mt_nonneg : 0 ≤ 1 - t := by linarith
    have hsum_norm : (x + y) / 2 = x * (1 - t) := by
      dsimp [t]
      field_simp [hxpos.ne']
      ring
    have hdiff_norm : (x - y) / 2 = x * t := by
      dsimp [t]
      field_simp [hxpos.ne']
    have hlinear_norm :
        x - pStar p * (x - y) / 2 = x * (1 - pStar p * t) := by
      dsimp [t]
      field_simp [hxpos.ne']
    have hv_norm :
        vLeTwo p x y =
          x ^ p * ((1 - t) ^ p - coeffLeTwo p * t ^ p) := by
      have hsum_nonneg : 0 ≤ (x + y) / 2 := by
        rw [hsum_norm]
        exact mul_nonneg hx_nonneg' h1mt_nonneg
      have hdiff_nonneg : 0 ≤ (x - y) / 2 := by
        rw [hdiff_norm]
        exact mul_nonneg hx_nonneg' ht_nonneg
      calc
        vLeTwo p x y =
            ((x + y) / 2) ^ p - coeffLeTwo p * ((x - y) / 2) ^ p := by
              simp [vLeTwo, abs_of_nonneg hsum_nonneg, abs_of_nonneg hdiff_nonneg]
        _ = (x * (1 - t)) ^ p - coeffLeTwo p * (x * t) ^ p := by
              rw [hsum_norm, hdiff_norm]
        _ = x ^ p * (1 - t) ^ p - coeffLeTwo p * (x ^ p * t ^ p) := by
              rw [Real.mul_rpow hx_nonneg' h1mt_nonneg,
                Real.mul_rpow hx_nonneg' ht_nonneg]
        _ = x ^ p * ((1 - t) ^ p - coeffLeTwo p * t ^ p) := by ring
    have hu_norm :
        uA1 p x y = x ^ p * (alpha p * (1 - pStar p * t)) := by
      have hxpow : x ^ (p - 1) * x = x ^ p := by
        have h := Real.rpow_one_add' hx_nonneg'
          (by linarith : (1 : ℝ) + (p - 1) ≠ 0)
        have h' : x ^ p = x * x ^ (p - 1) := by
          simpa [show (1 : ℝ) + (p - 1) = p by ring] using h
        rw [h']
        ring
      calc
        uA1 p x y =
            alpha p * x ^ (p - 1) * (x - pStar p * (x - y) / 2) := by
              simp [uA1, hxpos]
        _ = alpha p * x ^ (p - 1) * (x * (1 - pStar p * t)) := by
              rw [hlinear_norm]
        _ = x ^ p * (alpha p * (1 - pStar p * t)) := by
              rw [← hxpow]
              ring
    have hscalar := burkholder_scalar_A1_leTwo p t hp1 hp2 ht_lower ht_upper
    have hxpow_nonneg : 0 ≤ x ^ p := Real.rpow_nonneg hx_nonneg' p
    calc
      vLeTwo p x y =
          x ^ p * ((1 - t) ^ p - coeffLeTwo p * t ^ p) := hv_norm
      _ ≤ x ^ p * (alpha p * (1 - pStar p * t)) :=
          mul_le_mul_of_nonneg_left hscalar hxpow_nonneg
      _ = uA1 p x y := hu_norm.symm

lemma vLeTwo_le_uCandidate_leTwo
    (p : ℝ) (hp1 : 1 < p) (hp2 : p < 2) (x y : ℝ) :
    vLeTwo p x y ≤ uCandidate p x y :=
  vLeTwo_le_uCandidate_of_A1_leTwo p hp1 hp2
    (fun {x y} hA1 => vLeTwo_le_uA1_on_closureA1_leTwo p hp1 hp2 hA1) x y

lemma uCandidate_neg_neg_of_y_neg_leTwo
    (p : ℝ) {x y : ℝ} (hy_neg : y < 0) :
    uCandidate p x y = uCandidate p (-x) (-y) := by
  by_cases hx_left : x ≤ y
  · have hQ2 : QuarterPlane2 x y := ⟨by linarith, by linarith, hx_left⟩
    have hQ_ref : QuarterPlane (-x) (-y) :=
      ⟨by linarith, by linarith, by linarith⟩
    have hnotQ : ¬ QuarterPlane x y := by
      intro hq
      linarith [hq.1]
    simp [uCandidate, hnotQ, hQ2, hQ_ref]
  · have hyx : y < x := lt_of_not_ge hx_left
    by_cases hx_mid : x < -y
    · have hQ4 : QuarterPlane4 x y := ⟨hy_neg.le, hyx.le, hx_mid.le⟩
      have hQ3_ref : QuarterPlane3 (-x) (-y) :=
        ⟨by linarith, by linarith, by linarith⟩
      have hnotQ : ¬ QuarterPlane x y := by
        intro hq
        linarith [hq.2.2]
      have hnotQ2 : ¬ QuarterPlane2 x y := by
        intro hq
        linarith [hq.2.2]
      have hnotQ3 : ¬ QuarterPlane3 x y := by
        intro hq
        linarith [hq.1]
      have hnotQ_ref : ¬ QuarterPlane (-x) (-y) := by
        intro hq
        linarith [hq.2.1]
      have hnotQ2_ref : ¬ QuarterPlane2 (-x) (-y) := by
        intro hq
        have hle : -y ≤ x := by simpa using hq.2.1
        linarith
      simp [uCandidate, hnotQ, hnotQ2, hnotQ3, hQ4, hnotQ_ref, hnotQ2_ref, hQ3_ref]
    · have hx_right : -y ≤ x := le_of_not_gt hx_mid
      have hQ : QuarterPlane x y := ⟨by linarith, by linarith, by linarith⟩
      have hQ2_ref : QuarterPlane2 (-x) (-y) :=
        ⟨by linarith, by linarith, by linarith⟩
      have hnotQ_ref : ¬ QuarterPlane (-x) (-y) := by
        intro hq
        linarith [hq.1]
      simp [uCandidate, hQ, hnotQ_ref, hQ2_ref]

lemma DxuCandidate_neg_neg_of_y_neg_leTwo
    (p : ℝ) {x y : ℝ} (hy_neg : y < 0) :
    DxuCandidate p x y = -DxuCandidate p (-x) (-y) := by
  by_cases hx_left : x ≤ y
  · have hQ2 : QuarterPlane2 x y := ⟨by linarith, by linarith, hx_left⟩
    have hQ_ref : QuarterPlane (-x) (-y) :=
      ⟨by linarith, by linarith, by linarith⟩
    have hnotQ : ¬ QuarterPlane x y := by
      intro hq
      linarith [hq.1]
    simp [DxuCandidate, hnotQ, hQ2, hQ_ref]
  · have hyx : y < x := lt_of_not_ge hx_left
    by_cases hx_mid : x < -y
    · have hQ4 : QuarterPlane4 x y := ⟨hy_neg.le, hyx.le, hx_mid.le⟩
      have hQ3_ref : QuarterPlane3 (-x) (-y) :=
        ⟨by linarith, by linarith, by linarith⟩
      have hnotQ : ¬ QuarterPlane x y := by
        intro hq
        linarith [hq.2.2]
      have hnotQ2 : ¬ QuarterPlane2 x y := by
        intro hq
        linarith [hq.2.2]
      have hnotQ3 : ¬ QuarterPlane3 x y := by
        intro hq
        linarith [hq.1]
      have hnotQ_ref : ¬ QuarterPlane (-x) (-y) := by
        intro hq
        linarith [hq.2.1]
      have hnotQ2_ref : ¬ QuarterPlane2 (-x) (-y) := by
        intro hq
        have hle : -y ≤ x := by simpa using hq.2.1
        linarith
      simp [DxuCandidate, hnotQ, hnotQ2, hnotQ3, hQ4, hnotQ_ref, hnotQ2_ref, hQ3_ref]
    · have hx_right : -y ≤ x := le_of_not_gt hx_mid
      have hQ : QuarterPlane x y := ⟨by linarith, by linarith, by linarith⟩
      have hQ2_ref : QuarterPlane2 (-x) (-y) :=
        ⟨by linarith, by linarith, by linarith⟩
      have hnotQ_ref : ¬ QuarterPlane (-x) (-y) := by
        intro hq
        linarith [hq.1]
      simp [DxuCandidate, hQ, hnotQ_ref, hQ2_ref]

lemma uCandidate_tangent_x_increment_of_y_neg_leTwo_of_pos
    (p : ℝ)
    (hpos_tangent :
      ∀ {x y h : ℝ}, 0 < y →
        uCandidate p (x + h) y ≤
          uCandidate p x y + DxuCandidate p x y * h)
    {x y h : ℝ} (hy_neg : y < 0) :
    uCandidate p (x + h) y ≤
      uCandidate p x y + DxuCandidate p x y * h := by
  have hpos : 0 < -y := by linarith
  have hmain := hpos_tangent (x := -x) (y := -y) (h := -h) hpos
  have hstart := uCandidate_neg_neg_of_y_neg_leTwo (p := p) (x := x) (y := y) hy_neg
  have hend := uCandidate_neg_neg_of_y_neg_leTwo (p := p) (x := x + h) (y := y) hy_neg
  have hdx := DxuCandidate_neg_neg_of_y_neg_leTwo (p := p) (x := x) (y := y) hy_neg
  calc
    uCandidate p (x + h) y = uCandidate p (-(x + h)) (-y) := hend
    _ = uCandidate p ((-x) + (-h)) (-y) := by ring
    _ ≤ uCandidate p (-x) (-y) + DxuCandidate p (-x) (-y) * (-h) := hmain
    _ = uCandidate p x y + DxuCandidate p x y * h := by
      rw [← hstart, hdx]
      ring

lemma concaveOn_Icc_tangent_inequality_of_hasDerivAt_leTwo
    {f : ℝ → ℝ} {a b x z f' : ℝ}
    (hf : ConcaveOn ℝ (Set.Icc a b) f)
    (hx : x ∈ Set.Icc a b) (hz : z ∈ Set.Icc a b)
    (hderiv : HasDerivAt f f' x) :
    f z ≤ f x + f' * (z - x) := by
  rcases lt_trichotomy z x with hlt | heq | hgt
  · have hslope : f' ≤ slope f z x :=
      hf.le_slope_of_hasDerivAt hz hx hlt hderiv
    have hslope' : f' ≤ (f x - f z) / (x - z) := by
      simpa [slope_def_field] using hslope
    have hden_pos : 0 < x - z := by linarith
    have hmul := mul_le_mul_of_nonneg_right hslope' hden_pos.le
    field_simp [hden_pos.ne'] at hmul
    linarith
  · subst z
    simp
  · have hslope : slope f x z ≤ f' :=
      hf.slope_le_of_hasDerivAt hx hz hgt hderiv
    have hslope' : (f z - f x) / (z - x) ≤ f' := by
      simpa [slope_def_field] using hslope
    have hden_pos : 0 < z - x := by linarith
    have hmul := mul_le_mul_of_nonneg_right hslope' hden_pos.le
    field_simp [hden_pos.ne'] at hmul
    linarith

lemma tangent_inequality_on_Icc_of_hasDerivWithinAt2_nonpos_leTwo
    {f f₁ f₂ : ℝ → ℝ} {a b x z f' : ℝ}
    (hcont : ContinuousOn f (Set.Icc a b))
    (hf₁ : ∀ t ∈ interior (Set.Icc a b),
      HasDerivWithinAt f (f₁ t) (interior (Set.Icc a b)) t)
    (hf₂ : ∀ t ∈ interior (Set.Icc a b),
      HasDerivWithinAt f₁ (f₂ t) (interior (Set.Icc a b)) t)
    (hf₂_nonpos : ∀ t ∈ interior (Set.Icc a b), f₂ t ≤ 0)
    (hx : x ∈ Set.Icc a b) (hz : z ∈ Set.Icc a b)
    (hderiv : HasDerivAt f f' x) :
    f z ≤ f x + f' * (z - x) := by
  exact concaveOn_Icc_tangent_inequality_of_hasDerivAt_leTwo
    (concaveOn_of_hasDerivWithinAt2_nonpos
      (convex_Icc a b) hcont hf₁ hf₂ hf₂_nonpos)
    hx hz hderiv

lemma hasDerivAt_uA1_x_of_pos_leTwo
    (p : ℝ) (hp1 : 1 < p) (hp2 : p < 2) (x y : ℝ) (hx : 0 < x) :
    HasDerivAt (fun t => uA1 p t y) (DxuA1 p x y) x := by
  have hpStar : pStar p = q p := pStar_eq_q_of_one_lt_of_lt_two p hp1 hp2
  have hp_ne_one : p ≠ 1 := by linarith
  have hpden_ne : p - 1 ≠ 0 := by linarith
  let g : ℝ → ℝ := fun t =>
    alpha p * ((1 - pStar p / 2) * t ^ p + (pStar p * y / 2) * t ^ (p - 1))
  have hEq : (fun t => uA1 p t y) =ᶠ[nhds x] g := by
    filter_upwards [Ioi_mem_nhds hx] with t ht
    have ht0 : 0 < t := by simpa [Set.mem_Ioi] using ht
    have hpow : t ^ p = t ^ (p - 1) * t := by
      calc
        t ^ p = t ^ ((p - 1) + (1 : ℝ)) := by ring_nf
        _ = t ^ (p - 1) * t ^ (1 : ℝ) := by rw [Real.rpow_add ht0]
        _ = t ^ (p - 1) * t := by rw [Real.rpow_one]
    simp [uA1, g, ht0]
    rw [hpow]
    ring
  have hxne : x ≠ 0 := by linarith
  have hxne1 : x ≠ 0 ∨ 1 ≤ p := Or.inl hxne
  have hxne2 : x ≠ 0 ∨ 1 ≤ p - 1 := Or.inl hxne
  have hd1 :
      HasDerivAt (fun t : ℝ => t ^ p) (p * x ^ (p - 1)) x := by
    simpa using
      (Real.hasDerivAt_rpow_const hxne1 :
        HasDerivAt (fun t : ℝ => t ^ p) (p * x ^ (p - 1)) x)
  have hd2 :
      HasDerivAt (fun t : ℝ => t ^ (p - 1)) ((p - 1) * x ^ (p - 2)) x := by
    have h := (Real.hasDerivAt_rpow_const hxne2 :
      HasDerivAt (fun t : ℝ => t ^ (p - 1))
        ((p - 1) * x ^ ((p - 1) - 1)) x)
    simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc,
      show p + (-1 + -1) = p + -2 by ring] using h
  have hd :
      HasDerivAt g
        (alpha p *
          ((1 - pStar p / 2) * (p * x ^ (p - 1)) +
            (pStar p * y / 2) * ((p - 1) * x ^ (p - 2)))) x := by
    dsimp [g]
    have hsum :=
      ((hd1.const_mul (1 - pStar p / 2)).add
        (hd2.const_mul (pStar p * y / 2))).const_mul (alpha p)
    simpa [mul_add, mul_assoc, mul_left_comm, mul_comm] using hsum
  have hpow : x ^ (p - 1) = x ^ (p - 2) * x := by
    calc
      x ^ (p - 1) = x ^ ((p - 2) + (1 : ℝ)) := by ring_nf
      _ = x ^ (p - 2) * x ^ (1 : ℝ) := by rw [Real.rpow_add hx]
      _ = x ^ (p - 2) * x := by rw [Real.rpow_one]
  have hg :
      HasDerivAt g
        (alpha p * (p / 2) * x ^ (p - 2) *
          (((p - 2) / (p - 1)) * x + y)) x := by
    refine hd.congr_deriv ?_
    rw [hpow, hpStar]
    simp [q, hp_ne_one]
    field_simp [hpden_ne]
    ring
  refine (hg.congr_of_eventuallyEq hEq).congr_deriv ?_
  simp [DxuA1, hx]

lemma deriv_DxuA1Fun_x_nonpos_leTwo
    (p : ℝ) (hp1 : 1 < p) (hp2 : p < 2) (x y : ℝ)
    (hx : 0 < x) (hxy : 0 ≤ x + y) :
    deriv (fun t => DxuA1Fun p (t, y)) x ≤ 0 := by
  have hpden_ne : p - 1 ≠ 0 := by linarith
  have hEq :
      (fun t => DxuA1Fun p (t, y)) =ᶠ[nhds x]
        fun t => alpha p * (p / 2) * t ^ (p - 2) *
          (((p - 2) / (p - 1)) * t + y) := by
    filter_upwards [Ioi_mem_nhds hx] with t ht
    have htpos : 0 < t := by simpa using ht
    simp [DxuA1Fun, DxuA1, htpos]
  have hxne : x ≠ 0 := by linarith
  have hxne_pow : x ≠ 0 ∨ 1 ≤ p - 2 := Or.inl hxne
  have hpow :
      HasDerivAt (fun t : ℝ => t ^ (p - 2)) ((p - 2) * x ^ (p - 3)) x := by
    have h := (Real.hasDerivAt_rpow_const hxne_pow :
      HasDerivAt (fun t : ℝ => t ^ (p - 2))
        ((p - 2) * x ^ ((p - 2) - 1)) x)
    simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc,
      show p + (-1 + -2) = p + -3 by ring] using h
  have hlin :
      HasDerivAt (fun t : ℝ => ((p - 2) / (p - 1)) * t + y)
        ((p - 2) / (p - 1)) x := by
    simpa using
      ((hasDerivAt_id x).const_mul ((p - 2) / (p - 1))).const_add y
  have hd :
      HasDerivAt
        (fun t : ℝ => alpha p * (p / 2) * t ^ (p - 2) *
          (((p - 2) / (p - 1)) * t + y))
        (alpha p * (p / 2) *
          (((p - 2) * x ^ (p - 3)) *
              (((p - 2) / (p - 1)) * x + y) +
            x ^ (p - 2) * ((p - 2) / (p - 1)))) x := by
    have hmul := hpow.mul hlin
    simpa [mul_add, mul_assoc, mul_left_comm, mul_comm] using
      hmul.const_mul (alpha p * (p / 2))
  have hshift : x ^ (p - 2) = x ^ (p - 3) * x := by
    calc
      x ^ (p - 2) = x ^ ((p - 3) + (1 : ℝ)) := by ring_nf
      _ = x ^ (p - 3) * x ^ (1 : ℝ) := by rw [Real.rpow_add hx]
      _ = x ^ (p - 3) * x := by rw [Real.rpow_one]
  have hderiv :
      deriv
        (fun t : ℝ => alpha p * (p / 2) * t ^ (p - 2) *
          (((p - 2) / (p - 1)) * t + y)) x
        = alpha p * (p / 2) * (p - 2) * x ^ (p - 3) * (x + y) := by
    rw [hd.deriv]
    rw [hshift]
    field_simp [hpden_ne]
    ring
  rw [hEq.deriv_eq, hderiv]
  have ha : 0 ≤ alpha p := alpha_nonneg_of_one_lt_of_lt_two p hp1 hp2
  have hp_nonneg : 0 ≤ p / 2 := by linarith
  have hp2_nonpos : p - 2 ≤ 0 := by linarith
  have hpow_nonneg : 0 ≤ x ^ (p - 3) := Real.rpow_nonneg hx.le _
  have hmain :
      (alpha p * (p / 2) * x ^ (p - 3)) * ((p - 2) * (x + y)) ≤ 0 := by
    exact mul_nonpos_of_nonneg_of_nonpos
      (mul_nonneg (mul_nonneg ha hp_nonneg) hpow_nonneg)
      (mul_nonpos_of_nonpos_of_nonneg hp2_nonpos hxy)
  rw [show alpha p * (p / 2) * (p - 2) * x ^ (p - 3) * (x + y) =
      (alpha p * (p / 2) * x ^ (p - 3)) * ((p - 2) * (x + y)) by ring]
  exact hmain

lemma differentiableAt_DxuA1Fun_x_of_pos_leTwo
    (p x y : ℝ) (hx : 0 < x) :
    DifferentiableAt ℝ (fun t => DxuA1Fun p (t, y)) x := by
  have hEq :
      (fun t => DxuA1Fun p (t, y)) =ᶠ[nhds x]
        fun t => alpha p * (p / 2) * t ^ (p - 2) *
          (((p - 2) / (p - 1)) * t + y) := by
    filter_upwards [Ioi_mem_nhds hx] with t ht
    have htpos : 0 < t := by simpa using ht
    simp [DxuA1Fun, DxuA1, htpos]
  have hpow :
      DifferentiableAt ℝ (fun t : ℝ => t ^ (p - 2)) x := by
    exact (Real.hasDerivAt_rpow_const (Or.inl (ne_of_gt hx))).differentiableAt
  have hlin :
      DifferentiableAt ℝ (fun t : ℝ => ((p - 2) / (p - 1)) * t + y) x := by
    exact ((differentiableAt_id.const_mul ((p - 2) / (p - 1))).add
      (differentiableAt_const y))
  have hformula :
      DifferentiableAt ℝ
        (fun t : ℝ => alpha p * (p / 2) * t ^ (p - 2) *
          (((p - 2) / (p - 1)) * t + y)) x := by
    exact ((hpow.const_mul (alpha p * (p / 2))).mul hlin)
  exact hformula.congr_of_eventuallyEq hEq

lemma uA1_tangent_x_on_Icc_leTwo
    (p : ℝ) (hp1 : 1 < p) (hp2 : p < 2) {lo hi x z y : ℝ}
    (hIcc_pos : ∀ t ∈ Set.Icc lo hi, 0 < t)
    (hIcc_sum : ∀ t ∈ interior (Set.Icc lo hi), 0 ≤ t + y)
    (hx : x ∈ Set.Icc lo hi) (hz : z ∈ Set.Icc lo hi) :
    uA1 p z y ≤ uA1 p x y + DxuA1 p x y * (z - x) := by
  apply tangent_inequality_on_Icc_of_hasDerivWithinAt2_nonpos_leTwo
      (f := fun t => uA1 p t y)
      (f₁ := fun t => DxuA1Fun p (t, y))
      (f₂ := fun t => deriv (fun s => DxuA1Fun p (s, y)) t)
      (f' := DxuA1 p x y)
  · have hEq :
        ∀ t ∈ Set.Icc lo hi,
          uA1 p t y =
            alpha p * ((1 - pStar p / 2) * t ^ p +
              (pStar p * y / 2) * t ^ (p - 1)) := by
      intro t ht
      have htpos := hIcc_pos t ht
      have hpow : t ^ p = t ^ (p - 1) * t := by
        calc
          t ^ p = t ^ ((p - 1) + (1 : ℝ)) := by ring_nf
          _ = t ^ (p - 1) * t ^ (1 : ℝ) := by rw [Real.rpow_add htpos]
          _ = t ^ (p - 1) * t := by rw [Real.rpow_one]
      simp [uA1, htpos]
      rw [hpow]
      ring
    refine ContinuousOn.congr ?_ hEq
    apply continuousOn_const.mul
    apply ContinuousOn.add
    · exact continuousOn_const.mul
        (continuousOn_id.rpow_const (by intro t ht; exact Or.inl (ne_of_gt (hIcc_pos t ht))))
    · exact continuousOn_const.mul
        (continuousOn_id.rpow_const (by intro t ht; exact Or.inl (ne_of_gt (hIcc_pos t ht))))
  · intro t ht
    exact (hasDerivAt_uA1_x_of_pos_leTwo p hp1 hp2 t y (hIcc_pos t
      (interior_subset ht))).hasDerivWithinAt
  · intro t ht
    exact (differentiableAt_DxuA1Fun_x_of_pos_leTwo p t y (hIcc_pos t
      (interior_subset ht))).hasDerivAt.hasDerivWithinAt
  · intro t ht
    exact deriv_DxuA1Fun_x_nonpos_leTwo p hp1 hp2 t y
      (hIcc_pos t (interior_subset ht)) (hIcc_sum t ht)
  · exact hx
  · exact hz
  · exact hasDerivAt_uA1_x_of_pos_leTwo p hp1 hp2 x y (hIcc_pos x hx)

lemma vLeTwo_A2_second_bracket_nonpos_leTwo
    (p : ℝ) (hp1 : 1 < p) (hp2 : p < 2)
    (x y : ℝ) (hA2 : A2 p x y) :
    ((x + y) / 2) ^ (p - 2) -
      coeffLeTwo p * ((x - y) / 2) ^ (p - 2) ≤ 0 := by
  rcases hA2 with ⟨hx, hay, hyx⟩
  have hp_pos : 0 < p := by linarith
  have hpden_pos : 0 < p - 1 := by linarith
  have hpden_nonneg : 0 ≤ p - 1 := le_of_lt hpden_pos
  have hpden_le_one : p - 1 ≤ 1 := by linarith
  have ha_pos : 0 < a p := by
    rw [a_eq_leTwo p hp1 hp2]
    exact div_pos (by linarith) hp_pos
  have hy_pos : 0 < y := lt_trans (mul_pos ha_pos hx) hay
  have hsum_pos : 0 < (x + y) / 2 := by linarith
  have hdiff_pos : 0 < (x - y) / 2 := by linarith
  have ha_eq : a p = (2 - p) / p := a_eq_leTwo p hp1 hp2
  have hC_le :
      ((x - y) / 2) / (p - 1) ≤ (x + y) / 2 := by
    have hmain : (2 - p) * x ≤ p * y := by
      have hmul := mul_le_mul_of_nonneg_left (le_of_lt hay) hp_pos.le
      rw [ha_eq] at hmul
      field_simp [hp_pos.ne'] at hmul
      linarith
    rw [div_le_iff₀ hpden_pos]
    nlinarith
  have hC_pos : 0 < ((x - y) / 2) / (p - 1) :=
    div_pos hdiff_pos hpden_pos
  have hexp_neg : p - 2 < 0 := by linarith
  have hpow_le :
      ((x + y) / 2) ^ (p - 2) ≤
        (((x - y) / 2) / (p - 1)) ^ (p - 2) := by
    exact (Real.rpow_le_rpow_iff_of_neg hsum_pos hC_pos hexp_neg).2 hC_le
  have hsplit :
      (((x - y) / 2) / (p - 1)) ^ (p - 2) =
        ((x - y) / 2) ^ (p - 2) * (p - 1) ^ (2 - p) := by
    rw [div_eq_mul_inv]
    rw [Real.mul_rpow hdiff_pos.le (inv_nonneg.mpr hpden_nonneg)]
    rw [Real.inv_rpow hpden_nonneg]
    rw [← Real.rpow_neg hpden_nonneg]
    congr 2
    ring
  have hcoeff_pow :
      (p - 1) ^ (2 - p) ≤ coeffLeTwo p := by
    have hpow :
        (p - 1) ^ (2 - p) ≤ (p - 1) ^ (-p) := by
      exact Real.rpow_le_rpow_of_exponent_ge hpden_pos hpden_le_one (by linarith)
    have hcoeff : coeffLeTwo p = (p - 1) ^ (-p) := by
      rw [coeffLeTwo]
      exact (Real.rpow_neg_eq_inv_rpow (p - 1) p).symm
    simpa [hcoeff] using hpow
  have hright :
      (((x - y) / 2) / (p - 1)) ^ (p - 2) ≤
        coeffLeTwo p * ((x - y) / 2) ^ (p - 2) := by
    rw [hsplit]
    have hB_nonneg : 0 ≤ ((x - y) / 2) ^ (p - 2) :=
      Real.rpow_nonneg hdiff_pos.le _
    nlinarith [mul_le_mul_of_nonneg_left hcoeff_pow hB_nonneg]
  linarith

lemma deriv_DxvLeTwo_x_nonpos_leTwo
    (p : ℝ) (hp1 : 1 < p) (hp2 : p < 2) (x y : ℝ)
    (hA2 : A2 p x y) :
    deriv (fun t => DxvLeTwo p t y) x ≤ 0 := by
  rcases hA2 with ⟨hx, hay, hyx⟩
  have hp_pos : 0 < p := by linarith
  have ha_pos : 0 < a p := by
    rw [a_eq_leTwo p hp1 hp2]
    exact div_pos (by linarith) hp_pos
  have hy_pos : 0 < y := lt_trans (mul_pos ha_pos hx) hay
  have hsum : 0 < (x + y) / 2 := by linarith
  have hdiff : 0 < (x - y) / 2 := by linarith
  have hEq :
      (fun t => DxvLeTwo p t y) =ᶠ[nhds x]
        fun t =>
          ((t + y) / 2) ^ (p - 1) * (p / 2) -
            coeffLeTwo p * ((t - y) / 2) ^ (p - 1) * (p / 2) := by
    have hsum_nhds : {t : ℝ | 0 < (t + y) / 2} ∈ nhds x := by
      exact ((((continuous_id'.add continuous_const).div_const 2).continuousAt).preimage_mem_nhds
        (Ioi_mem_nhds hsum))
    have hdiff_nhds : {t : ℝ | 0 < (t - y) / 2} ∈ nhds x := by
      exact ((((continuous_id'.sub continuous_const).div_const 2).continuousAt).preimage_mem_nhds
        (Ioi_mem_nhds hdiff))
    filter_upwards [Ioi_mem_nhds hx, hsum_nhds, hdiff_nhds] with t ht htsum htdiff
    have htpos : 0 < t := by simpa using ht
    simp [DxvLeTwo, htpos, abs_of_pos htsum, abs_of_pos htdiff]
  have hbase_sum :
      HasDerivAt (fun t : ℝ => (t + y) / 2) (1 / 2) x := by
    simpa [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using
      (((hasDerivAt_id x).add_const y).const_mul (1 / 2 : ℝ))
  have hbase_diff :
      HasDerivAt (fun t : ℝ => (t - y) / 2) (1 / 2) x := by
    simpa [sub_eq_add_neg, div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using
      (((hasDerivAt_id x).add_const (-y)).const_mul (1 / 2 : ℝ))
  have hpow_sum :
      HasDerivAt (fun t : ℝ => ((t + y) / 2) ^ (p - 1))
        ((p - 1) * (((x + y) / 2) ^ (p - 2)) * (1 / 2)) x := by
    have hrpow :
        HasDerivAt (fun u : ℝ => u ^ (p - 1))
          ((p - 1) * (((x + y) / 2) ^ (p - 2))) ((x + y) / 2) := by
      simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm,
        show p + (-1 + -1) = p + -2 by ring] using
        (Real.hasDerivAt_rpow_const (Or.inl (ne_of_gt hsum)) :
          HasDerivAt (fun u : ℝ => u ^ (p - 1))
            ((p - 1) * ((x + y) / 2) ^ ((p - 1) - 1)) ((x + y) / 2))
    simpa [mul_assoc, mul_left_comm, mul_comm] using hrpow.comp x hbase_sum
  have hpow_diff :
      HasDerivAt (fun t : ℝ => ((t - y) / 2) ^ (p - 1))
        ((p - 1) * (((x - y) / 2) ^ (p - 2)) * (1 / 2)) x := by
    have hrpow :
        HasDerivAt (fun u : ℝ => u ^ (p - 1))
          ((p - 1) * (((x - y) / 2) ^ (p - 2))) ((x - y) / 2) := by
      simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm,
        show p + (-1 + -1) = p + -2 by ring] using
        (Real.hasDerivAt_rpow_const (Or.inl (ne_of_gt hdiff)) :
          HasDerivAt (fun u : ℝ => u ^ (p - 1))
            ((p - 1) * ((x - y) / 2) ^ ((p - 1) - 1)) ((x - y) / 2))
    simpa [mul_assoc, mul_left_comm, mul_comm] using hrpow.comp x hbase_diff
  have hd :
      HasDerivAt
        (fun t : ℝ =>
          ((t + y) / 2) ^ (p - 1) * (p / 2) -
            coeffLeTwo p * ((t - y) / 2) ^ (p - 1) * (p / 2))
        ((p * (p - 1) / 4) *
          (((x + y) / 2) ^ (p - 2) -
            coeffLeTwo p * ((x - y) / 2) ^ (p - 2))) x := by
    have htmp :
        HasDerivAt
          (fun t : ℝ =>
            ((t + y) / 2) ^ (p - 1) * (p / 2) -
              coeffLeTwo p * ((t - y) / 2) ^ (p - 1) * (p / 2))
          (((p - 1) * (((x + y) / 2) ^ (p - 2)) * (1 / 2)) * (p / 2) -
            coeffLeTwo p *
              (((p - 1) * (((x - y) / 2) ^ (p - 2)) * (1 / 2))) *
                (p / 2)) x := by
      exact (hpow_sum.mul_const (p / 2)).sub
        ((hpow_diff.const_mul (coeffLeTwo p)).mul_const (p / 2))
    refine htmp.congr_deriv ?_
    ring
  rw [hEq.deriv_eq, hd.deriv]
  have hcoef : 0 ≤ p * (p - 1) / 4 := by
    exact div_nonneg (mul_nonneg (by linarith) (by linarith)) (by norm_num)
  have hbr := vLeTwo_A2_second_bracket_nonpos_leTwo p hp1 hp2 x y ⟨hx, hay, hyx⟩
  exact mul_nonpos_of_nonneg_of_nonpos hcoef hbr

lemma hasDerivAt_vLeTwo_x_of_pos_leTwo (p : ℝ) (x y : ℝ)
    (hsum : 0 < (x + y) / 2) (hdiff : 0 < (x - y) / 2) :
    HasDerivAt (fun t => vLeTwo p t y) (DxvLeTwo p x y) x := by
  let g : ℝ → ℝ := fun t =>
    ((t + y) / 2) ^ p - coeffLeTwo p * (((t - y) / 2) ^ p)
  have hsum_nhds : {t : ℝ | 0 < (t + y) / 2} ∈ nhds x := by
    exact ((((continuous_id'.add continuous_const).div_const 2).continuousAt).preimage_mem_nhds
      (Ioi_mem_nhds hsum))
  have hdiff_nhds : {t : ℝ | 0 < (t - y) / 2} ∈ nhds x := by
    exact ((((continuous_id'.sub continuous_const).div_const 2).continuousAt).preimage_mem_nhds
      (Ioi_mem_nhds hdiff))
  have hEq : (fun t => vLeTwo p t y) =ᶠ[nhds x] g := by
    filter_upwards [hsum_nhds, hdiff_nhds] with t ht_sum ht_diff
    simp [vLeTwo, g, abs_of_pos ht_sum, abs_of_pos ht_diff]
  have hbase_sum :
      HasDerivAt (fun t : ℝ => (t + y) / 2) (1 / 2) x := by
    simpa [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using
      (((hasDerivAt_id x).add_const y).const_mul (1 / 2 : ℝ))
  have hbase_diff :
      HasDerivAt (fun t : ℝ => (t - y) / 2) (1 / 2) x := by
    simpa [sub_eq_add_neg, div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using
      (((hasDerivAt_id x).add_const (-y)).const_mul (1 / 2 : ℝ))
  have hpow_sum :
      HasDerivAt (fun t : ℝ => ((t + y) / 2) ^ p)
        (p * (((x + y) / 2) ^ (p - 1)) * (1 / 2)) x := by
    have hrpow :
        HasDerivAt (fun s : ℝ => s ^ p) (p * (((x + y) / 2) ^ (p - 1))) ((x + y) / 2) := by
      simpa using
        (Real.hasDerivAt_rpow_const (Or.inl (ne_of_gt hsum)) :
          HasDerivAt (fun s : ℝ => s ^ p) (p * ((x + y) / 2) ^ (p - 1)) ((x + y) / 2))
    simpa [mul_assoc, mul_left_comm, mul_comm] using hrpow.comp x hbase_sum
  have hpow_diff :
      HasDerivAt (fun t : ℝ => ((t - y) / 2) ^ p)
        (p * (((x - y) / 2) ^ (p - 1)) * (1 / 2)) x := by
    have hrpow :
        HasDerivAt (fun s : ℝ => s ^ p) (p * (((x - y) / 2) ^ (p - 1))) ((x - y) / 2) := by
      simpa using
        (Real.hasDerivAt_rpow_const (Or.inl (ne_of_gt hdiff)) :
          HasDerivAt (fun s : ℝ => s ^ p) (p * ((x - y) / 2) ^ (p - 1)) ((x - y) / 2))
    simpa [mul_assoc, mul_left_comm, mul_comm] using hrpow.comp x hbase_diff
  have hd :
      HasDerivAt g
        (((x + y) / 2) ^ (p - 1) * (p / 2) -
          coeffLeTwo p * (((x - y) / 2) ^ (p - 1)) * (p / 2)) x := by
    have htmp :
        HasDerivAt g
          (p * (((x + y) / 2) ^ (p - 1)) * (1 / 2) -
            coeffLeTwo p * (p * (((x - y) / 2) ^ (p - 1)) * (1 / 2))) x := by
      dsimp [g]
      exact hpow_sum.sub (hpow_diff.const_mul (coeffLeTwo p))
    refine htmp.congr_deriv ?_
    ring
  have hx : 0 < x := by linarith
  refine (hd.congr_of_eventuallyEq hEq).congr_deriv ?_
  simp [DxvLeTwo, hx, abs_of_pos hsum, abs_of_pos hdiff]

lemma continuous_vLeTwo_leTwo (p : ℝ) (hp1 : 1 < p) :
    Continuous (fun z : ℝ × ℝ => vLeTwo p z.1 z.2) := by
  have hp_nonneg : (0 : ℝ) ≤ p := by linarith
  simp only [vLeTwo]
  apply Continuous.sub
  · apply Continuous.rpow_const _ (fun _ => Or.inr hp_nonneg)
    exact ((continuous_fst.add continuous_snd).div_const 2).abs
  · apply Continuous.mul continuous_const
    apply Continuous.rpow_const _ (fun _ => Or.inr hp_nonneg)
    exact ((continuous_fst.sub continuous_snd).div_const 2).abs

lemma differentiableAt_DxvLeTwo_x_of_pos_leTwo (p x y : ℝ)
    (hsum : 0 < (x + y) / 2) (hdiff : 0 < (x - y) / 2) :
    DifferentiableAt ℝ (fun t => DxvLeTwo p t y) x := by
  have hx : 0 < x := by linarith
  have hEq :
      (fun t => DxvLeTwo p t y) =ᶠ[nhds x]
        fun t =>
          ((t + y) / 2) ^ (p - 1) * (p / 2) -
            coeffLeTwo p * ((t - y) / 2) ^ (p - 1) * (p / 2) := by
    have hsum_nhds : {t : ℝ | 0 < (t + y) / 2} ∈ nhds x := by
      exact ((((continuous_id'.add continuous_const).div_const 2).continuousAt).preimage_mem_nhds
        (Ioi_mem_nhds hsum))
    have hdiff_nhds : {t : ℝ | 0 < (t - y) / 2} ∈ nhds x := by
      exact ((((continuous_id'.sub continuous_const).div_const 2).continuousAt).preimage_mem_nhds
        (Ioi_mem_nhds hdiff))
    filter_upwards [Ioi_mem_nhds hx, hsum_nhds, hdiff_nhds] with t ht htsum htdiff
    have htpos : 0 < t := by simpa using ht
    simp [DxvLeTwo, htpos, abs_of_pos htsum, abs_of_pos htdiff]
  have hsum_diff :
      DifferentiableAt ℝ (fun t : ℝ => ((t + y) / 2) ^ (p - 1)) x := by
    have hbase : DifferentiableAt ℝ (fun t : ℝ => (t + y) / 2) x := by
      simpa [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using
        (((differentiableAt_id.add (differentiableAt_const y)).const_mul (1 / 2 : ℝ)))
    exact hbase.rpow_const (Or.inl (ne_of_gt hsum))
  have hdiff_diff :
      DifferentiableAt ℝ (fun t : ℝ => ((t - y) / 2) ^ (p - 1)) x := by
    have hbase : DifferentiableAt ℝ (fun t : ℝ => (t - y) / 2) x := by
      simpa [sub_eq_add_neg, div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using
        (((differentiableAt_id.sub (differentiableAt_const y)).const_mul (1 / 2 : ℝ)))
    exact hbase.rpow_const (Or.inl (ne_of_gt hdiff))
  have hformula :
      DifferentiableAt ℝ
        (fun t : ℝ =>
          ((t + y) / 2) ^ (p - 1) * (p / 2) -
            coeffLeTwo p * ((t - y) / 2) ^ (p - 1) * (p / 2)) x := by
    exact (hsum_diff.mul_const (p / 2)).sub
      ((hdiff_diff.const_mul (coeffLeTwo p)).mul_const (p / 2))
  exact hformula.congr_of_eventuallyEq hEq

lemma vLeTwo_tangent_x_on_Icc_of_A2_leTwo
    (p : ℝ) (hp1 : 1 < p) (hp2 : p < 2) {lo hi x z y : ℝ}
    (hA2_int : ∀ t ∈ interior (Set.Icc lo hi), A2 p t y)
    (hx : x ∈ Set.Icc lo hi) (hz : z ∈ Set.Icc lo hi)
    (hderiv : HasDerivAt (fun t => vLeTwo p t y) (DxvLeTwo p x y) x) :
    vLeTwo p z y ≤ vLeTwo p x y + DxvLeTwo p x y * (z - x) := by
  have hcont : ContinuousOn (fun t => vLeTwo p t y) (Set.Icc lo hi) := by
    have hpair : Continuous (fun t : ℝ => (t, y)) := by continuity
    simpa using
      ((continuous_vLeTwo_leTwo p hp1).comp hpair).continuousOn
  apply tangent_inequality_on_Icc_of_hasDerivWithinAt2_nonpos_leTwo
      (f := fun t => vLeTwo p t y)
      (f₁ := fun t => DxvLeTwo p t y)
      (f₂ := fun t => deriv (fun s => DxvLeTwo p s y) t)
      (f' := DxvLeTwo p x y)
  · exact hcont
  · intro t ht
    have hA2 := hA2_int t ht
    rcases hA2 with ⟨htpos, hlo, hup⟩
    have ha_pos : 0 < a p := by
      rw [a_eq_leTwo p hp1 hp2]
      exact div_pos (by linarith) (by linarith)
    have hy_pos : 0 < y := lt_trans (mul_pos ha_pos htpos) hlo
    have hsum : 0 < (t + y) / 2 := by linarith
    have hdiff : 0 < (t - y) / 2 := by linarith
    exact (hasDerivAt_vLeTwo_x_of_pos_leTwo p t y hsum hdiff).hasDerivWithinAt
  · intro t ht
    have hA2 := hA2_int t ht
    rcases hA2 with ⟨htpos, hlo, hup⟩
    have ha_pos : 0 < a p := by
      rw [a_eq_leTwo p hp1 hp2]
      exact div_pos (by linarith) (by linarith)
    have hy_pos : 0 < y := lt_trans (mul_pos ha_pos htpos) hlo
    have hsum : 0 < (t + y) / 2 := by linarith
    have hdiff : 0 < (t - y) / 2 := by linarith
    exact (differentiableAt_DxvLeTwo_x_of_pos_leTwo p t y hsum hdiff).hasDerivAt.hasDerivWithinAt
  · intro t ht
    exact deriv_DxvLeTwo_x_nonpos_leTwo p hp1 hp2 t y (hA2_int t ht)
  · exact hx
  · exact hz
  · exact hderiv

lemma DxauxFunction1_A2_boundary_le_leTwo
    (p : ℝ) (hp1 : 1 < p) (hp2 : p < 2) {x y : ℝ}
    (hy_pos : 0 < y) (hyx : y < x) (hax : a p * x < y) :
    DxauxFunction1 p (y / a p) y ≤ DxauxFunction1 p x y := by
  have ha_pos : 0 < a p := by
    rw [a_eq_leTwo p hp1 hp2]
    exact div_pos (by linarith) (by linarith)
  let c : ℝ := y / a p
  have hac : a p * c = y := by
    dsimp [c]
    field_simp [ha_pos.ne']
  have hxc : x < c := by
    have hmul : a p * x < a p * c := by simpa [hac] using hax
    nlinarith [hmul, ha_pos]
  have hx_pos : 0 < x := lt_trans hy_pos hyx
  have hboundary := horizontal_boundary_closureA1_closureA2_leTwo p y hp1 hp2 hy_pos
  have hcl_x : closureA2 p x y := ⟨hx_pos.le, le_of_lt hax, hyx.le⟩
  have hanti :
      AntitoneOn (fun t : ℝ => DxvLeTwo p t y) (Set.Icc x c) := by
    have hcont : ContinuousOn (fun t : ℝ => DxvLeTwo p t y) (Set.Icc x c) := by
      let g : ℝ → ℝ := fun t =>
        ((t + y) / 2) ^ (p - 1) * (p / 2) -
          coeffLeTwo p * ((t - y) / 2) ^ (p - 1) * (p / 2)
      have hg : ContinuousOn g (Set.Icc x c) := by
        dsimp [g]
        apply ContinuousOn.sub
        · exact ((continuousOn_id.add continuousOn_const).div_const 2).rpow_const
            (fun t ht => Or.inl (ne_of_gt (by
              change 0 < (t + y) / 2
              linarith [hx_pos, ht.1, hy_pos]))) |>.mul
            continuousOn_const
        · exact (continuousOn_const.mul
            (((continuousOn_id.sub continuousOn_const).div_const 2).rpow_const
              (fun t ht => Or.inl (ne_of_gt (by
                change 0 < (t - y) / 2
                linarith [hyx, ht.1]))))).mul
            continuousOn_const
      refine ContinuousOn.congr hg ?_
      intro t ht
      have ht_pos : 0 < t := lt_of_lt_of_le hx_pos ht.1
      have hsum : 0 < (t + y) / 2 := by linarith [ht_pos, hy_pos]
      have hdiff : 0 < (t - y) / 2 := by linarith [hyx, ht.1]
      simp [g, DxvLeTwo, ht_pos, abs_of_pos hsum, abs_of_pos hdiff]
    refine antitoneOn_of_hasDerivWithinAt_nonpos
      (D := Set.Icc x c)
      (f := fun t : ℝ => DxvLeTwo p t y)
      (f' := fun t : ℝ => deriv (fun s => DxvLeTwo p s y) t)
      (convex_Icc x c) hcont ?_ ?_
    · intro t ht
      have htIoo : t ∈ Set.Ioo x c := by
        simpa [interior_Icc] using ht
      have hsum : 0 < (t + y) / 2 := by linarith [hx_pos, htIoo.1, hy_pos]
      have hdiff : 0 < (t - y) / 2 := by linarith [hyx, htIoo.1]
      exact (differentiableAt_DxvLeTwo_x_of_pos_leTwo p t y hsum hdiff).hasDerivAt.hasDerivWithinAt
    · intro t ht
      have htIoo : t ∈ Set.Ioo x c := by
        simpa [interior_Icc] using ht
      have h_at : a p * t < y := by
        have hmul : a p * t < a p * c := mul_lt_mul_of_pos_left htIoo.2 ha_pos
        simpa [hac] using hmul
      exact deriv_DxvLeTwo_x_nonpos_leTwo p hp1 hp2 t y
        ⟨lt_trans hx_pos htIoo.1, h_at, lt_trans hyx htIoo.1⟩
  have hx_mem : x ∈ Set.Icc x c := ⟨le_rfl, hxc.le⟩
  have hc_mem : c ∈ Set.Icc x c := ⟨hxc.le, le_rfl⟩
  have hle : DxvLeTwo p c y ≤ DxvLeTwo p x y :=
    hanti hx_mem hc_mem hxc.le
  simpa [c, auxFunction1_Dx_eq_DxvLeTwo_leTwo p hp1 hp2 x y hcl_x,
    auxFunction1_Dx_eq_DxvLeTwo_leTwo p hp1 hp2 (y / a p) y hboundary.2] using hle

lemma DxauxFunction1_A1_le_boundary_leTwo
    (p : ℝ) (hp1 : 1 < p) (hp2 : p < 2) {x y : ℝ}
    (hy_pos : 0 < y) (hyx : y < x) (hay : y < a p * x) :
    DxauxFunction1 p x y ≤ DxauxFunction1 p (y / a p) y := by
  have ha_pos : 0 < a p := by
    rw [a_eq_leTwo p hp1 hp2]
    exact div_pos (by linarith) (by linarith)
  let c : ℝ := y / a p
  have hac : a p * c = y := by
    dsimp [c]
    field_simp [ha_pos.ne']
  have hcx : c < x := by
    have hmul : a p * c < a p * x := by simpa [hac] using hay
    nlinarith [hmul, ha_pos]
  have hx_pos : 0 < x := lt_trans hy_pos hyx
  have hc_pos : 0 < c := div_pos hy_pos ha_pos
  have hboundary := horizontal_boundary_closureA1_closureA2_leTwo p y hp1 hp2 hy_pos
  have hcl_x : closureA1 p x y := ⟨hx_pos.le, by linarith [hx_pos, hy_pos], le_of_lt hay⟩
  have hanti :
      AntitoneOn (fun t : ℝ => DxuA1Fun p (t, y)) (Set.Icc c x) := by
    have hcont : ContinuousOn (fun t : ℝ => DxuA1Fun p (t, y)) (Set.Icc c x) := by
      let g : ℝ → ℝ := fun t =>
        alpha p * (p / 2) * t ^ (p - 2) *
          (((p - 2) / (p - 1)) * t + y)
      have hg : ContinuousOn g (Set.Icc c x) := by
        dsimp [g]
        exact ((continuousOn_const.mul continuousOn_const).mul
          (continuousOn_id.rpow_const
            (fun t ht => Or.inl (ne_of_gt (lt_of_lt_of_le hc_pos ht.1))))).mul
          ((continuousOn_const.mul continuousOn_id).add continuousOn_const)
      refine ContinuousOn.congr hg ?_
      intro t ht
      have htpos : 0 < t := lt_of_lt_of_le hc_pos ht.1
      simp [g, DxuA1Fun, DxuA1, htpos]
    refine antitoneOn_of_hasDerivWithinAt_nonpos
      (D := Set.Icc c x)
      (f := fun t : ℝ => DxuA1Fun p (t, y))
      (f' := fun t : ℝ => deriv (fun s => DxuA1Fun p (s, y)) t)
      (convex_Icc c x) hcont ?_ ?_
    · intro t ht
      have htIoo : t ∈ Set.Ioo c x := by
        simpa [interior_Icc] using ht
      exact (differentiableAt_DxuA1Fun_x_of_pos_leTwo p t y
        (lt_trans hc_pos htIoo.1)).hasDerivAt.hasDerivWithinAt
    · intro t ht
      have htIoo : t ∈ Set.Ioo c x := by
        simpa [interior_Icc] using ht
      exact deriv_DxuA1Fun_x_nonpos_leTwo p hp1 hp2 t y
        (lt_trans hc_pos htIoo.1) (by linarith [hy_pos, lt_trans hc_pos htIoo.1])
  have hc_mem : c ∈ Set.Icc c x := ⟨le_rfl, hcx.le⟩
  have hx_mem : x ∈ Set.Icc c x := ⟨hcx.le, le_rfl⟩
  have hle : DxuA1Fun p (x, y) ≤ DxuA1Fun p (c, y) :=
    hanti hc_mem hx_mem hcx.le
  simpa [c, DxauxFunction1, hcl_x, hboundary.1, DxuA1Fun] using hle

lemma hasDerivAt_vLeTwo_y_of_pos_leTwo (p : ℝ) (x y : ℝ)
    (hsum : 0 < (x + y) / 2) (hdiff : 0 < (x - y) / 2) :
    HasDerivAt (fun s => vLeTwo p x s) (DyvLeTwo p x y) y := by
  let g : ℝ → ℝ := fun s =>
    ((x + s) / 2) ^ p - coeffLeTwo p * (((x - s) / 2) ^ p)
  have hsum_nhds : {s : ℝ | 0 < (x + s) / 2} ∈ nhds y := by
    exact ((((continuous_const.add continuous_id').div_const 2).continuousAt).preimage_mem_nhds
      (Ioi_mem_nhds hsum))
  have hdiff_nhds : {s : ℝ | 0 < (x - s) / 2} ∈ nhds y := by
    exact ((((continuous_const.sub continuous_id').div_const 2).continuousAt).preimage_mem_nhds
      (Ioi_mem_nhds hdiff))
  have hEq : (fun s => vLeTwo p x s) =ᶠ[nhds y] g := by
    filter_upwards [hsum_nhds, hdiff_nhds] with s hs_sum hs_diff
    simp [vLeTwo, g, abs_of_pos hs_sum, abs_of_pos hs_diff]
  have hbase_sum :
      HasDerivAt (fun s : ℝ => (x + s) / 2) (1 / 2) y := by
    simpa [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using
      (((hasDerivAt_id y).const_add x).const_mul (1 / 2 : ℝ))
  have hbase_diff :
      HasDerivAt (fun s : ℝ => (x - s) / 2) (-(1 / 2)) y := by
    simpa [sub_eq_add_neg, div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using
      ((((hasDerivAt_id y).neg).const_add x).const_mul (1 / 2 : ℝ))
  have hpow_sum :
      HasDerivAt (fun s : ℝ => ((x + s) / 2) ^ p)
        (p * (((x + y) / 2) ^ (p - 1)) * (1 / 2)) y := by
    have hrpow :
        HasDerivAt (fun t : ℝ => t ^ p) (p * (((x + y) / 2) ^ (p - 1))) ((x + y) / 2) := by
      simpa using
        (Real.hasDerivAt_rpow_const (Or.inl (ne_of_gt hsum)) :
          HasDerivAt (fun t : ℝ => t ^ p) (p * ((x + y) / 2) ^ (p - 1)) ((x + y) / 2))
    simpa [mul_assoc, mul_left_comm, mul_comm] using hrpow.comp y hbase_sum
  have hpow_diff :
      HasDerivAt (fun s : ℝ => ((x - s) / 2) ^ p)
        (p * (((x - y) / 2) ^ (p - 1)) * (-(1 / 2))) y := by
    have hrpow :
        HasDerivAt (fun t : ℝ => t ^ p) (p * (((x - y) / 2) ^ (p - 1))) ((x - y) / 2) := by
      simpa using
        (Real.hasDerivAt_rpow_const (Or.inl (ne_of_gt hdiff)) :
          HasDerivAt (fun t : ℝ => t ^ p) (p * ((x - y) / 2) ^ (p - 1)) ((x - y) / 2))
    simpa [mul_assoc, mul_left_comm, mul_comm] using hrpow.comp y hbase_diff
  have hd :
      HasDerivAt g
        (((x + y) / 2) ^ (p - 1) * (p / 2) +
          coeffLeTwo p * (((x - y) / 2) ^ (p - 1)) * (p / 2)) y := by
    have htmp :
        HasDerivAt g
          (p * (((x + y) / 2) ^ (p - 1)) * (1 / 2) -
            coeffLeTwo p * (p * (((x - y) / 2) ^ (p - 1)) * (-(1 / 2)))) y := by
      dsimp [g]
      exact hpow_sum.sub (hpow_diff.const_mul (coeffLeTwo p))
    refine htmp.congr_deriv ?_
    ring
  have hx : 0 < x := by linarith
  refine (hd.congr_of_eventuallyEq hEq).congr_deriv ?_
  simp [DyvLeTwo, hx, abs_of_pos hsum, abs_of_pos hdiff]

lemma differentiableAt_DyvLeTwo_y_of_pos_leTwo (p x y : ℝ)
    (hsum : 0 < (x + y) / 2) (hdiff : 0 < (x - y) / 2) :
    DifferentiableAt ℝ (fun s => DyvLeTwo p x s) y := by
  have hx : 0 < x := by linarith
  have hEq :
      (fun s => DyvLeTwo p x s) =ᶠ[nhds y]
        fun s =>
          ((x + s) / 2) ^ (p - 1) * (p / 2) +
            coeffLeTwo p * ((x - s) / 2) ^ (p - 1) * (p / 2) := by
    have hsum_nhds : {s : ℝ | 0 < (x + s) / 2} ∈ nhds y := by
      exact ((((continuous_const.add continuous_id').div_const 2).continuousAt).preimage_mem_nhds
        (Ioi_mem_nhds hsum))
    have hdiff_nhds : {s : ℝ | 0 < (x - s) / 2} ∈ nhds y := by
      exact ((((continuous_const.sub continuous_id').div_const 2).continuousAt).preimage_mem_nhds
        (Ioi_mem_nhds hdiff))
    filter_upwards [hsum_nhds, hdiff_nhds] with s hssum hsdiff
    simp [DyvLeTwo, hx, abs_of_pos hssum, abs_of_pos hsdiff]
  have hsum_diff :
      DifferentiableAt ℝ (fun s : ℝ => ((x + s) / 2) ^ (p - 1)) y := by
    have hbase : DifferentiableAt ℝ (fun s : ℝ => (x + s) / 2) y := by
      simpa [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using
        (((differentiableAt_id.const_add x).const_mul (1 / 2 : ℝ)))
    exact hbase.rpow_const (Or.inl (ne_of_gt hsum))
  have hdiff_diff :
      DifferentiableAt ℝ (fun s : ℝ => ((x - s) / 2) ^ (p - 1)) y := by
    have hbase : DifferentiableAt ℝ (fun s : ℝ => (x - s) / 2) y := by
      simpa [sub_eq_add_neg, div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using
        (((differentiableAt_const x).sub differentiableAt_id).const_mul (1 / 2 : ℝ))
    exact hbase.rpow_const (Or.inl (ne_of_gt hdiff))
  have hformula :
      DifferentiableAt ℝ
        (fun s : ℝ =>
          ((x + s) / 2) ^ (p - 1) * (p / 2) +
            coeffLeTwo p * ((x - s) / 2) ^ (p - 1) * (p / 2)) y := by
    exact (hsum_diff.mul_const (p / 2)).add
      ((hdiff_diff.const_mul (coeffLeTwo p)).mul_const (p / 2))
  exact hformula.congr_of_eventuallyEq hEq

lemma deriv_DyvLeTwo_y_nonpos_leTwo
    (p : ℝ) (hp1 : 1 < p) (hp2 : p < 2) (x y : ℝ)
    (hA2 : A2 p x y) :
    deriv (fun s => DyvLeTwo p x s) y ≤ 0 := by
  rcases hA2 with ⟨hx, hay, hyx⟩
  have hsum : 0 < (x + y) / 2 := by
    have ha_pos : 0 < a p := by
      rw [a_eq_leTwo p hp1 hp2]
      exact div_pos (by linarith) (by linarith)
    have hy_pos : 0 < y := lt_trans (mul_pos ha_pos hx) hay
    linarith
  have hdiff : 0 < (x - y) / 2 := by linarith
  have hEq :
      (fun s => DyvLeTwo p x s) =ᶠ[nhds y]
        fun s =>
          ((x + s) / 2) ^ (p - 1) * (p / 2) +
            coeffLeTwo p * ((x - s) / 2) ^ (p - 1) * (p / 2) := by
    have hsum_nhds : {s : ℝ | 0 < (x + s) / 2} ∈ nhds y := by
      exact ((((continuous_const.add continuous_id').div_const 2).continuousAt).preimage_mem_nhds
        (Ioi_mem_nhds hsum))
    have hdiff_nhds : {s : ℝ | 0 < (x - s) / 2} ∈ nhds y := by
      exact ((((continuous_const.sub continuous_id').div_const 2).continuousAt).preimage_mem_nhds
        (Ioi_mem_nhds hdiff))
    filter_upwards [hsum_nhds, hdiff_nhds] with s hssum hsdiff
    simp [DyvLeTwo, hx, abs_of_pos hssum, abs_of_pos hsdiff]
  have hbase_sum :
      HasDerivAt (fun s : ℝ => (x + s) / 2) (1 / 2) y := by
    simpa [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using
      (((hasDerivAt_id y).const_add x).const_mul (1 / 2 : ℝ))
  have hbase_diff :
      HasDerivAt (fun s : ℝ => (x - s) / 2) (-(1 / 2)) y := by
    simpa [sub_eq_add_neg, div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using
      ((((hasDerivAt_id y).neg).const_add x).const_mul (1 / 2 : ℝ))
  have hpow_sum :
      HasDerivAt (fun s : ℝ => ((x + s) / 2) ^ (p - 1))
        ((p - 1) * (((x + y) / 2) ^ (p - 2)) * (1 / 2)) y := by
    have hrpow :
        HasDerivAt (fun u : ℝ => u ^ (p - 1))
          ((p - 1) * (((x + y) / 2) ^ (p - 2))) ((x + y) / 2) := by
      simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm,
        show p + (-1 + -1) = p + -2 by ring] using
        (Real.hasDerivAt_rpow_const (Or.inl (ne_of_gt hsum)) :
          HasDerivAt (fun u : ℝ => u ^ (p - 1))
            ((p - 1) * ((x + y) / 2) ^ ((p - 1) - 1)) ((x + y) / 2))
    simpa [mul_assoc, mul_left_comm, mul_comm] using hrpow.comp y hbase_sum
  have hpow_diff :
      HasDerivAt (fun s : ℝ => ((x - s) / 2) ^ (p - 1))
        ((p - 1) * (((x - y) / 2) ^ (p - 2)) * (-(1 / 2))) y := by
    have hrpow :
        HasDerivAt (fun u : ℝ => u ^ (p - 1))
          ((p - 1) * (((x - y) / 2) ^ (p - 2))) ((x - y) / 2) := by
      simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm,
        show p + (-1 + -1) = p + -2 by ring] using
        (Real.hasDerivAt_rpow_const (Or.inl (ne_of_gt hdiff)) :
          HasDerivAt (fun u : ℝ => u ^ (p - 1))
            ((p - 1) * ((x - y) / 2) ^ ((p - 1) - 1)) ((x - y) / 2))
    simpa [mul_assoc, mul_left_comm, mul_comm] using hrpow.comp y hbase_diff
  have hd :
      HasDerivAt
        (fun s : ℝ =>
          ((x + s) / 2) ^ (p - 1) * (p / 2) +
            coeffLeTwo p * ((x - s) / 2) ^ (p - 1) * (p / 2))
        ((p * (p - 1) / 4) *
          (((x + y) / 2) ^ (p - 2) -
            coeffLeTwo p * ((x - y) / 2) ^ (p - 2))) y := by
    have htmp :
        HasDerivAt
          (fun s : ℝ =>
            ((x + s) / 2) ^ (p - 1) * (p / 2) +
              coeffLeTwo p * ((x - s) / 2) ^ (p - 1) * (p / 2))
          (((p - 1) * (((x + y) / 2) ^ (p - 2)) * (1 / 2)) * (p / 2) +
            coeffLeTwo p *
              (((p - 1) * (((x - y) / 2) ^ (p - 2)) * (-(1 / 2)))) *
                (p / 2)) y := by
      exact (hpow_sum.mul_const (p / 2)).add
        ((hpow_diff.const_mul (coeffLeTwo p)).mul_const (p / 2))
    refine htmp.congr_deriv ?_
    ring
  rw [hEq.deriv_eq, hd.deriv]
  have hcoef : 0 ≤ p * (p - 1) / 4 := by
    exact div_nonneg (mul_nonneg (by linarith) (by linarith)) (by norm_num)
  have hbr := vLeTwo_A2_second_bracket_nonpos_leTwo p hp1 hp2 x y ⟨hx, hay, hyx⟩
  exact mul_nonpos_of_nonneg_of_nonpos hcoef hbr

lemma vLeTwo_tangent_y_on_Icc_of_A2_leTwo
    (p : ℝ) (hp1 : 1 < p) (hp2 : p < 2) {lo hi y z x : ℝ}
    (hA2_int : ∀ t ∈ interior (Set.Icc lo hi), A2 p x t)
    (hy : y ∈ Set.Icc lo hi) (hz : z ∈ Set.Icc lo hi)
    (hderiv : HasDerivAt (fun t => vLeTwo p x t) (DyvLeTwo p x y) y) :
    vLeTwo p x z ≤ vLeTwo p x y + DyvLeTwo p x y * (z - y) := by
  have hcont : ContinuousOn (fun t => vLeTwo p x t) (Set.Icc lo hi) := by
    have hpair : Continuous (fun t : ℝ => (x, t)) := by continuity
    simpa using
      ((continuous_vLeTwo_leTwo p hp1).comp hpair).continuousOn
  apply tangent_inequality_on_Icc_of_hasDerivWithinAt2_nonpos_leTwo
      (f := fun t => vLeTwo p x t)
      (f₁ := fun t => DyvLeTwo p x t)
      (f₂ := fun t => deriv (fun s => DyvLeTwo p x s) t)
      (f' := DyvLeTwo p x y)
  · exact hcont
  · intro t ht
    rcases hA2_int t ht with ⟨hx, hat, htx⟩
    have ha_pos : 0 < a p := by
      rw [a_eq_leTwo p hp1 hp2]
      exact div_pos (by linarith) (by linarith)
    have ht_pos : 0 < t := lt_trans (mul_pos ha_pos hx) hat
    have hsum : 0 < (x + t) / 2 := by linarith
    have hdiff : 0 < (x - t) / 2 := by linarith
    exact (hasDerivAt_vLeTwo_y_of_pos_leTwo p x t hsum hdiff).hasDerivWithinAt
  · intro t ht
    rcases hA2_int t ht with ⟨hx, hat, htx⟩
    have ha_pos : 0 < a p := by
      rw [a_eq_leTwo p hp1 hp2]
      exact div_pos (by linarith) (by linarith)
    have ht_pos : 0 < t := lt_trans (mul_pos ha_pos hx) hat
    have hsum : 0 < (x + t) / 2 := by linarith
    have hdiff : 0 < (x - t) / 2 := by linarith
    exact (differentiableAt_DyvLeTwo_y_of_pos_leTwo p x t hsum hdiff).hasDerivAt.hasDerivWithinAt
  · intro t ht
    exact deriv_DyvLeTwo_y_nonpos_leTwo p hp1 hp2 x t (hA2_int t ht)
  · exact hy
  · exact hz
  · exact hderiv

lemma uA1_affine_y_tangent_leTwo
    (p x y z : ℝ) (hx : 0 < x) :
    uA1 p x z = uA1 p x y + DyuA1 p x y * (z - y) := by
  simp [uA1, DyuA1, hx]
  ring

lemma uCandidate_tangent_x_on_Q3_A1_segment_leTwo
    (p : ℝ) (hp1 : 1 < p) (hp2 : p < 2) {x z y : ℝ}
    (hy_pos : 0 < y) (hx_lower : -y < x) (hx_upper : x < a p * y)
    (hz_lower : -y < z) (hz_upper : z < a p * y) :
    uCandidate p z y ≤
      uCandidate p x y + DxuCandidate p x y * (z - x) := by
  have hQx : QuarterPlane3 x y := ⟨hy_pos.le, le_of_lt hx_lower, by
    have ha_lt : a p < 1 := a_lt_one_of_one_lt_of_lt_two p hp1 hp2
    have hax_lt_y : a p * y < y := by
      simpa using mul_lt_mul_of_pos_right ha_lt hy_pos
    exact le_of_lt (lt_trans hx_upper hax_lt_y)⟩
  have hQz : QuarterPlane3 z y := ⟨hy_pos.le, le_of_lt hz_lower, by
    have ha_lt : a p < 1 := a_lt_one_of_one_lt_of_lt_two p hp1 hp2
    have hax_lt_y : a p * y < y := by
      simpa using mul_lt_mul_of_pos_right ha_lt hy_pos
    exact le_of_lt (lt_trans hz_upper hax_lt_y)⟩
  have hclx : closureA1 p y x := ⟨hy_pos.le, le_of_lt hx_lower, le_of_lt hx_upper⟩
  have hclz : closureA1 p y z := ⟨hy_pos.le, le_of_lt hz_lower, le_of_lt hz_upper⟩
  have hux : uCandidate p x y = uA1 p y x := by
    rw [uCandidate_eq_Q3_leTwo p hQx]
    simp [auxFunction1, hclx]
  have huz : uCandidate p z y = uA1 p y z := by
    rw [uCandidate_eq_Q3_leTwo p hQz]
    simp [auxFunction1, hclz]
  have hdx : DxuCandidate p x y = DyuA1 p y x := by
    rw [DxuCandidate_eq_Q3_leTwo p hp1 hp2 hQx]
    simp [DyauxFunction1, hclx]
  apply le_of_eq
  calc
    uCandidate p z y = uA1 p y z := huz
    _ = uA1 p y x + DyuA1 p y x * (z - x) :=
        uA1_affine_y_tangent_leTwo p y x z hy_pos
    _ = uCandidate p x y + DxuCandidate p x y * (z - x) := by
        rw [hux, hdx]

lemma uCandidate_tangent_x_on_Q3_A2_segment_leTwo
    (p : ℝ) (hp1 : 1 < p) (hp2 : p < 2) {x z y : ℝ}
    (hy_pos : 0 < y) (hx_lower : a p * y < x) (hx_upper : x < y)
    (hz_lower : a p * y < z) (hz_upper : z < y) :
    uCandidate p z y ≤
      uCandidate p x y + DxuCandidate p x y * (z - x) := by
  have hQx : QuarterPlane3 x y := ⟨hy_pos.le, by
    have ha_nonneg : 0 ≤ a p := a_nonneg_of_one_lt_of_lt_two p hp1 hp2
    have haxy_nonneg : 0 ≤ a p * y := mul_nonneg ha_nonneg hy_pos.le
    linarith, le_of_lt hx_upper⟩
  have hQz : QuarterPlane3 z y := ⟨hy_pos.le, by
    have ha_nonneg : 0 ≤ a p := a_nonneg_of_one_lt_of_lt_two p hp1 hp2
    have haxy_nonneg : 0 ≤ a p * y := mul_nonneg ha_nonneg hy_pos.le
    linarith, le_of_lt hz_upper⟩
  have hclx : closureA2 p y x := ⟨hy_pos.le, le_of_lt hx_lower, le_of_lt hx_upper⟩
  have hclz : closureA2 p y z := ⟨hy_pos.le, le_of_lt hz_lower, le_of_lt hz_upper⟩
  have hux : uCandidate p x y = vLeTwo p y x := by
    rw [uCandidate_eq_Q3_leTwo p hQx, auxFunction1_eq_vLeTwo_leTwo p hp1 hp2 y x hclx]
  have huz : uCandidate p z y = vLeTwo p y z := by
    rw [uCandidate_eq_Q3_leTwo p hQz, auxFunction1_eq_vLeTwo_leTwo p hp1 hp2 y z hclz]
  have hdx : DxuCandidate p x y = DyvLeTwo p y x := by
    rw [DxuCandidate_eq_Q3_leTwo p hp1 hp2 hQx]
    have hnot : ¬ closureA1 p y x := by
      intro h
      exact not_le_of_gt hx_lower h.2.2
    simp [DyauxFunction1, hnot, hclx]
  have hderiv :
      HasDerivAt (fun t => vLeTwo p y t) (DyvLeTwo p y x) x := by
    have hsum : 0 < (y + x) / 2 := by
      have ha_nonneg : 0 ≤ a p := a_nonneg_of_one_lt_of_lt_two p hp1 hp2
      have haxy_nonneg : 0 ≤ a p * y := mul_nonneg ha_nonneg hy_pos.le
      linarith
    have hdiff : 0 < (y - x) / 2 := by linarith
    exact hasDerivAt_vLeTwo_y_of_pos_leTwo p y x hsum hdiff
  have hmain :
      vLeTwo p y z ≤ vLeTwo p y x + DyvLeTwo p y x * (z - x) := by
    apply vLeTwo_tangent_y_on_Icc_of_A2_leTwo
        (p := p) (hp1 := hp1) (hp2 := hp2)
        (lo := min x z) (hi := max x z) (x := y)
        (y := x) (z := z)
    · intro t ht
      have htI : t ∈ Set.Icc (min x z) (max x z) := interior_subset ht
      have hlow : a p * y < min x z := lt_min hx_lower hz_lower
      have hhi : max x z < y := max_lt hx_upper hz_upper
      exact ⟨hy_pos, lt_of_lt_of_le hlow htI.1, lt_of_le_of_lt htI.2 hhi⟩
    · exact ⟨min_le_left x z, le_max_left x z⟩
    · exact ⟨min_le_right x z, le_max_right x z⟩
    · exact hderiv
  calc
    uCandidate p z y = vLeTwo p y z := huz
    _ ≤ vLeTwo p y x + DyvLeTwo p y x * (z - x) := hmain
    _ = uCandidate p x y + DxuCandidate p x y * (z - x) := by
      rw [hux, hdx]

lemma tangent_glue_two_forward_leTwo_local
    (f d : ℝ → ℝ) {x m z : ℝ}
    (_hxm : x ≤ m) (hmz : m ≤ z)
    (hxm_tangent : f m ≤ f x + d x * (m - x))
    (hmz_tangent : f z ≤ f m + d m * (z - m))
    (hd_antitone : d m ≤ d x) :
    f z ≤ f x + d x * (z - x) := by
  have hnonneg : 0 ≤ z - m := by linarith
  have hmul : d m * (z - m) ≤ d x * (z - m) :=
    mul_le_mul_of_nonneg_right hd_antitone hnonneg
  calc
    f z ≤ f m + d m * (z - m) := hmz_tangent
    _ ≤ (f x + d x * (m - x)) + d m * (z - m) := by linarith
    _ ≤ (f x + d x * (m - x)) + d x * (z - m) := by linarith
    _ = f x + d x * (z - x) := by ring

lemma tangent_glue_two_backward_leTwo_local
    (f d : ℝ → ℝ) {x m z : ℝ}
    (hzm : z ≤ m) (_hmx : m ≤ x)
    (hxm_tangent : f m ≤ f x + d x * (m - x))
    (hmz_tangent : f z ≤ f m + d m * (z - m))
    (hd_antitone : d x ≤ d m) :
    f z ≤ f x + d x * (z - x) := by
  have hnonpos : z - m ≤ 0 := by linarith
  have hmul : d m * (z - m) ≤ d x * (z - m) :=
    mul_le_mul_of_nonpos_right hd_antitone hnonpos
  calc
    f z ≤ f m + d m * (z - m) := hmz_tangent
    _ ≤ (f x + d x * (m - x)) + d m * (z - m) := by linarith
    _ ≤ (f x + d x * (m - x)) + d x * (z - m) := by linarith
    _ = f x + d x * (z - x) := by ring

lemma uCandidate_tangent_x_Q3_A1_to_A2_boundary_leTwo
    (p : ℝ) (hp1 : 1 < p) (hp2 : p < 2) {x y : ℝ}
    (hy_pos : 0 < y) (hx_lower : -y < x) (hx_upper : x < a p * y) :
    uCandidate p (a p * y) y ≤
      uCandidate p x y + DxuCandidate p x y * (a p * y - x) := by
  have ha_nonneg : 0 ≤ a p := a_nonneg_of_one_lt_of_lt_two p hp1 hp2
  have ha_lt : a p < 1 := a_lt_one_of_one_lt_of_lt_two p hp1 hp2
  have hQx : QuarterPlane3 x y := ⟨hy_pos.le, le_of_lt hx_lower, by
    have haxy_lt_y : a p * y < y := by
      simpa using mul_lt_mul_of_pos_right ha_lt hy_pos
    exact le_of_lt (lt_trans hx_upper haxy_lt_y)⟩
  have hQc : QuarterPlane3 (a p * y) y := ⟨hy_pos.le, by
    have hnonneg : 0 ≤ a p * y := mul_nonneg ha_nonneg hy_pos.le
    linarith, by
      have haxy_le_y : a p * y ≤ y := by
        simpa using mul_le_mul_of_nonneg_right ha_lt.le hy_pos.le
      exact haxy_le_y⟩
  have hclx : closureA1 p y x := ⟨hy_pos.le, le_of_lt hx_lower, le_of_lt hx_upper⟩
  have hclc : closureA1 p y (a p * y) := ⟨hy_pos.le, by
    have hnonneg : 0 ≤ a p * y := mul_nonneg ha_nonneg hy_pos.le
    linarith, le_rfl⟩
  have hux : uCandidate p x y = uA1 p y x := by
    rw [uCandidate_eq_Q3_leTwo p hQx]
    simp [auxFunction1, hclx]
  have huc : uCandidate p (a p * y) y = uA1 p y (a p * y) := by
    rw [uCandidate_eq_Q3_leTwo p hQc]
    simp [auxFunction1, hclc]
  have hdx : DxuCandidate p x y = DyuA1 p y x := by
    rw [DxuCandidate_eq_Q3_leTwo p hp1 hp2 hQx]
    simp [DyauxFunction1, hclx]
  apply le_of_eq
  calc
    uCandidate p (a p * y) y = uA1 p y (a p * y) := huc
    _ = uA1 p y x + DyuA1 p y x * (a p * y - x) :=
      uA1_affine_y_tangent_leTwo p y x (a p * y) hy_pos
    _ = uCandidate p x y + DxuCandidate p x y * (a p * y - x) := by
      rw [hux, hdx]

lemma uCandidate_tangent_x_Q3_A2_boundary_to_A2_leTwo
    (p : ℝ) (hp1 : 1 < p) (hp2 : p < 2) {z y : ℝ}
    (hy_pos : 0 < y) (hz_lower : a p * y < z) (hz_upper : z < y) :
    uCandidate p z y ≤
      uCandidate p (a p * y) y +
        DxuCandidate p (a p * y) y * (z - a p * y) := by
  have ha_pos : 0 < a p := by
    rw [a_eq_leTwo p hp1 hp2]
    exact div_pos (by linarith) (by linarith)
  have ha_nonneg : 0 ≤ a p := ha_pos.le
  have ha_lt : a p < 1 := a_lt_one_of_one_lt_of_lt_two p hp1 hp2
  have hc_pos : 0 < a p * y := mul_pos ha_pos hy_pos
  have hc_lt_y : a p * y < y := by
    simpa using mul_lt_mul_of_pos_right ha_lt hy_pos
  have hQc : QuarterPlane3 (a p * y) y := ⟨hy_pos.le, by linarith, le_of_lt hc_lt_y⟩
  have hQz : QuarterPlane3 z y := ⟨hy_pos.le, by linarith [hc_pos, hz_lower], le_of_lt hz_upper⟩
  have hclc1 : closureA1 p y (a p * y) := ⟨hy_pos.le, by linarith [hc_pos], le_rfl⟩
  have hclc2 : closureA2 p y (a p * y) := ⟨hy_pos.le, le_rfl, le_of_lt hc_lt_y⟩
  have hclz : closureA2 p y z := ⟨hy_pos.le, le_of_lt hz_lower, le_of_lt hz_upper⟩
  have huc : uCandidate p (a p * y) y = vLeTwo p y (a p * y) := by
    rw [uCandidate_eq_Q3_leTwo p hQc]
    rw [auxFunction1_eq_vLeTwo_leTwo p hp1 hp2 y (a p * y) hclc2]
  have huz : uCandidate p z y = vLeTwo p y z := by
    rw [uCandidate_eq_Q3_leTwo p hQz]
    rw [auxFunction1_eq_vLeTwo_leTwo p hp1 hp2 y z hclz]
  have hdc : DxuCandidate p (a p * y) y = DyvLeTwo p y (a p * y) := by
    rw [DxuCandidate_eq_Q3_leTwo p hp1 hp2 hQc]
    have hdyu : DyauxFunction1 p y (a p * y) = DyuA1 p y (a p * y) := by
      simp [DyauxFunction1, hclc1]
    have hglue := DyuA1_eq_DyvLeTwo_on_A1A2_boundary_leTwo
      p y hp1 hp2 hy_pos
    simpa [hdyu] using hglue
  have hderiv : HasDerivAt (fun t => vLeTwo p y t) (DyvLeTwo p y (a p * y)) (a p * y) := by
    have hsum : 0 < (y + a p * y) / 2 := by linarith [hy_pos, hc_pos]
    have hdiff : 0 < (y - a p * y) / 2 := by linarith [hc_lt_y]
    exact hasDerivAt_vLeTwo_y_of_pos_leTwo p y (a p * y) hsum hdiff
  have hmain :
      vLeTwo p y z ≤
        vLeTwo p y (a p * y) + DyvLeTwo p y (a p * y) * (z - a p * y) := by
    apply vLeTwo_tangent_y_on_Icc_of_A2_leTwo
        (p := p) (hp1 := hp1) (hp2 := hp2)
        (lo := a p * y) (hi := z) (x := y) (y := a p * y) (z := z)
    · intro t ht
      have htI : t ∈ Set.Ioo (a p * y) z := by
        simpa [interior_Icc] using ht
      exact ⟨hy_pos, htI.1, lt_trans htI.2 hz_upper⟩
    · exact ⟨le_rfl, le_of_lt hz_lower⟩
    · exact ⟨le_of_lt hz_lower, le_rfl⟩
    · exact hderiv
  calc
    uCandidate p z y = vLeTwo p y z := huz
    _ ≤ vLeTwo p y (a p * y) + DyvLeTwo p y (a p * y) * (z - a p * y) := hmain
    _ = uCandidate p (a p * y) y +
        DxuCandidate p (a p * y) y * (z - a p * y) := by
      rw [huc, hdc]

lemma uCandidate_tangent_x_cross_Q3_A1_to_A2_leTwo
    (p : ℝ) (hp1 : 1 < p) (hp2 : p < 2) {x z y : ℝ}
    (hy_pos : 0 < y) (hx_lower : -y < x) (hx_upper : x < a p * y)
    (hz_lower : a p * y < z) (hz_upper : z < y) :
    uCandidate p z y ≤
      uCandidate p x y + DxuCandidate p x y * (z - x) := by
  have hxc := uCandidate_tangent_x_Q3_A1_to_A2_boundary_leTwo
    (p := p) (hp1 := hp1) (hp2 := hp2) (x := x) (y := y)
    hy_pos hx_lower hx_upper
  have hcz := uCandidate_tangent_x_Q3_A2_boundary_to_A2_leTwo
    (p := p) (hp1 := hp1) (hp2 := hp2) (z := z) (y := y)
    hy_pos hz_lower hz_upper
  have hd : DxuCandidate p (a p * y) y ≤ DxuCandidate p x y := by
    have ha_nonneg : 0 ≤ a p := a_nonneg_of_one_lt_of_lt_two p hp1 hp2
    have ha_lt : a p < 1 := a_lt_one_of_one_lt_of_lt_two p hp1 hp2
    have hQx : QuarterPlane3 x y := ⟨hy_pos.le, le_of_lt hx_lower, by
      have hc_lt_y : a p * y < y := by
        simpa using mul_lt_mul_of_pos_right ha_lt hy_pos
      exact le_of_lt (lt_trans hx_upper hc_lt_y)⟩
    have hQc : QuarterPlane3 (a p * y) y := ⟨hy_pos.le, by
      have hnonneg : 0 ≤ a p * y := mul_nonneg ha_nonneg hy_pos.le
      linarith, by
        have hle : a p * y ≤ y := by
          simpa using mul_le_mul_of_nonneg_right ha_lt.le hy_pos.le
        exact hle⟩
    have hclx : closureA1 p y x := ⟨hy_pos.le, le_of_lt hx_lower, le_of_lt hx_upper⟩
    have hclc : closureA1 p y (a p * y) := ⟨hy_pos.le, by
      have hnonneg : 0 ≤ a p * y := mul_nonneg ha_nonneg hy_pos.le
      linarith, le_rfl⟩
    have hdx : DxuCandidate p x y = DyuA1 p y x := by
      rw [DxuCandidate_eq_Q3_leTwo p hp1 hp2 hQx]
      simp [DyauxFunction1, hclx]
    have hdc : DxuCandidate p (a p * y) y = DyuA1 p y (a p * y) := by
      rw [DxuCandidate_eq_Q3_leTwo p hp1 hp2 hQc]
      simp [DyauxFunction1, hclc]
    rw [hdx, hdc]
    simp [DyuA1, hy_pos]
  exact tangent_glue_two_forward_leTwo_local
    (fun t => uCandidate p t y) (fun t => DxuCandidate p t y)
    (le_of_lt hx_upper) (le_of_lt hz_lower) hxc hcz hd

lemma uCandidate_tangent_x_on_Q1_A2_segment_leTwo
    (p : ℝ) (hp1 : 1 < p) (hp2 : p < 2) {x z y : ℝ}
    (hy_pos : 0 < y) (hx_lower : y < x) (hx_upper : x < y / a p)
    (hz_lower : y < z) (hz_upper : z < y / a p) :
    uCandidate p z y ≤
      uCandidate p x y + DxuCandidate p x y * (z - x) := by
  have ha_pos : 0 < a p := by
    rw [a_eq_leTwo p hp1 hp2]
    exact div_pos (by linarith) (by linarith)
  have hQx : QuarterPlane x y := ⟨by linarith, le_of_lt hx_lower, by linarith⟩
  have hQz : QuarterPlane z y := ⟨by linarith, le_of_lt hz_lower, by linarith⟩
  have hax : a p * x < y := by
    have hmul := mul_lt_mul_of_pos_left hx_upper ha_pos
    field_simp [ha_pos.ne'] at hmul
    simpa [mul_comm, mul_left_comm, mul_assoc] using hmul
  have haz : a p * z < y := by
    have hmul := mul_lt_mul_of_pos_left hz_upper ha_pos
    field_simp [ha_pos.ne'] at hmul
    simpa [mul_comm, mul_left_comm, mul_assoc] using hmul
  have hclx : closureA2 p x y := ⟨by linarith, by linarith, le_of_lt hx_lower⟩
  have hclz : closureA2 p z y := ⟨by linarith, by linarith, le_of_lt hz_lower⟩
  have hnotx : ¬ closureA1 p x y := by
    intro h
    exact not_le_of_gt hax h.2.2
  have hux : uCandidate p x y = vLeTwo p x y := by
    rw [uCandidate_eq_Q1_leTwo p hQx]
    simp [auxFunction1, hnotx, hclx]
  have huz : uCandidate p z y = vLeTwo p z y := by
    have hnotz : ¬ closureA1 p z y := by
      intro h
      exact not_le_of_gt haz h.2.2
    rw [uCandidate_eq_Q1_leTwo p hQz]
    simp [auxFunction1, hnotz, hclz]
  have hdx : DxuCandidate p x y = DxvLeTwo p x y := by
    rw [DxuCandidate_eq_Q1_leTwo p hQx]
    simp [DxauxFunction1, hnotx, hclx]
  have hderiv :
      HasDerivAt (fun t => vLeTwo p t y) (DxvLeTwo p x y) x := by
    have hsum : 0 < (x + y) / 2 := by linarith
    have hdiff : 0 < (x - y) / 2 := by linarith
    exact hasDerivAt_vLeTwo_x_of_pos_leTwo p x y hsum hdiff
  have hmain :
      vLeTwo p z y ≤ vLeTwo p x y + DxvLeTwo p x y * (z - x) := by
    apply vLeTwo_tangent_x_on_Icc_of_A2_leTwo
        (p := p) (hp1 := hp1) (hp2 := hp2)
        (lo := min x z) (hi := max x z) (y := y)
        (x := x) (z := z)
    · intro t ht
      have htI : t ∈ Set.Icc (min x z) (max x z) := interior_subset ht
      have hlow : y < min x z := lt_min hx_lower hz_lower
      have hhi : max x z < y / a p := max_lt hx_upper hz_upper
      have hyt : y < t := lt_of_lt_of_le hlow htI.1
      have ht_pos : 0 < t := lt_trans hy_pos hyt
      have hat : a p * t < y := by
        have ht_div : t < y / a p := lt_of_le_of_lt htI.2 hhi
        have hmul := mul_lt_mul_of_pos_left ht_div ha_pos
        field_simp [ha_pos.ne'] at hmul
        simpa [mul_comm, mul_left_comm, mul_assoc] using hmul
      exact ⟨ht_pos, hat, hyt⟩
    · exact ⟨min_le_left x z, le_max_left x z⟩
    · exact ⟨min_le_right x z, le_max_right x z⟩
    · exact hderiv
  calc
    uCandidate p z y = vLeTwo p z y := huz
    _ ≤ vLeTwo p x y + DxvLeTwo p x y * (z - x) := hmain
    _ = uCandidate p x y + DxuCandidate p x y * (z - x) := by
      rw [hux, hdx]

lemma DyvLeTwo_diag_le_DyvLeTwo_Q3_A2_leTwo
    (p : ℝ) (hp1 : 1 < p) (hp2 : p < 2) {x y : ℝ}
    (hy_pos : 0 < y) (hx_lower : a p * y < x) (hx_upper : x < y) :
    DyvLeTwo p y y ≤ DyvLeTwo p y x := by
  have hx_pos : 0 < x := by
    have ha_nonneg : 0 ≤ a p := a_nonneg_of_one_lt_of_lt_two p hp1 hp2
    have haxy_nonneg : 0 ≤ a p * y := mul_nonneg ha_nonneg hy_pos.le
    linarith
  have hanti :
      AntitoneOn (fun t : ℝ => DyvLeTwo p y t) (Set.Icc x y) := by
    have hcont : ContinuousOn (fun t : ℝ => DyvLeTwo p y t) (Set.Icc x y) := by
      let g : ℝ → ℝ := fun t =>
        ((y + t) / 2) ^ (p - 1) * (p / 2) +
          coeffLeTwo p * ((y - t) / 2) ^ (p - 1) * (p / 2)
      have hg : ContinuousOn g (Set.Icc x y) := by
        dsimp [g]
        apply ContinuousOn.add
        · exact (((continuousOn_const.add continuousOn_id).div_const 2).rpow_const
            (fun t ht => Or.inl (ne_of_gt (by
              change 0 < (y + t) / 2
              linarith [hy_pos, hx_pos, ht.1])))).mul continuousOn_const
        · exact (continuousOn_const.mul
            (((continuousOn_const.sub continuousOn_id).div_const 2).rpow_const
              (fun t ht => Or.inr (by linarith)))).mul continuousOn_const
      refine ContinuousOn.congr hg ?_
      intro t ht
      have ht_upper : t ≤ y := ht.2
      have hsum : 0 < (y + t) / 2 := by linarith [hy_pos, hx_pos, ht.1]
      have hdiff_nonneg : 0 ≤ (y - t) / 2 := by linarith [ht.2]
      by_cases hdiff : 0 < (y - t) / 2
      · have htpos : 0 < y := hy_pos
        simp [g, DyvLeTwo, htpos, abs_of_pos hsum, abs_of_pos hdiff]
      · have hdiff_zero : (y - t) / 2 = 0 := le_antisymm (le_of_not_gt hdiff) hdiff_nonneg
        have ht_eq : t = y := by linarith
        subst t
        have hp_ne : p - 1 ≠ 0 := by linarith
        simp [g, DyvLeTwo, hy_pos, abs_of_pos hy_pos, Real.zero_rpow hp_ne]
    refine antitoneOn_of_hasDerivWithinAt_nonpos
      (D := Set.Icc x y)
      (f := fun t : ℝ => DyvLeTwo p y t)
      (f' := fun t : ℝ => deriv (fun s => DyvLeTwo p y s) t)
      (convex_Icc x y) hcont ?_ ?_
    · intro t ht
      have htI : t ∈ Set.Ioo x y := by
        simpa [interior_Icc] using ht
      have hsum : 0 < (y + t) / 2 := by linarith [hy_pos, hx_pos, htI.1]
      have hdiff : 0 < (y - t) / 2 := by linarith [htI.2]
      exact (differentiableAt_DyvLeTwo_y_of_pos_leTwo p y t hsum hdiff).hasDerivAt.hasDerivWithinAt
    · intro t ht
      have htI : t ∈ Set.Ioo x y := by
        simpa [interior_Icc] using ht
      exact deriv_DyvLeTwo_y_nonpos_leTwo p hp1 hp2 y t
        ⟨hy_pos, lt_trans hx_lower htI.1, htI.2⟩
  exact hanti ⟨le_rfl, hx_upper.le⟩ ⟨hx_upper.le, le_rfl⟩ hx_upper.le

lemma DyvLeTwo_diag_le_DyvLeTwo_Q3_A2_closed_leTwo
    (p : ℝ) (hp1 : 1 < p) (hp2 : p < 2) {x y : ℝ}
    (hy_pos : 0 < y) (hx_lower : a p * y ≤ x) (hx_upper : x < y) :
    DyvLeTwo p y y ≤ DyvLeTwo p y x := by
  have ha_pos : 0 < a p := by
    rw [a_eq_leTwo p hp1 hp2]
    exact div_pos (by linarith) (by linarith)
  have hx_pos : 0 < x := lt_of_lt_of_le (mul_pos ha_pos hy_pos) hx_lower
  have hanti :
      AntitoneOn (fun t : ℝ => DyvLeTwo p y t) (Set.Icc x y) := by
    have hcont : ContinuousOn (fun t : ℝ => DyvLeTwo p y t) (Set.Icc x y) := by
      let g : ℝ → ℝ := fun t =>
        ((y + t) / 2) ^ (p - 1) * (p / 2) +
          coeffLeTwo p * ((y - t) / 2) ^ (p - 1) * (p / 2)
      have hg : ContinuousOn g (Set.Icc x y) := by
        dsimp [g]
        apply ContinuousOn.add
        · exact (((continuousOn_const.add continuousOn_id).div_const 2).rpow_const
            (fun t ht => Or.inl (ne_of_gt (by
              change 0 < (y + t) / 2
              linarith [hy_pos, hx_pos, ht.1])))).mul continuousOn_const
        · exact (continuousOn_const.mul
            (((continuousOn_const.sub continuousOn_id).div_const 2).rpow_const
              (fun t ht => Or.inr (by linarith)))).mul continuousOn_const
      refine ContinuousOn.congr hg ?_
      intro t ht
      have hsum : 0 < (y + t) / 2 := by linarith [hy_pos, hx_pos, ht.1]
      have hdiff_nonneg : 0 ≤ (y - t) / 2 := by linarith [ht.2]
      by_cases hdiff : 0 < (y - t) / 2
      · simp [g, DyvLeTwo, hy_pos, abs_of_pos hsum, abs_of_pos hdiff]
      · have hdiff_zero : (y - t) / 2 = 0 := le_antisymm (le_of_not_gt hdiff) hdiff_nonneg
        have ht_eq : t = y := by linarith
        subst t
        have hp_ne : p - 1 ≠ 0 := by linarith
        simp [g, DyvLeTwo, hy_pos, abs_of_pos hy_pos, Real.zero_rpow hp_ne]
    refine antitoneOn_of_hasDerivWithinAt_nonpos
      (D := Set.Icc x y)
      (f := fun t : ℝ => DyvLeTwo p y t)
      (f' := fun t : ℝ => deriv (fun s => DyvLeTwo p y s) t)
      (convex_Icc x y) hcont ?_ ?_
    · intro t ht
      have htI : t ∈ Set.Ioo x y := by
        simpa [interior_Icc] using ht
      have hsum : 0 < (y + t) / 2 := by linarith [hy_pos, hx_pos, htI.1]
      have hdiff : 0 < (y - t) / 2 := by linarith [htI.2]
      exact (differentiableAt_DyvLeTwo_y_of_pos_leTwo p y t hsum hdiff).hasDerivAt.hasDerivWithinAt
    · intro t ht
      have htI : t ∈ Set.Ioo x y := by
        simpa [interior_Icc] using ht
      exact deriv_DyvLeTwo_y_nonpos_leTwo p hp1 hp2 y t
        ⟨hy_pos, lt_of_le_of_lt hx_lower htI.1, htI.2⟩
  exact hanti ⟨le_rfl, hx_upper.le⟩ ⟨hx_upper.le, le_rfl⟩ hx_upper.le

lemma uCandidate_tangent_x_Q3_A2_to_diag_leTwo
    (p : ℝ) (hp1 : 1 < p) (hp2 : p < 2) {x y : ℝ}
    (hy_pos : 0 < y) (hx_lower : a p * y < x) (hx_upper : x < y) :
    uCandidate p y y ≤
      uCandidate p x y + DxuCandidate p x y * (y - x) := by
  have hQx : QuarterPlane3 x y := ⟨hy_pos.le, by
    have ha_nonneg : 0 ≤ a p := a_nonneg_of_one_lt_of_lt_two p hp1 hp2
    have haxy_nonneg : 0 ≤ a p * y := mul_nonneg ha_nonneg hy_pos.le
    linarith, le_of_lt hx_upper⟩
  have hQy : QuarterPlane3 y y := ⟨hy_pos.le, by linarith, le_rfl⟩
  have hclx : closureA2 p y x := ⟨hy_pos.le, le_of_lt hx_lower, le_of_lt hx_upper⟩
  have hcly : closureA2 p y y := by
    have ha_lt : a p < 1 := a_lt_one_of_one_lt_of_lt_two p hp1 hp2
    exact ⟨hy_pos.le, (mul_le_mul_of_nonneg_right ha_lt.le hy_pos.le).trans_eq (one_mul y), le_rfl⟩
  have hux : uCandidate p x y = vLeTwo p y x := by
    rw [uCandidate_eq_Q3_leTwo p hQx, auxFunction1_eq_vLeTwo_leTwo p hp1 hp2 y x hclx]
  have huy : uCandidate p y y = vLeTwo p y y := by
    rw [uCandidate_eq_Q3_leTwo p hQy, auxFunction1_eq_vLeTwo_leTwo p hp1 hp2 y y hcly]
  have hdx : DxuCandidate p x y = DyvLeTwo p y x := by
    rw [DxuCandidate_eq_Q3_leTwo p hp1 hp2 hQx]
    have hnot : ¬ closureA1 p y x := by
      intro h
      exact not_le_of_gt hx_lower h.2.2
    simp [DyauxFunction1, hnot, hclx]
  have hderiv : HasDerivAt (fun t => vLeTwo p y t) (DyvLeTwo p y x) x := by
    have hsum : 0 < (y + x) / 2 := by
      have ha_nonneg : 0 ≤ a p := a_nonneg_of_one_lt_of_lt_two p hp1 hp2
      have haxy_nonneg : 0 ≤ a p * y := mul_nonneg ha_nonneg hy_pos.le
      linarith
    have hdiff : 0 < (y - x) / 2 := by linarith
    exact hasDerivAt_vLeTwo_y_of_pos_leTwo p y x hsum hdiff
  have hmain :
      vLeTwo p y y ≤ vLeTwo p y x + DyvLeTwo p y x * (y - x) := by
    apply vLeTwo_tangent_y_on_Icc_of_A2_leTwo
        (p := p) (hp1 := hp1) (hp2 := hp2)
        (lo := x) (hi := y) (x := y) (y := x) (z := y)
    · intro t ht
      have htI : t ∈ Set.Ioo x y := by
        simpa [interior_Icc] using ht
      exact ⟨hy_pos, lt_trans hx_lower htI.1, htI.2⟩
    · exact ⟨le_rfl, le_of_lt hx_upper⟩
    · exact ⟨le_of_lt hx_upper, le_rfl⟩
    · exact hderiv
  calc
    uCandidate p y y = vLeTwo p y y := huy
    _ ≤ vLeTwo p y x + DyvLeTwo p y x * (y - x) := hmain
    _ = uCandidate p x y + DxuCandidate p x y * (y - x) := by
      rw [hux, hdx]

lemma uCandidate_tangent_x_Q3_A2_boundary_to_diag_leTwo
    (p : ℝ) (hp1 : 1 < p) (hp2 : p < 2) {y : ℝ}
    (hy_pos : 0 < y) :
    uCandidate p y y ≤
      uCandidate p (a p * y) y +
        DxuCandidate p (a p * y) y * (y - a p * y) := by
  have ha_pos : 0 < a p := by
    rw [a_eq_leTwo p hp1 hp2]
    exact div_pos (by linarith) (by linarith)
  have ha_lt : a p < 1 := a_lt_one_of_one_lt_of_lt_two p hp1 hp2
  have hc_pos : 0 < a p * y := mul_pos ha_pos hy_pos
  have hc_lt_y : a p * y < y := by
    simpa using mul_lt_mul_of_pos_right ha_lt hy_pos
  have hQc : QuarterPlane3 (a p * y) y := ⟨hy_pos.le, by linarith, le_of_lt hc_lt_y⟩
  have hQy : QuarterPlane3 y y := ⟨hy_pos.le, by linarith, le_rfl⟩
  have hclc1 : closureA1 p y (a p * y) := ⟨hy_pos.le, by linarith [hc_pos], le_rfl⟩
  have hclc2 : closureA2 p y (a p * y) := ⟨hy_pos.le, le_rfl, le_of_lt hc_lt_y⟩
  have hcly : closureA2 p y y := by
    exact ⟨hy_pos.le, by
      have h := mul_le_mul_of_nonneg_right ha_lt.le hy_pos.le
      simpa using h, le_rfl⟩
  have huc : uCandidate p (a p * y) y = vLeTwo p y (a p * y) := by
    rw [uCandidate_eq_Q3_leTwo p hQc]
    rw [auxFunction1_eq_vLeTwo_leTwo p hp1 hp2 y (a p * y) hclc2]
  have huy : uCandidate p y y = vLeTwo p y y := by
    rw [uCandidate_eq_Q3_leTwo p hQy, auxFunction1_eq_vLeTwo_leTwo p hp1 hp2 y y hcly]
  have hdc : DxuCandidate p (a p * y) y = DyvLeTwo p y (a p * y) := by
    rw [DxuCandidate_eq_Q3_leTwo p hp1 hp2 hQc]
    have hdyu : DyauxFunction1 p y (a p * y) = DyuA1 p y (a p * y) := by
      simp [DyauxFunction1, hclc1]
    have hglue := DyuA1_eq_DyvLeTwo_on_A1A2_boundary_leTwo
      p y hp1 hp2 hy_pos
    simpa [hdyu] using hglue
  have hderiv : HasDerivAt (fun t => vLeTwo p y t) (DyvLeTwo p y (a p * y)) (a p * y) := by
    have hsum : 0 < (y + a p * y) / 2 := by linarith [hy_pos, hc_pos]
    have hdiff : 0 < (y - a p * y) / 2 := by linarith [hc_lt_y]
    exact hasDerivAt_vLeTwo_y_of_pos_leTwo p y (a p * y) hsum hdiff
  have hmain :
      vLeTwo p y y ≤
        vLeTwo p y (a p * y) + DyvLeTwo p y (a p * y) * (y - a p * y) := by
    apply vLeTwo_tangent_y_on_Icc_of_A2_leTwo
        (p := p) (hp1 := hp1) (hp2 := hp2)
        (lo := a p * y) (hi := y) (x := y) (y := a p * y) (z := y)
    · intro t ht
      have htI : t ∈ Set.Ioo (a p * y) y := by
        simpa [interior_Icc] using ht
      exact ⟨hy_pos, htI.1, htI.2⟩
    · exact ⟨le_rfl, le_of_lt hc_lt_y⟩
    · exact ⟨le_of_lt hc_lt_y, le_rfl⟩
    · exact hderiv
  calc
    uCandidate p y y = vLeTwo p y y := huy
    _ ≤ vLeTwo p y (a p * y) + DyvLeTwo p y (a p * y) * (y - a p * y) := hmain
    _ = uCandidate p (a p * y) y +
        DxuCandidate p (a p * y) y * (y - a p * y) := by
      rw [huc, hdc]

lemma hasDerivAt_vLeTwo_x_on_diag_pos_leTwo (p : ℝ) (hp1 : 1 < p)
    (y : ℝ) (hy : 0 < y) :
    HasDerivAt (fun t => vLeTwo p t y) (DxvLeTwo p y y) y := by
  let g : ℝ → ℝ := fun t =>
    |((t + y) / 2)| ^ p - coeffLeTwo p * |((t - y) / 2)| ^ p
  have hEq : (fun t => vLeTwo p t y) = g := by
    ext t
    simp [vLeTwo, g]
  have hbase_sum :
      HasDerivAt (fun t : ℝ => (t + y) / 2) (1 / 2) y := by
    simpa [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using
      (((hasDerivAt_id y).add_const y).const_mul (1 / 2 : ℝ))
  have hbase_diff :
      HasDerivAt (fun t : ℝ => (t - y) / 2) (1 / 2) y := by
    simpa [sub_eq_add_neg, div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using
      (((hasDerivAt_id y).add_const (-y)).const_mul (1 / 2 : ℝ))
  have hpow_sum :
      HasDerivAt (fun t : ℝ => |((t + y) / 2)| ^ p)
        (p * (y ^ (p - 2) * y) * (1 / 2)) y := by
    have h :
        HasDerivAt (fun s : ℝ => |s| ^ p)
          (p * |(y + y) / 2| ^ (p - 2) * ((y + y) / 2)) ((y + y) / 2) :=
      hasDerivAt_abs_rpow ((y + y) / 2) hp1
    have hcomp := h.comp y hbase_sum
    refine hcomp.congr_deriv ?_
    simp [abs_of_pos hy]
    ring
  have hpow_diff :
      HasDerivAt (fun t : ℝ => |((t - y) / 2)| ^ p) 0 y := by
    have h :
        HasDerivAt (fun s : ℝ => |s| ^ p)
          (p * |(y - y) / 2| ^ (p - 2) * ((y - y) / 2)) ((y - y) / 2) :=
      hasDerivAt_abs_rpow ((y - y) / 2) hp1
    have hcomp := h.comp y hbase_diff
    simpa using hcomp
  have hd :
      HasDerivAt g (p * (y ^ (p - 2) * y) * (1 / 2) - coeffLeTwo p * 0) y := by
    dsimp [g]
    exact hpow_sum.sub (hpow_diff.const_mul (coeffLeTwo p))
  rw [hEq]
  refine hd.congr_deriv ?_
  have hpow : y ^ (p - 2) * y = y ^ (p - 1) := by
    calc
      y ^ (p - 2) * y = y ^ (p - 2) * y ^ (1 : ℝ) := by rw [Real.rpow_one]
      _ = y ^ ((p - 2) + 1) := by rw [← Real.rpow_add hy]
      _ = y ^ (p - 1) := by ring_nf
  have hzero : (0 : ℝ) ^ (p - 1) = 0 := Real.zero_rpow (by linarith)
  simp [DxvLeTwo, hy, abs_of_pos hy, hzero]
  rw [hpow]
  ring

lemma uCandidate_tangent_x_diag_to_Q1_A2_leTwo
    (p : ℝ) (hp1 : 1 < p) (hp2 : p < 2) {z y : ℝ}
    (hy_pos : 0 < y) (hz_lower : y < z) (hz_upper : z < y / a p) :
    uCandidate p z y ≤
      uCandidate p y y + DxuCandidate p y y * (z - y) := by
  have ha_pos : 0 < a p := by
    rw [a_eq_leTwo p hp1 hp2]
    exact div_pos (by linarith) (by linarith)
  have hQy : QuarterPlane y y := ⟨hy_pos.le, le_rfl, by linarith⟩
  have hQz : QuarterPlane z y := ⟨by linarith, le_of_lt hz_lower, by linarith⟩
  have hcly : closureA2 p y y := by
    have ha_lt : a p < 1 := a_lt_one_of_one_lt_of_lt_two p hp1 hp2
    exact ⟨hy_pos.le, by
      have h := mul_le_mul_of_nonneg_right ha_lt.le hy_pos.le
      simpa using h, le_rfl⟩
  have hclz : closureA2 p z y := by
    have haz : a p * z < y := by
      have hmul := mul_lt_mul_of_pos_left hz_upper ha_pos
      field_simp [ha_pos.ne'] at hmul
      simpa [mul_comm, mul_left_comm, mul_assoc] using hmul
    exact ⟨by linarith, le_of_lt haz, le_of_lt hz_lower⟩
  have hnotz : ¬ closureA1 p z y := by
    intro h
    have haz : a p * z < y := by
      have hmul := mul_lt_mul_of_pos_left hz_upper ha_pos
      field_simp [ha_pos.ne'] at hmul
      simpa [mul_comm, mul_left_comm, mul_assoc] using hmul
    exact not_le_of_gt haz h.2.2
  have huy : uCandidate p y y = vLeTwo p y y := by
    rw [uCandidate_eq_Q1_leTwo p hQy, auxFunction1_eq_vLeTwo_leTwo p hp1 hp2 y y hcly]
  have huz : uCandidate p z y = vLeTwo p z y := by
    rw [uCandidate_eq_Q1_leTwo p hQz]
    simp [auxFunction1, hnotz, hclz]
  have hdy : DxuCandidate p y y = DxvLeTwo p y y := by
    rw [DxuCandidate_eq_Q1_leTwo p hQy]
    exact auxFunction1_Dx_eq_DxvLeTwo_leTwo p hp1 hp2 y y hcly
  have hderiv : HasDerivAt (fun t => vLeTwo p t y) (DxvLeTwo p y y) y :=
    hasDerivAt_vLeTwo_x_on_diag_pos_leTwo p hp1 y hy_pos
  have hmain :
      vLeTwo p z y ≤ vLeTwo p y y + DxvLeTwo p y y * (z - y) := by
    apply vLeTwo_tangent_x_on_Icc_of_A2_leTwo
        (p := p) (hp1 := hp1) (hp2 := hp2)
        (lo := y) (hi := z) (y := y) (x := y) (z := z)
    · intro t ht
      have htI : t ∈ Set.Ioo y z := by
        simpa [interior_Icc] using ht
      have ht_pos : 0 < t := by linarith [hy_pos, htI.1]
      have hat : a p * t < y := by
        have hmul : a p * t < a p * (y / a p) := by
          exact mul_lt_mul_of_pos_left (lt_trans htI.2 hz_upper) ha_pos
        have hac : a p * (y / a p) = y := by field_simp [ha_pos.ne']
        simpa [hac] using hmul
      exact ⟨ht_pos, hat, htI.1⟩
    · exact ⟨le_rfl, le_of_lt hz_lower⟩
    · exact ⟨le_of_lt hz_lower, le_rfl⟩
    · exact hderiv
  calc
    uCandidate p z y = vLeTwo p z y := huz
    _ ≤ vLeTwo p y y + DxvLeTwo p y y * (z - y) := hmain
    _ = uCandidate p y y + DxuCandidate p y y * (z - y) := by
      rw [huy, hdy]

lemma uCandidate_tangent_x_cross_Q3_A2_to_Q1_A2_leTwo
    (p : ℝ) (hp1 : 1 < p) (hp2 : p < 2) {x z y : ℝ}
    (hy_pos : 0 < y) (hx_lower : a p * y < x) (hx_upper : x < y)
    (hz_lower : y < z) (hz_upper : z < y / a p) :
    uCandidate p z y ≤
      uCandidate p x y + DxuCandidate p x y * (z - x) := by
  have h_xy := uCandidate_tangent_x_Q3_A2_to_diag_leTwo
    (p := p) (hp1 := hp1) (hp2 := hp2) (x := x) (y := y)
    hy_pos hx_lower hx_upper
  have h_yz := uCandidate_tangent_x_diag_to_Q1_A2_leTwo
    (p := p) (hp1 := hp1) (hp2 := hp2) (z := z) (y := y)
    hy_pos hz_lower hz_upper
  have hd : DxuCandidate p y y ≤ DxuCandidate p x y := by
    have hQx : QuarterPlane3 x y := ⟨hy_pos.le, by
      have ha_nonneg : 0 ≤ a p := a_nonneg_of_one_lt_of_lt_two p hp1 hp2
      have haxy_nonneg : 0 ≤ a p * y := mul_nonneg ha_nonneg hy_pos.le
      linarith, le_of_lt hx_upper⟩
    have hQy : QuarterPlane y y := ⟨hy_pos.le, le_rfl, by linarith⟩
    have hcly : closureA2 p y y := by
      have ha_lt : a p < 1 := a_lt_one_of_one_lt_of_lt_two p hp1 hp2
      exact ⟨hy_pos.le, by
        have h := mul_le_mul_of_nonneg_right ha_lt.le hy_pos.le
        simpa using h, le_rfl⟩
    have hclx : closureA2 p y x := ⟨hy_pos.le, le_of_lt hx_lower, le_of_lt hx_upper⟩
    have hdx : DxuCandidate p x y = DyvLeTwo p y x := by
      rw [DxuCandidate_eq_Q3_leTwo p hp1 hp2 hQx]
      have hnot : ¬ closureA1 p y x := by
        intro h
        exact not_le_of_gt hx_lower h.2.2
      simp [DyauxFunction1, hnot, hclx]
    have hdy : DxuCandidate p y y = DxvLeTwo p y y := by
      rw [DxuCandidate_eq_Q1_leTwo p hQy]
      exact auxFunction1_Dx_eq_DxvLeTwo_leTwo p hp1 hp2 y y hcly
    have hdiag : DxvLeTwo p y y = DyvLeTwo p y y := by
      have hzero : (0 : ℝ) ^ (p - 1) = 0 := Real.zero_rpow (by linarith)
      simp [DxvLeTwo, DyvLeTwo, hy_pos, abs_of_pos hy_pos, hzero]
    have hmono := DyvLeTwo_diag_le_DyvLeTwo_Q3_A2_leTwo
      (p := p) (hp1 := hp1) (hp2 := hp2) (x := x) (y := y)
      hy_pos hx_lower hx_upper
    rw [hdy, hdx, hdiag]
    exact hmono
  exact tangent_glue_two_forward_leTwo_local
    (fun t => uCandidate p t y) (fun t => DxuCandidate p t y)
    (le_of_lt hx_upper) (le_of_lt hz_lower) h_xy h_yz hd

lemma uCandidate_tangent_x_on_Q1_A1_segment_leTwo
    (p : ℝ) (hp1 : 1 < p) (hp2 : p < 2) {x z y : ℝ}
    (hy_pos : 0 < y) (hx_lower : y / a p < x)
    (hz_lower : y / a p < z) :
    uCandidate p z y ≤
      uCandidate p x y + DxuCandidate p x y * (z - x) := by
  have ha_pos : 0 < a p := by
    rw [a_eq_leTwo p hp1 hp2]
    exact div_pos (by linarith) (by linarith)
  have ha_lt : a p < 1 := a_lt_one_of_one_lt_of_lt_two p hp1 hp2
  have hy_div_pos : 0 < y / a p := div_pos hy_pos ha_pos
  have hQx : QuarterPlane x y := ⟨by linarith, by
    have hlt : y < y / a p := by
      rw [div_eq_mul_inv]
      have hinv : 1 < (a p)⁻¹ := by
        rw [one_lt_inv₀ ha_pos]
        exact ha_lt
      nlinarith
    exact le_of_lt (lt_trans hlt hx_lower), by linarith⟩
  have hQz : QuarterPlane z y := ⟨by linarith, by
    have hlt : y < y / a p := by
      rw [div_eq_mul_inv]
      have hinv : 1 < (a p)⁻¹ := by
        rw [one_lt_inv₀ ha_pos]
        exact ha_lt
      nlinarith
    exact le_of_lt (lt_trans hlt hz_lower), by linarith⟩
  have hayx : y < a p * x := by
    have hmul := mul_lt_mul_of_pos_left hx_lower ha_pos
    field_simp [ha_pos.ne'] at hmul
    simpa [mul_comm, mul_left_comm, mul_assoc] using hmul
  have hayz : y < a p * z := by
    have hmul := mul_lt_mul_of_pos_left hz_lower ha_pos
    field_simp [ha_pos.ne'] at hmul
    simpa [mul_comm, mul_left_comm, mul_assoc] using hmul
  have hclx : closureA1 p x y := ⟨hQx.1, hQx.2.2, le_of_lt hayx⟩
  have hclz : closureA1 p z y := ⟨hQz.1, hQz.2.2, le_of_lt hayz⟩
  have hux : uCandidate p x y = uA1 p x y := by
    rw [uCandidate_eq_Q1_leTwo p hQx]
    simp [auxFunction1, hclx]
  have huz : uCandidate p z y = uA1 p z y := by
    rw [uCandidate_eq_Q1_leTwo p hQz]
    simp [auxFunction1, hclz]
  have hdx : DxuCandidate p x y = DxuA1 p x y := by
    rw [DxuCandidate_eq_Q1_leTwo p hQx]
    simp [DxauxFunction1, hclx]
  have hderiv : HasDerivAt (fun t => uA1 p t y) (DxuA1 p x y) x :=
    hasDerivAt_uA1_x_of_pos_leTwo p hp1 hp2 x y (by linarith)
  have hmain : uA1 p z y ≤ uA1 p x y + DxuA1 p x y * (z - x) := by
    apply uA1_tangent_x_on_Icc_leTwo
        (p := p) (hp1 := hp1) (hp2 := hp2)
        (lo := min x z) (hi := max x z) (x := x) (z := z) (y := y)
    · intro t ht
      have hlow : y / a p < min x z := lt_min hx_lower hz_lower
      exact lt_of_lt_of_le (lt_trans hy_div_pos hlow) ht.1
    · intro t ht
      have htI : t ∈ Set.Icc (min x z) (max x z) := interior_subset ht
      have hlow : y / a p < min x z := lt_min hx_lower hz_lower
      have hyt_div : y / a p < t := lt_of_lt_of_le hlow htI.1
      have ht_pos : 0 < t := lt_trans hy_div_pos hyt_div
      linarith
    · exact ⟨min_le_left x z, le_max_left x z⟩
    · exact ⟨min_le_right x z, le_max_right x z⟩
  calc
    uCandidate p z y = uA1 p z y := huz
    _ ≤ uA1 p x y + DxuA1 p x y * (z - x) := hmain
    _ = uCandidate p x y + DxuCandidate p x y * (z - x) := by
      rw [hux, hdx]

lemma tangent_glue_two_forward_leTwo
    (f d : ℝ → ℝ) {x m z : ℝ}
    (_hxm : x ≤ m) (hmz : m ≤ z)
    (hxm_tangent : f m ≤ f x + d x * (m - x))
    (hmz_tangent : f z ≤ f m + d m * (z - m))
    (hd_antitone : d m ≤ d x) :
    f z ≤ f x + d x * (z - x) := by
  have hnonneg : 0 ≤ z - m := by linarith
  have hmul : d m * (z - m) ≤ d x * (z - m) :=
    mul_le_mul_of_nonneg_right hd_antitone hnonneg
  calc
    f z ≤ f m + d m * (z - m) := hmz_tangent
    _ ≤ (f x + d x * (m - x)) + d m * (z - m) := by linarith
    _ ≤ (f x + d x * (m - x)) + d x * (z - m) := by linarith
    _ = f x + d x * (z - x) := by ring

lemma uCandidate_tangent_x_Q1_A2_to_boundary_leTwo
    (p : ℝ) (hp1 : 1 < p) (hp2 : p < 2) {x y : ℝ}
    (hy_pos : 0 < y) (hx_lower : y < x) (hx_upper : x < y / a p) :
    uCandidate p (y / a p) y ≤
      uCandidate p x y + DxuCandidate p x y * (y / a p - x) := by
  have ha_pos : 0 < a p := by
    rw [a_eq_leTwo p hp1 hp2]
    exact div_pos (by linarith) (by linarith)
  have hQx : QuarterPlane x y := ⟨by linarith, le_of_lt hx_lower, by linarith⟩
  have hQb : QuarterPlane (y / a p) y := by
    have hlt : y < y / a p := by
      rw [div_eq_mul_inv]
      have ha_lt : a p < 1 := a_lt_one_of_one_lt_of_lt_two p hp1 hp2
      have hinv : 1 < (a p)⁻¹ := by
        rw [one_lt_inv₀ ha_pos]
        exact ha_lt
      nlinarith
    exact ⟨(div_pos hy_pos ha_pos).le, le_of_lt hlt, by linarith⟩
  have hclx : closureA2 p x y := by
    have hax : a p * x < y := by
      have hmul := mul_lt_mul_of_pos_left hx_upper ha_pos
      field_simp [ha_pos.ne'] at hmul
      simpa [mul_comm, mul_left_comm, mul_assoc] using hmul
    exact ⟨by linarith, le_of_lt hax, le_of_lt hx_lower⟩
  have hboundary := horizontal_boundary_closureA1_closureA2_leTwo p y hp1 hp2 hy_pos
  have hnotx : ¬ closureA1 p x y := by
    intro h
    have hax : a p * x < y := by
      have hmul := mul_lt_mul_of_pos_left hx_upper ha_pos
      field_simp [ha_pos.ne'] at hmul
      simpa [mul_comm, mul_left_comm, mul_assoc] using hmul
    exact not_le_of_gt hax h.2.2
  have hux : uCandidate p x y = vLeTwo p x y := by
    rw [uCandidate_eq_Q1_leTwo p hQx]
    simp [auxFunction1, hnotx, hclx]
  have hub : uCandidate p (y / a p) y = vLeTwo p (y / a p) y := by
    rw [uCandidate_eq_Q1_leTwo p hQb, auxFunction1_eq_vLeTwo_leTwo p hp1 hp2 _ _ hboundary.2]
  have hdx : DxuCandidate p x y = DxvLeTwo p x y := by
    rw [DxuCandidate_eq_Q1_leTwo p hQx]
    simp [DxauxFunction1, hnotx, hclx]
  have hderiv : HasDerivAt (fun t => vLeTwo p t y) (DxvLeTwo p x y) x := by
    have hsum : 0 < (x + y) / 2 := by linarith
    have hdiff : 0 < (x - y) / 2 := by linarith
    exact hasDerivAt_vLeTwo_x_of_pos_leTwo p x y hsum hdiff
  have hmain :
      vLeTwo p (y / a p) y ≤
        vLeTwo p x y + DxvLeTwo p x y * (y / a p - x) := by
    apply vLeTwo_tangent_x_on_Icc_of_A2_leTwo
        (p := p) (hp1 := hp1) (hp2 := hp2)
        (lo := x) (hi := y / a p) (x := x) (z := y / a p) (y := y)
    · intro t ht
      have htI : t ∈ Set.Ioo x (y / a p) := by
        simpa [interior_Icc] using ht
      have ht_pos : 0 < t := by linarith [hy_pos, hx_lower, htI.1]
      have hat : a p * t < y := by
        have hmul : a p * t < a p * (y / a p) :=
          mul_lt_mul_of_pos_left htI.2 ha_pos
        have hac : a p * (y / a p) = y := by field_simp [ha_pos.ne']
        simpa [hac] using hmul
      exact ⟨ht_pos, hat, lt_trans hx_lower htI.1⟩
    · exact ⟨le_rfl, le_of_lt hx_upper⟩
    · exact ⟨le_of_lt hx_upper, le_rfl⟩
    · exact hderiv
  calc
    uCandidate p (y / a p) y = vLeTwo p (y / a p) y := hub
    _ ≤ vLeTwo p x y + DxvLeTwo p x y * (y / a p - x) := hmain
    _ = uCandidate p x y + DxuCandidate p x y * (y / a p - x) := by
      rw [hux, hdx]

lemma uCandidate_tangent_x_Q1_boundary_to_A1_leTwo
    (p : ℝ) (hp1 : 1 < p) (hp2 : p < 2) {z y : ℝ}
    (hy_pos : 0 < y) (hz_lower : y / a p < z) :
    uCandidate p z y ≤
      uCandidate p (y / a p) y +
        DxuCandidate p (y / a p) y * (z - y / a p) := by
  have ha_pos : 0 < a p := by
    rw [a_eq_leTwo p hp1 hp2]
    exact div_pos (by linarith) (by linarith)
  have ha_lt : a p < 1 := a_lt_one_of_one_lt_of_lt_two p hp1 hp2
  have hb_pos : 0 < y / a p := div_pos hy_pos ha_pos
  have hy_lt_b : y < y / a p := by
    rw [div_eq_mul_inv]
    have hinv : 1 < (a p)⁻¹ := by
      rw [one_lt_inv₀ ha_pos]
      exact ha_lt
    nlinarith
  have hQb : QuarterPlane (y / a p) y :=
    ⟨hb_pos.le, le_of_lt hy_lt_b, by linarith⟩
  have hQz : QuarterPlane z y :=
    ⟨by linarith, le_of_lt (lt_trans hy_lt_b hz_lower), by linarith⟩
  have hboundary := horizontal_boundary_closureA1_closureA2_leTwo p y hp1 hp2 hy_pos
  have hclz : closureA1 p z y := by
    have hayz : y < a p * z := by
      have hmul := mul_lt_mul_of_pos_left hz_lower ha_pos
      field_simp [ha_pos.ne'] at hmul
      simpa [mul_comm, mul_left_comm, mul_assoc] using hmul
    exact ⟨hQz.1, hQz.2.2, le_of_lt hayz⟩
  have hub : uCandidate p (y / a p) y = uA1 p (y / a p) y := by
    rw [uCandidate_eq_Q1_leTwo p hQb]
    simp [auxFunction1, hboundary.1]
  have huz : uCandidate p z y = uA1 p z y := by
    rw [uCandidate_eq_Q1_leTwo p hQz]
    simp [auxFunction1, hclz]
  have hdb : DxuCandidate p (y / a p) y = DxuA1 p (y / a p) y := by
    rw [DxuCandidate_eq_Q1_leTwo p hQb]
    simp [DxauxFunction1, hboundary.1]
  have hmain :
      uA1 p z y ≤
        uA1 p (y / a p) y + DxuA1 p (y / a p) y * (z - y / a p) := by
    apply uA1_tangent_x_on_Icc_leTwo
        (p := p) (hp1 := hp1) (hp2 := hp2)
        (lo := y / a p) (hi := z) (x := y / a p) (z := z) (y := y)
    · intro t ht
      exact lt_of_lt_of_le hb_pos ht.1
    · intro t ht
      have htI : t ∈ Set.Ioo (y / a p) z := by
        simpa [interior_Icc] using ht
      linarith [hy_pos, hb_pos, htI.1]
    · exact ⟨le_rfl, le_of_lt hz_lower⟩
    · exact ⟨le_of_lt hz_lower, le_rfl⟩
  calc
    uCandidate p z y = uA1 p z y := huz
    _ ≤ uA1 p (y / a p) y + DxuA1 p (y / a p) y * (z - y / a p) := hmain
    _ = uCandidate p (y / a p) y +
        DxuCandidate p (y / a p) y * (z - y / a p) := by
      rw [hub, hdb]

lemma uCandidate_tangent_x_cross_Q1_A2_to_A1_leTwo
    (p : ℝ) (hp1 : 1 < p) (hp2 : p < 2) {x z y : ℝ}
    (hy_pos : 0 < y) (hx_lower : y < x) (hx_upper : x < y / a p)
    (hz_lower : y / a p < z) :
    uCandidate p z y ≤
      uCandidate p x y + DxuCandidate p x y * (z - x) := by
  have h_xb := uCandidate_tangent_x_Q1_A2_to_boundary_leTwo
    (p := p) (hp1 := hp1) (hp2 := hp2) (x := x) (y := y)
    hy_pos hx_lower hx_upper
  have h_bz := uCandidate_tangent_x_Q1_boundary_to_A1_leTwo
    (p := p) (hp1 := hp1) (hp2 := hp2) (z := z) (y := y)
    hy_pos hz_lower
  have hd : DxuCandidate p (y / a p) y ≤ DxuCandidate p x y := by
    have ha_pos : 0 < a p := by
      rw [a_eq_leTwo p hp1 hp2]
      exact div_pos (by linarith) (by linarith)
    have hQx : QuarterPlane x y := ⟨by linarith, le_of_lt hx_lower, by linarith⟩
    have hQb : QuarterPlane (y / a p) y := by
      have ha_lt : a p < 1 := a_lt_one_of_one_lt_of_lt_two p hp1 hp2
      have hy_lt_b : y < y / a p := by
        rw [div_eq_mul_inv]
        have hinv : 1 < (a p)⁻¹ := by
          rw [one_lt_inv₀ ha_pos]
          exact ha_lt
        nlinarith
      exact ⟨(div_pos hy_pos ha_pos).le, le_of_lt hy_lt_b, by linarith⟩
    have hax : a p * x < y := by
      have hmul := mul_lt_mul_of_pos_left hx_upper ha_pos
      field_simp [ha_pos.ne'] at hmul
      simpa [mul_comm, mul_left_comm, mul_assoc] using hmul
    have hdx := DxauxFunction1_A2_boundary_le_leTwo
      (p := p) (hp1 := hp1) (hp2 := hp2) (x := x) (y := y)
      hy_pos hx_lower hax
    have hcx : DxuCandidate p x y = DxauxFunction1 p x y := by
      rw [DxuCandidate_eq_Q1_leTwo p hQx]
    have hcb : DxuCandidate p (y / a p) y = DxauxFunction1 p (y / a p) y := by
      rw [DxuCandidate_eq_Q1_leTwo p hQb]
    rwa [hcx, hcb]
  exact tangent_glue_two_forward_leTwo
    (fun t => uCandidate p t y) (fun t => DxuCandidate p t y)
    (le_of_lt hx_upper) (le_of_lt hz_lower) h_xb h_bz hd

lemma uCandidate_tangent_x_forward_on_Q1_leTwo
    (p : ℝ) (hp1 : 1 < p) (hp2 : p < 2) {x z y : ℝ}
    (hy_pos : 0 < y) (hyx : y < x) (hxz : x ≤ z) :
    uCandidate p z y ≤
      uCandidate p x y + DxuCandidate p x y * (z - x) := by
  have ha_pos : 0 < a p := by
    rw [a_eq_leTwo p hp1 hp2]
    exact div_pos (by linarith) (by linarith)
  let b : ℝ := y / a p
  by_cases hxb : x < b
  · rcases lt_trichotomy z b with hzb | hzb | hbz
    · exact uCandidate_tangent_x_on_Q1_A2_segment_leTwo
        (p := p) (hp1 := hp1) (hp2 := hp2) (x := x) (z := z) (y := y)
        hy_pos hyx hxb (lt_of_lt_of_le hyx hxz) hzb
    · subst z
      simpa [b] using
        uCandidate_tangent_x_Q1_A2_to_boundary_leTwo
          (p := p) (hp1 := hp1) (hp2 := hp2) (x := x) (y := y)
          hy_pos hyx hxb
    · exact uCandidate_tangent_x_cross_Q1_A2_to_A1_leTwo
        (p := p) (hp1 := hp1) (hp2 := hp2) (x := x) (z := z) (y := y)
        hy_pos hyx hxb hbz
  · have hbx : b ≤ x := le_of_not_gt hxb
    rcases hbx.lt_or_eq with hbx_lt | hbx_eq
    · have hbz : b < z := lt_of_lt_of_le hbx_lt hxz
      exact uCandidate_tangent_x_on_Q1_A1_segment_leTwo
        (p := p) (hp1 := hp1) (hp2 := hp2) (x := x) (z := z) (y := y)
        hy_pos (by simpa [b] using hbx_lt) (by simpa [b] using hbz)
    · subst x
      rcases hxz.lt_or_eq with hxz_lt | rfl
      · exact uCandidate_tangent_x_Q1_boundary_to_A1_leTwo
          (p := p) (hp1 := hp1) (hp2 := hp2) (z := z) (y := y)
          hy_pos (by simpa [b] using hxz_lt)
      · simp

lemma uCandidate_tangent_x_on_Q2_A1_segment_leTwo
    (p : ℝ) (hp1 : 1 < p) (hp2 : p < 2) {x z y : ℝ}
    (hy_pos : 0 < y) (hx_left : x < -y) (hz_left : z < -y) :
    uCandidate p z y ≤
      uCandidate p x y + DxuCandidate p x y * (z - x) := by
  have ha_nonneg : 0 ≤ a p := a_nonneg_of_one_lt_of_lt_two p hp1 hp2
  have hQx : QuarterPlane2 x y := ⟨by linarith, by linarith, by linarith⟩
  have hQz : QuarterPlane2 z y := ⟨by linarith, by linarith, by linarith⟩
  have hclx : closureA1 p (-x) (-y) := by
    refine ⟨by linarith, by linarith, ?_⟩
    have hmul : a p * x ≤ 0 := mul_nonpos_of_nonneg_of_nonpos ha_nonneg (by linarith)
    linarith
  have hclz : closureA1 p (-z) (-y) := by
    refine ⟨by linarith, by linarith, ?_⟩
    have hmul : a p * z ≤ 0 := mul_nonpos_of_nonneg_of_nonpos ha_nonneg (by linarith)
    linarith
  have hux : uCandidate p x y = uA1 p (-x) (-y) := by
    rw [uCandidate_eq_Q2_leTwo p hQx]
    simp [auxFunction1, hclx]
  have huz : uCandidate p z y = uA1 p (-z) (-y) := by
    rw [uCandidate_eq_Q2_leTwo p hQz]
    simp [auxFunction1, hclz]
  have hdx : DxuCandidate p x y = -DxuA1 p (-x) (-y) := by
    rw [DxuCandidate_eq_Q2_leTwo p hQx]
    simp [DxauxFunction1, hclx]
  have hmain :
      uA1 p (-z) (-y) ≤
        uA1 p (-x) (-y) + DxuA1 p (-x) (-y) * ((-z) - (-x)) := by
    apply uA1_tangent_x_on_Icc_leTwo
        (p := p) (hp1 := hp1) (hp2 := hp2)
        (lo := min (-x) (-z)) (hi := max (-x) (-z))
        (x := -x) (z := -z) (y := -y)
    · intro t ht
      have hlow : y < min (-x) (-z) := lt_min (by linarith) (by linarith)
      exact lt_trans hy_pos (lt_of_lt_of_le hlow ht.1)
    · intro t ht
      have htI : t ∈ Set.Icc (min (-x) (-z)) (max (-x) (-z)) := interior_subset ht
      have hlow : y < min (-x) (-z) := lt_min (by linarith) (by linarith)
      have hyt : y < t := lt_of_lt_of_le hlow htI.1
      linarith
    · exact ⟨min_le_left (-x) (-z), le_max_left (-x) (-z)⟩
    · exact ⟨min_le_right (-x) (-z), le_max_right (-x) (-z)⟩
  calc
    uCandidate p z y = uA1 p (-z) (-y) := huz
    _ ≤ uA1 p (-x) (-y) + DxuA1 p (-x) (-y) * ((-z) - (-x)) := hmain
    _ = uCandidate p x y + DxuCandidate p x y * (z - x) := by
      rw [hux, hdx]
      ring

lemma uCandidate_tangent_x_Q2_to_antidiag_leTwo
    (p : ℝ) (hp1 : 1 < p) (hp2 : p < 2) {x y : ℝ}
    (hy_pos : 0 < y) (hx_left : x < -y) :
    uCandidate p (-y) y ≤
      uCandidate p x y + DxuCandidate p x y * ((-y) - x) := by
  have ha_nonneg : 0 ≤ a p := a_nonneg_of_one_lt_of_lt_two p hp1 hp2
  have hQx : QuarterPlane2 x y := ⟨by linarith, by linarith, by linarith⟩
  have hQa : QuarterPlane2 (-y) y := ⟨by linarith, by linarith, by linarith⟩
  have hclx : closureA1 p (-x) (-y) := by
    refine ⟨by linarith, by linarith, ?_⟩
    have hmul : a p * x ≤ 0 := mul_nonpos_of_nonneg_of_nonpos ha_nonneg (by linarith)
    linarith
  have hcla : closureA1 p y (-y) := by
    refine ⟨hy_pos.le, le_rfl, ?_⟩
    have hnonneg : 0 ≤ a p * y := mul_nonneg ha_nonneg hy_pos.le
    linarith
  have hux : uCandidate p x y = uA1 p (-x) (-y) := by
    rw [uCandidate_eq_Q2_leTwo p hQx]
    simp [auxFunction1, hclx]
  have hua : uCandidate p (-y) y = uA1 p y (-y) := by
    rw [uCandidate_eq_Q2_leTwo p hQa]
    simp [auxFunction1, hcla]
  have hdx : DxuCandidate p x y = -DxuA1 p (-x) (-y) := by
    rw [DxuCandidate_eq_Q2_leTwo p hQx]
    simp [DxauxFunction1, hclx]
  have hmain :
      uA1 p y (-y) ≤
        uA1 p (-x) (-y) + DxuA1 p (-x) (-y) * (y - (-x)) := by
    apply uA1_tangent_x_on_Icc_leTwo
        (p := p) (hp1 := hp1) (hp2 := hp2)
        (lo := y) (hi := -x) (x := -x) (z := y) (y := -y)
    · intro t ht
      exact lt_of_lt_of_le hy_pos ht.1
    · intro t ht
      have htI : t ∈ Set.Ioo y (-x) := by
        simpa [interior_Icc] using ht
      linarith [htI.1]
    · exact ⟨le_of_lt (by linarith), le_rfl⟩
    · exact ⟨le_rfl, le_of_lt (by linarith)⟩
  calc
    uCandidate p (-y) y = uA1 p y (-y) := hua
    _ ≤ uA1 p (-x) (-y) + DxuA1 p (-x) (-y) * (y - (-x)) := hmain
    _ = uCandidate p x y + DxuCandidate p x y * ((-y) - x) := by
      rw [hux, hdx]
      ring

lemma uCandidate_tangent_x_antidiag_to_Q3_A1_leTwo
    (p : ℝ) (hp1 : 1 < p) (hp2 : p < 2) {z y : ℝ}
    (hy_pos : 0 < y) (hz_lower : -y < z) (hz_upper : z < a p * y) :
    uCandidate p z y ≤
      uCandidate p (-y) y + DxuCandidate p (-y) y * (z - (-y)) := by
  have ha_nonneg : 0 ≤ a p := a_nonneg_of_one_lt_of_lt_two p hp1 hp2
  have ha_lt : a p < 1 := a_lt_one_of_one_lt_of_lt_two p hp1 hp2
  have hQa : QuarterPlane2 (-y) y := ⟨by linarith, by linarith, by linarith⟩
  have hQz : QuarterPlane3 z y := ⟨hy_pos.le, le_of_lt hz_lower, by
    have hc_lt_y : a p * y < y := by
      simpa using mul_lt_mul_of_pos_right ha_lt hy_pos
    exact le_of_lt (lt_trans hz_upper hc_lt_y)⟩
  have hcla : closureA1 p y (-y) := by
    refine ⟨hy_pos.le, le_rfl, ?_⟩
    have hnonneg : 0 ≤ a p * y := mul_nonneg ha_nonneg hy_pos.le
    linarith
  have hclz : closureA1 p y z := ⟨hy_pos.le, le_of_lt hz_lower, le_of_lt hz_upper⟩
  have hua : uCandidate p (-y) y = uA1 p y (-y) := by
    rw [uCandidate_eq_Q2_leTwo p hQa]
    simp [auxFunction1, hcla]
  have huz : uCandidate p z y = uA1 p y z := by
    rw [uCandidate_eq_Q3_leTwo p hQz]
    simp [auxFunction1, hclz]
  have hda : DxuCandidate p (-y) y = DyuA1 p y (-y) := by
    rw [DxuCandidate_eq_Q2_leTwo p hQa]
    have hrel := DxauxFunction1_eq_neg_DyauxFunction1_on_antidiag_leTwo
      p hp1 hp2 y hy_pos.le
    have hdy : DyauxFunction1 p y (-y) = DyuA1 p y (-y) := by
      simp [DyauxFunction1, hcla]
    simp only [neg_neg]
    rw [hrel, hdy]
    ring
  apply le_of_eq
  calc
    uCandidate p z y = uA1 p y z := huz
    _ = uA1 p y (-y) + DyuA1 p y (-y) * (z - (-y)) :=
      uA1_affine_y_tangent_leTwo p y (-y) z hy_pos
    _ = uCandidate p (-y) y + DxuCandidate p (-y) y * (z - (-y)) := by
      rw [hua, hda]

lemma uCandidate_tangent_x_antidiag_to_Q3_A1_boundary_leTwo
    (p : ℝ) (hp1 : 1 < p) (hp2 : p < 2) {y : ℝ}
    (hy_pos : 0 < y) :
    uCandidate p (a p * y) y ≤
      uCandidate p (-y) y + DxuCandidate p (-y) y * (a p * y - (-y)) := by
  have ha_nonneg : 0 ≤ a p := a_nonneg_of_one_lt_of_lt_two p hp1 hp2
  have ha_lt : a p < 1 := a_lt_one_of_one_lt_of_lt_two p hp1 hp2
  have hQa : QuarterPlane2 (-y) y := ⟨by linarith, by linarith, by linarith⟩
  have hQc : QuarterPlane3 (a p * y) y := ⟨hy_pos.le, by
    have hnonneg : 0 ≤ a p * y := mul_nonneg ha_nonneg hy_pos.le
    linarith, by
      have hc_le_y : a p * y ≤ y := by
        simpa using mul_le_mul_of_nonneg_right ha_lt.le hy_pos.le
      exact hc_le_y⟩
  have hcla : closureA1 p y (-y) := by
    refine ⟨hy_pos.le, le_rfl, ?_⟩
    have hnonneg : 0 ≤ a p * y := mul_nonneg ha_nonneg hy_pos.le
    linarith
  have hclc : closureA1 p y (a p * y) := ⟨hy_pos.le, by
    have hnonneg : 0 ≤ a p * y := mul_nonneg ha_nonneg hy_pos.le
    linarith, le_rfl⟩
  have hua : uCandidate p (-y) y = uA1 p y (-y) := by
    rw [uCandidate_eq_Q2_leTwo p hQa]
    simp [auxFunction1, hcla]
  have huc : uCandidate p (a p * y) y = uA1 p y (a p * y) := by
    rw [uCandidate_eq_Q3_leTwo p hQc]
    simp [auxFunction1, hclc]
  have hda : DxuCandidate p (-y) y = DyuA1 p y (-y) := by
    rw [DxuCandidate_eq_Q2_leTwo p hQa]
    have hrel := DxauxFunction1_eq_neg_DyauxFunction1_on_antidiag_leTwo
      p hp1 hp2 y hy_pos.le
    have hdy : DyauxFunction1 p y (-y) = DyuA1 p y (-y) := by
      simp [DyauxFunction1, hcla]
    simp only [neg_neg]
    rw [hrel, hdy]
    ring
  apply le_of_eq
  calc
    uCandidate p (a p * y) y = uA1 p y (a p * y) := huc
    _ = uA1 p y (-y) + DyuA1 p y (-y) * (a p * y - (-y)) :=
      uA1_affine_y_tangent_leTwo p y (-y) (a p * y) hy_pos
    _ = uCandidate p (-y) y + DxuCandidate p (-y) y * (a p * y - (-y)) := by
      rw [hua, hda]

lemma DxuCandidate_antidiag_le_Q2_leTwo
    (p : ℝ) (hp1 : 1 < p) (hp2 : p < 2) {x y : ℝ}
    (hy_pos : 0 < y) (hx_left : x < -y) :
    DxuCandidate p (-y) y ≤ DxuCandidate p x y := by
  have ha_nonneg : 0 ≤ a p := a_nonneg_of_one_lt_of_lt_two p hp1 hp2
  have hQx : QuarterPlane2 x y := ⟨by linarith, by linarith, by linarith⟩
  have hQa : QuarterPlane2 (-y) y := ⟨by linarith, by linarith, by linarith⟩
  have hclx : closureA1 p (-x) (-y) := by
    refine ⟨by linarith, by linarith, ?_⟩
    have hmul : a p * x ≤ 0 := mul_nonpos_of_nonneg_of_nonpos ha_nonneg (by linarith)
    linarith
  have hcla : closureA1 p y (-y) := by
    refine ⟨hy_pos.le, le_rfl, ?_⟩
    have hnonneg : 0 ≤ a p * y := mul_nonneg ha_nonneg hy_pos.le
    linarith
  have hdx : DxuCandidate p x y = -DxuA1 p (-x) (-y) := by
    rw [DxuCandidate_eq_Q2_leTwo p hQx]
    simp [DxauxFunction1, hclx]
  have hda : DxuCandidate p (-y) y = -DxuA1 p y (-y) := by
    rw [DxuCandidate_eq_Q2_leTwo p hQa]
    simp [DxauxFunction1, hcla]
  have hmono : DxuA1 p (-x) (-y) ≤ DxuA1 p y (-y) := by
    have hanti :
        AntitoneOn (fun t : ℝ => DxuA1Fun p (t, -y)) (Set.Icc y (-x)) := by
      have hcont : ContinuousOn (fun t : ℝ => DxuA1Fun p (t, -y)) (Set.Icc y (-x)) := by
        let g : ℝ → ℝ := fun t =>
          alpha p * (p / 2) * t ^ (p - 2) *
            (((p - 2) / (p - 1)) * t + (-y))
        have hg : ContinuousOn g (Set.Icc y (-x)) := by
          dsimp [g]
          exact ((continuousOn_const.mul continuousOn_const).mul
            (continuousOn_id.rpow_const
              (fun t ht => Or.inl (ne_of_gt (lt_of_lt_of_le hy_pos ht.1))))).mul
            ((continuousOn_const.mul continuousOn_id).add continuousOn_const)
        refine ContinuousOn.congr hg ?_
        intro t ht
        have htpos : 0 < t := lt_of_lt_of_le hy_pos ht.1
        simp [g, DxuA1Fun, DxuA1, htpos]
      refine antitoneOn_of_hasDerivWithinAt_nonpos
        (D := Set.Icc y (-x))
        (f := fun t : ℝ => DxuA1Fun p (t, -y))
        (f' := fun t : ℝ => deriv (fun s => DxuA1Fun p (s, -y)) t)
        (convex_Icc y (-x)) hcont ?_ ?_
      · intro t ht
        have htI : t ∈ Set.Ioo y (-x) := by
          simpa [interior_Icc] using ht
        exact (differentiableAt_DxuA1Fun_x_of_pos_leTwo p t (-y)
          (lt_trans hy_pos htI.1)).hasDerivAt.hasDerivWithinAt
      · intro t ht
        have htI : t ∈ Set.Ioo y (-x) := by
          simpa [interior_Icc] using ht
        exact deriv_DxuA1Fun_x_nonpos_leTwo p hp1 hp2 t (-y)
          (lt_trans hy_pos htI.1) (by linarith [htI.1])
    have hy_mem : y ∈ Set.Icc y (-x) := ⟨le_rfl, le_of_lt (by linarith)⟩
    have hx_mem : -x ∈ Set.Icc y (-x) := ⟨le_of_lt (by linarith), le_rfl⟩
    have hle := hanti hy_mem hx_mem (le_of_lt (by linarith))
    simpa [DxuA1Fun] using hle
  rw [hda, hdx]
  linarith

lemma uCandidate_tangent_x_cross_Q2_to_Q3_A1_leTwo
    (p : ℝ) (hp1 : 1 < p) (hp2 : p < 2) {x z y : ℝ}
    (hy_pos : 0 < y) (hx_left : x < -y)
    (hz_lower : -y < z) (hz_upper : z < a p * y) :
    uCandidate p z y ≤
      uCandidate p x y + DxuCandidate p x y * (z - x) := by
  have hxa := uCandidate_tangent_x_Q2_to_antidiag_leTwo
    (p := p) (hp1 := hp1) (hp2 := hp2) (x := x) (y := y)
    hy_pos hx_left
  have haz := uCandidate_tangent_x_antidiag_to_Q3_A1_leTwo
    (p := p) (hp1 := hp1) (hp2 := hp2) (z := z) (y := y)
    hy_pos hz_lower hz_upper
  have hd := DxuCandidate_antidiag_le_Q2_leTwo
    (p := p) (hp1 := hp1) (hp2 := hp2) (x := x) (y := y)
    hy_pos hx_left
  exact tangent_glue_two_forward_leTwo_local
    (fun t => uCandidate p t y) (fun t => DxuCandidate p t y)
    (le_of_lt hx_left) (le_of_lt hz_lower) hxa haz hd

lemma uCandidate_tangent_x_Q2_to_Q3_A1_boundary_leTwo
    (p : ℝ) (hp1 : 1 < p) (hp2 : p < 2) {x y : ℝ}
    (hy_pos : 0 < y) (hx_left : x < -y) :
    uCandidate p (a p * y) y ≤
      uCandidate p x y + DxuCandidate p x y * (a p * y - x) := by
  have hxa := uCandidate_tangent_x_Q2_to_antidiag_leTwo
    (p := p) (hp1 := hp1) (hp2 := hp2) (x := x) (y := y)
    hy_pos hx_left
  have hac := uCandidate_tangent_x_antidiag_to_Q3_A1_boundary_leTwo
    (p := p) (hp1 := hp1) (hp2 := hp2) (y := y) hy_pos
  have hd := DxuCandidate_antidiag_le_Q2_leTwo
    (p := p) (hp1 := hp1) (hp2 := hp2) (x := x) (y := y)
    hy_pos hx_left
  exact tangent_glue_two_forward_leTwo_local
    (fun t => uCandidate p t y) (fun t => DxuCandidate p t y)
    (le_of_lt hx_left) (by
      have ha_nonneg : 0 ≤ a p := a_nonneg_of_one_lt_of_lt_two p hp1 hp2
      have hnonneg : 0 ≤ a p * y := mul_nonneg ha_nonneg hy_pos.le
      linarith) hxa hac hd

lemma DxuCandidate_Q3_A1_boundary_le_Q2_leTwo
    (p : ℝ) (hp1 : 1 < p) (hp2 : p < 2) {x y : ℝ}
    (hy_pos : 0 < y) (hx_left : x < -y) :
    DxuCandidate p (a p * y) y ≤ DxuCandidate p x y := by
  have ha_nonneg : 0 ≤ a p := a_nonneg_of_one_lt_of_lt_two p hp1 hp2
  have ha_lt : a p < 1 := a_lt_one_of_one_lt_of_lt_two p hp1 hp2
  have hQc : QuarterPlane3 (a p * y) y := ⟨hy_pos.le, by
    have hnonneg : 0 ≤ a p * y := mul_nonneg ha_nonneg hy_pos.le
    linarith, by
      have hc_le_y : a p * y ≤ y := by
        simpa using mul_le_mul_of_nonneg_right ha_lt.le hy_pos.le
      exact hc_le_y⟩
  have hclc : closureA1 p y (a p * y) := ⟨hy_pos.le, by
    have hnonneg : 0 ≤ a p * y := mul_nonneg ha_nonneg hy_pos.le
    linarith, le_rfl⟩
  have hdc : DxuCandidate p (a p * y) y = DyuA1 p y (a p * y) := by
    rw [DxuCandidate_eq_Q3_leTwo p hp1 hp2 hQc]
    simp [DyauxFunction1, hclc]
  have hda : DxuCandidate p (-y) y = DyuA1 p y (-y) := by
    have hQa : QuarterPlane2 (-y) y := ⟨by linarith, by linarith, by linarith⟩
    have hcla : closureA1 p y (-y) := by
      refine ⟨hy_pos.le, le_rfl, ?_⟩
      have hnonneg : 0 ≤ a p * y := mul_nonneg ha_nonneg hy_pos.le
      linarith
    rw [DxuCandidate_eq_Q2_leTwo p hQa]
    have hrel := DxauxFunction1_eq_neg_DyauxFunction1_on_antidiag_leTwo
      p hp1 hp2 y hy_pos.le
    have hdy : DyauxFunction1 p y (-y) = DyuA1 p y (-y) := by
      simp [DyauxFunction1, hcla]
    simp only [neg_neg]
    rw [hrel, hdy]
    ring
  have heq : DxuCandidate p (a p * y) y = DxuCandidate p (-y) y := by
    rw [hdc, hda]
    simp [DyuA1, hy_pos]
  rw [heq]
  exact DxuCandidate_antidiag_le_Q2_leTwo
    (p := p) (hp1 := hp1) (hp2 := hp2) (x := x) (y := y)
    hy_pos hx_left

lemma DxuCandidate_Q3_A1_boundary_eq_antidiag_leTwo
    (p : ℝ) (hp1 : 1 < p) (hp2 : p < 2) {y : ℝ}
    (hy_pos : 0 < y) :
    DxuCandidate p (a p * y) y = DxuCandidate p (-y) y := by
  have ha_nonneg : 0 ≤ a p := a_nonneg_of_one_lt_of_lt_two p hp1 hp2
  have ha_lt : a p < 1 := a_lt_one_of_one_lt_of_lt_two p hp1 hp2
  have hQc : QuarterPlane3 (a p * y) y := ⟨hy_pos.le, by
    have hnonneg : 0 ≤ a p * y := mul_nonneg ha_nonneg hy_pos.le
    linarith, by
      have hc_le_y : a p * y ≤ y := by
        simpa using mul_le_mul_of_nonneg_right ha_lt.le hy_pos.le
      exact hc_le_y⟩
  have hclc : closureA1 p y (a p * y) := ⟨hy_pos.le, by
    have hnonneg : 0 ≤ a p * y := mul_nonneg ha_nonneg hy_pos.le
    linarith, le_rfl⟩
  have hdc : DxuCandidate p (a p * y) y = DyuA1 p y (a p * y) := by
    rw [DxuCandidate_eq_Q3_leTwo p hp1 hp2 hQc]
    simp [DyauxFunction1, hclc]
  have hda : DxuCandidate p (-y) y = DyuA1 p y (-y) := by
    have hQa : QuarterPlane2 (-y) y := ⟨by linarith, by linarith, by linarith⟩
    have hcla : closureA1 p y (-y) := by
      refine ⟨hy_pos.le, le_rfl, ?_⟩
      have hnonneg : 0 ≤ a p * y := mul_nonneg ha_nonneg hy_pos.le
      linarith
    rw [DxuCandidate_eq_Q2_leTwo p hQa]
    have hrel := DxauxFunction1_eq_neg_DyauxFunction1_on_antidiag_leTwo
      p hp1 hp2 y hy_pos.le
    have hdy : DyauxFunction1 p y (-y) = DyuA1 p y (-y) := by
      simp [DyauxFunction1, hcla]
    simp only [neg_neg]
    rw [hrel, hdy]
    ring
  rw [hdc, hda]
  simp [DyuA1, hy_pos]

lemma DxuCandidate_Q3_A1_boundary_le_antidiag_leTwo
    (p : ℝ) (hp1 : 1 < p) (hp2 : p < 2) {y : ℝ}
    (hy_pos : 0 < y) :
    DxuCandidate p (a p * y) y ≤ DxuCandidate p (-y) y := by
  rw [DxuCandidate_Q3_A1_boundary_eq_antidiag_leTwo
    (p := p) (hp1 := hp1) (hp2 := hp2) (y := y) hy_pos]

lemma uCandidate_tangent_x_antidiag_to_Q3_A2_leTwo
    (p : ℝ) (hp1 : 1 < p) (hp2 : p < 2) {z y : ℝ}
    (hy_pos : 0 < y) (hz_lower : a p * y < z) (hz_upper : z < y) :
    uCandidate p z y ≤
      uCandidate p (-y) y + DxuCandidate p (-y) y * (z - (-y)) := by
  have hac := uCandidate_tangent_x_antidiag_to_Q3_A1_boundary_leTwo
    (p := p) (hp1 := hp1) (hp2 := hp2) (y := y) hy_pos
  have hcz := uCandidate_tangent_x_Q3_A2_boundary_to_A2_leTwo
    (p := p) (hp1 := hp1) (hp2 := hp2) (z := z) (y := y)
    hy_pos hz_lower hz_upper
  have hd := DxuCandidate_Q3_A1_boundary_le_antidiag_leTwo
    (p := p) (hp1 := hp1) (hp2 := hp2) (y := y) hy_pos
  exact tangent_glue_two_forward_leTwo_local
    (fun t => uCandidate p t y) (fun t => DxuCandidate p t y)
    (by
      have ha_nonneg : 0 ≤ a p := a_nonneg_of_one_lt_of_lt_two p hp1 hp2
      have hnonneg : 0 ≤ a p * y := mul_nonneg ha_nonneg hy_pos.le
      linarith) (le_of_lt hz_lower) hac hcz hd

lemma uCandidate_tangent_x_antidiag_to_diag_leTwo
    (p : ℝ) (hp1 : 1 < p) (hp2 : p < 2) {y : ℝ}
    (hy_pos : 0 < y) :
    uCandidate p y y ≤
      uCandidate p (-y) y + DxuCandidate p (-y) y * (y - (-y)) := by
  have hac := uCandidate_tangent_x_antidiag_to_Q3_A1_boundary_leTwo
    (p := p) (hp1 := hp1) (hp2 := hp2) (y := y) hy_pos
  have hcy := uCandidate_tangent_x_Q3_A2_boundary_to_diag_leTwo
    (p := p) (hp1 := hp1) (hp2 := hp2) (y := y) hy_pos
  have hd := DxuCandidate_Q3_A1_boundary_le_antidiag_leTwo
    (p := p) (hp1 := hp1) (hp2 := hp2) (y := y) hy_pos
  exact tangent_glue_two_forward_leTwo_local
    (fun t => uCandidate p t y) (fun t => DxuCandidate p t y)
    (by
      have ha_nonneg : 0 ≤ a p := a_nonneg_of_one_lt_of_lt_two p hp1 hp2
      have hnonneg : 0 ≤ a p * y := mul_nonneg ha_nonneg hy_pos.le
      linarith) (by
      have ha_lt : a p < 1 := a_lt_one_of_one_lt_of_lt_two p hp1 hp2
      have hlt : a p * y < y := by
        simpa using mul_lt_mul_of_pos_right ha_lt hy_pos
      exact le_of_lt hlt) hac hcy hd

lemma uCandidate_tangent_x_cross_Q2_to_Q3_A2_leTwo
    (p : ℝ) (hp1 : 1 < p) (hp2 : p < 2) {x z y : ℝ}
    (hy_pos : 0 < y) (hx_left : x < -y)
    (hz_lower : a p * y < z) (hz_upper : z < y) :
    uCandidate p z y ≤
      uCandidate p x y + DxuCandidate p x y * (z - x) := by
  have hxc := uCandidate_tangent_x_Q2_to_Q3_A1_boundary_leTwo
    (p := p) (hp1 := hp1) (hp2 := hp2) (x := x) (y := y)
    hy_pos hx_left
  have hcz := uCandidate_tangent_x_Q3_A2_boundary_to_A2_leTwo
    (p := p) (hp1 := hp1) (hp2 := hp2) (z := z) (y := y)
    hy_pos hz_lower hz_upper
  have hd := DxuCandidate_Q3_A1_boundary_le_Q2_leTwo
    (p := p) (hp1 := hp1) (hp2 := hp2) (x := x) (y := y)
    hy_pos hx_left
  exact tangent_glue_two_forward_leTwo_local
    (fun t => uCandidate p t y) (fun t => DxuCandidate p t y)
    (by
      have ha_nonneg : 0 ≤ a p := a_nonneg_of_one_lt_of_lt_two p hp1 hp2
      have hnonneg : 0 ≤ a p * y := mul_nonneg ha_nonneg hy_pos.le
      linarith) (le_of_lt hz_lower) hxc hcz hd

lemma uCandidate_tangent_x_Q2_to_diag_leTwo
    (p : ℝ) (hp1 : 1 < p) (hp2 : p < 2) {x y : ℝ}
    (hy_pos : 0 < y) (hx_left : x < -y) :
    uCandidate p y y ≤
      uCandidate p x y + DxuCandidate p x y * (y - x) := by
  have hxc := uCandidate_tangent_x_Q2_to_Q3_A1_boundary_leTwo
    (p := p) (hp1 := hp1) (hp2 := hp2) (x := x) (y := y)
    hy_pos hx_left
  have hcy := uCandidate_tangent_x_Q3_A2_boundary_to_diag_leTwo
    (p := p) (hp1 := hp1) (hp2 := hp2) (y := y) hy_pos
  have hd := DxuCandidate_Q3_A1_boundary_le_Q2_leTwo
    (p := p) (hp1 := hp1) (hp2 := hp2) (x := x) (y := y)
    hy_pos hx_left
  exact tangent_glue_two_forward_leTwo_local
    (fun t => uCandidate p t y) (fun t => DxuCandidate p t y)
    (by
      have ha_nonneg : 0 ≤ a p := a_nonneg_of_one_lt_of_lt_two p hp1 hp2
      have hnonneg : 0 ≤ a p * y := mul_nonneg ha_nonneg hy_pos.le
      linarith) (by
      have ha_lt : a p < 1 := a_lt_one_of_one_lt_of_lt_two p hp1 hp2
      have hlt : a p * y < y := by
        simpa using mul_lt_mul_of_pos_right ha_lt hy_pos
      exact le_of_lt hlt) hxc hcy hd

lemma DxuCandidate_diag_le_Q2_leTwo
    (p : ℝ) (hp1 : 1 < p) (hp2 : p < 2) {x y : ℝ}
    (hy_pos : 0 < y) (hx_left : x < -y) :
    DxuCandidate p y y ≤ DxuCandidate p x y := by
  have ha_nonneg : 0 ≤ a p := a_nonneg_of_one_lt_of_lt_two p hp1 hp2
  have ha_lt : a p < 1 := a_lt_one_of_one_lt_of_lt_two p hp1 hp2
  have hc_lt_y : a p * y < y := by
    simpa using mul_lt_mul_of_pos_right ha_lt hy_pos
  have hdiag_a2 :
      DxuCandidate p y y ≤ DxuCandidate p (a p * y) y := by
    have hQd : QuarterPlane y y := ⟨hy_pos.le, le_rfl, by linarith⟩
    have hQc : QuarterPlane3 (a p * y) y := ⟨hy_pos.le, by
      have hnonneg : 0 ≤ a p * y := mul_nonneg ha_nonneg hy_pos.le
      linarith, le_of_lt hc_lt_y⟩
    have hcld : closureA2 p y y := by
      refine ⟨hy_pos.le, ?_, le_rfl⟩
      have hle : a p * y ≤ y := le_of_lt hc_lt_y
      exact hle
    have hclc : closureA2 p y (a p * y) := ⟨hy_pos.le, le_rfl, le_of_lt hc_lt_y⟩
    have hnotd : ¬ closureA1 p y y := by
      intro h
      exact not_le_of_gt hc_lt_y h.2.2
    have hdd : DxuCandidate p y y = DxvLeTwo p y y := by
      rw [DxuCandidate_eq_Q1_leTwo p hQd]
      simp [DxauxFunction1, hnotd, hcld]
    have hclc1 : closureA1 p y (a p * y) := ⟨hy_pos.le, by
      have hnonneg : 0 ≤ a p * y := mul_nonneg ha_nonneg hy_pos.le
      linarith, le_rfl⟩
    have hdc : DxuCandidate p (a p * y) y = DyuA1 p y (a p * y) := by
      rw [DxuCandidate_eq_Q3_leTwo p hp1 hp2 hQc]
      simp [DyauxFunction1, hclc1]
    have hglue : DyuA1 p y (a p * y) = DyvLeTwo p y (a p * y) :=
      DyuA1_eq_DyvLeTwo_on_A1A2_boundary_leTwo p y hp1 hp2 hy_pos
    have hrel := DxauxFunction1_eq_DyauxFunction1_on_diag_leTwo
      p hp1 hp2 y hy_pos.le
    have hdy : DyauxFunction1 p y y = DyvLeTwo p y y := by
      simp [DyauxFunction1, hnotd, hcld]
    have hdx : DxvLeTwo p y y = DyvLeTwo p y y := by
      have hdx' : DxauxFunction1 p y y = DxvLeTwo p y y := by
        simp [DxauxFunction1, hnotd, hcld]
      rw [← hdx', hrel, hdy]
    have hmono := DyvLeTwo_diag_le_DyvLeTwo_Q3_A2_closed_leTwo
      (p := p) (hp1 := hp1) (hp2 := hp2) (x := a p * y) (y := y)
      hy_pos le_rfl hc_lt_y
    calc
      DxuCandidate p y y = DxvLeTwo p y y := hdd
      _ = DyvLeTwo p y y := hdx
      _ ≤ DyvLeTwo p y (a p * y) := hmono
      _ = DyuA1 p y (a p * y) := hglue.symm
      _ = DxuCandidate p (a p * y) y := hdc.symm
  exact le_trans hdiag_a2
    (DxuCandidate_Q3_A1_boundary_le_Q2_leTwo
      (p := p) (hp1 := hp1) (hp2 := hp2) (x := x) (y := y)
      hy_pos hx_left)

lemma uCandidate_tangent_x_cross_Q2_to_Q1_A2_leTwo
    (p : ℝ) (hp1 : 1 < p) (hp2 : p < 2) {x z y : ℝ}
    (hy_pos : 0 < y) (hx_left : x < -y)
    (hz_lower : y < z) (hz_upper : z < y / a p) :
    uCandidate p z y ≤
      uCandidate p x y + DxuCandidate p x y * (z - x) := by
  have hxy := uCandidate_tangent_x_Q2_to_diag_leTwo
    (p := p) (hp1 := hp1) (hp2 := hp2) (x := x) (y := y)
    hy_pos hx_left
  have hyz := uCandidate_tangent_x_diag_to_Q1_A2_leTwo
    (p := p) (hp1 := hp1) (hp2 := hp2) (z := z) (y := y)
    hy_pos hz_lower hz_upper
  have hd := DxuCandidate_diag_le_Q2_leTwo
    (p := p) (hp1 := hp1) (hp2 := hp2) (x := x) (y := y)
    hy_pos hx_left
  exact tangent_glue_two_forward_leTwo_local
    (fun t => uCandidate p t y) (fun t => DxuCandidate p t y)
    (by linarith) (le_of_lt hz_lower) hxy hyz hd

lemma DxuCandidate_Q1_boundary_le_diag_leTwo
    (p : ℝ) (hp1 : 1 < p) (hp2 : p < 2) {y : ℝ}
    (hy_pos : 0 < y) :
    DxuCandidate p (y / a p) y ≤ DxuCandidate p y y := by
  have ha_pos : 0 < a p := by
    rw [a_eq_leTwo p hp1 hp2]
    exact div_pos (by linarith) (by linarith)
  have ha_lt : a p < 1 := a_lt_one_of_one_lt_of_lt_two p hp1 hp2
  let b : ℝ := y / a p
  have hb_pos : 0 < b := by
    dsimp [b]
    exact div_pos hy_pos ha_pos
  have hab : a p * b = y := by
    dsimp [b]
    field_simp [ha_pos.ne']
  have hy_lt_b : y < b := by
    dsimp [b]
    rw [div_eq_mul_inv]
    have hinv : 1 < (a p)⁻¹ := by
      rw [one_lt_inv₀ ha_pos]
      exact ha_lt
    nlinarith
  have hQd : QuarterPlane y y := ⟨hy_pos.le, le_rfl, by linarith⟩
  have hQb : QuarterPlane b y := ⟨hb_pos.le, le_of_lt hy_lt_b, by linarith⟩
  have hcld : closureA2 p y y := by
    refine ⟨hy_pos.le, ?_, le_rfl⟩
    have hle : a p * y ≤ y := by
      exact (mul_le_mul_of_nonneg_right ha_lt.le hy_pos.le).trans_eq (one_mul y)
    exact hle
  have hnotd : ¬ closureA1 p y y := by
    intro h
    have hlt : a p * y < y := by
      simpa using mul_lt_mul_of_pos_right ha_lt hy_pos
    exact not_le_of_gt hlt h.2.2
  have hboundary := horizontal_boundary_closureA1_closureA2_leTwo p y hp1 hp2 hy_pos
  have hdd : DxuCandidate p y y = DxvLeTwo p y y := by
    rw [DxuCandidate_eq_Q1_leTwo p hQd]
    simp [DxauxFunction1, hnotd, hcld]
  have hb1 : closureA1 p b y := by
    simpa [b] using hboundary.1
  have hdb : DxuCandidate p b y = DxuA1 p b y := by
    rw [DxuCandidate_eq_Q1_leTwo p hQb]
    simp [DxauxFunction1, hb1]
  have hglue : DxuA1 p b y = DxvLeTwo p b y := by
    dsimp [b]
    simpa [hab] using DxuA1_eq_DxvLeTwo_on_A1A2_boundary_leTwo
      p b hp1 hp2 hb_pos
  have hanti :
      AntitoneOn (fun t : ℝ => DxvLeTwo p t y) (Set.Icc y b) := by
    have hcont : ContinuousOn (fun t : ℝ => DxvLeTwo p t y) (Set.Icc y b) := by
      let g : ℝ → ℝ := fun t =>
        ((t + y) / 2) ^ (p - 1) * (p / 2) -
          coeffLeTwo p * ((t - y) / 2) ^ (p - 1) * (p / 2)
      have hg : ContinuousOn g (Set.Icc y b) := by
        dsimp [g]
        apply ContinuousOn.sub
        · exact (((continuousOn_id.add continuousOn_const).div_const 2).rpow_const
            (fun t ht => Or.inl (ne_of_gt (by
              change 0 < (t + y) / 2
              linarith [hy_pos, ht.1])))).mul continuousOn_const
        · exact (continuousOn_const.mul
            (((continuousOn_id.sub continuousOn_const).div_const 2).rpow_const
              (fun _ _ => Or.inr (by linarith)))).mul continuousOn_const
      refine ContinuousOn.congr hg ?_
      intro t ht
      have ht_pos : 0 < t := lt_of_lt_of_le hy_pos ht.1
      have hsum : 0 < (t + y) / 2 := by linarith [ht_pos, hy_pos]
      have hdiff_nonneg : 0 ≤ (t - y) / 2 := by linarith [ht.1]
      by_cases hdiff : 0 < (t - y) / 2
      · simp [g, DxvLeTwo, ht_pos, abs_of_pos hsum, abs_of_pos hdiff]
      · have hdiff_zero : (t - y) / 2 = 0 :=
          le_antisymm (le_of_not_gt hdiff) hdiff_nonneg
        have ht_eq : t = y := by linarith
        subst t
        have hp_ne : p - 1 ≠ 0 := by linarith
        simp [g, DxvLeTwo, hy_pos, abs_of_pos hy_pos, Real.zero_rpow hp_ne]
    refine antitoneOn_of_hasDerivWithinAt_nonpos
      (D := Set.Icc y b)
      (f := fun t : ℝ => DxvLeTwo p t y)
      (f' := fun t : ℝ => deriv (fun s => DxvLeTwo p s y) t)
      (convex_Icc y b) hcont ?_ ?_
    · intro t ht
      have htI : t ∈ Set.Ioo y b := by
        simpa [interior_Icc] using ht
      have hsum : 0 < (t + y) / 2 := by linarith [hy_pos, htI.1]
      have hdiff : 0 < (t - y) / 2 := by linarith [htI.1]
      exact (differentiableAt_DxvLeTwo_x_of_pos_leTwo p t y hsum hdiff).hasDerivAt.hasDerivWithinAt
    · intro t ht
      have htI : t ∈ Set.Ioo y b := by
        simpa [interior_Icc] using ht
      have h_at : a p * t < y := by
        have hmul : a p * t < a p * b := mul_lt_mul_of_pos_left htI.2 ha_pos
        simpa [hab] using hmul
      exact deriv_DxvLeTwo_x_nonpos_leTwo p hp1 hp2 t y
        ⟨lt_trans hy_pos htI.1, h_at, htI.1⟩
  have hle : DxvLeTwo p b y ≤ DxvLeTwo p y y :=
    hanti ⟨le_rfl, hy_lt_b.le⟩ ⟨hy_lt_b.le, le_rfl⟩ hy_lt_b.le
  calc
    DxuCandidate p (y / a p) y = DxuCandidate p b y := by rfl
    _ = DxuA1 p b y := hdb
    _ = DxvLeTwo p b y := hglue
    _ ≤ DxvLeTwo p y y := hle
    _ = DxuCandidate p y y := hdd.symm

lemma DxuCandidate_Q1_boundary_le_Q2_leTwo
    (p : ℝ) (hp1 : 1 < p) (hp2 : p < 2) {x y : ℝ}
    (hy_pos : 0 < y) (hx_left : x < -y) :
    DxuCandidate p (y / a p) y ≤ DxuCandidate p x y :=
  le_trans
    (DxuCandidate_Q1_boundary_le_diag_leTwo
      (p := p) (hp1 := hp1) (hp2 := hp2) (y := y) hy_pos)
    (DxuCandidate_diag_le_Q2_leTwo
      (p := p) (hp1 := hp1) (hp2 := hp2) (x := x) (y := y)
      hy_pos hx_left)

lemma uCandidate_tangent_x_diag_to_Q1_boundary_leTwo
    (p : ℝ) (hp1 : 1 < p) (hp2 : p < 2) {y : ℝ}
    (hy_pos : 0 < y) :
    uCandidate p (y / a p) y ≤
      uCandidate p y y + DxuCandidate p y y * (y / a p - y) := by
  have ha_pos : 0 < a p := by
    rw [a_eq_leTwo p hp1 hp2]
    exact div_pos (by linarith) (by linarith)
  have ha_lt : a p < 1 := a_lt_one_of_one_lt_of_lt_two p hp1 hp2
  have hy_lt_b : y < y / a p := by
    rw [div_eq_mul_inv]
    have hinv : 1 < (a p)⁻¹ := by
      rw [one_lt_inv₀ ha_pos]
      exact ha_lt
    nlinarith
  have hQy : QuarterPlane y y := ⟨hy_pos.le, le_rfl, by linarith⟩
  have hQb : QuarterPlane (y / a p) y :=
    ⟨(div_pos hy_pos ha_pos).le, le_of_lt hy_lt_b, by linarith⟩
  have hcl_y : closureA2 p y y := by
    refine ⟨hy_pos.le, ?_, le_rfl⟩
    exact (mul_le_mul_of_nonneg_right ha_lt.le hy_pos.le).trans_eq (one_mul y)
  have hnot_y : ¬ closureA1 p y y := by
    intro h
    have hlt : a p * y < y := by
      simpa using mul_lt_mul_of_pos_right ha_lt hy_pos
    exact not_le_of_gt hlt h.2.2
  have hboundary := horizontal_boundary_closureA1_closureA2_leTwo p y hp1 hp2 hy_pos
  have huy : uCandidate p y y = vLeTwo p y y := by
    rw [uCandidate_eq_Q1_leTwo p hQy]
    simp [auxFunction1, hnot_y, hcl_y]
  have hub : uCandidate p (y / a p) y = vLeTwo p (y / a p) y := by
    rw [uCandidate_eq_Q1_leTwo p hQb,
      auxFunction1_eq_vLeTwo_leTwo p hp1 hp2 (y / a p) y hboundary.2]
  have hdy : DxuCandidate p y y = DxvLeTwo p y y := by
    rw [DxuCandidate_eq_Q1_leTwo p hQy]
    simp [DxauxFunction1, hnot_y, hcl_y]
  have hderiv := hasDerivAt_vLeTwo_x_on_diag_pos_leTwo p hp1 y hy_pos
  have hmain :
      vLeTwo p (y / a p) y ≤
        vLeTwo p y y + DxvLeTwo p y y * (y / a p - y) := by
    apply vLeTwo_tangent_x_on_Icc_of_A2_leTwo
        (p := p) (hp1 := hp1) (hp2 := hp2)
        (lo := y) (hi := y / a p) (x := y) (z := y / a p) (y := y)
    · intro t ht
      have htI : t ∈ Set.Ioo y (y / a p) := by
        simpa [interior_Icc] using ht
      have hat : a p * t < y := by
        have hmul : a p * t < a p * (y / a p) :=
          mul_lt_mul_of_pos_left htI.2 ha_pos
        have hac : a p * (y / a p) = y := by field_simp [ha_pos.ne']
        simpa [hac] using hmul
      exact ⟨lt_trans hy_pos htI.1, hat, htI.1⟩
    · exact ⟨le_rfl, le_of_lt hy_lt_b⟩
    · exact ⟨le_of_lt hy_lt_b, le_rfl⟩
    · exact hderiv
  calc
    uCandidate p (y / a p) y = vLeTwo p (y / a p) y := hub
    _ ≤ vLeTwo p y y + DxvLeTwo p y y * (y / a p - y) := hmain
    _ = uCandidate p y y + DxuCandidate p y y * (y / a p - y) := by
      rw [huy, hdy]

lemma uCandidate_tangent_x_Q2_to_Q1_boundary_leTwo
    (p : ℝ) (hp1 : 1 < p) (hp2 : p < 2) {x y : ℝ}
    (hy_pos : 0 < y) (hx_left : x < -y) :
    uCandidate p (y / a p) y ≤
      uCandidate p x y + DxuCandidate p x y * (y / a p - x) := by
  have ha_pos : 0 < a p := by
    rw [a_eq_leTwo p hp1 hp2]
    exact div_pos (by linarith) (by linarith)
  have ha_lt : a p < 1 := a_lt_one_of_one_lt_of_lt_two p hp1 hp2
  have hy_lt_b : y < y / a p := by
    rw [div_eq_mul_inv]
    have hinv : 1 < (a p)⁻¹ := by
      rw [one_lt_inv₀ ha_pos]
      exact ha_lt
    nlinarith
  have hxy := uCandidate_tangent_x_Q2_to_diag_leTwo
    (p := p) (hp1 := hp1) (hp2 := hp2) (x := x) (y := y)
    hy_pos hx_left
  have hyb := uCandidate_tangent_x_diag_to_Q1_boundary_leTwo
    (p := p) (hp1 := hp1) (hp2 := hp2) (y := y) hy_pos
  have hd := DxuCandidate_diag_le_Q2_leTwo
    (p := p) (hp1 := hp1) (hp2 := hp2) (x := x) (y := y)
    hy_pos hx_left
  exact tangent_glue_two_forward_leTwo_local
    (fun t => uCandidate p t y) (fun t => DxuCandidate p t y)
    (by linarith) (le_of_lt hy_lt_b) hxy hyb hd

lemma uCandidate_tangent_x_cross_Q2_to_Q1_A1_leTwo
    (p : ℝ) (hp1 : 1 < p) (hp2 : p < 2) {x z y : ℝ}
    (hy_pos : 0 < y) (hx_left : x < -y)
    (hz_lower : y / a p < z) :
    uCandidate p z y ≤
      uCandidate p x y + DxuCandidate p x y * (z - x) := by
  have hxb := uCandidate_tangent_x_Q2_to_Q1_boundary_leTwo
    (p := p) (hp1 := hp1) (hp2 := hp2) (x := x) (y := y)
    hy_pos hx_left
  have hbz := uCandidate_tangent_x_Q1_boundary_to_A1_leTwo
    (p := p) (hp1 := hp1) (hp2 := hp2) (z := z) (y := y)
    hy_pos hz_lower
  have hd := DxuCandidate_Q1_boundary_le_Q2_leTwo
    (p := p) (hp1 := hp1) (hp2 := hp2) (x := x) (y := y)
    hy_pos hx_left
  exact tangent_glue_two_forward_leTwo_local
    (fun t => uCandidate p t y) (fun t => DxuCandidate p t y)
    (by
      have ha_pos : 0 < a p := by
        rw [a_eq_leTwo p hp1 hp2]
        exact div_pos (by linarith) (by linarith)
      have ha_lt : a p < 1 := a_lt_one_of_one_lt_of_lt_two p hp1 hp2
      have hy_lt_b : y < y / a p := by
        rw [div_eq_mul_inv]
        have hinv : 1 < (a p)⁻¹ := by
          rw [one_lt_inv₀ ha_pos]
          exact ha_lt
        nlinarith
      linarith)
    (le_of_lt hz_lower) hxb hbz hd

lemma DxuCandidate_Q3_A1_boundary_le_Q3_A1_leTwo
    (p : ℝ) (hp1 : 1 < p) (hp2 : p < 2) {x y : ℝ}
    (hy_pos : 0 < y) (hx_lower : -y < x) (hx_upper : x < a p * y) :
    DxuCandidate p (a p * y) y ≤ DxuCandidate p x y := by
  have ha_nonneg : 0 ≤ a p := a_nonneg_of_one_lt_of_lt_two p hp1 hp2
  have ha_lt : a p < 1 := a_lt_one_of_one_lt_of_lt_two p hp1 hp2
  have hQx : QuarterPlane3 x y := ⟨hy_pos.le, le_of_lt hx_lower, by
    have hc_lt_y : a p * y < y := by
      simpa using mul_lt_mul_of_pos_right ha_lt hy_pos
    exact le_of_lt (lt_trans hx_upper hc_lt_y)⟩
  have hQc : QuarterPlane3 (a p * y) y := ⟨hy_pos.le, by
    have hnonneg : 0 ≤ a p * y := mul_nonneg ha_nonneg hy_pos.le
    linarith, by
      have hle : a p * y ≤ y := by
        simpa using mul_le_mul_of_nonneg_right ha_lt.le hy_pos.le
      exact hle⟩
  have hclx : closureA1 p y x := ⟨hy_pos.le, le_of_lt hx_lower, le_of_lt hx_upper⟩
  have hclc : closureA1 p y (a p * y) := ⟨hy_pos.le, by
    have hnonneg : 0 ≤ a p * y := mul_nonneg ha_nonneg hy_pos.le
    linarith, le_rfl⟩
  have hdx : DxuCandidate p x y = DyuA1 p y x := by
    rw [DxuCandidate_eq_Q3_leTwo p hp1 hp2 hQx]
    simp [DyauxFunction1, hclx]
  have hdc : DxuCandidate p (a p * y) y = DyuA1 p y (a p * y) := by
    rw [DxuCandidate_eq_Q3_leTwo p hp1 hp2 hQc]
    simp [DyauxFunction1, hclc]
  rw [hdx, hdc]
  simp [DyuA1, hy_pos]

lemma DxuCandidate_diag_le_Q3_A1_boundary_leTwo
    (p : ℝ) (hp1 : 1 < p) (hp2 : p < 2) {y : ℝ}
    (hy_pos : 0 < y) :
    DxuCandidate p y y ≤ DxuCandidate p (a p * y) y := by
  have ha_nonneg : 0 ≤ a p := a_nonneg_of_one_lt_of_lt_two p hp1 hp2
  have ha_lt : a p < 1 := a_lt_one_of_one_lt_of_lt_two p hp1 hp2
  have hc_lt_y : a p * y < y := by
    simpa using mul_lt_mul_of_pos_right ha_lt hy_pos
  have hQd : QuarterPlane y y := ⟨hy_pos.le, le_rfl, by linarith⟩
  have hQc : QuarterPlane3 (a p * y) y := ⟨hy_pos.le, by
    have hnonneg : 0 ≤ a p * y := mul_nonneg ha_nonneg hy_pos.le
    linarith, le_of_lt hc_lt_y⟩
  have hcld : closureA2 p y y := ⟨hy_pos.le, le_of_lt hc_lt_y, le_rfl⟩
  have hnotd : ¬ closureA1 p y y := by
    intro h
    exact not_le_of_gt hc_lt_y h.2.2
  have hclc1 : closureA1 p y (a p * y) := ⟨hy_pos.le, by
    have hnonneg : 0 ≤ a p * y := mul_nonneg ha_nonneg hy_pos.le
    linarith, le_rfl⟩
  have hdd : DxuCandidate p y y = DxvLeTwo p y y := by
    rw [DxuCandidate_eq_Q1_leTwo p hQd]
    simp [DxauxFunction1, hnotd, hcld]
  have hdc : DxuCandidate p (a p * y) y = DyuA1 p y (a p * y) := by
    rw [DxuCandidate_eq_Q3_leTwo p hp1 hp2 hQc]
    simp [DyauxFunction1, hclc1]
  have hglue : DyuA1 p y (a p * y) = DyvLeTwo p y (a p * y) :=
    DyuA1_eq_DyvLeTwo_on_A1A2_boundary_leTwo p y hp1 hp2 hy_pos
  have hrel := DxauxFunction1_eq_DyauxFunction1_on_diag_leTwo
    p hp1 hp2 y hy_pos.le
  have hdy : DyauxFunction1 p y y = DyvLeTwo p y y := by
    simp [DyauxFunction1, hnotd, hcld]
  have hdx : DxvLeTwo p y y = DyvLeTwo p y y := by
    have hdx' : DxauxFunction1 p y y = DxvLeTwo p y y := by
      simp [DxauxFunction1, hnotd, hcld]
    rw [← hdx', hrel, hdy]
  have hmono := DyvLeTwo_diag_le_DyvLeTwo_Q3_A2_closed_leTwo
    (p := p) (hp1 := hp1) (hp2 := hp2) (x := a p * y) (y := y)
    hy_pos le_rfl hc_lt_y
  calc
    DxuCandidate p y y = DxvLeTwo p y y := hdd
    _ = DyvLeTwo p y y := hdx
    _ ≤ DyvLeTwo p y (a p * y) := hmono
    _ = DyuA1 p y (a p * y) := hglue.symm
    _ = DxuCandidate p (a p * y) y := hdc.symm

lemma DxuCandidate_diag_le_antidiag_leTwo
    (p : ℝ) (hp1 : 1 < p) (hp2 : p < 2) {y : ℝ}
    (hy_pos : 0 < y) :
    DxuCandidate p y y ≤ DxuCandidate p (-y) y := by
  calc
    DxuCandidate p y y ≤ DxuCandidate p (a p * y) y :=
      DxuCandidate_diag_le_Q3_A1_boundary_leTwo
        (p := p) (hp1 := hp1) (hp2 := hp2) (y := y) hy_pos
    _ = DxuCandidate p (-y) y :=
      DxuCandidate_Q3_A1_boundary_eq_antidiag_leTwo
        (p := p) (hp1 := hp1) (hp2 := hp2) (y := y) hy_pos

lemma DxuCandidate_diag_le_Q3_A1_leTwo
    (p : ℝ) (hp1 : 1 < p) (hp2 : p < 2) {x y : ℝ}
    (hy_pos : 0 < y) (hx_lower : -y < x) (hx_upper : x < a p * y) :
    DxuCandidate p y y ≤ DxuCandidate p x y :=
  le_trans
    (DxuCandidate_diag_le_Q3_A1_boundary_leTwo
      (p := p) (hp1 := hp1) (hp2 := hp2) (y := y) hy_pos)
    (DxuCandidate_Q3_A1_boundary_le_Q3_A1_leTwo
      (p := p) (hp1 := hp1) (hp2 := hp2) (x := x) (y := y)
      hy_pos hx_lower hx_upper)

lemma DxuCandidate_Q1_boundary_le_Q3_A1_leTwo
    (p : ℝ) (hp1 : 1 < p) (hp2 : p < 2) {x y : ℝ}
    (hy_pos : 0 < y) (hx_lower : -y < x) (hx_upper : x < a p * y) :
    DxuCandidate p (y / a p) y ≤ DxuCandidate p x y :=
  le_trans
    (DxuCandidate_Q1_boundary_le_diag_leTwo
      (p := p) (hp1 := hp1) (hp2 := hp2) (y := y) hy_pos)
    (DxuCandidate_diag_le_Q3_A1_leTwo
      (p := p) (hp1 := hp1) (hp2 := hp2) (x := x) (y := y)
      hy_pos hx_lower hx_upper)

lemma DxuCandidate_Q1_boundary_le_antidiag_leTwo
    (p : ℝ) (hp1 : 1 < p) (hp2 : p < 2) {y : ℝ}
    (hy_pos : 0 < y) :
    DxuCandidate p (y / a p) y ≤ DxuCandidate p (-y) y :=
  le_trans
    (DxuCandidate_Q1_boundary_le_diag_leTwo
      (p := p) (hp1 := hp1) (hp2 := hp2) (y := y) hy_pos)
    (DxuCandidate_diag_le_antidiag_leTwo
      (p := p) (hp1 := hp1) (hp2 := hp2) (y := y) hy_pos)

lemma DxuCandidate_diag_le_Q3_A2_leTwo
    (p : ℝ) (hp1 : 1 < p) (hp2 : p < 2) {x y : ℝ}
    (hy_pos : 0 < y) (hx_lower : a p * y < x) (hx_upper : x < y) :
    DxuCandidate p y y ≤ DxuCandidate p x y := by
  have hQx : QuarterPlane3 x y := ⟨hy_pos.le, by
    have ha_nonneg : 0 ≤ a p := a_nonneg_of_one_lt_of_lt_two p hp1 hp2
    have haxy_nonneg : 0 ≤ a p * y := mul_nonneg ha_nonneg hy_pos.le
    linarith, le_of_lt hx_upper⟩
  have hQy : QuarterPlane y y := ⟨hy_pos.le, le_rfl, by linarith⟩
  have hcly : closureA2 p y y := by
    have ha_lt : a p < 1 := a_lt_one_of_one_lt_of_lt_two p hp1 hp2
    exact ⟨hy_pos.le, by
      have h := mul_le_mul_of_nonneg_right ha_lt.le hy_pos.le
      simpa using h, le_rfl⟩
  have hclx : closureA2 p y x := ⟨hy_pos.le, le_of_lt hx_lower, le_of_lt hx_upper⟩
  have hdx : DxuCandidate p x y = DyvLeTwo p y x := by
    rw [DxuCandidate_eq_Q3_leTwo p hp1 hp2 hQx]
    have hnot : ¬ closureA1 p y x := by
      intro h
      exact not_le_of_gt hx_lower h.2.2
    simp [DyauxFunction1, hnot, hclx]
  have hdy : DxuCandidate p y y = DxvLeTwo p y y := by
    rw [DxuCandidate_eq_Q1_leTwo p hQy]
    exact auxFunction1_Dx_eq_DxvLeTwo_leTwo p hp1 hp2 y y hcly
  have hdiag : DxvLeTwo p y y = DyvLeTwo p y y := by
    have hzero : (0 : ℝ) ^ (p - 1) = 0 := Real.zero_rpow (by linarith)
    simp [DxvLeTwo, DyvLeTwo, hy_pos, abs_of_pos hy_pos, hzero]
  have hmono := DyvLeTwo_diag_le_DyvLeTwo_Q3_A2_leTwo
    (p := p) (hp1 := hp1) (hp2 := hp2) (x := x) (y := y)
    hy_pos hx_lower hx_upper
  rw [hdy, hdx, hdiag]
  exact hmono

lemma DxuCandidate_Q1_boundary_le_Q3_A2_leTwo
    (p : ℝ) (hp1 : 1 < p) (hp2 : p < 2) {x y : ℝ}
    (hy_pos : 0 < y) (hx_lower : a p * y < x) (hx_upper : x < y) :
    DxuCandidate p (y / a p) y ≤ DxuCandidate p x y :=
  le_trans
    (DxuCandidate_Q1_boundary_le_diag_leTwo
      (p := p) (hp1 := hp1) (hp2 := hp2) (y := y) hy_pos)
    (DxuCandidate_diag_le_Q3_A2_leTwo
      (p := p) (hp1 := hp1) (hp2 := hp2) (x := x) (y := y)
      hy_pos hx_lower hx_upper)

lemma uCandidate_tangent_x_antidiag_to_Q1_A2_leTwo
    (p : ℝ) (hp1 : 1 < p) (hp2 : p < 2) {z y : ℝ}
    (hy_pos : 0 < y) (hz_lower : y < z) (hz_upper : z < y / a p) :
    uCandidate p z y ≤
      uCandidate p (-y) y + DxuCandidate p (-y) y * (z - (-y)) := by
  have hxy := uCandidate_tangent_x_antidiag_to_diag_leTwo
    (p := p) (hp1 := hp1) (hp2 := hp2) (y := y) hy_pos
  have hyz := uCandidate_tangent_x_diag_to_Q1_A2_leTwo
    (p := p) (hp1 := hp1) (hp2 := hp2) (z := z) (y := y)
    hy_pos hz_lower hz_upper
  have hd := DxuCandidate_diag_le_antidiag_leTwo
    (p := p) (hp1 := hp1) (hp2 := hp2) (y := y) hy_pos
  exact tangent_glue_two_forward_leTwo_local
    (fun t => uCandidate p t y) (fun t => DxuCandidate p t y)
    (by linarith) (le_of_lt hz_lower) hxy hyz hd

lemma uCandidate_tangent_x_antidiag_to_Q1_boundary_leTwo
    (p : ℝ) (hp1 : 1 < p) (hp2 : p < 2) {y : ℝ}
    (hy_pos : 0 < y) :
    uCandidate p (y / a p) y ≤
      uCandidate p (-y) y + DxuCandidate p (-y) y * (y / a p - (-y)) := by
  have hxy := uCandidate_tangent_x_antidiag_to_diag_leTwo
    (p := p) (hp1 := hp1) (hp2 := hp2) (y := y) hy_pos
  have hyb := uCandidate_tangent_x_diag_to_Q1_boundary_leTwo
    (p := p) (hp1 := hp1) (hp2 := hp2) (y := y) hy_pos
  have hd := DxuCandidate_diag_le_antidiag_leTwo
    (p := p) (hp1 := hp1) (hp2 := hp2) (y := y) hy_pos
  exact tangent_glue_two_forward_leTwo_local
    (fun t => uCandidate p t y) (fun t => DxuCandidate p t y)
    (by linarith) (by
      have ha_pos : 0 < a p := by
        rw [a_eq_leTwo p hp1 hp2]
        exact div_pos (by linarith) (by linarith)
      have ha_lt : a p < 1 := a_lt_one_of_one_lt_of_lt_two p hp1 hp2
      have hlt : y < y / a p := by
        rw [div_eq_mul_inv]
        have hinv : 1 < (a p)⁻¹ := by
          rw [one_lt_inv₀ ha_pos]
          exact ha_lt
        nlinarith
      exact le_of_lt hlt) hxy hyb hd

lemma uCandidate_tangent_x_antidiag_to_Q1_A1_leTwo
    (p : ℝ) (hp1 : 1 < p) (hp2 : p < 2) {z y : ℝ}
    (hy_pos : 0 < y) (hz_lower : y / a p < z) :
    uCandidate p z y ≤
      uCandidate p (-y) y + DxuCandidate p (-y) y * (z - (-y)) := by
  have hxb := uCandidate_tangent_x_antidiag_to_Q1_boundary_leTwo
    (p := p) (hp1 := hp1) (hp2 := hp2) (y := y) hy_pos
  have hbz := uCandidate_tangent_x_Q1_boundary_to_A1_leTwo
    (p := p) (hp1 := hp1) (hp2 := hp2) (z := z) (y := y)
    hy_pos hz_lower
  have hd := DxuCandidate_Q1_boundary_le_antidiag_leTwo
    (p := p) (hp1 := hp1) (hp2 := hp2) (y := y) hy_pos
  exact tangent_glue_two_forward_leTwo_local
    (fun t => uCandidate p t y) (fun t => DxuCandidate p t y)
    (by
      have ha_pos : 0 < a p := by
        rw [a_eq_leTwo p hp1 hp2]
        exact div_pos (by linarith) (by linarith)
      have ha_lt : a p < 1 := a_lt_one_of_one_lt_of_lt_two p hp1 hp2
      have hlt : y < y / a p := by
        rw [div_eq_mul_inv]
        have hinv : 1 < (a p)⁻¹ := by
          rw [one_lt_inv₀ ha_pos]
          exact ha_lt
        nlinarith
      linarith)
    (le_of_lt hz_lower) hxb hbz hd

lemma uCandidate_tangent_x_Q3_A1_to_diag_leTwo
    (p : ℝ) (hp1 : 1 < p) (hp2 : p < 2) {x y : ℝ}
    (hy_pos : 0 < y) (hx_lower : -y < x) (hx_upper : x < a p * y) :
    uCandidate p y y ≤
      uCandidate p x y + DxuCandidate p x y * (y - x) := by
  have hxc := uCandidate_tangent_x_Q3_A1_to_A2_boundary_leTwo
    (p := p) (hp1 := hp1) (hp2 := hp2) (x := x) (y := y)
    hy_pos hx_lower hx_upper
  have hcy := uCandidate_tangent_x_Q3_A2_boundary_to_diag_leTwo
    (p := p) (hp1 := hp1) (hp2 := hp2) (y := y) hy_pos
  have hd := DxuCandidate_Q3_A1_boundary_le_Q3_A1_leTwo
    (p := p) (hp1 := hp1) (hp2 := hp2) (x := x) (y := y)
    hy_pos hx_lower hx_upper
  exact tangent_glue_two_forward_leTwo_local
    (fun t => uCandidate p t y) (fun t => DxuCandidate p t y)
    (le_of_lt hx_upper) (by
      have ha_lt : a p < 1 := a_lt_one_of_one_lt_of_lt_two p hp1 hp2
      have hlt : a p * y < y := by
        simpa using mul_lt_mul_of_pos_right ha_lt hy_pos
      exact le_of_lt hlt) hxc hcy hd

lemma uCandidate_tangent_x_Q3_A1_to_Q1_A2_leTwo
    (p : ℝ) (hp1 : 1 < p) (hp2 : p < 2) {x z y : ℝ}
    (hy_pos : 0 < y) (hx_lower : -y < x) (hx_upper : x < a p * y)
    (hz_lower : y < z) (hz_upper : z < y / a p) :
    uCandidate p z y ≤
      uCandidate p x y + DxuCandidate p x y * (z - x) := by
  have hxy := uCandidate_tangent_x_Q3_A1_to_diag_leTwo
    (p := p) (hp1 := hp1) (hp2 := hp2) (x := x) (y := y)
    hy_pos hx_lower hx_upper
  have hyz := uCandidate_tangent_x_diag_to_Q1_A2_leTwo
    (p := p) (hp1 := hp1) (hp2 := hp2) (z := z) (y := y)
    hy_pos hz_lower hz_upper
  have hd := DxuCandidate_diag_le_Q3_A1_leTwo
    (p := p) (hp1 := hp1) (hp2 := hp2) (x := x) (y := y)
    hy_pos hx_lower hx_upper
  exact tangent_glue_two_forward_leTwo_local
    (fun t => uCandidate p t y) (fun t => DxuCandidate p t y)
    (by
      have ha_lt : a p < 1 := a_lt_one_of_one_lt_of_lt_two p hp1 hp2
      have hlt : a p * y < y := by
        simpa using mul_lt_mul_of_pos_right ha_lt hy_pos
      linarith) (le_of_lt hz_lower) hxy hyz hd

lemma uCandidate_tangent_x_Q3_A1_to_Q1_boundary_leTwo
    (p : ℝ) (hp1 : 1 < p) (hp2 : p < 2) {x y : ℝ}
    (hy_pos : 0 < y) (hx_lower : -y < x) (hx_upper : x < a p * y) :
    uCandidate p (y / a p) y ≤
      uCandidate p x y + DxuCandidate p x y * (y / a p - x) := by
  have hxy := uCandidate_tangent_x_Q3_A1_to_diag_leTwo
    (p := p) (hp1 := hp1) (hp2 := hp2) (x := x) (y := y)
    hy_pos hx_lower hx_upper
  have hyb := uCandidate_tangent_x_diag_to_Q1_boundary_leTwo
    (p := p) (hp1 := hp1) (hp2 := hp2) (y := y) hy_pos
  have hd := DxuCandidate_diag_le_Q3_A1_leTwo
    (p := p) (hp1 := hp1) (hp2 := hp2) (x := x) (y := y)
    hy_pos hx_lower hx_upper
  exact tangent_glue_two_forward_leTwo_local
    (fun t => uCandidate p t y) (fun t => DxuCandidate p t y)
    (by
      have ha_lt : a p < 1 := a_lt_one_of_one_lt_of_lt_two p hp1 hp2
      have hlt : a p * y < y := by
        simpa using mul_lt_mul_of_pos_right ha_lt hy_pos
      linarith) (by
      have ha_pos : 0 < a p := by
        rw [a_eq_leTwo p hp1 hp2]
        exact div_pos (by linarith) (by linarith)
      have ha_lt : a p < 1 := a_lt_one_of_one_lt_of_lt_two p hp1 hp2
      have hlt : y < y / a p := by
        rw [div_eq_mul_inv]
        have hinv : 1 < (a p)⁻¹ := by
          rw [one_lt_inv₀ ha_pos]
          exact ha_lt
        nlinarith
      exact le_of_lt hlt) hxy hyb hd

lemma uCandidate_tangent_x_Q3_A1_to_Q1_A1_leTwo
    (p : ℝ) (hp1 : 1 < p) (hp2 : p < 2) {x z y : ℝ}
    (hy_pos : 0 < y) (hx_lower : -y < x) (hx_upper : x < a p * y)
    (hz_lower : y / a p < z) :
    uCandidate p z y ≤
      uCandidate p x y + DxuCandidate p x y * (z - x) := by
  have hxb := uCandidate_tangent_x_Q3_A1_to_Q1_boundary_leTwo
    (p := p) (hp1 := hp1) (hp2 := hp2) (x := x) (y := y)
    hy_pos hx_lower hx_upper
  have hbz := uCandidate_tangent_x_Q1_boundary_to_A1_leTwo
    (p := p) (hp1 := hp1) (hp2 := hp2) (z := z) (y := y)
    hy_pos hz_lower
  have hd := DxuCandidate_Q1_boundary_le_Q3_A1_leTwo
    (p := p) (hp1 := hp1) (hp2 := hp2) (x := x) (y := y)
    hy_pos hx_lower hx_upper
  exact tangent_glue_two_forward_leTwo_local
    (fun t => uCandidate p t y) (fun t => DxuCandidate p t y)
    (by
      have ha_pos : 0 < a p := by
        rw [a_eq_leTwo p hp1 hp2]
        exact div_pos (by linarith) (by linarith)
      have ha_lt : a p < 1 := a_lt_one_of_one_lt_of_lt_two p hp1 hp2
      have hlt : a p * y < y / a p := by
        have hay : a p * y < y := by
          simpa using mul_lt_mul_of_pos_right ha_lt hy_pos
        have hyb : y < y / a p := by
          rw [div_eq_mul_inv]
          have hinv : 1 < (a p)⁻¹ := by
            rw [one_lt_inv₀ ha_pos]
            exact ha_lt
          nlinarith
        linarith
      linarith)
    (le_of_lt hz_lower) hxb hbz hd

lemma uCandidate_tangent_x_Q3_A2_to_Q1_boundary_leTwo
    (p : ℝ) (hp1 : 1 < p) (hp2 : p < 2) {x y : ℝ}
    (hy_pos : 0 < y) (hx_lower : a p * y < x) (hx_upper : x < y) :
    uCandidate p (y / a p) y ≤
      uCandidate p x y + DxuCandidate p x y * (y / a p - x) := by
  have hxy := uCandidate_tangent_x_Q3_A2_to_diag_leTwo
    (p := p) (hp1 := hp1) (hp2 := hp2) (x := x) (y := y)
    hy_pos hx_lower hx_upper
  have hyb := uCandidate_tangent_x_diag_to_Q1_boundary_leTwo
    (p := p) (hp1 := hp1) (hp2 := hp2) (y := y) hy_pos
  have hd := DxuCandidate_diag_le_Q3_A2_leTwo
    (p := p) (hp1 := hp1) (hp2 := hp2) (x := x) (y := y)
    hy_pos hx_lower hx_upper
  exact tangent_glue_two_forward_leTwo_local
    (fun t => uCandidate p t y) (fun t => DxuCandidate p t y)
    (le_of_lt hx_upper) (by
      have ha_pos : 0 < a p := by
        rw [a_eq_leTwo p hp1 hp2]
        exact div_pos (by linarith) (by linarith)
      have ha_lt : a p < 1 := a_lt_one_of_one_lt_of_lt_two p hp1 hp2
      have hlt : y < y / a p := by
        rw [div_eq_mul_inv]
        have hinv : 1 < (a p)⁻¹ := by
          rw [one_lt_inv₀ ha_pos]
          exact ha_lt
        nlinarith
      exact le_of_lt hlt) hxy hyb hd

lemma uCandidate_tangent_x_Q3_A2_to_Q1_A1_leTwo
    (p : ℝ) (hp1 : 1 < p) (hp2 : p < 2) {x z y : ℝ}
    (hy_pos : 0 < y) (hx_lower : a p * y < x) (hx_upper : x < y)
    (hz_lower : y / a p < z) :
    uCandidate p z y ≤
      uCandidate p x y + DxuCandidate p x y * (z - x) := by
  have hxb := uCandidate_tangent_x_Q3_A2_to_Q1_boundary_leTwo
    (p := p) (hp1 := hp1) (hp2 := hp2) (x := x) (y := y)
    hy_pos hx_lower hx_upper
  have hbz := uCandidate_tangent_x_Q1_boundary_to_A1_leTwo
    (p := p) (hp1 := hp1) (hp2 := hp2) (z := z) (y := y)
    hy_pos hz_lower
  have hd := DxuCandidate_Q1_boundary_le_Q3_A2_leTwo
    (p := p) (hp1 := hp1) (hp2 := hp2) (x := x) (y := y)
    hy_pos hx_lower hx_upper
  exact tangent_glue_two_forward_leTwo_local
    (fun t => uCandidate p t y) (fun t => DxuCandidate p t y)
    (by
      have ha_pos : 0 < a p := by
        rw [a_eq_leTwo p hp1 hp2]
        exact div_pos (by linarith) (by linarith)
      have ha_lt : a p < 1 := a_lt_one_of_one_lt_of_lt_two p hp1 hp2
      have hlt : y < y / a p := by
        rw [div_eq_mul_inv]
        have hinv : 1 < (a p)⁻¹ := by
          rw [one_lt_inv₀ ha_pos]
          exact ha_lt
        nlinarith
      linarith)
    (le_of_lt hz_lower) hxb hbz hd

lemma uCandidate_tangent_x_Q3_A2_boundary_to_Q1_A2_leTwo
    (p : ℝ) (hp1 : 1 < p) (hp2 : p < 2) {z y : ℝ}
    (hy_pos : 0 < y) (hz_lower : y < z) (hz_upper : z < y / a p) :
    uCandidate p z y ≤
      uCandidate p (a p * y) y +
        DxuCandidate p (a p * y) y * (z - a p * y) := by
  have hcy := uCandidate_tangent_x_Q3_A2_boundary_to_diag_leTwo
    (p := p) (hp1 := hp1) (hp2 := hp2) (y := y) hy_pos
  have hyz := uCandidate_tangent_x_diag_to_Q1_A2_leTwo
    (p := p) (hp1 := hp1) (hp2 := hp2) (z := z) (y := y)
    hy_pos hz_lower hz_upper
  have hd := DxuCandidate_diag_le_Q3_A1_boundary_leTwo
    (p := p) (hp1 := hp1) (hp2 := hp2) (y := y) hy_pos
  exact tangent_glue_two_forward_leTwo_local
    (fun t => uCandidate p t y) (fun t => DxuCandidate p t y)
    (by
      have ha_lt : a p < 1 := a_lt_one_of_one_lt_of_lt_two p hp1 hp2
      have hlt : a p * y < y := by
        simpa using mul_lt_mul_of_pos_right ha_lt hy_pos
      exact le_of_lt hlt)
    (le_of_lt hz_lower) hcy hyz hd

lemma uCandidate_tangent_x_Q3_A2_boundary_to_Q1_boundary_leTwo
    (p : ℝ) (hp1 : 1 < p) (hp2 : p < 2) {y : ℝ}
    (hy_pos : 0 < y) :
    uCandidate p (y / a p) y ≤
      uCandidate p (a p * y) y +
        DxuCandidate p (a p * y) y * (y / a p - a p * y) := by
  have hcy := uCandidate_tangent_x_Q3_A2_boundary_to_diag_leTwo
    (p := p) (hp1 := hp1) (hp2 := hp2) (y := y) hy_pos
  have hyb := uCandidate_tangent_x_diag_to_Q1_boundary_leTwo
    (p := p) (hp1 := hp1) (hp2 := hp2) (y := y) hy_pos
  have hd := DxuCandidate_diag_le_Q3_A1_boundary_leTwo
    (p := p) (hp1 := hp1) (hp2 := hp2) (y := y) hy_pos
  exact tangent_glue_two_forward_leTwo_local
    (fun t => uCandidate p t y) (fun t => DxuCandidate p t y)
    (by
      have ha_lt : a p < 1 := a_lt_one_of_one_lt_of_lt_two p hp1 hp2
      have hlt : a p * y < y := by
        simpa using mul_lt_mul_of_pos_right ha_lt hy_pos
      exact le_of_lt hlt)
    (by
      have ha_pos : 0 < a p := by
        rw [a_eq_leTwo p hp1 hp2]
        exact div_pos (by linarith) (by linarith)
      have ha_lt : a p < 1 := a_lt_one_of_one_lt_of_lt_two p hp1 hp2
      have hlt : y < y / a p := by
        rw [div_eq_mul_inv]
        have hinv : 1 < (a p)⁻¹ := by
          rw [one_lt_inv₀ ha_pos]
          exact ha_lt
        nlinarith
      exact le_of_lt hlt) hcy hyb hd

lemma uCandidate_tangent_x_Q3_A2_boundary_to_Q1_A1_leTwo
    (p : ℝ) (hp1 : 1 < p) (hp2 : p < 2) {z y : ℝ}
    (hy_pos : 0 < y) (hz_lower : y / a p < z) :
    uCandidate p z y ≤
      uCandidate p (a p * y) y +
        DxuCandidate p (a p * y) y * (z - a p * y) := by
  have hcb := uCandidate_tangent_x_Q3_A2_boundary_to_Q1_boundary_leTwo
    (p := p) (hp1 := hp1) (hp2 := hp2) (y := y) hy_pos
  have hbz := uCandidate_tangent_x_Q1_boundary_to_A1_leTwo
    (p := p) (hp1 := hp1) (hp2 := hp2) (z := z) (y := y)
    hy_pos hz_lower
  have hd : DxuCandidate p (y / a p) y ≤ DxuCandidate p (a p * y) y := by
    exact le_trans
      (DxuCandidate_Q1_boundary_le_diag_leTwo
        (p := p) (hp1 := hp1) (hp2 := hp2) (y := y) hy_pos)
      (DxuCandidate_diag_le_Q3_A1_boundary_leTwo
        (p := p) (hp1 := hp1) (hp2 := hp2) (y := y) hy_pos)
  exact tangent_glue_two_forward_leTwo_local
    (fun t => uCandidate p t y) (fun t => DxuCandidate p t y)
    (by
      have ha_pos : 0 < a p := by
        rw [a_eq_leTwo p hp1 hp2]
        exact div_pos (by linarith) (by linarith)
      have ha_lt : a p < 1 := a_lt_one_of_one_lt_of_lt_two p hp1 hp2
      have hlt1 : a p * y < y := by
        simpa using mul_lt_mul_of_pos_right ha_lt hy_pos
      have hlt2 : y < y / a p := by
        rw [div_eq_mul_inv]
        have hinv : 1 < (a p)⁻¹ := by
          rw [one_lt_inv₀ ha_pos]
          exact ha_lt
        nlinarith
      linarith)
    (le_of_lt hz_lower) hcb hbz hd

lemma uCandidate_tangent_x_forward_of_y_pos_leTwo
    (p : ℝ) (hp1 : 1 < p) (hp2 : p < 2) {x z y : ℝ}
    (hy_pos : 0 < y) (hxz : x < z) :
    uCandidate p z y ≤
      uCandidate p x y + DxuCandidate p x y * (z - x) := by
  have ha_pos : 0 < a p := by
    rw [a_eq_leTwo p hp1 hp2]
    exact div_pos (by linarith) (by linarith)
  have ha_nonneg : 0 ≤ a p := ha_pos.le
  have ha_lt : a p < 1 := a_lt_one_of_one_lt_of_lt_two p hp1 hp2
  have hneg_lt_c : -y < a p * y := by
    have hnonneg : 0 ≤ a p * y := mul_nonneg ha_nonneg hy_pos.le
    linarith
  have hc_lt_y : a p * y < y := by
    simpa using mul_lt_mul_of_pos_right ha_lt hy_pos
  have hy_lt_b : y < y / a p := by
    rw [div_eq_mul_inv]
    have hinv : 1 < (a p)⁻¹ := by
      rw [one_lt_inv₀ ha_pos]
      exact ha_lt
    nlinarith
  by_cases hx_left : x < -y
  · by_cases hz_left : z < -y
    · exact uCandidate_tangent_x_on_Q2_A1_segment_leTwo
        (p := p) (hp1 := hp1) (hp2 := hp2) (x := x) (z := z) (y := y)
        hy_pos hx_left hz_left
    · have hza_le : -y ≤ z := le_of_not_gt hz_left
      rcases hza_le.lt_or_eq with hza | hza_eq
      · by_cases hz_c : z < a p * y
        · exact uCandidate_tangent_x_cross_Q2_to_Q3_A1_leTwo
            (p := p) (hp1 := hp1) (hp2 := hp2) (x := x) (z := z) (y := y)
            hy_pos hx_left hza hz_c
        · have hcz_le : a p * y ≤ z := le_of_not_gt hz_c
          rcases hcz_le.lt_or_eq with hcz | hcz_eq
          · by_cases hz_y : z < y
            · exact uCandidate_tangent_x_cross_Q2_to_Q3_A2_leTwo
                (p := p) (hp1 := hp1) (hp2 := hp2) (x := x) (z := z) (y := y)
                hy_pos hx_left hcz hz_y
            · have hyz_le : y ≤ z := le_of_not_gt hz_y
              rcases hyz_le.lt_or_eq with hyz | hyz_eq
              · by_cases hz_b : z < y / a p
                · exact uCandidate_tangent_x_cross_Q2_to_Q1_A2_leTwo
                    (p := p) (hp1 := hp1) (hp2 := hp2) (x := x) (z := z) (y := y)
                    hy_pos hx_left hyz hz_b
                · have hbz_le : y / a p ≤ z := le_of_not_gt hz_b
                  rcases hbz_le.lt_or_eq with hbz | hbz_eq
                  · exact uCandidate_tangent_x_cross_Q2_to_Q1_A1_leTwo
                      (p := p) (hp1 := hp1) (hp2 := hp2) (x := x) (z := z) (y := y)
                      hy_pos hx_left hbz
                  · subst z
                    exact uCandidate_tangent_x_Q2_to_Q1_boundary_leTwo
                      (p := p) (hp1 := hp1) (hp2 := hp2) (x := x) (y := y)
                      hy_pos hx_left
              · subst z
                exact uCandidate_tangent_x_Q2_to_diag_leTwo
                  (p := p) (hp1 := hp1) (hp2 := hp2) (x := x) (y := y)
                  hy_pos hx_left
          · subst z
            exact uCandidate_tangent_x_Q2_to_Q3_A1_boundary_leTwo
              (p := p) (hp1 := hp1) (hp2 := hp2) (x := x) (y := y)
              hy_pos hx_left
      · subst z
        exact uCandidate_tangent_x_Q2_to_antidiag_leTwo
          (p := p) (hp1 := hp1) (hp2 := hp2) (x := x) (y := y)
          hy_pos hx_left
  · have hxa_le : -y ≤ x := le_of_not_gt hx_left
    rcases hxa_le.lt_or_eq with hxa | hxa_eq
    · by_cases hx_c : x < a p * y
      · by_cases hz_c : z < a p * y
        · exact uCandidate_tangent_x_on_Q3_A1_segment_leTwo
            (p := p) (hp1 := hp1) (hp2 := hp2) (x := x) (z := z) (y := y)
            hy_pos hxa hx_c (lt_trans hxa hxz) hz_c
        · have hcz_le : a p * y ≤ z := le_of_not_gt hz_c
          rcases hcz_le.lt_or_eq with hcz | hcz_eq
          · by_cases hz_y : z < y
            · exact uCandidate_tangent_x_cross_Q3_A1_to_A2_leTwo
                (p := p) (hp1 := hp1) (hp2 := hp2) (x := x) (z := z) (y := y)
                hy_pos hxa hx_c hcz hz_y
            · have hyz_le : y ≤ z := le_of_not_gt hz_y
              rcases hyz_le.lt_or_eq with hyz | hyz_eq
              · by_cases hz_b : z < y / a p
                · exact uCandidate_tangent_x_Q3_A1_to_Q1_A2_leTwo
                    (p := p) (hp1 := hp1) (hp2 := hp2) (x := x) (z := z) (y := y)
                    hy_pos hxa hx_c hyz hz_b
                · have hbz_le : y / a p ≤ z := le_of_not_gt hz_b
                  rcases hbz_le.lt_or_eq with hbz | hbz_eq
                  · exact uCandidate_tangent_x_Q3_A1_to_Q1_A1_leTwo
                      (p := p) (hp1 := hp1) (hp2 := hp2) (x := x) (z := z) (y := y)
                      hy_pos hxa hx_c hbz
                  · subst z
                    exact uCandidate_tangent_x_Q3_A1_to_Q1_boundary_leTwo
                      (p := p) (hp1 := hp1) (hp2 := hp2) (x := x) (y := y)
                      hy_pos hxa hx_c
              · subst z
                exact uCandidate_tangent_x_Q3_A1_to_diag_leTwo
                  (p := p) (hp1 := hp1) (hp2 := hp2) (x := x) (y := y)
                  hy_pos hxa hx_c
          · subst z
            exact uCandidate_tangent_x_Q3_A1_to_A2_boundary_leTwo
              (p := p) (hp1 := hp1) (hp2 := hp2) (x := x) (y := y)
              hy_pos hxa hx_c
      · have hcx_le : a p * y ≤ x := le_of_not_gt hx_c
        rcases hcx_le.lt_or_eq with hcx | hcx_eq
        · by_cases hx_y : x < y
          · by_cases hz_y : z < y
            · exact uCandidate_tangent_x_on_Q3_A2_segment_leTwo
                (p := p) (hp1 := hp1) (hp2 := hp2) (x := x) (z := z) (y := y)
                hy_pos hcx hx_y (lt_trans hcx hxz) hz_y
            · have hyz_le : y ≤ z := le_of_not_gt hz_y
              rcases hyz_le.lt_or_eq with hyz | hyz_eq
              · by_cases hz_b : z < y / a p
                · exact uCandidate_tangent_x_cross_Q3_A2_to_Q1_A2_leTwo
                    (p := p) (hp1 := hp1) (hp2 := hp2) (x := x) (z := z) (y := y)
                    hy_pos hcx hx_y hyz hz_b
                · have hbz_le : y / a p ≤ z := le_of_not_gt hz_b
                  rcases hbz_le.lt_or_eq with hbz | hbz_eq
                  · exact uCandidate_tangent_x_Q3_A2_to_Q1_A1_leTwo
                      (p := p) (hp1 := hp1) (hp2 := hp2) (x := x) (z := z) (y := y)
                      hy_pos hcx hx_y hbz
                  · subst z
                    exact uCandidate_tangent_x_Q3_A2_to_Q1_boundary_leTwo
                      (p := p) (hp1 := hp1) (hp2 := hp2) (x := x) (y := y)
                      hy_pos hcx hx_y
              · subst z
                exact uCandidate_tangent_x_Q3_A2_to_diag_leTwo
                  (p := p) (hp1 := hp1) (hp2 := hp2) (x := x) (y := y)
                  hy_pos hcx hx_y
          · have hyx_le : y ≤ x := le_of_not_gt hx_y
            rcases hyx_le.lt_or_eq with hyx | hyx_eq
            · exact uCandidate_tangent_x_forward_on_Q1_leTwo
                (p := p) (hp1 := hp1) (hp2 := hp2) (x := x) (z := z) (y := y)
                hy_pos hyx (le_of_lt hxz)
            · subst x
              by_cases hz_b : z < y / a p
              · exact uCandidate_tangent_x_diag_to_Q1_A2_leTwo
                  (p := p) (hp1 := hp1) (hp2 := hp2) (z := z) (y := y)
                  hy_pos (by simpa using hxz) hz_b
              · have hbz_le : y / a p ≤ z := le_of_not_gt hz_b
                rcases hbz_le.lt_or_eq with hbz | hbz_eq
                · have hyb := uCandidate_tangent_x_diag_to_Q1_boundary_leTwo
                    (p := p) (hp1 := hp1) (hp2 := hp2) (y := y) hy_pos
                  have hbz' := uCandidate_tangent_x_Q1_boundary_to_A1_leTwo
                    (p := p) (hp1 := hp1) (hp2 := hp2) (z := z) (y := y)
                    hy_pos hbz
                  have hd := DxuCandidate_Q1_boundary_le_diag_leTwo
                    (p := p) (hp1 := hp1) (hp2 := hp2) (y := y) hy_pos
                  exact tangent_glue_two_forward_leTwo_local
                    (fun t => uCandidate p t y) (fun t => DxuCandidate p t y)
                    (le_of_lt hy_lt_b) (le_of_lt hbz) hyb hbz' hd
                · subst z
                  exact uCandidate_tangent_x_diag_to_Q1_boundary_leTwo
                    (p := p) (hp1 := hp1) (hp2 := hp2) (y := y) hy_pos
        · subst x
          by_cases hz_y : z < y
          · exact uCandidate_tangent_x_Q3_A2_boundary_to_A2_leTwo
              (p := p) (hp1 := hp1) (hp2 := hp2) (z := z) (y := y)
              hy_pos (by simpa using hxz) hz_y
          · have hyz_le : y ≤ z := le_of_not_gt hz_y
            rcases hyz_le.lt_or_eq with hyz | hyz_eq
            · by_cases hz_b : z < y / a p
              · exact uCandidate_tangent_x_Q3_A2_boundary_to_Q1_A2_leTwo
                  (p := p) (hp1 := hp1) (hp2 := hp2) (z := z) (y := y)
                  hy_pos hyz hz_b
              · have hbz_le : y / a p ≤ z := le_of_not_gt hz_b
                rcases hbz_le.lt_or_eq with hbz | hbz_eq
                · exact uCandidate_tangent_x_Q3_A2_boundary_to_Q1_A1_leTwo
                    (p := p) (hp1 := hp1) (hp2 := hp2) (z := z) (y := y)
                    hy_pos hbz
                · subst z
                  exact uCandidate_tangent_x_Q3_A2_boundary_to_Q1_boundary_leTwo
                    (p := p) (hp1 := hp1) (hp2 := hp2) (y := y) hy_pos
            · subst z
              exact uCandidate_tangent_x_Q3_A2_boundary_to_diag_leTwo
                (p := p) (hp1 := hp1) (hp2 := hp2) (y := y) hy_pos
    · subst x
      by_cases hz_c : z < a p * y
      · exact uCandidate_tangent_x_antidiag_to_Q3_A1_leTwo
          (p := p) (hp1 := hp1) (hp2 := hp2) (z := z) (y := y)
          hy_pos (by simpa using hxz) hz_c
      · have hcz_le : a p * y ≤ z := le_of_not_gt hz_c
        rcases hcz_le.lt_or_eq with hcz | hcz_eq
        · by_cases hz_y : z < y
          · exact uCandidate_tangent_x_antidiag_to_Q3_A2_leTwo
              (p := p) (hp1 := hp1) (hp2 := hp2) (z := z) (y := y)
              hy_pos hcz hz_y
          · have hyz_le : y ≤ z := le_of_not_gt hz_y
            rcases hyz_le.lt_or_eq with hyz | hyz_eq
            · by_cases hz_b : z < y / a p
              · exact uCandidate_tangent_x_antidiag_to_Q1_A2_leTwo
                  (p := p) (hp1 := hp1) (hp2 := hp2) (z := z) (y := y)
                  hy_pos hyz hz_b
              · have hbz_le : y / a p ≤ z := le_of_not_gt hz_b
                rcases hbz_le.lt_or_eq with hbz | hbz_eq
                · exact uCandidate_tangent_x_antidiag_to_Q1_A1_leTwo
                    (p := p) (hp1 := hp1) (hp2 := hp2) (z := z) (y := y)
                    hy_pos hbz
                · subst z
                  exact uCandidate_tangent_x_antidiag_to_Q1_boundary_leTwo
                    (p := p) (hp1 := hp1) (hp2 := hp2) (y := y) hy_pos
            · subst z
              exact uCandidate_tangent_x_antidiag_to_diag_leTwo
                (p := p) (hp1 := hp1) (hp2 := hp2) (y := y) hy_pos
        · subst z
          exact uCandidate_tangent_x_antidiag_to_Q3_A1_boundary_leTwo
            (p := p) (hp1 := hp1) (hp2 := hp2) (y := y) hy_pos

lemma uCandidate_tangent_x_forward_of_y_pos_le_leTwo
    (p : ℝ) (hp1 : 1 < p) (hp2 : p < 2) {x z y : ℝ}
    (hy_pos : 0 < y) (hxz : x ≤ z) :
    uCandidate p z y ≤
      uCandidate p x y + DxuCandidate p x y * (z - x) := by
  rcases hxz.lt_or_eq with hxz_lt | rfl
  · exact uCandidate_tangent_x_forward_of_y_pos_leTwo
      (p := p) (hp1 := hp1) (hp2 := hp2) (x := x) (z := z) (y := y)
      hy_pos hxz_lt
  · simp

lemma uCandidate_tangent_x_Q1_A1_to_boundary_leTwo
    (p : ℝ) (hp1 : 1 < p) (hp2 : p < 2) {x y : ℝ}
    (hy_pos : 0 < y) (hx_lower : y / a p < x) :
    uCandidate p (y / a p) y ≤
      uCandidate p x y + DxuCandidate p x y * (y / a p - x) := by
  have ha_pos : 0 < a p := by
    rw [a_eq_leTwo p hp1 hp2]
    exact div_pos (by linarith) (by linarith)
  have ha_lt : a p < 1 := a_lt_one_of_one_lt_of_lt_two p hp1 hp2
  have hb_pos : 0 < y / a p := div_pos hy_pos ha_pos
  have hy_lt_b : y < y / a p := by
    rw [div_eq_mul_inv]
    have hinv : 1 < (a p)⁻¹ := by
      rw [one_lt_inv₀ ha_pos]
      exact ha_lt
    nlinarith
  have hQx : QuarterPlane x y :=
    ⟨by linarith, le_of_lt (lt_trans hy_lt_b hx_lower), by linarith⟩
  have hQb : QuarterPlane (y / a p) y :=
    ⟨hb_pos.le, le_of_lt hy_lt_b, by linarith⟩
  have hboundary := horizontal_boundary_closureA1_closureA2_leTwo p y hp1 hp2 hy_pos
  have hclx : closureA1 p x y := by
    have hay : y < a p * x := by
      have hmul := mul_lt_mul_of_pos_left hx_lower ha_pos
      field_simp [ha_pos.ne'] at hmul
      simpa [mul_comm, mul_left_comm, mul_assoc] using hmul
    exact ⟨by linarith, by linarith, le_of_lt hay⟩
  have hux : uCandidate p x y = uA1 p x y := by
    rw [uCandidate_eq_Q1_leTwo p hQx]
    simp [auxFunction1, hclx]
  have hub : uCandidate p (y / a p) y = uA1 p (y / a p) y := by
    rw [uCandidate_eq_Q1_leTwo p hQb]
    simp [auxFunction1, hboundary.1]
  have hdx : DxuCandidate p x y = DxuA1 p x y := by
    rw [DxuCandidate_eq_Q1_leTwo p hQx]
    simp [DxauxFunction1, hclx]
  have hmain :
      uA1 p (y / a p) y ≤
        uA1 p x y + DxuA1 p x y * (y / a p - x) := by
    apply uA1_tangent_x_on_Icc_leTwo
        (p := p) (hp1 := hp1) (hp2 := hp2)
        (lo := y / a p) (hi := x) (x := x) (z := y / a p) (y := y)
    · intro t ht
      exact lt_of_lt_of_le hb_pos ht.1
    · intro t ht
      have htI : t ∈ Set.Ioo (y / a p) x := by
        simpa [interior_Icc] using ht
      linarith [hy_pos, hb_pos, htI.1]
    · exact ⟨le_of_lt hx_lower, le_rfl⟩
    · exact ⟨le_rfl, le_of_lt hx_lower⟩
  calc
    uCandidate p (y / a p) y = uA1 p (y / a p) y := hub
    _ ≤ uA1 p x y + DxuA1 p x y * (y / a p - x) := hmain
    _ = uCandidate p x y + DxuCandidate p x y * (y / a p - x) := by
      rw [hux, hdx]

lemma uCandidate_tangent_x_Q1_A2_to_diag_leTwo
    (p : ℝ) (hp1 : 1 < p) (hp2 : p < 2) {x y : ℝ}
    (hy_pos : 0 < y) (hx_lower : y < x) (hx_upper : x < y / a p) :
    uCandidate p y y ≤
      uCandidate p x y + DxuCandidate p x y * (y - x) := by
  have ha_pos : 0 < a p := by
    rw [a_eq_leTwo p hp1 hp2]
    exact div_pos (by linarith) (by linarith)
  have hQx : QuarterPlane x y := ⟨by linarith, le_of_lt hx_lower, by linarith⟩
  have hQy : QuarterPlane y y := ⟨hy_pos.le, le_rfl, by linarith⟩
  have hax : a p * x < y := by
    have hmul := mul_lt_mul_of_pos_left hx_upper ha_pos
    field_simp [ha_pos.ne'] at hmul
    simpa [mul_comm, mul_left_comm, mul_assoc] using hmul
  have hclx : closureA2 p x y := ⟨by linarith, le_of_lt hax, le_of_lt hx_lower⟩
  have hcly : closureA2 p y y := by
    have ha_lt : a p < 1 := a_lt_one_of_one_lt_of_lt_two p hp1 hp2
    exact ⟨hy_pos.le, by
      have h := mul_le_mul_of_nonneg_right ha_lt.le hy_pos.le
      simpa using h, le_rfl⟩
  have hnotx : ¬ closureA1 p x y := by
    intro h
    exact not_le_of_gt hax h.2.2
  have hux : uCandidate p x y = vLeTwo p x y := by
    rw [uCandidate_eq_Q1_leTwo p hQx]
    simp [auxFunction1, hnotx, hclx]
  have huy : uCandidate p y y = vLeTwo p y y := by
    rw [uCandidate_eq_Q1_leTwo p hQy, auxFunction1_eq_vLeTwo_leTwo p hp1 hp2 y y hcly]
  have hdx : DxuCandidate p x y = DxvLeTwo p x y := by
    rw [DxuCandidate_eq_Q1_leTwo p hQx]
    simp [DxauxFunction1, hnotx, hclx]
  have hderiv : HasDerivAt (fun t => vLeTwo p t y) (DxvLeTwo p x y) x := by
    have hsum : 0 < (x + y) / 2 := by linarith
    have hdiff : 0 < (x - y) / 2 := by linarith
    exact hasDerivAt_vLeTwo_x_of_pos_leTwo p x y hsum hdiff
  have hmain :
      vLeTwo p y y ≤ vLeTwo p x y + DxvLeTwo p x y * (y - x) := by
    apply vLeTwo_tangent_x_on_Icc_of_A2_leTwo
        (p := p) (hp1 := hp1) (hp2 := hp2)
        (lo := y) (hi := x) (x := x) (z := y) (y := y)
    · intro t ht
      have htI : t ∈ Set.Ioo y x := by
        simpa [interior_Icc] using ht
      have ht_pos : 0 < t := by linarith [hy_pos, htI.1]
      have hat : a p * t < y := by
        have ht_div : t < y / a p := lt_trans htI.2 hx_upper
        have hmul := mul_lt_mul_of_pos_left ht_div ha_pos
        field_simp [ha_pos.ne'] at hmul
        simpa [mul_comm, mul_left_comm, mul_assoc] using hmul
      exact ⟨ht_pos, hat, htI.1⟩
    · exact ⟨le_of_lt hx_lower, le_rfl⟩
    · exact ⟨le_rfl, le_of_lt hx_lower⟩
    · exact hderiv
  calc
    uCandidate p y y = vLeTwo p y y := huy
    _ ≤ vLeTwo p x y + DxvLeTwo p x y * (y - x) := hmain
    _ = uCandidate p x y + DxuCandidate p x y * (y - x) := by
      rw [hux, hdx]

lemma uCandidate_tangent_x_Q1_boundary_to_A2_leTwo
    (p : ℝ) (hp1 : 1 < p) (hp2 : p < 2) {z y : ℝ}
    (hy_pos : 0 < y) (hz_lower : y < z) (hz_upper : z < y / a p) :
    uCandidate p z y ≤
      uCandidate p (y / a p) y +
        DxuCandidate p (y / a p) y * (z - y / a p) := by
  have ha_pos : 0 < a p := by
    rw [a_eq_leTwo p hp1 hp2]
    exact div_pos (by linarith) (by linarith)
  have ha_lt : a p < 1 := a_lt_one_of_one_lt_of_lt_two p hp1 hp2
  have hb_pos : 0 < y / a p := div_pos hy_pos ha_pos
  have hy_lt_b : y < y / a p := by
    rw [div_eq_mul_inv]
    have hinv : 1 < (a p)⁻¹ := by
      rw [one_lt_inv₀ ha_pos]
      exact ha_lt
    nlinarith
  have hQb : QuarterPlane (y / a p) y :=
    ⟨hb_pos.le, le_of_lt hy_lt_b, by linarith⟩
  have hQz : QuarterPlane z y := ⟨by linarith, le_of_lt hz_lower, by linarith⟩
  have hboundary := horizontal_boundary_closureA1_closureA2_leTwo p y hp1 hp2 hy_pos
  have hclz : closureA2 p z y := by
    have haz : a p * z < y := by
      have hmul := mul_lt_mul_of_pos_left hz_upper ha_pos
      field_simp [ha_pos.ne'] at hmul
      simpa [mul_comm, mul_left_comm, mul_assoc] using hmul
    exact ⟨by linarith, le_of_lt haz, le_of_lt hz_lower⟩
  have hnotz : ¬ closureA1 p z y := by
    intro h
    have haz : a p * z < y := by
      have hmul := mul_lt_mul_of_pos_left hz_upper ha_pos
      field_simp [ha_pos.ne'] at hmul
      simpa [mul_comm, mul_left_comm, mul_assoc] using hmul
    exact not_le_of_gt haz h.2.2
  have hub : uCandidate p (y / a p) y = vLeTwo p (y / a p) y := by
    rw [uCandidate_eq_Q1_leTwo p hQb,
      auxFunction1_eq_vLeTwo_leTwo p hp1 hp2 (y / a p) y hboundary.2]
  have huz : uCandidate p z y = vLeTwo p z y := by
    rw [uCandidate_eq_Q1_leTwo p hQz]
    simp [auxFunction1, hnotz, hclz]
  have hdb : DxuCandidate p (y / a p) y = DxvLeTwo p (y / a p) y := by
    rw [DxuCandidate_eq_Q1_leTwo p hQb]
    exact auxFunction1_Dx_eq_DxvLeTwo_leTwo p hp1 hp2 (y / a p) y hboundary.2
  have hderiv : HasDerivAt (fun t => vLeTwo p t y)
      (DxvLeTwo p (y / a p) y) (y / a p) := by
    have hsum : 0 < (y / a p + y) / 2 := by linarith [hb_pos, hy_pos]
    have hdiff : 0 < (y / a p - y) / 2 := by linarith [hy_lt_b]
    exact hasDerivAt_vLeTwo_x_of_pos_leTwo p (y / a p) y hsum hdiff
  have hmain :
      vLeTwo p z y ≤
        vLeTwo p (y / a p) y + DxvLeTwo p (y / a p) y * (z - y / a p) := by
    apply vLeTwo_tangent_x_on_Icc_of_A2_leTwo
        (p := p) (hp1 := hp1) (hp2 := hp2)
        (lo := z) (hi := y / a p) (x := y / a p) (z := z) (y := y)
    · intro t ht
      have htI : t ∈ Set.Ioo z (y / a p) := by
        simpa [interior_Icc] using ht
      have ht_pos : 0 < t := by linarith [hy_pos, hz_lower, htI.1]
      have hat : a p * t < y := by
        have hmul : a p * t < a p * (y / a p) :=
          mul_lt_mul_of_pos_left htI.2 ha_pos
        have hac : a p * (y / a p) = y := by field_simp [ha_pos.ne']
        simpa [hac] using hmul
      exact ⟨ht_pos, hat, lt_trans hz_lower htI.1⟩
    · exact ⟨le_of_lt hz_upper, le_rfl⟩
    · exact ⟨le_rfl, le_of_lt hz_upper⟩
    · exact hderiv
  calc
    uCandidate p z y = vLeTwo p z y := huz
    _ ≤ vLeTwo p (y / a p) y + DxvLeTwo p (y / a p) y * (z - y / a p) := hmain
    _ = uCandidate p (y / a p) y +
        DxuCandidate p (y / a p) y * (z - y / a p) := by
      rw [hub, hdb]

lemma uCandidate_tangent_x_Q1_A1_to_A2_leTwo
    (p : ℝ) (hp1 : 1 < p) (hp2 : p < 2) {x z y : ℝ}
    (hy_pos : 0 < y) (hx_lower : y / a p < x)
    (hz_lower : y < z) (hz_upper : z < y / a p) :
    uCandidate p z y ≤
      uCandidate p x y + DxuCandidate p x y * (z - x) := by
  have hxb := uCandidate_tangent_x_Q1_A1_to_boundary_leTwo
    (p := p) (hp1 := hp1) (hp2 := hp2) (x := x) (y := y)
    hy_pos hx_lower
  have hbz := uCandidate_tangent_x_Q1_boundary_to_A2_leTwo
    (p := p) (hp1 := hp1) (hp2 := hp2) (z := z) (y := y)
    hy_pos hz_lower hz_upper
  have hd : DxuCandidate p x y ≤ DxuCandidate p (y / a p) y := by
    have ha_pos : 0 < a p := by
      rw [a_eq_leTwo p hp1 hp2]
      exact div_pos (by linarith) (by linarith)
    have ha_lt : a p < 1 := a_lt_one_of_one_lt_of_lt_two p hp1 hp2
    have hQx : QuarterPlane x y := by
      have hy_lt_b : y < y / a p := by
        rw [div_eq_mul_inv]
        have hinv : 1 < (a p)⁻¹ := by
          rw [one_lt_inv₀ ha_pos]
          exact ha_lt
        nlinarith
      exact ⟨by linarith, le_of_lt (lt_trans hy_lt_b hx_lower), by linarith⟩
    have hclx : closureA1 p x y := by
      have hay : y < a p * x := by
        have hmul := mul_lt_mul_of_pos_left hx_lower ha_pos
        field_simp [ha_pos.ne'] at hmul
        simpa [mul_comm, mul_left_comm, mul_assoc] using hmul
      exact ⟨by linarith, by linarith, le_of_lt hay⟩
    have hboundary := horizontal_boundary_closureA1_closureA2_leTwo p y hp1 hp2 hy_pos
    have hdx : DxuCandidate p x y = DxauxFunction1 p x y := by
      rw [DxuCandidate_eq_Q1_leTwo p hQx]
    have hdb : DxuCandidate p (y / a p) y = DxauxFunction1 p (y / a p) y := by
      have hQb : QuarterPlane (y / a p) y := by
        have hb_pos : 0 < y / a p := div_pos hy_pos ha_pos
        have hy_lt_b : y < y / a p := by
          rw [div_eq_mul_inv]
          have hinv : 1 < (a p)⁻¹ := by
            rw [one_lt_inv₀ ha_pos]
            exact ha_lt
          nlinarith
        exact ⟨hb_pos.le, le_of_lt hy_lt_b, by linarith⟩
      rw [DxuCandidate_eq_Q1_leTwo p hQb]
    have hle := DxauxFunction1_A1_le_boundary_leTwo
      (p := p) (hp1 := hp1) (hp2 := hp2) (x := x) (y := y)
      hy_pos (by
        have hy_lt_b : y < y / a p := by
          rw [div_eq_mul_inv]
          have hinv : 1 < (a p)⁻¹ := by
            rw [one_lt_inv₀ ha_pos]
            exact ha_lt
          nlinarith
        linarith) (by
        have hmul := mul_lt_mul_of_pos_left hx_lower ha_pos
        field_simp [ha_pos.ne'] at hmul
        simpa [mul_comm, mul_left_comm, mul_assoc] using hmul)
    rwa [hdx, hdb]
  exact tangent_glue_two_backward_leTwo_local
    (fun t => uCandidate p t y) (fun t => DxuCandidate p t y)
    (le_of_lt hz_upper) (le_of_lt hx_lower) hxb hbz hd

lemma uCandidate_tangent_x_Q1_boundary_to_diag_leTwo
    (p : ℝ) (hp1 : 1 < p) (hp2 : p < 2) {y : ℝ}
    (hy_pos : 0 < y) :
    uCandidate p y y ≤
      uCandidate p (y / a p) y +
        DxuCandidate p (y / a p) y * (y - y / a p) := by
  have ha_pos : 0 < a p := by
    rw [a_eq_leTwo p hp1 hp2]
    exact div_pos (by linarith) (by linarith)
  have ha_lt : a p < 1 := a_lt_one_of_one_lt_of_lt_two p hp1 hp2
  have hb_pos : 0 < y / a p := div_pos hy_pos ha_pos
  have hy_lt_b : y < y / a p := by
    rw [div_eq_mul_inv]
    have hinv : 1 < (a p)⁻¹ := by
      rw [one_lt_inv₀ ha_pos]
      exact ha_lt
    nlinarith
  have hQb : QuarterPlane (y / a p) y :=
    ⟨hb_pos.le, le_of_lt hy_lt_b, by linarith⟩
  have hQy : QuarterPlane y y := ⟨hy_pos.le, le_rfl, by linarith⟩
  have hboundary := horizontal_boundary_closureA1_closureA2_leTwo p y hp1 hp2 hy_pos
  have hcly : closureA2 p y y := by
    exact ⟨hy_pos.le, by
      have h := mul_le_mul_of_nonneg_right ha_lt.le hy_pos.le
      simpa using h, le_rfl⟩
  have hub : uCandidate p (y / a p) y = vLeTwo p (y / a p) y := by
    rw [uCandidate_eq_Q1_leTwo p hQb,
      auxFunction1_eq_vLeTwo_leTwo p hp1 hp2 (y / a p) y hboundary.2]
  have huy : uCandidate p y y = vLeTwo p y y := by
    rw [uCandidate_eq_Q1_leTwo p hQy, auxFunction1_eq_vLeTwo_leTwo p hp1 hp2 y y hcly]
  have hdb : DxuCandidate p (y / a p) y = DxvLeTwo p (y / a p) y := by
    rw [DxuCandidate_eq_Q1_leTwo p hQb]
    exact auxFunction1_Dx_eq_DxvLeTwo_leTwo p hp1 hp2 (y / a p) y hboundary.2
  have hderiv : HasDerivAt (fun t => vLeTwo p t y)
      (DxvLeTwo p (y / a p) y) (y / a p) := by
    have hsum : 0 < (y / a p + y) / 2 := by linarith [hb_pos, hy_pos]
    have hdiff : 0 < (y / a p - y) / 2 := by linarith [hy_lt_b]
    exact hasDerivAt_vLeTwo_x_of_pos_leTwo p (y / a p) y hsum hdiff
  have hmain :
      vLeTwo p y y ≤
        vLeTwo p (y / a p) y + DxvLeTwo p (y / a p) y * (y - y / a p) := by
    apply vLeTwo_tangent_x_on_Icc_of_A2_leTwo
        (p := p) (hp1 := hp1) (hp2 := hp2)
        (lo := y) (hi := y / a p) (x := y / a p) (z := y) (y := y)
    · intro t ht
      have htI : t ∈ Set.Ioo y (y / a p) := by
        simpa [interior_Icc] using ht
      have ht_pos : 0 < t := by linarith [hy_pos, htI.1]
      have hat : a p * t < y := by
        have hmul : a p * t < a p * (y / a p) :=
          mul_lt_mul_of_pos_left htI.2 ha_pos
        have hac : a p * (y / a p) = y := by field_simp [ha_pos.ne']
        simpa [hac] using hmul
      exact ⟨ht_pos, hat, htI.1⟩
    · exact ⟨le_of_lt hy_lt_b, le_rfl⟩
    · exact ⟨le_rfl, le_of_lt hy_lt_b⟩
    · exact hderiv
  calc
    uCandidate p y y = vLeTwo p y y := huy
    _ ≤ vLeTwo p (y / a p) y + DxvLeTwo p (y / a p) y * (y - y / a p) := hmain
    _ = uCandidate p (y / a p) y +
        DxuCandidate p (y / a p) y * (y - y / a p) := by
      rw [hub, hdb]

lemma uCandidate_tangent_x_Q1_A1_to_diag_leTwo
    (p : ℝ) (hp1 : 1 < p) (hp2 : p < 2) {x y : ℝ}
    (hy_pos : 0 < y) (hx_lower : y / a p < x) :
    uCandidate p y y ≤
      uCandidate p x y + DxuCandidate p x y * (y - x) := by
  have hxb := uCandidate_tangent_x_Q1_A1_to_boundary_leTwo
    (p := p) (hp1 := hp1) (hp2 := hp2) (x := x) (y := y)
    hy_pos hx_lower
  have hby := uCandidate_tangent_x_Q1_boundary_to_diag_leTwo
    (p := p) (hp1 := hp1) (hp2 := hp2) (y := y) hy_pos
  have hd : DxuCandidate p x y ≤ DxuCandidate p (y / a p) y := by
    have ha_pos : 0 < a p := by
      rw [a_eq_leTwo p hp1 hp2]
      exact div_pos (by linarith) (by linarith)
    have ha_lt : a p < 1 := a_lt_one_of_one_lt_of_lt_two p hp1 hp2
    have hQx : QuarterPlane x y := by
      have hy_lt_b : y < y / a p := by
        rw [div_eq_mul_inv]
        have hinv : 1 < (a p)⁻¹ := by
          rw [one_lt_inv₀ ha_pos]
          exact ha_lt
        nlinarith
      exact ⟨by linarith, le_of_lt (lt_trans hy_lt_b hx_lower), by linarith⟩
    have hQb : QuarterPlane (y / a p) y := by
      have hb_pos : 0 < y / a p := div_pos hy_pos ha_pos
      have hy_lt_b : y < y / a p := by
        rw [div_eq_mul_inv]
        have hinv : 1 < (a p)⁻¹ := by
          rw [one_lt_inv₀ ha_pos]
          exact ha_lt
        nlinarith
      exact ⟨hb_pos.le, le_of_lt hy_lt_b, by linarith⟩
    have hdx : DxuCandidate p x y = DxauxFunction1 p x y := by
      rw [DxuCandidate_eq_Q1_leTwo p hQx]
    have hdb : DxuCandidate p (y / a p) y = DxauxFunction1 p (y / a p) y := by
      rw [DxuCandidate_eq_Q1_leTwo p hQb]
    have hle := DxauxFunction1_A1_le_boundary_leTwo
      (p := p) (hp1 := hp1) (hp2 := hp2) (x := x) (y := y)
      hy_pos (by
        have hy_lt_b : y < y / a p := by
          rw [div_eq_mul_inv]
          have hinv : 1 < (a p)⁻¹ := by
            rw [one_lt_inv₀ ha_pos]
            exact ha_lt
          nlinarith
        linarith) (by
        have hmul := mul_lt_mul_of_pos_left hx_lower ha_pos
        field_simp [ha_pos.ne'] at hmul
        simpa [mul_comm, mul_left_comm, mul_assoc] using hmul)
    rwa [hdx, hdb]
  exact tangent_glue_two_backward_leTwo_local
    (fun t => uCandidate p t y) (fun t => DxuCandidate p t y)
    (by
      have ha_pos : 0 < a p := by
        rw [a_eq_leTwo p hp1 hp2]
        exact div_pos (by linarith) (by linarith)
      have ha_lt : a p < 1 := a_lt_one_of_one_lt_of_lt_two p hp1 hp2
      have hlt : y < y / a p := by
        rw [div_eq_mul_inv]
        have hinv : 1 < (a p)⁻¹ := by
          rw [one_lt_inv₀ ha_pos]
          exact ha_lt
        nlinarith
      exact le_of_lt hlt)
    (le_of_lt hx_lower) hxb hby hd

lemma uCandidate_tangent_x_diag_to_Q3_A2_leTwo
    (p : ℝ) (hp1 : 1 < p) (hp2 : p < 2) {z y : ℝ}
    (hy_pos : 0 < y) (hz_lower : a p * y < z) (hz_upper : z < y) :
    uCandidate p z y ≤
      uCandidate p y y + DxuCandidate p y y * (z - y) := by
  have hzy := uCandidate_tangent_x_Q3_A2_to_diag_leTwo
    (p := p) (hp1 := hp1) (hp2 := hp2) (x := z) (y := y)
    hy_pos hz_lower hz_upper
  -- Same A2 concavity segment, but based at the diagonal endpoint.
  have ha_nonneg : 0 ≤ a p := a_nonneg_of_one_lt_of_lt_two p hp1 hp2
  have hQz : QuarterPlane3 z y := ⟨hy_pos.le, by
    have haxy_nonneg : 0 ≤ a p * y := mul_nonneg ha_nonneg hy_pos.le
    linarith, le_of_lt hz_upper⟩
  have hQy : QuarterPlane y y := ⟨hy_pos.le, le_rfl, by linarith⟩
  have hclz : closureA2 p y z := ⟨hy_pos.le, le_of_lt hz_lower, le_of_lt hz_upper⟩
  have hcly : closureA2 p y y := by
    have ha_lt : a p < 1 := a_lt_one_of_one_lt_of_lt_two p hp1 hp2
    exact ⟨hy_pos.le, by
      have h := mul_le_mul_of_nonneg_right ha_lt.le hy_pos.le
      simpa using h, le_rfl⟩
  have huz : uCandidate p z y = vLeTwo p y z := by
    rw [uCandidate_eq_Q3_leTwo p hQz, auxFunction1_eq_vLeTwo_leTwo p hp1 hp2 y z hclz]
  have huy : uCandidate p y y = vLeTwo p y y := by
    rw [uCandidate_eq_Q1_leTwo p hQy, auxFunction1_eq_vLeTwo_leTwo p hp1 hp2 y y hcly]
  have hdy : DxuCandidate p y y = DxvLeTwo p y y := by
    rw [DxuCandidate_eq_Q1_leTwo p hQy]
    exact auxFunction1_Dx_eq_DxvLeTwo_leTwo p hp1 hp2 y y hcly
  have hdiag : DxvLeTwo p y y = DyvLeTwo p y y := by
    have hzero : (0 : ℝ) ^ (p - 1) = 0 := Real.zero_rpow (by linarith)
    simp [DxvLeTwo, DyvLeTwo, hy_pos, abs_of_pos hy_pos, hzero]
  have hderiv : HasDerivAt (fun t => vLeTwo p y t) (DyvLeTwo p y y) y := by
    have hsum : 0 < (y + y) / 2 := by linarith
    have hdiff_nonneg : 0 ≤ (y - y) / 2 := by norm_num
    -- use the x-derivative diagonal lemma and symmetry of formulas at the diagonal
    have hxder := hasDerivAt_vLeTwo_x_on_diag_pos_leTwo p hp1 y hy_pos
    -- direct y-derivative at the cusp follows from the abs-rpow derivative as in the x lemma.
    let g : ℝ → ℝ := fun t =>
      |((y + t) / 2)| ^ p - coeffLeTwo p * |((y - t) / 2)| ^ p
    have hEq : (fun t => vLeTwo p y t) = g := by
      ext t
      simp [vLeTwo, g]
    have hbase_sum :
        HasDerivAt (fun t : ℝ => (y + t) / 2) (1 / 2) y := by
      simpa [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using
        (((hasDerivAt_id y).const_add y).const_mul (1 / 2 : ℝ))
    have hbase_diff :
        HasDerivAt (fun t : ℝ => (y - t) / 2) (-(1 / 2)) y := by
      simpa [sub_eq_add_neg, div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using
        ((((hasDerivAt_id y).neg).const_add y).const_mul (1 / 2 : ℝ))
    have hpow_sum :
        HasDerivAt (fun t : ℝ => |((y + t) / 2)| ^ p)
          (p * (y ^ (p - 2) * y) * (1 / 2)) y := by
      have h :
          HasDerivAt (fun s : ℝ => |s| ^ p)
            (p * |(y + y) / 2| ^ (p - 2) * ((y + y) / 2)) ((y + y) / 2) :=
        hasDerivAt_abs_rpow ((y + y) / 2) hp1
      have hcomp := h.comp y hbase_sum
      refine hcomp.congr_deriv ?_
      simp [abs_of_pos hy_pos]
      ring
    have hpow_diff :
        HasDerivAt (fun t : ℝ => |((y - t) / 2)| ^ p) 0 y := by
      have h :
          HasDerivAt (fun s : ℝ => |s| ^ p)
            (p * |(y - y) / 2| ^ (p - 2) * ((y - y) / 2)) ((y - y) / 2) :=
        hasDerivAt_abs_rpow ((y - y) / 2) hp1
      have hcomp := h.comp y hbase_diff
      simpa using hcomp
    have hd :
        HasDerivAt g (p * (y ^ (p - 2) * y) * (1 / 2) - coeffLeTwo p * 0) y := by
      dsimp [g]
      exact hpow_sum.sub (hpow_diff.const_mul (coeffLeTwo p))
    rw [hEq]
    refine hd.congr_deriv ?_
    have hpow : y ^ (p - 2) * y = y ^ (p - 1) := by
      calc
        y ^ (p - 2) * y = y ^ (p - 2) * y ^ (1 : ℝ) := by rw [Real.rpow_one]
        _ = y ^ ((p - 2) + 1) := by rw [← Real.rpow_add hy_pos]
        _ = y ^ (p - 1) := by ring_nf
    have hzero : (0 : ℝ) ^ (p - 1) = 0 := Real.zero_rpow (by linarith)
    simp [DyvLeTwo, hy_pos, abs_of_pos hy_pos, hzero]
    rw [hpow]
    ring
  have hmain :
      vLeTwo p y z ≤ vLeTwo p y y + DyvLeTwo p y y * (z - y) := by
    apply vLeTwo_tangent_y_on_Icc_of_A2_leTwo
        (p := p) (hp1 := hp1) (hp2 := hp2)
        (lo := z) (hi := y) (x := y) (y := y) (z := z)
    · intro t ht
      have htI : t ∈ Set.Ioo z y := by
        simpa [interior_Icc] using ht
      exact ⟨hy_pos, lt_trans hz_lower htI.1, htI.2⟩
    · exact ⟨le_of_lt hz_upper, le_rfl⟩
    · exact ⟨le_rfl, le_of_lt hz_upper⟩
    · exact hderiv
  calc
    uCandidate p z y = vLeTwo p y z := huz
    _ ≤ vLeTwo p y y + DyvLeTwo p y y * (z - y) := hmain
    _ = uCandidate p y y + DxuCandidate p y y * (z - y) := by
      rw [huy, hdy, hdiag]

lemma uCandidate_tangent_x_Q3_A1_to_antidiag_leTwo
    (p : ℝ) (hp1 : 1 < p) (hp2 : p < 2) {x y : ℝ}
    (hy_pos : 0 < y) (hx_lower : -y < x) (hx_upper : x < a p * y) :
    uCandidate p (-y) y ≤
      uCandidate p x y + DxuCandidate p x y * ((-y) - x) := by
  have ha_lt : a p < 1 := a_lt_one_of_one_lt_of_lt_two p hp1 hp2
  have hQx : QuarterPlane3 x y := ⟨hy_pos.le, le_of_lt hx_lower, by
    have hc_lt_y : a p * y < y := by
      simpa using mul_lt_mul_of_pos_right ha_lt hy_pos
    exact le_of_lt (lt_trans hx_upper hc_lt_y)⟩
  have hQa : QuarterPlane2 (-y) y := ⟨by linarith, by linarith, by linarith⟩
  have hclx : closureA1 p y x := ⟨hy_pos.le, le_of_lt hx_lower, le_of_lt hx_upper⟩
  have hcla : closureA1 p y (-y) := by
    have ha_nonneg : 0 ≤ a p := a_nonneg_of_one_lt_of_lt_two p hp1 hp2
    refine ⟨hy_pos.le, le_rfl, ?_⟩
    have hnonneg : 0 ≤ a p * y := mul_nonneg ha_nonneg hy_pos.le
    linarith
  have hux : uCandidate p x y = uA1 p y x := by
    rw [uCandidate_eq_Q3_leTwo p hQx]
    simp [auxFunction1, hclx]
  have hua : uCandidate p (-y) y = uA1 p y (-y) := by
    rw [uCandidate_eq_Q2_leTwo p hQa]
    simp [auxFunction1, hcla]
  have hdx : DxuCandidate p x y = DyuA1 p y x := by
    rw [DxuCandidate_eq_Q3_leTwo p hp1 hp2 hQx]
    simp [DyauxFunction1, hclx]
  apply le_of_eq
  calc
    uCandidate p (-y) y = uA1 p y (-y) := hua
    _ = uA1 p y x + DyuA1 p y x * ((-y) - x) :=
      uA1_affine_y_tangent_leTwo p y x (-y) hy_pos
    _ = uCandidate p x y + DxuCandidate p x y * ((-y) - x) := by
      rw [hux, hdx]

lemma uCandidate_tangent_x_antidiag_to_Q2_leTwo
    (p : ℝ) (hp1 : 1 < p) (hp2 : p < 2) {z y : ℝ}
    (hy_pos : 0 < y) (hz_left : z < -y) :
    uCandidate p z y ≤
      uCandidate p (-y) y + DxuCandidate p (-y) y * (z - (-y)) := by
  have ha_nonneg : 0 ≤ a p := a_nonneg_of_one_lt_of_lt_two p hp1 hp2
  have hQz : QuarterPlane2 z y := ⟨by linarith, by linarith, by linarith⟩
  have hQa : QuarterPlane2 (-y) y := ⟨by linarith, by linarith, by linarith⟩
  have hclz : closureA1 p (-z) (-y) := by
    refine ⟨by linarith, by linarith, ?_⟩
    have hmul : a p * z ≤ 0 := mul_nonpos_of_nonneg_of_nonpos ha_nonneg (by linarith)
    linarith
  have hcla : closureA1 p y (-y) := by
    refine ⟨hy_pos.le, le_rfl, ?_⟩
    have hnonneg : 0 ≤ a p * y := mul_nonneg ha_nonneg hy_pos.le
    linarith
  have huz : uCandidate p z y = uA1 p (-z) (-y) := by
    rw [uCandidate_eq_Q2_leTwo p hQz]
    simp [auxFunction1, hclz]
  have hua : uCandidate p (-y) y = uA1 p y (-y) := by
    rw [uCandidate_eq_Q2_leTwo p hQa]
    simp [auxFunction1, hcla]
  have hda : DxuCandidate p (-y) y = -DxuA1 p y (-y) := by
    rw [DxuCandidate_eq_Q2_leTwo p hQa]
    simp [DxauxFunction1, hcla]
  have hmain :
      uA1 p (-z) (-y) ≤
        uA1 p y (-y) + DxuA1 p y (-y) * ((-z) - y) := by
    apply uA1_tangent_x_on_Icc_leTwo
        (p := p) (hp1 := hp1) (hp2 := hp2)
        (lo := y) (hi := -z) (x := y) (z := -z) (y := -y)
    · intro t ht
      exact lt_of_lt_of_le hy_pos ht.1
    · intro t ht
      have htI : t ∈ Set.Ioo y (-z) := by
        simpa [interior_Icc] using ht
      linarith [hy_pos, htI.1]
    · exact ⟨le_rfl, le_of_lt (by linarith)⟩
    · exact ⟨le_of_lt (by linarith), le_rfl⟩
  calc
    uCandidate p z y = uA1 p (-z) (-y) := huz
    _ ≤ uA1 p y (-y) + DxuA1 p y (-y) * ((-z) - y) := hmain
    _ = uCandidate p (-y) y + DxuCandidate p (-y) y * (z - (-y)) := by
      rw [hua, hda]
      ring

lemma DxuCandidate_Q1_A2_le_diag_leTwo
    (p : ℝ) (hp1 : 1 < p) (hp2 : p < 2) {x y : ℝ}
    (hy_pos : 0 < y) (hx_lower : y < x) (hx_upper : x < y / a p) :
    DxuCandidate p x y ≤ DxuCandidate p y y := by
  have ha_pos : 0 < a p := by
    rw [a_eq_leTwo p hp1 hp2]
    exact div_pos (by linarith) (by linarith)
  have hQx : QuarterPlane x y := ⟨by linarith, le_of_lt hx_lower, by linarith⟩
  have hQy : QuarterPlane y y := ⟨hy_pos.le, le_rfl, by linarith⟩
  have hax : a p * x < y := by
    have hmul := mul_lt_mul_of_pos_left hx_upper ha_pos
    field_simp [ha_pos.ne'] at hmul
    simpa [mul_comm, mul_left_comm, mul_assoc] using hmul
  have hclx : closureA2 p x y := ⟨by linarith, le_of_lt hax, le_of_lt hx_lower⟩
  have hcly : closureA2 p y y := by
    have ha_lt : a p < 1 := a_lt_one_of_one_lt_of_lt_two p hp1 hp2
    exact ⟨hy_pos.le, by
      have h := mul_le_mul_of_nonneg_right ha_lt.le hy_pos.le
      simpa using h, le_rfl⟩
  have hnotx : ¬ closureA1 p x y := by
    intro h
    exact not_le_of_gt hax h.2.2
  have hdx : DxuCandidate p x y = DxvLeTwo p x y := by
    rw [DxuCandidate_eq_Q1_leTwo p hQx]
    simp [DxauxFunction1, hnotx, hclx]
  have hdy : DxuCandidate p y y = DxvLeTwo p y y := by
    rw [DxuCandidate_eq_Q1_leTwo p hQy]
    exact auxFunction1_Dx_eq_DxvLeTwo_leTwo p hp1 hp2 y y hcly
  have hanti :
      AntitoneOn (fun t : ℝ => DxvLeTwo p t y) (Set.Icc y x) := by
    have hcont : ContinuousOn (fun t : ℝ => DxvLeTwo p t y) (Set.Icc y x) := by
      let g : ℝ → ℝ := fun t =>
        ((t + y) / 2) ^ (p - 1) * (p / 2) -
          coeffLeTwo p * ((t - y) / 2) ^ (p - 1) * (p / 2)
      have hg : ContinuousOn g (Set.Icc y x) := by
        dsimp [g]
        apply ContinuousOn.sub
        · exact (((continuousOn_id.add continuousOn_const).div_const 2).rpow_const
            (fun t ht => Or.inl (ne_of_gt (by
              change 0 < (t + y) / 2
              linarith [hy_pos, ht.1])))).mul continuousOn_const
        · exact (continuousOn_const.mul
            (((continuousOn_id.sub continuousOn_const).div_const 2).rpow_const
              (fun _ _ => Or.inr (by linarith)))).mul continuousOn_const
      refine ContinuousOn.congr hg ?_
      intro t ht
      have ht_pos : 0 < t := lt_of_lt_of_le hy_pos ht.1
      have hsum : 0 < (t + y) / 2 := by linarith [ht_pos, hy_pos]
      have hdiff_nonneg : 0 ≤ (t - y) / 2 := by linarith [ht.1]
      by_cases hdiff : 0 < (t - y) / 2
      · simp [g, DxvLeTwo, ht_pos, abs_of_pos hsum, abs_of_pos hdiff]
      · have hdiff_zero : (t - y) / 2 = 0 :=
          le_antisymm (le_of_not_gt hdiff) hdiff_nonneg
        have ht_eq : t = y := by linarith
        subst t
        have hp_ne : p - 1 ≠ 0 := by linarith
        simp [g, DxvLeTwo, hy_pos, abs_of_pos hy_pos, Real.zero_rpow hp_ne]
    refine antitoneOn_of_hasDerivWithinAt_nonpos
      (D := Set.Icc y x)
      (f := fun t : ℝ => DxvLeTwo p t y)
      (f' := fun t : ℝ => deriv (fun s => DxvLeTwo p s y) t)
      (convex_Icc y x) hcont ?_ ?_
    · intro t ht
      have htI : t ∈ Set.Ioo y x := by
        simpa [interior_Icc] using ht
      have hsum : 0 < (t + y) / 2 := by linarith [hy_pos, htI.1]
      have hdiff : 0 < (t - y) / 2 := by linarith [htI.1]
      exact (differentiableAt_DxvLeTwo_x_of_pos_leTwo p t y hsum hdiff).hasDerivAt.hasDerivWithinAt
    · intro t ht
      have htI : t ∈ Set.Ioo y x := by
        simpa [interior_Icc] using ht
      have h_at : a p * t < y := by
        have ht_div : t < y / a p := lt_trans htI.2 hx_upper
        have hmul := mul_lt_mul_of_pos_left ht_div ha_pos
        field_simp [ha_pos.ne'] at hmul
        simpa [mul_comm, mul_left_comm, mul_assoc] using hmul
      exact deriv_DxvLeTwo_x_nonpos_leTwo p hp1 hp2 t y
        ⟨lt_trans hy_pos htI.1, h_at, htI.1⟩
  have hle := hanti ⟨le_rfl, le_of_lt hx_lower⟩ ⟨le_of_lt hx_lower, le_rfl⟩
    (le_of_lt hx_lower)
  rwa [hdx, hdy]

lemma DxuCandidate_Q3_A2_le_boundary_leTwo
    (p : ℝ) (hp1 : 1 < p) (hp2 : p < 2) {x y : ℝ}
    (hy_pos : 0 < y) (hx_lower : a p * y < x) (hx_upper : x < y) :
    DxuCandidate p x y ≤ DxuCandidate p (a p * y) y := by
  have hdiag := DxuCandidate_diag_le_Q3_A2_leTwo
    (p := p) (hp1 := hp1) (hp2 := hp2) (x := x) (y := y)
    hy_pos hx_lower hx_upper
  have hbd := DxuCandidate_diag_le_Q3_A1_boundary_leTwo
    (p := p) (hp1 := hp1) (hp2 := hp2) (y := y) hy_pos
  -- On the A2 strip the derivative is antitone, so the right endpoint has
  -- smaller derivative than the left boundary.
  have ha_pos : 0 < a p := by
    rw [a_eq_leTwo p hp1 hp2]
    exact div_pos (by linarith) (by linarith)
  have hQx : QuarterPlane3 x y := ⟨hy_pos.le, by
    have ha_nonneg : 0 ≤ a p := ha_pos.le
    have haxy_nonneg : 0 ≤ a p * y := mul_nonneg ha_nonneg hy_pos.le
    linarith, le_of_lt hx_upper⟩
  have hQc : QuarterPlane3 (a p * y) y := ⟨hy_pos.le, by
    have hnonneg : 0 ≤ a p * y := mul_nonneg ha_pos.le hy_pos.le
    linarith, by
      have ha_lt : a p < 1 := a_lt_one_of_one_lt_of_lt_two p hp1 hp2
      exact (mul_le_mul_of_nonneg_right ha_lt.le hy_pos.le).trans_eq (one_mul y)⟩
  have hclx : closureA2 p y x := ⟨hy_pos.le, le_of_lt hx_lower, le_of_lt hx_upper⟩
  have hclc1 : closureA1 p y (a p * y) := ⟨hy_pos.le, by
    have hnonneg : 0 ≤ a p * y := mul_nonneg ha_pos.le hy_pos.le
    linarith, le_rfl⟩
  have hdx : DxuCandidate p x y = DyvLeTwo p y x := by
    rw [DxuCandidate_eq_Q3_leTwo p hp1 hp2 hQx]
    have hnot : ¬ closureA1 p y x := by
      intro h
      exact not_le_of_gt hx_lower h.2.2
    simp [DyauxFunction1, hnot, hclx]
  have hdc : DxuCandidate p (a p * y) y = DyuA1 p y (a p * y) := by
    rw [DxuCandidate_eq_Q3_leTwo p hp1 hp2 hQc]
    simp [DyauxFunction1, hclc1]
  have hglue : DyuA1 p y (a p * y) = DyvLeTwo p y (a p * y) :=
    DyuA1_eq_DyvLeTwo_on_A1A2_boundary_leTwo p y hp1 hp2 hy_pos
  have hmono : DyvLeTwo p y x ≤ DyvLeTwo p y (a p * y) := by
    have hanti := DyvLeTwo_diag_le_DyvLeTwo_Q3_A2_closed_leTwo
      (p := p) (hp1 := hp1) (hp2 := hp2) (x := x) (y := y)
      hy_pos (le_of_lt hx_lower) hx_upper
    have hanti_c := DyvLeTwo_diag_le_DyvLeTwo_Q3_A2_closed_leTwo
      (p := p) (hp1 := hp1) (hp2 := hp2) (x := a p * y) (y := y)
      hy_pos le_rfl (by
        have ha_lt : a p < 1 := a_lt_one_of_one_lt_of_lt_two p hp1 hp2
        simpa using mul_lt_mul_of_pos_right ha_lt hy_pos)
    -- Direct antitonicity on `[a*y,x]`.
    have hantiOn :
        AntitoneOn (fun t : ℝ => DyvLeTwo p y t) (Set.Icc (a p * y) x) := by
      have hcont : ContinuousOn (fun t : ℝ => DyvLeTwo p y t) (Set.Icc (a p * y) x) := by
        let g : ℝ → ℝ := fun t =>
          ((y + t) / 2) ^ (p - 1) * (p / 2) +
            coeffLeTwo p * ((y - t) / 2) ^ (p - 1) * (p / 2)
        have hg : ContinuousOn g (Set.Icc (a p * y) x) := by
          dsimp [g]
          apply ContinuousOn.add
          · exact (((continuousOn_const.add continuousOn_id).div_const 2).rpow_const
              (fun t ht => Or.inl (ne_of_gt (by
                change 0 < (y + t) / 2
                have hnonneg : 0 ≤ a p * y := mul_nonneg ha_pos.le hy_pos.le
                linarith [hy_pos, hnonneg, ht.1])))).mul continuousOn_const
          · exact (continuousOn_const.mul
              (((continuousOn_const.sub continuousOn_id).div_const 2).rpow_const
                (fun t ht => Or.inl (ne_of_gt (by
                  change 0 < (y - t) / 2
                  linarith [ht.2, hx_upper]))))).mul continuousOn_const
        refine ContinuousOn.congr hg ?_
        intro t ht
        have hsum : 0 < (y + t) / 2 := by
          have hnonneg : 0 ≤ a p * y := mul_nonneg ha_pos.le hy_pos.le
          linarith [hy_pos, hnonneg, ht.1]
        have hdiff : 0 < (y - t) / 2 := by linarith [ht.2, hx_upper]
        simp [g, DyvLeTwo, hy_pos, abs_of_pos hsum, abs_of_pos hdiff]
      refine antitoneOn_of_hasDerivWithinAt_nonpos
        (D := Set.Icc (a p * y) x)
        (f := fun t : ℝ => DyvLeTwo p y t)
        (f' := fun t : ℝ => deriv (fun s => DyvLeTwo p y s) t)
        (convex_Icc (a p * y) x) hcont ?_ ?_
      · intro t ht
        have htI : t ∈ Set.Ioo (a p * y) x := by
          simpa [interior_Icc] using ht
        have hsum : 0 < (y + t) / 2 := by
          have hnonneg : 0 ≤ a p * y := mul_nonneg ha_pos.le hy_pos.le
          linarith [hy_pos, hnonneg, htI.1]
        have hdiff : 0 < (y - t) / 2 := by linarith [htI.2, hx_upper]
        exact (differentiableAt_DyvLeTwo_y_of_pos_leTwo p y t hsum hdiff).hasDerivAt.hasDerivWithinAt
      · intro t ht
        have htI : t ∈ Set.Ioo (a p * y) x := by
          simpa [interior_Icc] using ht
        exact deriv_DyvLeTwo_y_nonpos_leTwo p hp1 hp2 y t
          ⟨hy_pos, htI.1, lt_trans htI.2 hx_upper⟩
    exact hantiOn ⟨le_rfl, le_of_lt hx_lower⟩ ⟨le_of_lt hx_lower, le_rfl⟩
      (le_of_lt hx_lower)
  rw [hdx, hdc, hglue]
  exact hmono

lemma DxuCandidate_Q3_A1_eq_antidiag_leTwo
    (p : ℝ) (hp1 : 1 < p) (hp2 : p < 2) {x y : ℝ}
    (hy_pos : 0 < y) (hx_lower : -y < x) (hx_upper : x < a p * y) :
    DxuCandidate p x y = DxuCandidate p (-y) y := by
  have ha_nonneg : 0 ≤ a p := a_nonneg_of_one_lt_of_lt_two p hp1 hp2
  have ha_lt : a p < 1 := a_lt_one_of_one_lt_of_lt_two p hp1 hp2
  have hQx : QuarterPlane3 x y := ⟨hy_pos.le, le_of_lt hx_lower, by
    have hc_lt_y : a p * y < y := by
      simpa using mul_lt_mul_of_pos_right ha_lt hy_pos
    exact le_of_lt (lt_trans hx_upper hc_lt_y)⟩
  have hQa : QuarterPlane2 (-y) y := ⟨by linarith, by linarith, by linarith⟩
  have hclx : closureA1 p y x := ⟨hy_pos.le, le_of_lt hx_lower, le_of_lt hx_upper⟩
  have hcla : closureA1 p y (-y) := by
    refine ⟨hy_pos.le, le_rfl, ?_⟩
    have hnonneg : 0 ≤ a p * y := mul_nonneg ha_nonneg hy_pos.le
    linarith
  have hdx : DxuCandidate p x y = DyuA1 p y x := by
    rw [DxuCandidate_eq_Q3_leTwo p hp1 hp2 hQx]
    simp [DyauxFunction1, hclx]
  have hda : DxuCandidate p (-y) y = DyuA1 p y (-y) := by
    rw [DxuCandidate_eq_Q2_leTwo p hQa]
    have hrel := DxauxFunction1_eq_neg_DyauxFunction1_on_antidiag_leTwo
      p hp1 hp2 y hy_pos.le
    have hdy : DyauxFunction1 p y (-y) = DyuA1 p y (-y) := by
      simp [DyauxFunction1, hcla]
    simp only [neg_neg]
    rw [hrel, hdy]
    ring
  rw [hdx, hda]
  simp [DyuA1, hy_pos]

lemma uCandidate_tangent_x_diag_to_Q3_A2_boundary_leTwo
    (p : ℝ) (hp1 : 1 < p) (hp2 : p < 2) {y : ℝ}
    (hy_pos : 0 < y) :
    uCandidate p (a p * y) y ≤
      uCandidate p y y + DxuCandidate p y y * (a p * y - y) := by
  have ha_pos : 0 < a p := by
    rw [a_eq_leTwo p hp1 hp2]
    exact div_pos (by linarith) (by linarith)
  have ha_lt : a p < 1 := a_lt_one_of_one_lt_of_lt_two p hp1 hp2
  have hc_lt_y : a p * y < y := by
    simpa using mul_lt_mul_of_pos_right ha_lt hy_pos
  have hc_pos : 0 < a p * y := mul_pos ha_pos hy_pos
  have hQc : QuarterPlane3 (a p * y) y := ⟨hy_pos.le, by linarith, le_of_lt hc_lt_y⟩
  have hQy : QuarterPlane y y := ⟨hy_pos.le, le_rfl, by linarith⟩
  have hclc : closureA2 p y (a p * y) := ⟨hy_pos.le, le_rfl, le_of_lt hc_lt_y⟩
  have hcly : closureA2 p y y := ⟨hy_pos.le, le_of_lt hc_lt_y, le_rfl⟩
  have huc : uCandidate p (a p * y) y = vLeTwo p y (a p * y) := by
    rw [uCandidate_eq_Q3_leTwo p hQc,
      auxFunction1_eq_vLeTwo_leTwo p hp1 hp2 y (a p * y) hclc]
  have huy : uCandidate p y y = vLeTwo p y y := by
    rw [uCandidate_eq_Q1_leTwo p hQy,
      auxFunction1_eq_vLeTwo_leTwo p hp1 hp2 y y hcly]
  have hdy : DxuCandidate p y y = DxvLeTwo p y y := by
    rw [DxuCandidate_eq_Q1_leTwo p hQy]
    exact auxFunction1_Dx_eq_DxvLeTwo_leTwo p hp1 hp2 y y hcly
  have hdiag : DxvLeTwo p y y = DyvLeTwo p y y := by
    have hzero : (0 : ℝ) ^ (p - 1) = 0 := Real.zero_rpow (by linarith)
    simp [DxvLeTwo, DyvLeTwo, hy_pos, abs_of_pos hy_pos, hzero]
  have hderiv : HasDerivAt (fun t => vLeTwo p y t) (DyvLeTwo p y y) y := by
    -- same diagonal derivative in the second coordinate as above
    let g : ℝ → ℝ := fun t =>
      |((y + t) / 2)| ^ p - coeffLeTwo p * |((y - t) / 2)| ^ p
    have hEq : (fun t => vLeTwo p y t) = g := by
      ext t
      simp [vLeTwo, g]
    have hbase_sum :
        HasDerivAt (fun t : ℝ => (y + t) / 2) (1 / 2) y := by
      simpa [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using
        (((hasDerivAt_id y).const_add y).const_mul (1 / 2 : ℝ))
    have hbase_diff :
        HasDerivAt (fun t : ℝ => (y - t) / 2) (-(1 / 2)) y := by
      simpa [sub_eq_add_neg, div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using
        ((((hasDerivAt_id y).neg).const_add y).const_mul (1 / 2 : ℝ))
    have hpow_sum :
        HasDerivAt (fun t : ℝ => |((y + t) / 2)| ^ p)
          (p * (y ^ (p - 2) * y) * (1 / 2)) y := by
      have h :
          HasDerivAt (fun s : ℝ => |s| ^ p)
            (p * |(y + y) / 2| ^ (p - 2) * ((y + y) / 2)) ((y + y) / 2) :=
        hasDerivAt_abs_rpow ((y + y) / 2) hp1
      have hcomp := h.comp y hbase_sum
      refine hcomp.congr_deriv ?_
      simp [abs_of_pos hy_pos]
      ring
    have hpow_diff :
        HasDerivAt (fun t : ℝ => |((y - t) / 2)| ^ p) 0 y := by
      have h :
          HasDerivAt (fun s : ℝ => |s| ^ p)
            (p * |(y - y) / 2| ^ (p - 2) * ((y - y) / 2)) ((y - y) / 2) :=
        hasDerivAt_abs_rpow ((y - y) / 2) hp1
      have hcomp := h.comp y hbase_diff
      simpa using hcomp
    have hd :
        HasDerivAt g (p * (y ^ (p - 2) * y) * (1 / 2) - coeffLeTwo p * 0) y := by
      dsimp [g]
      exact hpow_sum.sub (hpow_diff.const_mul (coeffLeTwo p))
    rw [hEq]
    refine hd.congr_deriv ?_
    have hpow : y ^ (p - 2) * y = y ^ (p - 1) := by
      calc
        y ^ (p - 2) * y = y ^ (p - 2) * y ^ (1 : ℝ) := by rw [Real.rpow_one]
        _ = y ^ ((p - 2) + 1) := by rw [← Real.rpow_add hy_pos]
        _ = y ^ (p - 1) := by ring_nf
    have hzero : (0 : ℝ) ^ (p - 1) = 0 := Real.zero_rpow (by linarith)
    simp [DyvLeTwo, hy_pos, abs_of_pos hy_pos, hzero]
    rw [hpow]
    ring
  have hmain :
      vLeTwo p y (a p * y) ≤
        vLeTwo p y y + DyvLeTwo p y y * (a p * y - y) := by
    apply vLeTwo_tangent_y_on_Icc_of_A2_leTwo
        (p := p) (hp1 := hp1) (hp2 := hp2)
        (lo := a p * y) (hi := y) (x := y) (y := y) (z := a p * y)
    · intro t ht
      have htI : t ∈ Set.Ioo (a p * y) y := by
        simpa [interior_Icc] using ht
      exact ⟨hy_pos, htI.1, htI.2⟩
    · exact ⟨le_of_lt hc_lt_y, le_rfl⟩
    · exact ⟨le_rfl, le_of_lt hc_lt_y⟩
    · exact hderiv
  calc
    uCandidate p (a p * y) y = vLeTwo p y (a p * y) := huc
    _ ≤ vLeTwo p y y + DyvLeTwo p y y * (a p * y - y) := hmain
    _ = uCandidate p y y + DxuCandidate p y y * (a p * y - y) := by
      rw [huy, hdy, hdiag]

lemma uCandidate_tangent_x_Q1_A2_to_Q3_A2_leTwo
    (p : ℝ) (hp1 : 1 < p) (hp2 : p < 2) {x z y : ℝ}
    (hy_pos : 0 < y) (hx_lower : y < x) (hx_upper : x < y / a p)
    (hz_lower : a p * y < z) (hz_upper : z < y) :
    uCandidate p z y ≤
      uCandidate p x y + DxuCandidate p x y * (z - x) := by
  have hxy := uCandidate_tangent_x_Q1_A2_to_diag_leTwo
    (p := p) (hp1 := hp1) (hp2 := hp2) (x := x) (y := y)
    hy_pos hx_lower hx_upper
  have hyz := uCandidate_tangent_x_diag_to_Q3_A2_leTwo
    (p := p) (hp1 := hp1) (hp2 := hp2) (z := z) (y := y)
    hy_pos hz_lower hz_upper
  have hd := DxuCandidate_Q1_A2_le_diag_leTwo
    (p := p) (hp1 := hp1) (hp2 := hp2) (x := x) (y := y)
    hy_pos hx_lower hx_upper
  exact tangent_glue_two_backward_leTwo_local
    (fun t => uCandidate p t y) (fun t => DxuCandidate p t y)
    (le_of_lt hz_upper) (le_of_lt hx_lower) hxy hyz hd

lemma uCandidate_tangent_x_Q1_A2_to_Q3_A2_boundary_leTwo
    (p : ℝ) (hp1 : 1 < p) (hp2 : p < 2) {x y : ℝ}
    (hy_pos : 0 < y) (hx_lower : y < x) (hx_upper : x < y / a p) :
    uCandidate p (a p * y) y ≤
      uCandidate p x y + DxuCandidate p x y * (a p * y - x) := by
  have hxy := uCandidate_tangent_x_Q1_A2_to_diag_leTwo
    (p := p) (hp1 := hp1) (hp2 := hp2) (x := x) (y := y)
    hy_pos hx_lower hx_upper
  have hyc := uCandidate_tangent_x_diag_to_Q3_A2_boundary_leTwo
    (p := p) (hp1 := hp1) (hp2 := hp2) (y := y) hy_pos
  have hd := DxuCandidate_Q1_A2_le_diag_leTwo
    (p := p) (hp1 := hp1) (hp2 := hp2) (x := x) (y := y)
    hy_pos hx_lower hx_upper
  exact tangent_glue_two_backward_leTwo_local
    (fun t => uCandidate p t y) (fun t => DxuCandidate p t y)
    (by
      have ha_lt : a p < 1 := a_lt_one_of_one_lt_of_lt_two p hp1 hp2
      have hlt : a p * y < y := by
        simpa using mul_lt_mul_of_pos_right ha_lt hy_pos
      exact le_of_lt hlt)
    (le_of_lt hx_lower) hxy hyc hd

lemma uCandidate_tangent_x_Q3_A2_to_boundary_leTwo
    (p : ℝ) (hp1 : 1 < p) (hp2 : p < 2) {x y : ℝ}
    (hy_pos : 0 < y) (hx_lower : a p * y < x) (hx_upper : x < y) :
    uCandidate p (a p * y) y ≤
      uCandidate p x y + DxuCandidate p x y * (a p * y - x) := by
  have ha_pos : 0 < a p := by
    rw [a_eq_leTwo p hp1 hp2]
    exact div_pos (by linarith) (by linarith)
  have ha_lt : a p < 1 := a_lt_one_of_one_lt_of_lt_two p hp1 hp2
  have hc_lt_y : a p * y < y := by
    simpa using mul_lt_mul_of_pos_right ha_lt hy_pos
  have hc_pos : 0 < a p * y := mul_pos ha_pos hy_pos
  have hQx : QuarterPlane3 x y := ⟨hy_pos.le, by linarith [hc_pos, hx_lower], le_of_lt hx_upper⟩
  have hQc : QuarterPlane3 (a p * y) y := ⟨hy_pos.le, by linarith, le_of_lt hc_lt_y⟩
  have hclx : closureA2 p y x := ⟨hy_pos.le, le_of_lt hx_lower, le_of_lt hx_upper⟩
  have hclc : closureA2 p y (a p * y) := ⟨hy_pos.le, le_rfl, le_of_lt hc_lt_y⟩
  have hux : uCandidate p x y = vLeTwo p y x := by
    rw [uCandidate_eq_Q3_leTwo p hQx, auxFunction1_eq_vLeTwo_leTwo p hp1 hp2 y x hclx]
  have huc : uCandidate p (a p * y) y = vLeTwo p y (a p * y) := by
    rw [uCandidate_eq_Q3_leTwo p hQc, auxFunction1_eq_vLeTwo_leTwo p hp1 hp2 y (a p * y) hclc]
  have hdx : DxuCandidate p x y = DyvLeTwo p y x := by
    rw [DxuCandidate_eq_Q3_leTwo p hp1 hp2 hQx]
    have hnot : ¬ closureA1 p y x := by
      intro h
      exact not_le_of_gt hx_lower h.2.2
    simp [DyauxFunction1, hnot, hclx]
  have hderiv : HasDerivAt (fun t => vLeTwo p y t) (DyvLeTwo p y x) x := by
    have hsum : 0 < (y + x) / 2 := by linarith [hy_pos, hc_pos, hx_lower]
    have hdiff : 0 < (y - x) / 2 := by linarith
    exact hasDerivAt_vLeTwo_y_of_pos_leTwo p y x hsum hdiff
  have hmain :
      vLeTwo p y (a p * y) ≤
        vLeTwo p y x + DyvLeTwo p y x * (a p * y - x) := by
    apply vLeTwo_tangent_y_on_Icc_of_A2_leTwo
        (p := p) (hp1 := hp1) (hp2 := hp2)
        (lo := a p * y) (hi := x) (x := y) (y := x) (z := a p * y)
    · intro t ht
      have htI : t ∈ Set.Ioo (a p * y) x := by
        simpa [interior_Icc] using ht
      exact ⟨hy_pos, htI.1, lt_trans htI.2 hx_upper⟩
    · exact ⟨le_of_lt hx_lower, le_rfl⟩
    · exact ⟨le_rfl, le_of_lt hx_lower⟩
    · exact hderiv
  calc
    uCandidate p (a p * y) y = vLeTwo p y (a p * y) := huc
    _ ≤ vLeTwo p y x + DyvLeTwo p y x * (a p * y - x) := hmain
    _ = uCandidate p x y + DxuCandidate p x y * (a p * y - x) := by
      rw [hux, hdx]

lemma uCandidate_tangent_x_Q3_A2_boundary_to_Q3_A1_leTwo
    (p : ℝ) (hp1 : 1 < p) (hp2 : p < 2) {z y : ℝ}
    (hy_pos : 0 < y) (hz_lower : -y < z) (hz_upper : z < a p * y) :
    uCandidate p z y ≤
      uCandidate p (a p * y) y +
        DxuCandidate p (a p * y) y * (z - a p * y) := by
  have ha_nonneg : 0 ≤ a p := a_nonneg_of_one_lt_of_lt_two p hp1 hp2
  have ha_lt : a p < 1 := a_lt_one_of_one_lt_of_lt_two p hp1 hp2
  have hc_lt_y : a p * y < y := by
    simpa using mul_lt_mul_of_pos_right ha_lt hy_pos
  have hQc : QuarterPlane3 (a p * y) y := ⟨hy_pos.le, by
    have hnonneg : 0 ≤ a p * y := mul_nonneg ha_nonneg hy_pos.le
    linarith, le_of_lt hc_lt_y⟩
  have hQz : QuarterPlane3 z y := ⟨hy_pos.le, le_of_lt hz_lower, le_of_lt (lt_trans hz_upper hc_lt_y)⟩
  have hclc : closureA1 p y (a p * y) := ⟨hy_pos.le, by
    have hnonneg : 0 ≤ a p * y := mul_nonneg ha_nonneg hy_pos.le
    linarith, le_rfl⟩
  have hclz : closureA1 p y z := ⟨hy_pos.le, le_of_lt hz_lower, le_of_lt hz_upper⟩
  have huc : uCandidate p (a p * y) y = uA1 p y (a p * y) := by
    rw [uCandidate_eq_Q3_leTwo p hQc]
    simp [auxFunction1, hclc]
  have huz : uCandidate p z y = uA1 p y z := by
    rw [uCandidate_eq_Q3_leTwo p hQz]
    simp [auxFunction1, hclz]
  have hdc : DxuCandidate p (a p * y) y = DyuA1 p y (a p * y) := by
    rw [DxuCandidate_eq_Q3_leTwo p hp1 hp2 hQc]
    simp [DyauxFunction1, hclc]
  apply le_of_eq
  calc
    uCandidate p z y = uA1 p y z := huz
    _ = uA1 p y (a p * y) + DyuA1 p y (a p * y) * (z - a p * y) :=
      uA1_affine_y_tangent_leTwo p y (a p * y) z hy_pos
    _ = uCandidate p (a p * y) y +
        DxuCandidate p (a p * y) y * (z - a p * y) := by
      rw [huc, hdc]

lemma uCandidate_tangent_x_Q3_A2_boundary_to_antidiag_leTwo
    (p : ℝ) (hp1 : 1 < p) (hp2 : p < 2) {y : ℝ}
    (hy_pos : 0 < y) :
    uCandidate p (-y) y ≤
      uCandidate p (a p * y) y +
        DxuCandidate p (a p * y) y * ((-y) - a p * y) := by
  have ha_nonneg : 0 ≤ a p := a_nonneg_of_one_lt_of_lt_two p hp1 hp2
  have ha_lt : a p < 1 := a_lt_one_of_one_lt_of_lt_two p hp1 hp2
  have hc_lt_y : a p * y < y := by
    simpa using mul_lt_mul_of_pos_right ha_lt hy_pos
  have hQc : QuarterPlane3 (a p * y) y := ⟨hy_pos.le, by
    have hnonneg : 0 ≤ a p * y := mul_nonneg ha_nonneg hy_pos.le
    linarith, le_of_lt hc_lt_y⟩
  have hQa : QuarterPlane2 (-y) y := ⟨by linarith, by linarith, by linarith⟩
  have hclc : closureA1 p y (a p * y) := ⟨hy_pos.le, by
    have hnonneg : 0 ≤ a p * y := mul_nonneg ha_nonneg hy_pos.le
    linarith, le_rfl⟩
  have hcla : closureA1 p y (-y) := by
    refine ⟨hy_pos.le, le_rfl, ?_⟩
    have hnonneg : 0 ≤ a p * y := mul_nonneg ha_nonneg hy_pos.le
    linarith
  have huc : uCandidate p (a p * y) y = uA1 p y (a p * y) := by
    rw [uCandidate_eq_Q3_leTwo p hQc]
    simp [auxFunction1, hclc]
  have hua : uCandidate p (-y) y = uA1 p y (-y) := by
    rw [uCandidate_eq_Q2_leTwo p hQa]
    simp [auxFunction1, hcla]
  have hdc : DxuCandidate p (a p * y) y = DyuA1 p y (a p * y) := by
    rw [DxuCandidate_eq_Q3_leTwo p hp1 hp2 hQc]
    simp [DyauxFunction1, hclc]
  apply le_of_eq
  calc
    uCandidate p (-y) y = uA1 p y (-y) := hua
    _ = uA1 p y (a p * y) + DyuA1 p y (a p * y) * ((-y) - a p * y) :=
      uA1_affine_y_tangent_leTwo p y (a p * y) (-y) hy_pos
    _ = uCandidate p (a p * y) y +
        DxuCandidate p (a p * y) y * ((-y) - a p * y) := by
      rw [huc, hdc]

lemma uCandidate_tangent_x_Q3_A2_boundary_to_Q2_leTwo
    (p : ℝ) (hp1 : 1 < p) (hp2 : p < 2) {z y : ℝ}
    (hy_pos : 0 < y) (hz_left : z < -y) :
    uCandidate p z y ≤
      uCandidate p (a p * y) y +
        DxuCandidate p (a p * y) y * (z - a p * y) := by
  have hca := uCandidate_tangent_x_Q3_A2_boundary_to_antidiag_leTwo
    (p := p) (hp1 := hp1) (hp2 := hp2) (y := y) hy_pos
  have haz := uCandidate_tangent_x_antidiag_to_Q2_leTwo
    (p := p) (hp1 := hp1) (hp2 := hp2) (z := z) (y := y)
    hy_pos hz_left
  have hd := DxuCandidate_Q3_A1_boundary_le_antidiag_leTwo
    (p := p) (hp1 := hp1) (hp2 := hp2) (y := y) hy_pos
  exact tangent_glue_two_backward_leTwo_local
    (fun t => uCandidate p t y) (fun t => DxuCandidate p t y)
    (le_of_lt hz_left) (by
      have ha_nonneg : 0 ≤ a p := a_nonneg_of_one_lt_of_lt_two p hp1 hp2
      have hnonneg : 0 ≤ a p * y := mul_nonneg ha_nonneg hy_pos.le
      linarith)
    hca haz hd

lemma uCandidate_tangent_x_Q3_A2_to_Q3_A1_leTwo
    (p : ℝ) (hp1 : 1 < p) (hp2 : p < 2) {x z y : ℝ}
    (hy_pos : 0 < y) (hx_lower : a p * y < x) (hx_upper : x < y)
    (hz_lower : -y < z) (hz_upper : z < a p * y) :
    uCandidate p z y ≤
      uCandidate p x y + DxuCandidate p x y * (z - x) := by
  have hxc := uCandidate_tangent_x_Q3_A2_to_boundary_leTwo
    (p := p) (hp1 := hp1) (hp2 := hp2) (x := x) (y := y)
    hy_pos hx_lower hx_upper
  have hcz := uCandidate_tangent_x_Q3_A2_boundary_to_Q3_A1_leTwo
    (p := p) (hp1 := hp1) (hp2 := hp2) (z := z) (y := y)
    hy_pos hz_lower hz_upper
  have hd := DxuCandidate_Q3_A2_le_boundary_leTwo
    (p := p) (hp1 := hp1) (hp2 := hp2) (x := x) (y := y)
    hy_pos hx_lower hx_upper
  exact tangent_glue_two_backward_leTwo_local
    (fun t => uCandidate p t y) (fun t => DxuCandidate p t y)
    (le_of_lt hz_upper) (le_of_lt hx_lower) hxc hcz hd

lemma uCandidate_tangent_x_Q3_A2_to_antidiag_leTwo
    (p : ℝ) (hp1 : 1 < p) (hp2 : p < 2) {x y : ℝ}
    (hy_pos : 0 < y) (hx_lower : a p * y < x) (hx_upper : x < y) :
    uCandidate p (-y) y ≤
      uCandidate p x y + DxuCandidate p x y * ((-y) - x) := by
  have hxc := uCandidate_tangent_x_Q3_A2_to_boundary_leTwo
    (p := p) (hp1 := hp1) (hp2 := hp2) (x := x) (y := y)
    hy_pos hx_lower hx_upper
  have hca := uCandidate_tangent_x_Q3_A2_boundary_to_antidiag_leTwo
    (p := p) (hp1 := hp1) (hp2 := hp2) (y := y) hy_pos
  have hd := DxuCandidate_Q3_A2_le_boundary_leTwo
    (p := p) (hp1 := hp1) (hp2 := hp2) (x := x) (y := y)
    hy_pos hx_lower hx_upper
  exact tangent_glue_two_backward_leTwo_local
    (fun t => uCandidate p t y) (fun t => DxuCandidate p t y)
    (by
      have ha_nonneg : 0 ≤ a p := a_nonneg_of_one_lt_of_lt_two p hp1 hp2
      have hnonneg : 0 ≤ a p * y := mul_nonneg ha_nonneg hy_pos.le
      linarith)
    (le_of_lt hx_lower) hxc hca hd

lemma uCandidate_tangent_x_Q3_A2_to_Q2_leTwo
    (p : ℝ) (hp1 : 1 < p) (hp2 : p < 2) {x z y : ℝ}
    (hy_pos : 0 < y) (hx_lower : a p * y < x) (hx_upper : x < y)
    (hz_left : z < -y) :
    uCandidate p z y ≤
      uCandidate p x y + DxuCandidate p x y * (z - x) := by
  have hxc := uCandidate_tangent_x_Q3_A2_to_boundary_leTwo
    (p := p) (hp1 := hp1) (hp2 := hp2) (x := x) (y := y)
    hy_pos hx_lower hx_upper
  have hcz := uCandidate_tangent_x_Q3_A2_boundary_to_Q2_leTwo
    (p := p) (hp1 := hp1) (hp2 := hp2) (z := z) (y := y)
    hy_pos hz_left
  have hd := DxuCandidate_Q3_A2_le_boundary_leTwo
    (p := p) (hp1 := hp1) (hp2 := hp2) (x := x) (y := y)
    hy_pos hx_lower hx_upper
  exact tangent_glue_two_backward_leTwo_local
    (fun t => uCandidate p t y) (fun t => DxuCandidate p t y)
    (by
      have ha_nonneg : 0 ≤ a p := a_nonneg_of_one_lt_of_lt_two p hp1 hp2
      have hnonneg : 0 ≤ a p * y := mul_nonneg ha_nonneg hy_pos.le
      linarith)
    (le_of_lt hx_lower) hxc hcz hd

lemma uCandidate_tangent_x_Q3_A1_to_Q2_leTwo
    (p : ℝ) (hp1 : 1 < p) (hp2 : p < 2) {x z y : ℝ}
    (hy_pos : 0 < y) (hx_lower : -y < x) (hx_upper : x < a p * y)
    (hz_left : z < -y) :
    uCandidate p z y ≤
      uCandidate p x y + DxuCandidate p x y * (z - x) := by
  have hxa := uCandidate_tangent_x_Q3_A1_to_antidiag_leTwo
    (p := p) (hp1 := hp1) (hp2 := hp2) (x := x) (y := y)
    hy_pos hx_lower hx_upper
  have haz := uCandidate_tangent_x_antidiag_to_Q2_leTwo
    (p := p) (hp1 := hp1) (hp2 := hp2) (z := z) (y := y)
    hy_pos hz_left
  have hd : DxuCandidate p x y ≤ DxuCandidate p (-y) y := by
    rw [DxuCandidate_Q3_A1_eq_antidiag_leTwo
      (p := p) (hp1 := hp1) (hp2 := hp2) (x := x) (y := y)
      hy_pos hx_lower hx_upper]
  exact tangent_glue_two_backward_leTwo_local
    (fun t => uCandidate p t y) (fun t => DxuCandidate p t y)
    (le_of_lt hz_left) (le_of_lt hx_lower) hxa haz hd

lemma uCandidate_tangent_x_diag_to_Q3_A1_leTwo
    (p : ℝ) (hp1 : 1 < p) (hp2 : p < 2) {z y : ℝ}
    (hy_pos : 0 < y) (hz_lower : -y < z) (hz_upper : z < a p * y) :
    uCandidate p z y ≤
      uCandidate p y y + DxuCandidate p y y * (z - y) := by
  have hyc := uCandidate_tangent_x_diag_to_Q3_A2_boundary_leTwo
    (p := p) (hp1 := hp1) (hp2 := hp2) (y := y) hy_pos
  have hcz := uCandidate_tangent_x_Q3_A2_boundary_to_Q3_A1_leTwo
    (p := p) (hp1 := hp1) (hp2 := hp2) (z := z) (y := y)
    hy_pos hz_lower hz_upper
  have hd := DxuCandidate_diag_le_Q3_A1_boundary_leTwo
    (p := p) (hp1 := hp1) (hp2 := hp2) (y := y) hy_pos
  exact tangent_glue_two_backward_leTwo_local
    (fun t => uCandidate p t y) (fun t => DxuCandidate p t y)
    (le_of_lt hz_upper) (by
      have ha_lt : a p < 1 := a_lt_one_of_one_lt_of_lt_two p hp1 hp2
      have hlt : a p * y < y := by
        simpa using mul_lt_mul_of_pos_right ha_lt hy_pos
      exact le_of_lt hlt)
    hyc hcz hd

lemma uCandidate_tangent_x_diag_to_antidiag_leTwo
    (p : ℝ) (hp1 : 1 < p) (hp2 : p < 2) {y : ℝ}
    (hy_pos : 0 < y) :
    uCandidate p (-y) y ≤
      uCandidate p y y + DxuCandidate p y y * ((-y) - y) := by
  have hyc := uCandidate_tangent_x_diag_to_Q3_A2_boundary_leTwo
    (p := p) (hp1 := hp1) (hp2 := hp2) (y := y) hy_pos
  have hca := uCandidate_tangent_x_Q3_A2_boundary_to_antidiag_leTwo
    (p := p) (hp1 := hp1) (hp2 := hp2) (y := y) hy_pos
  have hd := DxuCandidate_diag_le_Q3_A1_boundary_leTwo
    (p := p) (hp1 := hp1) (hp2 := hp2) (y := y) hy_pos
  exact tangent_glue_two_backward_leTwo_local
    (fun t => uCandidate p t y) (fun t => DxuCandidate p t y)
    (by
      have ha_nonneg : 0 ≤ a p := a_nonneg_of_one_lt_of_lt_two p hp1 hp2
      have hnonneg : 0 ≤ a p * y := mul_nonneg ha_nonneg hy_pos.le
      linarith)
    (by
      have ha_lt : a p < 1 := a_lt_one_of_one_lt_of_lt_two p hp1 hp2
      have hlt : a p * y < y := by
        simpa using mul_lt_mul_of_pos_right ha_lt hy_pos
      exact le_of_lt hlt)
    hyc hca hd

lemma uCandidate_tangent_x_diag_to_Q2_leTwo
    (p : ℝ) (hp1 : 1 < p) (hp2 : p < 2) {z y : ℝ}
    (hy_pos : 0 < y) (hz_left : z < -y) :
    uCandidate p z y ≤
      uCandidate p y y + DxuCandidate p y y * (z - y) := by
  have hyc := uCandidate_tangent_x_diag_to_Q3_A2_boundary_leTwo
    (p := p) (hp1 := hp1) (hp2 := hp2) (y := y) hy_pos
  have hcz := uCandidate_tangent_x_Q3_A2_boundary_to_Q2_leTwo
    (p := p) (hp1 := hp1) (hp2 := hp2) (z := z) (y := y)
    hy_pos hz_left
  have hd := DxuCandidate_diag_le_Q3_A1_boundary_leTwo
    (p := p) (hp1 := hp1) (hp2 := hp2) (y := y) hy_pos
  exact tangent_glue_two_backward_leTwo_local
    (fun t => uCandidate p t y) (fun t => DxuCandidate p t y)
    (by
      have ha_nonneg : 0 ≤ a p := a_nonneg_of_one_lt_of_lt_two p hp1 hp2
      have hnonneg : 0 ≤ a p * y := mul_nonneg ha_nonneg hy_pos.le
      linarith)
    (by
      have ha_lt : a p < 1 := a_lt_one_of_one_lt_of_lt_two p hp1 hp2
      have hlt : a p * y < y := by
        simpa using mul_lt_mul_of_pos_right ha_lt hy_pos
      exact le_of_lt hlt)
    hyc hcz hd

lemma DxuCandidate_Q1_A2_le_Q3_A1_boundary_leTwo
    (p : ℝ) (hp1 : 1 < p) (hp2 : p < 2) {x y : ℝ}
    (hy_pos : 0 < y) (hx_lower : y < x) (hx_upper : x < y / a p) :
    DxuCandidate p x y ≤ DxuCandidate p (a p * y) y :=
  le_trans
    (DxuCandidate_Q1_A2_le_diag_leTwo
      (p := p) (hp1 := hp1) (hp2 := hp2) (x := x) (y := y)
      hy_pos hx_lower hx_upper)
    (DxuCandidate_diag_le_Q3_A1_boundary_leTwo
      (p := p) (hp1 := hp1) (hp2 := hp2) (y := y) hy_pos)

lemma DxuCandidate_Q1_A1_le_diag_leTwo
    (p : ℝ) (hp1 : 1 < p) (hp2 : p < 2) {x y : ℝ}
    (hy_pos : 0 < y) (hx_lower : y / a p < x) :
    DxuCandidate p x y ≤ DxuCandidate p y y := by
  have ha_pos : 0 < a p := by
    rw [a_eq_leTwo p hp1 hp2]
    exact div_pos (by linarith) (by linarith)
  have ha_lt : a p < 1 := a_lt_one_of_one_lt_of_lt_two p hp1 hp2
  have hy_lt_b : y < y / a p := by
    rw [div_eq_mul_inv]
    have hinv : 1 < (a p)⁻¹ := by
      rw [one_lt_inv₀ ha_pos]
      exact ha_lt
    nlinarith
  have hQx : QuarterPlane x y :=
    ⟨by linarith, le_of_lt (lt_trans hy_lt_b hx_lower), by linarith⟩
  have hQb : QuarterPlane (y / a p) y :=
    ⟨(div_pos hy_pos ha_pos).le, le_of_lt hy_lt_b, by linarith⟩
  have hdx : DxuCandidate p x y = DxauxFunction1 p x y := by
    rw [DxuCandidate_eq_Q1_leTwo p hQx]
  have hdb : DxuCandidate p (y / a p) y = DxauxFunction1 p (y / a p) y := by
    rw [DxuCandidate_eq_Q1_leTwo p hQb]
  have hxb : DxuCandidate p x y ≤ DxuCandidate p (y / a p) y := by
    have hle := DxauxFunction1_A1_le_boundary_leTwo
      (p := p) (hp1 := hp1) (hp2 := hp2) (x := x) (y := y)
      hy_pos (lt_trans hy_lt_b hx_lower) (by
        have hmul := mul_lt_mul_of_pos_left hx_lower ha_pos
        field_simp [ha_pos.ne'] at hmul
        simpa [mul_comm, mul_left_comm, mul_assoc] using hmul)
    rwa [hdx, hdb]
  exact le_trans hxb
    (DxuCandidate_Q1_boundary_le_diag_leTwo
      (p := p) (hp1 := hp1) (hp2 := hp2) (y := y) hy_pos)

lemma DxuCandidate_Q1_A1_le_Q3_A1_boundary_leTwo
    (p : ℝ) (hp1 : 1 < p) (hp2 : p < 2) {x y : ℝ}
    (hy_pos : 0 < y) (hx_lower : y / a p < x) :
    DxuCandidate p x y ≤ DxuCandidate p (a p * y) y :=
  le_trans
    (DxuCandidate_Q1_A1_le_diag_leTwo
      (p := p) (hp1 := hp1) (hp2 := hp2) (x := x) (y := y)
      hy_pos hx_lower)
    (DxuCandidate_diag_le_Q3_A1_boundary_leTwo
      (p := p) (hp1 := hp1) (hp2 := hp2) (y := y) hy_pos)

lemma uCandidate_tangent_x_Q1_A2_to_Q3_A1_leTwo
    (p : ℝ) (hp1 : 1 < p) (hp2 : p < 2) {x z y : ℝ}
    (hy_pos : 0 < y) (hx_lower : y < x) (hx_upper : x < y / a p)
    (hz_lower : -y < z) (hz_upper : z < a p * y) :
    uCandidate p z y ≤
      uCandidate p x y + DxuCandidate p x y * (z - x) := by
  have hxc := uCandidate_tangent_x_Q1_A2_to_Q3_A2_boundary_leTwo
    (p := p) (hp1 := hp1) (hp2 := hp2) (x := x) (y := y)
    hy_pos hx_lower hx_upper
  have hcz := uCandidate_tangent_x_Q3_A2_boundary_to_Q3_A1_leTwo
    (p := p) (hp1 := hp1) (hp2 := hp2) (z := z) (y := y)
    hy_pos hz_lower hz_upper
  have hd := DxuCandidate_Q1_A2_le_Q3_A1_boundary_leTwo
    (p := p) (hp1 := hp1) (hp2 := hp2) (x := x) (y := y)
    hy_pos hx_lower hx_upper
  exact tangent_glue_two_backward_leTwo_local
    (fun t => uCandidate p t y) (fun t => DxuCandidate p t y)
    (le_of_lt hz_upper) (by
      have ha_lt : a p < 1 := a_lt_one_of_one_lt_of_lt_two p hp1 hp2
      have hlt : a p * y < y := by
        simpa using mul_lt_mul_of_pos_right ha_lt hy_pos
      exact le_trans (le_of_lt hlt) (le_of_lt hx_lower))
    hxc hcz hd

lemma uCandidate_tangent_x_Q1_A2_to_antidiag_leTwo
    (p : ℝ) (hp1 : 1 < p) (hp2 : p < 2) {x y : ℝ}
    (hy_pos : 0 < y) (hx_lower : y < x) (hx_upper : x < y / a p) :
    uCandidate p (-y) y ≤
      uCandidate p x y + DxuCandidate p x y * ((-y) - x) := by
  have hxc := uCandidate_tangent_x_Q1_A2_to_Q3_A2_boundary_leTwo
    (p := p) (hp1 := hp1) (hp2 := hp2) (x := x) (y := y)
    hy_pos hx_lower hx_upper
  have hca := uCandidate_tangent_x_Q3_A2_boundary_to_antidiag_leTwo
    (p := p) (hp1 := hp1) (hp2 := hp2) (y := y) hy_pos
  have hd := DxuCandidate_Q1_A2_le_Q3_A1_boundary_leTwo
    (p := p) (hp1 := hp1) (hp2 := hp2) (x := x) (y := y)
    hy_pos hx_lower hx_upper
  exact tangent_glue_two_backward_leTwo_local
    (fun t => uCandidate p t y) (fun t => DxuCandidate p t y)
    (by
      have ha_nonneg : 0 ≤ a p := a_nonneg_of_one_lt_of_lt_two p hp1 hp2
      have hnonneg : 0 ≤ a p * y := mul_nonneg ha_nonneg hy_pos.le
      linarith)
    (by
      have ha_lt : a p < 1 := a_lt_one_of_one_lt_of_lt_two p hp1 hp2
      have hlt : a p * y < y := by
        simpa using mul_lt_mul_of_pos_right ha_lt hy_pos
      exact le_trans (le_of_lt hlt) (le_of_lt hx_lower))
    hxc hca hd

lemma uCandidate_tangent_x_Q1_A2_to_Q2_leTwo
    (p : ℝ) (hp1 : 1 < p) (hp2 : p < 2) {x z y : ℝ}
    (hy_pos : 0 < y) (hx_lower : y < x) (hx_upper : x < y / a p)
    (hz_left : z < -y) :
    uCandidate p z y ≤
      uCandidate p x y + DxuCandidate p x y * (z - x) := by
  have hxc := uCandidate_tangent_x_Q1_A2_to_Q3_A2_boundary_leTwo
    (p := p) (hp1 := hp1) (hp2 := hp2) (x := x) (y := y)
    hy_pos hx_lower hx_upper
  have hcz := uCandidate_tangent_x_Q3_A2_boundary_to_Q2_leTwo
    (p := p) (hp1 := hp1) (hp2 := hp2) (z := z) (y := y)
    hy_pos hz_left
  have hd := DxuCandidate_Q1_A2_le_Q3_A1_boundary_leTwo
    (p := p) (hp1 := hp1) (hp2 := hp2) (x := x) (y := y)
    hy_pos hx_lower hx_upper
  exact tangent_glue_two_backward_leTwo_local
    (fun t => uCandidate p t y) (fun t => DxuCandidate p t y)
    (by
      have ha_nonneg : 0 ≤ a p := a_nonneg_of_one_lt_of_lt_two p hp1 hp2
      have hnonneg : 0 ≤ a p * y := mul_nonneg ha_nonneg hy_pos.le
      linarith)
    (by
      have ha_lt : a p < 1 := a_lt_one_of_one_lt_of_lt_two p hp1 hp2
      have hlt : a p * y < y := by
        simpa using mul_lt_mul_of_pos_right ha_lt hy_pos
      exact le_trans (le_of_lt hlt) (le_of_lt hx_lower))
    hxc hcz hd

lemma uCandidate_tangent_x_Q1_boundary_to_Q3_A2_leTwo
    (p : ℝ) (hp1 : 1 < p) (hp2 : p < 2) {z y : ℝ}
    (hy_pos : 0 < y) (hz_lower : a p * y < z) (hz_upper : z < y) :
    uCandidate p z y ≤
      uCandidate p (y / a p) y +
        DxuCandidate p (y / a p) y * (z - y / a p) := by
  have hbd := uCandidate_tangent_x_Q1_boundary_to_diag_leTwo
    (p := p) (hp1 := hp1) (hp2 := hp2) (y := y) hy_pos
  have hdz := uCandidate_tangent_x_diag_to_Q3_A2_leTwo
    (p := p) (hp1 := hp1) (hp2 := hp2) (z := z) (y := y)
    hy_pos hz_lower hz_upper
  have hd := DxuCandidate_Q1_boundary_le_diag_leTwo
    (p := p) (hp1 := hp1) (hp2 := hp2) (y := y) hy_pos
  exact tangent_glue_two_backward_leTwo_local
    (fun t => uCandidate p t y) (fun t => DxuCandidate p t y)
    (le_of_lt hz_upper) (by
      have ha_pos : 0 < a p := by
        rw [a_eq_leTwo p hp1 hp2]
        exact div_pos (by linarith) (by linarith)
      have ha_lt : a p < 1 := a_lt_one_of_one_lt_of_lt_two p hp1 hp2
      have hlt : y < y / a p := by
        rw [div_eq_mul_inv]
        have hinv : 1 < (a p)⁻¹ := by
          rw [one_lt_inv₀ ha_pos]
          exact ha_lt
        nlinarith
      exact le_of_lt hlt)
    hbd hdz hd

lemma uCandidate_tangent_x_Q1_boundary_to_Q3_A2_boundary_leTwo
    (p : ℝ) (hp1 : 1 < p) (hp2 : p < 2) {y : ℝ}
    (hy_pos : 0 < y) :
    uCandidate p (a p * y) y ≤
      uCandidate p (y / a p) y +
        DxuCandidate p (y / a p) y * (a p * y - y / a p) := by
  have hbd := uCandidate_tangent_x_Q1_boundary_to_diag_leTwo
    (p := p) (hp1 := hp1) (hp2 := hp2) (y := y) hy_pos
  have hdc := uCandidate_tangent_x_diag_to_Q3_A2_boundary_leTwo
    (p := p) (hp1 := hp1) (hp2 := hp2) (y := y) hy_pos
  have hd := DxuCandidate_Q1_boundary_le_diag_leTwo
    (p := p) (hp1 := hp1) (hp2 := hp2) (y := y) hy_pos
  exact tangent_glue_two_backward_leTwo_local
    (fun t => uCandidate p t y) (fun t => DxuCandidate p t y)
    (by
      have ha_lt : a p < 1 := a_lt_one_of_one_lt_of_lt_two p hp1 hp2
      have hlt : a p * y < y := by
        simpa using mul_lt_mul_of_pos_right ha_lt hy_pos
      exact le_of_lt hlt)
    (by
      have ha_pos : 0 < a p := by
        rw [a_eq_leTwo p hp1 hp2]
        exact div_pos (by linarith) (by linarith)
      have ha_lt : a p < 1 := a_lt_one_of_one_lt_of_lt_two p hp1 hp2
      have hlt : y < y / a p := by
        rw [div_eq_mul_inv]
        have hinv : 1 < (a p)⁻¹ := by
          rw [one_lt_inv₀ ha_pos]
          exact ha_lt
        nlinarith
      exact le_of_lt hlt)
    hbd hdc hd

lemma uCandidate_tangent_x_Q1_boundary_to_Q3_A1_leTwo
    (p : ℝ) (hp1 : 1 < p) (hp2 : p < 2) {z y : ℝ}
    (hy_pos : 0 < y) (hz_lower : -y < z) (hz_upper : z < a p * y) :
    uCandidate p z y ≤
      uCandidate p (y / a p) y +
        DxuCandidate p (y / a p) y * (z - y / a p) := by
  have hbc := uCandidate_tangent_x_Q1_boundary_to_Q3_A2_boundary_leTwo
    (p := p) (hp1 := hp1) (hp2 := hp2) (y := y) hy_pos
  have hcz := uCandidate_tangent_x_Q3_A2_boundary_to_Q3_A1_leTwo
    (p := p) (hp1 := hp1) (hp2 := hp2) (z := z) (y := y)
    hy_pos hz_lower hz_upper
  have hd : DxuCandidate p (y / a p) y ≤ DxuCandidate p (a p * y) y :=
    le_trans
      (DxuCandidate_Q1_boundary_le_diag_leTwo
        (p := p) (hp1 := hp1) (hp2 := hp2) (y := y) hy_pos)
      (DxuCandidate_diag_le_Q3_A1_boundary_leTwo
        (p := p) (hp1 := hp1) (hp2 := hp2) (y := y) hy_pos)
  exact tangent_glue_two_backward_leTwo_local
    (fun t => uCandidate p t y) (fun t => DxuCandidate p t y)
    (le_of_lt hz_upper) (by
      have ha_pos : 0 < a p := by
        rw [a_eq_leTwo p hp1 hp2]
        exact div_pos (by linarith) (by linarith)
      have ha_lt : a p < 1 := a_lt_one_of_one_lt_of_lt_two p hp1 hp2
      have hlt1 : a p * y < y := by
        simpa using mul_lt_mul_of_pos_right ha_lt hy_pos
      have hlt2 : y < y / a p := by
        rw [div_eq_mul_inv]
        have hinv : 1 < (a p)⁻¹ := by
          rw [one_lt_inv₀ ha_pos]
          exact ha_lt
        nlinarith
      exact le_trans (le_of_lt hlt1) (le_of_lt hlt2))
    hbc hcz hd

lemma uCandidate_tangent_x_Q1_boundary_to_Q2_leTwo
    (p : ℝ) (hp1 : 1 < p) (hp2 : p < 2) {z y : ℝ}
    (hy_pos : 0 < y) (hz_left : z < -y) :
    uCandidate p z y ≤
      uCandidate p (y / a p) y +
        DxuCandidate p (y / a p) y * (z - y / a p) := by
  have hbc := uCandidate_tangent_x_Q1_boundary_to_Q3_A2_boundary_leTwo
    (p := p) (hp1 := hp1) (hp2 := hp2) (y := y) hy_pos
  have hcz := uCandidate_tangent_x_Q3_A2_boundary_to_Q2_leTwo
    (p := p) (hp1 := hp1) (hp2 := hp2) (z := z) (y := y)
    hy_pos hz_left
  have hd : DxuCandidate p (y / a p) y ≤ DxuCandidate p (a p * y) y :=
    le_trans
      (DxuCandidate_Q1_boundary_le_diag_leTwo
        (p := p) (hp1 := hp1) (hp2 := hp2) (y := y) hy_pos)
      (DxuCandidate_diag_le_Q3_A1_boundary_leTwo
        (p := p) (hp1 := hp1) (hp2 := hp2) (y := y) hy_pos)
  exact tangent_glue_two_backward_leTwo_local
    (fun t => uCandidate p t y) (fun t => DxuCandidate p t y)
    (by
      have ha_nonneg : 0 ≤ a p := a_nonneg_of_one_lt_of_lt_two p hp1 hp2
      have hnonneg : 0 ≤ a p * y := mul_nonneg ha_nonneg hy_pos.le
      linarith)
    (by
      have ha_pos : 0 < a p := by
        rw [a_eq_leTwo p hp1 hp2]
        exact div_pos (by linarith) (by linarith)
      have ha_lt : a p < 1 := a_lt_one_of_one_lt_of_lt_two p hp1 hp2
      have hlt1 : a p * y < y := by
        simpa using mul_lt_mul_of_pos_right ha_lt hy_pos
      have hlt2 : y < y / a p := by
        rw [div_eq_mul_inv]
        have hinv : 1 < (a p)⁻¹ := by
          rw [one_lt_inv₀ ha_pos]
          exact ha_lt
        nlinarith
      exact le_trans (le_of_lt hlt1) (le_of_lt hlt2))
    hbc hcz hd

lemma uCandidate_tangent_x_Q1_boundary_to_antidiag_leTwo
    (p : ℝ) (hp1 : 1 < p) (hp2 : p < 2) {y : ℝ}
    (hy_pos : 0 < y) :
    uCandidate p (-y) y ≤
      uCandidate p (y / a p) y +
        DxuCandidate p (y / a p) y * ((-y) - y / a p) := by
  have hbc := uCandidate_tangent_x_Q1_boundary_to_Q3_A2_boundary_leTwo
    (p := p) (hp1 := hp1) (hp2 := hp2) (y := y) hy_pos
  have hca := uCandidate_tangent_x_Q3_A2_boundary_to_antidiag_leTwo
    (p := p) (hp1 := hp1) (hp2 := hp2) (y := y) hy_pos
  have hd : DxuCandidate p (y / a p) y ≤ DxuCandidate p (a p * y) y :=
    le_trans
      (DxuCandidate_Q1_boundary_le_diag_leTwo
        (p := p) (hp1 := hp1) (hp2 := hp2) (y := y) hy_pos)
      (DxuCandidate_diag_le_Q3_A1_boundary_leTwo
        (p := p) (hp1 := hp1) (hp2 := hp2) (y := y) hy_pos)
  exact tangent_glue_two_backward_leTwo_local
    (fun t => uCandidate p t y) (fun t => DxuCandidate p t y)
    (by
      have ha_nonneg : 0 ≤ a p := a_nonneg_of_one_lt_of_lt_two p hp1 hp2
      have hnonneg : 0 ≤ a p * y := mul_nonneg ha_nonneg hy_pos.le
      linarith)
    (by
      have ha_pos : 0 < a p := by
        rw [a_eq_leTwo p hp1 hp2]
        exact div_pos (by linarith) (by linarith)
      have ha_lt : a p < 1 := a_lt_one_of_one_lt_of_lt_two p hp1 hp2
      have hlt1 : a p * y < y := by
        simpa using mul_lt_mul_of_pos_right ha_lt hy_pos
      have hlt2 : y < y / a p := by
        rw [div_eq_mul_inv]
        have hinv : 1 < (a p)⁻¹ := by
          rw [one_lt_inv₀ ha_pos]
          exact ha_lt
        nlinarith
      exact le_trans (le_of_lt hlt1) (le_of_lt hlt2))
    hbc hca hd

lemma uCandidate_tangent_x_Q1_A1_to_Q3_A2_leTwo
    (p : ℝ) (hp1 : 1 < p) (hp2 : p < 2) {x z y : ℝ}
    (hy_pos : 0 < y) (hx_lower : y / a p < x)
    (hz_lower : a p * y < z) (hz_upper : z < y) :
    uCandidate p z y ≤
      uCandidate p x y + DxuCandidate p x y * (z - x) := by
  have hxd := uCandidate_tangent_x_Q1_A1_to_diag_leTwo
    (p := p) (hp1 := hp1) (hp2 := hp2) (x := x) (y := y)
    hy_pos hx_lower
  have hdz := uCandidate_tangent_x_diag_to_Q3_A2_leTwo
    (p := p) (hp1 := hp1) (hp2 := hp2) (z := z) (y := y)
    hy_pos hz_lower hz_upper
  have hd := DxuCandidate_Q1_A1_le_diag_leTwo
    (p := p) (hp1 := hp1) (hp2 := hp2) (x := x) (y := y)
    hy_pos hx_lower
  exact tangent_glue_two_backward_leTwo_local
    (fun t => uCandidate p t y) (fun t => DxuCandidate p t y)
    (le_of_lt hz_upper) (by
      have ha_pos : 0 < a p := by
        rw [a_eq_leTwo p hp1 hp2]
        exact div_pos (by linarith) (by linarith)
      have ha_lt : a p < 1 := a_lt_one_of_one_lt_of_lt_two p hp1 hp2
      have hlt : y < y / a p := by
        rw [div_eq_mul_inv]
        have hinv : 1 < (a p)⁻¹ := by
          rw [one_lt_inv₀ ha_pos]
          exact ha_lt
        nlinarith
      exact le_trans (le_of_lt hlt) (le_of_lt hx_lower))
    hxd hdz hd

lemma uCandidate_tangent_x_Q1_A1_to_Q3_A2_boundary_leTwo
    (p : ℝ) (hp1 : 1 < p) (hp2 : p < 2) {x y : ℝ}
    (hy_pos : 0 < y) (hx_lower : y / a p < x) :
    uCandidate p (a p * y) y ≤
      uCandidate p x y + DxuCandidate p x y * (a p * y - x) := by
  have hxd := uCandidate_tangent_x_Q1_A1_to_diag_leTwo
    (p := p) (hp1 := hp1) (hp2 := hp2) (x := x) (y := y)
    hy_pos hx_lower
  have hdc := uCandidate_tangent_x_diag_to_Q3_A2_boundary_leTwo
    (p := p) (hp1 := hp1) (hp2 := hp2) (y := y) hy_pos
  have hd := DxuCandidate_Q1_A1_le_diag_leTwo
    (p := p) (hp1 := hp1) (hp2 := hp2) (x := x) (y := y)
    hy_pos hx_lower
  exact tangent_glue_two_backward_leTwo_local
    (fun t => uCandidate p t y) (fun t => DxuCandidate p t y)
    (by
      have ha_lt : a p < 1 := a_lt_one_of_one_lt_of_lt_two p hp1 hp2
      have hlt : a p * y < y := by
        simpa using mul_lt_mul_of_pos_right ha_lt hy_pos
      exact le_of_lt hlt)
    (by
      have ha_pos : 0 < a p := by
        rw [a_eq_leTwo p hp1 hp2]
        exact div_pos (by linarith) (by linarith)
      have ha_lt : a p < 1 := a_lt_one_of_one_lt_of_lt_two p hp1 hp2
      have hlt : y < y / a p := by
        rw [div_eq_mul_inv]
        have hinv : 1 < (a p)⁻¹ := by
          rw [one_lt_inv₀ ha_pos]
          exact ha_lt
        nlinarith
      exact le_trans (le_of_lt hlt) (le_of_lt hx_lower))
    hxd hdc hd

lemma uCandidate_tangent_x_Q1_A1_to_Q3_A1_leTwo
    (p : ℝ) (hp1 : 1 < p) (hp2 : p < 2) {x z y : ℝ}
    (hy_pos : 0 < y) (hx_lower : y / a p < x)
    (hz_lower : -y < z) (hz_upper : z < a p * y) :
    uCandidate p z y ≤
      uCandidate p x y + DxuCandidate p x y * (z - x) := by
  have hxc := uCandidate_tangent_x_Q1_A1_to_Q3_A2_boundary_leTwo
    (p := p) (hp1 := hp1) (hp2 := hp2) (x := x) (y := y)
    hy_pos hx_lower
  have hcz := uCandidate_tangent_x_Q3_A2_boundary_to_Q3_A1_leTwo
    (p := p) (hp1 := hp1) (hp2 := hp2) (z := z) (y := y)
    hy_pos hz_lower hz_upper
  have hd := DxuCandidate_Q1_A1_le_Q3_A1_boundary_leTwo
    (p := p) (hp1 := hp1) (hp2 := hp2) (x := x) (y := y)
    hy_pos hx_lower
  exact tangent_glue_two_backward_leTwo_local
    (fun t => uCandidate p t y) (fun t => DxuCandidate p t y)
    (le_of_lt hz_upper) (by
      have ha_pos : 0 < a p := by
        rw [a_eq_leTwo p hp1 hp2]
        exact div_pos (by linarith) (by linarith)
      have ha_lt : a p < 1 := a_lt_one_of_one_lt_of_lt_two p hp1 hp2
      have hlt1 : a p * y < y := by
        simpa using mul_lt_mul_of_pos_right ha_lt hy_pos
      have hlt2 : y < y / a p := by
        rw [div_eq_mul_inv]
        have hinv : 1 < (a p)⁻¹ := by
          rw [one_lt_inv₀ ha_pos]
          exact ha_lt
        nlinarith
      exact le_trans (le_of_lt hlt1) (le_trans (le_of_lt hlt2) (le_of_lt hx_lower)))
    hxc hcz hd

lemma uCandidate_tangent_x_Q1_A1_to_Q2_leTwo
    (p : ℝ) (hp1 : 1 < p) (hp2 : p < 2) {x z y : ℝ}
    (hy_pos : 0 < y) (hx_lower : y / a p < x) (hz_left : z < -y) :
    uCandidate p z y ≤
      uCandidate p x y + DxuCandidate p x y * (z - x) := by
  have hxc := uCandidate_tangent_x_Q1_A1_to_Q3_A2_boundary_leTwo
    (p := p) (hp1 := hp1) (hp2 := hp2) (x := x) (y := y)
    hy_pos hx_lower
  have hcz := uCandidate_tangent_x_Q3_A2_boundary_to_Q2_leTwo
    (p := p) (hp1 := hp1) (hp2 := hp2) (z := z) (y := y)
    hy_pos hz_left
  have hd := DxuCandidate_Q1_A1_le_Q3_A1_boundary_leTwo
    (p := p) (hp1 := hp1) (hp2 := hp2) (x := x) (y := y)
    hy_pos hx_lower
  exact tangent_glue_two_backward_leTwo_local
    (fun t => uCandidate p t y) (fun t => DxuCandidate p t y)
    (by
      have ha_nonneg : 0 ≤ a p := a_nonneg_of_one_lt_of_lt_two p hp1 hp2
      have hnonneg : 0 ≤ a p * y := mul_nonneg ha_nonneg hy_pos.le
      linarith)
    (by
      have ha_pos : 0 < a p := by
        rw [a_eq_leTwo p hp1 hp2]
        exact div_pos (by linarith) (by linarith)
      have ha_lt : a p < 1 := a_lt_one_of_one_lt_of_lt_two p hp1 hp2
      have hlt1 : a p * y < y := by
        simpa using mul_lt_mul_of_pos_right ha_lt hy_pos
      have hlt2 : y < y / a p := by
        rw [div_eq_mul_inv]
        have hinv : 1 < (a p)⁻¹ := by
          rw [one_lt_inv₀ ha_pos]
          exact ha_lt
        nlinarith
      exact le_trans (le_of_lt hlt1) (le_trans (le_of_lt hlt2) (le_of_lt hx_lower)))
    hxc hcz hd

lemma uCandidate_tangent_x_Q1_A1_to_antidiag_leTwo
    (p : ℝ) (hp1 : 1 < p) (hp2 : p < 2) {x y : ℝ}
    (hy_pos : 0 < y) (hx_lower : y / a p < x) :
    uCandidate p (-y) y ≤
      uCandidate p x y + DxuCandidate p x y * ((-y) - x) := by
  have hxc := uCandidate_tangent_x_Q1_A1_to_Q3_A2_boundary_leTwo
    (p := p) (hp1 := hp1) (hp2 := hp2) (x := x) (y := y)
    hy_pos hx_lower
  have hca := uCandidate_tangent_x_Q3_A2_boundary_to_antidiag_leTwo
    (p := p) (hp1 := hp1) (hp2 := hp2) (y := y) hy_pos
  have hd := DxuCandidate_Q1_A1_le_Q3_A1_boundary_leTwo
    (p := p) (hp1 := hp1) (hp2 := hp2) (x := x) (y := y)
    hy_pos hx_lower
  exact tangent_glue_two_backward_leTwo_local
    (fun t => uCandidate p t y) (fun t => DxuCandidate p t y)
    (by
      have ha_nonneg : 0 ≤ a p := a_nonneg_of_one_lt_of_lt_two p hp1 hp2
      have hnonneg : 0 ≤ a p * y := mul_nonneg ha_nonneg hy_pos.le
      linarith)
    (by
      have ha_pos : 0 < a p := by
        rw [a_eq_leTwo p hp1 hp2]
        exact div_pos (by linarith) (by linarith)
      have ha_lt : a p < 1 := a_lt_one_of_one_lt_of_lt_two p hp1 hp2
      have hlt1 : a p * y < y := by
        simpa using mul_lt_mul_of_pos_right ha_lt hy_pos
      have hlt2 : y < y / a p := by
        rw [div_eq_mul_inv]
        have hinv : 1 < (a p)⁻¹ := by
          rw [one_lt_inv₀ ha_pos]
          exact ha_lt
        nlinarith
      exact le_trans (le_of_lt hlt1) (le_trans (le_of_lt hlt2) (le_of_lt hx_lower)))
    hxc hca hd

lemma uCandidate_tangent_x_backward_of_y_pos_leTwo
    (p : ℝ) (hp1 : 1 < p) (hp2 : p < 2) {x z y : ℝ}
    (hy_pos : 0 < y) (hzx : z < x) :
    uCandidate p z y ≤
      uCandidate p x y + DxuCandidate p x y * (z - x) := by
  have ha_pos : 0 < a p := by
    rw [a_eq_leTwo p hp1 hp2]
    exact div_pos (by linarith) (by linarith)
  have ha_nonneg : 0 ≤ a p := ha_pos.le
  have ha_lt : a p < 1 := a_lt_one_of_one_lt_of_lt_two p hp1 hp2
  have hneg_lt_c : -y < a p * y := by
    have hnonneg : 0 ≤ a p * y := mul_nonneg ha_nonneg hy_pos.le
    linarith
  have hc_lt_y : a p * y < y := by
    simpa using mul_lt_mul_of_pos_right ha_lt hy_pos
  have hy_lt_b : y < y / a p := by
    rw [div_eq_mul_inv]
    have hinv : 1 < (a p)⁻¹ := by
      rw [one_lt_inv₀ ha_pos]
      exact ha_lt
    nlinarith
  by_cases hx_b : y / a p < x
  · by_cases hz_b : y / a p < z
    · exact uCandidate_tangent_x_on_Q1_A1_segment_leTwo
        (p := p) (hp1 := hp1) (hp2 := hp2) (x := x) (z := z) (y := y)
        hy_pos hx_b hz_b
    · have hzb_le : z ≤ y / a p := le_of_not_gt hz_b
      rcases hzb_le.lt_or_eq with hzb_lt | hzb_eq
      · by_cases hz_y : y < z
        · exact uCandidate_tangent_x_Q1_A1_to_A2_leTwo
            (p := p) (hp1 := hp1) (hp2 := hp2) (x := x) (z := z) (y := y)
            hy_pos hx_b hz_y hzb_lt
        · have hzy_le : z ≤ y := le_of_not_gt hz_y
          rcases hzy_le.lt_or_eq with hzy | hzy_eq
          · by_cases hz_c : a p * y < z
            · exact uCandidate_tangent_x_Q1_A1_to_Q3_A2_leTwo
                (p := p) (hp1 := hp1) (hp2 := hp2) (x := x) (z := z) (y := y)
                hy_pos hx_b hz_c hzy
            · have hzc_le : z ≤ a p * y := le_of_not_gt hz_c
              rcases hzc_le.lt_or_eq with hzc | hzc_eq
              · by_cases hz_a : -y < z
                · exact uCandidate_tangent_x_Q1_A1_to_Q3_A1_leTwo
                    (p := p) (hp1 := hp1) (hp2 := hp2) (x := x) (z := z) (y := y)
                    hy_pos hx_b hz_a hzc
                · have hza_le : z ≤ -y := le_of_not_gt hz_a
                  rcases hza_le.lt_or_eq with hza | hza_eq
                  · exact uCandidate_tangent_x_Q1_A1_to_Q2_leTwo
                      (p := p) (hp1 := hp1) (hp2 := hp2) (x := x) (z := z) (y := y)
                      hy_pos hx_b hza
                  · subst z
                    exact uCandidate_tangent_x_Q1_A1_to_antidiag_leTwo
                      (p := p) (hp1 := hp1) (hp2 := hp2) (x := x) (y := y)
                      hy_pos hx_b
              · subst z
                exact uCandidate_tangent_x_Q1_A1_to_Q3_A2_boundary_leTwo
                  (p := p) (hp1 := hp1) (hp2 := hp2) (x := x) (y := y)
                  hy_pos hx_b
          · subst z
            exact uCandidate_tangent_x_Q1_A1_to_diag_leTwo
              (p := p) (hp1 := hp1) (hp2 := hp2) (x := x) (y := y)
              hy_pos hx_b
      · subst z
        exact uCandidate_tangent_x_Q1_A1_to_boundary_leTwo
          (p := p) (hp1 := hp1) (hp2 := hp2) (x := x) (y := y)
          hy_pos hx_b
  · have hxb_le : x ≤ y / a p := le_of_not_gt hx_b
    rcases hxb_le.lt_or_eq with hxb_lt | hxb_eq
    · by_cases hx_y : y < x
      · by_cases hz_y : y < z
        · exact uCandidate_tangent_x_on_Q1_A2_segment_leTwo
            (p := p) (hp1 := hp1) (hp2 := hp2) (x := x) (z := z) (y := y)
            hy_pos hx_y hxb_lt hz_y (lt_trans hzx hxb_lt)
        · have hzy_le : z ≤ y := le_of_not_gt hz_y
          rcases hzy_le.lt_or_eq with hzy | hzy_eq
          · by_cases hz_c : a p * y < z
            · exact uCandidate_tangent_x_Q1_A2_to_Q3_A2_leTwo
                (p := p) (hp1 := hp1) (hp2 := hp2) (x := x) (z := z) (y := y)
                hy_pos hx_y hxb_lt hz_c hzy
            · have hzc_le : z ≤ a p * y := le_of_not_gt hz_c
              rcases hzc_le.lt_or_eq with hzc | hzc_eq
              · by_cases hz_a : -y < z
                · exact uCandidate_tangent_x_Q1_A2_to_Q3_A1_leTwo
                    (p := p) (hp1 := hp1) (hp2 := hp2) (x := x) (z := z) (y := y)
                    hy_pos hx_y hxb_lt hz_a hzc
                · have hza_le : z ≤ -y := le_of_not_gt hz_a
                  rcases hza_le.lt_or_eq with hza | hza_eq
                  · exact uCandidate_tangent_x_Q1_A2_to_Q2_leTwo
                      (p := p) (hp1 := hp1) (hp2 := hp2) (x := x) (z := z) (y := y)
                      hy_pos hx_y hxb_lt hza
                  · subst z
                    exact uCandidate_tangent_x_Q1_A2_to_antidiag_leTwo
                      (p := p) (hp1 := hp1) (hp2 := hp2) (x := x) (y := y)
                      hy_pos hx_y hxb_lt
              · subst z
                exact uCandidate_tangent_x_Q1_A2_to_Q3_A2_boundary_leTwo
                  (p := p) (hp1 := hp1) (hp2 := hp2) (x := x) (y := y)
                  hy_pos hx_y hxb_lt
          · subst z
            exact uCandidate_tangent_x_Q1_A2_to_diag_leTwo
              (p := p) (hp1 := hp1) (hp2 := hp2) (x := x) (y := y)
              hy_pos hx_y hxb_lt
      · have hxy_le : x ≤ y := le_of_not_gt hx_y
        rcases hxy_le.lt_or_eq with hxy | hxy_eq
        · by_cases hx_c : a p * y < x
          · by_cases hz_c : a p * y < z
            · exact uCandidate_tangent_x_on_Q3_A2_segment_leTwo
                (p := p) (hp1 := hp1) (hp2 := hp2) (x := x) (z := z) (y := y)
                hy_pos hx_c hxy hz_c (lt_trans hzx hxy)
            · have hzc_le : z ≤ a p * y := le_of_not_gt hz_c
              rcases hzc_le.lt_or_eq with hzc | hzc_eq
              · by_cases hz_a : -y < z
                · exact uCandidate_tangent_x_Q3_A2_to_Q3_A1_leTwo
                    (p := p) (hp1 := hp1) (hp2 := hp2) (x := x) (z := z) (y := y)
                    hy_pos hx_c hxy hz_a hzc
                · have hza_le : z ≤ -y := le_of_not_gt hz_a
                  rcases hza_le.lt_or_eq with hza | hza_eq
                  · exact uCandidate_tangent_x_Q3_A2_to_Q2_leTwo
                      (p := p) (hp1 := hp1) (hp2 := hp2) (x := x) (z := z) (y := y)
                      hy_pos hx_c hxy hza
                  · subst z
                    exact uCandidate_tangent_x_Q3_A2_to_antidiag_leTwo
                      (p := p) (hp1 := hp1) (hp2 := hp2) (x := x) (y := y)
                      hy_pos hx_c hxy
              · subst z
                exact uCandidate_tangent_x_Q3_A2_to_boundary_leTwo
                  (p := p) (hp1 := hp1) (hp2 := hp2) (x := x) (y := y)
                  hy_pos hx_c hxy
          · have hxc_le : x ≤ a p * y := le_of_not_gt hx_c
            rcases hxc_le.lt_or_eq with hxc | hxc_eq
            · by_cases hx_a : -y < x
              · by_cases hz_a : -y < z
                · exact uCandidate_tangent_x_on_Q3_A1_segment_leTwo
                    (p := p) (hp1 := hp1) (hp2 := hp2) (x := x) (z := z) (y := y)
                    hy_pos hx_a hxc hz_a (lt_trans hzx hxc)
                · have hza_le : z ≤ -y := le_of_not_gt hz_a
                  rcases hza_le.lt_or_eq with hza | hza_eq
                  · exact uCandidate_tangent_x_Q3_A1_to_Q2_leTwo
                      (p := p) (hp1 := hp1) (hp2 := hp2) (x := x) (z := z) (y := y)
                      hy_pos hx_a hxc hza
                  · subst z
                    exact uCandidate_tangent_x_Q3_A1_to_antidiag_leTwo
                      (p := p) (hp1 := hp1) (hp2 := hp2) (x := x) (y := y)
                      hy_pos hx_a hxc
              · have hxa_le : x ≤ -y := le_of_not_gt hx_a
                rcases hxa_le.lt_or_eq with hxa | hxa_eq
                · exact uCandidate_tangent_x_on_Q2_A1_segment_leTwo
                    (p := p) (hp1 := hp1) (hp2 := hp2) (x := x) (z := z) (y := y)
                    hy_pos hxa (lt_trans hzx hxa)
                · subst x
                  exact uCandidate_tangent_x_antidiag_to_Q2_leTwo
                    (p := p) (hp1 := hp1) (hp2 := hp2) (z := z) (y := y)
                    hy_pos (by simpa using hzx)
            · subst x
              by_cases hz_a : -y < z
              · exact uCandidate_tangent_x_Q3_A2_boundary_to_Q3_A1_leTwo
                  (p := p) (hp1 := hp1) (hp2 := hp2) (z := z) (y := y)
                  hy_pos hz_a (by simpa using hzx)
              · have hza_le : z ≤ -y := le_of_not_gt hz_a
                rcases hza_le.lt_or_eq with hza | hza_eq
                · exact uCandidate_tangent_x_Q3_A2_boundary_to_Q2_leTwo
                    (p := p) (hp1 := hp1) (hp2 := hp2) (z := z) (y := y)
                    hy_pos hza
                · subst z
                  exact uCandidate_tangent_x_Q3_A2_boundary_to_antidiag_leTwo
                    (p := p) (hp1 := hp1) (hp2 := hp2) (y := y) hy_pos
        · subst x
          by_cases hz_c : a p * y < z
          · exact uCandidate_tangent_x_diag_to_Q3_A2_leTwo
              (p := p) (hp1 := hp1) (hp2 := hp2) (z := z) (y := y)
              hy_pos hz_c (by simpa using hzx)
          · have hzc_le : z ≤ a p * y := le_of_not_gt hz_c
            rcases hzc_le.lt_or_eq with hzc | hzc_eq
            · by_cases hz_a : -y < z
              · exact uCandidate_tangent_x_diag_to_Q3_A1_leTwo
                  (p := p) (hp1 := hp1) (hp2 := hp2) (z := z) (y := y)
                  hy_pos hz_a hzc
              · have hza_le : z ≤ -y := le_of_not_gt hz_a
                rcases hza_le.lt_or_eq with hza | hza_eq
                · exact uCandidate_tangent_x_diag_to_Q2_leTwo
                    (p := p) (hp1 := hp1) (hp2 := hp2) (z := z) (y := y)
                    hy_pos hza
                · subst z
                  exact uCandidate_tangent_x_diag_to_antidiag_leTwo
                    (p := p) (hp1 := hp1) (hp2 := hp2) (y := y) hy_pos
            · subst z
              exact uCandidate_tangent_x_diag_to_Q3_A2_boundary_leTwo
                (p := p) (hp1 := hp1) (hp2 := hp2) (y := y) hy_pos
    · subst x
      by_cases hz_y : y < z
      · exact uCandidate_tangent_x_Q1_boundary_to_A2_leTwo
          (p := p) (hp1 := hp1) (hp2 := hp2) (z := z) (y := y)
          hy_pos hz_y (by simpa using hzx)
      · have hzy_le : z ≤ y := le_of_not_gt hz_y
        rcases hzy_le.lt_or_eq with hzy | hzy_eq
        · by_cases hz_c : a p * y < z
          · exact uCandidate_tangent_x_Q1_boundary_to_Q3_A2_leTwo
              (p := p) (hp1 := hp1) (hp2 := hp2) (z := z) (y := y)
              hy_pos hz_c hzy
          · have hzc_le : z ≤ a p * y := le_of_not_gt hz_c
            rcases hzc_le.lt_or_eq with hzc | hzc_eq
            · by_cases hz_a : -y < z
              · exact uCandidate_tangent_x_Q1_boundary_to_Q3_A1_leTwo
                  (p := p) (hp1 := hp1) (hp2 := hp2) (z := z) (y := y)
                  hy_pos hz_a hzc
              · have hza_le : z ≤ -y := le_of_not_gt hz_a
                rcases hza_le.lt_or_eq with hza | hza_eq
                · exact uCandidate_tangent_x_Q1_boundary_to_Q2_leTwo
                    (p := p) (hp1 := hp1) (hp2 := hp2) (z := z) (y := y)
                    hy_pos hza
                · subst z
                  exact uCandidate_tangent_x_Q1_boundary_to_antidiag_leTwo
                    (p := p) (hp1 := hp1) (hp2 := hp2) (y := y) hy_pos
            · subst z
              exact uCandidate_tangent_x_Q1_boundary_to_Q3_A2_boundary_leTwo
                (p := p) (hp1 := hp1) (hp2 := hp2) (y := y) hy_pos
        · subst z
          exact uCandidate_tangent_x_Q1_boundary_to_diag_leTwo
            (p := p) (hp1 := hp1) (hp2 := hp2) (y := y) hy_pos

lemma uCandidate_tangent_x_backward_of_y_pos_le_leTwo
    (p : ℝ) (hp1 : 1 < p) (hp2 : p < 2) {x z y : ℝ}
    (hy_pos : 0 < y) (hzx : z ≤ x) :
    uCandidate p z y ≤
      uCandidate p x y + DxuCandidate p x y * (z - x) := by
  rcases hzx.lt_or_eq with hzx_lt | rfl
  · exact uCandidate_tangent_x_backward_of_y_pos_leTwo
      (p := p) (hp1 := hp1) (hp2 := hp2) (x := x) (z := z) (y := y)
      hy_pos hzx_lt
  · simp

lemma uCandidate_tangent_x_increment_of_y_pos_leTwo
    (p : ℝ) (hp1 : 1 < p) (hp2 : p < 2) {x y h : ℝ}
    (hy_pos : 0 < y) :
    uCandidate p (x + h) y ≤
      uCandidate p x y + DxuCandidate p x y * h := by
  rcases le_total 0 h with hh | hh
  · have hxz : x ≤ x + h := by linarith
    have hmain := uCandidate_tangent_x_forward_of_y_pos_le_leTwo
      (p := p) (hp1 := hp1) (hp2 := hp2) (x := x) (z := x + h) (y := y)
      hy_pos hxz
    simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using hmain
  · have hxz : x + h ≤ x := by linarith
    have hmain := uCandidate_tangent_x_backward_of_y_pos_le_leTwo
      (p := p) (hp1 := hp1) (hp2 := hp2) (x := x) (z := x + h) (y := y)
      hy_pos hxz
    simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using hmain

lemma uCandidate_tangent_x_increment_of_y_neg_leTwo
    (p : ℝ) (hp1 : 1 < p) (hp2 : p < 2) {x y h : ℝ}
    (hy_neg : y < 0) :
    uCandidate p (x + h) y ≤
      uCandidate p x y + DxuCandidate p x y * h := by
  exact uCandidate_tangent_x_increment_of_y_neg_leTwo_of_pos
    p (fun {x y h} hy_pos =>
      uCandidate_tangent_x_increment_of_y_pos_leTwo
        (p := p) (hp1 := hp1) (hp2 := hp2) (x := x) (y := y) (h := h) hy_pos)
    hy_neg

lemma rpow_tangent_nonneg_leTwo
    (p : ℝ) (hp1 : 1 < p) {x z : ℝ}
    (hx : 0 < x) (hz : 0 ≤ z) :
    x ^ p + (p * x ^ (p - 1)) * (z - x) ≤ z ^ p := by
  have hconv : ConvexOn ℝ (Set.Ici (0 : ℝ)) (fun t : ℝ => t ^ p) :=
    convexOn_rpow (by linarith : 1 ≤ p)
  have hderiv :
      HasDerivAt (fun t : ℝ => t ^ p) (p * x ^ (p - 1)) x :=
    Real.hasDerivAt_rpow_const (Or.inl (ne_of_gt hx))
  rcases lt_trichotomy x z with hxz | hxz | hzx
  · have hslope :=
      hconv.le_slope_of_hasDerivAt
        (x := x) (y := z) (f' := p * x ^ (p - 1))
        hx.le hz hxz hderiv
    have hslope' :
        p * x ^ (p - 1) ≤ (z ^ p - x ^ p) / (z - x) := by
      simpa [slope_def_field] using hslope
    have hden_pos : 0 < z - x := by linarith
    have hmul := mul_le_mul_of_nonneg_right hslope' hden_pos.le
    field_simp [hden_pos.ne'] at hmul
    linarith
  · subst z
    simp
  · have hslope :=
      hconv.slope_le_of_hasDerivAt
        (x := z) (y := x) (f' := p * x ^ (p - 1))
        hz hx.le hzx hderiv
    have hslope' :
        (x ^ p - z ^ p) / (x - z) ≤ p * x ^ (p - 1) := by
      simpa [slope_def_field] using hslope
    have hden_pos : 0 < x - z := by linarith
    have hmul := mul_le_mul_of_nonneg_right hslope' hden_pos.le
    field_simp [hden_pos.ne'] at hmul
    linarith

lemma abs_rpow_tangent_leTwo
    (p : ℝ) (hp1 : 1 < p) (x z : ℝ) :
    |x| ^ p +
        (if 0 < x then p * x ^ (p - 1)
         else if x < 0 then -p * (-x) ^ (p - 1)
         else 0) * (z - x) ≤
      |z| ^ p := by
  by_cases hxpos : 0 < x
  · by_cases hzneg : z < 0
    · have hxpow_nonneg : 0 ≤ x ^ p := Real.rpow_nonneg hxpos.le p
      have hxpow1_nonneg : 0 ≤ x ^ (p - 1) := Real.rpow_nonneg hxpos.le (p - 1)
      have hlin :
          x ^ p + (p * x ^ (p - 1)) * (z - x) ≤ 0 := by
        have hz_le : z ≤ 0 := le_of_lt hzneg
        have hp_nonneg : 0 ≤ p := by linarith
        have hterm_nonpos : p * x ^ (p - 1) * z ≤ 0 := by
          exact mul_nonpos_of_nonneg_of_nonpos
            (mul_nonneg hp_nonneg hxpow1_nonneg) hz_le
        have hshift : x ^ (p - 1) * x = x ^ p := by
          calc
            x ^ (p - 1) * x = x ^ (p - 1) * x ^ (1 : ℝ) := by rw [Real.rpow_one]
            _ = x ^ ((p - 1) + 1) := by rw [Real.rpow_add hxpos]
            _ = x ^ p := by ring_nf
        calc
          x ^ p + (p * x ^ (p - 1)) * (z - x)
              = (1 - p) * x ^ p + p * x ^ (p - 1) * z := by
                  rw [← hshift]
                  ring
          _ ≤ 0 := by
            have hfirst : (1 - p) * x ^ p ≤ 0 := by
              exact mul_nonpos_of_nonpos_of_nonneg (by linarith) hxpow_nonneg
            linarith
      have hzpow_nonneg : 0 ≤ |z| ^ p := Real.rpow_nonneg (abs_nonneg z) p
      simpa [hxpos, abs_of_pos hxpos] using hlin.trans hzpow_nonneg
    · have hz_nonneg : 0 ≤ z := le_of_not_gt hzneg
      have ht := rpow_tangent_nonneg_leTwo p hp1 hxpos hz_nonneg
      simpa [hxpos, abs_of_pos hxpos, abs_of_nonneg hz_nonneg] using ht
  · by_cases hxneg : x < 0
    · by_cases hzpos : 0 < z
      · have hxabs_pos : 0 < -x := by linarith
        have hxpow_nonneg : 0 ≤ (-x) ^ p := Real.rpow_nonneg (le_of_lt hxabs_pos) p
        have hxpow1_nonneg : 0 ≤ (-x) ^ (p - 1) :=
          Real.rpow_nonneg (le_of_lt hxabs_pos) (p - 1)
        have hlin :
            (-x) ^ p + (-p * (-x) ^ (p - 1)) * (z - x) ≤ 0 := by
          have hp_nonneg : 0 ≤ p := by linarith
          have hterm_nonpos : -(p * (-x) ^ (p - 1) * z) ≤ 0 := by
            have hz_nonneg : 0 ≤ z := le_of_lt hzpos
            have hnonneg : 0 ≤ p * (-x) ^ (p - 1) * z :=
              mul_nonneg (mul_nonneg hp_nonneg hxpow1_nonneg) hz_nonneg
            linarith
          have hshift : (-x) ^ (p - 1) * (-x) = (-x) ^ p := by
            calc
              (-x) ^ (p - 1) * (-x) = (-x) ^ (p - 1) * (-x) ^ (1 : ℝ) := by
                rw [Real.rpow_one]
              _ = (-x) ^ ((p - 1) + 1) := by rw [Real.rpow_add hxabs_pos]
              _ = (-x) ^ p := by ring_nf
          calc
            (-x) ^ p + (-p * (-x) ^ (p - 1)) * (z - x)
                = (1 - p) * (-x) ^ p - p * (-x) ^ (p - 1) * z := by
                    rw [← hshift]
                    ring
            _ ≤ 0 := by
              have hfirst : (1 - p) * (-x) ^ p ≤ 0 := by
                exact mul_nonpos_of_nonpos_of_nonneg (by linarith) hxpow_nonneg
              linarith
        have hzpow_nonneg : 0 ≤ |z| ^ p := Real.rpow_nonneg (abs_nonneg z) p
        simpa [hxpos, hxneg, abs_of_neg hxneg] using hlin.trans hzpow_nonneg
      · have hz_nonpos : z ≤ 0 := le_of_not_gt hzpos
        have ht := rpow_tangent_nonneg_leTwo p hp1
          (x := -x) (z := -z) (by linarith) (by linarith)
        have hrewrite :
            (-x) ^ p + (p * (-x) ^ (p - 1)) * ((-z) - (-x))
              = (-x) ^ p + (-p * (-x) ^ (p - 1)) * (z - x) := by ring
        rw [hrewrite] at ht
        simpa [hxpos, hxneg, abs_of_neg hxneg, abs_of_nonpos hz_nonpos] using ht
    · have hx0 : x = 0 := le_antisymm (le_of_not_gt hxpos) (le_of_not_gt hxneg)
      subst x
      simp only [abs_zero, lt_irrefl, if_false, zero_mul, sub_zero, add_zero]
      rw [Real.zero_rpow (by linarith : p ≠ 0)]
      exact Real.rpow_nonneg (abs_nonneg z) p

lemma axisCoeff_nonpos_leTwo
    (p : ℝ) (hp1 : 1 < p) (hp2 : p < 2) :
    alpha p * (1 - pStar p / 2) ≤ 0 := by
  have ha : 0 ≤ alpha p := alpha_nonneg_of_one_lt_of_lt_two p hp1 hp2
  have hstar : 1 ≤ pStar p / 2 := one_le_half_pStar_of_one_lt_of_lt_two p hp1 hp2
  exact mul_nonpos_of_nonneg_of_nonpos ha (by linarith)

lemma uCandidate_axis_eq_abs_rpow_leTwo
    (p : ℝ) (hp1 : 1 < p) (hp2 : p < 2) (x : ℝ) :
    uCandidate p x 0 = alpha p * (1 - pStar p / 2) * |x| ^ p := by
  let C : ℝ := alpha p * (1 - pStar p / 2)
  rcases lt_trichotomy x 0 with hxneg | hx0 | hxpos
  · have hQ2 : QuarterPlane2 x 0 := ⟨le_of_lt hxneg, by linarith, by linarith⟩
    have hxpos' : 0 < -x := by linarith
    have hcl : closureA1 p (-x) 0 := by
      have ha_nonneg : 0 ≤ a p := a_nonneg_of_one_lt_of_lt_two p hp1 hp2
      exact ⟨le_of_lt hxpos', by linarith, mul_nonneg ha_nonneg (le_of_lt hxpos')⟩
    have hshift : (-x) ^ (p - 1) * (-x) = (-x) ^ p := by
      calc
        (-x) ^ (p - 1) * (-x) = (-x) ^ (p - 1) * (-x) ^ (1 : ℝ) := by
          rw [Real.rpow_one]
        _ = (-x) ^ ((p - 1) + 1) := by rw [Real.rpow_add hxpos']
        _ = (-x) ^ p := by ring_nf
    calc
      uCandidate p x 0 = auxFunction1 p (-x) 0 := by
        simpa using uCandidate_eq_Q2_leTwo p hQ2
      _ = uA1 p (-x) 0 := by simp [auxFunction1, hcl]
      _ = C * |x| ^ p := by
        simp [uA1, hxpos', C, abs_of_neg hxneg]
        rw [← hshift]
        ring
  · subst x
    have hQ : QuarterPlane 0 0 := by norm_num [QuarterPlane]
    calc
      uCandidate p 0 0 = auxFunction1 p 0 0 := uCandidate_eq_Q1_leTwo p hQ
      _ = 0 := by simp [auxFunction1, closureA1, uA1]
      _ = C * |(0 : ℝ)| ^ p := by
        simp [C, Real.zero_rpow (by linarith : p ≠ 0)]
  · have hQ : QuarterPlane x 0 := ⟨le_of_lt hxpos, by linarith, by linarith⟩
    have hcl : closureA1 p x 0 := by
      have ha_nonneg : 0 ≤ a p := a_nonneg_of_one_lt_of_lt_two p hp1 hp2
      exact ⟨le_of_lt hxpos, by linarith, mul_nonneg ha_nonneg (le_of_lt hxpos)⟩
    have hshift : x ^ (p - 1) * x = x ^ p := by
      calc
        x ^ (p - 1) * x = x ^ (p - 1) * x ^ (1 : ℝ) := by
          rw [Real.rpow_one]
        _ = x ^ ((p - 1) + 1) := by rw [Real.rpow_add hxpos]
        _ = x ^ p := by ring_nf
    calc
      uCandidate p x 0 = auxFunction1 p x 0 := uCandidate_eq_Q1_leTwo p hQ
      _ = uA1 p x 0 := by simp [auxFunction1, hcl]
      _ = C * |x| ^ p := by
        simp [uA1, hxpos, C, abs_of_pos hxpos]
        rw [← hshift]
        ring

lemma DxuCandidate_axis_eq_abs_deriv_leTwo
    (p : ℝ) (hp1 : 1 < p) (hp2 : p < 2) (x : ℝ) :
    DxuCandidate p x 0 =
      alpha p * (1 - pStar p / 2) *
        (if 0 < x then p * x ^ (p - 1)
         else if x < 0 then -p * (-x) ^ (p - 1)
         else 0) := by
  let C : ℝ := alpha p * (1 - pStar p / 2)
  have hpStar : pStar p = q p :=
    pStar_eq_q_of_one_lt_of_lt_two p hp1 hp2
  have hp_ne_one : p ≠ 1 := by linarith
  have hpden_ne : p - 1 ≠ 0 := by linarith
  rcases lt_trichotomy x 0 with hxneg | hx0 | hxpos
  · have hQ2 : QuarterPlane2 x 0 := ⟨le_of_lt hxneg, by linarith, by linarith⟩
    have hxpos' : 0 < -x := by linarith
    have hcl : closureA1 p (-x) 0 := by
      have ha_nonneg : 0 ≤ a p := a_nonneg_of_one_lt_of_lt_two p hp1 hp2
      exact ⟨le_of_lt hxpos', by linarith, mul_nonneg ha_nonneg (le_of_lt hxpos')⟩
    have hshift : (-x) ^ (p - 1) = (-x) ^ (p - 2) * (-x) := by
      calc
        (-x) ^ (p - 1) = (-x) ^ ((p - 2) + (1 : ℝ)) := by ring_nf
        _ = (-x) ^ (p - 2) * (-x) ^ (1 : ℝ) := by rw [Real.rpow_add hxpos']
        _ = (-x) ^ (p - 2) * (-x) := by rw [Real.rpow_one]
    calc
      DxuCandidate p x 0 = -DxauxFunction1 p (-x) 0 := by
        simpa using DxuCandidate_eq_Q2_leTwo p hQ2
      _ = C * (-p * (-x) ^ (p - 1)) := by
        simp [DxauxFunction1, hcl, DxuA1, hxpos', C, hpStar, q, hp_ne_one]
        rw [hshift]
        field_simp [hpden_ne]
        ring
      _ = C *
          (if 0 < x then p * x ^ (p - 1)
           else if x < 0 then -p * (-x) ^ (p - 1)
           else 0) := by
        simp [hxneg, not_lt_of_gt hxneg]
  · subst x
    have hQ : QuarterPlane 0 0 := by norm_num [QuarterPlane]
    calc
      DxuCandidate p 0 0 = DxauxFunction1 p 0 0 := DxuCandidate_eq_Q1_leTwo p hQ
      _ = 0 := by simp [DxauxFunction1, closureA1, DxuA1]
      _ = C *
          (if 0 < (0 : ℝ) then p * (0 : ℝ) ^ (p - 1)
           else if (0 : ℝ) < 0 then -p * (-(0 : ℝ)) ^ (p - 1)
           else 0) := by simp [C]
  · have hQ : QuarterPlane x 0 := ⟨le_of_lt hxpos, by linarith, by linarith⟩
    have hcl : closureA1 p x 0 := by
      have ha_nonneg : 0 ≤ a p := a_nonneg_of_one_lt_of_lt_two p hp1 hp2
      exact ⟨le_of_lt hxpos, by linarith, mul_nonneg ha_nonneg (le_of_lt hxpos)⟩
    have hshift : x ^ (p - 1) = x ^ (p - 2) * x := by
      calc
        x ^ (p - 1) = x ^ ((p - 2) + (1 : ℝ)) := by ring_nf
        _ = x ^ (p - 2) * x ^ (1 : ℝ) := by rw [Real.rpow_add hxpos]
        _ = x ^ (p - 2) * x := by rw [Real.rpow_one]
    calc
      DxuCandidate p x 0 = DxauxFunction1 p x 0 := DxuCandidate_eq_Q1_leTwo p hQ
      _ = C * (p * x ^ (p - 1)) := by
        simp [DxauxFunction1, hcl, DxuA1, hxpos, C, hpStar, q, hp_ne_one]
        rw [hshift]
        field_simp [hpden_ne]
        ring
      _ = C *
          (if 0 < x then p * x ^ (p - 1)
           else if x < 0 then -p * (-x) ^ (p - 1)
           else 0) := by
        simp [hxpos]

lemma uCandidate_tangent_x_increment_of_y_zero_leTwo
    (p : ℝ) (hp1 : 1 < p) (hp2 : p < 2) {x h : ℝ} :
    uCandidate p (x + h) 0 ≤
      uCandidate p x 0 + DxuCandidate p x 0 * h := by
  let C : ℝ := alpha p * (1 - pStar p / 2)
  let d : ℝ :=
    if 0 < x then p * x ^ (p - 1)
    else if x < 0 then -p * (-x) ^ (p - 1)
    else 0
  have hC : C ≤ 0 := by
    simpa [C] using axisCoeff_nonpos_leTwo p hp1 hp2
  have htangent :
      |x| ^ p + d * ((x + h) - x) ≤ |x + h| ^ p := by
    simpa [d] using abs_rpow_tangent_leTwo p hp1 x (x + h)
  have hmul :
      C * |x + h| ^ p ≤ C * (|x| ^ p + d * ((x + h) - x)) := by
    exact mul_le_mul_of_nonpos_left htangent hC
  calc
    uCandidate p (x + h) 0 = C * |x + h| ^ p := by
      simpa [C] using uCandidate_axis_eq_abs_rpow_leTwo p hp1 hp2 (x + h)
    _ ≤ C * (|x| ^ p + d * ((x + h) - x)) := hmul
    _ = C * |x| ^ p + (C * d) * h := by ring
    _ = uCandidate p x 0 + DxuCandidate p x 0 * h := by
      rw [uCandidate_axis_eq_abs_rpow_leTwo p hp1 hp2 x,
        DxuCandidate_axis_eq_abs_deriv_leTwo p hp1 hp2 x]

lemma uCandidate_axis_tangent_horizontal_leTwo
    (p : ℝ) (hp1 : 1 < p) (hp2 : p < 2) {x y h k : ℝ}
    (hk0 : k = 0) :
    uCandidate p (x + h) (y + k) ≤
      uCandidate p x y + DxuCandidate p x y * h + DyuCandidate p x y * k := by
  subst k
  rcases lt_trichotomy y 0 with hy_neg | hy0 | hy_pos
  · have hx := uCandidate_tangent_x_increment_of_y_neg_leTwo
      (p := p) (hp1 := hp1) (hp2 := hp2) (x := x) (y := y) (h := h) hy_neg
    simpa using hx
  · subst y
    have hx := uCandidate_tangent_x_increment_of_y_zero_leTwo
      (p := p) (hp1 := hp1) (hp2 := hp2) (x := x) (h := h)
    simpa using hx
  · have hx := uCandidate_tangent_x_increment_of_y_pos_leTwo
      (p := p) (hp1 := hp1) (hp2 := hp2) (x := x) (y := y) (h := h) hy_pos
    simpa using hx

lemma uCandidate_axis_tangent_vertical_leTwo
    (p : ℝ) (hp1 : 1 < p) (hp2 : p < 2) {x y h k : ℝ}
    (hh0 : h = 0) :
    uCandidate p (x + h) (y + k) ≤
      uCandidate p x y + DxuCandidate p x y * h + DyuCandidate p x y * k := by
  subst h
  have hhor := uCandidate_axis_tangent_horizontal_leTwo
    (p := p) (hp1 := hp1) (hp2 := hp2) (x := y) (y := x) (h := k) (k := 0) rfl
  have hswap_target :
      uCandidate p (x + 0) (y + k) =
        uCandidate p (y + k) (x + 0) := by
    exact uCandidate_swap_leTwo p (x + 0) (y + k)
  have hswap_base : uCandidate p y x = uCandidate p x y :=
    (uCandidate_swap_leTwo p x y).symm
  have hderiv : DxuCandidate p y x = DyuCandidate p x y :=
    (DyuCandidate_eq_DxuCandidate_swap_leTwo p hp1 hp2 x y).symm
  calc
    uCandidate p (x + 0) (y + k) =
        uCandidate p (y + k) (x + 0) := hswap_target
    _ ≤ uCandidate p y x + DxuCandidate p y x * k + DyuCandidate p y x * 0 := hhor
    _ = uCandidate p x y + DxuCandidate p x y * 0 + DyuCandidate p x y * k := by
      rw [hswap_base, hderiv]
      ring

lemma uCandidate_axis_tangent_leTwo
    (p : ℝ) (hp1 : 1 < p) (hp2 : p < 2) {x y h k : ℝ}
    (hk : h * k = 0) :
    uCandidate p (x + h) (y + k) ≤
      uCandidate p x y + DxuCandidate p x y * h + DyuCandidate p x y * k := by
  rcases mul_eq_zero.mp hk with hh0 | hk0
  · exact uCandidate_axis_tangent_vertical_leTwo p hp1 hp2 hh0
  · exact uCandidate_axis_tangent_horizontal_leTwo p hp1 hp2 hk0




end Majorant_p_l_2



theorem exists_majorant_leTwo (p : ℝ) (hp : 1 < p ∧ p < 2) :
    ∃ u : ℝ → ℝ → ℝ,
      (∀ x y, ∃ d_u_dx d_u_dy : ℝ,
        ∀ h k, h * k = 0 →
          u (x + h) (y + k) ≤ u x y + d_u_dx * h + d_u_dy * k) ∧
      (∀ x y, v p x y ≤ u x y) ∧
      (∀ x y, x * y ≤ 0 → u x y ≤ 0) ∧
      (∀ x y, x*y = 0 → u x y ≤ 0) := by
  use Majorant_p_l_2.uCandidate p
  constructor
  · intro x y
    refine ⟨Majorant_p_l_2.DxuCandidate p x y, Majorant_p_l_2.DyuCandidate p x y, ?_⟩
    intro h k hk
    exact Majorant_p_l_2.uCandidate_axis_tangent_leTwo p hp.1 hp.2 hk
  constructor
  · intro x y
    rw [Majorant_p_l_2.v_eq_vLeTwo_of_one_lt_of_lt_two p x y hp.1 hp.2]
    exact Majorant_p_l_2.vLeTwo_le_uCandidate_leTwo p hp.1 hp.2 x y
  constructor
  · intro x y hxy
    exact Majorant_p_l_2.uCandidate_le_zero_of_mul_nonpos_leTwo p x y hp.1 hp.2 hxy
  · intro x y hxy
    exact Majorant_p_l_2.uCandidate_le_zero_of_xy_zero_leTwo p x y hp.1 hp.2 hxy

end Majorants
