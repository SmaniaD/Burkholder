import Mathlib.Analysis.Convex.Function
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.InnerProductSpace.NormPow
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

noncomputable section

namespace Burkholder

def q (p : ℝ) : ℝ := if p = 1 then 0 else p / (p - 1)

def pStar (p : ℝ) : ℝ := max p (q p)

theorem pStar_eq_self_of_two_le (p : ℝ) (hp : 2 ≤ p) : pStar p = p := by
  unfold pStar
  apply max_eq_left
  unfold q
  have hp_ne_one : p ≠ 1 := by linarith
  simp [hp_ne_one]
  have hden : 0 < p - 1 := by linarith
  have hnonneg : 0 ≤ p := by linarith
  have h1 : 1 ≤ p - 1 := by linarith
  have hmul : p * 1 ≤ p * (p - 1) := mul_le_mul_of_nonneg_left h1 hnonneg
  have hp_le : p ≤ p * (p - 1) := by simpa using hmul
  have hden_ne : p - 1 ≠ 0 := by linarith
  have h_inv_nonneg : 0 ≤ (p - 1)⁻¹ := by positivity
  have hmul' : p * (p - 1)⁻¹ ≤ (p * (p - 1)) * (p - 1)⁻¹ :=
    mul_le_mul_of_nonneg_right hp_le h_inv_nonneg
  simpa [div_eq_mul_inv, hden_ne, mul_assoc, mul_comm, mul_left_comm] using hmul'




def v (p x y : ℝ) : ℝ :=
  Real.rpow (|((x + y) / 2)|) p
    - Real.rpow (|pStar p - 1|) p * Real.rpow (|((x - y) / 2)|) p

def vGeTwo (p x y : ℝ) : ℝ :=
  Real.rpow (|((x + y) / 2)|) p
    - Real.rpow (p - 1) p * Real.rpow (|((x - y) / 2)|) p

def a (p : ℝ) : ℝ := 1 - 2 / (pStar p)

def alpha (p : ℝ) : ℝ :=  p* Real.rpow (pStar p/(pStar p - 1)) (1-p)


def A1 (p x y : ℝ) : Prop := 0 < x ∧ (a p) * x < y ∧ y < x

def closureA1 (p x y : ℝ) : Prop := 0 ≤ x ∧ (a p) * x ≤ y ∧ y ≤ x

def A2 (p x y : ℝ) : Prop := 0 < x ∧ -x < y ∧ y < (a p) * x

def closureA2 (p x y : ℝ) : Prop := 0 ≤ x ∧ -x ≤ y ∧ y ≤ (a p) * x

def uA1 (p x y : ℝ) : ℝ :=
  if x > 0 then
     alpha p * Real.rpow x (p-1) * (x - (pStar p) * (x - y) /2)
     else 0

def DxuA1 (p x y : ℝ) : ℝ :=
  if x > 0 then
     alpha p * (p / 2) * Real.rpow x (p - 2) * ((2 - p) * x + (p - 1) * y)
     else 0

def DyuA1 (p x _y : ℝ) : ℝ :=
  if x > 0 then
     alpha p * Real.rpow x (p - 1) * (pStar p / 2)
     else 0

def DxvGeTwo (p x y : ℝ) : ℝ :=
  if x > 0 then
     Real.rpow (|((x + y) / 2)|) (p - 1) * (p / 2)
     - Real.rpow (p - 1) p * Real.rpow (|((x - y) / 2)|) (p - 1) * (p / 2)
     else 0

def DyvGeTwo (p x y : ℝ) : ℝ :=
  if x > 0 then
     Real.rpow (|((x + y) / 2)|) (p - 1) * (p / 2)
     + Real.rpow (p - 1) p * Real.rpow (|((x - y) / 2)|) (p - 1) * (p / 2)
     else 0

def closureA1Set (p : ℝ) : Set (ℝ × ℝ) :=
  {z | closureA1 p z.1 z.2}

def closureA2Set (p : ℝ) : Set (ℝ × ℝ) :=
  {z | closureA2 p z.1 z.2}

def DxuA1Fun (p : ℝ) : ℝ × ℝ → ℝ :=
  fun z => DxuA1 p z.1 z.2

def DyuA1Fun (p : ℝ) : ℝ × ℝ → ℝ :=
  fun z => DyuA1 p z.1 z.2

def DxuA1Formula (p : ℝ) : ℝ × ℝ → ℝ :=
  fun z => alpha p * (p / 2) * Real.rpow z.1 (p - 2) * ((2 - p) * z.1 + (p - 1) * z.2)

def DyuA1Formula (p : ℝ) : ℝ × ℝ → ℝ :=
  fun z => alpha p * Real.rpow z.1 (p - 1) * (pStar p / 2)

def DxvGeTwoFun (p : ℝ) : ℝ × ℝ → ℝ :=
  fun z => DxvGeTwo p z.1 z.2

def DyvGeTwoFun (p : ℝ) : ℝ × ℝ → ℝ :=
  fun z => DyvGeTwo p z.1 z.2

def DxvGeTwoFormula (p : ℝ) : ℝ × ℝ → ℝ :=
  fun z =>
    Real.rpow (|((z.1 + z.2) / 2)|) (p - 1) * (p / 2) -
      Real.rpow (p - 1) p * Real.rpow (|((z.1 - z.2) / 2)|) (p - 1) * (p / 2)

def DyvGeTwoFormula (p : ℝ) : ℝ × ℝ → ℝ :=
  fun z =>
    Real.rpow (|((z.1 + z.2) / 2)|) (p - 1) * (p / 2) +
      Real.rpow (p - 1) p * Real.rpow (|((z.1 - z.2) / 2)|) (p - 1) * (p / 2)


open Topology




lemma continuousAt_DxuA1_interior
    (p x y : ℝ) (hx : 0 < x) :
    ContinuousAt (DxuA1Fun p) (x, y) := by
  have hpos : {z : ℝ × ℝ | 0 < z.1} ∈ nhds (x, y) := by
    exact continuous_fst.continuousAt.preimage_mem_nhds (Ioi_mem_nhds hx)

  have hEvent :
      DxuA1Fun p =ᶠ[nhds (x, y)] DxuA1Formula p := by
    filter_upwards [hpos] with z hz
    simp [DxuA1Fun, DxuA1Formula, DxuA1, hz]

  have hcont_rpow :
      ContinuousAt (fun z : ℝ × ℝ => z.1 ^ (p - 2)) (x, y) := by
    exact continuous_fst.continuousAt.rpow_const (Or.inl (ne_of_gt hx))

  have hcont_sub : ContinuousAt (fun z : ℝ × ℝ => z.1 - z.2) (x, y) := by
    exact continuous_fst.continuousAt.sub continuous_snd.continuousAt

  have hcont_lin :
      ContinuousAt
        (fun z : ℝ × ℝ => (2 - p) * z.1 + (p - 1) * z.2)
        (x, y) := by
    exact
      (continuous_const.continuousAt.mul continuous_fst.continuousAt).add
        (continuous_const.continuousAt.mul continuous_snd.continuousAt)

  have hcont : ContinuousAt (DxuA1Formula p) (x, y) := by
    change ContinuousAt
      (fun z : ℝ × ℝ =>
        alpha p * (p / 2) * z.1 ^ (p - 2) * ((2 - p) * z.1 + (p - 1) * z.2))
      (x, y)
    simpa [mul_assoc, mul_left_comm, mul_comm] using
      (continuous_const.continuousAt.mul continuous_const.continuousAt).mul
        (hcont_rpow.mul hcont_lin)

  exact hcont.congr_of_eventuallyEq hEvent



lemma continuousAt_DyuA1_interior
    (p x y : ℝ) (hx : 0 < x) :
    ContinuousAt (DyuA1Fun p) (x, y):=
by
  have hpos : {z : ℝ × ℝ | 0 < z.1} ∈ nhds (x, y) := by
    exact continuous_fst.continuousAt.preimage_mem_nhds (Ioi_mem_nhds hx)

  have hEvent :
      DyuA1Fun p =ᶠ[nhds (x, y)]
        (fun z : ℝ × ℝ => alpha p * Real.rpow z.1 (p - 1) * (pStar p / 2)) := by
    filter_upwards [hpos] with z hz
    simp [DyuA1Fun, DyuA1, hz]

  have hcont_rpow :
      ContinuousAt (fun z : ℝ × ℝ => z.1 ^ (p - 1)) (x, y) := by
    exact continuous_fst.continuousAt.rpow_const (Or.inl (ne_of_gt hx))

  have hcont :
      ContinuousAt
        (fun z : ℝ × ℝ => alpha p * Real.rpow z.1 (p - 1) * (pStar p / 2))
        (x, y) := by
    simpa [mul_assoc] using
      (continuous_const.continuousAt.mul hcont_rpow).mul continuous_const.continuousAt

  exact hcont.congr_of_eventuallyEq hEvent







lemma closureA1_x0_y0
    (p x y : ℝ) (h : closureA1 p x y) (hx : ¬ 0 < x) :
    x = 0 ∧ y = 0 := by
  rcases h with ⟨hxnonneg, hylow, hyup⟩
  have hx0 : x = 0 := by linarith
  have hy0 : y = 0 := by
    subst hx0
    linarith
  exact ⟨hx0, hy0⟩

lemma closureA2_x0_y0
    (p x y : ℝ) (h : closureA2 p x y) (hx : ¬ 0 < x) :
    x = 0 ∧ y = 0 := by
  rcases h with ⟨hxnonneg, hylow, hyup⟩
  have hx0 : x = 0 := by linarith
  have hy0 : y = 0 := by
    subst hx0
    linarith
  exact ⟨hx0, hy0⟩

/-- Em `closureA1`, temos `|y| ≤ max 1 |a p| * x`. -/
lemma abs_y_le_const_mul_x
    (p x y : ℝ) (h : closureA1 p x y) :
    |y| ≤ (max 1 |a p|) * x := by
  rcases h with ⟨hx, hlow, hup⟩
  have hx' : 0 ≤ x := hx
  have h1 : y ≤ x := hup
  have h2 : -(max 1 |a p| * x) ≤ y := by
    have ha : -(max 1 |a p|) ≤ a p := by
      have hmax : |a p| ≤ max 1 |a p| := le_max_right _ _
      have hneg : -(max 1 |a p|) ≤ -|a p| := by linarith
      have habs : -|a p| ≤ a p := by
        exact neg_abs_le (a p)
      linarith
    have := mul_le_mul_of_nonneg_right ha hx'
    linarith
  have h3 : y ≤ max 1 |a p| * x := by
    have hmax1 : 1 ≤ max 1 |a p| := le_max_left _ _
    have := mul_le_mul_of_nonneg_right hmax1 hx'
    linarith
  exact abs_le.mpr ⟨h2, h3⟩

/-- Estimativa grosseira suficiente para o bordo:
`|DxuA1| ≤ C * x^(p-1)` em `closureA1`. -/
lemma abs_DxuA1_le
    (p x y : ℝ) (h : closureA1 p x y) :
    |DxuA1 p x y|
      ≤ |alpha p| * (|p| / 2) * (|2 - p| + |p - 1| * max 1 |a p|) * Real.rpow x (p - 1) := by
  rcases h with ⟨hx, hlow, hup⟩
  by_cases hx0 : 0 < x
  · have hxnonneg : 0 ≤ x := le_of_lt hx0
    have hyabs : |y| ≤ (max 1 |a p|) * x := by
      exact abs_y_le_const_mul_x p x y ⟨hx, hlow, hup⟩
    have hx_abs : |x| = x := abs_of_nonneg hxnonneg
    have hlin :
        |(2 - p) * x + (p - 1) * y|
          ≤ (|2 - p| + |p - 1| * max 1 |a p|) * x := by
      have htmp :
          |(2 - p) * x + (p - 1) * y|
            ≤ |(2 - p) * x| + |(p - 1) * y| := by
        simpa using abs_add_le ((2 - p) * x) ((p - 1) * y)
      have hmulx : |(2 - p) * x| = |2 - p| * x := by
        rw [abs_mul, hx_abs]
      have hmuly : |(p - 1) * y| = |p - 1| * |y| := by
        rw [abs_mul]
      rw [hmulx, hmuly] at htmp
      calc
        |(2 - p) * x + (p - 1) * y|
            ≤ |2 - p| * x + |p - 1| * |y| := htmp
        _ ≤ |2 - p| * x + |p - 1| * (max 1 |a p| * x) := by
            gcongr
        _ = (|2 - p| + |p - 1| * max 1 |a p|) * x := by
            ring
    have hrpow_nonneg : 0 ≤ Real.rpow x (p - 2) := Real.rpow_nonneg hxnonneg _
    have hpow :
        Real.rpow x (p - 2) * x = Real.rpow x (p - 1) := by
      have hexp : (p - 2) + 1 = p - 1 := by ring
      nth_rewrite 2 [show x = Real.rpow x (1 : ℝ) by simpa using (Real.rpow_one x).symm]
      calc
        Real.rpow x (p - 2) * Real.rpow x (1 : ℝ)
            = Real.rpow x ((p - 2) + 1) := by
                simpa using (Real.rpow_add hx0 (p - 2) 1).symm
        _ = Real.rpow x (p - 1) := by simpa [hexp]
    have habs :
        |alpha p * (p / 2) * Real.rpow x (p - 2) * ((2 - p) * x + (p - 1) * y)|
          = |alpha p| * (|p| / 2) * Real.rpow x (p - 2) * |(2 - p) * x + (p - 1) * y| := by
      have hmul :
          |alpha p * (p / 2) * Real.rpow x (p - 2)|
            = |alpha p| * (|p| / 2) * Real.rpow x (p - 2) := by
        rw [abs_mul, abs_mul, abs_of_nonneg hrpow_nonneg, abs_div, abs_of_pos (show (0 : ℝ) < 2 by norm_num)]
      calc
        |alpha p * (p / 2) * Real.rpow x (p - 2) * ((2 - p) * x + (p - 1) * y)|
            = |(alpha p * (p / 2) * Real.rpow x (p - 2)) * ((2 - p) * x + (p - 1) * y)| := by
                ring_nf
        _ = |alpha p * (p / 2) * Real.rpow x (p - 2)| * |(2 - p) * x + (p - 1) * y| := by
            rw [abs_mul]
        _ = (|alpha p| * (|p| / 2) * Real.rpow x (p - 2)) * |(2 - p) * x + (p - 1) * y| := by
            rw [hmul]
        _ = |alpha p| * (|p| / 2) * Real.rpow x (p - 2) * |(2 - p) * x + (p - 1) * y| := by ring
    calc
      |DxuA1 p x y|
          = |alpha p * (p / 2) * Real.rpow x (p - 2) * ((2 - p) * x + (p - 1) * y)| := by
              simp [DxuA1, hx0]
      _ = |alpha p| * (|p| / 2) * Real.rpow x (p - 2) * |(2 - p) * x + (p - 1) * y| := habs
      _ ≤ |alpha p| * (|p| / 2) * Real.rpow x (p - 2) *
            ((|2 - p| + |p - 1| * max 1 |a p|) * x) := by
              gcongr
      _ = |alpha p| * (|p| / 2) * (|2 - p| + |p - 1| * max 1 |a p|) *
            (Real.rpow x (p - 2) * x) := by
              ring
      _ = |alpha p| * (|p| / 2) * (|2 - p| + |p - 1| * max 1 |a p|) *
            Real.rpow x (p - 1) := by
              rw [hpow]
  · have h00 : x = 0 ∧ y = 0 := closureA1_x0_y0 p x y ⟨hx, hlow, hup⟩ hx0
    rcases h00 with ⟨rfl, rfl⟩
    have hnonneg :
        0 ≤ |alpha p| * (|p| / 2) * (|2 - p| + |p - 1| * max 1 |a p|) * Real.rpow 0 (p - 1) := by
      have hrpow_nonneg : 0 ≤ Real.rpow (0 : ℝ) (p - 1) := Real.zero_rpow_nonneg (p - 1)
      positivity
    simpa [DxuA1] using hnonneg


lemma continuousOn_DxuA1_closureA1
    (p : ℝ) (hp : 1 < p) :
    ContinuousOn (DxuA1Fun p) (closureA1Set p) := by
  intro z hz
  rcases z with ⟨x, y⟩
  rcases hz with ⟨hx, hlow, hup⟩
  by_cases hx0 : 0 < x
  · exact (continuousAt_DxuA1_interior p x y hx0).continuousWithinAt
  · have h00 := closureA1_x0_y0 p x y ⟨hx, hlow, hup⟩ hx0
    rcases h00 with ⟨rfl, rfl⟩
    rw [ContinuousWithinAt, DxuA1Fun]
    simp only [DxuA1, lt_irrefl, ite_false]
    rw [tendsto_zero_iff_abs_tendsto_zero]
    let C : ℝ := |alpha p| * (|p| / 2) * (|2 - p| + |p - 1| * max 1 |a p|)
    have hC_nonneg : 0 ≤ C := by
      dsimp [C]
      positivity
    have hbound :
        ∀ᶠ z : ℝ × ℝ in nhdsWithin (0, 0) (closureA1Set p),
          |DxuA1Fun p z| ≤ C * Real.rpow z.1 (p - 1) := by
      refine Filter.mem_of_superset self_mem_nhdsWithin ?_
      intro z hz'
      simpa [closureA1Set, DxuA1Fun, C] using abs_DxuA1_le p z.1 z.2 hz'
    have hrpow :
        Filter.Tendsto (fun z : ℝ × ℝ => Real.rpow z.1 (p - 1))
          (nhdsWithin (0, 0) (closureA1Set p)) (nhds 0) := by
      have hcont :
          ContinuousAt (fun z : ℝ × ℝ => Real.rpow z.1 (p - 1)) (0, 0) := by
        exact continuous_fst.continuousAt.rpow_const (Or.inr (by linarith : 0 ≤ p - 1))
      have hzero : Real.rpow (0 : ℝ) (p - 1) = 0 := by
        exact Real.zero_rpow (by linarith)
      have ht : Filter.Tendsto (fun z : ℝ × ℝ => Real.rpow z.1 (p - 1)) (nhds (0, 0)) (nhds 0) := by
        convert hcont.tendsto using 1
        simpa using hzero.symm
      exact ht.mono_left nhdsWithin_le_nhds
    have hmajor :
        Filter.Tendsto (fun z : ℝ × ℝ => C * Real.rpow z.1 (p - 1))
          (nhdsWithin (0, 0) (closureA1Set p)) (nhds 0) := by
      simpa using tendsto_const_nhds.mul hrpow
    exact squeeze_zero' (Filter.Eventually.of_forall fun _ => abs_nonneg _) hbound hmajor



lemma continuousOn_DyuA1_closureA1
    (p : ℝ) (hp : 2 < p) :
    ContinuousOn (DyuA1Fun p) (closureA1Set p) := by
  intro z hz
  rcases z with ⟨x, y⟩
  rcases hz with ⟨hx, hlow, hup⟩
  by_cases hx0 : 0 < x
  · have hpos : {w : ℝ × ℝ | 0 < w.1} ∈ nhds (x, y) := by
      exact continuous_fst.continuousAt.preimage_mem_nhds (Ioi_mem_nhds hx0)
    have hEvent :
        DyuA1Fun p =ᶠ[nhds (x, y)]
          (fun w : ℝ × ℝ => alpha p * Real.rpow w.1 (p - 1) * (pStar p / 2)) := by
      filter_upwards [hpos] with w hw
      simp [DyuA1Fun, DyuA1, hw]
    have hcont_rpow :
        ContinuousAt (fun w : ℝ × ℝ => Real.rpow w.1 (p - 1)) (x, y) := by
      exact continuous_fst.continuousAt.rpow_const (Or.inl (ne_of_gt hx0))
    have hcont :
        ContinuousAt
          (fun w : ℝ × ℝ => alpha p * Real.rpow w.1 (p - 1) * (pStar p / 2))
          (x, y) := by
      simpa [mul_assoc] using
        (continuous_const.continuousAt.mul hcont_rpow).mul continuous_const.continuousAt
    exact (hcont.congr_of_eventuallyEq hEvent).continuousWithinAt
  · have h00 := closureA1_x0_y0 p x y ⟨hx, hlow, hup⟩ hx0
    rcases h00 with ⟨rfl, rfl⟩
    rw [ContinuousWithinAt, DyuA1Fun]
    simp only [DyuA1, lt_irrefl, ite_false]
    rw [tendsto_zero_iff_abs_tendsto_zero]
    let C : ℝ := |alpha p * (pStar p / 2)|
    have hbound :
        ∀ᶠ w : ℝ × ℝ in nhdsWithin (0, 0) (closureA1Set p),
          |DyuA1Fun p w| ≤ C * Real.rpow w.1 (p - 1) := by
      refine Filter.mem_of_superset self_mem_nhdsWithin ?_
      intro w hw
      rcases hw with ⟨hwx, hwlow, hwup⟩
      by_cases hw0 : 0 < w.1
      · have habs :
            |DyuA1Fun p w| =
              C * Real.rpow w.1 (p - 1) := by
          calc
            |DyuA1Fun p w|
                = |alpha p| * Real.rpow w.1 (p - 1) * |pStar p / 2| := by
                    simp [DyuA1Fun, DyuA1, hw0, abs_mul, Real.rpow_nonneg hwx, mul_assoc]
            _ = (|alpha p| * |pStar p / 2|) * Real.rpow w.1 (p - 1) := by ring
            _ = C * Real.rpow w.1 (p - 1) := by
                    simp [C, abs_mul, mul_assoc]
        exact le_of_eq habs
      · have h00 := closureA1_x0_y0 p w.1 w.2 ⟨hwx, hwlow, hwup⟩ hw0
        rcases h00 with ⟨hw1, hw2⟩
        simp [hw1, hw2, DyuA1Fun, DyuA1, C]
        positivity
    have hrpow :
        Filter.Tendsto (fun w : ℝ × ℝ => Real.rpow w.1 (p - 1))
          (nhdsWithin (0, 0) (closureA1Set p)) (nhds 0) := by
      have hcont :
          ContinuousAt (fun w : ℝ × ℝ => Real.rpow w.1 (p - 1)) (0, 0) := by
        exact continuous_fst.continuousAt.rpow_const (Or.inr (by linarith : 0 ≤ p - 1))
      have hzero : Real.rpow (0 : ℝ) (p - 1) = 0 := by
        exact Real.zero_rpow (by linarith)
      have ht :
          Filter.Tendsto (fun w : ℝ × ℝ => Real.rpow w.1 (p - 1)) (nhds (0, 0)) (nhds 0) := by
        convert hcont.tendsto using 1
        simpa using hzero.symm
      exact ht.mono_left nhdsWithin_le_nhds
    have hmajor :
        Filter.Tendsto (fun w : ℝ × ℝ => C * Real.rpow w.1 (p - 1))
          (nhdsWithin (0, 0) (closureA1Set p)) (nhds 0) := by
      simpa using tendsto_const_nhds.mul hrpow
    exact squeeze_zero' (Filter.Eventually.of_forall fun _ => abs_nonneg _) hbound hmajor

lemma DxvGeTwo_eq_formula_on_closureA2
    (p : ℝ) (hp : 2 ≤ p) (z : ℝ × ℝ) (hz : z ∈ closureA2Set p) :
    DxvGeTwoFun p z = DxvGeTwoFormula p z := by
  rcases z with ⟨x, y⟩
  rcases hz with ⟨hx, hlow, hup⟩
  by_cases hx0 : 0 < x
  · simp [DxvGeTwoFun, DxvGeTwoFormula, DxvGeTwo, hx0]
  · have h00 := closureA2_x0_y0 p x y ⟨hx, hlow, hup⟩ hx0
    rcases h00 with ⟨rfl, rfl⟩
    have hp1 : p - 1 ≠ 0 := by linarith
    have hzero : Real.rpow (0 : ℝ) (p - 1) = 0 := Real.zero_rpow hp1
    simp [DxvGeTwoFun, DxvGeTwoFormula, DxvGeTwo, hx0]
    rw [show (0 : ℝ) ^ (p - 1) = 0 by simpa using hzero]
    ring

lemma DyvGeTwo_eq_formula_on_closureA2
    (p : ℝ) (hp : 2 ≤ p) (z : ℝ × ℝ) (hz : z ∈ closureA2Set p) :
    DyvGeTwoFun p z = DyvGeTwoFormula p z := by
  rcases z with ⟨x, y⟩
  rcases hz with ⟨hx, hlow, hup⟩
  by_cases hx0 : 0 < x
  · simp [DyvGeTwoFun, DyvGeTwoFormula, DyvGeTwo, hx0]
  · have h00 := closureA2_x0_y0 p x y ⟨hx, hlow, hup⟩ hx0
    rcases h00 with ⟨rfl, rfl⟩
    have hp1 : p - 1 ≠ 0 := by linarith
    have hzero : Real.rpow (0 : ℝ) (p - 1) = 0 := Real.zero_rpow hp1
    simp [DyvGeTwoFun, DyvGeTwoFormula, DyvGeTwo, hx0]
    rw [show (0 : ℝ) ^ (p - 1) = 0 by simpa using hzero]
    ring

lemma continuousOn_DxvGeTwo_closureA2
    (p : ℝ) (hp : 2 ≤ p) :
    ContinuousOn (DxvGeTwoFun p) (closureA2Set p) := by
  have hp1 : 0 ≤ p - 1 := by linarith
  have hcont : Continuous (DxvGeTwoFormula p) := by
    have hsum :
        Continuous (fun z : ℝ × ℝ => Real.rpow (|((z.1 + z.2) / 2)|) (p - 1)) := by
      exact Continuous.rpow_const (((continuous_fst.add continuous_snd).div_const 2).abs)
        (fun _ => Or.inr hp1)
    have hdiff :
        Continuous (fun z : ℝ × ℝ => Real.rpow (|((z.1 - z.2) / 2)|) (p - 1)) := by
      exact Continuous.rpow_const (((continuous_fst.sub continuous_snd).div_const 2).abs)
        (fun _ => Or.inr hp1)
    apply Continuous.sub
    · simpa [DxvGeTwoFormula] using hsum.mul continuous_const
    · simpa [DxvGeTwoFormula, mul_assoc, mul_left_comm, mul_comm] using
        continuous_const.mul (hdiff.mul continuous_const)
  apply ContinuousOn.congr hcont.continuousOn
  intro z hz
  exact DxvGeTwo_eq_formula_on_closureA2 p hp z hz

lemma continuousOn_DyvGeTwo_closureA2
    (p : ℝ) (hp : 2 ≤ p) :
    ContinuousOn (DyvGeTwoFun p) (closureA2Set p) := by
  have hp1 : 0 ≤ p - 1 := by linarith
  have hcont : Continuous (DyvGeTwoFormula p) := by
    have hsum :
        Continuous (fun z : ℝ × ℝ => Real.rpow (|((z.1 + z.2) / 2)|) (p - 1)) := by
      exact Continuous.rpow_const (((continuous_fst.add continuous_snd).div_const 2).abs)
        (fun _ => Or.inr hp1)
    have hdiff :
        Continuous (fun z : ℝ × ℝ => Real.rpow (|((z.1 - z.2) / 2)|) (p - 1)) := by
      exact Continuous.rpow_const (((continuous_fst.sub continuous_snd).div_const 2).abs)
        (fun _ => Or.inr hp1)
    apply Continuous.add
    · simpa [DyvGeTwoFormula] using hsum.mul continuous_const
    · simpa [DyvGeTwoFormula, mul_assoc, mul_left_comm, mul_comm] using
        continuous_const.mul (hdiff.mul continuous_const)
  apply ContinuousOn.congr hcont.continuousOn
  intro z hz
  exact DyvGeTwo_eq_formula_on_closureA2 p hp z hz




def auxFunction1 (p x y : ℝ) : ℝ :=
    by
    classical
    exact
      if  closureA1 p x y then
         uA1 p x y
      else if closureA2 p x y then
          vGeTwo p x y
        else 0

def DxauxFunction1 (p x y : ℝ) : ℝ :=
    by
    classical
    exact
      if closureA1 p x y then
        DxuA1 p x y
      else if closureA2 p x y then
        DxvGeTwo p x y
      else 0

def DyauxFunction1 (p x y : ℝ) : ℝ :=
    by
    classical
    exact
      if closureA1 p x y then
        DyuA1 p x y
      else if closureA2 p x y then
        DyvGeTwo p x y
      else 0


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


/-- For x ≥ 0, uA1 equals the smooth expression (using 0^(p-1)=0 when x=0). -/
lemma uA1_eq_smooth_of_nonneg (p : ℝ) (hp : 2 ≤ p) (x y : ℝ) (hx : 0 ≤ x) :
    uA1 p x y = alpha p * x ^ (p - 1) * (x - pStar p * (x - y) / 2) := by
  have hexp_ne : p - 1 ≠ 0 := by linarith
  unfold uA1
  rcases hx.lt_or_eq with hxpos | hxeq
  · exact if_pos hxpos
  · have hx0 : x = 0 := hxeq.symm
    subst hx0
    simp [Real.zero_rpow hexp_ne]

/-- uA1 is continuous on {(x, y) | 0 ≤ x} when p ≥ 2. -/
lemma continuousOn_uA1 (p : ℝ) (hp : 2 ≤ p) :
    ContinuousOn (fun z : ℝ × ℝ => uA1 p z.1 z.2) {z | 0 ≤ z.1} := by
  have hexp_pos : 0 < p - 1 := by linarith
  have heq : ∀ z : ℝ × ℝ, z ∈ {z : ℝ × ℝ | 0 ≤ z.1} →
      uA1 p z.1 z.2 = alpha p * z.1 ^ (p - 1) * (z.1 - pStar p * (z.1 - z.2) / 2) :=
    fun ⟨x, y⟩ hx => uA1_eq_smooth_of_nonneg p hp x y hx
  apply ContinuousOn.congr _ heq
  apply ContinuousOn.mul
  · exact continuousOn_const.mul
      (continuousOn_fst.rpow_const fun _ _ => Or.inr hexp_pos.le)
  · exact continuousOn_fst.sub
      ((continuousOn_const.mul (continuousOn_fst.sub continuousOn_snd)).div_const 2)




/-- On the A1/A2 boundary (y = a(p)·x, x > 0), uA1 vanishes. -/
lemma uA1_eq_zero_on_boundary (p x : ℝ) (hp : 2 ≤ p) (hx : 0 < x) :
    uA1 p x ((a p) * x) = 0 := by
  have hpStar : pStar p = p := pStar_eq_self_of_two_le p hp
  have hp_pos : 0 < p := by linarith
  unfold uA1
  rw [if_pos hx]
  have hfactor : x - pStar p * (x - a p * x) / 2 = 0 := by
    simp only [a, hpStar]
    field_simp [hp_pos.ne']
    ring
  rw [hfactor, mul_zero]

/-- On the A1/A2 boundary (y = a(p)·x, x > 0), vGeTwo vanishes. -/
lemma vGeTwo_eq_zero_on_boundary (p x : ℝ) (hp : 2 ≤ p) (hx : 0 < x) :
    vGeTwo p x ((a p) * x) = 0 := by
  have hpStar : pStar p = p := pStar_eq_self_of_two_le p hp
  have hp_pos : 0 < p := by linarith
  simp only [vGeTwo, a, hpStar]
  have h_sum : (x + (1 - 2 / p) * x) / 2 = (p - 1) / p * x := by
    field_simp [hp_pos.ne']; ring
  have h_diff : (x - (1 - 2 / p) * x) / 2 = x / p := by
    field_simp [hp_pos.ne']; ring
  rw [h_sum, h_diff,
      abs_of_pos (mul_pos (div_pos (by linarith) hp_pos) hx),
      abs_of_pos (div_pos hx hp_pos)]
  have key : ((p - 1) / p * x) ^ p = (p - 1) ^ p * (x / p) ^ p := by
    rw [Real.mul_rpow (div_nonneg (by linarith) hp_pos.le) hx.le,
        Real.div_rpow (by linarith : 0 ≤ p - 1) hp_pos.le,
        Real.div_rpow hx.le hp_pos.le]
    ring
  exact sub_eq_zero.mpr key

/-- Both formulas agree on the shared A1/A2 boundary. -/
lemma uA1_eq_vGeTwo_on_A1A2_boundary (p x : ℝ) (hp : 2 ≤ p) (hx : 0 < x) :
    uA1 p x ((a p) * x) = vGeTwo p x ((a p) * x) :=
  (uA1_eq_zero_on_boundary p x hp hx).trans (vGeTwo_eq_zero_on_boundary p x hp hx).symm

/- Continuity auxiliary functions -/

/-- As x → 0⁺, x ^ (p - 1) → 0 when p > 1. -/
lemma tendsto_rpow_nhdsWithin_Ioi_zero (p : ℝ) (hp : 1 < p) :
    Filter.Tendsto (fun x : ℝ => x ^ (p - 1)) (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
  have hexp : 0 < p - 1 := by linarith
  have h0 : (0 : ℝ) ^ (p - 1) = 0 := Real.zero_rpow hexp.ne'
  have hcont : ContinuousAt (fun x : ℝ => x ^ (p - 1)) 0 :=
    continuousAt_id.rpow_const (Or.inr hexp.le)
  have key : Filter.Tendsto (fun x : ℝ => x ^ (p - 1))
      (nhdsWithin 0 (Set.Ioi 0)) (nhds ((0 : ℝ) ^ (p - 1))) :=
    hcont.continuousWithinAt
  rwa [h0] at key


/-- vGeTwo is continuous on ℝ² when p > 1. -/
lemma continuous_vGeTwo (p : ℝ) (hp : 1 < p) :
    Continuous (fun z : ℝ × ℝ => vGeTwo p z.1 z.2) := by
  have hp_pos : (0 : ℝ) ≤ p := by linarith
  simp only [vGeTwo]
  apply Continuous.sub
  · apply Continuous.rpow_const _ (fun _ => Or.inr hp_pos)
    exact ((continuous_fst.add continuous_snd).div_const 2).abs
  · apply Continuous.mul continuous_const
    apply Continuous.rpow_const _ (fun _ => Or.inr hp_pos)
    exact ((continuous_fst.sub continuous_snd).div_const 2).abs








/-- closureA1 and closureA2 are closed subsets of ℝ². -/
lemma isClosed_closureA1_set (p : ℝ) :
    IsClosed {z : ℝ × ℝ | closureA1 p z.1 z.2} := by
  simp only [closureA1]
  apply IsClosed.inter
  · exact isClosed_le continuous_const continuous_fst
  apply IsClosed.inter
  · exact isClosed_le (continuous_const.mul continuous_fst) continuous_snd
  · exact isClosed_le continuous_snd continuous_fst

lemma isClosed_closureA2_set (p : ℝ) :
    IsClosed {z : ℝ × ℝ | closureA2 p z.1 z.2} := by
  simp only [closureA2]
  apply IsClosed.inter
  · exact isClosed_le continuous_const continuous_fst
  apply IsClosed.inter
  · exact isClosed_le continuous_fst.neg continuous_snd
  · exact isClosed_le continuous_snd (continuous_const.mul continuous_fst)

/-- On the boundary closureA1 ∩ closureA2, uA1 = vGeTwo (both equal 0). -/
lemma uA1_eq_vGeTwo_on_inter (p : ℝ) (hp : 2 ≤ p) (x y : ℝ)
    (h1 : closureA1 p x y) (h2 : closureA2 p x y) :
    uA1 p x y = vGeTwo p x y := by
  obtain ⟨hx, hay, hyx⟩ := h1
  obtain ⟨_, hmy, hyay⟩ := h2
  have heq : y = a p * x := le_antisymm hyay hay
  rcases hx.lt_or_eq with hxpos | hxeq
  · rw [heq]; exact uA1_eq_vGeTwo_on_A1A2_boundary p x hp hxpos
  · -- x = 0, so both sides are 0
    have hx0 : x = 0 := hxeq.symm
    subst hx0
    simp only [uA1, lt_irrefl, ite_false, vGeTwo]
    have hy0 : y = 0 := le_antisymm (by linarith) (by linarith)
    subst hy0
    simp [Real.zero_rpow (by linarith : p ≠ 0)]

/-- auxFunction1 = uA1 on closureA1. -/
lemma auxFunction1_eq_uA1 (p x y : ℝ) (h : closureA1 p x y) :
    auxFunction1 p x y = uA1 p x y := by
  simp only [auxFunction1, h, ite_true]

/-- auxFunction1 = vGeTwo on closureA2, given p ≥ 2. -/
lemma auxFunction1_eq_vGeTwo (p : ℝ) (hp : 2 ≤ p) (x y : ℝ) (h2 : closureA2 p x y) :
    auxFunction1 p x y = vGeTwo p x y := by
  simp only [auxFunction1]
  by_cases h1 : closureA1 p x y
  · simp only [h1, ite_true]
    exact uA1_eq_vGeTwo_on_inter p hp x y h1 h2
  · simp only [h1, ite_false, h2, ite_true]

/-- On the A1/A2 boundary, the x-partial formulas agree. -/
lemma alpha_eq_boundary_coeff (p : ℝ) (hp : 2 ≤ p) :
    alpha p = p * Real.rpow ((p - 1) / p) (p - 1) := by
  have hpStar : pStar p = p := pStar_eq_self_of_two_le p hp
  have hp_pos : 0 < p := by linarith
  have hp1_nonneg : 0 ≤ p - 1 := by linarith
  rw [alpha, hpStar]
  simp_rw [Real.rpow_eq_pow]
  calc
    p * (p / (p - 1)) ^ (1 - p)
        = p * (p / (p - 1)) ^ (-(p - 1)) := by
            congr 2
            ring
    _ = p * ((p / (p - 1)) ^ (p - 1))⁻¹ := by
          rw [Real.rpow_neg (div_nonneg hp_pos.le hp1_nonneg)]
    _ = p * (p ^ (p - 1) / (p - 1) ^ (p - 1))⁻¹ := by
          rw [Real.div_rpow hp_pos.le hp1_nonneg]
    _ = p * ((p - 1) ^ (p - 1) / p ^ (p - 1)) := by
          field_simp
    _ = p * ((p - 1) / p) ^ (p - 1) := by
          rw [Real.div_rpow hp1_nonneg hp_pos.le]

/-- On the A1/A2 boundary, the x-partial formulas agree. -/
lemma DxuA1_eq_DxvGeTwo_on_A1A2_boundary (p x : ℝ) (hp : 2 ≤ p) (hx : 0 < x) :
    DxuA1 p x ((a p) * x) = DxvGeTwo p x ((a p) * x) := by
  have hpStar : pStar p = p := pStar_eq_self_of_two_le p hp
  have hp_pos : 0 < p := by linarith
  have hp1_pos : 0 < p - 1 := by linarith
  simp [DxuA1, DxvGeTwo, hx, a, hpStar]
  have h_sum : (x + (1 - 2 / p) * x) / 2 = ((p - 1) / p) * x := by
    field_simp [hp_pos.ne]
    ring
  have h_diff : (x - (1 - 2 / p) * x) / 2 = x / p := by
    field_simp [hp_pos.ne]
    ring
  rw [h_sum, h_diff,
      abs_of_pos (mul_pos (div_pos hp1_pos hp_pos) hx),
      abs_of_pos (div_pos hx hp_pos),
      alpha_eq_boundary_coeff p hp]
  simp_rw [Real.rpow_eq_pow]
  rw [Real.mul_rpow (div_nonneg (by linarith) hp_pos.le) hx.le,
      Real.div_rpow (by linarith : 0 ≤ p - 1) hp_pos.le,
      Real.div_rpow hx.le hp_pos.le]
  have hsplit : (p - 1) ^ p = (p - 1) ^ (p - 1) * (p - 1) := by
    calc
      (p - 1) ^ p = (p - 1) ^ ((p - 1) + 1) := by
        congr 2
        ring
      _ = (p - 1) ^ (p - 1) * (p - 1) ^ (1 : ℝ) := by
            rw [Real.rpow_add hp1_pos]
      _ = (p - 1) ^ (p - 1) * (p - 1) := by
            rw [Real.rpow_one]
  rw [hsplit]
  have hlin : (2 - p) * x + (p - 1) * ((1 - 2 / p) * x) = ((2 - p) / p) * x := by
    field_simp [hp_pos.ne]
    ring
  rw [hlin]
  have hxpow : x ^ (p - 1) = x ^ (p - 2) * x := by
    calc
      x ^ (p - 1) = x ^ ((p - 2) + 1) := by
        congr 2
        ring
      _ = x ^ (p - 2) * x ^ (1 : ℝ) := by
            rw [Real.rpow_add hx]
      _ = x ^ (p - 2) * x := by
            rw [Real.rpow_one]
  calc
    p * ((p - 1) ^ (p - 1) / p ^ (p - 1)) * (p / 2) *
        x ^ (p - 2) * (((2 - p) / p) * x)
        = p * ((p - 1) ^ (p - 1) / p ^ (p - 1)) * (p / 2) *
            (((2 - p) / p) * (x ^ (p - 2) * x)) := by
              ring
    _ = p * ((p - 1) ^ (p - 1) / p ^ (p - 1)) * (p / 2) *
          (((2 - p) / p) * x ^ (p - 1)) := by
            rw [← hxpow]
    _ = ((p - 1) ^ (p - 1) / p ^ (p - 1)) *
          x ^ (p - 1) * (p / 2) -
          (p - 1) ^ (p - 1) * (p - 1) *
            (x ^ (p - 1) / p ^ (p - 1)) * (p / 2) := by
              field_simp [hp_pos.ne]
              ring

/-- On the A1/A2 boundary, the y-partial formulas agree. -/
lemma DyuA1_eq_DyvGeTwo_on_A1A2_boundary (p x : ℝ) (hp : 2 ≤ p) (hx : 0 < x) :
    DyuA1 p x ((a p) * x) = DyvGeTwo p x ((a p) * x) := by
  have hpStar : pStar p = p := pStar_eq_self_of_two_le p hp
  have hp_pos : 0 < p := by linarith
  have hp1_pos : 0 < p - 1 := by linarith
  simp [DyuA1, DyvGeTwo, hx, a, hpStar]
  have h_sum : (x + (1 - 2 / p) * x) / 2 = ((p - 1) / p) * x := by
    field_simp [hp_pos.ne]
    ring
  have h_diff : (x - (1 - 2 / p) * x) / 2 = x / p := by
    field_simp [hp_pos.ne]
    ring
  rw [h_sum, h_diff,
      abs_of_pos (mul_pos (div_pos hp1_pos hp_pos) hx),
      abs_of_pos (div_pos hx hp_pos),
      alpha_eq_boundary_coeff p hp]
  simp_rw [Real.rpow_eq_pow]
  rw [Real.mul_rpow (div_nonneg (by linarith) hp_pos.le) hx.le,
      Real.div_rpow (by linarith : 0 ≤ p - 1) hp_pos.le,
      Real.div_rpow hx.le hp_pos.le]
  have hsplit : (p - 1) ^ p = (p - 1) ^ (p - 1) * (p - 1) := by
    calc
      (p - 1) ^ p = (p - 1) ^ ((p - 1) + 1) := by
        congr 2
        ring
      _ = (p - 1) ^ (p - 1) * (p - 1) ^ (1 : ℝ) := by
            rw [Real.rpow_add hp1_pos]
      _ = (p - 1) ^ (p - 1) * (p - 1) := by
            rw [Real.rpow_one]
  rw [hsplit]
  ring

lemma DxuA1_eq_DxvGeTwo_on_inter (p : ℝ) (hp : 2 ≤ p) (x y : ℝ)
    (h1 : closureA1 p x y) (h2 : closureA2 p x y) :
    DxuA1 p x y = DxvGeTwo p x y := by
  obtain ⟨hx, hay, hyx⟩ := h1
  obtain ⟨_, hmy, hyay⟩ := h2
  have heq : y = a p * x := le_antisymm hyay hay
  rcases hx.lt_or_eq with hxpos | hxeq
  · rw [heq]
    exact DxuA1_eq_DxvGeTwo_on_A1A2_boundary p x hp hxpos
  · have hx0 : x = 0 := hxeq.symm
    subst hx0
    have hy0 : y = 0 := by linarith
    subst hy0
    simp [DxuA1, DxvGeTwo]

lemma DyuA1_eq_DyvGeTwo_on_inter (p : ℝ) (hp : 2 ≤ p) (x y : ℝ)
    (h1 : closureA1 p x y) (h2 : closureA2 p x y) :
    DyuA1 p x y = DyvGeTwo p x y := by
  obtain ⟨hx, hay, hyx⟩ := h1
  obtain ⟨_, hmy, hyay⟩ := h2
  have heq : y = a p * x := le_antisymm hyay hay
  rcases hx.lt_or_eq with hxpos | hxeq
  · rw [heq]
    exact DyuA1_eq_DyvGeTwo_on_A1A2_boundary p x hp hxpos
  · have hx0 : x = 0 := hxeq.symm
    subst hx0
    have hy0 : y = 0 := by linarith
    subst hy0
    simp [DyuA1, DyvGeTwo]

lemma auxFunction1_Dx_eq_DxuA1 (p x y : ℝ) (h : closureA1 p x y) :
    DxauxFunction1 p x y = DxuA1 p x y := by
  simp only [DxauxFunction1, h, ite_true]

lemma auxFunction1_Dx_eq_DxvGeTwo (p : ℝ) (hp : 2 ≤ p) (x y : ℝ) (h2 : closureA2 p x y) :
    DxauxFunction1 p x y = DxvGeTwo p x y := by
  simp only [DxauxFunction1]
  by_cases h1 : closureA1 p x y
  · simp only [h1, ite_true]
    exact DxuA1_eq_DxvGeTwo_on_inter p hp x y h1 h2
  · simp only [h1, ite_false, h2, ite_true]

lemma auxFunction1_Dy_eq_DyuA1 (p x y : ℝ) (h : closureA1 p x y) :
    DyauxFunction1 p x y = DyuA1 p x y := by
  simp only [DyauxFunction1, h, ite_true]

lemma auxFunction1_Dy_eq_DyvGeTwo (p : ℝ) (hp : 2 ≤ p) (x y : ℝ) (h2 : closureA2 p x y) :
    DyauxFunction1 p x y = DyvGeTwo p x y := by
  simp only [DyauxFunction1]
  by_cases h1 : closureA1 p x y
  · simp only [h1, ite_true]
    exact DyuA1_eq_DyvGeTwo_on_inter p hp x y h1 h2
  · simp only [h1, ite_false, h2, ite_true]

lemma DxauxFunction1_eq_DyauxFunction1_on_diag (p : ℝ) (hp : 2 < p) (x : ℝ)
    (hx : 0 ≤ x) :
    DxauxFunction1 p x x = DyauxFunction1 p x x := by
  have hp' : 2 ≤ p := by linarith
  rcases hx.lt_or_eq with hxpos | hxeq
  · have hlt : a p < 1 := by
      have hpStar : pStar p = p := pStar_eq_self_of_two_le p hp'
      have hp_pos : 0 < p := by linarith
      rw [a, hpStar]
      have hdiv : 0 < 2 / p := by positivity
      linarith
    have hax : a p * x ≤ x := (mul_le_mul_of_nonneg_right hlt.le hx).trans_eq (one_mul x)
    have hcl : closureA1 p x x := ⟨hx, hax, le_rfl⟩
    calc
      DxauxFunction1 p x x = DxuA1 p x x := auxFunction1_Dx_eq_DxuA1 p x x hcl
      _ = DyuA1 p x x := by
        have hxpow : x ^ (p - 1) = x ^ (p - 2) * x := by
          calc
            x ^ (p - 1) = x ^ ((p - 2) + 1) := by ring_nf
            _ = x ^ (p - 2) * x ^ (1 : ℝ) := by rw [Real.rpow_add hxpos]
            _ = x ^ (p - 2) * x := by rw [Real.rpow_one]
        simp [DxuA1, DyuA1, hxpos, pStar_eq_self_of_two_le p hp']
        rw [hxpow]
        ring
      _ = DyauxFunction1 p x x := (auxFunction1_Dy_eq_DyuA1 p x x hcl).symm
  · subst hxeq
    simp [DxauxFunction1, DyauxFunction1, closureA1, DxuA1, DyuA1]

lemma DxauxFunction1_eq_neg_DyauxFunction1_on_antidiag (p : ℝ) (hp : 2 < p) (x : ℝ)
    (hx : 0 ≤ x) :
    DxauxFunction1 p x (-x) = -DyauxFunction1 p x (-x) := by
  have hp' : 2 ≤ p := by linarith
  rcases hx.lt_or_eq with hxpos | hxeq
  · have ha_nonneg : 0 ≤ a p := by
      have hpStar : pStar p = p := pStar_eq_self_of_two_le p hp'
      have hp_pos : 0 < p := by linarith
      rw [a, hpStar]
      field_simp [hp_pos.ne]
      nlinarith
    have hcl : closureA2 p x (-x) := by
      refine ⟨hx, le_rfl, ?_⟩
      exact le_trans (neg_nonpos.mpr hx) (mul_nonneg ha_nonneg hx)
    calc
      DxauxFunction1 p x (-x) = DxvGeTwo p x (-x) :=
        auxFunction1_Dx_eq_DxvGeTwo p hp' x (-x) hcl
      _ = -DyvGeTwo p x (-x) := by
        have hp1_ne : p - 1 ≠ 0 := by linarith
        have hdiff : (x - -x) / 2 = x := by ring
        simp [DxvGeTwo, DyvGeTwo, hxpos, hp1_ne, hdiff, abs_of_pos hxpos]
      _ = -DyauxFunction1 p x (-x) := by
        rw [auxFunction1_Dy_eq_DyvGeTwo p hp' x (-x) hcl]
  · subst hxeq
    simp [DxauxFunction1, DyauxFunction1, closureA1, DxuA1, DyuA1]

lemma continuousOn_DxauxFunction1 (p : ℝ) (hp : 2 ≤ p) :
    ContinuousOn (fun z : ℝ × ℝ => DxauxFunction1 p z.1 z.2)
      {z | QuarterPlane z.1 z.2} := by
  have hp1 : 1 < p := by linarith
  let S  := {z : ℝ × ℝ | QuarterPlane z.1 z.2}
  let S1 := {z : ℝ × ℝ | closureA1 p z.1 z.2}
  let S2 := {z : ℝ × ℝ | closureA2 p z.1 z.2}
  have hcover : S ⊆ S1 ∪ S2 := by
    intro ⟨x, y⟩ hz
    simp only [QuarterPlane, closureA1, closureA2, S, S1, S2,
               Set.mem_union, Set.mem_setOf_eq] at *
    obtain ⟨hx, hyx, hmx⟩ := hz
    by_cases h : a p * x ≤ y
    · exact Or.inl ⟨hx, h, hyx⟩
    · exact Or.inr ⟨hx, hmx, le_of_lt (not_le.mp h)⟩
  have hc1 : ContinuousOn (fun z : ℝ × ℝ => DxauxFunction1 p z.1 z.2) (S ∩ S1) := by
    apply ContinuousOn.congr ((continuousOn_DxuA1_closureA1 p hp1).mono
      (fun _ h => h.2))
    intro z hz
    exact auxFunction1_Dx_eq_DxuA1 p z.1 z.2 hz.2
  have hc2 : ContinuousOn (fun z : ℝ × ℝ => DxauxFunction1 p z.1 z.2) (S ∩ S2) := by
    apply ContinuousOn.congr ((continuousOn_DxvGeTwo_closureA2 p hp).mono
      (fun _ h => h.2))
    intro z hz
    exact auxFunction1_Dx_eq_DxvGeTwo p hp z.1 z.2 hz.2
  have hcl1 : IsClosed (S ∩ S1) := by
    apply IsClosed.inter _ (isClosed_closureA1_set p)
    simp only [QuarterPlane, S, Set.setOf_and]
    exact (isClosed_le continuous_const continuous_fst).inter
      ((isClosed_le continuous_snd continuous_fst).inter
       (isClosed_le continuous_fst.neg continuous_snd))
  have hcl2 : IsClosed (S ∩ S2) := by
    apply IsClosed.inter _ (isClosed_closureA2_set p)
    simp only [QuarterPlane, S, Set.setOf_and]
    exact (isClosed_le continuous_const continuous_fst).inter
      ((isClosed_le continuous_snd continuous_fst).inter
       (isClosed_le continuous_fst.neg continuous_snd))
  have hcover' : S ⊆ S ∩ S1 ∪ S ∩ S2 := fun z hz =>
    (hcover hz).imp (And.intro hz) (And.intro hz)
  apply ContinuousOn.mono _ hcover'
  exact hc1.union_of_isClosed hc2 hcl1 hcl2

lemma continuousOn_DyauxFunction1 (p : ℝ) (hp : 2 < p) :
    ContinuousOn (fun z : ℝ × ℝ => DyauxFunction1 p z.1 z.2)
      {z | QuarterPlane z.1 z.2} := by
  let S  := {z : ℝ × ℝ | QuarterPlane z.1 z.2}
  let S1 := {z : ℝ × ℝ | closureA1 p z.1 z.2}
  let S2 := {z : ℝ × ℝ | closureA2 p z.1 z.2}
  have hp' : 2 ≤ p := by linarith
  have hcover : S ⊆ S1 ∪ S2 := by
    intro ⟨x, y⟩ hz
    simp only [QuarterPlane, closureA1, closureA2, S, S1, S2,
               Set.mem_union, Set.mem_setOf_eq] at *
    obtain ⟨hx, hyx, hmx⟩ := hz
    by_cases h : a p * x ≤ y
    · exact Or.inl ⟨hx, h, hyx⟩
    · exact Or.inr ⟨hx, hmx, le_of_lt (not_le.mp h)⟩
  have hc1 : ContinuousOn (fun z : ℝ × ℝ => DyauxFunction1 p z.1 z.2) (S ∩ S1) := by
    apply ContinuousOn.congr ((continuousOn_DyuA1_closureA1 p hp).mono
      (fun _ h => h.2))
    intro z hz
    exact auxFunction1_Dy_eq_DyuA1 p z.1 z.2 hz.2
  have hc2 : ContinuousOn (fun z : ℝ × ℝ => DyauxFunction1 p z.1 z.2) (S ∩ S2) := by
    apply ContinuousOn.congr ((continuousOn_DyvGeTwo_closureA2 p hp').mono
      (fun _ h => h.2))
    intro z hz
    exact auxFunction1_Dy_eq_DyvGeTwo p hp' z.1 z.2 hz.2
  have hcl1 : IsClosed (S ∩ S1) := by
    apply IsClosed.inter _ (isClosed_closureA1_set p)
    simp only [QuarterPlane, S, Set.setOf_and]
    exact (isClosed_le continuous_const continuous_fst).inter
      ((isClosed_le continuous_snd continuous_fst).inter
       (isClosed_le continuous_fst.neg continuous_snd))
  have hcl2 : IsClosed (S ∩ S2) := by
    apply IsClosed.inter _ (isClosed_closureA2_set p)
    simp only [QuarterPlane, S, Set.setOf_and]
    exact (isClosed_le continuous_const continuous_fst).inter
      ((isClosed_le continuous_snd continuous_fst).inter
       (isClosed_le continuous_fst.neg continuous_snd))
  have hcover' : S ⊆ S ∩ S1 ∪ S ∩ S2 := fun z hz =>
    (hcover hz).imp (And.intro hz) (And.intro hz)
  apply ContinuousOn.mono _ hcover'
  exact hc1.union_of_isClosed hc2 hcl1 hcl2

/-- auxFunction1 is continuous on the QuarterPlane when p ≥ 2. -/
lemma continuousOn_auxFunction1 (p : ℝ) (hp : 2 ≤ p) :
    ContinuousOn (fun z : ℝ × ℝ => auxFunction1 p z.1 z.2)
      {z | QuarterPlane z.1 z.2} := by
  have hp1 : 1 < p := by linarith
  let S  := {z : ℝ × ℝ | QuarterPlane z.1 z.2}
  let S1 := {z : ℝ × ℝ | closureA1 p z.1 z.2}
  let S2 := {z : ℝ × ℝ | closureA2 p z.1 z.2}
  -- S is covered by S1 ∪ S2
  have hcover : S ⊆ S1 ∪ S2 := by
    intro ⟨x, y⟩ hz
    simp only [QuarterPlane, closureA1, closureA2, S, S1, S2,
               Set.mem_union, Set.mem_setOf_eq] at *
    obtain ⟨hx, hyx, hmx⟩ := hz
    by_cases h : a p * x ≤ y
    · exact Or.inl ⟨hx, h, hyx⟩
    · exact Or.inr ⟨hx, hmx, le_of_lt (not_le.mp h)⟩
  -- auxFunction1 = uA1 on S1
  have heq1 : ∀ z : ℝ × ℝ, z ∈ S1 →
      auxFunction1 p z.1 z.2 = uA1 p z.1 z.2 :=
    fun ⟨x, y⟩ h1 => auxFunction1_eq_uA1 p x y h1
  -- auxFunction1 = vGeTwo on S2
  have heq2 : ∀ z : ℝ × ℝ, z ∈ S2 →
      auxFunction1 p z.1 z.2 = vGeTwo p z.1 z.2 :=
    fun ⟨x, y⟩ h2 => auxFunction1_eq_vGeTwo p hp x y h2
  -- ContinuousOn on each piece (intersected with S)
  have hc1 : ContinuousOn (fun z : ℝ × ℝ => auxFunction1 p z.1 z.2) (S ∩ S1) := by
    apply ContinuousOn.congr ((continuousOn_uA1 p hp).mono
      (fun ⟨_, _⟩ ⟨hq, _⟩ => hq.1))
    exact fun z ⟨_, h1⟩ => heq1 z h1
  have hc2 : ContinuousOn (fun z : ℝ × ℝ => auxFunction1 p z.1 z.2) (S ∩ S2) := by
    apply ContinuousOn.congr ((continuous_vGeTwo p hp1).continuousOn.mono
      Set.inter_subset_left)
    exact fun z ⟨_, h2⟩ => heq2 z h2
  -- Pieces are closed (as subsets of ℝ²)
  have hcl1 : IsClosed (S ∩ S1) := by
    apply IsClosed.inter _ (isClosed_closureA1_set p)
    simp only [QuarterPlane, S, Set.setOf_and]
    exact (isClosed_le continuous_const continuous_fst).inter
      ((isClosed_le continuous_snd continuous_fst).inter
       (isClosed_le continuous_fst.neg continuous_snd))
  have hcl2 : IsClosed (S ∩ S2) := by
    apply IsClosed.inter _ (isClosed_closureA2_set p)
    simp only [QuarterPlane, S, Set.setOf_and]
    exact (isClosed_le continuous_const continuous_fst).inter
      ((isClosed_le continuous_snd continuous_fst).inter
       (isClosed_le continuous_fst.neg continuous_snd))
  -- Glue on S = (S ∩ S1) ∪ (S ∩ S2)
  have hcover' : S ⊆ S ∩ S1 ∪ S ∩ S2 := fun z hz =>
    (hcover hz).imp (And.intro hz) (And.intro hz)
  apply ContinuousOn.mono _ hcover'
  exact hc1.union_of_isClosed hc2 hcl1 hcl2

lemma continuousuCandidate (p : ℝ) (hp : 2 ≤ p) :
    ContinuousOn (fun z : ℝ × ℝ => uCandidate p z.1 z.2) Set.univ := by
  let Q1 : Set (ℝ × ℝ) := {z | QuarterPlane z.1 z.2}
  let Q2 : Set (ℝ × ℝ) := {z | QuarterPlane2 z.1 z.2}
  let Q3 : Set (ℝ × ℝ) := {z | QuarterPlane3 z.1 z.2}
  let Q4 : Set (ℝ × ℝ) := {z | QuarterPlane4 z.1 z.2}

  let f1 : ℝ × ℝ → ℝ := fun z => auxFunction1 p z.1 z.2
  let f2 : ℝ × ℝ → ℝ := fun z => auxFunction1 p (-z.1) (-z.2)
  let f3 : ℝ × ℝ → ℝ := fun z => auxFunction1 p z.2 z.1
  let f4 : ℝ × ℝ → ℝ := fun z => auxFunction1 p (-z.2) (-z.1)

  have hcont1 : ContinuousOn f1 Q1 := by
    simpa [Q1, f1] using continuousOn_auxFunction1 p hp

  have hcont2 : ContinuousOn f2 Q2 := by
    have hmap : Set.MapsTo (fun z : ℝ × ℝ => (-z.1, -z.2)) Q2 Q1 := by
      intro z hz
      rcases hz with ⟨hx, hy, hxy⟩
      exact ⟨by linarith, by linarith, by linarith⟩
    have hneg : Continuous (fun z : ℝ × ℝ => (-z.1, -z.2)) := by
      continuity
    simpa [Q1, Q2, f2] using
      (continuousOn_auxFunction1 p hp).comp hneg.continuousOn hmap

  have hcont3 : ContinuousOn f3 Q3 := by
    have hmap : Set.MapsTo (fun z : ℝ × ℝ => (z.2, z.1)) Q3 Q1 := by
      intro z hz
      rcases hz with ⟨hy, hnyx, hxy⟩
      exact ⟨hy, hxy, hnyx⟩
    have hswap : Continuous (fun z : ℝ × ℝ => (z.2, z.1)) := by
      continuity
    simpa [Q1, Q3, f3] using
      (continuousOn_auxFunction1 p hp).comp hswap.continuousOn hmap

  have hcont4 : ContinuousOn f4 Q4 := by
    have hmap : Set.MapsTo (fun z : ℝ × ℝ => (-z.2, -z.1)) Q4 Q1 := by
      intro z hz
      rcases hz with ⟨hy, hyx, hxn⟩
      exact ⟨by linarith, by linarith, by linarith⟩
    have hns : Continuous (fun z : ℝ × ℝ => (-z.2, -z.1)) := by
      continuity
    simpa [Q1, Q4, f4] using
      (continuousOn_auxFunction1 p hp).comp hns.continuousOn hmap

  have hcl1 : IsClosed Q1 := by
    simp only [Q1, QuarterPlane, Set.setOf_and]
    exact (isClosed_le continuous_const continuous_fst).inter
      ((isClosed_le continuous_snd continuous_fst).inter
        (isClosed_le continuous_fst.neg continuous_snd))
  have hcl2 : IsClosed Q2 := by
    simp only [Q2, QuarterPlane2, Set.setOf_and]
    exact (isClosed_le continuous_fst continuous_const).inter
      ((isClosed_le continuous_snd continuous_fst.neg).inter
        (isClosed_le continuous_fst continuous_snd))
  have hcl3 : IsClosed Q3 := by
    simp only [Q3, QuarterPlane3, Set.setOf_and]
    exact (isClosed_le continuous_const continuous_snd).inter
      ((isClosed_le continuous_snd.neg continuous_fst).inter
        (isClosed_le continuous_fst continuous_snd))
  have hcl4 : IsClosed Q4 := by
    simp only [Q4, QuarterPlane4, Set.setOf_and]
    exact (isClosed_le continuous_snd continuous_const).inter
      ((isClosed_le continuous_snd continuous_fst).inter
        (isClosed_le continuous_fst continuous_snd.neg))

  have h12 : ∀ z : ℝ × ℝ, z ∈ Q1 → z ∈ Q2 → f1 z = f2 z := by
    intro z hz1 hz2
    rcases z with ⟨x, y⟩
    rcases hz1 with ⟨hx0, hyx, hmx⟩
    rcases hz2 with ⟨hx1, hy, hxy⟩
    have hx : x = 0 := le_antisymm hx1 hx0
    have hy0 : y = 0 := by
      have hy_le : y ≤ 0 := by simpa [hx] using hyx
      have hy_ge : 0 ≤ y := by simpa [hx] using hxy
      exact le_antisymm hy_le hy_ge
    simp [f1, f2, hx, hy0]

  have h13 : ∀ z : ℝ × ℝ, z ∈ Q1 → z ∈ Q3 → f1 z = f3 z := by
    intro z hz1 hz3
    rcases z with ⟨x, y⟩
    rcases hz1 with ⟨_, hyx, _⟩
    rcases hz3 with ⟨_, _, hxy⟩
    have hxy' : x = y := le_antisymm hxy hyx
    simp [f1, f3, hxy']

  have h14 : ∀ z : ℝ × ℝ, z ∈ Q1 → z ∈ Q4 → f1 z = f4 z := by
    intro z hz1 hz4
    rcases z with ⟨x, y⟩
    rcases hz1 with ⟨_, _, hmx⟩
    rcases hz4 with ⟨_, _, hxn⟩
    have hy : y = -x := by linarith [hxn, hmx]
    simp [f1, f4, hy]

  have h23 : ∀ z : ℝ × ℝ, z ∈ Q2 → z ∈ Q3 → f2 z = f3 z := by
    intro z hz2 hz3
    rcases z with ⟨x, y⟩
    rcases hz2 with ⟨_, hy, _⟩
    rcases hz3 with ⟨_, hnyx, _⟩
    have hx : x = -y := le_antisymm (by linarith [hy]) hnyx
    simp [f2, f3, hx]

  have h24 : ∀ z : ℝ × ℝ, z ∈ Q2 → z ∈ Q4 → f2 z = f4 z := by
    intro z hz2 hz4
    rcases z with ⟨x, y⟩
    rcases hz2 with ⟨_, _, hxy⟩
    rcases hz4 with ⟨_, hyx, _⟩
    have hxy' : x = y := le_antisymm hxy hyx
    simp [f2, f4, hxy']

  have h34 : ∀ z : ℝ × ℝ, z ∈ Q3 → z ∈ Q4 → f3 z = f4 z := by
    intro z hz3 hz4
    rcases z with ⟨x, y⟩
    rcases hz3 with ⟨hy0, hnyx, hxy⟩
    rcases hz4 with ⟨hy1, hyx, hxn⟩
    have hy : y = 0 := le_antisymm hy1 hy0
    have hx : x = 0 := by
      have hx_le : x ≤ 0 := by simpa [hy] using hxn
      have hx_ge : 0 ≤ x := by simpa [hy] using hnyx
      exact le_antisymm hx_le hx_ge
    simp [f3, f4, hx, hy]

  have heq1 : ∀ z : ℝ × ℝ, z ∈ Q1 → uCandidate p z.1 z.2 = f1 z := by
    intro z hz1
    have hq1 : QuarterPlane z.1 z.2 := by simpa [Q1] using hz1
    simp [uCandidate, f1, hq1]

  have heq2 : ∀ z : ℝ × ℝ, z ∈ Q2 → uCandidate p z.1 z.2 = f2 z := by
    intro z hz2
    by_cases hz1 : z ∈ Q1
    · have hu : uCandidate p z.1 z.2 = f1 z := heq1 z hz1
      exact hu.trans (h12 z hz1 hz2)
    · have hq1 : ¬ QuarterPlane z.1 z.2 := by simpa [Q1] using hz1
      have hq2 : QuarterPlane2 z.1 z.2 := by simpa [Q2] using hz2
      simp [uCandidate, f2, hq1, hq2]

  have heq3 : ∀ z : ℝ × ℝ, z ∈ Q3 → uCandidate p z.1 z.2 = f3 z := by
    intro z hz3
    by_cases hz1 : z ∈ Q1
    · have hu : uCandidate p z.1 z.2 = f1 z := heq1 z hz1
      exact hu.trans (h13 z hz1 hz3)
    · by_cases hz2 : z ∈ Q2
      · have hu : uCandidate p z.1 z.2 = f2 z := heq2 z hz2
        exact hu.trans (h23 z hz2 hz3)
      · have hq1 : ¬ QuarterPlane z.1 z.2 := by simpa [Q1] using hz1
        have hq2 : ¬ QuarterPlane2 z.1 z.2 := by simpa [Q2] using hz2
        have hq3 : QuarterPlane3 z.1 z.2 := by simpa [Q3] using hz3
        simp [uCandidate, f3, hq1, hq2, hq3]

  have heq4 : ∀ z : ℝ × ℝ, z ∈ Q4 → uCandidate p z.1 z.2 = f4 z := by
    intro z hz4
    by_cases hz1 : z ∈ Q1
    · have hu : uCandidate p z.1 z.2 = f1 z := heq1 z hz1
      exact hu.trans (h14 z hz1 hz4)
    · by_cases hz2 : z ∈ Q2
      · have hu : uCandidate p z.1 z.2 = f2 z := heq2 z hz2
        exact hu.trans (h24 z hz2 hz4)
      · by_cases hz3 : z ∈ Q3
        · have hu : uCandidate p z.1 z.2 = f3 z := heq3 z hz3
          exact hu.trans (h34 z hz3 hz4)
        · have hq1 : ¬ QuarterPlane z.1 z.2 := by simpa [Q1] using hz1
          have hq2 : ¬ QuarterPlane2 z.1 z.2 := by simpa [Q2] using hz2
          have hq3 : ¬ QuarterPlane3 z.1 z.2 := by simpa [Q3] using hz3
          have hq4 : QuarterPlane4 z.1 z.2 := by simpa [Q4] using hz4
          simp [uCandidate, f4, hq1, hq2, hq3, hq4]

  have hc1 : ContinuousOn (fun z : ℝ × ℝ => uCandidate p z.1 z.2) Q1 := by
    apply ContinuousOn.congr hcont1
    intro z hz
    simpa using (heq1 z hz)
  have hc2 : ContinuousOn (fun z : ℝ × ℝ => uCandidate p z.1 z.2) Q2 := by
    apply ContinuousOn.congr hcont2
    intro z hz
    simpa using (heq2 z hz)
  have hc3 : ContinuousOn (fun z : ℝ × ℝ => uCandidate p z.1 z.2) Q3 := by
    apply ContinuousOn.congr hcont3
    intro z hz
    simpa using (heq3 z hz)
  have hc4 : ContinuousOn (fun z : ℝ × ℝ => uCandidate p z.1 z.2) Q4 := by
    apply ContinuousOn.congr hcont4
    intro z hz
    simpa using (heq4 z hz)

  have hcover : Set.univ ⊆ Q1 ∪ Q2 ∪ Q3 ∪ Q4 := by
    intro z _
    rcases z with ⟨x, y⟩
    by_cases hxy : |x| ≤ |y|
    · by_cases hy : 0 ≤ y
      · have habs : |x| ≤ y := by simpa [abs_of_nonneg hy] using hxy
        rcases abs_le.mp habs with ⟨h1, h2⟩
        -- h1 : -y ≤ x, h2 : x ≤ y
        -- pertence a Q3
        exact Or.inl (Or.inr ⟨hy, h1, h2⟩)
      · have hy' : y < 0 := lt_of_not_ge hy
        have habs : |x| ≤ -y := by
          simpa [abs_of_neg hy'] using hxy
        rcases abs_le.mp habs with ⟨h1, h2⟩
        have h1' : y ≤ x := by
          simpa using h1
        exact Or.inr ⟨le_of_lt hy', h1', h2⟩
    · have hyx : |y| ≤ |x| := by
        rw [not_le] at hxy
        exact le_of_lt hxy
      by_cases hx : 0 ≤ x
      · have habs : |y| ≤ x := by simpa [abs_of_nonneg hx] using hyx
        rcases abs_le.mp habs with ⟨h1, h2⟩
        -- h1 : -x ≤ y, h2 : y ≤ x
        -- pertence a Q1
        exact Or.inl (Or.inl (Or.inl ⟨hx, h2, h1⟩))
      · have hx' : x < 0 := lt_of_not_ge hx
        have habs : |y| ≤ -x := by
         simpa [abs_of_neg hx'] using hyx
        rcases abs_le.mp habs with ⟨h1, h2⟩
        have h1' : x ≤ y := by
         simpa using h1
        exact Or.inl (Or.inl (Or.inr ⟨le_of_lt hx', h2, h1'⟩))

  have hc12 : ContinuousOn (fun z : ℝ × ℝ => uCandidate p z.1 z.2) (Q1 ∪ Q2) :=
    hc1.union_of_isClosed hc2 hcl1 hcl2
  have hcl12 : IsClosed (Q1 ∪ Q2) := hcl1.union hcl2
  have hc123 : ContinuousOn (fun z : ℝ × ℝ => uCandidate p z.1 z.2) (Q1 ∪ Q2 ∪ Q3) :=
    hc12.union_of_isClosed hc3 hcl12 hcl3
  have hcl123 : IsClosed (Q1 ∪ Q2 ∪ Q3) := hcl12.union hcl3
  have hc1234 : ContinuousOn (fun z : ℝ × ℝ => uCandidate p z.1 z.2) (Q1 ∪ Q2 ∪ Q3 ∪ Q4) :=
    hc123.union_of_isClosed hc4 hcl123 hcl4

  apply ContinuousOn.mono hc1234
  intro z hz
  exact hcover hz




lemma continuousDxuCandidate (p : ℝ) (hp : 2 < p) :
    ContinuousOn (fun z : ℝ × ℝ => DxuCandidate p z.1 z.2) Set.univ := by
  have hp' : 2 ≤ p := by linarith
  let Q1 : Set (ℝ × ℝ) := {z | QuarterPlane z.1 z.2}
  let Q2 : Set (ℝ × ℝ) := {z | QuarterPlane2 z.1 z.2}
  let Q3 : Set (ℝ × ℝ) := {z | QuarterPlane3 z.1 z.2}
  let Q4 : Set (ℝ × ℝ) := {z | QuarterPlane4 z.1 z.2}
  let f1 : ℝ × ℝ → ℝ := fun z => DxauxFunction1 p z.1 z.2
  let f2 : ℝ × ℝ → ℝ := fun z => -DxauxFunction1 p (-z.1) (-z.2)
  let f3 : ℝ × ℝ → ℝ := fun z => DyauxFunction1 p z.2 z.1
  let f4 : ℝ × ℝ → ℝ := fun z => -DyauxFunction1 p (-z.2) (-z.1)
  have hcont1 : ContinuousOn f1 Q1 := by
    simpa [Q1, f1] using continuousOn_DxauxFunction1 p hp'
  have hcont2 : ContinuousOn f2 Q2 := by
    have hmap : Set.MapsTo (fun z : ℝ × ℝ => (-z.1, -z.2)) Q2 Q1 := by
      intro z hz
      rcases hz with ⟨hx, hy, hxy⟩
      exact ⟨by linarith, by linarith, by linarith⟩
    have hneg : Continuous (fun z : ℝ × ℝ => (-z.1, -z.2)) := by continuity
    simpa [Q1, Q2, f2] using
      ((continuousOn_DxauxFunction1 p hp').comp hneg.continuousOn hmap).neg
  have hcont3 : ContinuousOn f3 Q3 := by
    have hmap : Set.MapsTo (fun z : ℝ × ℝ => (z.2, z.1)) Q3 Q1 := by
      intro z hz
      rcases hz with ⟨hy, hnyx, hxy⟩
      exact ⟨hy, hxy, hnyx⟩
    have hswap : Continuous (fun z : ℝ × ℝ => (z.2, z.1)) := by continuity
    simpa [Q1, Q3, f3] using
      (continuousOn_DyauxFunction1 p hp).comp hswap.continuousOn hmap
  have hcont4 : ContinuousOn f4 Q4 := by
    have hmap : Set.MapsTo (fun z : ℝ × ℝ => (-z.2, -z.1)) Q4 Q1 := by
      intro z hz
      rcases hz with ⟨hy, hyx, hxn⟩
      exact ⟨by linarith, by linarith, by linarith⟩
    have hns : Continuous (fun z : ℝ × ℝ => (-z.2, -z.1)) := by continuity
    simpa [Q1, Q4, f4] using
      ((continuousOn_DyauxFunction1 p hp).comp hns.continuousOn hmap).neg
  have hcl1 : IsClosed Q1 := by
    simp only [Q1, QuarterPlane, Set.setOf_and]
    exact (isClosed_le continuous_const continuous_fst).inter
      ((isClosed_le continuous_snd continuous_fst).inter
        (isClosed_le continuous_fst.neg continuous_snd))
  have hcl2 : IsClosed Q2 := by
    simp only [Q2, QuarterPlane2, Set.setOf_and]
    exact (isClosed_le continuous_fst continuous_const).inter
      ((isClosed_le continuous_snd continuous_fst.neg).inter
        (isClosed_le continuous_fst continuous_snd))
  have hcl3 : IsClosed Q3 := by
    simp only [Q3, QuarterPlane3, Set.setOf_and]
    exact (isClosed_le continuous_const continuous_snd).inter
      ((isClosed_le continuous_snd.neg continuous_fst).inter
        (isClosed_le continuous_fst continuous_snd))
  have hcl4 : IsClosed Q4 := by
    simp only [Q4, QuarterPlane4, Set.setOf_and]
    exact (isClosed_le continuous_snd continuous_const).inter
      ((isClosed_le continuous_snd continuous_fst).inter
        (isClosed_le continuous_fst continuous_snd.neg))
  have h12 : ∀ z : ℝ × ℝ, z ∈ Q1 → z ∈ Q2 → f1 z = f2 z := by
    intro z hz1 hz2
    rcases z with ⟨x, y⟩
    rcases hz1 with ⟨hx0, hyx, _⟩
    rcases hz2 with ⟨hx1, _, hxy⟩
    have hx : x = 0 := le_antisymm hx1 hx0
    have hy : y = 0 := by
      have hy_le : y ≤ 0 := by simpa [hx] using hyx
      have hy_ge : 0 ≤ y := by simpa [hx] using hxy
      exact le_antisymm hy_le hy_ge
    simp [f1, f2, hx, hy, DxauxFunction1, closureA1, DxuA1]
  have h13 : ∀ z : ℝ × ℝ, z ∈ Q1 → z ∈ Q3 → f1 z = f3 z := by
    intro z hz1 hz3
    rcases z with ⟨x, y⟩
    rcases hz1 with ⟨_, hyx, _⟩
    rcases hz3 with ⟨hy0, _, hxy⟩
    have hxy' : x = y := le_antisymm hxy hyx
    subst x
    simpa [f1, f3] using DxauxFunction1_eq_DyauxFunction1_on_diag p hp y hy0
  have h14 : ∀ z : ℝ × ℝ, z ∈ Q1 → z ∈ Q4 → f1 z = f4 z := by
    intro z hz1 hz4
    rcases z with ⟨x, y⟩
    rcases hz1 with ⟨hx0, _, hmx⟩
    rcases hz4 with ⟨_, _, hxn⟩
    have hy : y = -x := by linarith [hxn, hmx]
    subst hy
    simpa [f1, f4] using DxauxFunction1_eq_neg_DyauxFunction1_on_antidiag p hp x hx0
  have h23 : ∀ z : ℝ × ℝ, z ∈ Q2 → z ∈ Q3 → f2 z = f3 z := by
    intro z hz2 hz3
    rcases z with ⟨x, y⟩
    rcases hz2 with ⟨_, hy, _⟩
    rcases hz3 with ⟨hy0, hnyx, _⟩
    have hx : x = -y := le_antisymm (by linarith [hy]) hnyx
    subst x
    have h := DxauxFunction1_eq_neg_DyauxFunction1_on_antidiag p hp y hy0
    have h' : -DxauxFunction1 p y (-y) = DyauxFunction1 p y (-y) := by
      linarith
    simpa [f2, f3] using h'
  have h24 : ∀ z : ℝ × ℝ, z ∈ Q2 → z ∈ Q4 → f2 z = f4 z := by
    intro z hz2 hz4
    rcases z with ⟨x, y⟩
    rcases hz2 with ⟨hx0, _, hxy⟩
    rcases hz4 with ⟨_, hyx, _⟩
    have hxy' : x = y := le_antisymm hxy hyx
    subst x
    have hnonneg : 0 ≤ -y := by linarith
    have h := DxauxFunction1_eq_DyauxFunction1_on_diag p hp (-y) hnonneg
    simpa [f2, f4] using congrArg Neg.neg h
  have h34 : ∀ z : ℝ × ℝ, z ∈ Q3 → z ∈ Q4 → f3 z = f4 z := by
    intro z hz3 hz4
    rcases z with ⟨x, y⟩
    rcases hz3 with ⟨hy0, hnyx, _⟩
    rcases hz4 with ⟨hy1, _, hxn⟩
    have hy : y = 0 := le_antisymm hy1 hy0
    have hx : x = 0 := by
      have hx_le : x ≤ 0 := by simpa [hy] using hxn
      have hx_ge : 0 ≤ x := by simpa [hy] using hnyx
      exact le_antisymm hx_le hx_ge
    simp [f3, f4, hx, hy, DyauxFunction1, closureA1, DyuA1]
  have heq1 : ∀ z : ℝ × ℝ, z ∈ Q1 → DxuCandidate p z.1 z.2 = f1 z := by
    intro z hz1
    have hq1 : QuarterPlane z.1 z.2 := by simpa [Q1] using hz1
    simp [DxuCandidate, f1, hq1]
  have heq2 : ∀ z : ℝ × ℝ, z ∈ Q2 → DxuCandidate p z.1 z.2 = f2 z := by
    intro z hz2
    by_cases hz1 : z ∈ Q1
    · exact (heq1 z hz1).trans (h12 z hz1 hz2)
    · have hq1 : ¬ QuarterPlane z.1 z.2 := by simpa [Q1] using hz1
      have hq2 : QuarterPlane2 z.1 z.2 := by simpa [Q2] using hz2
      simp [DxuCandidate, f2, hq1, hq2]
  have heq3 : ∀ z : ℝ × ℝ, z ∈ Q3 → DxuCandidate p z.1 z.2 = f3 z := by
    intro z hz3
    by_cases hz1 : z ∈ Q1
    · exact (heq1 z hz1).trans (h13 z hz1 hz3)
    · by_cases hz2 : z ∈ Q2
      · exact (heq2 z hz2).trans (h23 z hz2 hz3)
      · have hq1 : ¬ QuarterPlane z.1 z.2 := by simpa [Q1] using hz1
        have hq2 : ¬ QuarterPlane2 z.1 z.2 := by simpa [Q2] using hz2
        have hq3 : QuarterPlane3 z.1 z.2 := by simpa [Q3] using hz3
        simp [DxuCandidate, f3, hq1, hq2, hq3]
  have heq4 : ∀ z : ℝ × ℝ, z ∈ Q4 → DxuCandidate p z.1 z.2 = f4 z := by
    intro z hz4
    by_cases hz1 : z ∈ Q1
    · exact (heq1 z hz1).trans (h14 z hz1 hz4)
    · by_cases hz2 : z ∈ Q2
      · exact (heq2 z hz2).trans (h24 z hz2 hz4)
      · by_cases hz3 : z ∈ Q3
        · exact (heq3 z hz3).trans (h34 z hz3 hz4)
        · have hq1 : ¬ QuarterPlane z.1 z.2 := by simpa [Q1] using hz1
          have hq2 : ¬ QuarterPlane2 z.1 z.2 := by simpa [Q2] using hz2
          have hq3 : ¬ QuarterPlane3 z.1 z.2 := by simpa [Q3] using hz3
          have hq4 : QuarterPlane4 z.1 z.2 := by simpa [Q4] using hz4
          simp [DxuCandidate, f4, hq1, hq2, hq3, hq4]
  have hc1 : ContinuousOn (fun z : ℝ × ℝ => DxuCandidate p z.1 z.2) Q1 := by
    apply ContinuousOn.congr hcont1
    intro z hz
    simpa using heq1 z hz
  have hc2 : ContinuousOn (fun z : ℝ × ℝ => DxuCandidate p z.1 z.2) Q2 := by
    apply ContinuousOn.congr hcont2
    intro z hz
    simpa using heq2 z hz
  have hc3 : ContinuousOn (fun z : ℝ × ℝ => DxuCandidate p z.1 z.2) Q3 := by
    apply ContinuousOn.congr hcont3
    intro z hz
    simpa using heq3 z hz
  have hc4 : ContinuousOn (fun z : ℝ × ℝ => DxuCandidate p z.1 z.2) Q4 := by
    apply ContinuousOn.congr hcont4
    intro z hz
    simpa using heq4 z hz
  have hcover : Set.univ ⊆ Q1 ∪ Q2 ∪ Q3 ∪ Q4 := by
    intro z _
    rcases z with ⟨x, y⟩
    by_cases hxy : |x| ≤ |y|
    · by_cases hy : 0 ≤ y
      · have habs : |x| ≤ y := by simpa [abs_of_nonneg hy] using hxy
        rcases abs_le.mp habs with ⟨h1, h2⟩
        exact Or.inl (Or.inr ⟨hy, h1, h2⟩)
      · have hy' : y < 0 := lt_of_not_ge hy
        have habs : |x| ≤ -y := by simpa [abs_of_neg hy'] using hxy
        rcases abs_le.mp habs with ⟨h1, h2⟩
        have h1' : y ≤ x := by simpa using h1
        exact Or.inr ⟨le_of_lt hy', h1', h2⟩
    · have hyx : |y| ≤ |x| := le_of_lt (not_le.mp hxy)
      by_cases hx : 0 ≤ x
      · have habs : |y| ≤ x := by simpa [abs_of_nonneg hx] using hyx
        rcases abs_le.mp habs with ⟨h1, h2⟩
        exact Or.inl (Or.inl (Or.inl ⟨hx, h2, h1⟩))
      · have hx' : x < 0 := lt_of_not_ge hx
        have habs : |y| ≤ -x := by simpa [abs_of_neg hx'] using hyx
        rcases abs_le.mp habs with ⟨h1, h2⟩
        have h1' : x ≤ y := by simpa using h1
        exact Or.inl (Or.inl (Or.inr ⟨le_of_lt hx', h2, h1'⟩))
  have hc12 := hc1.union_of_isClosed hc2 hcl1 hcl2
  have hcl12 : IsClosed (Q1 ∪ Q2) := hcl1.union hcl2
  have hc123 := hc12.union_of_isClosed hc3 hcl12 hcl3
  have hcl123 : IsClosed (Q1 ∪ Q2 ∪ Q3) := hcl12.union hcl3
  have hc1234 := hc123.union_of_isClosed hc4 hcl123 hcl4
  exact ContinuousOn.mono hc1234 hcover

lemma continuousDyuCandidate (p : ℝ) (hp : 2 < p) :
    ContinuousOn (fun z : ℝ × ℝ => DyuCandidate p z.1 z.2) Set.univ := by
  have hp' : 2 ≤ p := by linarith
  let Q1 : Set (ℝ × ℝ) := {z | QuarterPlane z.1 z.2}
  let Q2 : Set (ℝ × ℝ) := {z | QuarterPlane2 z.1 z.2}
  let Q3 : Set (ℝ × ℝ) := {z | QuarterPlane3 z.1 z.2}
  let Q4 : Set (ℝ × ℝ) := {z | QuarterPlane4 z.1 z.2}
  let f1 : ℝ × ℝ → ℝ := fun z => DyauxFunction1 p z.1 z.2
  let f2 : ℝ × ℝ → ℝ := fun z => -DyauxFunction1 p (-z.1) (-z.2)
  let f3 : ℝ × ℝ → ℝ := fun z => DxauxFunction1 p z.2 z.1
  let f4 : ℝ × ℝ → ℝ := fun z => -DxauxFunction1 p (-z.2) (-z.1)
  have hcont1 : ContinuousOn f1 Q1 := by
    simpa [Q1, f1] using continuousOn_DyauxFunction1 p hp
  have hcont2 : ContinuousOn f2 Q2 := by
    have hmap : Set.MapsTo (fun z : ℝ × ℝ => (-z.1, -z.2)) Q2 Q1 := by
      intro z hz
      rcases hz with ⟨hx, hy, hxy⟩
      exact ⟨by linarith, by linarith, by linarith⟩
    have hneg : Continuous (fun z : ℝ × ℝ => (-z.1, -z.2)) := by continuity
    simpa [Q1, Q2, f2] using
      ((continuousOn_DyauxFunction1 p hp).comp hneg.continuousOn hmap).neg
  have hcont3 : ContinuousOn f3 Q3 := by
    have hmap : Set.MapsTo (fun z : ℝ × ℝ => (z.2, z.1)) Q3 Q1 := by
      intro z hz
      rcases hz with ⟨hy, hnyx, hxy⟩
      exact ⟨hy, hxy, hnyx⟩
    have hswap : Continuous (fun z : ℝ × ℝ => (z.2, z.1)) := by continuity
    simpa [Q1, Q3, f3] using
      (continuousOn_DxauxFunction1 p hp').comp hswap.continuousOn hmap
  have hcont4 : ContinuousOn f4 Q4 := by
    have hmap : Set.MapsTo (fun z : ℝ × ℝ => (-z.2, -z.1)) Q4 Q1 := by
      intro z hz
      rcases hz with ⟨hy, hyx, hxn⟩
      exact ⟨by linarith, by linarith, by linarith⟩
    have hns : Continuous (fun z : ℝ × ℝ => (-z.2, -z.1)) := by continuity
    simpa [Q1, Q4, f4] using
      ((continuousOn_DxauxFunction1 p hp').comp hns.continuousOn hmap).neg
  have hcl1 : IsClosed Q1 := by
    simp only [Q1, QuarterPlane, Set.setOf_and]
    exact (isClosed_le continuous_const continuous_fst).inter
      ((isClosed_le continuous_snd continuous_fst).inter
        (isClosed_le continuous_fst.neg continuous_snd))
  have hcl2 : IsClosed Q2 := by
    simp only [Q2, QuarterPlane2, Set.setOf_and]
    exact (isClosed_le continuous_fst continuous_const).inter
      ((isClosed_le continuous_snd continuous_fst.neg).inter
        (isClosed_le continuous_fst continuous_snd))
  have hcl3 : IsClosed Q3 := by
    simp only [Q3, QuarterPlane3, Set.setOf_and]
    exact (isClosed_le continuous_const continuous_snd).inter
      ((isClosed_le continuous_snd.neg continuous_fst).inter
        (isClosed_le continuous_fst continuous_snd))
  have hcl4 : IsClosed Q4 := by
    simp only [Q4, QuarterPlane4, Set.setOf_and]
    exact (isClosed_le continuous_snd continuous_const).inter
      ((isClosed_le continuous_snd continuous_fst).inter
        (isClosed_le continuous_fst continuous_snd.neg))
  have h12 : ∀ z : ℝ × ℝ, z ∈ Q1 → z ∈ Q2 → f1 z = f2 z := by
    intro z hz1 hz2
    rcases z with ⟨x, y⟩
    rcases hz1 with ⟨hx0, hyx, _⟩
    rcases hz2 with ⟨hx1, _, hxy⟩
    have hx : x = 0 := le_antisymm hx1 hx0
    have hy : y = 0 := by
      have hy_le : y ≤ 0 := by simpa [hx] using hyx
      have hy_ge : 0 ≤ y := by simpa [hx] using hxy
      exact le_antisymm hy_le hy_ge
    simp [f1, f2, hx, hy, DyauxFunction1, closureA1, DyuA1]
  have h13 : ∀ z : ℝ × ℝ, z ∈ Q1 → z ∈ Q3 → f1 z = f3 z := by
    intro z hz1 hz3
    rcases z with ⟨x, y⟩
    rcases hz1 with ⟨_, hyx, _⟩
    rcases hz3 with ⟨hy0, _, hxy⟩
    have hxy' : x = y := le_antisymm hxy hyx
    subst x
    simpa [f1, f3] using (DxauxFunction1_eq_DyauxFunction1_on_diag p hp y hy0).symm
  have h14 : ∀ z : ℝ × ℝ, z ∈ Q1 → z ∈ Q4 → f1 z = f4 z := by
    intro z hz1 hz4
    rcases z with ⟨x, y⟩
    rcases hz1 with ⟨hx0, _, hmx⟩
    rcases hz4 with ⟨_, _, hxn⟩
    have hy : y = -x := by linarith [hxn, hmx]
    subst y
    have h := DxauxFunction1_eq_neg_DyauxFunction1_on_antidiag p hp x hx0
    have h' : DyauxFunction1 p x (-x) = -DxauxFunction1 p x (-x) := by
      linarith
    simpa [f1, f4] using h'
  have h23 : ∀ z : ℝ × ℝ, z ∈ Q2 → z ∈ Q3 → f2 z = f3 z := by
    intro z hz2 hz3
    rcases z with ⟨x, y⟩
    rcases hz2 with ⟨_, hy, _⟩
    rcases hz3 with ⟨hy0, hnyx, _⟩
    have hx : x = -y := le_antisymm (by linarith [hy]) hnyx
    subst x
    have h := DxauxFunction1_eq_neg_DyauxFunction1_on_antidiag p hp y hy0
    simpa [f2, f3] using h.symm
  have h24 : ∀ z : ℝ × ℝ, z ∈ Q2 → z ∈ Q4 → f2 z = f4 z := by
    intro z hz2 hz4
    rcases z with ⟨x, y⟩
    rcases hz2 with ⟨hx0, _, hxy⟩
    rcases hz4 with ⟨_, hyx, _⟩
    have hxy' : x = y := le_antisymm hxy hyx
    subst x
    have hnonneg : 0 ≤ -y := by linarith
    have h := DxauxFunction1_eq_DyauxFunction1_on_diag p hp (-y) hnonneg
    simpa [f2, f4] using congrArg Neg.neg h.symm
  have h34 : ∀ z : ℝ × ℝ, z ∈ Q3 → z ∈ Q4 → f3 z = f4 z := by
    intro z hz3 hz4
    rcases z with ⟨x, y⟩
    rcases hz3 with ⟨hy0, hnyx, _⟩
    rcases hz4 with ⟨hy1, _, hxn⟩
    have hy : y = 0 := le_antisymm hy1 hy0
    have hx : x = 0 := by
      have hx_le : x ≤ 0 := by simpa [hy] using hxn
      have hx_ge : 0 ≤ x := by simpa [hy] using hnyx
      exact le_antisymm hx_le hx_ge
    simp [f3, f4, hx, hy, DxauxFunction1, closureA1, DxuA1]
  have heq1 : ∀ z : ℝ × ℝ, z ∈ Q1 → DyuCandidate p z.1 z.2 = f1 z := by
    intro z hz1
    have hq1 : QuarterPlane z.1 z.2 := by simpa [Q1] using hz1
    simp [DyuCandidate, f1, hq1]
  have heq2 : ∀ z : ℝ × ℝ, z ∈ Q2 → DyuCandidate p z.1 z.2 = f2 z := by
    intro z hz2
    by_cases hz1 : z ∈ Q1
    · exact (heq1 z hz1).trans (h12 z hz1 hz2)
    · have hq1 : ¬ QuarterPlane z.1 z.2 := by simpa [Q1] using hz1
      have hq2 : QuarterPlane2 z.1 z.2 := by simpa [Q2] using hz2
      simp [DyuCandidate, f2, hq1, hq2]
  have heq3 : ∀ z : ℝ × ℝ, z ∈ Q3 → DyuCandidate p z.1 z.2 = f3 z := by
    intro z hz3
    by_cases hz1 : z ∈ Q1
    · exact (heq1 z hz1).trans (h13 z hz1 hz3)
    · by_cases hz2 : z ∈ Q2
      · exact (heq2 z hz2).trans (h23 z hz2 hz3)
      · have hq1 : ¬ QuarterPlane z.1 z.2 := by simpa [Q1] using hz1
        have hq2 : ¬ QuarterPlane2 z.1 z.2 := by simpa [Q2] using hz2
        have hq3 : QuarterPlane3 z.1 z.2 := by simpa [Q3] using hz3
        simp [DyuCandidate, f3, hq1, hq2, hq3]
  have heq4 : ∀ z : ℝ × ℝ, z ∈ Q4 → DyuCandidate p z.1 z.2 = f4 z := by
    intro z hz4
    by_cases hz1 : z ∈ Q1
    · exact (heq1 z hz1).trans (h14 z hz1 hz4)
    · by_cases hz2 : z ∈ Q2
      · exact (heq2 z hz2).trans (h24 z hz2 hz4)
      · by_cases hz3 : z ∈ Q3
        · exact (heq3 z hz3).trans (h34 z hz3 hz4)
        · have hq1 : ¬ QuarterPlane z.1 z.2 := by simpa [Q1] using hz1
          have hq2 : ¬ QuarterPlane2 z.1 z.2 := by simpa [Q2] using hz2
          have hq3 : ¬ QuarterPlane3 z.1 z.2 := by simpa [Q3] using hz3
          have hq4 : QuarterPlane4 z.1 z.2 := by simpa [Q4] using hz4
          simp [DyuCandidate, f4, hq1, hq2, hq3, hq4]
  have hc1 : ContinuousOn (fun z : ℝ × ℝ => DyuCandidate p z.1 z.2) Q1 := by
    apply ContinuousOn.congr hcont1
    intro z hz
    simpa using heq1 z hz
  have hc2 : ContinuousOn (fun z : ℝ × ℝ => DyuCandidate p z.1 z.2) Q2 := by
    apply ContinuousOn.congr hcont2
    intro z hz
    simpa using heq2 z hz
  have hc3 : ContinuousOn (fun z : ℝ × ℝ => DyuCandidate p z.1 z.2) Q3 := by
    apply ContinuousOn.congr hcont3
    intro z hz
    simpa using heq3 z hz
  have hc4 : ContinuousOn (fun z : ℝ × ℝ => DyuCandidate p z.1 z.2) Q4 := by
    apply ContinuousOn.congr hcont4
    intro z hz
    simpa using heq4 z hz
  have hcover : Set.univ ⊆ Q1 ∪ Q2 ∪ Q3 ∪ Q4 := by
    intro z _
    rcases z with ⟨x, y⟩
    by_cases hxy : |x| ≤ |y|
    · by_cases hy : 0 ≤ y
      · have habs : |x| ≤ y := by simpa [abs_of_nonneg hy] using hxy
        rcases abs_le.mp habs with ⟨h1, h2⟩
        exact Or.inl (Or.inr ⟨hy, h1, h2⟩)
      · have hy' : y < 0 := lt_of_not_ge hy
        have habs : |x| ≤ -y := by simpa [abs_of_neg hy'] using hxy
        rcases abs_le.mp habs with ⟨h1, h2⟩
        have h1' : y ≤ x := by simpa using h1
        exact Or.inr ⟨le_of_lt hy', h1', h2⟩
    · have hyx : |y| ≤ |x| := le_of_lt (not_le.mp hxy)
      by_cases hx : 0 ≤ x
      · have habs : |y| ≤ x := by simpa [abs_of_nonneg hx] using hyx
        rcases abs_le.mp habs with ⟨h1, h2⟩
        exact Or.inl (Or.inl (Or.inl ⟨hx, h2, h1⟩))
      · have hx' : x < 0 := lt_of_not_ge hx
        have habs : |y| ≤ -x := by simpa [abs_of_neg hx'] using hyx
        rcases abs_le.mp habs with ⟨h1, h2⟩
        have h1' : x ≤ y := by simpa using h1
        exact Or.inl (Or.inl (Or.inr ⟨le_of_lt hx', h2, h1'⟩))
  have hc12 := hc1.union_of_isClosed hc2 hcl1 hcl2
  have hcl12 : IsClosed (Q1 ∪ Q2) := hcl1.union hcl2
  have hc123 := hc12.union_of_isClosed hc3 hcl12 hcl3
  have hcl123 : IsClosed (Q1 ∪ Q2 ∪ Q3) := hcl12.union hcl3
  have hc1234 := hc123.union_of_isClosed hc4 hcl123 hcl4
  exact ContinuousOn.mono hc1234 hcover
/-- For p > 2, DxuCandidate p x y is continuous in (x, y) on all of ℝ².  -/
lemma continuous_firstPartials_uCandidate (p : ℝ) (hp : 2 < p) :
    ContinuousOn (fun z : ℝ × ℝ => DxuCandidate p z.1 z.2) Set.univ ∧
    ContinuousOn (fun z : ℝ × ℝ => DyuCandidate p z.1 z.2) Set.univ := by
  exact ⟨continuousDxuCandidate p hp, continuousDyuCandidate p hp⟩

lemma axis_tangent_inequality_of_coordinate_tangents
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

lemma uCandidate_axis_tangent_inequality_of_coordinate_tangents
    (p : ℝ)
    (hx_tangent :
      ∀ x y h,
        uCandidate p (x + h) y ≤
          uCandidate p x y + DxuCandidate p x y * h)
    (hy_tangent :
      ∀ x y k,
        uCandidate p x (y + k) ≤
          uCandidate p x y + DyuCandidate p x y * k)
    (x y h k : ℝ) (hk : h * k = 0) :
    uCandidate p (x + h) (y + k) ≤
      uCandidate p x y + DxuCandidate p x y * h + DyuCandidate p x y * k := by
  exact axis_tangent_inequality_of_coordinate_tangents
    (uCandidate p) (DxuCandidate p) (DyuCandidate p)
    hx_tangent hy_tangent x y h k hk

/-- The displayed axis-tangent inequality for `uCandidate` when the increment is
supported on one coordinate. -/
lemma uCandidate_axis_tangent_inequality
    (p x y h k : ℝ) (hk : h * k = 0)
    (hx_tangent :
      uCandidate p (x + h) y ≤
        uCandidate p x y + DxuCandidate p x y * h)
    (hy_tangent :
      uCandidate p x (y + k) ≤
        uCandidate p x y + DyuCandidate p x y * k) :
    uCandidate p (x + h) (y + k) ≤
      uCandidate p x y + DxuCandidate p x y * h + DyuCandidate p x y * k := by
  rcases mul_eq_zero.mp hk with hh | hk'
  · subst h
    simpa [add_assoc] using hy_tangent
  · subst k
    simpa [add_assoc] using hx_tangent

lemma tangent_glue_two_forward
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

lemma tangent_glue_two_backward
    (f d : ℝ → ℝ) {x m z : ℝ}
    (hz_m : z ≤ m) (_hmx : m ≤ x)
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

lemma tangent_glue_three_forward
    (f d : ℝ → ℝ) {x m n z : ℝ}
    (hxm : x ≤ m) (hmn : m ≤ n) (hnz : n ≤ z)
    (hxm_tangent : f m ≤ f x + d x * (m - x))
    (hmn_tangent : f n ≤ f m + d m * (n - m))
    (hnz_tangent : f z ≤ f n + d n * (z - n))
    (hd_mx : d m ≤ d x) (hd_nx : d n ≤ d x) :
    f z ≤ f x + d x * (z - x) := by
  have hxz : x ≤ n := le_trans hxm hmn
  have hxn_tangent : f n ≤ f x + d x * (n - x) :=
    tangent_glue_two_forward f d hxm hmn hxm_tangent hmn_tangent hd_mx
  exact tangent_glue_two_forward f d hxz hnz hxn_tangent hnz_tangent hd_nx

lemma tangent_glue_three_backward
    (f d : ℝ → ℝ) {x m n z : ℝ}
    (hzn : z ≤ n) (hnm : n ≤ m) (hmx : m ≤ x)
    (hxm_tangent : f m ≤ f x + d x * (m - x))
    (hmn_tangent : f n ≤ f m + d m * (n - m))
    (hnz_tangent : f z ≤ f n + d n * (z - n))
    (hd_xm : d x ≤ d m) (hd_xn : d x ≤ d n) :
    f z ≤ f x + d x * (z - x) := by
  have hnx : n ≤ x := le_trans hnm hmx
  have hxn_tangent : f n ≤ f x + d x * (n - x) :=
    tangent_glue_two_backward f d hnm hmx hxm_tangent hmn_tangent hd_xm
  exact tangent_glue_two_backward f d hzn hnx hxn_tangent hnz_tangent hd_xn

lemma concave_tangent_inequality_of_hasDerivAt
    {f : ℝ → ℝ} {x f' : ℝ}
    (hf : ConcaveOn ℝ Set.univ f) (hderiv : HasDerivAt f f' x) (h : ℝ) :
    f (x + h) ≤ f x + f' * h := by
  rcases lt_trichotomy h 0 with hneg | hzero | hpos
  · have hxy : x + h < x := by linarith
    have hslope : f' ≤ slope f (x + h) x :=
      hf.le_slope_of_hasDerivAt (Set.mem_univ _) (Set.mem_univ _) hxy hderiv
    have hslope' : f' ≤ (f x - f (x + h)) / (x - (x + h)) := by
      simpa [slope_def_field] using hslope
    have hden_pos : 0 < x - (x + h) := by linarith
    have hmul := mul_le_mul_of_nonneg_right hslope' hden_pos.le
    field_simp [hden_pos.ne'] at hmul
    linarith
  · subst h
    simp
  · have hxy : x < x + h := by linarith
    have hslope : slope f x (x + h) ≤ f' :=
      hf.slope_le_of_hasDerivAt (Set.mem_univ _) (Set.mem_univ _) hxy hderiv
    have hslope' : (f (x + h) - f x) / ((x + h) - x) ≤ f' := by
      simpa [slope_def_field] using hslope
    have hden_pos : 0 < (x + h) - x := by linarith
    have hmul := mul_le_mul_of_nonneg_right hslope' hden_pos.le
    field_simp [hden_pos.ne'] at hmul
    linarith

lemma concaveOn_univ_of_hasDerivAt2_nonpos
    {f f' f'' : ℝ → ℝ}
    (hf : ∀ x, HasDerivAt f (f' x) x)
    (hf' : ∀ x, HasDerivAt f' (f'' x) x)
    (hf''_nonpos : ∀ x, f'' x ≤ 0) :
    ConcaveOn ℝ Set.univ f := by
  have hdiff_all : Differentiable ℝ f := fun x => (hf x).differentiableAt
  have hcont : ContinuousOn f Set.univ :=
    hdiff_all.continuous.continuousOn
  have hdiff : DifferentiableOn ℝ f (interior (Set.univ : Set ℝ)) := by
    intro x _
    exact (hdiff_all x).differentiableWithinAt
  have hanti : AntitoneOn (deriv f) (interior (Set.univ : Set ℝ)) := by
    intro x _ y _ hxy
    rw [(hf x).deriv, (hf y).deriv]
    exact antitone_of_hasDerivAt_nonpos hf' hf''_nonpos hxy
  exact hanti.concaveOn_of_deriv convex_univ hcont hdiff

lemma tangent_inequality_of_hasDerivAt2_nonpos
    {f f' f'' : ℝ → ℝ} {x : ℝ}
    (hf : ∀ x, HasDerivAt f (f' x) x)
    (hf' : ∀ x, HasDerivAt f' (f'' x) x)
    (hf''_nonpos : ∀ x, f'' x ≤ 0) (h : ℝ) :
    f (x + h) ≤ f x + f' x * h := by
  exact concave_tangent_inequality_of_hasDerivAt
    (concaveOn_univ_of_hasDerivAt2_nonpos hf hf' hf''_nonpos) (hf x) h

lemma uCandidate_axis_tangent_inequality_of_concavity
    (p : ℝ)
    (hconc_x : ∀ y, ConcaveOn ℝ Set.univ (fun x => uCandidate p x y))
    (hconc_y : ∀ x, ConcaveOn ℝ Set.univ (fun y => uCandidate p x y))
    (hdx : ∀ x y, HasDerivAt (fun t => uCandidate p t y) (DxuCandidate p x y) x)
    (hdy : ∀ x y, HasDerivAt (fun s => uCandidate p x s) (DyuCandidate p x y) y)
    (x y h k : ℝ) (hk : h * k = 0) :
    uCandidate p (x + h) (y + k) ≤
      uCandidate p x y + DxuCandidate p x y * h + DyuCandidate p x y * k := by
  apply uCandidate_axis_tangent_inequality_of_coordinate_tangents
  · intro x y h
    exact concave_tangent_inequality_of_hasDerivAt (hconc_x y) (hdx x y) h
  · intro x y k
    exact concave_tangent_inequality_of_hasDerivAt (hconc_y x) (hdy x y) k
  · exact hk

lemma uCandidate_axis_tangent_inequality_of_second_derivatives
    (p : ℝ)
    (hdx : ∀ x y, HasDerivAt (fun t => uCandidate p t y) (DxuCandidate p x y) x)
    (hdy : ∀ x y, HasDerivAt (fun s => uCandidate p x s) (DyuCandidate p x y) y)
    (hDxx :
      ∀ y, ∃ Dxx : ℝ → ℝ,
        (∀ x, HasDerivAt (fun t => DxuCandidate p t y) (Dxx x) x) ∧
        ∀ x, Dxx x ≤ 0)
    (hDyy :
      ∀ x, ∃ Dyy : ℝ → ℝ,
        (∀ y, HasDerivAt (fun s => DyuCandidate p x s) (Dyy y) y) ∧
        ∀ y, Dyy y ≤ 0)
    (x y h k : ℝ) (hk : h * k = 0) :
    uCandidate p (x + h) (y + k) ≤
      uCandidate p x y + DxuCandidate p x y * h + DyuCandidate p x y * k := by
  apply uCandidate_axis_tangent_inequality_of_concavity
  · intro y
    rcases hDxx y with ⟨Dxx, hDxx_deriv, hDxx_nonpos⟩
    exact concaveOn_univ_of_hasDerivAt2_nonpos
      (fun x => hdx x y) hDxx_deriv hDxx_nonpos
  · intro x
    rcases hDyy x with ⟨Dyy, hDyy_deriv, hDyy_nonpos⟩
    exact concaveOn_univ_of_hasDerivAt2_nonpos
      (fun y => hdy x y) hDyy_deriv hDyy_nonpos
  · exact hdx
  · exact hdy
  · exact hk


/-- For p ≥ 2, uA1 p x y is linear (hence concave) in y for fixed x. -/
lemma concaveOn_uA1_in_y (p : ℝ) (hp : 2 ≤ p) (x : ℝ) :
    ConcaveOn ℝ Set.univ (fun y => uA1 p x y) := by
  rcases le_or_gt x 0 with hx | hx
  · have h0 : ∀ y, uA1 p x y = 0 := fun y => by simp [uA1, not_lt.mpr hx]
    simp_rw [h0]; exact concaveOn_const _ convex_univ
  · -- uA1 p x y is affine in y: slope = alpha p * x^(p-1) * pStar p / 2 ≥ 0
    have hpStar : pStar p = p := pStar_eq_self_of_two_le p hp
    -- Write uA1 as a + b * y where a, b are constants in y
    let b := alpha p * x ^ (p - 1) * p / 2
    let a := alpha p * x ^ (p - 1) * x - b * x
    have hcoeff : ∀ y, uA1 p x y = a + b * y := by
      intro y
      simp only [uA1, if_pos hx, hpStar, a, b]
      show alpha p * x ^ (p - 1) * (x - p * (x - y) / 2) =
           alpha p * x ^ (p - 1) * x - alpha p * x ^ (p - 1) * p / 2 * x +
           alpha p * x ^ (p - 1) * p / 2 * y
      ring
    have hb_nn : 0 ≤ b := by
      simp only [b]
      apply div_nonneg _ (by norm_num)
      apply mul_nonneg _ (by linarith)
      apply mul_nonneg _ (Real.rpow_nonneg hx.le _)
      simp only [alpha, hpStar]
      exact mul_nonneg (by linarith) (Real.rpow_nonneg (div_nonneg (by linarith) (by linarith)) _)
    simp_rw [hcoeff]
    exact (concaveOn_const a convex_univ).add
      ((concaveOn_id convex_univ).smul hb_nn)

/-- For p ≥ 2, uA1 p x y is concave in x on {x | y ≤ x}.
    Note: the domain must be {x | y ≤ x}, not {x | 0 ≤ x} — for y > 0 the second
    derivative f''(x) = αp·p·(p-1)·(p-2)/2·x^(p-3)·(y-x) is positive when x < y. -/

lemma deriv_uA1_eq_DxuA1Fun_on_A1 (p : ℝ) (hp : 2 ≤ p) (x y : ℝ) (hA1 : A1 p x y) :
    deriv (fun t => uA1 p t y) x = DxuA1Fun p (x, y) := by
  rcases hA1 with ⟨hx, -, -⟩
  have hpStar : pStar p = p := pStar_eq_self_of_two_le p hp

  let g : ℝ → ℝ := fun t =>
    alpha p * ((1 - p / 2) * t ^ p + (p * y / 2) * t ^ (p - 1))

  have hEq : (fun t => uA1 p t y) =ᶠ[nhds x] g := by
    filter_upwards [Ioi_mem_nhds hx] with t ht
    have ht0 : 0 < t := by simpa [Set.mem_Ioi] using ht
    have hpow : t ^ p = t ^ (p - 1) * t := by
      calc
        t ^ p = t ^ ((p - 1) + (1 : ℝ)) := by ring_nf
        _ = t ^ (p - 1) * t ^ (1 : ℝ) := by rw [Real.rpow_add ht0]
        _ = t ^ (p - 1) * t := by rw [Real.rpow_one]
    simp [uA1, g, hpStar, ht0]
    rw [hpow]
    ring

  have hderiv :
      deriv (fun t => uA1 p t y) x = deriv g x := hEq.deriv_eq

  have hxne : x ≠ 0 := by linarith
  have hg :
      deriv g x =
        alpha p * (p / 2) * x ^ (p - 2) * ((2 - p) * x + (p - 1) * y) := by
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
            ((1 - p / 2) * (p * x ^ (p - 1)) +
              (p * y / 2) * ((p - 1) * x ^ (p - 2)))) x := by
      dsimp [g]
      have hsum :=
        ((hd1.const_mul (1 - p / 2)).add (hd2.const_mul (p * y / 2))).const_mul (alpha p)
      simpa [mul_add, mul_assoc, mul_left_comm, mul_comm] using hsum

    have hpow : x ^ (p - 1) = x ^ (p - 2) * x := by
      calc
        x ^ (p - 1) = x ^ ((p - 2) + (1 : ℝ)) := by ring_nf
        _ = x ^ (p - 2) * x ^ (1 : ℝ) := by rw [Real.rpow_add hx]
        _ = x ^ (p - 2) * x := by rw [Real.rpow_one]

    calc
      deriv g x
          = alpha p *
              ((1 - p / 2) * (p * x ^ (p - 1)) +
                (p * y / 2) * ((p - 1) * x ^ (p - 2))) := hd.deriv
      _ = alpha p *
            ((1 - p / 2) * (p * (x ^ (p - 2) * x)) +
              (p * y / 2) * ((p - 1) * x ^ (p - 2))) := by rw [hpow]
      _ = alpha p * (p / 2) * x ^ (p - 2) * ((2 - p) * x + (p - 1) * y) := by
          ring_nf

  calc
    deriv (fun t => uA1 p t y) x = deriv g x := hderiv
    _ = alpha p * (p / 2) * x ^ (p - 2) * ((2 - p) * x + (p - 1) * y) := hg
    _ = DxuA1Fun p (x, y) := by simp [DxuA1Fun, DxuA1, hx]

lemma hasDerivAt_uA1_x_of_pos (p : ℝ) (hp : 2 ≤ p) (x y : ℝ) (hx : 0 < x) :
    HasDerivAt (fun t => uA1 p t y) (DxuA1Fun p (x, y)) x := by
  have hpStar : pStar p = p := pStar_eq_self_of_two_le p hp

  let g : ℝ → ℝ := fun t =>
    alpha p * ((1 - p / 2) * t ^ p + (p * y / 2) * t ^ (p - 1))

  have hEq : (fun t => uA1 p t y) =ᶠ[nhds x] g := by
    filter_upwards [Ioi_mem_nhds hx] with t ht
    have ht0 : 0 < t := by simpa [Set.mem_Ioi] using ht
    have hpow : t ^ p = t ^ (p - 1) * t := by
      calc
        t ^ p = t ^ ((p - 1) + (1 : ℝ)) := by ring_nf
        _ = t ^ (p - 1) * t ^ (1 : ℝ) := by rw [Real.rpow_add ht0]
        _ = t ^ (p - 1) * t := by rw [Real.rpow_one]
    simp [uA1, g, hpStar, ht0]
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
          ((1 - p / 2) * (p * x ^ (p - 1)) +
            (p * y / 2) * ((p - 1) * x ^ (p - 2)))) x := by
    dsimp [g]
    have hsum :=
      ((hd1.const_mul (1 - p / 2)).add (hd2.const_mul (p * y / 2))).const_mul (alpha p)
    simpa [mul_add, mul_assoc, mul_left_comm, mul_comm] using hsum

  have hpow : x ^ (p - 1) = x ^ (p - 2) * x := by
    calc
      x ^ (p - 1) = x ^ ((p - 2) + (1 : ℝ)) := by ring_nf
      _ = x ^ (p - 2) * x ^ (1 : ℝ) := by rw [Real.rpow_add hx]
      _ = x ^ (p - 2) * x := by rw [Real.rpow_one]

  have hg :
      HasDerivAt g
        (alpha p * (p / 2) * x ^ (p - 2) * ((2 - p) * x + (p - 1) * y)) x := by
    refine hd.congr_deriv ?_
    calc
      alpha p *
          ((1 - p / 2) * (p * x ^ (p - 1)) +
            (p * y / 2) * ((p - 1) * x ^ (p - 2)))
        = alpha p *
            ((1 - p / 2) * (p * (x ^ (p - 2) * x)) +
              (p * y / 2) * ((p - 1) * x ^ (p - 2))) := by rw [hpow]
      _ = alpha p * (p / 2) * x ^ (p - 2) * ((2 - p) * x + (p - 1) * y) := by ring_nf

  refine (hg.congr_of_eventuallyEq hEq).congr_deriv ?_
  simp [DxuA1Fun, DxuA1, hx]

lemma Dxx_uA1_nonpos (p : ℝ) (hp : 2 ≤ p) (x y : ℝ) (hA1 : A1 p x y)
    : 0 ≥ deriv (deriv (fun x => uA1 p x y)) x := by
  rcases hA1 with ⟨hx, hax, hyx⟩

  let g : ℝ → ℝ := fun t =>
    alpha p * ((1 - p / 2) * t ^ p + (p * y / 2) * t ^ (p - 1))

  have hEq : (fun t => uA1 p t y) =ᶠ[nhds x] g := by
    filter_upwards [Ioi_mem_nhds hx] with t ht
    have ht0 : 0 < t := by simpa [Set.mem_Ioi] using ht
    have hpow : t ^ p = t ^ (p - 1) * t := by
      calc
        t ^ p = t ^ ((p - 1) + (1 : ℝ)) := by ring_nf
        _ = t ^ (p - 1) * t ^ (1 : ℝ) := by rw [Real.rpow_add ht0]
        _ = t ^ (p - 1) * t := by rw [Real.rpow_one]
    simp [uA1, g, pStar_eq_self_of_two_le p hp, ht0]
    rw [hpow]
    ring

  have hderiv2 :
      deriv (deriv (fun t => uA1 p t y)) x = deriv (deriv g) x := by
    exact hEq.deriv.deriv_eq

  have hxne : x ≠ 0 := by linarith
  have hp_ge1 : 1 ≤ p := by linarith
  have hp1_ge1 : 1 ≤ p - 1 := by linarith

  have hg1_formula :
      deriv g x =
        alpha p *
          ((1 - p / 2) * (p * x ^ (p - 1)) +
            (p * y / 2) * ((p - 1) * x ^ (p - 2))) := by
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
      simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc, show p + (-1 + -1) = p + -2 by ring] using h

    have hd :
        HasDerivAt g
          (alpha p *
            ((1 - p / 2) * (p * x ^ (p - 1)) +
              (p * y / 2) * ((p - 1) * x ^ (p - 2)))) x := by
      dsimp [g]
      have h :=
        ((hd1.const_mul (1 - p / 2)).add (hd2.const_mul (p * y / 2))).const_mul (alpha p)
      simpa [mul_assoc, mul_left_comm, mul_comm] using h

    exact hd.deriv

  have hg2 :
      deriv (deriv g) x =
        -(alpha p * p * (p - 1) * (p - 2) * x ^ (p - 3) * (x - y) / 2) := by
    have hxne2 : x ≠ 0 ∨ 1 ≤ p - 1 := Or.inl hxne
    have hxne3 : x ≠ 0 ∨ 1 ≤ p - 2 := Or.inl hxne

    have hd1 :
        HasDerivAt (fun t : ℝ => t ^ (p - 1)) ((p - 1) * x ^ (p - 2)) x := by
      have h := (Real.hasDerivAt_rpow_const hxne2 :
        HasDerivAt (fun t : ℝ => t ^ (p - 1))
          ((p - 1) * x ^ ((p - 1) - 1)) x)
      simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc, show p + (-1 + -1) = p + -2 by ring] using h

    have hd2 :
        HasDerivAt (fun t : ℝ => t ^ (p - 2)) ((p - 2) * x ^ (p - 3)) x := by
      have h := (Real.hasDerivAt_rpow_const hxne3 :
        HasDerivAt (fun t : ℝ => t ^ (p - 2))
          ((p - 2) * x ^ ((p - 2) - 1)) x)
      simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc, show p + (-1 + -2) = p + -3 by ring] using h

    have hd :
        HasDerivAt
          (fun t =>
            alpha p *
              ((1 - p / 2) * (p * t ^ (p - 1)) +
                (p * y / 2) * ((p - 1) * t ^ (p - 2))))
          (alpha p *
            ((1 - p / 2) * (p * ((p - 1) * x ^ (p - 2))) +
              (p * y / 2) * ((p - 1) * ((p - 2) * x ^ (p - 3))))) x := by
      have h_deriv_combined :
          HasDerivAt
            (fun t =>
              alpha p *
                (p * (1 - p / 2) * t ^ (p - 1) +
                  (p * y / 2 * (p - 1)) * t ^ (p - 2)))
            (alpha p *
              (p * (1 - p / 2) * ((p - 1) * x ^ (p - 2)) +
                (p * y / 2 * (p - 1)) * ((p - 2) * x ^ (p - 3)))) x := by
        exact
          ((hd1.const_mul (p * (1 - p / 2))).add
            (hd2.const_mul (p * y / 2 * (p - 1)))).const_mul (alpha p)
      simpa [mul_assoc, mul_left_comm, mul_comm, add_assoc, add_left_comm, add_comm] using
        h_deriv_combined

    have hfun :
        deriv g =
          fun t =>
            alpha p *
              ((1 - p / 2) * (p * t ^ (p - 1)) +
                (p * y / 2) * ((p - 1) * t ^ (p - 2))) := by
      funext t
      have hp_t : t ≠ 0 ∨ 1 ≤ p := Or.inr hp_ge1
      have hp1_t : t ≠ 0 ∨ 1 ≤ p - 1 := Or.inr hp1_ge1

      have hd1t :
          HasDerivAt (fun s : ℝ => s ^ p) (p * t ^ (p - 1)) t := by
        simpa using
          (Real.hasDerivAt_rpow_const hp_t :
            HasDerivAt (fun s : ℝ => s ^ p) (p * t ^ (p - 1)) t)

      have hd2t :
          HasDerivAt (fun s : ℝ => s ^ (p - 1)) ((p - 1) * t ^ (p - 2)) t := by
        have h := (Real.hasDerivAt_rpow_const hp1_t :
          HasDerivAt (fun s : ℝ => s ^ (p - 1))
            ((p - 1) * t ^ ((p - 1) - 1)) t)
        simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc, show p + (-1 + -1) = p + -2 by ring] using h

      have hdt :
          HasDerivAt g
            (alpha p *
              ((1 - p / 2) * (p * t ^ (p - 1)) +
                (p * y / 2) * ((p - 1) * t ^ (p - 2)))) t := by
        dsimp [g]
        have h :=
          ((hd1t.const_mul (1 - p / 2)).add
            (hd2t.const_mul (p * y / 2))).const_mul (alpha p)
        simpa using h

      exact hdt.deriv

    rw [hfun]
    rw [hd.deriv]
    have hx_pos : (0 : ℝ) < x := hx
    have hshift : x ^ (p - 3) * x = x ^ (p - 2) := by
      nth_rewrite 2 [← Real.rpow_one x]
      rw [← Real.rpow_add hx_pos (p - 3) 1]
      congr 1
      ring
    have hshift' : x ^ (p - 2) = x ^ (p - 3) * x := by
      simpa [eq_comm] using hshift
    rw [hshift']
    ring

  rw [hderiv2, hg2]

  have hα : 0 ≤ alpha p := by
    rw [alpha, pStar_eq_self_of_two_le p hp]
    apply mul_nonneg
    · linarith
    · apply Real.rpow_nonneg
      apply div_nonneg <;> linarith

  have hp0 : 0 ≤ p := by linarith
  have hp1 : 0 ≤ p - 1 := by linarith
  have hp2 : 0 ≤ p - 2 := by linarith
  have hpow : 0 ≤ x ^ (p - 3) := by
    exact Real.rpow_nonneg hx.le _
  have hxy : 0 ≤ x - y := by
    linarith

  have hnonneg :
      0 ≤ alpha p * p * (p - 1) * (p - 2) * x ^ (p - 3) * (x - y) / 2 := by
    apply div_nonneg
    · exact mul_nonneg
        (mul_nonneg
          (mul_nonneg
            (mul_nonneg
              (mul_nonneg hα hp0)
              hp1)
            hp2)
          hpow)
        hxy
    · norm_num

  linarith

lemma Dyy_uA1_nonpos (p : ℝ) (_hp : 2 ≤ p) (x y : ℝ) (hA1 : A1 p x y)
    : 0 ≥ deriv (deriv (fun y => uA1 p x y)) y := by
  rcases hA1 with ⟨hx, -, -⟩
  let c : ℝ := alpha p * x ^ (p - 1) * (x - pStar p * x / 2)
  let m : ℝ := alpha p * x ^ (p - 1) * (pStar p / 2)

  have hrepr : (fun t => uA1 p x t) = fun t => c + m * t := by
    funext t
    simp [uA1, hx, c, m]
    ring

  rw [hrepr]

  have hderiv_lin : deriv (fun t => c + m * t) = fun _ => m := by
    funext t
    have hlin : HasDerivAt (fun s : ℝ => c + m * s) m t := by
      simpa [one_mul] using (((hasDerivAt_id t).const_mul m).const_add c)
    exact hlin.deriv

  rw [hderiv_lin]
  simp

lemma deriv_uA1_eq_DyuA1Fun_on_A1 (p : ℝ) (hp : 2 < p) (x y : ℝ) (hA1 : A1 p x y) :
    deriv (fun s => uA1 p x s) y = DyuA1Fun p (x, y) := by
  rcases hA1 with ⟨hx, -, -⟩
  have hp' : 2 ≤ p := by linarith
  have hpStar : pStar p = p := pStar_eq_self_of_two_le p hp'
  let c : ℝ := alpha p * x ^ (p - 1) * (x - pStar p * x / 2)
  let m : ℝ := alpha p * x ^ (p - 1) * (pStar p / 2)

  have hrepr : (fun s => uA1 p x s) = fun s => c + m * s := by
    funext s
    simp [uA1, hx, c, m]
    ring

  have hderiv_lin : deriv (fun s => c + m * s) = fun _ => m := by
    funext s
    have hlin : HasDerivAt (fun z : ℝ => c + m * z) m s := by
      simpa [one_mul] using (((hasDerivAt_id s).const_mul m).const_add c)
    exact hlin.deriv

  calc
    deriv (fun s => uA1 p x s) y = deriv (fun s => c + m * s) y := by rw [hrepr]
    _ = m := by rw [hderiv_lin]
    _ = DyuA1Fun p (x, y) := by
        simp [DyuA1Fun, DyuA1, m, hx, hpStar]

lemma hasDerivAt_uA1_y_of_pos (p : ℝ) (hp : 2 ≤ p) (x y : ℝ) (hx : 0 < x) :
    HasDerivAt (fun s => uA1 p x s) (DyuA1Fun p (x, y)) y := by
  have hpStar : pStar p = p := pStar_eq_self_of_two_le p hp
  let c : ℝ := alpha p * x ^ (p - 1) * (x - pStar p * x / 2)
  let m : ℝ := alpha p * x ^ (p - 1) * (pStar p / 2)

  have hrepr : (fun s => uA1 p x s) = fun s => c + m * s := by
    funext s
    simp [uA1, hx, c, m]
    ring

  have hderiv_lin : HasDerivAt (fun s => c + m * s) m y := by
    simpa [one_mul] using (((hasDerivAt_id y).const_mul m).const_add c)

  rw [hrepr]
  convert hderiv_lin using 1
  simp [DyuA1Fun, DyuA1, m, hx, hpStar]

  lemma Dxy_uA1_nonneg (p : ℝ) (hp : 2 ≤ p) (x y : ℝ) (hA1 : A1 p x y) :
    0 ≤ deriv (fun x => deriv (fun y => uA1 p x y) y) x := by
    rcases hA1 with ⟨hx, -, -⟩
    have hpStar : pStar p = p := pStar_eq_self_of_two_le p hp

    let g : ℝ → ℝ := fun t => alpha p * (p / 2) * t ^ (p - 1)

    have hEq :
        (fun t => deriv (fun y => uA1 p t y) y) =ᶠ[nhds x] g := by
      filter_upwards [Ioi_mem_nhds hx] with t ht
      have ht0 : 0 < t := by simpa [Set.mem_Ioi] using ht
      let c : ℝ := alpha p * t ^ (p - 1) * (t - pStar p * t / 2)
      let m : ℝ := alpha p * t ^ (p - 1) * (pStar p / 2)
      have hrepr : (fun s => uA1 p t s) = fun s => c + m * s := by
        funext s
        simp [uA1, ht0, c, m]
        ring
      have hderiv_lin : deriv (fun s => c + m * s) = fun _ => m := by
        funext s
        have hlin : HasDerivAt (fun z : ℝ => c + m * z) m s := by
          simpa [one_mul] using (((hasDerivAt_id s).const_mul m).const_add c)
        exact hlin.deriv
      calc
        deriv (fun y => uA1 p t y) y = deriv (fun s => c + m * s) y := by rw [hrepr]
        _ = m := by rw [hderiv_lin]
        _ = g t := by
          simp [g, m, hpStar]; ring

    have hderiv_outer :
        deriv (fun x => deriv (fun y => uA1 p x y) y) x = deriv g x :=
      hEq.deriv_eq

    have hxne : x ≠ 0 := by linarith
    have hg :
        deriv g x = alpha p * (p / 2) * ((p - 1) * x ^ (p - 2)) := by
      have hxne1 : x ≠ 0 ∨ 1 ≤ p - 1 := Or.inl hxne
      have hrpow :
          HasDerivAt (fun t : ℝ => t ^ (p - 1)) ((p - 1) * x ^ (p - 2)) x := by
        have h := (Real.hasDerivAt_rpow_const hxne1 :
          HasDerivAt (fun t : ℝ => t ^ (p - 1))
            ((p - 1) * x ^ ((p - 1) - 1)) x)
        simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm,
          show p + (-1 + -1) = p + -2 by ring] using h
      have hg' :
          HasDerivAt g (alpha p * (p / 2) * ((p - 1) * x ^ (p - 2))) x := by
        simpa [g, mul_assoc, mul_left_comm, mul_comm] using
          (hrpow.const_mul (alpha p * (p / 2)))
      exact hg'.deriv

    rw [hderiv_outer, hg]

    have hα : 0 ≤ alpha p := by
      rw [alpha, hpStar]
      apply mul_nonneg
      · linarith
      · apply Real.rpow_nonneg
        apply div_nonneg <;> linarith
    have hp0 : 0 ≤ p / 2 := by linarith
    have hp1 : 0 ≤ p - 1 := by linarith
    have hpow : 0 ≤ x ^ (p - 2) := Real.rpow_nonneg hx.le _

    exact mul_nonneg
      (mul_nonneg hα hp0)
      (mul_nonneg hp1 hpow)

lemma deriv_vGeTwo_eq_DxvGeTwo_on_A2 (p : ℝ) (hp : 2 ≤ p) (x y : ℝ) (hA2 : A2 p x y) :
    deriv (fun t => vGeTwo p t y) x = DxvGeTwo p x y := by
  rcases hA2 with ⟨hx, hneg, hay⟩
  have hp1 : 1 ≤ p := by linarith
  have hyx : y < x := by
    rw [a, pStar_eq_self_of_two_le p hp] at hay
    have hp0 : 0 < p := by linarith
    have hcoeff : 1 - 2 / p < (1 : ℝ) := by
      have hdiv : 0 < 2 / p := by positivity
      linarith
    have hax_lt_x : (1 - 2 / p) * x < x := by
      simpa using mul_lt_mul_of_pos_right hcoeff hx
    linarith
  have hsum : 0 < (x + y) / 2 := by linarith
  have hdiff : 0 < (x - y) / 2 := by linarith

  let g : ℝ → ℝ := fun t =>
    ((t + y) / 2) ^ p - (p - 1) ^ p * (((t - y) / 2) ^ p)

  have hsum_nhds : {t : ℝ | 0 < (t + y) / 2} ∈ nhds x := by
    exact ((((continuous_id'.add continuous_const).div_const 2).continuousAt).preimage_mem_nhds
      (Ioi_mem_nhds hsum))
  have hdiff_nhds : {t : ℝ | 0 < (t - y) / 2} ∈ nhds x := by
    exact ((((continuous_id'.sub continuous_const).div_const 2).continuousAt).preimage_mem_nhds
      (Ioi_mem_nhds hdiff))

  have hEq : (fun t => vGeTwo p t y) =ᶠ[nhds x] g := by
    filter_upwards [hsum_nhds, hdiff_nhds] with t ht_sum ht_diff
    simp [vGeTwo, g, abs_of_pos ht_sum, abs_of_pos ht_diff]

  have hderiv :
      deriv (fun t => vGeTwo p t y) x = deriv g x := hEq.deriv_eq

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

  have hg :
      deriv g x =
        ((x + y) / 2) ^ (p - 1) * (p / 2) -
          (p - 1) ^ p * (((x - y) / 2) ^ (p - 1)) * (p / 2) := by
    have hd :
        HasDerivAt g
          (p * (((x + y) / 2) ^ (p - 1)) * (1 / 2) -
            (p - 1) ^ p * (p * (((x - y) / 2) ^ (p - 1)) * (1 / 2))) x := by
      dsimp [g]
      exact hpow_sum.sub (hpow_diff.const_mul ((p - 1) ^ p))
    calc
      deriv g x
          = p * (((x + y) / 2) ^ (p - 1)) * (1 / 2) -
              (p - 1) ^ p * (p * (((x - y) / 2) ^ (p - 1)) * (1 / 2)) := hd.deriv
      _ = ((x + y) / 2) ^ (p - 1) * (p / 2) -
            (p - 1) ^ p * (((x - y) / 2) ^ (p - 1)) * (p / 2) := by ring

  calc
    deriv (fun t => vGeTwo p t y) x = deriv g x := hderiv
    _ = ((x + y) / 2) ^ (p - 1) * (p / 2) -
          (p - 1) ^ p * (((x - y) / 2) ^ (p - 1)) * (p / 2) := hg
    _ = DxvGeTwo p x y := by
      simp [DxvGeTwo, hx, abs_of_pos hsum, abs_of_pos hdiff]

lemma hasDerivAt_vGeTwo_x_of_pos (p : ℝ) (hp : 2 ≤ p) (x y : ℝ)
    (hsum : 0 < (x + y) / 2) (hdiff : 0 < (x - y) / 2) :
    HasDerivAt (fun t => vGeTwo p t y) (DxvGeTwo p x y) x := by
  let g : ℝ → ℝ := fun t =>
    ((t + y) / 2) ^ p - (p - 1) ^ p * (((t - y) / 2) ^ p)

  have hsum_nhds : {t : ℝ | 0 < (t + y) / 2} ∈ nhds x := by
    exact ((((continuous_id'.add continuous_const).div_const 2).continuousAt).preimage_mem_nhds
      (Ioi_mem_nhds hsum))
  have hdiff_nhds : {t : ℝ | 0 < (t - y) / 2} ∈ nhds x := by
    exact ((((continuous_id'.sub continuous_const).div_const 2).continuousAt).preimage_mem_nhds
      (Ioi_mem_nhds hdiff))

  have hEq : (fun t => vGeTwo p t y) =ᶠ[nhds x] g := by
    filter_upwards [hsum_nhds, hdiff_nhds] with t ht_sum ht_diff
    simp [vGeTwo, g, abs_of_pos ht_sum, abs_of_pos ht_diff]

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
          (p - 1) ^ p * (((x - y) / 2) ^ (p - 1)) * (p / 2)) x := by
    have htmp :
        HasDerivAt g
          (p * (((x + y) / 2) ^ (p - 1)) * (1 / 2) -
            (p - 1) ^ p * (p * (((x - y) / 2) ^ (p - 1)) * (1 / 2))) x := by
      dsimp [g]
      exact hpow_sum.sub (hpow_diff.const_mul ((p - 1) ^ p))
    refine htmp.congr_deriv ?_
    ring

  have hx : 0 < x := by linarith
  refine (hd.congr_of_eventuallyEq hEq).congr_deriv ?_
  simp [DxvGeTwo, hx, abs_of_pos hsum, abs_of_pos hdiff]

lemma deriv_vGeTwo_eq_DyvGeTwo_on_A2 (p : ℝ) (hp : 2 ≤ p) (x y : ℝ) (hA2 : A2 p x y) :
    deriv (fun s => vGeTwo p x s) y = DyvGeTwo p x y := by
  rcases hA2 with ⟨hx, hneg, hay⟩
  have hp1 : 1 ≤ p := by linarith
  have hyx : y < x := by
    rw [a, pStar_eq_self_of_two_le p hp] at hay
    have hp0 : 0 < p := by linarith
    have hcoeff : 1 - 2 / p < (1 : ℝ) := by
      have hdiv : 0 < 2 / p := by positivity
      linarith
    have hax_lt_x : (1 - 2 / p) * x < x := by
      simpa using mul_lt_mul_of_pos_right hcoeff hx
    linarith
  have hsum : 0 < (x + y) / 2 := by linarith
  have hdiff : 0 < (x - y) / 2 := by linarith

  let g : ℝ → ℝ := fun s =>
    ((x + s) / 2) ^ p - (p - 1) ^ p * (((x - s) / 2) ^ p)

  have hsum_nhds : {s : ℝ | 0 < (x + s) / 2} ∈ nhds y := by
    exact ((((continuous_const.add continuous_id').div_const 2).continuousAt).preimage_mem_nhds
      (Ioi_mem_nhds hsum))
  have hdiff_nhds : {s : ℝ | 0 < (x - s) / 2} ∈ nhds y := by
    exact ((((continuous_const.sub continuous_id').div_const 2).continuousAt).preimage_mem_nhds
      (Ioi_mem_nhds hdiff))

  have hEq : (fun s => vGeTwo p x s) =ᶠ[nhds y] g := by
    filter_upwards [hsum_nhds, hdiff_nhds] with s hs_sum hs_diff
    simp [vGeTwo, g, abs_of_pos hs_sum, abs_of_pos hs_diff]

  have hderiv :
      deriv (fun s => vGeTwo p x s) y = deriv g y := hEq.deriv_eq

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

  have hg :
      deriv g y =
        ((x + y) / 2) ^ (p - 1) * (p / 2) +
          (p - 1) ^ p * (((x - y) / 2) ^ (p - 1)) * (p / 2) := by
    have hd :
        HasDerivAt g
          (p * (((x + y) / 2) ^ (p - 1)) * (1 / 2) -
            (p - 1) ^ p * (p * (((x - y) / 2) ^ (p - 1)) * (-(1 / 2)))) y := by
      dsimp [g]
      exact hpow_sum.sub (hpow_diff.const_mul ((p - 1) ^ p))
    calc
      deriv g y
          = p * (((x + y) / 2) ^ (p - 1)) * (1 / 2) -
              (p - 1) ^ p * (p * (((x - y) / 2) ^ (p - 1)) * (-(1 / 2))) := hd.deriv
      _ = ((x + y) / 2) ^ (p - 1) * (p / 2) +
            (p - 1) ^ p * (((x - y) / 2) ^ (p - 1)) * (p / 2) := by ring

  calc
    deriv (fun s => vGeTwo p x s) y = deriv g y := hderiv
    _ = ((x + y) / 2) ^ (p - 1) * (p / 2) +
          (p - 1) ^ p * (((x - y) / 2) ^ (p - 1)) * (p / 2) := hg
    _ = DyvGeTwo p x y := by
      simp [DyvGeTwo, hx, abs_of_pos hsum, abs_of_pos hdiff]

lemma hasDerivAt_vGeTwo_y_of_pos (p : ℝ) (hp : 2 ≤ p) (x y : ℝ)
    (hsum : 0 < (x + y) / 2) (hdiff : 0 < (x - y) / 2) :
    HasDerivAt (fun s => vGeTwo p x s) (DyvGeTwo p x y) y := by
  let g : ℝ → ℝ := fun s =>
    ((x + s) / 2) ^ p - (p - 1) ^ p * (((x - s) / 2) ^ p)

  have hsum_nhds : {s : ℝ | 0 < (x + s) / 2} ∈ nhds y := by
    exact ((((continuous_const.add continuous_id').div_const 2).continuousAt).preimage_mem_nhds
      (Ioi_mem_nhds hsum))
  have hdiff_nhds : {s : ℝ | 0 < (x - s) / 2} ∈ nhds y := by
    exact ((((continuous_const.sub continuous_id').div_const 2).continuousAt).preimage_mem_nhds
      (Ioi_mem_nhds hdiff))

  have hEq : (fun s => vGeTwo p x s) =ᶠ[nhds y] g := by
    filter_upwards [hsum_nhds, hdiff_nhds] with s hs_sum hs_diff
    simp [vGeTwo, g, abs_of_pos hs_sum, abs_of_pos hs_diff]

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
          (p - 1) ^ p * (((x - y) / 2) ^ (p - 1)) * (p / 2)) y := by
    have htmp :
        HasDerivAt g
          (p * (((x + y) / 2) ^ (p - 1)) * (1 / 2) -
            (p - 1) ^ p * (p * (((x - y) / 2) ^ (p - 1)) * (-(1 / 2)))) y := by
      dsimp [g]
      exact hpow_sum.sub (hpow_diff.const_mul ((p - 1) ^ p))
    refine htmp.congr_deriv ?_
    ring

  have hx : 0 < x := by linarith
  refine (hd.congr_of_eventuallyEq hEq).congr_deriv ?_
  simp [DyvGeTwo, hx, abs_of_pos hsum, abs_of_pos hdiff]

lemma hasDerivAt_vGeTwo_x_on_antidiag_pos (p : ℝ) (hp : 2 < p)
    (x : ℝ) (hx : 0 < x) :
    HasDerivAt (fun t => vGeTwo p t (-x)) (DxvGeTwo p x (-x)) x := by
  let g : ℝ → ℝ := fun t =>
    |((t - x) / 2)| ^ p - (p - 1) ^ p * |((t + x) / 2)| ^ p
  have hEq : (fun t => vGeTwo p t (-x)) = g := by
    ext t
    simp [vGeTwo, g, sub_eq_add_neg]
  have hp1 : 1 < p := by linarith
  have hbase_sum :
      HasDerivAt (fun t : ℝ => (t - x) / 2) (1 / 2) x := by
    simpa [sub_eq_add_neg, div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using
      (((hasDerivAt_id x).add_const (-x)).const_mul (1 / 2 : ℝ))
  have hbase_diff :
      HasDerivAt (fun t : ℝ => (t + x) / 2) (1 / 2) x := by
    simpa [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using
      (((hasDerivAt_id x).add_const x).const_mul (1 / 2 : ℝ))
  have hpow_sum :
      HasDerivAt (fun t : ℝ => |((t - x) / 2)| ^ p) 0 x := by
    have h :
        HasDerivAt (fun s : ℝ => |s| ^ p)
          (p * |(x - x) / 2| ^ (p - 2) * ((x - x) / 2)) ((x - x) / 2) :=
      hasDerivAt_abs_rpow ((x - x) / 2) hp1
    have hcomp := h.comp x hbase_sum
    simpa using hcomp
  have hpow_diff :
      HasDerivAt (fun t : ℝ => |((t + x) / 2)| ^ p)
        (p * x ^ (p - 1) * (1 / 2)) x := by
    have h :
        HasDerivAt (fun s : ℝ => |s| ^ p)
          (p * |(x + x) / 2| ^ (p - 2) * ((x + x) / 2)) ((x + x) / 2) :=
      hasDerivAt_abs_rpow ((x + x) / 2) hp1
    have hcomp := h.comp x hbase_diff
    refine hcomp.congr_deriv ?_
    have hpow : x ^ (p - 1) = x ^ (p - 2) * x := by
      calc
        x ^ (p - 1) = x ^ ((p - 2) + (1 : ℝ)) := by ring_nf
        _ = x ^ (p - 2) * x ^ (1 : ℝ) := by rw [Real.rpow_add hx]
        _ = x ^ (p - 2) * x := by rw [Real.rpow_one]
    simp [abs_of_pos hx, hpow]
    ring
  have hd :
      HasDerivAt g
        (-(p - 1) ^ p * (p * x ^ (p - 1) * (1 / 2))) x := by
    have htmp :
        HasDerivAt g
          (0 - (p - 1) ^ p * (p * x ^ (p - 1) * (1 / 2))) x := by
      dsimp [g]
      exact hpow_sum.sub (hpow_diff.const_mul ((p - 1) ^ p))
    simpa using htmp
  rw [hEq]
  refine hd.congr_deriv ?_
  have hp1_ne : p - 1 ≠ 0 := by linarith
  simp [DxvGeTwo, hx, hp1_ne, abs_of_pos hx]
  ring

lemma hasDerivAt_vGeTwo_y_on_antidiag_pos (p : ℝ) (hp : 2 < p)
    (x : ℝ) (hx : 0 < x) :
    HasDerivAt (fun s => vGeTwo p x s) (DyvGeTwo p x (-x)) (-x) := by
  let g : ℝ → ℝ := fun s =>
    |((x + s) / 2)| ^ p - (p - 1) ^ p * |((x - s) / 2)| ^ p
  have hEq : (fun s => vGeTwo p x s) = g := by
    ext s
    rfl
  have hp1 : 1 < p := by linarith
  have hbase_sum :
      HasDerivAt (fun s : ℝ => (x + s) / 2) (1 / 2) (-x) := by
    simpa [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using
      (((hasDerivAt_id (-x)).const_add x).const_mul (1 / 2 : ℝ))
  have hbase_diff :
      HasDerivAt (fun s : ℝ => (x - s) / 2) (-(1 / 2)) (-x) := by
    simpa [sub_eq_add_neg, div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using
      ((((hasDerivAt_id (-x)).neg).const_add x).const_mul (1 / 2 : ℝ))
  have hpow_sum :
      HasDerivAt (fun s : ℝ => |((x + s) / 2)| ^ p) 0 (-x) := by
    have h :
        HasDerivAt (fun t : ℝ => |t| ^ p)
          (p * |(x + -x) / 2| ^ (p - 2) * ((x + -x) / 2)) ((x + -x) / 2) :=
      hasDerivAt_abs_rpow ((x + -x) / 2) hp1
    have hcomp := h.comp (-x) hbase_sum
    simpa using hcomp
  have hpow_diff :
      HasDerivAt (fun s : ℝ => |((x - s) / 2)| ^ p)
        (p * x ^ (p - 1) * (-(1 / 2))) (-x) := by
    have h :
        HasDerivAt (fun t : ℝ => |t| ^ p)
          (p * |(x - -x) / 2| ^ (p - 2) * ((x - -x) / 2)) ((x - -x) / 2) :=
      hasDerivAt_abs_rpow ((x - -x) / 2) hp1
    have hcomp := h.comp (-x) hbase_diff
    refine hcomp.congr_deriv ?_
    have hpow : x ^ (p - 1) = x ^ (p - 2) * x := by
      calc
        x ^ (p - 1) = x ^ ((p - 2) + (1 : ℝ)) := by ring_nf
        _ = x ^ (p - 2) * x ^ (1 : ℝ) := by rw [Real.rpow_add hx]
        _ = x ^ (p - 2) * x := by rw [Real.rpow_one]
    simp [abs_of_pos hx, hpow]
    ring
  have hd :
      HasDerivAt g
        (-((p - 1) ^ p * (p * x ^ (p - 1) * (-(1 / 2))))) (-x) := by
    have htmp :
        HasDerivAt g
          (0 - (p - 1) ^ p * (p * x ^ (p - 1) * (-(1 / 2)))) (-x) := by
      dsimp [g]
      exact hpow_sum.sub (hpow_diff.const_mul ((p - 1) ^ p))
    simpa using htmp
  rw [hEq]
  refine hd.congr_deriv ?_
  have hp1_ne : p - 1 ≠ 0 := by linarith
  simp [DyvGeTwo, hx, hp1_ne, abs_of_pos hx]
  ring

lemma vGeTwo_A2_second_bracket_nonpos (p : ℝ) (hp : 2 ≤ p)
    (x y : ℝ) (hA2 : A2 p x y) :
    ((x + y) / 2) ^ (p - 2) -
      (p - 1) ^ p * ((x - y) / 2) ^ (p - 2) ≤ 0 := by
  rcases hA2 with ⟨hx, hneg, hay⟩
  have hpStar : pStar p = p := pStar_eq_self_of_two_le p hp
  have hp_pos : 0 < p := by linarith
  have hp1_nonneg : 0 ≤ p - 1 := by linarith
  have hp1_one : 1 ≤ p - 1 := by linarith
  have hp2_nonneg : 0 ≤ p - 2 := by linarith
  have hsum_pos : 0 < (x + y) / 2 := by linarith
  have hdiff_pos : 0 < (x - y) / 2 := by
    have hyx : y < x := by
      rw [a, hpStar] at hay
      have hcoeff : 1 - 2 / p < (1 : ℝ) := by
        have hdiv : 0 < 2 / p := by positivity
        linarith
      have hax_lt_x : (1 - 2 / p) * x < x := by
        simpa using mul_lt_mul_of_pos_right hcoeff hx
      linarith
    linarith
  have hay' : p * y < (p - 2) * x := by
    rw [a, hpStar] at hay
    have h := mul_lt_mul_of_pos_left hay hp_pos
    field_simp [hp_pos.ne] at h
    linarith
  have hAB : (x + y) / 2 ≤ (p - 1) * ((x - y) / 2) := by
    nlinarith [le_of_lt hay']
  have hpow_le :
      ((x + y) / 2) ^ (p - 2) ≤
        ((p - 1) * ((x - y) / 2)) ^ (p - 2) :=
    Real.rpow_le_rpow hsum_pos.le hAB hp2_nonneg
  have hsplit :
      ((p - 1) * ((x - y) / 2)) ^ (p - 2) =
        (p - 1) ^ (p - 2) * ((x - y) / 2) ^ (p - 2) := by
    rw [Real.mul_rpow hp1_nonneg hdiff_pos.le]
  have hbase :
      (p - 1) ^ (p - 2) ≤ (p - 1) ^ p :=
    Real.rpow_le_rpow_of_exponent_le hp1_one (by linarith)
  have hright :
      (p - 1) ^ (p - 2) * ((x - y) / 2) ^ (p - 2) ≤
        (p - 1) ^ p * ((x - y) / 2) ^ (p - 2) :=
    mul_le_mul_of_nonneg_right hbase (Real.rpow_nonneg hdiff_pos.le _)
  linarith

lemma Dxx_vGeTwo_formula_on_A2 (p : ℝ) (hp : 2 ≤ p) (x y : ℝ) (hA2 : A2 p x y) :
    deriv (deriv (fun t => vGeTwo p t y)) x =
      (p * (p - 1) / 4) *
        (((x + y) / 2) ^ (p - 2) -
          (p - 1) ^ p * ((x - y) / 2) ^ (p - 2)) := by
  rcases hA2 with ⟨hx, hneg, hay⟩
  have hp_ge1 : 1 ≤ p := by linarith
  have hp1_ge1 : 1 ≤ p - 1 := by linarith
  have hyx : y < x := by
    rw [a, pStar_eq_self_of_two_le p hp] at hay
    have hp0 : 0 < p := by linarith
    have hcoeff : 1 - 2 / p < (1 : ℝ) := by
      have hdiv : 0 < 2 / p := by positivity
      linarith
    have hax_lt_x : (1 - 2 / p) * x < x := by
      simpa using mul_lt_mul_of_pos_right hcoeff hx
    linarith
  have hsum : 0 < (x + y) / 2 := by linarith
  have hdiff : 0 < (x - y) / 2 := by linarith
  let g : ℝ → ℝ := fun t =>
    ((t + y) / 2) ^ p - (p - 1) ^ p * (((t - y) / 2) ^ p)
  have hsum_nhds : {t : ℝ | 0 < (t + y) / 2} ∈ nhds x := by
    exact ((((continuous_id'.add continuous_const).div_const 2).continuousAt).preimage_mem_nhds
      (Ioi_mem_nhds hsum))
  have hdiff_nhds : {t : ℝ | 0 < (t - y) / 2} ∈ nhds x := by
    exact ((((continuous_id'.sub continuous_const).div_const 2).continuousAt).preimage_mem_nhds
      (Ioi_mem_nhds hdiff))
  have hEq : (fun t => vGeTwo p t y) =ᶠ[nhds x] g := by
    filter_upwards [hsum_nhds, hdiff_nhds] with t ht_sum ht_diff
    simp [vGeTwo, g, abs_of_pos ht_sum, abs_of_pos ht_diff]
  have hderiv2 :
      deriv (deriv (fun t => vGeTwo p t y)) x = deriv (deriv g) x :=
    hEq.deriv.deriv_eq
  have hfun :
      deriv g =
        fun t =>
          ((t + y) / 2) ^ (p - 1) * (p / 2) -
            (p - 1) ^ p * (((t - y) / 2) ^ (p - 1)) * (p / 2) := by
    funext t
    have hbase_sum :
        HasDerivAt (fun s : ℝ => (s + y) / 2) (1 / 2) t := by
      simpa [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using
        (((hasDerivAt_id t).add_const y).const_mul (1 / 2 : ℝ))
    have hbase_diff :
        HasDerivAt (fun s : ℝ => (s - y) / 2) (1 / 2) t := by
      simpa [sub_eq_add_neg, div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using
        (((hasDerivAt_id t).add_const (-y)).const_mul (1 / 2 : ℝ))
    have hpow_sum :
        HasDerivAt (fun s : ℝ => ((s + y) / 2) ^ p)
          (p * (((t + y) / 2) ^ (p - 1)) * (1 / 2)) t := by
      have hrpow :
          HasDerivAt (fun u : ℝ => u ^ p) (p * (((t + y) / 2) ^ (p - 1)))
            ((t + y) / 2) := by
        simpa using
          (Real.hasDerivAt_rpow_const (Or.inr hp_ge1) :
            HasDerivAt (fun u : ℝ => u ^ p) (p * ((t + y) / 2) ^ (p - 1))
              ((t + y) / 2))
      simpa [mul_assoc, mul_left_comm, mul_comm] using hrpow.comp t hbase_sum
    have hpow_diff :
        HasDerivAt (fun s : ℝ => ((s - y) / 2) ^ p)
          (p * (((t - y) / 2) ^ (p - 1)) * (1 / 2)) t := by
      have hrpow :
          HasDerivAt (fun u : ℝ => u ^ p) (p * (((t - y) / 2) ^ (p - 1)))
            ((t - y) / 2) := by
        simpa using
          (Real.hasDerivAt_rpow_const (Or.inr hp_ge1) :
            HasDerivAt (fun u : ℝ => u ^ p) (p * ((t - y) / 2) ^ (p - 1))
              ((t - y) / 2))
      simpa [mul_assoc, mul_left_comm, mul_comm] using hrpow.comp t hbase_diff
    have hd :
        HasDerivAt g
          (p * (((t + y) / 2) ^ (p - 1)) * (1 / 2) -
            (p - 1) ^ p * (p * (((t - y) / 2) ^ (p - 1)) * (1 / 2))) t := by
      dsimp [g]
      exact hpow_sum.sub (hpow_diff.const_mul ((p - 1) ^ p))
    calc
      deriv g t =
          p * (((t + y) / 2) ^ (p - 1)) * (1 / 2) -
            (p - 1) ^ p * (p * (((t - y) / 2) ^ (p - 1)) * (1 / 2)) := hd.deriv
      _ = ((t + y) / 2) ^ (p - 1) * (p / 2) -
            (p - 1) ^ p * (((t - y) / 2) ^ (p - 1)) * (p / 2) := by ring
  have hd2 :
      HasDerivAt
        (fun t =>
          ((t + y) / 2) ^ (p - 1) * (p / 2) -
            (p - 1) ^ p * (((t - y) / 2) ^ (p - 1)) * (p / 2))
        ((p * (p - 1) / 4) *
          (((x + y) / 2) ^ (p - 2) -
            (p - 1) ^ p * ((x - y) / 2) ^ (p - 2))) x := by
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
          (Real.hasDerivAt_rpow_const (Or.inr hp1_ge1) :
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
          (Real.hasDerivAt_rpow_const (Or.inr hp1_ge1) :
            HasDerivAt (fun u : ℝ => u ^ (p - 1))
              ((p - 1) * ((x - y) / 2) ^ ((p - 1) - 1)) ((x - y) / 2))
      simpa [mul_assoc, mul_left_comm, mul_comm] using hrpow.comp x hbase_diff
    have hd :
        HasDerivAt
          (fun t =>
            ((t + y) / 2) ^ (p - 1) * (p / 2) -
              (p - 1) ^ p * (((t - y) / 2) ^ (p - 1)) * (p / 2))
          (((p - 1) * (((x + y) / 2) ^ (p - 2)) * (1 / 2)) * (p / 2) -
            (p - 1) ^ p *
              (((p - 1) * (((x - y) / 2) ^ (p - 2)) * (1 / 2))) *
                (p / 2)) x := by
      exact (hpow_sum.mul_const (p / 2)).sub
        ((hpow_diff.const_mul ((p - 1) ^ p)).mul_const (p / 2))
    refine hd.congr_deriv ?_
    ring
  rw [hderiv2, hfun]
  exact hd2.deriv

lemma Dxx_vGeTwo_nonpos (p : ℝ) (hp : 2 ≤ p) (x y : ℝ) (hA2 : A2 p x y) :
    0 ≥ deriv (deriv (fun x => vGeTwo p x y)) x := by
  rw [Dxx_vGeTwo_formula_on_A2 p hp x y hA2]
  have hcoef : 0 ≤ p * (p - 1) / 4 := by
    exact div_nonneg (mul_nonneg (by linarith) (by linarith)) (by norm_num)
  have hbr := vGeTwo_A2_second_bracket_nonpos p hp x y hA2
  nlinarith [mul_nonpos_of_nonneg_of_nonpos hcoef hbr]

lemma Dyy_vGeTwo_formula_on_A2 (p : ℝ) (hp : 2 ≤ p) (x y : ℝ) (hA2 : A2 p x y) :
    deriv (deriv (fun s => vGeTwo p x s)) y =
      (p * (p - 1) / 4) *
        (((x + y) / 2) ^ (p - 2) -
          (p - 1) ^ p * ((x - y) / 2) ^ (p - 2)) := by
  rcases hA2 with ⟨hx, hneg, hay⟩
  have hp_ge1 : 1 ≤ p := by linarith
  have hp1_ge1 : 1 ≤ p - 1 := by linarith
  have hyx : y < x := by
    rw [a, pStar_eq_self_of_two_le p hp] at hay
    have hp0 : 0 < p := by linarith
    have hcoeff : 1 - 2 / p < (1 : ℝ) := by
      have hdiv : 0 < 2 / p := by positivity
      linarith
    have hax_lt_x : (1 - 2 / p) * x < x := by
      simpa using mul_lt_mul_of_pos_right hcoeff hx
    linarith
  have hsum : 0 < (x + y) / 2 := by linarith
  have hdiff : 0 < (x - y) / 2 := by linarith
  let g : ℝ → ℝ := fun s =>
    ((x + s) / 2) ^ p - (p - 1) ^ p * (((x - s) / 2) ^ p)
  have hsum_nhds : {s : ℝ | 0 < (x + s) / 2} ∈ nhds y := by
    exact ((((continuous_const.add continuous_id').div_const 2).continuousAt).preimage_mem_nhds
      (Ioi_mem_nhds hsum))
  have hdiff_nhds : {s : ℝ | 0 < (x - s) / 2} ∈ nhds y := by
    exact ((((continuous_const.sub continuous_id').div_const 2).continuousAt).preimage_mem_nhds
      (Ioi_mem_nhds hdiff))
  have hEq : (fun s => vGeTwo p x s) =ᶠ[nhds y] g := by
    filter_upwards [hsum_nhds, hdiff_nhds] with s hs_sum hs_diff
    simp [vGeTwo, g, abs_of_pos hs_sum, abs_of_pos hs_diff]
  have hderiv2 :
      deriv (deriv (fun s => vGeTwo p x s)) y = deriv (deriv g) y :=
    hEq.deriv.deriv_eq
  have hfun :
      deriv g =
        fun s =>
          ((x + s) / 2) ^ (p - 1) * (p / 2) +
            (p - 1) ^ p * (((x - s) / 2) ^ (p - 1)) * (p / 2) := by
    funext s
    have hbase_sum :
        HasDerivAt (fun u : ℝ => (x + u) / 2) (1 / 2) s := by
      simpa [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using
        (((hasDerivAt_id s).const_add x).const_mul (1 / 2 : ℝ))
    have hbase_diff :
        HasDerivAt (fun u : ℝ => (x - u) / 2) (-(1 / 2)) s := by
      simpa [sub_eq_add_neg, div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using
        ((((hasDerivAt_id s).neg).const_add x).const_mul (1 / 2 : ℝ))
    have hpow_sum :
        HasDerivAt (fun u : ℝ => ((x + u) / 2) ^ p)
          (p * (((x + s) / 2) ^ (p - 1)) * (1 / 2)) s := by
      have hrpow :
          HasDerivAt (fun u : ℝ => u ^ p) (p * (((x + s) / 2) ^ (p - 1)))
            ((x + s) / 2) := by
        simpa using
          (Real.hasDerivAt_rpow_const (Or.inr hp_ge1) :
            HasDerivAt (fun u : ℝ => u ^ p) (p * ((x + s) / 2) ^ (p - 1))
              ((x + s) / 2))
      simpa [mul_assoc, mul_left_comm, mul_comm] using hrpow.comp s hbase_sum
    have hpow_diff :
        HasDerivAt (fun u : ℝ => ((x - u) / 2) ^ p)
          (p * (((x - s) / 2) ^ (p - 1)) * (-(1 / 2))) s := by
      have hrpow :
          HasDerivAt (fun u : ℝ => u ^ p) (p * (((x - s) / 2) ^ (p - 1)))
            ((x - s) / 2) := by
        simpa using
          (Real.hasDerivAt_rpow_const (Or.inr hp_ge1) :
            HasDerivAt (fun u : ℝ => u ^ p) (p * ((x - s) / 2) ^ (p - 1))
              ((x - s) / 2))
      simpa [mul_assoc, mul_left_comm, mul_comm] using hrpow.comp s hbase_diff
    have hd :
        HasDerivAt g
          (p * (((x + s) / 2) ^ (p - 1)) * (1 / 2) -
            (p - 1) ^ p * (p * (((x - s) / 2) ^ (p - 1)) * (-(1 / 2)))) s := by
      dsimp [g]
      exact hpow_sum.sub (hpow_diff.const_mul ((p - 1) ^ p))
    calc
      deriv g s =
          p * (((x + s) / 2) ^ (p - 1)) * (1 / 2) -
            (p - 1) ^ p * (p * (((x - s) / 2) ^ (p - 1)) * (-(1 / 2))) := hd.deriv
      _ = ((x + s) / 2) ^ (p - 1) * (p / 2) +
            (p - 1) ^ p * (((x - s) / 2) ^ (p - 1)) * (p / 2) := by ring
  have hd2 :
      HasDerivAt
        (fun s =>
          ((x + s) / 2) ^ (p - 1) * (p / 2) +
            (p - 1) ^ p * (((x - s) / 2) ^ (p - 1)) * (p / 2))
        ((p * (p - 1) / 4) *
          (((x + y) / 2) ^ (p - 2) -
            (p - 1) ^ p * ((x - y) / 2) ^ (p - 2))) y := by
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
          (Real.hasDerivAt_rpow_const (Or.inr hp1_ge1) :
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
          (Real.hasDerivAt_rpow_const (Or.inr hp1_ge1) :
            HasDerivAt (fun u : ℝ => u ^ (p - 1))
              ((p - 1) * ((x - y) / 2) ^ ((p - 1) - 1)) ((x - y) / 2))
      simpa [mul_assoc, mul_left_comm, mul_comm] using hrpow.comp y hbase_diff
    have hd :
        HasDerivAt
          (fun s =>
            ((x + s) / 2) ^ (p - 1) * (p / 2) +
              (p - 1) ^ p * (((x - s) / 2) ^ (p - 1)) * (p / 2))
          (((p - 1) * (((x + y) / 2) ^ (p - 2)) * (1 / 2)) * (p / 2) +
            (p - 1) ^ p *
              (((p - 1) * (((x - y) / 2) ^ (p - 2)) * (-(1 / 2)))) *
                (p / 2)) y := by
      exact (hpow_sum.mul_const (p / 2)).add
        ((hpow_diff.const_mul ((p - 1) ^ p)).mul_const (p / 2))
    refine hd.congr_deriv ?_
    ring
  rw [hderiv2, hfun]
  exact hd2.deriv

lemma Dyy_vGeTwo_nonpos (p : ℝ) (hp : 2 ≤ p) (x y : ℝ) (hA2 : A2 p x y) :
    0 ≥ deriv (deriv (fun y => vGeTwo p x y)) y := by
  rw [Dyy_vGeTwo_formula_on_A2 p hp x y hA2]
  have hcoef : 0 ≤ p * (p - 1) / 4 := by
    exact div_nonneg (mul_nonneg (by linarith) (by linarith)) (by norm_num)
  have hbr := vGeTwo_A2_second_bracket_nonpos p hp x y hA2
  nlinarith [mul_nonpos_of_nonneg_of_nonpos hcoef hbr]

lemma Dxy_vGeTwo_formula_on_A2 (p : ℝ) (hp : 2 ≤ p) (x y : ℝ) (hA2 : A2 p x y) :
    deriv (fun x => deriv (fun y => vGeTwo p x y) y) x =
      (p * (p - 1) / 4) *
        (((x + y) / 2) ^ (p - 2) +
          (p - 1) ^ p * ((x - y) / 2) ^ (p - 2)) := by
  rcases hA2 with ⟨hx, hneg, hay⟩
  have hp1_ge1 : 1 ≤ p - 1 := by linarith
  have hyx : y < x := by
    rw [a, pStar_eq_self_of_two_le p hp] at hay
    have hp0 : 0 < p := by linarith
    have hcoeff : 1 - 2 / p < (1 : ℝ) := by
      have hdiv : 0 < 2 / p := by positivity
      linarith
    have hax_lt_x : (1 - 2 / p) * x < x := by
      simpa using mul_lt_mul_of_pos_right hcoeff hx
    linarith
  have hsum : 0 < (x + y) / 2 := by linarith
  have hdiff : 0 < (x - y) / 2 := by linarith
  let g : ℝ → ℝ := fun t =>
    ((t + y) / 2) ^ (p - 1) * (p / 2) +
      (p - 1) ^ p * (((t - y) / 2) ^ (p - 1)) * (p / 2)
  have ht0_nhds : {t : ℝ | 0 < t} ∈ nhds x := Ioi_mem_nhds hx
  have hneg_nhds : {t : ℝ | -t < y} ∈ nhds x := by
    have hxy : -y < x := by linarith
    simpa [neg_lt] using (Ioi_mem_nhds hxy : Set.Ioi (-y) ∈ nhds x)
  have hA_nhds : {t : ℝ | y < a p * t} ∈ nhds x := by
    have hcont : ContinuousAt (fun t : ℝ => a p * t - y) x :=
      ((continuous_const.mul continuous_id').sub continuous_const).continuousAt
    have hapos : 0 < a p * x - y := by linarith
    simpa [Set.preimage, sub_pos] using hcont.preimage_mem_nhds (Ioi_mem_nhds hapos)
  have hsum_nhds : {t : ℝ | 0 < (t + y) / 2} ∈ nhds x := by
    exact ((((continuous_id'.add continuous_const).div_const 2).continuousAt).preimage_mem_nhds
      (Ioi_mem_nhds hsum))
  have hdiff_nhds : {t : ℝ | 0 < (t - y) / 2} ∈ nhds x := by
    exact ((((continuous_id'.sub continuous_const).div_const 2).continuousAt).preimage_mem_nhds
      (Ioi_mem_nhds hdiff))
  have hEq :
      (fun t => deriv (fun s => vGeTwo p t s) y) =ᶠ[nhds x] g := by
    filter_upwards [ht0_nhds, hneg_nhds, hA_nhds, hsum_nhds, hdiff_nhds] with
      t ht0 htneg htA htsum htdiff
    have hA2t : A2 p t y := ⟨ht0, htneg, htA⟩
    calc
      deriv (fun s => vGeTwo p t s) y = DyvGeTwo p t y :=
        deriv_vGeTwo_eq_DyvGeTwo_on_A2 p hp t y hA2t
      _ = g t := by
        simp [g, DyvGeTwo, ht0, abs_of_pos htsum, abs_of_pos htdiff]
  have hd :
      HasDerivAt g
        ((p * (p - 1) / 4) *
          (((x + y) / 2) ^ (p - 2) +
            (p - 1) ^ p * ((x - y) / 2) ^ (p - 2))) x := by
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
          (Real.hasDerivAt_rpow_const (Or.inr hp1_ge1) :
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
          (Real.hasDerivAt_rpow_const (Or.inr hp1_ge1) :
            HasDerivAt (fun u : ℝ => u ^ (p - 1))
              ((p - 1) * ((x - y) / 2) ^ ((p - 1) - 1)) ((x - y) / 2))
      simpa [mul_assoc, mul_left_comm, mul_comm] using hrpow.comp x hbase_diff
    have hd' :
        HasDerivAt g
          (((p - 1) * (((x + y) / 2) ^ (p - 2)) * (1 / 2)) * (p / 2) +
            (p - 1) ^ p *
              (((p - 1) * (((x - y) / 2) ^ (p - 2)) * (1 / 2))) *
                (p / 2)) x := by
      dsimp [g]
      exact (hpow_sum.mul_const (p / 2)).add
        ((hpow_diff.const_mul ((p - 1) ^ p)).mul_const (p / 2))
    refine hd'.congr_deriv ?_
    ring
  rw [hEq.deriv_eq]
  exact hd.deriv

lemma Dxy_vGeTwo_nonneg (p : ℝ) (hp : 2 ≤ p) (x y : ℝ) (hA2 : A2 p x y) :
    0 ≤ deriv (fun x => deriv (fun y => vGeTwo p x y) y) x := by
  rw [Dxy_vGeTwo_formula_on_A2 p hp x y hA2]
  rcases hA2 with ⟨hx, hneg, hay⟩
  have hpcoef : 0 ≤ p * (p - 1) / 4 := by
    exact div_nonneg (mul_nonneg (by linarith) (by linarith)) (by norm_num)
  have hsum : 0 ≤ ((x + y) / 2) ^ (p - 2) := by
    have hpos : 0 < (x + y) / 2 := by
      have hp' : 2 ≤ p := hp
      rw [a, pStar_eq_self_of_two_le p hp'] at hay
      have hp0 : 0 < p := by linarith
      have hcoeff : 1 - 2 / p < (1 : ℝ) := by
        have hdiv : 0 < 2 / p := by positivity
        linarith
      have hyx : y < x := by
        have hax_lt_x : (1 - 2 / p) * x < x := by
          simpa using mul_lt_mul_of_pos_right hcoeff hx
        linarith
      linarith
    exact Real.rpow_nonneg hpos.le _
  have hdiff : 0 ≤ ((x - y) / 2) ^ (p - 2) := by
    have hpos : 0 < (x - y) / 2 := by
      rw [a, pStar_eq_self_of_two_le p hp] at hay
      have hp0 : 0 < p := by linarith
      have hcoeff : 1 - 2 / p < (1 : ℝ) := by
        have hdiv : 0 < 2 / p := by positivity
        linarith
      have hyx : y < x := by
        have hax_lt_x : (1 - 2 / p) * x < x := by
          simpa using mul_lt_mul_of_pos_right hcoeff hx
        linarith
      linarith
    exact Real.rpow_nonneg hpos.le _
  have hpbase : 0 ≤ (p - 1) ^ p := Real.rpow_nonneg (by linarith) _
  have hsumbr :
      0 ≤ ((x + y) / 2) ^ (p - 2) +
        (p - 1) ^ p * ((x - y) / 2) ^ (p - 2) :=
    add_nonneg hsum (mul_nonneg hpbase hdiff)
  exact mul_nonneg hpcoef hsumbr

lemma a_nonneg_of_two_le (p : ℝ) (hp : 2 ≤ p) : 0 ≤ a p := by
  have hpStar : pStar p = p := pStar_eq_self_of_two_le p hp
  have hp_pos : 0 < p := by linarith
  rw [a, hpStar]
  field_simp [hp_pos.ne]
  nlinarith

lemma a_lt_one_of_two_le (p : ℝ) (hp : 2 ≤ p) : a p < 1 := by
  have hpStar : pStar p = p := pStar_eq_self_of_two_le p hp
  have hp_pos : 0 < p := by linarith
  rw [a, hpStar]
  have hdiv : 0 < 2 / p := by positivity
  linarith

lemma deriv_auxFunction1_eq_DxauxFunction1_on_A1 (p : ℝ) (hp : 2 ≤ p) (x y : ℝ)
    (hA1 : A1 p x y) :
    deriv (fun t => auxFunction1 p t y) x = DxauxFunction1 p x y := by
  rcases hA1 with ⟨hx, hay, hyx⟩
  have hEq : (fun t => auxFunction1 p t y) =ᶠ[nhds x] fun t => uA1 p t y := by
    have h0 : {t : ℝ | 0 < t} ∈ nhds x := Ioi_mem_nhds hx
    have hA : {t : ℝ | a p * t < y} ∈ nhds x := by
      have hcont : ContinuousAt (fun t : ℝ => y - a p * t) x :=
        (continuous_const.sub (continuous_const.mul continuous_id')).continuousAt
      have hypos : 0 < y - a p * x := by linarith
      simpa [Set.preimage, sub_pos] using hcont.preimage_mem_nhds (Ioi_mem_nhds hypos)
    have hY : {t : ℝ | y < t} ∈ nhds x := Ioi_mem_nhds hyx
    filter_upwards [h0, hA, hY] with t ht0 htA htY
    exact auxFunction1_eq_uA1 p t y ⟨le_of_lt ht0, le_of_lt htA, le_of_lt htY⟩
  calc
    deriv (fun t => auxFunction1 p t y) x = deriv (fun t => uA1 p t y) x := hEq.deriv_eq
    _ = DxuA1Fun p (x, y) := deriv_uA1_eq_DxuA1Fun_on_A1 p hp x y ⟨hx, hay, hyx⟩
    _ = DxauxFunction1 p x y := by
          symm
          exact auxFunction1_Dx_eq_DxuA1 p x y ⟨le_of_lt hx, le_of_lt hay, le_of_lt hyx⟩

lemma deriv_auxFunction1_eq_DxauxFunction1_on_A2 (p : ℝ) (hp : 2 ≤ p) (x y : ℝ)
    (hA2 : A2 p x y) :
    deriv (fun t => auxFunction1 p t y) x = DxauxFunction1 p x y := by
  rcases hA2 with ⟨hx, hneg, hay⟩
  have hEq : (fun t => auxFunction1 p t y) =ᶠ[nhds x] fun t => vGeTwo p t y := by
    have h0 : {t : ℝ | 0 < t} ∈ nhds x := Ioi_mem_nhds hx
    have hN : {t : ℝ | -t < y} ∈ nhds x := by
      have hxy : -y < x := by linarith
      simpa [neg_lt] using (Ioi_mem_nhds hxy : Set.Ioi (-y) ∈ nhds x)
    have hA : {t : ℝ | y < a p * t} ∈ nhds x := by
      have hcont : ContinuousAt (fun t : ℝ => a p * t - y) x :=
        ((continuous_const.mul continuous_id').sub continuous_const).continuousAt
      have hapos : 0 < a p * x - y := by linarith
      simpa [Set.preimage, sub_pos] using hcont.preimage_mem_nhds (Ioi_mem_nhds hapos)
    filter_upwards [h0, hN, hA] with t ht0 htN htA
    exact auxFunction1_eq_vGeTwo p hp t y ⟨le_of_lt ht0, le_of_lt htN, le_of_lt htA⟩
  calc
    deriv (fun t => auxFunction1 p t y) x = deriv (fun t => vGeTwo p t y) x := hEq.deriv_eq
    _ = DxvGeTwo p x y := deriv_vGeTwo_eq_DxvGeTwo_on_A2 p hp x y ⟨hx, hneg, hay⟩
    _ = DxauxFunction1 p x y := by
          symm
          exact auxFunction1_Dx_eq_DxvGeTwo p hp x y ⟨le_of_lt hx, le_of_lt hneg, le_of_lt hay⟩

lemma hasDerivAt_auxFunction1_x_on_boundary (p x : ℝ) (hp : 2 ≤ p) (hx : 0 < x) :
    HasDerivAt (fun t => auxFunction1 p t ((a p) * x))
      (DxauxFunction1 p x ((a p) * x)) x := by
  have ha_nonneg : 0 ≤ a p := a_nonneg_of_two_le p hp
  have hy_nonneg : 0 ≤ a p * x := mul_nonneg ha_nonneg hx.le
  have hyx : a p * x < x := by
    have hlt : a p < 1 := a_lt_one_of_two_le p hp
    simpa using mul_lt_mul_of_pos_right hlt hx
  have hsum : 0 < (x + a p * x) / 2 := by
    have : 0 < x + a p * x := by nlinarith
    linarith
  have hdiff : 0 < (x - a p * x) / 2 := by
    have : 0 < x - a p * x := by nlinarith
    linarith
  have hleftEq :
      (fun t => auxFunction1 p t ((a p) * x)) =ᶠ[𝓝[Set.Iic x] x]
        fun t => uA1 p t ((a p) * x) := by
    have hmem : {t : ℝ | t ≤ x ∧ a p * x < t} ∈ 𝓝[Set.Iic x] x := by
      simpa [Set.Iic, Set.setOf_and] using inter_mem_nhdsWithin (Set.Iic x) (Ioi_mem_nhds hyx)
    filter_upwards [hmem] with t ht
    rcases ht with ⟨htle, hty⟩
    have hmul : a p * t ≤ a p * x := mul_le_mul_of_nonneg_left htle ha_nonneg
    have hcl : closureA1 p t ((a p) * x) := by
      refine ⟨le_of_lt (lt_of_le_of_lt hy_nonneg hty), hmul, le_of_lt hty⟩
    exact auxFunction1_eq_uA1 p t ((a p) * x) hcl
  have hrightEq :
      (fun t => auxFunction1 p t ((a p) * x)) =ᶠ[𝓝[Set.Ici x] x]
        fun t => vGeTwo p t ((a p) * x) := by
    filter_upwards [self_mem_nhdsWithin] with t ht
    have hcl : closureA2 p t ((a p) * x) := by
      refine ⟨le_trans hx.le ht, ?_, ?_⟩
      · have htpos : 0 < t := lt_of_lt_of_le hx ht
        linarith
      · exact mul_le_mul_of_nonneg_left ht ha_nonneg
    exact auxFunction1_eq_vGeTwo p hp t ((a p) * x) hcl
  have hleft :
      HasDerivWithinAt (fun t => auxFunction1 p t ((a p) * x))
        (DxauxFunction1 p x ((a p) * x)) (Set.Iic x) x := by
    have hbase :
        HasDerivWithinAt (fun t => uA1 p t ((a p) * x))
          (DxuA1Fun p (x, (a p) * x)) (Set.Iic x) x :=
      (hasDerivAt_uA1_x_of_pos p hp x ((a p) * x) hx).hasDerivWithinAt
    refine (hbase.congr_of_eventuallyEq_of_mem hleftEq (Set.mem_Iic.mpr le_rfl)).congr_deriv ?_
    exact (auxFunction1_Dx_eq_DxuA1 p x ((a p) * x)
      ⟨hx.le, le_rfl, le_of_lt hyx⟩).symm
  have hright :
      HasDerivWithinAt (fun t => auxFunction1 p t ((a p) * x))
        (DxauxFunction1 p x ((a p) * x)) (Set.Ici x) x := by
    have hbase :
        HasDerivWithinAt (fun t => vGeTwo p t ((a p) * x))
          (DxvGeTwo p x ((a p) * x)) (Set.Ici x) x :=
      (hasDerivAt_vGeTwo_x_of_pos p hp x ((a p) * x) hsum hdiff).hasDerivWithinAt
    refine (hbase.congr_of_eventuallyEq_of_mem hrightEq (Set.mem_Ici.mpr le_rfl)).congr_deriv ?_
    exact (auxFunction1_Dx_eq_DxvGeTwo p hp x ((a p) * x)
      ⟨hx.le, by linarith, le_rfl⟩).symm
  simpa [Set.Iic_union_Ici] using hleft.union hright

lemma deriv_auxFunction1_eq_DyauxFunction1_on_A1 (p : ℝ) (hp : 2 < p) (x y : ℝ)
    (hA1 : A1 p x y) :
    deriv (fun s => auxFunction1 p x s) y = DyauxFunction1 p x y := by
  rcases hA1 with ⟨hx, hay, hyx⟩
  have hEq : (fun s => auxFunction1 p x s) =ᶠ[nhds y] fun s => uA1 p x s := by
    have h1 : {s : ℝ | a p * x < s} ∈ nhds y := Ioi_mem_nhds hay
    have h2 : {s : ℝ | s < x} ∈ nhds y := Iio_mem_nhds hyx
    filter_upwards [h1, h2] with s hs1 hs2
    exact auxFunction1_eq_uA1 p x s ⟨le_of_lt hx, le_of_lt hs1, le_of_lt hs2⟩
  calc
    deriv (fun s => auxFunction1 p x s) y = deriv (fun s => uA1 p x s) y := hEq.deriv_eq
    _ = DyuA1Fun p (x, y) := deriv_uA1_eq_DyuA1Fun_on_A1 p hp x y ⟨hx, hay, hyx⟩
    _ = DyauxFunction1 p x y := by
          symm
          exact auxFunction1_Dy_eq_DyuA1 p x y ⟨le_of_lt hx, le_of_lt hay, le_of_lt hyx⟩

lemma deriv_auxFunction1_eq_DyauxFunction1_on_A2 (p : ℝ) (hp : 2 ≤ p) (x y : ℝ)
    (hA2 : A2 p x y) :
    deriv (fun s => auxFunction1 p x s) y = DyauxFunction1 p x y := by
  rcases hA2 with ⟨hx, hneg, hay⟩
  have hEq : (fun s => auxFunction1 p x s) =ᶠ[nhds y] fun s => vGeTwo p x s := by
    have h1 : {s : ℝ | -x < s} ∈ nhds y := Ioi_mem_nhds hneg
    have h2 : {s : ℝ | s < a p * x} ∈ nhds y := Iio_mem_nhds hay
    filter_upwards [h1, h2] with s hs1 hs2
    exact auxFunction1_eq_vGeTwo p hp x s ⟨le_of_lt hx, le_of_lt hs1, le_of_lt hs2⟩
  calc
    deriv (fun s => auxFunction1 p x s) y = deriv (fun s => vGeTwo p x s) y := hEq.deriv_eq
    _ = DyvGeTwo p x y := deriv_vGeTwo_eq_DyvGeTwo_on_A2 p hp x y ⟨hx, hneg, hay⟩
    _ = DyauxFunction1 p x y := by
          symm
          exact auxFunction1_Dy_eq_DyvGeTwo p hp x y ⟨le_of_lt hx, le_of_lt hneg, le_of_lt hay⟩

lemma hasDerivAt_auxFunction1_y_on_boundary (p x : ℝ) (hp : 2 < p) (hx : 0 < x) :
    HasDerivAt (fun s => auxFunction1 p x s)
      (DyauxFunction1 p x ((a p) * x)) ((a p) * x) := by
  have hp' : 2 ≤ p := by linarith
  have ha_nonneg : 0 ≤ a p := a_nonneg_of_two_le p hp'
  have hy_nonneg : 0 ≤ a p * x := mul_nonneg ha_nonneg hx.le
  have hneg : -x < a p * x := by linarith
  have hyx : a p * x < x := by
    have hlt : a p < 1 := a_lt_one_of_two_le p hp'
    simpa using mul_lt_mul_of_pos_right hlt hx
  have hsum : 0 < (x + a p * x) / 2 := by
    have : 0 < x + a p * x := by nlinarith
    linarith
  have hdiff : 0 < (x - a p * x) / 2 := by
    have : 0 < x - a p * x := by nlinarith
    linarith
  have hleftEq :
      (fun s => auxFunction1 p x s) =ᶠ[𝓝[Set.Iic (a p * x)] (a p * x)]
        fun s => vGeTwo p x s := by
    have hmem : {s : ℝ | -x < s ∧ s ≤ a p * x} ∈ 𝓝[Set.Iic (a p * x)] (a p * x) := by
      exact Filter.inter_mem
        (mem_nhdsWithin_of_mem_nhds (Ioi_mem_nhds hneg))
        self_mem_nhdsWithin
    filter_upwards [hmem] with s hs
    rcases hs with ⟨hs1, hs2⟩
    have hcl : closureA2 p x s := ⟨hx.le, le_of_lt hs1, hs2⟩
    exact auxFunction1_eq_vGeTwo p hp' x s hcl
  have hrightEq :
      (fun s => auxFunction1 p x s) =ᶠ[𝓝[Set.Ici (a p * x)] (a p * x)]
        fun s => uA1 p x s := by
    have hmem : {s : ℝ | a p * x ≤ s ∧ s < x} ∈ 𝓝[Set.Ici (a p * x)] (a p * x) := by
      simpa [Set.Ici, Set.setOf_and] using
        inter_mem_nhdsWithin (Set.Ici (a p * x)) (Iio_mem_nhds hyx)
    filter_upwards [hmem] with s hs
    rcases hs with ⟨hs1, hs2⟩
    have hcl : closureA1 p x s := ⟨hx.le, hs1, le_of_lt hs2⟩
    exact auxFunction1_eq_uA1 p x s hcl
  have hleft :
      HasDerivWithinAt (fun s => auxFunction1 p x s)
        (DyauxFunction1 p x ((a p) * x)) (Set.Iic ((a p) * x)) ((a p) * x) := by
    have hbase :
        HasDerivWithinAt (fun s => vGeTwo p x s)
          (DyvGeTwo p x ((a p) * x)) (Set.Iic ((a p) * x)) ((a p) * x) :=
      (hasDerivAt_vGeTwo_y_of_pos p hp' x ((a p) * x) hsum hdiff).hasDerivWithinAt
    refine (hbase.congr_of_eventuallyEq_of_mem hleftEq (Set.mem_Iic.mpr le_rfl)).congr_deriv ?_
    exact (auxFunction1_Dy_eq_DyvGeTwo p hp' x ((a p) * x)
      ⟨hx.le, le_of_lt hneg, le_rfl⟩).symm
  have hright :
      HasDerivWithinAt (fun s => auxFunction1 p x s)
        (DyauxFunction1 p x ((a p) * x)) (Set.Ici ((a p) * x)) ((a p) * x) := by
    have hbase :
        HasDerivWithinAt (fun s => uA1 p x s)
          (DyuA1Fun p (x, (a p) * x)) (Set.Ici ((a p) * x)) ((a p) * x) :=
      (hasDerivAt_uA1_y_of_pos p hp' x ((a p) * x) hx).hasDerivWithinAt
    refine (hbase.congr_of_eventuallyEq_of_mem hrightEq (Set.mem_Ici.mpr le_rfl)).congr_deriv ?_
    exact (auxFunction1_Dy_eq_DyuA1 p x ((a p) * x)
      ⟨hx.le, le_rfl, le_of_lt hyx⟩).symm
  simpa [Set.Iic_union_Ici] using hleft.union hright

lemma deriv_auxFunction1_eq_DxauxFunction1_on_QuarterPlaneOpen (p : ℝ) (hp : 2 ≤ p)
    (x y : ℝ) (hQ : QuarterPlaneOpen x y) :
    deriv (fun t => auxFunction1 p t y) x = DxauxFunction1 p x y := by
  rcases hQ with ⟨hx, hyx, hneg⟩
  by_cases h1 : a p * x < y
  · exact deriv_auxFunction1_eq_DxauxFunction1_on_A1 p hp x y ⟨hx, h1, hyx⟩
  · by_cases h2 : y < a p * x
    · exact deriv_auxFunction1_eq_DxauxFunction1_on_A2 p hp x y ⟨hx, hneg, h2⟩
    · have hy : y = a p * x := le_antisymm (not_lt.mp h1) (not_lt.mp h2)
      rw [hy]
      exact (hasDerivAt_auxFunction1_x_on_boundary p x hp hx).deriv

lemma hasDerivAt_auxFunction1_x_on_QuarterPlaneOpen (p : ℝ) (hp : 2 ≤ p)
    (x y : ℝ) (hQ : QuarterPlaneOpen x y) :
    HasDerivAt (fun t => auxFunction1 p t y) (DxauxFunction1 p x y) x := by
  rcases hQ with ⟨hx, hyx, hneg⟩
  by_cases h1 : a p * x < y
  · have hEq : (fun t => auxFunction1 p t y) =ᶠ[nhds x] fun t => uA1 p t y := by
      have h0 : {t : ℝ | 0 < t} ∈ nhds x := Ioi_mem_nhds hx
      have hA : {t : ℝ | a p * t < y} ∈ nhds x := by
        have hcont : ContinuousAt (fun t : ℝ => y - a p * t) x :=
          (continuous_const.sub (continuous_const.mul continuous_id')).continuousAt
        have hpos : 0 < y - a p * x := sub_pos.mpr h1
        simpa [Set.preimage, sub_pos] using hcont.preimage_mem_nhds (Ioi_mem_nhds hpos)
      have hY : {t : ℝ | y < t} ∈ nhds x := Ioi_mem_nhds hyx
      filter_upwards [h0, hA, hY] with t ht0 htA htY
      exact auxFunction1_eq_uA1 p t y ⟨le_of_lt ht0, le_of_lt htA, le_of_lt htY⟩
    have hbase : HasDerivAt (fun t => uA1 p t y) (DxuA1Fun p (x, y)) x :=
      hasDerivAt_uA1_x_of_pos p hp x y hx
    refine (hbase.congr_of_eventuallyEq hEq).congr_deriv ?_
    exact (auxFunction1_Dx_eq_DxuA1 p x y ⟨hx.le, le_of_lt h1, le_of_lt hyx⟩).symm
  · by_cases h2 : y < a p * x
    · have hEq : (fun t => auxFunction1 p t y) =ᶠ[nhds x] fun t => vGeTwo p t y := by
        have h0 : {t : ℝ | 0 < t} ∈ nhds x := Ioi_mem_nhds hx
        have hN : {t : ℝ | -t < y} ∈ nhds x := by
          have hxy : -y < x := by linarith
          simpa [neg_lt] using (Ioi_mem_nhds hxy : Set.Ioi (-y) ∈ nhds x)
        have hA : {t : ℝ | y < a p * t} ∈ nhds x := by
          have hcont : ContinuousAt (fun t : ℝ => a p * t - y) x :=
            ((continuous_const.mul continuous_id').sub continuous_const).continuousAt
          have hpos : 0 < a p * x - y := sub_pos.mpr h2
          simpa [Set.preimage, sub_pos] using hcont.preimage_mem_nhds (Ioi_mem_nhds hpos)
        filter_upwards [h0, hN, hA] with t ht0 htN htA
        exact auxFunction1_eq_vGeTwo p hp t y ⟨le_of_lt ht0, le_of_lt htN, le_of_lt htA⟩
      have hsum : 0 < (x + y) / 2 := by linarith
      have hdiff : 0 < (x - y) / 2 := by linarith
      have hbase : HasDerivAt (fun t => vGeTwo p t y) (DxvGeTwo p x y) x :=
        hasDerivAt_vGeTwo_x_of_pos p hp x y hsum hdiff
      refine (hbase.congr_of_eventuallyEq hEq).congr_deriv ?_
      exact (auxFunction1_Dx_eq_DxvGeTwo p hp x y ⟨hx.le, le_of_lt hneg, le_of_lt h2⟩).symm
    · have hy : y = a p * x := le_antisymm (not_lt.mp h1) (not_lt.mp h2)
      rw [hy]
      exact hasDerivAt_auxFunction1_x_on_boundary p x hp hx

lemma deriv_auxFunction1_eq_DyauxFunction1_on_QuarterPlaneOpen (p : ℝ) (hp : 2 < p)
    (x y : ℝ) (hQ : QuarterPlaneOpen x y) :
    deriv (fun s => auxFunction1 p x s) y = DyauxFunction1 p x y := by
  rcases hQ with ⟨hx, hyx, hneg⟩
  have hp' : 2 ≤ p := by linarith
  by_cases h1 : a p * x < y
  · exact deriv_auxFunction1_eq_DyauxFunction1_on_A1 p hp x y ⟨hx, h1, hyx⟩
  · by_cases h2 : y < a p * x
    · exact deriv_auxFunction1_eq_DyauxFunction1_on_A2 p hp' x y ⟨hx, hneg, h2⟩
    · have hy : y = a p * x := le_antisymm (not_lt.mp h1) (not_lt.mp h2)
      rw [hy]
      exact (hasDerivAt_auxFunction1_y_on_boundary p x hp hx).deriv

lemma hasDerivAt_auxFunction1_y_on_QuarterPlaneOpen (p : ℝ) (hp : 2 < p)
    (x y : ℝ) (hQ : QuarterPlaneOpen x y) :
    HasDerivAt (fun s => auxFunction1 p x s) (DyauxFunction1 p x y) y := by
  rcases hQ with ⟨hx, hyx, hneg⟩
  have hp' : 2 ≤ p := by linarith
  by_cases h1 : a p * x < y
  · have hEq : (fun s => auxFunction1 p x s) =ᶠ[nhds y] fun s => uA1 p x s := by
      have hA : {s : ℝ | a p * x < s} ∈ nhds y := Ioi_mem_nhds h1
      have hY : {s : ℝ | s < x} ∈ nhds y := Iio_mem_nhds hyx
      filter_upwards [hA, hY] with s hsA hsY
      exact auxFunction1_eq_uA1 p x s ⟨le_of_lt hx, le_of_lt hsA, le_of_lt hsY⟩
    have hbase : HasDerivAt (fun s => uA1 p x s) (DyuA1Fun p (x, y)) y :=
      hasDerivAt_uA1_y_of_pos p hp' x y hx
    refine (hbase.congr_of_eventuallyEq hEq).congr_deriv ?_
    exact (auxFunction1_Dy_eq_DyuA1 p x y ⟨hx.le, le_of_lt h1, le_of_lt hyx⟩).symm
  · by_cases h2 : y < a p * x
    · have hEq : (fun s => auxFunction1 p x s) =ᶠ[nhds y] fun s => vGeTwo p x s := by
        have hN : {s : ℝ | -x < s} ∈ nhds y := Ioi_mem_nhds hneg
        have hA : {s : ℝ | s < a p * x} ∈ nhds y := Iio_mem_nhds h2
        filter_upwards [hN, hA] with s hsN hsA
        exact auxFunction1_eq_vGeTwo p hp' x s ⟨le_of_lt hx, le_of_lt hsN, le_of_lt hsA⟩
      have hsum : 0 < (x + y) / 2 := by linarith
      have hdiff : 0 < (x - y) / 2 := by linarith
      have hbase : HasDerivAt (fun s => vGeTwo p x s) (DyvGeTwo p x y) y :=
        hasDerivAt_vGeTwo_y_of_pos p hp' x y hsum hdiff
      refine (hbase.congr_of_eventuallyEq hEq).congr_deriv ?_
      exact (auxFunction1_Dy_eq_DyvGeTwo p hp' x y ⟨hx.le, le_of_lt hneg, le_of_lt h2⟩).symm
    · have hy : y = a p * x := le_antisymm (not_lt.mp h1) (not_lt.mp h2)
      rw [hy]
      exact hasDerivAt_auxFunction1_y_on_boundary p x hp hx

lemma hasDerivAt_uCandidate_x_on_QuarterPlaneOpen (p : ℝ) (hp : 2 ≤ p)
    (x y : ℝ) (hQ : QuarterPlaneOpen x y) :
    HasDerivAt (fun t => uCandidate p t y) (DxuCandidate p x y) x := by
  rcases hQ with ⟨hx, hyx, hneg⟩
  have hEq : (fun t => uCandidate p t y) =ᶠ[nhds x] fun t => auxFunction1 p t y := by
    have h0 : {t : ℝ | 0 < t} ∈ nhds x := Ioi_mem_nhds hx
    have hY : {t : ℝ | y < t} ∈ nhds x := Ioi_mem_nhds hyx
    have hN : {t : ℝ | -t < y} ∈ nhds x := by
      have hxy : -y < x := by linarith
      simpa [neg_lt] using (Ioi_mem_nhds hxy : Set.Ioi (-y) ∈ nhds x)
    filter_upwards [h0, hY, hN] with t ht0 htY htN
    have hq : QuarterPlane t y := ⟨le_of_lt ht0, le_of_lt htY, le_of_lt htN⟩
    simp [uCandidate, hq]
  have hbase :
      HasDerivAt (fun t => auxFunction1 p t y) (DxauxFunction1 p x y) x :=
    hasDerivAt_auxFunction1_x_on_QuarterPlaneOpen p hp x y ⟨hx, hyx, hneg⟩
  refine (hbase.congr_of_eventuallyEq hEq).congr_deriv ?_
  simp [DxuCandidate, QuarterPlane, hx.le, hyx.le, hneg.le]

lemma hasDerivAt_uCandidate_y_on_QuarterPlaneOpen (p : ℝ) (hp : 2 < p)
    (x y : ℝ) (hQ : QuarterPlaneOpen x y) :
    HasDerivAt (fun s => uCandidate p x s) (DyuCandidate p x y) y := by
  rcases hQ with ⟨hx, hyx, hneg⟩
  have hEq : (fun s => uCandidate p x s) =ᶠ[nhds y] fun s => auxFunction1 p x s := by
    have hY : {s : ℝ | s < x} ∈ nhds y := Iio_mem_nhds hyx
    have hN : {s : ℝ | -x < s} ∈ nhds y := Ioi_mem_nhds hneg
    filter_upwards [hY, hN] with s hsY hsN
    have hq : QuarterPlane x s := ⟨hx.le, le_of_lt hsY, le_of_lt hsN⟩
    simp [uCandidate, hq]
  have hbase :
      HasDerivAt (fun s => auxFunction1 p x s) (DyauxFunction1 p x y) y :=
    hasDerivAt_auxFunction1_y_on_QuarterPlaneOpen p hp x y ⟨hx, hyx, hneg⟩
  refine (hbase.congr_of_eventuallyEq hEq).congr_deriv ?_
  simp [DyuCandidate, QuarterPlane, hx.le, hyx.le, hneg.le]

lemma hasDerivAt_uCandidate_x_on_QuarterPlane2Open (p : ℝ) (hp : 2 ≤ p)
    (x y : ℝ) (hQ : QuarterPlane2Open x y) :
    HasDerivAt (fun t => uCandidate p t y) (DxuCandidate p x y) x := by
  rcases hQ with ⟨hx, hynegx, hxy⟩
  have hQaux : QuarterPlaneOpen (-x) (-y) := by
    exact ⟨by linarith, by linarith, by linarith⟩
  have hEq : (fun t => uCandidate p t y) =ᶠ[nhds x]
      fun t => auxFunction1 p (-t) (-y) := by
    have hX : {t : ℝ | t < 0} ∈ nhds x := Iio_mem_nhds hx
    have hY : {t : ℝ | y < -t} ∈ nhds x := by
      have hcont : ContinuousAt (fun t : ℝ => -t - y) x :=
        (continuous_id'.neg.sub continuous_const).continuousAt
      have hpos : 0 < -x - y := by linarith
      simpa [Set.preimage, sub_pos] using hcont.preimage_mem_nhds (Ioi_mem_nhds hpos)
    have hXY : {t : ℝ | t < y} ∈ nhds x := Iio_mem_nhds hxy
    filter_upwards [hX, hY, hXY] with t htX htY htXY
    have hq1 : ¬ QuarterPlane t y := by
      intro hq
      exact not_le_of_gt htX hq.1
    have hq2 : QuarterPlane2 t y := ⟨le_of_lt htX, le_of_lt htY, le_of_lt htXY⟩
    simp [uCandidate, hq1, hq2]
  have haux :
      HasDerivAt (fun r => auxFunction1 p r (-y))
        (DxauxFunction1 p (-x) (-y)) (-x) :=
    hasDerivAt_auxFunction1_x_on_QuarterPlaneOpen p hp (-x) (-y) hQaux
  have hbase :
      HasDerivAt (fun t => auxFunction1 p (-t) (-y))
        (-(DxauxFunction1 p (-x) (-y))) x := by
    simpa [mul_comm] using haux.comp x (hasDerivAt_neg x)
  refine (hbase.congr_of_eventuallyEq hEq).congr_deriv ?_
  simp [DxuCandidate, QuarterPlane, QuarterPlane2, hx.le, hynegx.le, hxy.le,
    not_le_of_gt hx]

lemma hasDerivAt_uCandidate_x_on_QuarterPlane3Open (p : ℝ) (hp : 2 < p)
    (x y : ℝ) (hQ : QuarterPlane3Open x y) :
    HasDerivAt (fun t => uCandidate p t y) (DxuCandidate p x y) x := by
  rcases hQ with ⟨hy, hneg, hxy⟩
  have hQaux : QuarterPlaneOpen y x := ⟨hy, hxy, hneg⟩
  have hEq : (fun t => uCandidate p t y) =ᶠ[nhds x]
      fun t => auxFunction1 p y t := by
    have hN : {t : ℝ | -y < t} ∈ nhds x := Ioi_mem_nhds hneg
    have hY : {t : ℝ | t < y} ∈ nhds x := Iio_mem_nhds hxy
    filter_upwards [hN, hY] with t htN htY
    have hq1 : ¬ QuarterPlane t y := by
      intro hq
      exact not_le_of_gt htY hq.2.1
    have hq2 : ¬ QuarterPlane2 t y := by
      intro hq
      have hlt : -t < y := by linarith
      exact not_le_of_gt hlt hq.2.1
    have hq3 : QuarterPlane3 t y := ⟨hy.le, le_of_lt htN, le_of_lt htY⟩
    simp [uCandidate, hq1, hq2, hq3]
  have hbase :
      HasDerivAt (fun t => auxFunction1 p y t) (DyauxFunction1 p y x) x :=
    hasDerivAt_auxFunction1_y_on_QuarterPlaneOpen p hp y x hQaux
  refine (hbase.congr_of_eventuallyEq hEq).congr_deriv ?_
  have hq1 : ¬ QuarterPlane x y := by
    intro hq
    exact not_le_of_gt hxy hq.2.1
  have hq2 : ¬ QuarterPlane2 x y := by
    intro hq
    have hlt : -x < y := by linarith
    exact not_le_of_gt hlt hq.2.1
  have hq3 : QuarterPlane3 x y := ⟨hy.le, hneg.le, hxy.le⟩
  simp [DxuCandidate, hq1, hq2, hq3]

lemma hasDerivAt_uCandidate_x_on_QuarterPlane4Open (p : ℝ) (hp : 2 < p)
    (x y : ℝ) (hQ : QuarterPlane4Open x y) :
    HasDerivAt (fun t => uCandidate p t y) (DxuCandidate p x y) x := by
  rcases hQ with ⟨hy, hyx, hxnegy⟩
  have hQaux : QuarterPlaneOpen (-y) (-x) := by
    exact ⟨by linarith, by linarith, by linarith⟩
  have hEq : (fun t => uCandidate p t y) =ᶠ[nhds x]
      fun t => auxFunction1 p (-y) (-t) := by
    have hY : {t : ℝ | y < t} ∈ nhds x := Ioi_mem_nhds hyx
    have hX : {t : ℝ | t < -y} ∈ nhds x := Iio_mem_nhds hxnegy
    filter_upwards [hY, hX] with t htY htX
    have hq1 : ¬ QuarterPlane t y := by
      intro hq
      have hlt : y < -t := by linarith
      exact not_le_of_gt hlt hq.2.2
    have hq2 : ¬ QuarterPlane2 t y := by
      intro hq
      exact not_le_of_gt htY hq.2.2
    have hq3 : ¬ QuarterPlane3 t y := by
      intro hq
      exact not_le_of_gt hy hq.1
    have hq4 : QuarterPlane4 t y := ⟨le_of_lt hy, le_of_lt htY, le_of_lt htX⟩
    simp [uCandidate, hq1, hq2, hq3, hq4]
  have haux :
      HasDerivAt (fun s => auxFunction1 p (-y) s)
        (DyauxFunction1 p (-y) (-x)) (-x) :=
    hasDerivAt_auxFunction1_y_on_QuarterPlaneOpen p hp (-y) (-x) hQaux
  have hbase :
      HasDerivAt (fun t => auxFunction1 p (-y) (-t))
        (-(DyauxFunction1 p (-y) (-x))) x := by
    simpa [mul_comm] using haux.comp x (hasDerivAt_neg x)
  refine (hbase.congr_of_eventuallyEq hEq).congr_deriv ?_
  have hq1 : ¬ QuarterPlane x y := by
    intro hq
    have hlt : y < -x := by linarith
    exact not_le_of_gt hlt hq.2.2
  have hq2 : ¬ QuarterPlane2 x y := by
    intro hq
    exact not_le_of_gt hyx hq.2.2
  have hq3 : ¬ QuarterPlane3 x y := by
    intro hq
    exact not_le_of_gt hy hq.1
  have hq4 : QuarterPlane4 x y := ⟨hy.le, hyx.le, hxnegy.le⟩
  simp [DxuCandidate, hq1, hq2, hq3, hq4]

lemma hasDerivAt_uCandidate_y_on_QuarterPlane2Open (p : ℝ) (hp : 2 < p)
    (x y : ℝ) (hQ : QuarterPlane2Open x y) :
    HasDerivAt (fun s => uCandidate p x s) (DyuCandidate p x y) y := by
  rcases hQ with ⟨hx, hynegx, hxy⟩
  have hQaux : QuarterPlaneOpen (-x) (-y) := by
    exact ⟨by linarith, by linarith, by linarith⟩
  have hEq : (fun s => uCandidate p x s) =ᶠ[nhds y]
      fun s => auxFunction1 p (-x) (-s) := by
    have hY : {s : ℝ | s < -x} ∈ nhds y := Iio_mem_nhds hynegx
    have hX : {s : ℝ | x < s} ∈ nhds y := Ioi_mem_nhds hxy
    filter_upwards [hY, hX] with s hsY hsX
    have hq1 : ¬ QuarterPlane x s := by
      intro hq
      exact not_le_of_gt hx hq.1
    have hq2 : QuarterPlane2 x s := ⟨le_of_lt hx, le_of_lt hsY, le_of_lt hsX⟩
    simp [uCandidate, hq1, hq2]
  have haux :
      HasDerivAt (fun r => auxFunction1 p (-x) r)
        (DyauxFunction1 p (-x) (-y)) (-y) :=
    hasDerivAt_auxFunction1_y_on_QuarterPlaneOpen p hp (-x) (-y) hQaux
  have hbase :
      HasDerivAt (fun s => auxFunction1 p (-x) (-s))
        (-(DyauxFunction1 p (-x) (-y))) y := by
    simpa [mul_comm] using haux.comp y (hasDerivAt_neg y)
  refine (hbase.congr_of_eventuallyEq hEq).congr_deriv ?_
  have hq1 : ¬ QuarterPlane x y := by
    intro hq
    exact not_le_of_gt hx hq.1
  have hq2 : QuarterPlane2 x y := ⟨hx.le, hynegx.le, hxy.le⟩
  simp [DyuCandidate, hq1, hq2]

lemma hasDerivAt_uCandidate_y_on_QuarterPlane3Open (p : ℝ) (hp : 2 ≤ p)
    (x y : ℝ) (hQ : QuarterPlane3Open x y) :
    HasDerivAt (fun s => uCandidate p x s) (DyuCandidate p x y) y := by
  rcases hQ with ⟨hy, hneg, hxy⟩
  have hQaux : QuarterPlaneOpen y x := ⟨hy, hxy, hneg⟩
  have hEq : (fun s => uCandidate p x s) =ᶠ[nhds y]
      fun s => auxFunction1 p s x := by
    have hY : {s : ℝ | 0 < s} ∈ nhds y := Ioi_mem_nhds hy
    have hN : {s : ℝ | 0 < x + s} ∈ nhds y := by
      have hcont : ContinuousAt (fun s : ℝ => x + s) y :=
        (continuous_const.add continuous_id').continuousAt
      have hpos : 0 < x + y := by linarith
      simpa [Set.preimage] using hcont.preimage_mem_nhds (Ioi_mem_nhds hpos)
    have hX : {s : ℝ | x < s} ∈ nhds y := Ioi_mem_nhds hxy
    filter_upwards [hY, hN, hX] with s hsY hsN hsX
    have hq1 : ¬ QuarterPlane x s := by
      intro hq
      exact not_le_of_gt hsX hq.2.1
    have hq2 : ¬ QuarterPlane2 x s := by
      intro hq
      have hlt : -x < s := by linarith
      exact not_le_of_gt hlt hq.2.1
    have hsN' : -s < x := by linarith
    have hq3 : QuarterPlane3 x s := ⟨le_of_lt hsY, le_of_lt hsN', le_of_lt hsX⟩
    simp [uCandidate, hq1, hq2, hq3]
  have hbase :
      HasDerivAt (fun s => auxFunction1 p s x) (DxauxFunction1 p y x) y :=
    hasDerivAt_auxFunction1_x_on_QuarterPlaneOpen p hp y x hQaux
  refine (hbase.congr_of_eventuallyEq hEq).congr_deriv ?_
  have hq1 : ¬ QuarterPlane x y := by
    intro hq
    exact not_le_of_gt hxy hq.2.1
  have hq2 : ¬ QuarterPlane2 x y := by
    intro hq
    have hlt : -x < y := by linarith
    exact not_le_of_gt hlt hq.2.1
  have hq3 : QuarterPlane3 x y := ⟨hy.le, hneg.le, hxy.le⟩
  simp [DyuCandidate, hq1, hq2, hq3]

lemma hasDerivAt_uCandidate_y_on_QuarterPlane4Open (p : ℝ) (hp : 2 ≤ p)
    (x y : ℝ) (hQ : QuarterPlane4Open x y) :
    HasDerivAt (fun s => uCandidate p x s) (DyuCandidate p x y) y := by
  rcases hQ with ⟨hy, hyx, hxnegy⟩
  have hQaux : QuarterPlaneOpen (-y) (-x) := by
    exact ⟨by linarith, by linarith, by linarith⟩
  have hEq : (fun s => uCandidate p x s) =ᶠ[nhds y]
      fun s => auxFunction1 p (-s) (-x) := by
    have hY : {s : ℝ | s < 0} ∈ nhds y := Iio_mem_nhds hy
    have hYX : {s : ℝ | s < x} ∈ nhds y := Iio_mem_nhds hyx
    have hX : {s : ℝ | x < -s} ∈ nhds y := by
      have hcont : ContinuousAt (fun s : ℝ => -s - x) y :=
        (continuous_id'.neg.sub continuous_const).continuousAt
      have hpos : 0 < -y - x := by linarith
      simpa [Set.preimage, sub_pos] using hcont.preimage_mem_nhds (Ioi_mem_nhds hpos)
    filter_upwards [hY, hYX, hX] with s hsY hsYX hsX
    have hq1 : ¬ QuarterPlane x s := by
      intro hq
      have hlt : s < -x := by linarith
      exact not_le_of_gt hlt hq.2.2
    have hq2 : ¬ QuarterPlane2 x s := by
      intro hq
      exact not_le_of_gt hsYX hq.2.2
    have hq3 : ¬ QuarterPlane3 x s := by
      intro hq
      exact not_le_of_gt hsY hq.1
    have hq4 : QuarterPlane4 x s := ⟨le_of_lt hsY, le_of_lt hsYX, le_of_lt hsX⟩
    simp [uCandidate, hq1, hq2, hq3, hq4]
  have haux :
      HasDerivAt (fun r => auxFunction1 p r (-x))
        (DxauxFunction1 p (-y) (-x)) (-y) :=
    hasDerivAt_auxFunction1_x_on_QuarterPlaneOpen p hp (-y) (-x) hQaux
  have hbase :
      HasDerivAt (fun s => auxFunction1 p (-s) (-x))
        (-(DxauxFunction1 p (-y) (-x))) y := by
    simpa [mul_comm] using haux.comp y (hasDerivAt_neg y)
  refine (hbase.congr_of_eventuallyEq hEq).congr_deriv ?_
  have hq1 : ¬ QuarterPlane x y := by
    intro hq
    have hlt : y < -x := by linarith
    exact not_le_of_gt hlt hq.2.2
  have hq2 : ¬ QuarterPlane2 x y := by
    intro hq
    exact not_le_of_gt hyx hq.2.2
  have hq3 : ¬ QuarterPlane3 x y := by
    intro hq
    exact not_le_of_gt hy hq.1
  have hq4 : QuarterPlane4 x y := ⟨hy.le, hyx.le, hxnegy.le⟩
  simp [DyuCandidate, hq1, hq2, hq3, hq4]

lemma hasDerivAt_uCandidate_x_on_diag_pos (p : ℝ) (hp : 2 < p)
    (x : ℝ) (hx : 0 < x) :
    HasDerivAt (fun t => uCandidate p t x) (DxuCandidate p x x) x := by
  have hp' : 2 ≤ p := by linarith
  have hleftEq :
      (fun t => uCandidate p t x) =ᶠ[𝓝[Set.Iic x] x]
        fun t => auxFunction1 p x t := by
    have hmem : {t : ℝ | -x < t ∧ t ≤ x} ∈ 𝓝[Set.Iic x] x := by
      exact Filter.inter_mem
        (mem_nhdsWithin_of_mem_nhds (Ioi_mem_nhds (by linarith)))
        self_mem_nhdsWithin
    filter_upwards [hmem] with t ht
    rcases ht with ⟨hneg, htx⟩
    by_cases ht_eq : t = x
    · subst t
      have hq : QuarterPlane x x := ⟨hx.le, le_rfl, by linarith⟩
      simp [uCandidate, hq]
    · have htx_lt : t < x := lt_of_le_of_ne htx ht_eq
      have hq1' : ¬ QuarterPlane t x := by
        intro hq
        exact not_le_of_gt htx_lt hq.2.1
      have hq2 : ¬ QuarterPlane2 t x := by
        intro hq
        have hlt : -t < x := by linarith
        exact not_le_of_gt hlt hq.2.1
      have hq3 : QuarterPlane3 t x := ⟨hx.le, le_of_lt hneg, htx⟩
      simp [uCandidate, hq1', hq2, hq3]
  have hrightEq :
      (fun t => uCandidate p t x) =ᶠ[𝓝[Set.Ici x] x]
        fun t => auxFunction1 p t x := by
    filter_upwards [self_mem_nhdsWithin] with t ht
    have htpos : 0 < t := lt_of_lt_of_le hx ht
    have hq : QuarterPlane t x := ⟨le_of_lt htpos, ht, by linarith⟩
    simp [uCandidate, hq]
  have hleft :
      HasDerivWithinAt (fun t => uCandidate p t x)
        (DxuCandidate p x x) (Set.Iic x) x := by
    have hbase :
        HasDerivWithinAt (fun t => auxFunction1 p x t)
          (DyauxFunction1 p x x) (Set.Iic x) x :=
      by
        have ha_lt : a p * x < x := by
          have hlt : a p < 1 := a_lt_one_of_two_le p hp'
          simpa using mul_lt_mul_of_pos_right hlt hx
        have hEq :
            (fun t => auxFunction1 p x t) =ᶠ[𝓝[Set.Iic x] x]
              fun t => uA1 p x t := by
          have hmem : {t : ℝ | a p * x < t ∧ t ≤ x} ∈ 𝓝[Set.Iic x] x := by
            exact Filter.inter_mem
              (mem_nhdsWithin_of_mem_nhds (Ioi_mem_nhds ha_lt))
              self_mem_nhdsWithin
          filter_upwards [hmem] with t ht
          rcases ht with ⟨hat, htx⟩
          exact auxFunction1_eq_uA1 p x t ⟨hx.le, le_of_lt hat, htx⟩
        have hu :
            HasDerivWithinAt (fun t => uA1 p x t)
              (DyuA1Fun p (x, x)) (Set.Iic x) x :=
          (hasDerivAt_uA1_y_of_pos p hp' x x hx).hasDerivWithinAt
        refine (hu.congr_of_eventuallyEq_of_mem hEq (Set.mem_Iic.mpr le_rfl)).congr_deriv ?_
        exact (auxFunction1_Dy_eq_DyuA1 p x x ⟨hx.le, le_of_lt ha_lt, le_rfl⟩).symm
    refine (hbase.congr_of_eventuallyEq_of_mem hleftEq (Set.mem_Iic.mpr le_rfl)).congr_deriv ?_
    have hD : DxuCandidate p x x = DxauxFunction1 p x x := by
      simp [DxuCandidate, QuarterPlane, hx.le]
    rw [hD]
    exact (DxauxFunction1_eq_DyauxFunction1_on_diag p hp x hx.le).symm
  have hright :
      HasDerivWithinAt (fun t => uCandidate p t x)
        (DxuCandidate p x x) (Set.Ici x) x := by
    have hbase :
        HasDerivWithinAt (fun t => auxFunction1 p t x)
          (DxauxFunction1 p x x) (Set.Ici x) x :=
      by
        have ha_lt : a p * x < x := by
          have hlt : a p < 1 := a_lt_one_of_two_le p hp'
          simpa using mul_lt_mul_of_pos_right hlt hx
        have hEq :
            (fun t => auxFunction1 p t x) =ᶠ[𝓝[Set.Ici x] x]
              fun t => uA1 p t x := by
          have ha_pos : 0 < a p := by
            have hpStar : pStar p = p := pStar_eq_self_of_two_le p hp'
            have hp_pos : 0 < p := by linarith
            rw [a, hpStar]
            field_simp [hp_pos.ne]
            nlinarith
          have hx_lt_div : x < x / a p := by
            rw [div_eq_mul_inv]
            have ha_lt : a p < 1 := a_lt_one_of_two_le p hp'
            have hlt_inv : 1 < (a p)⁻¹ := by
              rw [one_lt_inv₀ ha_pos]
              exact ha_lt
            nlinarith
          have hmem : {t : ℝ | x ≤ t ∧ t < x / a p} ∈ 𝓝[Set.Ici x] x := by
            simpa [Set.Ici, Set.setOf_and] using
              inter_mem_nhdsWithin (Set.Ici x) (Iio_mem_nhds hx_lt_div)
          filter_upwards [hmem] with t ht
          rcases ht with ⟨ht, ht_div⟩
          have htpos : 0 < t := lt_of_lt_of_le hx ht
          have hat : a p * t < x := by
            have hmul := mul_lt_mul_of_pos_left ht_div ha_pos
            field_simp [ha_pos.ne'] at hmul
            simpa [mul_comm, mul_left_comm, mul_assoc] using hmul
          exact auxFunction1_eq_uA1 p t x ⟨le_of_lt htpos, le_of_lt hat, ht⟩
        have hu :
            HasDerivWithinAt (fun t => uA1 p t x)
              (DxuA1Fun p (x, x)) (Set.Ici x) x :=
          (hasDerivAt_uA1_x_of_pos p hp' x x hx).hasDerivWithinAt
        refine (hu.congr_of_eventuallyEq_of_mem hEq (Set.mem_Ici.mpr le_rfl)).congr_deriv ?_
        exact (auxFunction1_Dx_eq_DxuA1 p x x ⟨hx.le, le_of_lt ha_lt, le_rfl⟩).symm
    refine (hbase.congr_of_eventuallyEq_of_mem hrightEq (Set.mem_Ici.mpr le_rfl)).congr_deriv ?_
    simp [DxuCandidate, QuarterPlane, hx.le]
  simpa [Set.Iic_union_Ici] using hleft.union hright

lemma hasDerivAt_uCandidate_y_on_diag_pos (p : ℝ) (hp : 2 < p)
    (x : ℝ) (hx : 0 < x) :
    HasDerivAt (fun s => uCandidate p x s) (DyuCandidate p x x) x := by
  have hp' : 2 ≤ p := by linarith
  have hleftEq :
      (fun s => uCandidate p x s) =ᶠ[𝓝[Set.Iic x] x]
        fun s => auxFunction1 p x s := by
    have hmem : {s : ℝ | -x < s ∧ s ≤ x} ∈ 𝓝[Set.Iic x] x := by
      exact Filter.inter_mem
        (mem_nhdsWithin_of_mem_nhds (Ioi_mem_nhds (by linarith)))
        self_mem_nhdsWithin
    filter_upwards [hmem] with s hs
    rcases hs with ⟨hneg, hsx⟩
    have hq : QuarterPlane x s := ⟨hx.le, hsx, le_of_lt hneg⟩
    simp [uCandidate, hq]
  have hrightEq :
      (fun s => uCandidate p x s) =ᶠ[𝓝[Set.Ici x] x]
        fun s => auxFunction1 p s x := by
    filter_upwards [self_mem_nhdsWithin] with s hs
    by_cases hs_eq : s = x
    · subst s
      have hq : QuarterPlane x x := ⟨hx.le, le_rfl, by linarith⟩
      simp [uCandidate, hq]
    · have hxs_lt : x < s := lt_of_le_of_ne hs (Ne.symm hs_eq)
      have hq1 : ¬ QuarterPlane x s := by
        intro hq
        exact not_le_of_gt hxs_lt hq.2.1
      have hq2 : ¬ QuarterPlane2 x s := by
        intro hq
        exact not_le_of_gt hx hq.1
      have hq3 : QuarterPlane3 x s := ⟨le_trans hx.le hs, by linarith, le_of_lt hxs_lt⟩
      simp [uCandidate, hq1, hq2, hq3]
  have hleft :
      HasDerivWithinAt (fun s => uCandidate p x s)
        (DyuCandidate p x x) (Set.Iic x) x := by
    have hbase :
        HasDerivWithinAt (fun s => auxFunction1 p x s)
          (DyauxFunction1 p x x) (Set.Iic x) x :=
      by
        have ha_lt : a p * x < x := by
          have hlt : a p < 1 := a_lt_one_of_two_le p hp'
          simpa using mul_lt_mul_of_pos_right hlt hx
        have hEq :
            (fun s => auxFunction1 p x s) =ᶠ[𝓝[Set.Iic x] x]
              fun s => uA1 p x s := by
          have hmem : {s : ℝ | a p * x < s ∧ s ≤ x} ∈ 𝓝[Set.Iic x] x := by
            exact Filter.inter_mem
              (mem_nhdsWithin_of_mem_nhds (Ioi_mem_nhds ha_lt))
              self_mem_nhdsWithin
          filter_upwards [hmem] with s hs
          rcases hs with ⟨has, hsx⟩
          exact auxFunction1_eq_uA1 p x s ⟨hx.le, le_of_lt has, hsx⟩
        have hu :
            HasDerivWithinAt (fun s => uA1 p x s)
              (DyuA1Fun p (x, x)) (Set.Iic x) x :=
          (hasDerivAt_uA1_y_of_pos p hp' x x hx).hasDerivWithinAt
        refine (hu.congr_of_eventuallyEq_of_mem hEq (Set.mem_Iic.mpr le_rfl)).congr_deriv ?_
        exact (auxFunction1_Dy_eq_DyuA1 p x x ⟨hx.le, le_of_lt ha_lt, le_rfl⟩).symm
    refine (hbase.congr_of_eventuallyEq_of_mem hleftEq (Set.mem_Iic.mpr le_rfl)).congr_deriv ?_
    simp [DyuCandidate, QuarterPlane, hx.le]
  have hright :
      HasDerivWithinAt (fun s => uCandidate p x s)
        (DyuCandidate p x x) (Set.Ici x) x := by
    have hbase :
        HasDerivWithinAt (fun s => auxFunction1 p s x)
          (DxauxFunction1 p x x) (Set.Ici x) x :=
      by
        have ha_lt : a p * x < x := by
          have hlt : a p < 1 := a_lt_one_of_two_le p hp'
          simpa using mul_lt_mul_of_pos_right hlt hx
        have hEq :
            (fun s => auxFunction1 p s x) =ᶠ[𝓝[Set.Ici x] x]
              fun s => uA1 p s x := by
          have ha_pos : 0 < a p := by
            have hpStar : pStar p = p := pStar_eq_self_of_two_le p hp'
            have hp_pos : 0 < p := by linarith
            rw [a, hpStar]
            field_simp [hp_pos.ne]
            nlinarith
          have hx_lt_div : x < x / a p := by
            rw [div_eq_mul_inv]
            have ha_lt_one : a p < 1 := a_lt_one_of_two_le p hp'
            have hlt_inv : 1 < (a p)⁻¹ := by
              rw [one_lt_inv₀ ha_pos]
              exact ha_lt_one
            nlinarith
          have hmem : {s : ℝ | x ≤ s ∧ s < x / a p} ∈ 𝓝[Set.Ici x] x := by
            simpa [Set.Ici, Set.setOf_and] using
              inter_mem_nhdsWithin (Set.Ici x) (Iio_mem_nhds hx_lt_div)
          filter_upwards [hmem] with s hs
          rcases hs with ⟨hxs, hsdiv⟩
          have hspos : 0 < s := lt_of_lt_of_le hx hxs
          have has : a p * s < x := by
            have hmul := mul_lt_mul_of_pos_left hsdiv ha_pos
            field_simp [ha_pos.ne'] at hmul
            simpa [mul_comm, mul_left_comm, mul_assoc] using hmul
          exact auxFunction1_eq_uA1 p s x ⟨le_of_lt hspos, le_of_lt has, hxs⟩
        have hu :
            HasDerivWithinAt (fun s => uA1 p s x)
              (DxuA1Fun p (x, x)) (Set.Ici x) x :=
          (hasDerivAt_uA1_x_of_pos p hp' x x hx).hasDerivWithinAt
        refine (hu.congr_of_eventuallyEq_of_mem hEq (Set.mem_Ici.mpr le_rfl)).congr_deriv ?_
        exact (auxFunction1_Dx_eq_DxuA1 p x x ⟨hx.le, le_of_lt ha_lt, le_rfl⟩).symm
    refine (hbase.congr_of_eventuallyEq_of_mem hrightEq (Set.mem_Ici.mpr le_rfl)).congr_deriv ?_
    have hD : DyuCandidate p x x = DyauxFunction1 p x x := by
      simp [DyuCandidate, QuarterPlane, hx.le]
    rw [hD]
    exact DxauxFunction1_eq_DyauxFunction1_on_diag p hp x hx.le
  simpa [Set.Iic_union_Ici] using hleft.union hright

lemma hasDerivAt_uCandidate_x_on_antidiag_pos (p : ℝ) (hp : 2 < p)
    (x : ℝ) (hx : 0 < x) :
    HasDerivAt (fun t => uCandidate p t (-x)) (DxuCandidate p x (-x)) x := by
  have hp' : 2 ≤ p := by linarith
  have ha_nonneg : 0 ≤ a p := by
    have hpStar : pStar p = p := pStar_eq_self_of_two_le p hp'
    have hp_pos : 0 < p := by linarith
    rw [a, hpStar]
    field_simp [hp_pos.ne]
    nlinarith
  have hleftEq :
      (fun t => uCandidate p t (-x)) =ᶠ[𝓝[Set.Iic x] x]
        fun t => auxFunction1 p x (-t) := by
    have hmem : {t : ℝ | -x < t ∧ t ≤ x} ∈ 𝓝[Set.Iic x] x := by
      exact Filter.inter_mem
        (mem_nhdsWithin_of_mem_nhds (Ioi_mem_nhds (by linarith)))
        self_mem_nhdsWithin
    filter_upwards [hmem] with t ht
    rcases ht with ⟨hneg, htx⟩
    by_cases ht_eq : t = x
    · subst t
      have hq : QuarterPlane x (-x) := ⟨hx.le, by linarith, le_rfl⟩
      simp [uCandidate, hq]
    · have htx_lt : t < x := lt_of_le_of_ne htx ht_eq
      have hq1 : ¬ QuarterPlane t (-x) := by
        intro hq
        have hxt : x ≤ t := by linarith [hq.2.2]
        linarith
      have hq2 : ¬ QuarterPlane2 t (-x) := by
        intro hq
        linarith [hq.2.2]
      have hq3 : ¬ QuarterPlane3 t (-x) := by
        intro hq
        exact not_le_of_gt (neg_neg_of_pos hx) hq.1
      have hq4 : QuarterPlane4 t (-x) := ⟨by linarith, by linarith, by linarith⟩
      simp [uCandidate, hq1, hq2, hq3, hq4]
  have hrightEq :
      (fun t => uCandidate p t (-x)) =ᶠ[𝓝[Set.Ici x] x]
        fun t => auxFunction1 p t (-x) := by
    filter_upwards [self_mem_nhdsWithin] with t ht
    have htpos : 0 < t := lt_of_lt_of_le hx ht
    have hq : QuarterPlane t (-x) :=
      ⟨htpos.le, le_trans (neg_nonpos.mpr hx.le) htpos.le, neg_le_neg ht⟩
    simp [uCandidate, hq]
  have hleft :
      HasDerivWithinAt (fun t => uCandidate p t (-x))
        (DxuCandidate p x (-x)) (Set.Iic x) x := by
    have hbase :
        HasDerivWithinAt (fun t => auxFunction1 p x (-t))
          (-(DyauxFunction1 p x (-x))) (Set.Iic x) x := by
      have hEq :
          (fun t => auxFunction1 p x (-t)) =ᶠ[𝓝[Set.Iic x] x]
            fun t => vGeTwo p x (-t) := by
        have hmem : {t : ℝ | t ≤ x ∧ -t < a p * x} ∈ 𝓝[Set.Iic x] x := by
          have hlt : -x < a p * x := by
            have hmul : 0 ≤ a p * x := mul_nonneg ha_nonneg hx.le
            linarith
          exact Filter.inter_mem self_mem_nhdsWithin
            (mem_nhdsWithin_of_mem_nhds
              ((continuous_id'.neg).continuousAt.preimage_mem_nhds
                (Iio_mem_nhds hlt)))
        filter_upwards [hmem] with t ht
        rcases ht with ⟨htx, htax⟩
        exact auxFunction1_eq_vGeTwo p hp' x (-t) ⟨hx.le, by linarith, le_of_lt htax⟩
      have hv :
          HasDerivWithinAt (fun t => vGeTwo p x (-t))
            (-(DyvGeTwo p x (-x))) (Set.Iic x) x := by
        have h0 :
            HasDerivAt (fun s => vGeTwo p x s)
              (DyvGeTwo p x (-x)) (-x) :=
          hasDerivAt_vGeTwo_y_on_antidiag_pos p hp x hx
        have hcomp :
            HasDerivAt (fun t => vGeTwo p x (-t))
              (-(DyvGeTwo p x (-x))) x := by
          simpa [mul_comm] using h0.comp x (hasDerivAt_neg x)
        exact hcomp.hasDerivWithinAt
      refine (hv.congr_of_eventuallyEq_of_mem hEq (Set.mem_Iic.mpr le_rfl)).congr_deriv ?_
      exact congrArg Neg.neg (auxFunction1_Dy_eq_DyvGeTwo p hp' x (-x)
        ⟨hx.le, le_rfl, by
          have hmul : 0 ≤ a p * x := mul_nonneg ha_nonneg hx.le
          linarith⟩).symm
    refine (hbase.congr_of_eventuallyEq_of_mem hleftEq (Set.mem_Iic.mpr le_rfl)).congr_deriv ?_
    have hD : DxuCandidate p x (-x) = DxauxFunction1 p x (-x) := by
      simp [DxuCandidate, QuarterPlane, hx.le]
    rw [hD]
    exact (DxauxFunction1_eq_neg_DyauxFunction1_on_antidiag p hp x hx.le).symm
  have hright :
      HasDerivWithinAt (fun t => uCandidate p t (-x))
        (DxuCandidate p x (-x)) (Set.Ici x) x := by
    have hbase :
        HasDerivWithinAt (fun t => auxFunction1 p t (-x))
          (DxauxFunction1 p x (-x)) (Set.Ici x) x := by
      have hEq :
          (fun t => auxFunction1 p t (-x)) =ᶠ[𝓝[Set.Ici x] x]
            fun t => vGeTwo p t (-x) := by
        filter_upwards [self_mem_nhdsWithin] with t ht
        have htpos : 0 ≤ t := le_trans hx.le ht
        exact auxFunction1_eq_vGeTwo p hp' t (-x) ⟨htpos, neg_le_neg ht, by
          exact le_trans (neg_nonpos.mpr hx.le) (mul_nonneg ha_nonneg htpos)⟩
      have hv :
          HasDerivWithinAt (fun t => vGeTwo p t (-x))
            (DxvGeTwo p x (-x)) (Set.Ici x) x :=
        (hasDerivAt_vGeTwo_x_on_antidiag_pos p hp x hx).hasDerivWithinAt
      refine (hv.congr_of_eventuallyEq_of_mem hEq (Set.mem_Ici.mpr le_rfl)).congr_deriv ?_
      exact (auxFunction1_Dx_eq_DxvGeTwo p hp' x (-x)
        ⟨hx.le, le_rfl, by
          have hmul : 0 ≤ a p * x := mul_nonneg ha_nonneg hx.le
          linarith⟩).symm
    refine (hbase.congr_of_eventuallyEq_of_mem hrightEq (Set.mem_Ici.mpr le_rfl)).congr_deriv ?_
    simp [DxuCandidate, QuarterPlane, hx.le]
  simpa [Set.Iic_union_Ici] using hleft.union hright

lemma hasDerivAt_uCandidate_y_on_antidiag_pos (p : ℝ) (hp : 2 < p)
    (x : ℝ) (hx : 0 < x) :
    HasDerivAt (fun s => uCandidate p x s) (DyuCandidate p x (-x)) (-x) := by
  have hp' : 2 ≤ p := by linarith
  have ha_nonneg : 0 ≤ a p := by
    have hpStar : pStar p = p := pStar_eq_self_of_two_le p hp'
    have hp_pos : 0 < p := by linarith
    rw [a, hpStar]
    field_simp [hp_pos.ne]
    nlinarith
  have hleftEq :
      (fun s => uCandidate p x s) =ᶠ[𝓝[Set.Iic (-x)] (-x)]
        fun s => auxFunction1 p (-s) (-x) := by
    filter_upwards [self_mem_nhdsWithin] with s hs
    by_cases hs_eq : s = -x
    · subst s
      have hq : QuarterPlane x (-x) := ⟨hx.le, by linarith, le_rfl⟩
      simp [uCandidate, hq]
    · have hs_lt : s < -x := lt_of_le_of_ne hs hs_eq
      have hq1 : ¬ QuarterPlane x s := by
        intro hq
        exact not_le_of_gt hs_lt hq.2.2
      have hq2 : ¬ QuarterPlane2 x s := by
        intro hq
        exact not_le_of_gt hx hq.1
      have hq3 : ¬ QuarterPlane3 x s := by
        intro hq
        linarith [hq.2.2]
      have hq4 : QuarterPlane4 x s := ⟨by linarith, by linarith, by linarith⟩
      simp [uCandidate, hq1, hq2, hq3, hq4]
  have hrightEq :
      (fun s => uCandidate p x s) =ᶠ[𝓝[Set.Ici (-x)] (-x)]
        fun s => auxFunction1 p x s := by
    have hmem : {s : ℝ | s ≤ x ∧ -x ≤ s} ∈ 𝓝[Set.Ici (-x)] (-x) := by
      exact Filter.inter_mem
        (mem_nhdsWithin_of_mem_nhds (Iic_mem_nhds (by linarith)))
        self_mem_nhdsWithin
    filter_upwards [hmem] with s hs
    rcases hs with ⟨hsx, hnegs⟩
    have hq : QuarterPlane x s := ⟨hx.le, hsx, hnegs⟩
    simp [uCandidate, hq]
  have hleft :
      HasDerivWithinAt (fun s => uCandidate p x s)
        (DyuCandidate p x (-x)) (Set.Iic (-x)) (-x) := by
    have hbase :
        HasDerivWithinAt (fun s => auxFunction1 p (-s) (-x))
          (-(DxauxFunction1 p x (-x))) (Set.Iic (-x)) (-x) := by
      have hEq :
          (fun s => auxFunction1 p (-s) (-x)) =ᶠ[𝓝[Set.Iic (-x)] (-x)]
            fun s => vGeTwo p (-s) (-x) := by
        filter_upwards [self_mem_nhdsWithin] with s hs
        have hspos : 0 ≤ -s := by
          have hs0 : s ≤ 0 := le_trans hs (neg_nonpos.mpr hx.le)
          linarith
        exact auxFunction1_eq_vGeTwo p hp' (-s) (-x) ⟨hspos, by simpa using hs, by
          exact le_trans (neg_nonpos.mpr hx.le) (mul_nonneg ha_nonneg hspos)⟩
      have hv :
          HasDerivWithinAt (fun s => vGeTwo p (-s) (-x))
            (-(DxvGeTwo p x (-x))) (Set.Iic (-x)) (-x) := by
        have h0 :
            HasDerivAt (fun t => vGeTwo p t (-x))
              (DxvGeTwo p x (-x)) x :=
          hasDerivAt_vGeTwo_x_on_antidiag_pos p hp x hx
        have hcomp :
            HasDerivAt (fun s => vGeTwo p (-s) (-x))
              (-(DxvGeTwo p x (-x))) (-x) := by
          have h0' :
              HasDerivAt (fun t => vGeTwo p t (-x))
                (DxvGeTwo p x (-x)) (- -x) := by
            simpa using h0
          convert h0'.comp (-x) (by
            simpa using (hasDerivAt_neg (-x))) using 1 <;>
            simp [Function.comp_def]
        exact hcomp.hasDerivWithinAt
      refine (hv.congr_of_eventuallyEq_of_mem hEq (Set.mem_Iic.mpr le_rfl)).congr_deriv ?_
      exact congrArg Neg.neg (auxFunction1_Dx_eq_DxvGeTwo p hp' x (-x)
        ⟨hx.le, le_rfl, by
          have hmul : 0 ≤ a p * x := mul_nonneg ha_nonneg hx.le
          linarith⟩).symm
    refine (hbase.congr_of_eventuallyEq_of_mem hleftEq (Set.mem_Iic.mpr le_rfl)).congr_deriv ?_
    have hD : DyuCandidate p x (-x) = DyauxFunction1 p x (-x) := by
      simp [DyuCandidate, QuarterPlane, hx.le]
    rw [hD]
    rw [DxauxFunction1_eq_neg_DyauxFunction1_on_antidiag p hp x hx.le]
    simp
  have hright :
      HasDerivWithinAt (fun s => uCandidate p x s)
        (DyuCandidate p x (-x)) (Set.Ici (-x)) (-x) := by
    have hbase :
        HasDerivWithinAt (fun s => auxFunction1 p x s)
          (DyauxFunction1 p x (-x)) (Set.Ici (-x)) (-x) := by
      have hEq :
          (fun s => auxFunction1 p x s) =ᶠ[𝓝[Set.Ici (-x)] (-x)]
            fun s => vGeTwo p x s := by
        have hmem : {s : ℝ | -x ≤ s ∧ s < a p * x} ∈ 𝓝[Set.Ici (-x)] (-x) := by
          have hlt : -x < a p * x := by
            have hmul : 0 ≤ a p * x := mul_nonneg ha_nonneg hx.le
            linarith
          exact Filter.inter_mem self_mem_nhdsWithin
            (mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds hlt))
        filter_upwards [hmem] with s hs
        exact auxFunction1_eq_vGeTwo p hp' x s ⟨hx.le, hs.1, le_of_lt hs.2⟩
      have hv :
          HasDerivWithinAt (fun s => vGeTwo p x s)
            (DyvGeTwo p x (-x)) (Set.Ici (-x)) (-x) :=
        (hasDerivAt_vGeTwo_y_on_antidiag_pos p hp x hx).hasDerivWithinAt
      refine (hv.congr_of_eventuallyEq_of_mem hEq (Set.mem_Ici.mpr le_rfl)).congr_deriv ?_
      exact (auxFunction1_Dy_eq_DyvGeTwo p hp' x (-x)
        ⟨hx.le, le_rfl, by
          have hmul : 0 ≤ a p * x := mul_nonneg ha_nonneg hx.le
          linarith⟩).symm
    refine (hbase.congr_of_eventuallyEq_of_mem hrightEq (Set.mem_Ici.mpr le_rfl)).congr_deriv ?_
    simp [DyuCandidate, QuarterPlane, hx.le]
  simpa [Set.Iic_union_Ici] using hleft.union hright

lemma continuousOn_DxauxFunction1_on_QuarterPlaneOpen (p : ℝ) (hp : 2 ≤ p) :
    ContinuousOn (fun z : ℝ × ℝ => DxauxFunction1 p z.1 z.2)
      {z | QuarterPlaneOpen z.1 z.2} := by
  exact (continuousOn_DxauxFunction1 p hp).mono (by
    intro z hz
    rcases hz with ⟨hz1, hz2, hz3⟩
    exact ⟨le_of_lt hz1, le_of_lt hz2, le_of_lt hz3⟩)

lemma continuousOn_DyauxFunction1_on_QuarterPlaneOpen (p : ℝ) (hp : 2 < p) :
    ContinuousOn (fun z : ℝ × ℝ => DyauxFunction1 p z.1 z.2)
      {z | QuarterPlaneOpen z.1 z.2} := by
  exact (continuousOn_DyauxFunction1 p hp).mono (by
    intro z hz
    rcases hz with ⟨hz1, hz2, hz3⟩
    exact ⟨le_of_lt hz1, le_of_lt hz2, le_of_lt hz3⟩)

lemma continuousOn_DxauxFunction1_on_QuarterPlane (p : ℝ) (hp : 2 ≤ p) :
    ContinuousOn (fun z : ℝ × ℝ => DxauxFunction1 p z.1 z.2)
      {z | QuarterPlane z.1 z.2} := by
  exact continuousOn_DxauxFunction1 p hp

lemma continuousOn_DyauxFunction1_on_QuarterPlane (p : ℝ) (hp : 2 < p) :
    ContinuousOn (fun z : ℝ × ℝ => DyauxFunction1 p z.1 z.2)
      {z | QuarterPlane z.1 z.2} := by
  exact continuousOn_DyauxFunction1 p hp


theorem exists_majorant_geTwo (p : ℝ) (hp : 2 ≤ p) :
    ∃ u : ℝ → ℝ → ℝ,
      (∀ x y, u x y = u y x) ∧
      (∀ x y, u x y = u (-x) (-y)) ∧
      (∀ y, ConcaveOn ℝ Set.univ (fun x => u x y)) ∧
      (∀ x, ConcaveOn ℝ Set.univ (fun y => u x y)) ∧
      (∀ x y, vGeTwo p x y ≤ u x y) ∧
      (∀ x y, x * y ≤ 0 → u x y ≤ 0) ∧
      (∀ x y, A1 p x y → u x y = uA1 p x y) ∧
      (∀ x y, A2 p x y → u x y = vGeTwo p x y) := by
       sorry



end Burkholder
