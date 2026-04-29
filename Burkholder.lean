import Mathlib.Probability.Martingale.Basic
import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
import Burkholder.Basic
import Burkholder.Majorants
import Burkholder.UnconditionalSchauderBasisNontrivialField
noncomputable section

open MeasureTheory
open scoped BigOperators NNReal ENNReal

namespace Burkholder

/-- The conjugate exponent helper, re-exported in the `Burkholder` namespace. -/
def q (p : ℝ) : ℝ :=
  Majorants.q p

/-- `pStar = max p q`, re-exported in the `Burkholder` namespace. -/
def pStar (p : ℝ) : ℝ :=
  Majorants.pStar p

/-- The Burkholder function `v`, imported from the majorant development. -/
def v (p x y : ℝ) : ℝ :=
  Majorants.v p x y

/-- The package of properties saying that `u` is a Burkholder majorant for exponent `p`. -/
def IsMajorant (p : ℝ) (u : ℝ → ℝ → ℝ) : Prop :=
  (∀ x y, ∃ d_u_dx d_u_dy : ℝ,
    ∀ h k, h * k = 0 →
      u (x + h) (y + k) ≤ u x y + d_u_dx * h + d_u_dy * k) ∧
  (∀ x y, v p x y ≤ u x y) ∧
  (∀ x y, x * y ≤ 0 → u x y ≤ 0) ∧
  (∀ x y, p ≠ 2 ∧ x * y = 0 ∧ (x, y) ≠ (0, 0) → u x y < 0)

/-- A chosen Burkholder majorant for `p > 1`. -/
def u (p : ℝ) (hp : p > 1) : ℝ → ℝ → ℝ :=
  Classical.choose (Majorants.exists_majorant_p_g_1 p hp)

theorem u_isMajorant (p : ℝ) (hp : p > 1) :
    IsMajorant p (u p hp) := by
  simpa [u, IsMajorant, v] using
    Classical.choose_spec (Majorants.exists_majorant_p_g_1 p hp)

end Burkholder

namespace MeasureTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω}

/--
The martingale difference sequence associated to a discrete real-valued process.

With this convention, `martingaleDiff f 0 = f 0` and
`martingaleDiff f (n + 1) = f (n + 1) - f n`.
-/
def martingaleDiff (f : ℕ → Ω → ℝ) : ℕ → Ω → ℝ
  | 0 => f 0
  | n + 1 => f (n + 1) - f n

/--
The discrete martingale transform of `f` by the multiplier process `v`.

If `f` has difference sequence `d`, then the transformed process has
difference sequence `v n * d n`.
-/
def martingaleTransform (v f : ℕ → Ω → ℝ) : ℕ → Ω → ℝ :=
  fun n => (Finset.range (n + 1)).sum fun i => v i * martingaleDiff f i

scoped infixl:70 " ⋆ₘ " => martingaleTransform

/--
`g` is the martingale transform of the martingale `f` by a strongly predictable multiplier `v`,
relative to the filtration `ℱ` and measure `μ`.
-/
def IsMartingaleTransform (ℱ : Filtration ℕ mΩ) (μ : Measure Ω)
    (v f g : ℕ → Ω → ℝ) : Prop :=
  IsStronglyPredictable ℱ v ∧ Martingale f ℱ μ ∧ g = v ⋆ₘ f

@[simp]
theorem martingaleTransform_zero (v f : ℕ → Ω → ℝ) :
    (v ⋆ₘ f) 0 = v 0 * f 0 := by
  ext ω
  simp [martingaleTransform, martingaleDiff]

theorem martingaleTransform_succ_sub (v f : ℕ → Ω → ℝ) (n : ℕ) :
    (v ⋆ₘ f) (n + 1) - (v ⋆ₘ f) n =
      v (n + 1) * (f (n + 1) - f n) := by
  ext ω
  simp [martingaleTransform, martingaleDiff, Finset.sum_range_succ]

/--
A strongly predictable transform of a martingale is a martingale, once the usual
integrability and adaptedness hypotheses for the transformed process are available.

The only integrability assumption specific to the multiplier is that each product
`v (n+1) * (f (n+1) - f n)` is integrable; predictability then pulls `v (n+1)`
out of the conditional expectation.
-/
theorem martingaleTransform_martingale {μ : Measure Ω} [IsFiniteMeasure μ]
  {ℱ : Filtration ℕ mΩ} {v f : ℕ → Ω → ℝ}
  (hv : IsStronglyPredictable ℱ v) (hf : Martingale f ℱ μ)
  (hbounded :  ∃ C, ∀ n ω, |v n ω| ≤ C) :
  Martingale (v ⋆ₘ f) ℱ μ := by
  rcases hbounded with ⟨C, hC⟩
  have hv_bound : ∀ n ω, ‖v n ω‖ ≤ |C| := by
    intro n ω
    simpa [Real.norm_eq_abs] using (hC n ω).trans (le_abs_self C)
  have hv_adapted : StronglyAdapted ℱ v := IsStronglyPredictable.stronglyAdapted hv
  have hdiff_integrable : ∀ n, Integrable (martingaleDiff f n) μ := by
    intro n
    cases n with
    | zero =>
        simpa [martingaleDiff] using hf.integrable 0
    | succ n =>
        simpa [martingaleDiff] using (hf.integrable (n + 1)).sub (hf.integrable n)
  have hdiff_measurable_le :
      ∀ {i n : ℕ}, i ≤ n → StronglyMeasurable[ℱ n] (martingaleDiff f i) := by
    intro i n hin
    cases i with
    | zero =>
        simpa [martingaleDiff] using
          hf.stronglyAdapted.stronglyMeasurable_le (Nat.zero_le n)
    | succ i =>
        have hi_succ : i + 1 ≤ n := hin
        have hi : i ≤ n := Nat.le_trans (Nat.le_succ i) hi_succ
        simpa [martingaleDiff] using
          (hf.stronglyAdapted.stronglyMeasurable_le hi_succ).sub
            (hf.stronglyAdapted.stronglyMeasurable_le hi)
  have hprod_all : ∀ n, Integrable (v n * martingaleDiff f n) μ := by
    intro n
    have hv_meas : AEStronglyMeasurable (v n) μ :=
      ((hv_adapted n).mono (ℱ.le n)).aestronglyMeasurable
    have hb : ∀ᵐ ω ∂μ, ‖v n ω‖ ≤ |C| := ae_of_all _ (hv_bound n)
    simpa [Pi.smul_apply, smul_eq_mul] using
      (hdiff_integrable n).bdd_smul |C| hv_meas hb
  have hadapt : StronglyAdapted ℱ (v ⋆ₘ f) := by
    intro n
    simpa [martingaleTransform, Finset.sum_apply] using
      (Finset.stronglyMeasurable_sum (Finset.range (n + 1)) fun i hi => by
        have hin : i ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
        exact (hv_adapted.stronglyMeasurable_le hin).mul (hdiff_measurable_le hin))
  have hint : ∀ n, Integrable ((v ⋆ₘ f) n) μ := by
    intro n
    simpa [martingaleTransform, Finset.sum_apply] using
      (integrable_finsetSum' (Finset.range (n + 1)) fun i _ => hprod_all i)
  have hprod : ∀ n, Integrable (v (n + 1) * (f (n + 1) - f n)) μ := by
    intro n
    simpa [martingaleDiff] using hprod_all (n + 1)
  refine martingale_of_condExp_sub_eq_zero_nat hadapt hint ?_
  intro n
  have hvmeas : StronglyMeasurable[ℱ n] (v (n + 1)) :=
    IsStronglyPredictable.measurable_add_one hv n
  have hdiff_int : Integrable (f (n + 1) - f n) μ :=
    (hf.integrable (n + 1)).sub (hf.integrable n)
  have hdiff_zero :
      μ[f (n + 1) - f n | ℱ n] =ᵐ[μ] 0 := by
    have hnext : μ[f (n + 1) | ℱ n] =ᵐ[μ] f n :=
      hf.condExp_ae_eq (Nat.le_succ n)
    have hcurr : μ[f n | ℱ n] =ᵐ[μ] f n := by
      rw [condExp_of_stronglyMeasurable (ℱ.le n) (hf.stronglyMeasurable n) (hf.integrable n)]
    calc
      μ[f (n + 1) - f n | ℱ n]
          =ᵐ[μ] μ[f (n + 1) | ℱ n] - μ[f n | ℱ n] :=
            condExp_sub (hf.integrable (n + 1)) (hf.integrable n) (ℱ n)
      _ =ᵐ[μ] f n - f n := hnext.sub hcurr
      _ =ᵐ[μ] 0 := by simp
  have hpull :
      μ[v (n + 1) * (f (n + 1) - f n) | ℱ n]
        =ᵐ[μ] v (n + 1) * μ[f (n + 1) - f n | ℱ n] :=
    condExp_mul_of_stronglyMeasurable_left hvmeas (hprod n) hdiff_int
  calc
    μ[(v ⋆ₘ f) (n + 1) - (v ⋆ₘ f) n | ℱ n]
        =ᵐ[μ] μ[v (n + 1) * (f (n + 1) - f n) | ℱ n] := by
          rw [martingaleTransform_succ_sub]
    _ =ᵐ[μ] v (n + 1) * μ[f (n + 1) - f n | ℱ n] := hpull
    _ =ᵐ[μ] 0 := by
      filter_upwards [hdiff_zero] with ω hω
      simp [hω]

/--
Theorem 2.2, inequality (2.13): martingale transforms by strongly predictable
multipliers bounded by `1` are bounded on `L^p`, for `1 < p < ∞`.

This is stated at each finite time `n` for the discrete transform `v ⋆ₘ f`.
-/

def plusOne (w : ℕ → Ω → ℝ) : ℕ → Ω → ℝ :=
  fun n ω => w n ω + 1

def minusOne (w : ℕ → Ω → ℝ) : ℕ → Ω → ℝ :=
  fun n ω => w n ω - 1



scoped notation "X_{" n "}[" w "," f "]" => ((plusOne w) ⋆ₘ f) n
scoped notation "Y_{" n "}[" w "," f "]" => ((minusOne w) ⋆ₘ f) n





lemma   inequality_for_transform_differences
    (p : ℝ≥0∞) (_hp_one : 1 < p) (_hp_top : p ≠ ∞) :
    ∃ C : ℝ≥0∞, C ≠ ∞ ∧
      ∀ {Ω : Type*} [mΩ : MeasurableSpace Ω] {μ : Measure Ω} [IsFiniteMeasure μ]
        {ℱ : Filtration ℕ mΩ} {w f : ℕ → Ω → ℝ},
        IsStronglyPredictable ℱ w →
        Martingale f ℱ μ →
        (∀ n, MemLp (f n) p μ) →
        (∀ n, ∀ᵐ ω ∂μ, |w n ω| ≤ 1) →
        (∀ n, ∀ᵐ ω ∂μ,
          (X_{n+1}[w, f] ω -X_{n}[w, f] ω) * (Y_{n+1}[w, f] ω -Y_{n}[w, f] ω) ≤ 0) ∧
        (∀ᵐ ω ∂μ,
          (X_{0}[w, f] ω *
              Y_{0}[w, f] ω ≤ 0)) := by
  refine ⟨0, by simp, ?_⟩
  intro Ω mΩ μ hμ ℱ w f hw hf hfLp hw_bound
  constructor
  · intro n
    filter_upwards [hw_bound (n + 1)] with ω hwω
    have hplus :
        X_{n+1}[w, f] ω - X_{n}[w, f] ω =
          (w (n + 1) ω + 1) * (f (n + 1) ω - f n ω) := by
      change ((plusOne w) ⋆ₘ f) (n + 1) ω - ((plusOne w) ⋆ₘ f) n ω =
        (w (n + 1) ω + 1) * (f (n + 1) ω - f n ω)
      simpa [plusOne] using congrFun (martingaleTransform_succ_sub (plusOne w) f n) ω
    have hminus :
        Y_{n+1}[w, f] ω - Y_{n}[w, f] ω =
          (w (n + 1) ω - 1) * (f (n + 1) ω - f n ω) := by
      change ((minusOne w) ⋆ₘ f) (n + 1) ω - ((minusOne w) ⋆ₘ f) n ω =
        (w (n + 1) ω - 1) * (f (n + 1) ω - f n ω)
      simpa [minusOne] using congrFun (martingaleTransform_succ_sub (minusOne w) f n) ω
    have hsq_nonneg : 0 ≤ (f (n + 1) ω - f n ω) ^ 2 :=
      sq_nonneg (f (n + 1) ω - f n ω)
    have hw_sq_succ : w (n + 1) ω ^ 2 ≤ 1 := by
      have hneg : -1 ≤ w (n + 1) ω := (abs_le.mp hwω).1
      have hpos : w (n + 1) ω ≤ 1 := (abs_le.mp hwω).2
      nlinarith [sq_nonneg (w (n + 1) ω - 1),
        sq_nonneg (w (n + 1) ω + 1)]
    calc
      (X_{n+1}[w, f] ω - X_{n}[w, f] ω) *
          (Y_{n+1}[w, f] ω - Y_{n}[w, f] ω)
          = ((w (n + 1) ω) ^ 2 - 1) *
              ((f (n + 1) ω - f n ω) ^ 2) := by
            rw [hplus, hminus]
            ring
      _ ≤ 0 := by nlinarith
  · filter_upwards [hw_bound 0] with ω hwω
    have hw_sq : w 0 ω ^ 2 ≤ 1 := by
      have hneg : -1 ≤ w 0 ω := (abs_le.mp hwω).1
      have hpos : w 0 ω ≤ 1 := (abs_le.mp hwω).2
      nlinarith [sq_nonneg (w 0 ω - 1), sq_nonneg (w 0 ω + 1)]
    have hsq_nonneg : 0 ≤ f 0 ω ^ 2 := sq_nonneg (f 0 ω)
    calc
      X_{0}[w, f] ω *
          Y_{0}[w, f] ω
          = ((w 0 ω) ^ 2 - 1) * (f 0 ω ^ 2) := by
            simp [plusOne, minusOne, martingaleTransform, martingaleDiff]
            ring
      _ ≤ 0 := by nlinarith


/-- The chosen majorant dominates the Burkholder function `v`. -/
lemma burkholder_v_le_u (p : ℝ) (hp : p > 1) (x y : ℝ) :
    Burkholder.v p x y ≤ Burkholder.u p hp x y :=
  (Burkholder.u_isMajorant p hp).2.1 x y

/-- The chosen majorant is nonpositive on the region `x * y ≤ 0`. -/
lemma burkholder_u_nonpos_of_mul_nonpos (p : ℝ) (hp : p > 1)
    {x y : ℝ} (hxy : x * y ≤ 0) :
    Burkholder.u p hp x y ≤ 0 :=
  (Burkholder.u_isMajorant p hp).2.2.1 x y hxy

/--
The tangency/concavity property of the chosen majorant. This is the formal
version of the step
`u(x + h, y + k) ≤ u(x, y) + u_x(x,y) h + u_y(x,y) k`
when `h * k = 0`.
-/
lemma burkholder_u_tangent_step (p : ℝ) (hp : p > 1) (x y h k : ℝ)
    (hhk : h * k = 0) :
    ∃ d_u_dx d_u_dy : ℝ,
      Burkholder.u p hp (x + h) (y + k) ≤
        Burkholder.u p hp x y + d_u_dx * h + d_u_dy * k := by
  rcases (Burkholder.u_isMajorant p hp).1 x y with ⟨d_u_dx, d_u_dy, htangent⟩
  exact ⟨d_u_dx, d_u_dy, htangent h k hhk⟩

noncomputable def burkholder_tangentDx (p : ℝ) (hp : p > 1)
    {w f : ℕ → Ω → ℝ} (n : ℕ)
    (hcross : ∀ ω,
      (X_{n+1}[w, f] ω - X_{n}[w, f] ω) *
        (Y_{n+1}[w, f] ω - Y_{n}[w, f] ω) = 0) :
    Ω → ℝ :=
  fun ω =>
    Classical.choose
      (burkholder_u_tangent_step p hp (X_{n}[w, f] ω) (Y_{n}[w, f] ω)
        (X_{n+1}[w, f] ω - X_{n}[w, f] ω)
        (Y_{n+1}[w, f] ω - Y_{n}[w, f] ω) (hcross ω))

noncomputable def burkholder_tangentDy (p : ℝ) (hp : p > 1)
    {w f : ℕ → Ω → ℝ} (n : ℕ)
    (hcross : ∀ ω,
      (X_{n+1}[w, f] ω - X_{n}[w, f] ω) *
        (Y_{n+1}[w, f] ω - Y_{n}[w, f] ω) = 0) :
    Ω → ℝ :=
  fun ω =>
    Classical.choose
      (Classical.choose_spec
        (burkholder_u_tangent_step p hp (X_{n}[w, f] ω) (Y_{n}[w, f] ω)
          (X_{n+1}[w, f] ω - X_{n}[w, f] ω)
          (Y_{n+1}[w, f] ω - Y_{n}[w, f] ω) (hcross ω)))

lemma burkholder_u_XY_tangent_bound (p : ℝ) (hp : p > 1)
    {w f : ℕ → Ω → ℝ} (n : ℕ)
    (hcross : ∀ ω,
      (X_{n+1}[w, f] ω - X_{n}[w, f] ω) *
        (Y_{n+1}[w, f] ω - Y_{n}[w, f] ω) = 0) :
    ∀ ω,
      Burkholder.u p hp (X_{n+1}[w, f] ω) (Y_{n+1}[w, f] ω) ≤
        Burkholder.u p hp (X_{n}[w, f] ω) (Y_{n}[w, f] ω) +
          burkholder_tangentDx p hp n hcross ω *
            (X_{n+1}[w, f] ω - X_{n}[w, f] ω) +
          burkholder_tangentDy p hp n hcross ω *
            (Y_{n+1}[w, f] ω - Y_{n}[w, f] ω) := by
  intro ω
  have htangent :=
    Classical.choose_spec
      (Classical.choose_spec
        (burkholder_u_tangent_step p hp (X_{n}[w, f] ω) (Y_{n}[w, f] ω)
          (X_{n+1}[w, f] ω - X_{n}[w, f] ω)
          (Y_{n+1}[w, f] ω - Y_{n}[w, f] ω) (hcross ω)))
  simpa [burkholder_tangentDx, burkholder_tangentDy, sub_add_cancel] using htangent

lemma burkholder_u_XY_integral_succ_le (p : ℝ) (hp : p > 1)
    {μ : Measure Ω} {w f : ℕ → Ω → ℝ} (n : ℕ)
    (hcross : ∀ ω,
      (X_{n+1}[w, f] ω - X_{n}[w, f] ω) *
        (Y_{n+1}[w, f] ω - Y_{n}[w, f] ω) = 0)
    (hu_succ_int : Integrable
      (fun ω => Burkholder.u p hp (X_{n+1}[w, f] ω) (Y_{n+1}[w, f] ω)) μ)
    (hu_int : Integrable
      (fun ω => Burkholder.u p hp (X_{n}[w, f] ω) (Y_{n}[w, f] ω)) μ)
    (hlinear_int : Integrable
      (fun ω =>
        burkholder_tangentDx p hp n hcross ω *
          (X_{n+1}[w, f] ω - X_{n}[w, f] ω) +
        burkholder_tangentDy p hp n hcross ω *
          (Y_{n+1}[w, f] ω - Y_{n}[w, f] ω)) μ)
    (hlinear_nonpos :
      (∫ ω,
        burkholder_tangentDx p hp n hcross ω *
          (X_{n+1}[w, f] ω - X_{n}[w, f] ω) +
        burkholder_tangentDy p hp n hcross ω *
          (Y_{n+1}[w, f] ω - Y_{n}[w, f] ω) ∂μ) ≤ 0) :
    (∫ ω, Burkholder.u p hp (X_{n+1}[w, f] ω) (Y_{n+1}[w, f] ω) ∂μ) ≤
      ∫ ω, Burkholder.u p hp (X_{n}[w, f] ω) (Y_{n}[w, f] ω) ∂μ := by
  let linear : Ω → ℝ := fun ω =>
    burkholder_tangentDx p hp n hcross ω *
      (X_{n+1}[w, f] ω - X_{n}[w, f] ω) +
    burkholder_tangentDy p hp n hcross ω *
      (Y_{n+1}[w, f] ω - Y_{n}[w, f] ω)
  have hbound : ∀ᵐ ω ∂μ,
      Burkholder.u p hp (X_{n+1}[w, f] ω) (Y_{n+1}[w, f] ω) ≤
        Burkholder.u p hp (X_{n}[w, f] ω) (Y_{n}[w, f] ω) + linear ω := by
    filter_upwards with ω
    have h := burkholder_u_XY_tangent_bound p hp n hcross ω
    dsimp [linear]
    linarith
  have hright_int : Integrable
      (fun ω => Burkholder.u p hp (X_{n}[w, f] ω) (Y_{n}[w, f] ω) + linear ω) μ :=
    hu_int.add hlinear_int
  calc
    (∫ ω, Burkholder.u p hp (X_{n+1}[w, f] ω) (Y_{n+1}[w, f] ω) ∂μ)
        ≤ ∫ ω, Burkholder.u p hp (X_{n}[w, f] ω) (Y_{n}[w, f] ω) + linear ω ∂μ :=
          integral_mono_ae hu_succ_int hright_int hbound
    _ = (∫ ω, Burkholder.u p hp (X_{n}[w, f] ω) (Y_{n}[w, f] ω) ∂μ) +
          ∫ ω, linear ω ∂μ := by
            rw [integral_add hu_int hlinear_int]
    _ ≤ ∫ ω, Burkholder.u p hp (X_{n}[w, f] ω) (Y_{n}[w, f] ω) ∂μ := by
      have hlin : ∫ ω, linear ω ∂μ ≤ 0 := by
        simpa [linear] using hlinear_nonpos
      exact add_le_of_nonpos_right hlin

/-- Applying `v ≤ u` pointwise to the transform variables `X_n,Y_n`. -/
lemma burkholder_v_XY_le_u_XY_pointwise (p : ℝ) (hp : p > 1)
    {w f : ℕ → Ω → ℝ} (n : ℕ) (ω : Ω) :
    Burkholder.v p (X_{n}[w, f] ω) (Y_{n}[w, f] ω) ≤
      Burkholder.u p hp (X_{n}[w, f] ω) (Y_{n}[w, f] ω) :=
  burkholder_v_le_u p hp _ _

/-- Applying `v ≤ u` after taking averages. -/
lemma burkholder_v_XY_le_u_XY (p : ℝ) (hp : p > 1)
    {μ : Measure Ω} {w f : ℕ → Ω → ℝ} (n : ℕ)
    (hv_int : Integrable
      (fun ω => Burkholder.v p (X_{n}[w, f] ω) (Y_{n}[w, f] ω)) μ)
    (hu_int : Integrable
      (fun ω => Burkholder.u p hp (X_{n}[w, f] ω) (Y_{n}[w, f] ω)) μ) :
    (∫ ω, Burkholder.v p (X_{n}[w, f] ω) (Y_{n}[w, f] ω) ∂μ) ≤
      ∫ ω, Burkholder.u p hp (X_{n}[w, f] ω) (Y_{n}[w, f] ω) ∂μ := by
  exact integral_mono_ae hv_int hu_int
    (ae_of_all _ fun ω => burkholder_v_XY_le_u_XY_pointwise p hp n ω)





/-- The initial inequality `u(X_0,Y_0) ≤ 0` from `X_0 Y_0 ≤ 0` a.s. -/
lemma burkholder_u_X0Y0_nonpos_ae (p : ℝ) (hp : p > 1)
    {μ : Measure Ω} {w f : ℕ → Ω → ℝ}
    (hXY0 : ∀ᵐ ω ∂μ, X_{0}[w, f] ω * Y_{0}[w, f] ω ≤ 0) :
    ∀ᵐ ω ∂μ,
      Burkholder.u p hp (X_{0}[w, f] ω) (Y_{0}[w, f] ω) ≤ 0 := by
  filter_upwards [hXY0] with ω hxy
  exact burkholder_u_nonpos_of_mul_nonpos p hp hxy

/-- Consequently, `v(X_n,Y_n) ≤ 0` a.s. whenever `X_n Y_n ≤ 0` a.s. -/
lemma burkholder_v_XY_nonpos_ae (p : ℝ) (hp : p > 1)
    {μ : Measure Ω} {w f : ℕ → Ω → ℝ}
    (hXY : ∀ n, ∀ᵐ ω ∂μ, X_{n}[w, f] ω * Y_{n}[w, f] ω ≤ 0) :
    ∀ n, ∀ᵐ ω ∂μ,
      Burkholder.v p (X_{n}[w, f] ω) (Y_{n}[w, f] ω) ≤ 0 := by
  intro n
  filter_upwards [hXY n] with ω hxy
  exact le_trans (burkholder_v_XY_le_u_XY_pointwise p hp n ω)
    (burkholder_u_nonpos_of_mul_nonpos p hp hxy)





theorem Lp_Burkholder_inequality_martingaleTransform
    (p : ℝ≥0∞) (hp_one : 1 < p) (hp_top : p ≠ ∞) :
    ∃ C : ℝ≥0∞, C ≠ ∞ ∧
      ∀ {Ω : Type*} [mΩ : MeasurableSpace Ω] {μ : Measure Ω} [IsFiniteMeasure μ]
        {ℱ : Filtration ℕ mΩ} {w f : ℕ → Ω → ℝ},
        IsStronglyPredictable ℱ w →
        Martingale f ℱ μ →
        (∀ n, MemLp (f n) p μ) →
        (∀ n, ∀ᵐ ω ∂μ, |w n ω| ≤ 1) →
        ∀ n, eLpNorm ((w ⋆ₘ f) n) p μ ≤
          ENNReal.ofReal (Burkholder.pStar p.toReal - 1) * eLpNorm (f n) p μ := by
  sorry

end MeasureTheory
