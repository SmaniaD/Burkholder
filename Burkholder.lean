import Mathlib.Probability.Martingale.Basic
import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
import Burkholder.Basic
import Burkholder.Majorants
import Burkholder.UnconditionalSchauderBasisNontrivialField
noncomputable section

open MeasureTheory
open scoped BigOperators NNReal ENNReal

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
theorem Lp_Burkholder_inequality_martingaleTransform
    (p : ℝ≥0∞) (hp_one : 1 < p) (hp_top : p ≠ ∞) :
    ∃ C : ℝ≥0∞, C ≠ ∞ ∧
      ∀ {Ω : Type*} [mΩ : MeasurableSpace Ω] {μ : Measure Ω} [IsFiniteMeasure μ]
        {ℱ : Filtration ℕ mΩ} {v f : ℕ → Ω → ℝ},
        IsStronglyPredictable ℱ v →
        Martingale f ℱ μ →
        (∀ n, MemLp (f n) p μ) →
        (∀ n, ∀ᵐ ω ∂μ, |v n ω| ≤ 1) →
        ∀ n, eLpNorm ((v ⋆ₘ f) n) p μ ≤ C * eLpNorm (f n) p μ := by
  sorry

end MeasureTheory
