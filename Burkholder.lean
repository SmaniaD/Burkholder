import Mathlib.Probability.Martingale.Basic
import Burkholder.Basic
import Burkholder.Majorants

noncomputable section

open MeasureTheory
open scoped BigOperators

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
  fun n ω => (Finset.range (n + 1)).sum fun i => v i ω * martingaleDiff f i ω

scoped infixl:70 " ⋆ₘ " => martingaleTransform

/--
`g` is the martingale transform of the martingale `f` by a predictable multiplier `v`,
relative to the filtration `ℱ` and measure `μ`.
-/
def IsMartingaleTransform (ℱ : Filtration ℕ mΩ) (μ : Measure Ω)
    (v f g : ℕ → Ω → ℝ) : Prop :=
  IsPredictable ℱ v ∧ Martingale f ℱ μ ∧ g = v ⋆ₘ f

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
A predictable transform of a martingale is a martingale, once the usual
integrability and adaptedness hypotheses for the transformed process are available.

The only integrability assumption specific to the multiplier is that each product
`v (n+1) * (f (n+1) - f n)` is integrable; predictability then pulls `v (n+1)`
out of the conditional expectation.
-/
theorem martingaleTransform_martingale [IsFiniteMeasure μ]
    {ℱ : Filtration ℕ mΩ} {v f : ℕ → Ω → ℝ}
    (hv : IsPredictable ℱ v) (hf : Martingale f ℱ μ)
    (hadapt : StronglyAdapted ℱ (v ⋆ₘ f))
    (hint : ∀ n, Integrable ((v ⋆ₘ f) n) μ)
    (hprod : ∀ n, Integrable (v (n + 1) * (f (n + 1) - f n)) μ) :
    Martingale (v ⋆ₘ f) ℱ μ := by
  refine martingale_of_condExp_sub_eq_zero_nat hadapt hint ?_
  intro n
  have hvmeas : StronglyMeasurable[ℱ n] (v (n + 1)) :=
    (hv.measurable_add_one n).stronglyMeasurable
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
      simpa [hω]

end MeasureTheory
