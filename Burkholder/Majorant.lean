import Mathlib

noncomputable section

namespace Burkholder

def q (p : ℝ) : ℝ := p / (p - 1)

def pStar (p : ℝ) : ℝ := max p (q p)

def v (p x y : ℝ) : ℝ :=
  Real.rpow (|((x + y) / 2)|) p
    - Real.rpow (|pStar p - 1|) p * Real.rpow (|((x - y) / 2)|) p

def vGeTwo (p x y : ℝ) : ℝ :=
  Real.rpow (|((x + y) / 2)|) p
    - Real.rpow (p - 1) p * Real.rpow (|((x - y) / 2)|) p

def a (p : ℝ) : ℝ := 1 - 2 / p

def alpha (p : ℝ) : ℝ := p * Real.rpow ((p - 1) / p) (p - 1)

def A1 (p x y : ℝ) : Prop := 0 < x ∧ a p * x < y ∧ y < x

def A2 (p x y : ℝ) : Prop := 0 < x ∧ -x < y ∧ y < a p * x

def uA1 (p x y : ℝ) : ℝ :=
  alpha p * Real.rpow x p * (1 - (p * (x - y)) / (2 * x))

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
