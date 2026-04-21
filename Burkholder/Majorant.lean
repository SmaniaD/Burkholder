import Mathlib

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






def uCandidate (p x y : ℝ) : ℝ :=
  by
    classical
    exact
      if A1 p x y then
        uA1 p x y
      else if A2 p x y then
        vGeTwo p x y
      else if A1 p (-x) (-y) then
        uA1 p (-x) (-y)
      else if A2 p (-x) (-y) then
        vGeTwo p x y
      else if A1 p y x then
        uA1 p y x
      else if A2 p y x then
        vGeTwo p y x
      else if A1 p (-y) (-x) then
        uA1 p (-y) (-x)
      else if A2 p (-y) (-x) then
        vGeTwo p y x
      else if x=y then
        alpha p * Real.rpow |x| p
      else if x=-y then
        vGeTwo p x y
      else if y = (a p) * x  then
        vGeTwo p x y
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

def QuarterPlane (x y : ℝ) : Prop := 0 ≤ x ∧ y ≤ x ∧ -x ≤ y

def auxFunction1 (p x y : ℝ) : ℝ :=
    by
    classical
    exact
      if  closureA1 p x y then
         uA1 p x y
      else if closureA2 p x y then
          vGeTwo p x y
        else 0


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
    simpa using exists_majorant_geTwo_assumption p hp


end Burkholder
