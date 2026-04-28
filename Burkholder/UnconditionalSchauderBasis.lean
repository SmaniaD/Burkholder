import Mathlib.Analysis.Normed.Field.Basic
import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Module
import Mathlib.Topology.Algebra.Module.LinearMap

noncomputable section

open scoped BigOperators

/--
A Schauder basis of a Banach space.

The sequence `basis` is a Schauder basis when every vector `x` has a unique
norm-convergent expansion
`∑' n, coeff n x • basis n = x`.  The coordinate maps are bundled as
continuous linear maps, which is the natural Banach-space formulation.
-/
structure SchauderBasis (𝕜 E : Type*) [NontriviallyNormedField 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E] [CompleteSpace E] where
  /-- The basis vectors. -/
  basis : ℕ → E
  /-- The continuous coordinate functionals. -/
  coeff : ℕ → E →L[𝕜] 𝕜
  /-- Every vector is the sum of its basis expansion. -/
  hasSum_repr : ∀ x : E, HasSum (fun n : ℕ => coeff n x • basis n) x
  /-- The coefficients in such an expansion are unique. -/
  unique_coeff :
    ∀ (x : E) (a : ℕ → 𝕜), HasSum (fun n : ℕ => a n • basis n) x →
      a = fun n : ℕ => coeff n x

namespace SchauderBasis

variable {𝕜 E : Type*} [NontriviallyNormedField 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E] [CompleteSpace E]

/-- The `n`th coordinate of `x` with respect to a Schauder basis. -/
def coord (b : SchauderBasis 𝕜 E) (n : ℕ) (x : E) : 𝕜 :=
  b.coeff n x

@[simp]
theorem hasSum_repr_apply (b : SchauderBasis 𝕜 E) (x : E) :
    HasSum (fun n : ℕ => b.coeff n x • b.basis n) x :=
  b.hasSum_repr x

/--
A Schauder basis is unconditional if every basis expansion converges to the
same vector after any permutation of its terms.
-/
def IsUnconditional (b : SchauderBasis 𝕜 E) : Prop :=
  ∀ (x : E) (σ : Equiv.Perm ℕ),
    HasSum (fun n : ℕ => b.coeff (σ n) x • b.basis (σ n)) x

end SchauderBasis

/--
An unconditional Schauder basis of a Banach space.

This bundles a Schauder basis together with the assertion that all rearranged
basis expansions converge to the same vector.
-/
structure UnconditionalSchauderBasis (𝕜 E : Type*) [NontriviallyNormedField 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E] [CompleteSpace E] where
  /-- The underlying Schauder basis. -/
  toSchauderBasis : SchauderBasis 𝕜 E
  /-- Unconditional convergence of every basis expansion. -/
  unconditional : toSchauderBasis.IsUnconditional

namespace UnconditionalSchauderBasis

variable {𝕜 E : Type*} [NontriviallyNormedField 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E] [CompleteSpace E]

instance : Coe (UnconditionalSchauderBasis 𝕜 E) (SchauderBasis 𝕜 E) where
  coe b := b.toSchauderBasis

/-- The basis vectors of an unconditional Schauder basis. -/
def basis (b : UnconditionalSchauderBasis 𝕜 E) : ℕ → E :=
  b.toSchauderBasis.basis

/-- The continuous coordinate functionals of an unconditional Schauder basis. -/
def coeff (b : UnconditionalSchauderBasis 𝕜 E) : ℕ → E →L[𝕜] 𝕜 :=
  b.toSchauderBasis.coeff

@[simp]
theorem hasSum_repr_apply (b : UnconditionalSchauderBasis 𝕜 E) (x : E) :
    HasSum (fun n : ℕ => b.coeff n x • b.basis n) x :=
  b.toSchauderBasis.hasSum_repr x

theorem hasSum_rearranged (b : UnconditionalSchauderBasis 𝕜 E)
    (x : E) (σ : Equiv.Perm ℕ) :
    HasSum (fun n : ℕ => b.coeff (σ n) x • b.basis (σ n)) x :=
  b.unconditional x σ

end UnconditionalSchauderBasis
