import CubeSections.Analysis.PositiveGaussianTalagrand
import CubeSections.Analysis.GaussianMonotoneStein

/-! Unconditional scalar Gaussian quadratic transportation for continuous
strictly positive normalized Lebesgue densities with finite second moment
and finite actual KL. The coupling is the actual inverse-quantile graph.
This does not assert the arbitrary-law or finite-dimensional T2 contract.
-/
noncomputable section
open MeasureTheory ProbabilityTheory InformationTheory
open scoped NNReal ENNReal ContDiff
namespace CubeSections

/-- The actual inverse quantile has quadratic displacement at most twice the
actual Gaussian relative entropy. No Stein or compact-support hypothesis remains. -/
theorem positiveDensityInverse_cost_le_twice_klDiv
    (f : ℝ → ℝ) (hc : Continuous f) (hi : Integrable f)
    (hp : ∀ x, 0 < f x) (hm : (∫ x, f x)=1)
    (hL2 : MemLp id 2 (positiveDensityLaw f))
    (hKL : klDiv (positiveDensityLaw f) (gaussianReal 0 1) ≠ (⊤ : ℝ≥0∞)) :
    (∫ x, (positiveDensityInverse f hc hi hp hm x-x)^2 ∂gaussianReal 0 1) ≤
      2*(klDiv (positiveDensityLaw f) (gaussianReal 0 1)).toReal := by
  let g := positiveDensityInverse f hc hi hp hm
  have hd : ∀ x, HasDerivAt g (deriv g x) x := fun x =>
    ((contDiff_positiveDensityInverse hc hi hp hm).differentiable (by norm_num) x).hasDerivAt
  have hpos : ∀ x, 0 ≤ deriv g x := fun x =>
    (positiveDensityInverse_deriv_pos hc hi hp hm x).le
  have hg : MemLp g 2 (gaussianReal 0 1) :=
    memLp_positiveDensityInverse_two f hc hi hp hm hL2
  exact positiveDensityInverse_cost_le_twice_klDiv_of_stein f hc hi hp hm hL2 hKL
    (integrable_gaussian_deriv_of_nonneg g (deriv g) hd hpos hg)
    (gaussian_monotone_stein g (deriv g) hd hpos hg)

/-- Genuine one-dimensional Gaussian transportation for the specified positive
continuous density, including an explicit probability coupling and cost L1. -/
theorem gaussian_quadratic_transport_positiveDensity
    (f : ℝ → ℝ) (hc : Continuous f) (hi : Integrable f)
    (hp : ∀ x, 0 < f x) (hm : (∫ x, f x)=1)
    (hL2 : MemLp id 2 (positiveDensityLaw f))
    (hKL : klDiv (positiveDensityLaw f) (gaussianReal 0 1) ≠ (⊤ : ℝ≥0∞)) :
    ∃ π : Measure (ℝ × ℝ), IsProbabilityMeasure π ∧
      π.map Prod.fst = positiveDensityLaw f ∧ π.map Prod.snd = gaussianReal 0 1 ∧
      Integrable (fun p : ℝ × ℝ => |p.1-p.2|^2) π ∧
      (∫ p : ℝ × ℝ, |p.1-p.2|^2 ∂π) ≤
        2*(klDiv (positiveDensityLaw f) (gaussianReal 0 1)).toReal := by
  refine ⟨positiveDensityInverseCoupling f hc hi hp hm,
    positiveDensityInverseCoupling_probability f hc hi hp hm,
    positiveDensityInverseCoupling_fst f hc hi hp hm,
    positiveDensityInverseCoupling_snd f hc hi hp hm,
    positiveDensityInverseCoupling_cost_integrable f hc hi hp hm hL2, ?_⟩
  rw [positiveDensityInverseCoupling_cost]
  exact positiveDensityInverse_cost_le_twice_klDiv f hc hi hp hm hL2 hKL

#print axioms positiveDensityInverse_cost_le_twice_klDiv
#print axioms gaussian_quadratic_transport_positiveDensity
end CubeSections
