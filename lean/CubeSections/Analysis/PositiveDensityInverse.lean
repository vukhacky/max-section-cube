import CubeSections.Analysis.PositiveDensityLaw

/-! The actual C1 inverse transport from the standard Gaussian to a continuous
strictly positive probability density. -/

noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal ContDiff Topology

namespace CubeSections

def positiveDensityHomeomorph (f : ℝ → ℝ) (hc : Continuous f) (hi : Integrable f)
    (hp : ∀ x, 0 < f x) (hm : (∫ x, f x) = 1) : ℝ ≃ₜ ℝ :=
  (StrictMono.orderIsoOfSurjective (densityGaussianTransport f)
    (strictMono_densityGaussianTransport hc hi hp hm)
    (densityGaussianTransport_surjective hc hi hp hm)).toHomeomorph

def positiveDensityInverse (f : ℝ → ℝ) (hc : Continuous f) (hi : Integrable f)
    (hp : ∀ x, 0 < f x) (hm : (∫ x, f x) = 1) : ℝ → ℝ :=
  (positiveDensityHomeomorph f hc hi hp hm).symm

@[simp] theorem positiveDensityInverse_transport {f : ℝ → ℝ} (hc : Continuous f) (hi : Integrable f)
    (hp : ∀ x, 0 < f x) (hm : (∫ x, f x) = 1) (x : ℝ) :
    positiveDensityInverse f hc hi hp hm (densityGaussianTransport f x) = x :=
  (positiveDensityHomeomorph f hc hi hp hm).symm_apply_apply x

@[simp] theorem densityGaussianTransport_inverse {f : ℝ → ℝ} (hc : Continuous f) (hi : Integrable f)
    (hp : ∀ x, 0 < f x) (hm : (∫ x, f x) = 1) (x : ℝ) :
    densityGaussianTransport f (positiveDensityInverse f hc hi hp hm x) = x :=
  (positiveDensityHomeomorph f hc hi hp hm).apply_symm_apply x

theorem continuous_positiveDensityInverse {f : ℝ → ℝ} (hc : Continuous f) (hi : Integrable f)
    (hp : ∀ x, 0 < f x) (hm : (∫ x, f x) = 1) :
    Continuous (positiveDensityInverse f hc hi hp hm) :=
  (positiveDensityHomeomorph f hc hi hp hm).symm.continuous

theorem measurable_positiveDensityInverse {f : ℝ → ℝ} (hc : Continuous f) (hi : Integrable f)
    (hp : ∀ x, 0 < f x) (hm : (∫ x, f x) = 1) :
    Measurable (positiveDensityInverse f hc hi hp hm) :=
  (continuous_positiveDensityInverse hc hi hp hm).measurable

theorem strictMono_positiveDensityInverse {f : ℝ → ℝ} (hc : Continuous f) (hi : Integrable f)
    (hp : ∀ x, 0 < f x) (hm : (∫ x, f x) = 1) :
    StrictMono (positiveDensityInverse f hc hi hp hm) := by
  intro x y hxy
  apply (strictMono_densityGaussianTransport hc hi hp hm).lt_iff_lt.mp
  simpa only [densityGaussianTransport_inverse] using hxy

theorem densityCDF_positiveDensityInverse {f : ℝ → ℝ} (hc : Continuous f) (hi : Integrable f)
    (hp : ∀ x, 0 < f x) (hm : (∫ x, f x) = 1) (x : ℝ) :
    densityCDF f (positiveDensityInverse f hc hi hp hm x) = standardGaussianCDF x := by
  have h := CDF_densityGaussianTransport hc hi hp hm (positiveDensityInverse f hc hi hp hm x)
  simpa only [densityGaussianTransport_inverse] using h.symm

theorem hasDerivAt_positiveDensityInverse {f : ℝ → ℝ} (hc : Continuous f) (hi : Integrable f)
    (hp : ∀ x, 0 < f x) (hm : (∫ x, f x) = 1) (x : ℝ) :
    HasDerivAt (positiveDensityInverse f hc hi hp hm)
      (gaussianPDFReal 0 1 x / f (positiveDensityInverse f hc hi hp hm x)) x := by
  have h := HasDerivAt.of_local_left_inverse
    (continuous_positiveDensityInverse hc hi hp hm).continuousAt
    (hasDerivAt_densityGaussianTransport hc hi hp hm (positiveDensityInverse f hc hi hp hm x))
    (ne_of_gt (densityGaussianSlope_pos hp _))
    (Filter.Eventually.of_forall (densityGaussianTransport_inverse hc hi hp hm))
  simpa only [densityGaussianSlope, densityGaussianTransport_inverse, inv_div] using h

theorem positiveDensityInverse_deriv_pos {f : ℝ → ℝ} (hc : Continuous f) (hi : Integrable f)
    (hp : ∀ x, 0 < f x) (hm : (∫ x, f x) = 1) (x : ℝ) :
    0 < deriv (positiveDensityInverse f hc hi hp hm) x := by
  rw [(hasDerivAt_positiveDensityInverse hc hi hp hm x).deriv]
  exact div_pos (gaussianPDFReal_pos 0 1 x (by norm_num)) (hp _)

theorem contDiff_positiveDensityInverse {f : ℝ → ℝ} (hc : Continuous f) (hi : Integrable f)
    (hp : ∀ x, 0 < f x) (hm : (∫ x, f x) = 1) :
    ContDiff ℝ 1 (positiveDensityInverse f hc hi hp hm) := by
  apply contDiff_one_iff_deriv.mpr
  refine ⟨fun x => (hasDerivAt_positiveDensityInverse hc hi hp hm x).differentiableAt, ?_⟩
  have heq : deriv (positiveDensityInverse f hc hi hp hm) =
      fun x => gaussianPDFReal 0 1 x / f (positiveDensityInverse f hc hi hp hm x) :=
    funext (fun x => (hasDerivAt_positiveDensityInverse hc hi hp hm x).deriv)
  rw [heq]
  exact continuous_standardGaussianPDF.div
    (hc.comp (continuous_positiveDensityInverse hc hi hp hm)) (fun _ => ne_of_gt (hp _))

/-- The constructed inverse transports the actual standard Gaussian to `f dx`. -/
theorem positiveDensityInverse_map_law {f : ℝ → ℝ} (hc : Continuous f) (hi : Integrable f)
    (hp : ∀ x, 0 < f x) (hm : (∫ x, f x) = 1) :
    (gaussianReal 0 1).map (positiveDensityInverse f hc hi hp hm) = positiveDensityLaw f := by
  rw [← densityGaussianTransport_map_law hc hi hp hm,
    Measure.map_map (measurable_positiveDensityInverse hc hi hp hm)
      (measurable_densityGaussianTransport hc hi hp hm)]
  have heq : positiveDensityInverse f hc hi hp hm ∘ densityGaussianTransport f = id :=
    funext (positiveDensityInverse_transport hc hi hp hm)
  rw [heq, Measure.map_id]

theorem positiveDensityInverse_measurePreserving {f : ℝ → ℝ} (hc : Continuous f) (hi : Integrable f)
    (hp : ∀ x, 0 < f x) (hm : (∫ x, f x) = 1) :
    MeasurePreserving (positiveDensityInverse f hc hi hp hm) (gaussianReal 0 1) (positiveDensityLaw f) :=
  ⟨measurable_positiveDensityInverse hc hi hp hm, positiveDensityInverse_map_law hc hi hp hm⟩

end CubeSections
