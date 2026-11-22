import CubeSections.Analysis.FrameTransportRegularDensity
import CubeSections.Analysis.FrameTransportSurjective

/-! Unconditional regularity of the actual frame-transported probability law.
Global coverage and openness are proved for the actual quantile frame map;
there is no regularity, surjectivity, or transport-cost premise in these results. -/

noncomputable section
open Set MeasureTheory

namespace CubeSections

theorem frameGaussianInverse_continuous {n k : ℕ} (U : Frame n k) (r : Fin n → ℝ)
    (hr : ∀ i, 0 < r i) : Continuous (frameGaussianInverse U r hr) :=
  frameGaussianInverse_continuous_of_image_open U r hr
    (frameGaussianTransport_image_eq_univ U r hr)
    (fun _ hs hsub => frameGaussianTransport_isOpen_image U r hr hs hsub)

theorem frameTransportRealDensity_continuous {n k : ℕ} (U : Frame n k) (r : Fin n → ℝ)
    (hr : ∀ i, 0 < r i) : Continuous (frameTransportRealDensity U r hr) :=
  frameTransportRealDensity_continuous_of_inverse U r hr
    (frameGaussianTransport_image_eq_univ U r hr) (frameGaussianInverse_continuous U r hr)

theorem frameTransportRealDensity_gaussianDominated {n k : ℕ} (U : Frame n k) (r : Fin n → ℝ)
    (hr : ∀ i, 0 < r i) : GaussianDominated (frameTransportRealDensity U r hr) :=
  frameTransportRealDensity_gaussianDominated_of_image_eq_univ U r hr
    (frameGaussianTransport_image_eq_univ U r hr)

theorem frameTransportRealDensity_integral {n k : ℕ} (U : Frame n k) (r : Fin n → ℝ)
    (hr : ∀ i, 0 < r i) : (∫ y, frameTransportRealDensity U r hr y) = 1 :=
  frameTransportRealDensity_integral_of_image_eq_univ U r hr
    (frameGaussianTransport_image_eq_univ U r hr) (frameTransportRealDensity_continuous U r hr)

theorem frameTransportedLaw_eq_realDensity {n k : ℕ} (U : Frame n k) (r : Fin n → ℝ)
    (hr : ∀ i, 0 < r i) :
    frameTransportedLaw U r = euclideanDensityLaw (frameTransportRealDensity U r hr) :=
  frameTransportedLaw_eq_realDensity_of_image_eq_univ U r hr
    (frameGaussianTransport_image_eq_univ U r hr)

/-- The actual transported law has a normalized continuous positive density
with a Gaussian upper envelope in every finite dimension, including zero. -/
theorem frameTransportedLaw_regular_density {n k : ℕ} (U : Frame n k) (r : Fin n → ℝ)
    (hr : ∀ i, 0 < r i) :
    ∃ f : E k → ℝ, Continuous f ∧ GaussianDominated f ∧ (∀ y, 0 < f y) ∧
      (∫ y, f y) = 1 ∧ frameTransportedLaw U r = euclideanDensityLaw f :=
  frameTransportedLaw_regular_density_of_image_open U r hr
    (frameGaussianTransport_image_eq_univ U r hr)
    (fun _ hs hsub => frameGaussianTransport_isOpen_image U r hr hs hsub)

#print axioms frameGaussianInverse_continuous
#print axioms frameTransportRealDensity_continuous
#print axioms frameTransportRealDensity_gaussianDominated
#print axioms frameTransportRealDensity_integral
#print axioms frameTransportedLaw_eq_realDensity
#print axioms frameTransportedLaw_regular_density

end CubeSections
