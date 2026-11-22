import CubeSections.Analysis.TransportDensity
import CubeSections.Analysis.TransportIntegrand
import Mathlib.MeasureTheory.Measure.LogLikelihoodRatio

/-! Actual Radon–Nikodym and log-likelihood identities for the slab transport. -/

noncomputable section
open Set MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace CubeSections

def frameTransportGaussianDensity {n k : ℕ} (U : Frame n k) (r : Fin n → ℝ)
    (hr : ∀ i, 0 < r i) (y : E k) : ℝ≥0∞ :=
  frameTransportLebesgueDensity U r hr y / ENNReal.ofReal (euclideanGaussianDensity k y)

@[fun_prop] theorem measurable_frameTransportGaussianDensity {n k : ℕ} (U : Frame n k) (r : Fin n → ℝ)
    (hr : ∀ i, 0 < r i) : Measurable (frameTransportGaussianDensity U r hr) :=
  (measurable_frameTransportLebesgueDensity U r hr).div (euclideanGaussianDensity_measurable k).ennreal_ofReal

theorem frameTransportedLaw_eq_gaussian_withDensity {n k : ℕ} (U : Frame n k) (r : Fin n → ℝ)
    (hr : ∀ i, 0 < r i) :
    frameTransportedLaw U r = (stdGaussian (E k)).withDensity (frameTransportGaussianDensity U r hr) := by
  rw [stdGaussian_eq_euclideanGaussianDensity, ← withDensity_mul _
    (euclideanGaussianDensity_measurable k).ennreal_ofReal (measurable_frameTransportGaussianDensity U r hr),
    frameTransportedLaw_eq_withDensity U r hr]
  congr 1
  funext y
  exact (ENNReal.mul_div_cancel
    (ne_of_gt (ENNReal.ofReal_pos.mpr (euclideanGaussianDensity_pos k y))) ENNReal.ofReal_ne_top).symm

theorem frameTransportedLaw_absolutelyContinuous_gaussian {n k : ℕ} (U : Frame n k) (r : Fin n → ℝ)
    (hr : ∀ i, 0 < r i) : frameTransportedLaw U r ≪ stdGaussian (E k) := by
  rw [frameTransportedLaw_eq_gaussian_withDensity U r hr]
  exact withDensity_absolutelyContinuous _ _

theorem rnDeriv_frameTransportedLaw {n k : ℕ} (U : Frame n k) (r : Fin n → ℝ)
    (hr : ∀ i, 0 < r i) :
    (frameTransportedLaw U r).rnDeriv (stdGaussian (E k)) =ᵐ[stdGaussian (E k)]
      frameTransportGaussianDensity U r hr := by
  rw [frameTransportedLaw_eq_gaussian_withDensity U r hr]
  exact Measure.rnDeriv_withDensity _ (measurable_frameTransportGaussianDensity U r hr)

theorem log_frameTransportGaussianDensity_comp {n k : ℕ} (U : Frame n k) (r : Fin n → ℝ)
    (hr : ∀ i, 0 < r i) {x : E k} (hx : x ∈ frameSlabInterior U r) :
    Real.log (frameTransportGaussianDensity U r hr (frameGaussianTransport U r x)).toReal =
      (frameSlabLogFactor U r - Real.log (frameSlabVolume U r)) -
        frameTransportLogProduction U r x - frameTransportResidualEnergy U r x / 2 := by
  have hV := frameSlabVolume_pos U r hr
  have hJ := frameGaussianJacobian_pos U r hr x
  have hG := euclideanGaussianDensity_pos k (frameGaussianTransport U r x)
  rw [frameTransportGaussianDensity, frameTransportLebesgueDensity,
    indicator_of_mem (show frameGaussianTransport U r x ∈ frameGaussianTransport U r '' frameSlabInterior U r
      from ⟨x, hx, rfl⟩), frameInverseJacobianDensity,
    frameGaussianInverse_transport U r hr hx, ENNReal.toReal_div,
    ENNReal.toReal_ofReal (inv_nonneg.mpr (mul_nonneg hV.le hJ.le)), ENNReal.toReal_ofReal hG.le,
    Real.log_div (inv_ne_zero (mul_ne_zero (ne_of_gt hV) (ne_of_gt hJ))) (ne_of_gt hG),
    Real.log_inv, Real.log_mul (ne_of_gt hV) (ne_of_gt hJ)]
  have h := frameTransport_log_density_jacobian U r hr x
  linarith

/-- The actual logarithmic density identity, almost everywhere for the actual
uniform slab law. Every measure and transport in this statement is constructed. -/
theorem frameTransport_llr_comp {n k : ℕ} (U : Frame n k) (r : Fin n → ℝ)
    (hr : ∀ i, 0 < r i) :
    (fun x => llr (frameTransportedLaw U r) (stdGaussian (E k)) (frameGaussianTransport U r x))
      =ᵐ[frameSlabUniform U r] fun x =>
        (frameSlabLogFactor U r - Real.log (frameSlabVolume U r)) -
          frameTransportLogProduction U r x - frameTransportResidualEnergy U r x / 2 := by
  have hν := (frameTransportedLaw_absolutelyContinuous_gaussian U r hr).ae_le
    (rnDeriv_frameTransportedLaw U r hr)
  have hsrc := ae_of_ae_map (measurable_frameGaussianTransport U r).aemeasurable hν
  filter_upwards [hsrc, frameSlabUniform_ae_mem U r] with x hx hxK
  rw [llr, hx]
  exact log_frameTransportGaussianDensity_comp U r hr hxK

end CubeSections
