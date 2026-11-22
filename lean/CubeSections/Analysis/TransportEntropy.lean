import CubeSections.Analysis.TransportLikelihood
import CubeSections.Analysis.TransportIntegrability
import Mathlib.InformationTheory.KullbackLeibler.Basic

/-! Exact finite Kullback–Leibler decomposition for the actual uniform slab law
and the actual Gaussian frame transport. No transport-cost inequality is assumed here. -/

noncomputable section
open Set MeasureTheory ProbabilityTheory InformationTheory
open scoped ENNReal

namespace CubeSections

def frameSlabDeficit {n k : ℕ} (U : Frame n k) (r : Fin n → ℝ) : ℝ :=
  frameSlabLogFactor U r - Real.log (frameSlabVolume U r)

/-- The actual KL divergence; finiteness is proved below for positive slab widths. -/
def frameTransportEntropy {n k : ℕ} (U : Frame n k) (r : Fin n → ℝ) : ℝ :=
  (klDiv (frameTransportedLaw U r) (stdGaussian (E k))).toReal

theorem integrable_frameTransport_llr {n k : ℕ} (U : Frame n k) (r : Fin n → ℝ)
    (hr : ∀ i, 0 < r i) :
    Integrable (llr (frameTransportedLaw U r) (stdGaussian (E k))) (frameTransportedLaw U r) := by
  letI := frameSlabUniform_isProbabilityMeasure U r hr
  have hR : Integrable (fun x => (frameSlabLogFactor U r - Real.log (frameSlabVolume U r)) -
      frameTransportLogProduction U r x - frameTransportResidualEnergy U r x / 2) (frameSlabUniform U r) :=
    ((integrable_const _).sub (integrable_frameTransportLogProduction U r hr)).sub
      ((integrable_frameTransportResidualEnergy U r hr).div_const 2)
  have hcomp : Integrable (fun x =>
      llr (frameTransportedLaw U r) (stdGaussian (E k)) (frameGaussianTransport U r x)) (frameSlabUniform U r) :=
    hR.congr (frameTransport_llr_comp U r hr).symm
  exact (integrable_map_measure (measurable_llr _ _).aestronglyMeasurable
    (measurable_frameGaussianTransport U r).aemeasurable).mpr hcomp

theorem frameTransport_klDiv_ne_top {n k : ℕ} (U : Frame n k) (r : Fin n → ℝ)
    (hr : ∀ i, 0 < r i) : klDiv (frameTransportedLaw U r) (stdGaussian (E k)) ≠ ∞ :=
  klDiv_ne_top (frameTransportedLaw_absolutelyContinuous_gaussian U r hr) (integrable_frameTransport_llr U r hr)

theorem frameTransportEntropy_nonneg {n k : ℕ} (U : Frame n k) (r : Fin n → ℝ) :
    0 ≤ frameTransportEntropy U r := ENNReal.toReal_nonneg

theorem frameTransportEntropy_eq_integral_llr {n k : ℕ} (U : Frame n k) (r : Fin n → ℝ)
    (hr : ∀ i, 0 < r i) :
    frameTransportEntropy U r =
      ∫ y, llr (frameTransportedLaw U r) (stdGaussian (E k)) y ∂frameTransportedLaw U r := by
  letI := frameTransportedLaw_isProbabilityMeasure U r hr
  exact toReal_klDiv_of_measure_eq (frameTransportedLaw_absolutelyContinuous_gaussian U r hr) (by simp)

/-- The manuscript's exact entropy decomposition, with actual constructed objects
and every integrability assertion discharged. -/
theorem frameTransport_entropy_decomposition {n k : ℕ} (U : Frame n k) (r : Fin n → ℝ)
    (hr : ∀ i, 0 < r i) :
    frameSlabDeficit U r = frameTransportEntropy U r +
      (∫ x, frameTransportLogProduction U r x ∂frameSlabUniform U r) +
      (1 / 2 : ℝ) * (∫ x, frameTransportResidualEnergy U r x ∂frameSlabUniform U r) := by
  letI := frameSlabUniform_isProbabilityMeasure U r hr
  have hD : frameTransportEntropy U r = frameSlabDeficit U r -
      (∫ x, frameTransportLogProduction U r x ∂frameSlabUniform U r) -
      (∫ x, frameTransportResidualEnergy U r x ∂frameSlabUniform U r) / 2 := by
    rw [frameTransportEntropy_eq_integral_llr U r hr, frameTransportedLaw,
      integral_map (measurable_frameGaussianTransport U r).aemeasurable (measurable_llr _ _).aestronglyMeasurable]
    change (∫ x, llr (frameTransportedLaw U r) (stdGaussian (E k))
      (frameGaussianTransport U r x) ∂frameSlabUniform U r) = _
    rw [integral_congr_ae (frameTransport_llr_comp U r hr)]
    have h1 : Integrable (fun x => (frameSlabLogFactor U r - Real.log (frameSlabVolume U r)) -
        frameTransportLogProduction U r x) (frameSlabUniform U r) :=
      (integrable_const _).sub (integrable_frameTransportLogProduction U r hr)
    rw [integral_sub h1 ((integrable_frameTransportResidualEnergy U r hr).div_const 2),
      integral_sub (integrable_const (frameSlabLogFactor U r - Real.log (frameSlabVolume U r)))
        (integrable_frameTransportLogProduction U r hr), integral_div]
    simp only [integral_const, probReal_univ, one_smul, frameSlabDeficit]
  linarith

theorem frameTransportEntropy_le_deficit {n k : ℕ} (U : Frame n k) (r : Fin n → ℝ)
    (hr : ∀ i, 0 < r i) : frameTransportEntropy U r ≤ frameSlabDeficit U r := by
  rw [frameTransport_entropy_decomposition U r hr]
  have hJ := integral_nonneg (frameTransportLogProduction_nonneg U r)
    (μ := frameSlabUniform U r)
  have hP := integral_nonneg (frameTransportResidualEnergy_nonneg U r)
    (μ := frameSlabUniform U r)
  linarith

theorem frameSlabDeficit_nonneg {n k : ℕ} (U : Frame n k) (r : Fin n → ℝ)
    (hr : ∀ i, 0 < r i) : 0 ≤ frameSlabDeficit U r :=
  (frameTransportEntropy_nonneg U r).trans (frameTransportEntropy_le_deficit U r hr)

end CubeSections
