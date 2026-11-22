import CubeSections.Analysis.FrameQuantile
import CubeSections.Analysis.QuantileMeasurable
import Mathlib.Probability.ConditionalProbability

/-! Finite positive volume and the actual uniform law on the open slab intersection. -/

noncomputable section
open Set MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace CubeSections

@[fun_prop] theorem measurable_frameQuantileCoordinate {n k : ℕ} (U : Frame n k) (r : Fin n → ℝ)
    (i : Fin n) : Measurable (fun x => frameQuantileCoordinates U r x i) :=
  (measurable_intervalGaussianTransport (r i)).comp (normalizedFrameFunctional U i).measurable

@[fun_prop] theorem measurable_frameGaussianTransport {n k : ℕ} (U : Frame n k) (r : Fin n → ℝ) :
    Measurable (frameGaussianTransport U r) := by
  unfold frameGaussianTransport
  fun_prop

theorem frameSlabInterior_bounded {n k : ℕ} (U : Frame n k) (r : Fin n → ℝ) :
    Bornology.IsBounded (frameSlabInterior U r) := by
  let w : Fin n → ℝ := fun i => Real.sqrt (leverage U i) * r i
  let B : Set (E n) := {v | ∀ i, |v i| ≤ w i}
  have hB : IsCompact B := by
    have heq : B = (PiLp.homeomorph 2 (fun _ : Fin n => ℝ)) ⁻¹'
        Icc (fun i => -w i) w := by
      ext v
      simp only [B, mem_setOf_eq, mem_preimage, mem_Icc, Pi.le_def, abs_le]
      constructor
      · intro h
        exact ⟨fun i => (h i).1, fun i => (h i).2⟩
      · rintro ⟨h₁, h₂⟩ i
        exact ⟨h₁ i, h₂ i⟩
    rw [heq]
    exact (PiLp.homeomorph 2 (fun _ : Fin n => ℝ)).isCompact_preimage.mpr isCompact_Icc
  apply (U.isometry.isClosedEmbedding.isCompact_preimage hB).isBounded.subset
  intro x hx i
  change |(U x) i| ≤ Real.sqrt (leverage U i) * r i
  rw [← normalizedFrameCoordinate_scaled U i x, abs_mul, abs_of_nonneg (Real.sqrt_nonneg _)]
  exact mul_le_mul_of_nonneg_left (abs_lt.mpr (hx i)).le (Real.sqrt_nonneg _)

theorem zero_mem_frameSlabInterior {n k : ℕ} (U : Frame n k) (r : Fin n → ℝ)
    (hr : ∀ i, 0 < r i) : (0 : E k) ∈ frameSlabInterior U r := by
  intro i
  simp only [normalizedFrameCoordinate, inner_zero_right, mem_Ioo]
  exact ⟨by linarith [hr i], hr i⟩

theorem frameSlabInterior_mass_pos {n k : ℕ} (U : Frame n k) (r : Fin n → ℝ)
    (hr : ∀ i, 0 < r i) : 0 < volume (frameSlabInterior U r) :=
  (frameSlabInterior_isOpen U r).measure_pos volume ⟨0, zero_mem_frameSlabInterior U r hr⟩

theorem frameSlabInterior_mass_ne_top {n k : ℕ} (U : Frame n k) (r : Fin n → ℝ) :
    volume (frameSlabInterior U r) ≠ ∞ :=
  (frameSlabInterior_bounded U r).measure_lt_top.ne

def frameSlabVolume {n k : ℕ} (U : Frame n k) (r : Fin n → ℝ) : ℝ :=
  (volume (frameSlabInterior U r)).toReal

theorem frameSlabVolume_pos {n k : ℕ} (U : Frame n k) (r : Fin n → ℝ)
    (hr : ∀ i, 0 < r i) : 0 < frameSlabVolume U r :=
  ENNReal.toReal_pos (ne_of_gt (frameSlabInterior_mass_pos U r hr)) (frameSlabInterior_mass_ne_top U r)

/-- Actual uniform law on the open slab intersection. -/
def frameSlabUniform {n k : ℕ} (U : Frame n k) (r : Fin n → ℝ) : Measure (E k) :=
  ProbabilityTheory.cond volume (frameSlabInterior U r)

theorem frameSlabUniform_isProbabilityMeasure {n k : ℕ} (U : Frame n k) (r : Fin n → ℝ)
    (hr : ∀ i, 0 < r i) : IsProbabilityMeasure (frameSlabUniform U r) :=
  cond_isProbabilityMeasure_of_finite (ne_of_gt (frameSlabInterior_mass_pos U r hr))
    (frameSlabInterior_mass_ne_top U r)

theorem frameSlabUniform_ae_mem {n k : ℕ} (U : Frame n k) (r : Fin n → ℝ) :
    ∀ᵐ x ∂frameSlabUniform U r, x ∈ frameSlabInterior U r := by
  exact ae_cond_mem (frameSlabInterior_isOpen U r).measurableSet

end CubeSections
