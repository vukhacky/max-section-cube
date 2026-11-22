import CubeSections.Analysis.TransportIntegrand
import CubeSections.Analysis.FrameSlabMeasure
import CubeSections.Geometry.MeasureContracts
import CubeSections.Integer.ContinuousTarget

/-! The geometric Brascamp--Lieb bound from the actual Gaussian change of variables. -/

noncomputable section
open Set MeasureTheory
open scoped BigOperators

namespace CubeSections

theorem frameSlabVolume_le_factor {n k : ℕ} (U : Frame n k) (r : Fin n → ℝ)
    (hr : ∀ i, 0 < r i) :
    frameSlabVolume U r ≤ Real.exp (frameSlabLogFactor U r) := by
  have hi := (frameGaussianTransport_integrable_image_iff U r hr
    (euclideanGaussianDensity k)).1 (euclideanGaussianDensity_integrable k).restrict
  have hlow := setIntegral_ge_of_const_le
    (frameSlabInterior_isOpen U r).measurableSet (frameSlabInterior_mass_ne_top U r)
    (fun x _ => frameTransport_density_jacobian_lower U r hr x) hi
  have hu := setIntegral_le_integral (s := frameGaussianTransport U r '' frameSlabInterior U r)
    (euclideanGaussianDensity_integrable k)
    (ae_of_all _ (fun x => (euclideanGaussianDensity_pos k x).le))
  rw [euclideanGaussianDensity_integral,
    frameGaussianTransport_integral_image U r hr] at hu
  have h : frameSlabVolume U r * Real.exp (-frameSlabLogFactor U r) ≤ 1 :=
    hlow.trans hu
  rw [Real.exp_neg, ← div_eq_mul_inv] at h
  simpa only [one_mul] using (div_le_iff₀ (Real.exp_pos (frameSlabLogFactor U r))).1 h

/-- A harmless positive width at a zero row preserves the full original frame. -/
def cubeFrameRadius {n k : ℕ} (U : Frame n k) (i : Fin n) : ℝ :=
  if leverage U i = 0 then 1 else (2 * Real.sqrt (leverage U i))⁻¹

theorem cubeFrameRadius_pos {n k : ℕ} (U : Frame n k) (i : Fin n) :
    0 < cubeFrameRadius U i := by
  unfold cubeFrameRadius
  split_ifs with hi
  · norm_num
  · have hc := lt_of_le_of_ne (leverage_nonneg U i) (Ne.symm hi)
    positivity

theorem frameSlabInterior_cubeFrameRadius {n k : ℕ} (U : Frame n k) :
    frameSlabInterior U (cubeFrameRadius U) =
      {x : E k | ∀ i, |(U x) i| < (1 : ℝ) / 2} := by
  ext x
  change (∀ i, normalizedFrameCoordinate U i x ∈ Ioo (-cubeFrameRadius U i) (cubeFrameRadius U i)) ↔ _
  simp only [mem_setOf_eq, mem_Ioo, ← abs_lt]
  apply forall_congr'
  intro i
  by_cases hi : leverage U i = 0
  · have hrow := rowVector_eq_zero_of_leverage_eq_zero U i hi
    have hx : (U x) i = 0 := by rw [← rowVector_inner U i x, hrow, inner_zero_left]
    simp [cubeFrameRadius, hi, normalizedFrameCoordinate_eq, hx]
  · have hc : 0 < leverage U i := lt_of_le_of_ne (leverage_nonneg U i) (Ne.symm hi)
    have hs : 0 < Real.sqrt (leverage U i) := Real.sqrt_pos.mpr hc
    rw [cubeFrameRadius, if_neg hi, normalizedFrameCoordinate_eq, abs_div, abs_of_pos hs,
      div_lt_iff₀ hs]
    have heq : (2 * Real.sqrt (leverage U i))⁻¹ * Real.sqrt (leverage U i) = (1 : ℝ) / 2 := by
      field_simp
    rw [heq]

theorem frameSlabVolume_cubeFrameRadius {n k : ℕ} (U : Frame n k) :
    frameSlabVolume U (cubeFrameRadius U) = sectionVolume U := by
  rw [frameSlabVolume, frameSlabInterior_cubeFrameRadius, frame_openSlab_volume]

theorem frameSlabLogFactor_cubeFrameRadius {n k : ℕ} (U : Frame n k) :
    frameSlabLogFactor U (cubeFrameRadius U) = slabLogBound U := by
  unfold frameSlabLogFactor slabLogBound
  have heq (i : Fin n) :
      leverage U i * Real.log (2 * cubeFrameRadius U i) =
        -(leverage U i * Real.log (leverage U i)) / 2 := by
    by_cases hi : leverage U i = 0
    · simp [hi]
    · have hc : 0 < leverage U i := lt_of_le_of_ne (leverage_nonneg U i) (Ne.symm hi)
      have hs : Real.sqrt (leverage U i) ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr hc)
      have hr : 2 * cubeFrameRadius U i = (Real.sqrt (leverage U i))⁻¹ := by
        rw [cubeFrameRadius, if_neg hi]
        field_simp
      rw [hr, Real.log_inv, Real.log_sqrt hc.le]
      ring
  simp_rw [heq]
  rw [← Finset.sum_div, Finset.sum_neg_distrib]

/-- The slab factor bound, with every original row retained, including zero rows. -/
theorem sectionVolume_le_slabBound {n k : ℕ} (U : Frame n k) :
    sectionVolume U ≤ slabBound U := by
  have h := frameSlabVolume_le_factor U (cubeFrameRadius U) (cubeFrameRadius_pos U)
  rwa [frameSlabVolume_cubeFrameRadius, frameSlabLogFactor_cubeFrameRadius] at h

theorem sectionVolume_le_continuousTarget {n k : ℕ} (hk : 1 ≤ k) (hkn : k ≤ n)
    (U : Frame n k) :
    sectionVolume U ≤ ((n : ℝ) / (k : ℝ)) ^ ((k : ℝ) / 2) :=
  (sectionVolume_le_slabBound U).trans (slabBound_le_continuousTarget hk hkn U)

theorem sectionVolume_le_sharp_divisible (q k : ℕ) (hq : 1 ≤ q) (hk : 1 ≤ k)
    (U : Frame (q * k) k) : sectionVolume U ≤ sharpValue (q * k) k :=
  sectionVolume_le_sharp_divisible_of_slabBound q k hq hk U (sectionVolume_le_slabBound U)

end CubeSections
