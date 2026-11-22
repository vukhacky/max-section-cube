import CubeSections.Geometry.Blocks

/-!
# Exact volume of a signed coordinate-block section

The pullback of the unit cube is an explicit Cartesian product of intervals.
The resulting volume formula holds for every surjective block assignment,
without an extremality or balance hypothesis.
-/

noncomputable section
open Set MeasureTheory
open scoped BigOperators ENNReal

namespace CubeSections
namespace BlockData

variable {n k : ℕ} (d : BlockData n k)

theorem abs_frame_apply (x : E k) (i : Fin n) :
    |d.frame x i| = |x (d.block i)| / Real.sqrt (d.blockSize (d.block i)) := by
  rw [d.frame_apply, abs_div, abs_mul, d.abs_sign, one_mul,
    abs_of_nonneg (Real.sqrt_nonneg _)]

theorem abs_frame_le_half_iff (x : E k) (i : Fin n) :
    |d.frame x i| ≤ (1 : ℝ) / 2 ↔
      |x (d.block i)| ≤ Real.sqrt (d.blockSize (d.block i)) / 2 := by
  rw [d.abs_frame_apply, div_le_iff₀ (d.sqrt_blockSize_pos _)]
  have hm : (1 / 2 : ℝ) * Real.sqrt (d.blockSize (d.block i)) =
      Real.sqrt (d.blockSize (d.block i)) / 2 := by ring
  rw [hm]

theorem frame_mem_cube_iff (x : E k) :
    d.frame x ∈ cube n ↔ ∀ j, |x j| ≤ Real.sqrt (d.blockSize j) / 2 := by
  change (∀ i, |d.frame x i| ≤ (1 : ℝ) / 2) ↔ _
  constructor
  · intro h j
    obtain ⟨i, rfl⟩ := d.onto j
    exact (d.abs_frame_le_half_iff x i).mp (h i)
  · intro h i
    exact (d.abs_frame_le_half_iff x i).mpr (h (d.block i))

def lower : Fin k → ℝ := fun j => -(Real.sqrt (d.blockSize j) / 2)
def upper : Fin k → ℝ := fun j => Real.sqrt (d.blockSize j) / 2

theorem lower_le_upper : d.lower ≤ d.upper := by
  intro j
  exact neg_le_self (div_nonneg (Real.sqrt_nonneg _) (by norm_num))

theorem upper_sub_lower (j : Fin k) : d.upper j - d.lower j = Real.sqrt (d.blockSize j) := by
  unfold lower upper
  ring

theorem frame_preimage_cube :
    d.frame ⁻¹' cube n =
      (WithLp.ofLp : E k → Fin k → ℝ) ⁻¹' Set.Icc d.lower d.upper := by
  ext x
  rw [Set.mem_preimage, d.frame_mem_cube_iff]
  simp only [Set.mem_preimage, Set.mem_Icc, Pi.le_def, lower, upper, abs_le]
  constructor
  · intro h
    exact ⟨fun j => (h j).1, fun j => (h j).2⟩
  · rintro ⟨h₁, h₂⟩ j
    exact ⟨h₁ j, h₂ j⟩

theorem sectionMass_frame :
    sectionMass d.frame = ∏ j : Fin k, ENNReal.ofReal (Real.sqrt (d.blockSize j)) := by
  unfold sectionMass
  rw [d.frame_preimage_cube]
  rw [(PiLp.volume_preserving_ofLp (Fin k)).measure_preimage
    measurableSet_Icc.nullMeasurableSet]
  rw [Real.volume_Icc_pi]
  simp only [d.upper_sub_lower]

theorem sectionVolume_frame :
    sectionVolume d.frame = ∏ j : Fin k, Real.sqrt (d.blockSize j) := by
  unfold sectionVolume
  rw [d.sectionMass_frame, ENNReal.toReal_prod]
  apply Finset.prod_congr rfl
  intro j hj
  exact ENNReal.toReal_ofReal (Real.sqrt_nonneg _)

theorem sectionVolume_frame_eq_sqrt_prod :
    sectionVolume d.frame = Real.sqrt ((∏ j : Fin k, d.blockSize j : ℕ) : ℝ) := by
  rw [d.sectionVolume_frame, Nat.cast_prod]
  exact (Real.sqrt_prod Finset.univ (fun j hj => Nat.cast_nonneg (d.blockSize j))).symm

end BlockData
end CubeSections
