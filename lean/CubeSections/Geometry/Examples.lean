import CubeSections.Geometry.Attainment

/-! An explicit balanced three-dimensional section of the seven-dimensional cube. -/
noncomputable section
namespace CubeSections

def exampleFrame73 : Frame 7 3 := balancedFrame (by decide) (by decide)

theorem exampleFrame73_isBalanced : IsBalancedSection exampleFrame73 :=
  balancedFrame_isBalanced (by decide) (by decide)

theorem exampleFrame73_volume : sectionVolume exampleFrame73 = 2 * Real.sqrt 3 := by
  rw [exampleFrame73, balancedFrame_volume]
  have hs4 : Real.sqrt (4 : ℝ) = 2 := by
    convert (Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 2)) using 1 <;> norm_num
  have hs : Real.sqrt (12 : ℝ) = 2 * Real.sqrt 3 := by
    calc
      _ = Real.sqrt (4 : ℝ) * Real.sqrt 3 := by
        rw [← Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 4)]
        norm_num
      _ = 2 * Real.sqrt 3 := by rw [hs4]
  convert hs using 1 <;> norm_num [sharpValue]
end CubeSections
