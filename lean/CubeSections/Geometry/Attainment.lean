import CubeSections.Geometry.BlockVolume
import CubeSections.Integer.Balanced

/-!
# Unconditional attainment of the balanced target

This module proves the attainment target by an explicit isometric embedding.
It does not assert the universal upper bound or its converse rigidity statement.
-/

noncomputable section
open scoped BigOperators

namespace CubeSections

theorem BlockData.sectionVolume_frame_of_balanced {n k : ℕ} (d : BlockData n k)
    (h : d.IsBalanced) : sectionVolume d.frame = sharpValue n k := by
  rw [d.sectionVolume_frame_eq_sqrt_prod, d.prod_blockSize_of_balanced h]
  rfl

/-- An explicit balanced frame; coordinate signs are chosen positive. -/
def balancedFrame {n k : ℕ} (hk : 1 ≤ k) (hkn : k ≤ n) : Frame n k :=
  (balancedBlockData hk hkn).frame

theorem balancedFrame_isBalanced {n k : ℕ} (hk : 1 ≤ k) (hkn : k ≤ n) :
    IsBalancedSection (balancedFrame hk hkn) :=
  (balancedBlockData hk hkn).isBalancedSection_frame (balancedBlockData_isBalanced hk hkn)

theorem balancedFrame_volume {n k : ℕ} (hk : 1 ≤ k) (hkn : k ≤ n) :
    sectionVolume (balancedFrame hk hkn) = sharpValue n k :=
  (balancedBlockData hk hkn).sectionVolume_frame_of_balanced (balancedBlockData_isBalanced hk hkn)

/-- Every target value is attained by a signed balanced coordinate-block section. -/
theorem balancedSectionAttains : AttainmentStatement := by
  intro n k hk hkn
  exact ⟨balancedFrame hk hkn, balancedFrame_isBalanced hk hkn, balancedFrame_volume hk hkn⟩

end CubeSections
