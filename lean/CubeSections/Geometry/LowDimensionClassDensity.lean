import CubeSections.Geometry.LowDimensionalCentral
import CubeSections.Geometry.FiberDensityCap
import CubeSections.Geometry.DensityOrientation

/-! The geometric density input is unconditional in section dimensions two and
three: the fibers have dimension zero or one, whose central domination and
maximal section bounds are proved directly. -/
noncomputable section
namespace CubeSections

theorem lowDimension_fiber_central {N k : ℕ} (hk : k = 2 ∨ k = 3)
    (V : Frame N (k-2)) (y : E N) : affineMass V y ≤ sectionMass V := by
  rcases hk with rfl | rfl
  · exact affineMass_zero_le_sectionMass V y
  · exact affineMass_line_le_sectionMass V y

theorem lowDimension_fiber_bound {k : ℕ} (hk : k = 2 ∨ k = 3) :
    1 ≤ k-2 → ∀ N : ℕ, ∀ V : Frame N (k-2), sectionVolume V ≤ sharpValue N (k-2) := by
  intro hh N V
  rcases hk with rfl | rfl
  · omega
  · exact line_sectionVolume_le_sharp V

theorem actualClassDensity_two_three {n k : ℕ} (hk : k = 2 ∨ k = 3)
    (hq : 2 ≤ n/k) (U : Frame n k) (hU : IsMaximizingFrame U)
    (hwin : ReciprocalWindow (n/k) U) : Certificates.ActualClassDensity U (n/k) := by
  have hk₂ : 2 ≤ k := by omega
  have hrep := Certificates.rowReplacement_of_maximizing_window (n/k) hq U hU hwin
  have hn : n = (n/k)*k+n%k := by simpa only [Nat.mul_comm] using (Nat.div_add_mod n k).symm
  intro c d hw
  have hcd := classWeight_pos_ne U c d hw
  have hvol := reducedClassFrame_volume_le_radius_mul (n/k) (n%k) (by omega) hk₂
    (Nat.le_of_lt (Nat.mod_lt n (by omega))) hn U hU hrep hwin c d hw
    (lowDimension_fiber_bound hk)
  apply Certificates.sourcePairDensity_orientedPairFrame U _ _ _ (rowClassRep_val_ne U c d hcd)
  exact pairClass_density_cap_of_affine_domination (n/k) U c d hcd
    (lowDimension_fiber_central hk _) hvol

#print axioms lowDimension_fiber_central
#print axioms lowDimension_fiber_bound
#print axioms actualClassDensity_two_three
end CubeSections
