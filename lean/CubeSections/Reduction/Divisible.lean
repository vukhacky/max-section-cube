import CubeSections.Analysis.ZeroDeficitCoupling
import CubeSections.Analysis.SlabVolumeBound
import CubeSections.Reduction.LargeQuotient
import CubeSections.Geometry.Endpoints

/-! Unconditional sharp bound and complete range equality classification in
every divisible dimension. No Talagrand or Brunn--Minkowski premise remains. -/

noncomputable section
namespace CubeSections

theorem sectionVolume_eq_sharp_divisible_iff (q k : ℕ) (hq : 1 ≤ q) (hk : 1 ≤ k)
    (U : Frame (q * k) k) :
    sectionVolume U = sharpValue (q * k) k ↔ IsBalancedSection U := by
  by_cases hq1 : q = 1
  · subst q
    revert U
    rw [one_mul]
    intro U
    exact ⟨fun _ => fullDimension_isBalancedSection U (by omega),
      fun _ => fullDimension_sectionVolume_eq_sharp U (by omega)⟩
  constructor
  · intro heq
    have hmax : IsMaximizingFrame U := by
      intro V
      rw [heq]
      exact sectionVolume_le_sharp_divisible q k hq hk V
    have hδ := slabDeficit_zero_of_divisible_equality q k hq hk U
      (sectionVolume_le_slabBound U) heq
    have hzero := gramAngularDefect_eq_zero_of_slabDeficit_zero U hδ
    apply divisible_equality_isBalanced_of_angular q k (by omega) hk U hmax _ heq
    rw [hzero, hδ]
    norm_num
  · exact sectionVolume_eq_sharp_of_isBalancedSection U

theorem maximalSection_divisible (q k : ℕ) (hq : 1 ≤ q) (hk : 1 ≤ k)
    (U : Frame (q * k) k) :
    sectionVolume U ≤ sharpValue (q * k) k ∧
      (sectionVolume U = sharpValue (q * k) k ↔ IsBalancedSection U) :=
  ⟨sectionVolume_le_sharp_divisible q k hq hk U,
    sectionVolume_eq_sharp_divisible_iff q k hq hk U⟩

theorem maximalSection_of_dvd {n k : ℕ} (hk : 1 ≤ k) (hkn : k ≤ n) (hdiv : k ∣ n)
    (U : Frame n k) :
    sectionVolume U ≤ sharpValue n k ∧
      (sectionVolume U = sharpValue n k ↔ IsBalancedSection U) := by
  obtain ⟨q, rfl⟩ := hdiv
  have hq : 1 ≤ q := by
    by_contra h
    have hz : q = 0 := by omega
    simp only [hz, mul_zero] at hkn
    omega
  have h : ∀ m : ℕ, m = q * k → ∀ V : Frame m k,
      sectionVolume V ≤ sharpValue m k ∧
        (sectionVolume V = sharpValue m k ↔ IsBalancedSection V) := by
    intro m hm
    subst m
    exact maximalSection_divisible q k hq hk
  exact h (k * q) (Nat.mul_comm k q) U

#print axioms sectionVolume_eq_sharp_divisible_iff
#print axioms maximalSection_divisible
#print axioms maximalSection_of_dvd

end CubeSections
