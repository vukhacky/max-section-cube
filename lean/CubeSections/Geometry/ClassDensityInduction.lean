import CubeSections.Geometry.FiberDensityCap
import CubeSections.Geometry.DensityOrientation

/-! Interacting-class density from central-volume domination and the
lower-dimensional induction hypothesis. Rank-two coarea and the endpoint
geometry connect these hypotheses to the required density bound. -/
noncomputable section
namespace CubeSections

theorem actualClassDensity_of_midpointBM_induction {n k : ℕ} (q r : ℕ)
    (hq : 2 ≤ q) (hk : 2 ≤ k) (hr : r ≤ k) (hn : n = q*k+r)
    (U : Frame n k) (hU : IsMaximizingFrame U) (hwin : ReciprocalWindow q U)
    (hBM : MidpointBrunnMinkowski (k-2))
    (hIH : 1 ≤ k-2 → ∀ N : ℕ, ∀ V : Frame N (k-2), sectionVolume V ≤ sharpValue N (k-2)) :
    Certificates.ActualClassDensity U q := by
  intro c d hw
  have hcd := classWeight_pos_ne U c d hw
  have hrep := Certificates.rowReplacement_of_maximizing_window q hq U hU hwin
  have hvol := reducedClassFrame_volume_le_radius_mul q r (by omega) hk hr hn U hU hrep hwin c d hw hIH
  exact Certificates.sourcePairDensity_orientedPairFrame U _ _ _
    (rowClassRep_val_ne U c d hcd) _ _ _
    (pairClass_density_cap_of_central_bound q U c d hcd hBM hvol)

theorem actualClassDensity_of_midpointBM_induction_quotient {n k : ℕ}
    (hk : 2 ≤ k) (hq : 2 ≤ n/k) (U : Frame n k) (hU : IsMaximizingFrame U)
    (hwin : ReciprocalWindow (n/k) U) (hBM : MidpointBrunnMinkowski (k-2))
    (hIH : 1 ≤ k-2 → ∀ N : ℕ, ∀ V : Frame N (k-2), sectionVolume V ≤ sharpValue N (k-2)) :
    Certificates.ActualClassDensity U (n/k) := by
  apply actualClassDensity_of_midpointBM_induction (n/k) (n%k) hq hk
    (Nat.le_of_lt (Nat.mod_lt n (by omega))) _ U hU hwin hBM hIH
  simpa only [Nat.mul_comm] using (Nat.div_add_mod n k).symm

theorem actualClassDensity_of_midpointBM_restricted_induction {n k : ℕ} (q r : ℕ)
    (hq : 2 ≤ q) (hk : 2 ≤ k) (hr : r ≤ k) (hn : n = q*k+r)
    (U : Frame n k) (hU : IsMaximizingFrame U) (hwin : ReciprocalWindow q U)
    (hBM : MidpointBrunnMinkowski (k-2))
    (hIH : 1 ≤ k-2 → ∀ N : ℕ, 2*(k-2) ≤ N →
      ∀ V : Frame N (k-2), sectionVolume V ≤ sharpValue N (k-2)) :
    Certificates.ActualClassDensity U q := by
  intro c d hw
  have hcd := classWeight_pos_ne U c d hw
  have hrep := Certificates.rowReplacement_of_maximizing_window q hq U hU hwin
  have hvol := reducedClassFrame_volume_le_radius_mul_restricted q r hq hk hr hn
    U hU hrep hwin c d hw hIH
  exact Certificates.sourcePairDensity_orientedPairFrame U _ _ _
    (rowClassRep_val_ne U c d hcd) _ _ _
    (pairClass_density_cap_of_central_bound q U c d hcd hBM hvol)

theorem actualClassDensity_of_midpointBM_restricted_induction_quotient {n k : ℕ}
    (hk : 2 ≤ k) (hq : 2 ≤ n/k) (U : Frame n k) (hU : IsMaximizingFrame U)
    (hwin : ReciprocalWindow (n/k) U) (hBM : MidpointBrunnMinkowski (k-2))
    (hIH : 1 ≤ k-2 → ∀ N : ℕ, 2*(k-2) ≤ N →
      ∀ V : Frame N (k-2), sectionVolume V ≤ sharpValue N (k-2)) :
    Certificates.ActualClassDensity U (n/k) := by
  apply actualClassDensity_of_midpointBM_restricted_induction (n/k) (n%k) hq hk
    (Nat.le_of_lt (Nat.mod_lt n (by omega))) _ U hU hwin hBM hIH
  simpa only [Nat.mul_comm] using (Nat.div_add_mod n k).symm

#print axioms actualClassDensity_of_midpointBM_induction
#print axioms actualClassDensity_of_midpointBM_induction_quotient
#print axioms actualClassDensity_of_midpointBM_restricted_induction
#print axioms actualClassDensity_of_midpointBM_restricted_induction_quotient
end CubeSections
