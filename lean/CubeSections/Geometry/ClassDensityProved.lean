import CubeSections.Geometry.ClassDensityInduction
import CubeSections.Geometry.BrunnMinkowski

/-! The actual joint-density cap with only the intended smaller-k induction
premise. Central domination is independently proved, including point fibers. -/
noncomputable section
namespace CubeSections

theorem actualClassDensity_of_restricted_induction {n k : ℕ} (q r : ℕ)
    (hq : 2 ≤ q) (hk : 2 ≤ k) (hr : r ≤ k) (hn : n = q*k+r)
    (U : Frame n k) (hU : IsMaximizingFrame U) (hwin : ReciprocalWindow q U)
    (hIH : 1 ≤ k-2 → ∀ N : ℕ, 2*(k-2) ≤ N →
      ∀ V : Frame N (k-2), sectionVolume V ≤ sharpValue N (k-2)) :
    Certificates.ActualClassDensity U q :=
  actualClassDensity_of_midpointBM_restricted_induction q r hq hk hr hn U hU hwin
    (midpointBrunnMinkowski (k-2)) hIH

theorem actualClassDensity_of_restricted_induction_quotient {n k : ℕ}
    (hk : 2 ≤ k) (hq : 2 ≤ n/k) (U : Frame n k) (hU : IsMaximizingFrame U)
    (hwin : ReciprocalWindow (n/k) U)
    (hIH : 1 ≤ k-2 → ∀ N : ℕ, 2*(k-2) ≤ N →
      ∀ V : Frame N (k-2), sectionVolume V ≤ sharpValue N (k-2)) :
    Certificates.ActualClassDensity U (n/k) :=
  actualClassDensity_of_midpointBM_restricted_induction_quotient hk hq U hU hwin
    (midpointBrunnMinkowski (k-2)) hIH

#print axioms actualClassDensity_of_restricted_induction
#print axioms actualClassDensity_of_restricted_induction_quotient
end CubeSections
