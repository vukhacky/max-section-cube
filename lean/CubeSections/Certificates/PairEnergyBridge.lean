import CubeSections.Analysis.GaussianCost
import CubeSections.Analysis.PairEnergy
import CubeSections.Certificates.LeafSoundness

/-! Identification of the analytic Gaussian quotient with the certificate cost. -/
noncomputable section
namespace CubeSections.Certificates

theorem pairAngularCost_eq_gaussian_quotient (A B s : ℝ) :
    pairAngularCost A B s =
      (CubeSections.gaussianSecondMoment * ((1-s)/(16-s))) /
        CubeSections.pairTransferCoeff A B := by
  unfold pairAngularCost CubeSections.gaussianSecondMoment CubeSections.pairTransferCoeff
  simp only [div_eq_mul_inv, mul_inv_rev]
  ring

theorem pairAngularCost_le_energy (A B s a b E : ℝ)
    (hA : A < 1) (hB : B < 1) (hs : s ≤ 1) (hab : a=1 ∨ b=1)
    (htransfer : CubeSections.gaussianPairCost s a b ≤ CubeSections.pairTransferCoeff A B * E) :
    pairAngularCost A B s ≤ E := by
  rw [pairAngularCost_eq_gaussian_quotient]
  apply (div_le_iff₀ (CubeSections.pairTransferCoeff_pos A B hA hB)).mpr
  have h := (CubeSections.gaussianPairCost_lower s a b hs hab).trans htransfer
  simpa only [mul_comm] using h

#print axioms pairAngularCost_eq_gaussian_quotient
#print axioms pairAngularCost_le_energy
end CubeSections.Certificates
