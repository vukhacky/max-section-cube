import CubeSections.Certificates.SmallQuotient
import CubeSections.Certificates.CoalescedIncidence
import CubeSections.Certificates.IncidenceTransport

/-! Small-quotient classification with the weighted incidence hypothesis
discharged by a genuine common-Gaussian transport energy contract. The deficit
is that of the original section; coalescing is used for the isotropic frame and
the width parameters β, never for a new cube-section deficit.
-/
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped BigOperators

namespace CubeSections.Certificates

theorem isBalancedSection_of_maximizing_energy {n k : ℕ}
    (hk : 1 ≤ k) (hkn : k ≤ n) (hq : n/k=2 ∨ n/k=3 ∨ n/k=4)
    (U : Frame n k) (hU : IsMaximizingFrame U) (hwin : ReciprocalWindow (n/k) U)
    (hdensity : ActualClassDensity U (n/k))
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (G : Ω → E k) (hG : MeasurePreserving G μ (stdGaussian (E k)))
    (β : Fin (rowClassCount U) → ℝ) (T : Ω → Fin (rowClassCount U) → ℝ)
    (hE : Integrable (fun ω => frameTransportEnergy (coalescedFrame U) β (T ω) (G ω)) μ)
    (hbound : (∫ ω, frameTransportEnergy (coalescedFrame U) β (T ω) (G ω) ∂μ) ≤ slabDeficit U) :
    IsBalancedSection U := by
  exact isBalancedSection_of_maximizing_smallQuotient hk hkn hq U hU hwin hdensity
    (actualClass_incidence_bound_of_energy U μ G hG β T (slabDeficit U) hE hbound)

theorem balanced_and_target_of_ratioMaximizing_energy {n k : ℕ}
    (q : ℕ) (hq : q=2 ∨ q=3 ∨ q=4) (hk : 1 ≤ k) (U : Frame n k)
    (hlo : q*k < n) (hhi : n < (q+1)*k)
    (hmax : RatioMaximalOnWindow q U) (hdensity : ActualClassDensity U q)
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (G : Ω → E k) (hG : MeasurePreserving G μ (stdGaussian (E k)))
    (β : Fin (rowClassCount U) → ℝ) (T : Ω → Fin (rowClassCount U) → ℝ)
    (hE : Integrable (fun ω => frameTransportEnergy (coalescedFrame U) β (T ω) (G ω)) μ)
    (hbound : (∫ ω, frameTransportEnergy (coalescedFrame U) β (T ω) (G ω) ∂μ) ≤ slabDeficit U) :
    IsBalancedSection U ∧ sectionVolume U = sharpValue n k := by
  exact balanced_and_target_of_ratioMaximizing_smallQuotient q hq hk U hlo hhi hmax hdensity
    (actualClass_incidence_bound_of_energy U μ G hG β T (slabDeficit U) hE hbound)

/-- The small-quotient endpoint with actual determinant production, conditional
on the explicitly displayed transport entropy decomposition and coupling cost. -/
theorem balanced_and_target_of_ratioMaximizing_determinant_transport {n k : ℕ}
    (q : ℕ) (hq : q=2 ∨ q=3 ∨ q=4) (hk : 1 ≤ k) (U : Frame n k)
    (hlo : q*k < n) (hhi : n < (q+1)*k)
    (hmax : RatioMaximalOnWindow q U) (hdensity : ActualClassDensity U q)
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (G : Ω → E k) (hG : MeasurePreserving G μ (stdGaussian (E k)))
    (β : Fin (rowClassCount U) → ℝ) (T : Ω → Fin (rowClassCount U) → ℝ) (D : ℝ)
    (hT : ∀ i, Measurable (fun ω => T ω i))
    (hJ : Integrable (fun ω => determinantRemainder (coalescedFrame U)
      (fun i => β i+T ω i^2/2)) μ)
    (hres : Integrable (fun ω => ‖frameResidual (coalescedFrame U)
      (liftedScores (coalescedFrame U) (T ω))‖^2) μ)
    (herr : Integrable (fun ω => ‖frameAdjoint (coalescedFrame U)
      (liftedScores (coalescedFrame U) (T ω))-G ω‖^2) μ)
    (hdecomp : slabDeficit U = D+(∫ ω, determinantRemainder (coalescedFrame U)
      (fun i => β i+T ω i^2/2) ∂μ)+(1/2 : ℝ)*(∫ ω,
        ‖frameResidual (coalescedFrame U) (liftedScores (coalescedFrame U) (T ω))‖^2 ∂μ))
    (hcost : (∫ ω, ‖frameAdjoint (coalescedFrame U)
      (liftedScores (coalescedFrame U) (T ω))-G ω‖^2 ∂μ) ≤ 2*D) :
    IsBalancedSection U ∧ sectionVolume U = sharpValue n k := by
  have hinc := frame_incidence_bound_of_determinant_transport (coalescedFrame U)
    μ G hG β T D (slabDeficit U) hT hJ hres herr hdecomp hcost
  rw [framePairIncidence_coalesced] at hinc
  exact balanced_and_target_of_ratioMaximizing_smallQuotient q hq hk U hlo hhi hmax hdensity hinc

#print axioms isBalancedSection_of_maximizing_energy
#print axioms balanced_and_target_of_ratioMaximizing_energy
#print axioms balanced_and_target_of_ratioMaximizing_determinant_transport
end CubeSections.Certificates
