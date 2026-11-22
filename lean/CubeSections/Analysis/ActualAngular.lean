import CubeSections.Analysis.ActualGaussianCostProved

/-! Unconditional angular and incidence estimates for the actual slab deficits.
Both estimates allow zero coordinate rows and leverages equal to one. -/

noncomputable section
open MeasureTheory ProbabilityTheory
namespace CubeSections

theorem frame_angular_bound_twenty_slabs {n k : ℕ}
    (U : Frame n k) (r : Fin n → ℝ) (hr : ∀ i, 0 < r i) :
    gramAngularDefect U ≤ 20 * frameSlabDeficit U r := by
  obtain ⟨μ, hμ, hfirst, hG, hE, hbound⟩ := slabGaussianEnergy k n U r hr
  letI : IsProbabilityMeasure μ := hμ
  exact frame_angular_bound_twenty_of_energy U μ Prod.snd hG
    (slabQuantileOffset r) (fun p => frameQuantileCoordinates U r p.1)
    (frameSlabDeficit U r) hE hbound

theorem frame_pair_incidence_bound_slabs {n k : ℕ}
    (U : Frame n k) (r : Fin n → ℝ) (hr : ∀ i, 0 < r i) :
    Certificates.framePairIncidence U ≤ frameSlabDeficit U r := by
  obtain ⟨μ, hμ, hfirst, hG, hE, hbound⟩ := slabGaussianEnergy k n U r hr
  letI : IsProbabilityMeasure μ := hμ
  exact Certificates.frame_incidence_bound_of_energy U μ Prod.snd hG
    (slabQuantileOffset r) (fun p => frameQuantileCoordinates U r p.1)
    (frameSlabDeficit U r) hE hbound

theorem frame_angular_bound_twenty {n k : ℕ} (U : Frame n k) :
    gramAngularDefect U ≤ 20 * slabDeficit U :=
  angular_bound_of_slabGaussianEnergy (slabGaussianEnergy k) U

theorem frame_coalesced_incidence_bound {n k : ℕ}
    (U : Frame n k) (hrep : RowReplacement U) :
    Certificates.framePairIncidence (coalescedFrame U) ≤ slabDeficit U :=
  coalesced_incidence_of_slabGaussianEnergy (slabGaussianEnergy k) U hrep

#print axioms frame_angular_bound_twenty_slabs
#print axioms frame_pair_incidence_bound_slabs
#print axioms frame_angular_bound_twenty
#print axioms frame_coalesced_incidence_bound
end CubeSections
