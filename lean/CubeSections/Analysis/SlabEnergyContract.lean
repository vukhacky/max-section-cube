import CubeSections.Geometry.CoalescedSlabs
import CubeSections.Certificates.CoalescedIncidence

/-! Gaussian slab-energy estimates and their angular and incidence consequences.

`SlabGaussianEnergyStatement` specifies a coupling of the uniform slab law and
standard Gaussian, together with an integrable energy bound. The implications
below take this statement as a hypothesis. Its proof is supplied in
`Analysis.ActualGaussianCostProved`.
-/

noncomputable section
open MeasureTheory ProbabilityTheory

namespace CubeSections

def slabQuantileOffset {n : ℕ} (r : Fin n → ℝ) (i : Fin n) : ℝ :=
  Real.log (Real.sqrt (2 * Real.pi)) - Real.log (2 * r i)

def SlabGaussianEnergyStatement (k : ℕ) : Prop :=
  ∀ (n : ℕ) (U : Frame n k) (r : Fin n → ℝ), (∀ i, 0 < r i) →
    ∃ μ : Measure (E k × E k),
      IsProbabilityMeasure μ ∧
      MeasurePreserving Prod.fst μ (frameSlabUniform U r) ∧
      MeasurePreserving Prod.snd μ (stdGaussian (E k)) ∧
      Integrable (fun p => frameTransportEnergy U (slabQuantileOffset r)
        (frameQuantileCoordinates U r p.1) p.2) μ ∧
      (∫ p, frameTransportEnergy U (slabQuantileOffset r)
        (frameQuantileCoordinates U r p.1) p.2 ∂μ) ≤
        frameSlabLogFactor U r - Real.log (frameSlabVolume U r)

theorem cubeSlabDeficit {n k : ℕ} (U : Frame n k) :
    frameSlabLogFactor U (cubeFrameRadius U) - Real.log (frameSlabVolume U (cubeFrameRadius U)) =
      slabDeficit U := by
  rw [frameSlabLogFactor_cubeFrameRadius, frameSlabVolume_cubeFrameRadius]
  rfl

theorem angular_bound_of_slabGaussianEnergy {n k : ℕ}
    (henergy : SlabGaussianEnergyStatement k) (U : Frame n k) :
    gramAngularDefect U ≤ 20 * slabDeficit U := by
  obtain ⟨μ, hμ, hfirst, hG, hE, hbound⟩ :=
    henergy n U (cubeFrameRadius U) (cubeFrameRadius_pos U)
  letI : IsProbabilityMeasure μ := hμ
  rw [cubeSlabDeficit] at hbound
  exact frame_angular_bound_twenty_of_energy U μ Prod.snd hG
    (slabQuantileOffset (cubeFrameRadius U))
    (fun p => frameQuantileCoordinates U (cubeFrameRadius U) p.1)
    (slabDeficit U) hE hbound

theorem coalesced_incidence_of_slabGaussianEnergy {n k : ℕ}
    (henergy : SlabGaussianEnergyStatement k) (U : Frame n k) (hrep : RowReplacement U) :
    Certificates.framePairIncidence (coalescedFrame U) ≤ slabDeficit U := by
  obtain ⟨μ, hμ, hfirst, hG, hE, hbound⟩ := henergy (rowClassCount U)
    (coalescedFrame U) (coalescedCubeRadius U) (coalescedCubeRadius_pos U)
  letI : IsProbabilityMeasure μ := hμ
  rw [coalescedSlabDeficit U hrep] at hbound
  exact Certificates.frame_incidence_bound_of_energy (coalescedFrame U) μ Prod.snd hG
    (slabQuantileOffset (coalescedCubeRadius U))
    (fun p => frameQuantileCoordinates (coalescedFrame U) (coalescedCubeRadius U) p.1)
    (slabDeficit U) hE hbound

end CubeSections
