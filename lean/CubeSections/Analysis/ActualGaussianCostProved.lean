import CubeSections.Analysis.ActualGaussianCost
import CubeSections.Analysis.FrameTransportRegularDensityProved

/-! The unconditional Gaussian coupling and slab energy for the actual frame
laws. Global topology and regular-density identification discharge all premises
of the preceding coupling construction. -/

noncomputable section
namespace CubeSections

theorem frameTransportRegularDensity (k : ℕ) : FrameTransportRegularDensityStatement k := by
  intro n U r hr
  exact frameTransportedLaw_regular_density U r hr

theorem frameGaussianQuadraticCost (k : ℕ) : FrameGaussianQuadraticCostStatement k :=
  frameGaussianQuadraticCost_of_frameTransportRegularDensity (frameTransportRegularDensity k)

theorem slabGaussianEnergy (k : ℕ) : SlabGaussianEnergyStatement k :=
  slabGaussianEnergy_of_frameGaussianQuadraticCost (frameGaussianQuadraticCost k)

#print axioms frameTransportRegularDensity
#print axioms frameGaussianQuadraticCost
#print axioms slabGaussianEnergy
end CubeSections
