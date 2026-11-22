import CubeSections.Geometry.BrunnMinkowskiFromPL
import CubeSections.Analysis.PrekopaTensorization

/-! Unconditional midpoint Brunn--Minkowski in every finite dimension, from
actual one-dimensional transport, tensorization, compact Gaussian approximation,
and positive homothety. Empty/zero-volume and dimension-zero cases are included. -/
noncomputable section
namespace CubeSections

theorem midpointBrunnMinkowski (n : ℕ) : MidpointBrunnMinkowski n :=
  midpointBrunnMinkowski_of_positiveGaussianPrekopa (positiveGaussianPrekopa n)

theorem affineVolume_le_sectionVolume {n k : ℕ} (U : Frame n k) (y : E n) :
    affineVolume U y ≤ sectionVolume U :=
  affineVolume_le_sectionVolume_of_midpointBM U (midpointBrunnMinkowski k) y

theorem affineMass_le_sectionMass {n k : ℕ} (U : Frame n k) (y : E n) :
    affineMass U y ≤ sectionMass U :=
  affineMass_le_sectionMass_of_midpointBM U (midpointBrunnMinkowski k) y

#print axioms midpointBrunnMinkowski
#print axioms affineVolume_le_sectionVolume
#print axioms affineMass_le_sectionMass
end CubeSections
