import CubeSections.Semantics

/-! Proof-independent density law shared by the regular Gaussian transport modules. -/
noncomputable section
open MeasureTheory
namespace CubeSections

def euclideanDensityLaw {n : ℕ} (f : E n → ℝ) : Measure (E n) :=
  volume.withDensity (fun x => ENNReal.ofReal (f x))

end CubeSections
