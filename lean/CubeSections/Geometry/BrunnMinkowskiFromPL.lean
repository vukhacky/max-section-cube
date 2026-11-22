import CubeSections.Geometry.BrunnMinkowskiScaling
import CubeSections.Geometry.BrunnMinkowskiBoundary
import CubeSections.Analysis.CompactGaussianApprox

/-! Exact rescaling to root-volume midpoint Brunn--Minkowski, including zero
volume sets. The displayed positive functional PL premise remains explicit. -/
noncomputable section
open Set MeasureTheory
namespace CubeSections

theorem midpointBrunnMinkowski_of_multiplicative {n : ℕ}
    (hBM : CompactMultiplicativeBM n) : MidpointBrunnMinkowski n := by
  by_cases hn0 : n=0
  · subst n
    exact midpointBrunnMinkowski_zero
  have hn : 1 ≤ n := by omega
  intro A B hAc hBc hAv hBv hAn hBn
  by_cases hA0 : (volume A).toReal=0
  · exact midpoint_root_zero_left hn A B hAn hAc hBc hA0
  by_cases hB0 : (volume B).toReal=0
  · have h := midpoint_root_zero_left hn B A hBn hBc hAc hB0
    simpa only [midpointMinkowski_comm B A, add_comm] using h
  exact midpoint_root_volume_of_positive_multiplicative hn hBM A B hAc hBc hAv hBv hAn hBn
    (lt_of_le_of_ne ENNReal.toReal_nonneg (Ne.symm hA0))
    (lt_of_le_of_ne ENNReal.toReal_nonneg (Ne.symm hB0))

theorem midpointBrunnMinkowski_of_positiveGaussianPrekopa {n : ℕ}
    (hPL : PositiveGaussianPrekopa n) : MidpointBrunnMinkowski n :=
  midpointBrunnMinkowski_of_multiplicative (compactMultiplicativeBM_of_positiveGaussianPrekopa hPL)

#print axioms midpointBrunnMinkowski_of_multiplicative
#print axioms midpointBrunnMinkowski_of_positiveGaussianPrekopa
end CubeSections
