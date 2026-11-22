import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-! Scalar production bounds used in the determinant remainder argument. -/

noncomputable section
open Set

namespace CubeSections

/-- The scalar entropy production function. -/
def phi (t : ℝ) : ℝ := t - 1 + Real.exp (-t)

/-- The difference in the sharp exponential production comparison. -/
def scalarProductionGap (t : ℝ) : ℝ :=
  phi t - (9 / 2 : ℝ) * (1 - Real.exp (-t / 3)) ^ 2

theorem hasDerivAt_scalarProductionGap (t : ℝ) :
    HasDerivAt scalarProductionGap ((1 - Real.exp (-t / 3)) ^ 3) t := by
  have hexp : Real.exp (-t) = Real.exp (-t / 3) ^ 3 := by
    calc
      Real.exp (-t) = Real.exp ((-t / 3) * (3 : ℕ)) := by congr 1; norm_num
      _ = _ := Real.exp_mul_natCast _ _
  have h₁ := ((hasDerivAt_id t).sub_const 1).add
    ((hasDerivAt_id t).neg.exp)
  have h₂ := (((hasDerivAt_id t).neg.div_const 3).exp.const_sub 1).pow 2
  convert h₁.sub (h₂.const_mul (9 / 2 : ℝ)) using 1
  · rfl
  · dsimp
    rw [hexp]
    ring

theorem scalarProductionGap_monotoneOn :
    MonotoneOn scalarProductionGap (Ici 0) := by
  apply monotoneOn_of_hasDerivWithinAt_nonneg (convex_Ici 0)
  · exact (continuous_iff_continuousAt.mpr
      (fun t => (hasDerivAt_scalarProductionGap t).continuousAt)).continuousOn
  · intro t _
    exact (hasDerivAt_scalarProductionGap t).hasDerivWithinAt
  · intro t ht
    have ht₀ : 0 ≤ t := (interior_subset ht)
    exact pow_nonneg (sub_nonneg.mpr (Real.exp_le_one_iff.mpr (by linarith))) _

/-- Manuscript scalar inequality, valid on the whole nonnegative half-line. -/
theorem scalar_production (t : ℝ) (ht : 0 ≤ t) :
    (9 / 2 : ℝ) * (1 - Real.exp (-t / 3)) ^ 2 ≤ phi t := by
  have h := scalarProductionGap_monotoneOn (show (0 : ℝ) ∈ Ici 0 by simp)
    (show t ∈ Ici 0 from ht) ht
  simpa [scalarProductionGap, phi] using h

theorem phi_nonneg (t : ℝ) (ht : 0 ≤ t) : 0 ≤ phi t := by
  exact (mul_nonneg (by norm_num : (0 : ℝ) ≤ 9 / 2) (sq_nonneg _)).trans
    (scalar_production t ht)

private theorem exp_difference_le_of_le (s t : ℝ) (hs : 0 ≤ s) (hst : s ≤ t) :
    |Real.exp (-s / 3) - Real.exp (-t / 3)| ≤
      1 - Real.exp (-|s - t| / 3) := by
  have horder : Real.exp (-t / 3) ≤ Real.exp (-s / 3) :=
    Real.exp_le_exp.mpr (by linarith)
  have hs1 : Real.exp (-s / 3) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
  have hd1 : Real.exp (-(t - s) / 3) ≤ 1 :=
    Real.exp_le_one_iff.mpr (by linarith)
  have hfactor : Real.exp (-t / 3) =
      Real.exp (-s / 3) * Real.exp (-(t - s) / 3) := by
    rw [← Real.exp_add]
    congr 1
    ring
  rw [abs_of_nonneg (sub_nonneg.mpr horder), abs_of_nonpos (sub_nonpos.mpr hst)]
  have hneg : -(s - t) = t - s := by ring
  rw [hneg, hfactor]
  nlinarith [mul_nonneg (sub_nonneg.mpr hs1) (sub_nonneg.mpr hd1)]

/-- A bounded exponential score is controlled by the difference of nonnegative potentials. -/
theorem exponential_score_difference (s t : ℝ) (hs : 0 ≤ s) (ht : 0 ≤ t) :
    |Real.exp (-s / 3) - Real.exp (-t / 3)| ≤
      1 - Real.exp (-|s - t| / 3) := by
  rcases le_total s t with hst | hts
  · exact exp_difference_le_of_le s t hs hst
  · simpa only [abs_sub_comm] using exp_difference_le_of_le t s ht hts

/-- The pairwise scalar comparison used to obtain exponential determinant production. -/
theorem exponential_pair_production (s t : ℝ) (hs : 0 ≤ s) (ht : 0 ≤ t) :
    (9 / 2 : ℝ) * (Real.exp (-s / 3) - Real.exp (-t / 3)) ^ 2 ≤
      phi |s - t| := by
  have hd := exponential_score_difference s t hs ht
  have hnonneg : 0 ≤ 1 - Real.exp (-|s - t| / 3) := by
    exact sub_nonneg.mpr (Real.exp_le_one_iff.mpr (by nlinarith [abs_nonneg (s - t)]))
  have hsq := (sq_le_sq₀ (abs_nonneg _) hnonneg).mpr hd
  rw [sq_abs] at hsq
  calc
    _ ≤ (9 / 2 : ℝ) * (1 - Real.exp (-|s - t| / 3)) ^ 2 := by nlinarith
    _ ≤ phi |s - t| := scalar_production _ (abs_nonneg _)

end CubeSections
