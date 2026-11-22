import CubeSections.Analysis.GaussianScore
import CubeSections.Analysis.ScalarProduction
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Tactic.FinCases
import Mathlib.Data.Fin.VecNotation
import Mathlib.Algebra.BigOperators.Fin

/-! Pointwise transfer from transported scores to Gaussian scores. -/

noncomputable section
open scoped BigOperators

namespace CubeSections

theorem three_term_weighted_sq (x y z α β γ : ℝ)
    (hα : 0 < α) (hβ : 0 < β) (hγ : 0 < γ) :
    (x + y + z) ^ 2 ≤ (α + β + γ) * (x ^ 2 / α + y ^ 2 / β + z ^ 2 / γ) := by
  have h := Finset.sq_sum_div_le_sum_sq_div Finset.univ ![x, y, z]
    (g := ![α, β, γ]) (by
      intro i hi
      fin_cases i <;> simp_all)
  norm_num [Fin.sum_univ_succ] at h
  simp only [← add_assoc] at h
  have hsum : 0 < α + β + γ := by positivity
  have h' := (div_le_iff₀ hsum).mp h
  nlinarith

def pairTransferCoeff (A B : ℝ) : ℝ :=
  2 / 9 + (2 / (3 * Real.exp 1)) * (2 - A - B)

theorem pairTransferCoeff_pos (A B : ℝ) (hA : A < 1) (hB : B < 1) :
    0 < pairTransferCoeff A B := by
  have he : 0 < Real.exp 1 := Real.exp_pos _
  unfold pairTransferCoeff
  have hAB : 0 < 2 - A - B := by linarith
  positivity

theorem score_pair_transfer_bound (A B a b T S G H p : ℝ)
    (hA : A < 1) (hB : B < 1) (ha₀ : 0 ≤ a) (ha₁ : a ≤ 1)
    (hb₀ : 0 ≤ b) (hb₁ : b ≤ 1)
    (hp : (a * gaussianScore T - b * gaussianScore S) ^ 2 ≤ (2 / 9 : ℝ) * p) :
    (a * gaussianScore G - b * gaussianScore H) ^ 2 ≤
      pairTransferCoeff A B *
        (p + (T - G) ^ 2 / (2 * (1 - A)) + (S - H) ^ 2 / (2 * (1 - B))) := by
  let L : ℝ := 1 / (3 * Real.exp 1)
  have hL : 0 < L := by dsimp [L]; positivity
  have hα : (0 : ℝ) < 2 / 9 := by norm_num
  have hA' : 0 < 1 - A := by linarith
  have hB' : 0 < 1 - B := by linarith
  have hβ : 0 < 2 * L * (1 - A) := by positivity
  have hγ : 0 < 2 * L * (1 - B) := by positivity
  let x := a * gaussianScore T - b * gaussianScore S
  let y := a * gaussianScore G - a * gaussianScore T
  let z := b * gaussianScore S - b * gaussianScore H
  have hx : x ^ 2 / (2 / 9) ≤ p := by
    apply (div_le_iff₀ hα).mpr
    simpa [x, mul_comm] using hp
  have hy' : y ^ 2 ≤ L * (T - G) ^ 2 := by
    have ha₂ : a ^ 2 ≤ 1 := (sq_le_one_iff_abs_le_one a).mpr (by rwa [abs_of_nonneg ha₀])
    have h := scaledGaussianScore_difference_sq_le a G T
    have hc := div_le_div_of_nonneg_right ha₂ (by positivity : 0 ≤ 3 * Real.exp 1)
    have hh := mul_le_mul_of_nonneg_right hc (sq_nonneg (G - T))
    have hswap : (G - T) ^ 2 = (T - G) ^ 2 := by ring
    simpa only [y, L, hswap] using h.trans hh
  have hz' : z ^ 2 ≤ L * (S - H) ^ 2 := by
    have hb₂ : b ^ 2 ≤ 1 := (sq_le_one_iff_abs_le_one b).mpr (by rwa [abs_of_nonneg hb₀])
    have h := scaledGaussianScore_difference_sq_le b S H
    have hc := div_le_div_of_nonneg_right hb₂ (by positivity : 0 ≤ 3 * Real.exp 1)
    exact h.trans (mul_le_mul_of_nonneg_right hc (sq_nonneg (S - H)))
  have hy : y ^ 2 / (2 * L * (1 - A)) ≤ (T - G) ^ 2 / (2 * (1 - A)) := by
    calc
      _ ≤ (L * (T - G) ^ 2) / (2 * L * (1 - A)) :=
        div_le_div_of_nonneg_right hy' hβ.le
      _ = _ := by field_simp
  have hz : z ^ 2 / (2 * L * (1 - B)) ≤ (S - H) ^ 2 / (2 * (1 - B)) := by
    calc
      _ ≤ (L * (S - H) ^ 2) / (2 * L * (1 - B)) :=
        div_le_div_of_nonneg_right hz' hγ.le
      _ = _ := by field_simp
  have hC : 2 / 9 + 2 * L * (1 - A) + 2 * L * (1 - B) = pairTransferCoeff A B := by
    dsimp [L, pairTransferCoeff]
    ring
  have h := three_term_weighted_sq x y z (2 / 9) (2 * L * (1 - A))
    (2 * L * (1 - B)) hα hβ hγ
  rw [hC] at h
  have hbound := mul_le_mul_of_nonneg_left (add_le_add (add_le_add hx hy) hz)
    (pairTransferCoeff_pos A B hA hB).le
  have hid : a * gaussianScore G - b * gaussianScore H = x + y + z := by
    dsimp [x, y, z]
    ring
  rw [hid]
  exact h.trans hbound

theorem potential_pair_transfer_bound (A B β η T S G H : ℝ)
    (hA : A < 1) (hB : B < 1) (hβ : 0 ≤ β) (hη : 0 ≤ η) :
    (Real.exp (-β / 3) * gaussianScore G - Real.exp (-η / 3) * gaussianScore H) ^ 2 ≤
      pairTransferCoeff A B *
        (phi |(β + T ^ 2 / 2) - (η + S ^ 2 / 2)| +
          (T - G) ^ 2 / (2 * (1 - A)) + (S - H) ^ 2 / (2 * (1 - B))) := by
  have hβ' : 0 ≤ β + T ^ 2 / 2 := by positivity
  have hη' : 0 ≤ η + S ^ 2 / 2 := by positivity
  have hprod (d t : ℝ) : Real.exp (-d / 3) * gaussianScore t =
      Real.exp (-(d + t ^ 2 / 2) / 3) := by
    unfold gaussianScore
    rw [← Real.exp_add]
    congr 1
    ring
  apply score_pair_transfer_bound A B _ _ T S G H _ hA hB
    (Real.exp_pos _).le (Real.exp_le_one_iff.mpr (by linarith))
    (Real.exp_pos _).le (Real.exp_le_one_iff.mpr (by linarith))
  rw [hprod, hprod]
  have h := exponential_pair_production (β + T ^ 2 / 2) (η + S ^ 2 / 2) hβ' hη'
  nlinarith

end CubeSections
