import CubeSections.Analysis.AmplitudeContraction
import CubeSections.Analysis.PairEnergy

/-! Global score transfer from an explicit pointwise scalar production bound. -/

noncomputable section
open scoped BigOperators

namespace CubeSections

theorem two_term_weighted_sq (x y α β : ℝ) (hα : 0 < α) (hβ : 0 < β) :
    (x + y) ^ 2 ≤ (α + β) * (x ^ 2 / α + y ^ 2 / β) := by
  have h := Finset.sq_sum_div_le_sum_sq_div Finset.univ ![x, y]
    (g := ![α, β]) (by
      intro i hi
      fin_cases i <;> simp_all)
  norm_num [Fin.sum_univ_succ] at h
  have hsum : 0 < α + β := by positivity
  have h' := (div_le_iff₀ hsum).mp h
  nlinarith

theorem amplitudeVariance_add_le {n k : ℕ} (U : Frame n k)
    (b v w : Fin n → ℝ) (α β : ℝ) (hα : 0 < α) (hβ : 0 < β) :
    amplitudeVariance U b (v + w) ≤
      (α + β) * (amplitudeVariance U b v / α + amplitudeVariance U b w / β) := by
  have hpair (i j : Fin n) := two_term_weighted_sq
    (pairAmplitude (b i) (b j) * v i - pairAmplitude (b j) (b i) * v j)
    (pairAmplitude (b i) (b j) * w i - pairAmplitude (b j) (b i) * w j)
    α β hα hβ
  have hsum := Finset.sum_le_sum (s := Finset.univ) (fun i _ =>
    Finset.sum_le_sum (s := Finset.univ) (fun j _ =>
      mul_le_mul_of_nonneg_left (hpair i j) (sq_nonneg (gramProjection U i j))))
  have hhalf := mul_le_mul_of_nonneg_left hsum (by norm_num : (0 : ℝ) ≤ 1 / 2)
  unfold amplitudeVariance
  convert hhalf using 1
  · congr 1
    apply Finset.sum_congr rfl
    intro i hi
    apply Finset.sum_congr rfl
    intro j hj
    simp only [Pi.add_apply]
    ring
  · simp only [div_eq_mul_inv, mul_add, Finset.sum_add_distrib, Finset.mul_sum,
      Finset.sum_mul]
    simp only [mul_assoc, mul_left_comm, mul_comm]

theorem amplitudeVariance_score_error_le {n k : ℕ} (U : Frame n k)
    (b T G : Fin n → ℝ) (hb : ∀ i, 0 < b i) :
    amplitudeVariance U b (fun i => gaussianScore (G i) - gaussianScore (T i)) ≤
      (1 / (3 * Real.exp 1)) * ∑ i, leverage U i * (T i - G i) ^ 2 := by
  have h := amplitudeVariance_le U b
    (fun i => gaussianScore (G i) - gaussianScore (T i)) hb
  apply h.trans
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i hi
  have hi' := gaussianScore_difference_sq_le (G i) (T i)
  have heq : (G i - T i) ^ 2 = (T i - G i) ^ 2 := by ring
  rw [heq] at hi'
  have hh := mul_le_mul_of_nonneg_left hi' (leverage_nonneg U i)
  convert hh using 1 <;> ring

theorem global_score_transfer {n k : ℕ} (U : Frame n k)
    (b T G : Fin n → ℝ) (p : Fin n → Fin n → ℝ)
    (hb : ∀ i, 0 < b i)
    (hp : ∀ i j,
      (pairAmplitude (b i) (b j) * gaussianScore (T i) -
        pairAmplitude (b j) (b i) * gaussianScore (T j)) ^ 2 ≤ (2 / 9 : ℝ) * p i j) :
    amplitudeVariance U b (fun i => gaussianScore (G i)) ≤
      (2 / 9 + 2 / (3 * Real.exp 1)) *
        ((1 / 2 : ℝ) * ∑ i, ∑ j, gramProjection U i j ^ 2 * p i j +
          (1 / 2 : ℝ) * ∑ i, leverage U i * (T i - G i) ^ 2) := by
  let α : ℝ := 2 / 9
  let β : ℝ := 2 / (3 * Real.exp 1)
  have hα : 0 < α := by norm_num [α]
  have hβ : 0 < β := by dsimp [β]; positivity
  have hprod : amplitudeVariance U b (fun i => gaussianScore (T i)) ≤
      α * ((1 / 2 : ℝ) * ∑ i, ∑ j, gramProjection U i j ^ 2 * p i j) := by
    unfold amplitudeVariance
    have hsum := Finset.sum_le_sum (s := Finset.univ) (fun i _ =>
      Finset.sum_le_sum (s := Finset.univ) (fun j _ =>
        mul_le_mul_of_nonneg_left (hp i j) (sq_nonneg (gramProjection U i j))))
    have hhalf := mul_le_mul_of_nonneg_left hsum (by norm_num : (0 : ℝ) ≤ 1 / 2)
    convert hhalf using 1 <;>
      simp only [α, Finset.mul_sum, Finset.sum_mul] <;> ring
  have herr : amplitudeVariance U b (fun i => gaussianScore (G i) - gaussianScore (T i)) ≤
      β * ((1 / 2 : ℝ) * ∑ i, leverage U i * (T i - G i) ^ 2) := by
    convert amplitudeVariance_score_error_le U b T G hb using 1 <;> dsimp [β] <;> ring
  have h := amplitudeVariance_add_le U b (fun i => gaussianScore (T i))
    (fun i => gaussianScore (G i) - gaussianScore (T i)) α β hα hβ
  have heq : (fun i => gaussianScore (T i)) +
      (fun i => gaussianScore (G i) - gaussianScore (T i)) =
      (fun i => gaussianScore (G i)) := by funext i; simp
  rw [heq] at h
  have hprod' := (div_le_iff₀ hα).mpr (hprod.trans_eq (mul_comm _ _))
  have herr' := (div_le_iff₀ hβ).mpr (herr.trans_eq (mul_comm _ _))
  exact h.trans (mul_le_mul_of_nonneg_left (add_le_add hprod' herr') (by positivity))

end CubeSections
