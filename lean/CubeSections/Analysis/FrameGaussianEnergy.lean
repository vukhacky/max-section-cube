import CubeSections.Analysis.FrameGaussian
import CubeSections.Analysis.GaussianTest
import CubeSections.Analysis.AmplitudeContraction
import CubeSections.LinearAlgebra.Projection

/-! Gaussian lower energy for an actual frame. Zero rows are handled explicitly. -/

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped BigOperators InnerProductSpace RealInnerProductSpace

namespace CubeSections

/-- Normalized coordinate functional, defined also at zero leverage. -/
def normalizedFrameCoordinate {n k : ℕ} (U : Frame n k) (i : Fin n) (x : E k) : ℝ :=
  ⟪(Real.sqrt (leverage U i))⁻¹ • rowVector U i, x⟫_ℝ

theorem normalizedFrameCoordinate_eq {n k : ℕ} (U : Frame n k) (i : Fin n) (x : E k) :
    normalizedFrameCoordinate U i x = (U x) i / Real.sqrt (leverage U i) := by
  rw [normalizedFrameCoordinate, real_inner_smul_left, rowVector_inner]
  ring

theorem normalizedFrameCoordinate_active {n k : ℕ} (U : Frame n k)
    (i : ActiveRow U) (x : E k) :
    normalizedFrameCoordinate U i.val x = ⟪unitRow U i, x⟫_ℝ := rfl

theorem integrable_scaledGaussianScore_diff_sq {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsFiniteMeasure μ] (f g : Ω → ℝ)
    (hf : Measurable f) (hg : Measurable g) (a b : ℝ) :
    Integrable (fun x => (a * gaussianScore (f x) - b * gaussianScore (g x)) ^ 2) μ := by
  have hF : Integrable (fun x => gaussianScore (f x) ^ 2) μ := by
    simpa only [pow_two] using integrable_gaussianScore_product μ f f hf hf
  have hG : Integrable (fun x => gaussianScore (g x) ^ 2) μ := by
    simpa only [pow_two] using integrable_gaussianScore_product μ g g hg hg
  have hFG := integrable_gaussianScore_product μ f g hf hg
  have h := ((hF.const_mul (a ^ 2)).add (hG.const_mul (b ^ 2))).sub
    (hFG.const_mul (2 * a * b))
  apply h.congr
  filter_upwards with x
  simp only [Pi.sub_apply, Pi.add_apply]
  ring

def frameGaussianScoreEnergy {n k : ℕ} (U : Frame n k) (b : Fin n → ℝ) (x : E k) : ℝ :=
  amplitudeVariance U b (fun i => gaussianScore (normalizedFrameCoordinate U i x))

theorem integrable_frameGaussianScoreEnergy {n k : ℕ} (U : Frame n k) (b : Fin n → ℝ) :
    Integrable (frameGaussianScoreEnergy U b) (stdGaussian (E k)) := by
  unfold frameGaussianScoreEnergy amplitudeVariance
  apply Integrable.const_mul
  apply integrable_finsetSum
  intro i hi
  apply integrable_finsetSum
  intro j hj
  apply Integrable.const_mul
  exact integrable_scaledGaussianScore_diff_sq (stdGaussian (E k))
    (normalizedFrameCoordinate U i) (normalizedFrameCoordinate U j)
    (by unfold normalizedFrameCoordinate; fun_prop)
    (by unfold normalizedFrameCoordinate; fun_prop) _ _

theorem pairAmplitude_eq_one_or (b c : ℝ) (hb : 0 < b) (hc : 0 < c) :
    pairAmplitude b c = 1 ∨ pairAmplitude c b = 1 := by
  rcases le_total b c with h | h
  · left
    simp [pairAmplitude, min_eq_left h, ne_of_gt hb]
  · right
    simp [pairAmplitude, min_eq_left h, ne_of_gt hc]

theorem frame_gaussian_pair_energy_lower {n k : ℕ} (U : Frame n k)
    (b : Fin n → ℝ) (hb : ∀ i, 0 < b i) (i j : Fin n) :
    (gaussianSecondMoment / 16) * gramProjection U i j ^ 2 *
        (1 - gramProjection U i j ^ 2 / (leverage U i * leverage U j)) ≤
      ∫ x : E k, gramProjection U i j ^ 2 *
        (pairAmplitude (b i) (b j) * gaussianScore (normalizedFrameCoordinate U i x) -
          pairAmplitude (b j) (b i) * gaussianScore (normalizedFrameCoordinate U j x)) ^ 2
        ∂(stdGaussian (E k)) := by
  by_cases hi : 0 < leverage U i
  · by_cases hj : 0 < leverage U j
    · let i' : ActiveRow U := ⟨i, hi⟩
      let j' : ActiveRow U := ⟨j, hj⟩
      have hs₀ : 0 ≤ gramProjection U i j ^ 2 / (leverage U i * leverage U j) :=
        div_nonneg (sq_nonneg _) (mul_nonneg hi.le hj.le)
      have hs₁ : gramProjection U i j ^ 2 / (leverage U i * leverage U j) ≤ 1 := by
        apply (div_le_iff₀ (mul_pos hi hj)).mpr
        simpa using gramProjection_entry_sq_le U i j
      have hcost := gaussianPairCost_coarse_lower
        (gramProjection U i j ^ 2 / (leverage U i * leverage U j))
        (pairAmplitude (b i) (b j)) (pairAmplitude (b j) (b i)) hs₀ hs₁
        (pairAmplitude_eq_one_or (b i) (b j) (hb i) (hb j))
      have hmoment := integral_gaussianPairObservable (unitRow U i') (unitRow U j')
        (unitRow_norm U i') (unitRow_norm U j')
        (pairAmplitude (b i) (b j)) (pairAmplitude (b j) (b i))
      rw [unitRow_inner_sq] at hmoment
      have hmoment' :
          (∫ x : E k,
            (pairAmplitude (b i) (b j) * gaussianScore (normalizedFrameCoordinate U i x) -
              pairAmplitude (b j) (b i) * gaussianScore (normalizedFrameCoordinate U j x)) ^ 2
            ∂(stdGaussian (E k))) =
          gaussianPairCost (gramProjection U i j ^ 2 / (leverage U i * leverage U j))
            (pairAmplitude (b i) (b j)) (pairAmplitude (b j) (b i)) := by
        simpa only [gaussianPairObservable, normalizedFrameCoordinate, unitRow, i', j'] using hmoment
      rw [integral_const_mul, hmoment']
      convert mul_le_mul_of_nonneg_left hcost (sq_nonneg (gramProjection U i j)) using 1 <;> ring
    · have hj₀ : leverage U j = 0 := le_antisymm (le_of_not_gt hj) (leverage_nonneg U j)
      have hp : gramProjection U i j = 0 := by
        rw [gramProjection_symm]
        exact zero_leverage_row_zero U j i hj₀
      simp [hp]
  · have hi₀ : leverage U i = 0 := le_antisymm (le_of_not_gt hi) (leverage_nonneg U i)
    have hp := zero_leverage_row_zero U i j hi₀
    simp [hp]

theorem gramAngular_sum_identity {n k : ℕ} (U : Frame n k) :
    (∑ i, ∑ j, gramProjection U i j ^ 2 *
      (1 - gramProjection U i j ^ 2 / (leverage U i * leverage U j))) =
      (k : ℝ) - ∑ i, ∑ j, gramProjection U i j ^ 4 / (leverage U i * leverage U j) := by
  calc
    _ = (∑ i, ∑ j, gramProjection U i j ^ 2) -
        ∑ i, ∑ j, gramProjection U i j ^ 4 / (leverage U i * leverage U j) := by
      rw [← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro i hi
      rw [← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro j hj
      ring
    _ = _ := by simp_rw [gramProjection_row_sq_sum]; rw [sum_leverage]

theorem frame_gaussian_energy_lower {n k : ℕ} (U : Frame n k)
    (b : Fin n → ℝ) (hb : ∀ i, 0 < b i) :
    (gaussianSecondMoment / 32) *
        ((k : ℝ) - ∑ i, ∑ j, gramProjection U i j ^ 4 / (leverage U i * leverage U j)) ≤
      ∫ x : E k, frameGaussianScoreEnergy U b x ∂(stdGaussian (E k)) := by
  let f : Fin n → Fin n → E k → ℝ := fun i j x =>
    gramProjection U i j ^ 2 *
      (pairAmplitude (b i) (b j) * gaussianScore (normalizedFrameCoordinate U i x) -
        pairAmplitude (b j) (b i) * gaussianScore (normalizedFrameCoordinate U j x)) ^ 2
  have hint (i j : Fin n) : Integrable (f i j) (stdGaussian (E k)) := by
    apply Integrable.const_mul
    exact integrable_scaledGaussianScore_diff_sq (stdGaussian (E k))
      (normalizedFrameCoordinate U i) (normalizedFrameCoordinate U j)
      (by unfold normalizedFrameCoordinate; fun_prop)
      (by unfold normalizedFrameCoordinate; fun_prop) _ _
  have hintRow (i : Fin n) : Integrable (fun x => ∑ j, f i j x) (stdGaussian (E k)) :=
    integrable_finsetSum Finset.univ (fun j _ => hint i j)
  have hintegral : (∫ x : E k, frameGaussianScoreEnergy U b x ∂(stdGaussian (E k))) =
      (1 / 2 : ℝ) * ∑ i, ∑ j, ∫ x : E k, f i j x ∂(stdGaussian (E k)) := by
    unfold frameGaussianScoreEnergy amplitudeVariance
    change (∫ x : E k, (1 / 2 : ℝ) * ∑ i, ∑ j, f i j x ∂(stdGaussian (E k))) = _
    rw [integral_const_mul, integral_finsetSum Finset.univ (fun i _ => hintRow i)]
    congr 1
    apply Finset.sum_congr rfl
    intro i hi
    exact integral_finsetSum Finset.univ (fun j _ => hint i j)
  have hsum := Finset.sum_le_sum (s := Finset.univ) (fun i _ =>
    Finset.sum_le_sum (s := Finset.univ) (fun j _ => frame_gaussian_pair_energy_lower U b hb i j))
  have hhalf := mul_le_mul_of_nonneg_left hsum (by norm_num : (0 : ℝ) ≤ 1 / 2)
  have hcoef : (1 / 2 : ℝ) * ∑ i, ∑ j,
      (gaussianSecondMoment / 16) * gramProjection U i j ^ 2 *
        (1 - gramProjection U i j ^ 2 / (leverage U i * leverage U j)) =
      (gaussianSecondMoment / 32) * ∑ i, ∑ j, gramProjection U i j ^ 2 *
        (1 - gramProjection U i j ^ 2 / (leverage U i * leverage U j)) := by
    simp only [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    apply Finset.sum_congr rfl
    intro j hj
    ring
  rw [hcoef, gramAngular_sum_identity] at hhalf
  rw [hintegral]
  exact hhalf

end CubeSections
