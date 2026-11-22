import CubeSections.Analysis.GaussianPair
import Mathlib.Probability.Distributions.Gaussian.Multivariate

/-! Law of two unit-vector projections of a standard Gaussian. -/

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped InnerProductSpace RealInnerProductSpace NNReal

namespace CubeSections

private theorem stdGaussian_real : stdGaussian ℝ = gaussianReal 0 1 := by
  apply Measure.ext_of_charFun
  funext t
  rw [charFun_stdGaussian, charFun_gaussianReal]
  have hR : ‖t‖ ^ 2 = t ^ 2 := by simp [Real.norm_eq_abs]
  have hC : (‖t‖ : ℂ) ^ 2 = (t : ℂ) ^ 2 := by exact_mod_cast hR
  rw [hC]
  simp
  congr 1
  ring

private theorem realStrongDual_norm (L : StrongDual ℝ ℝ) : ‖L‖ = |L 1| := by
  have h : L = InnerProductSpace.toDualMap ℝ ℝ (L 1) := by
    ext x
    simpa [InnerProductSpace.toDualMap_apply_apply, real_inner_comm, mul_comm] using L.map_smul x 1
  calc
    ‖L‖ = ‖InnerProductSpace.toDualMap ℝ ℝ (L 1)‖ := congrArg norm h
    _ = ‖L 1‖ := (InnerProductSpace.toDualMap ℝ ℝ).norm_map _
    _ = |L 1| := Real.norm_eq_abs _

private theorem realPair_dual_apply (L : StrongDual ℝ (ℝ × ℝ)) (x y : ℝ) :
    L (x, y) = x * L (1, 0) + y * L (0, 1) := by
  have hp : (x, y) = x • (1, 0) + y • (0, 1) := by ext <;> simp
  rw [hp, map_add, map_smul, map_smul]
  simp only [smul_eq_mul]

section InnerSpace

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  [FiniteDimensional ℝ F] [MeasurableSpace F] [BorelSpace F]

def gaussianProjectionPair (u v : F) : F →L[ℝ] (ℝ × ℝ) :=
  (innerSL ℝ u).prod (innerSL ℝ v)

def gaussianCorrelatedPair (ρ σ : ℝ) : (ℝ × ℝ) →L[ℝ] (ℝ × ℝ) :=
  (ContinuousLinearMap.fst ℝ ℝ ℝ).prod
    (ρ • ContinuousLinearMap.fst ℝ ℝ ℝ + σ • ContinuousLinearMap.snd ℝ ℝ ℝ)

theorem map_gaussianProjectionPair (u v : F) (hu : ‖u‖ = 1) (hv : ‖v‖ = 1)
    (σ : ℝ) (hσ : ⟪u, v⟫_ℝ ^ 2 + σ ^ 2 = 1) :
    (stdGaussian F).map (gaussianProjectionPair u v) =
      ((gaussianReal 0 1).prod (gaussianReal 0 1)).map
        (gaussianCorrelatedPair ⟪u, v⟫_ℝ σ) := by
  apply Measure.ext_of_charFunDual
  funext L
  rw [charFunDual_map, charFunDual_map, charFunDual_prod]
  simp_rw [← stdGaussian_real, charFunDual_stdGaussian]
  let a : ℝ := L (1, 0)
  let b : ℝ := L (0, 1)
  have hform : L.comp (gaussianProjectionPair u v) =
      InnerProductSpace.toDualMap ℝ F (a • u + b • v) := by
    ext x
    simp only [ContinuousLinearMap.comp_apply, gaussianProjectionPair,
      ContinuousLinearMap.prod_apply, innerSL_apply_apply,
      InnerProductSpace.toDualMap_apply_apply, inner_add_left, real_inner_smul_left]
    simpa [a, b, mul_comm] using realPair_dual_apply L ⟪u, x⟫_ℝ ⟪v, x⟫_ℝ
  have hleft : ((L.comp (gaussianCorrelatedPair ⟪u, v⟫_ℝ σ)).comp
      (ContinuousLinearMap.inl ℝ ℝ ℝ)) 1 = a + ⟪u, v⟫_ℝ * b := by
    change L (1, ⟪u, v⟫_ℝ * 1 + σ * 0) = _
    simp only [mul_one, mul_zero, add_zero]
    rw [realPair_dual_apply]
    dsimp [a, b]
    ring
  have hright : ((L.comp (gaussianCorrelatedPair ⟪u, v⟫_ℝ σ)).comp
      (ContinuousLinearMap.inr ℝ ℝ ℝ)) 1 = σ * b := by
    change L (0, ⟪u, v⟫_ℝ * 0 + σ * 1) = _
    simp only [mul_one, mul_zero, zero_add]
    rw [realPair_dual_apply]
    dsimp [b]
    ring
  have hn : ‖L.comp (gaussianProjectionPair u v)‖ ^ 2 =
      ‖(L.comp (gaussianCorrelatedPair ⟪u, v⟫_ℝ σ)).comp (ContinuousLinearMap.inl ℝ ℝ ℝ)‖ ^ 2 +
      ‖(L.comp (gaussianCorrelatedPair ⟪u, v⟫_ℝ σ)).comp (ContinuousLinearMap.inr ℝ ℝ ℝ)‖ ^ 2 := by
    rw [hform, LinearIsometry.norm_map, realStrongDual_norm, realStrongDual_norm,
      hleft, hright, sq_abs, sq_abs, norm_add_sq_real]
    simp only [norm_smul, Real.norm_eq_abs, mul_pow, sq_abs, hu, hv,
      real_inner_smul_left, real_inner_smul_right]
    have hm := congrArg (fun t : ℝ => b ^ 2 * t) hσ
    nlinarith [hm]
  have hnC : (‖L.comp (gaussianProjectionPair u v)‖ : ℂ) ^ 2 =
      (‖(L.comp (gaussianCorrelatedPair ⟪u, v⟫_ℝ σ)).comp (ContinuousLinearMap.inl ℝ ℝ ℝ)‖ : ℂ) ^ 2 +
      (‖(L.comp (gaussianCorrelatedPair ⟪u, v⟫_ℝ σ)).comp (ContinuousLinearMap.inr ℝ ℝ ℝ)‖ : ℂ) ^ 2 := by
    exact_mod_cast hn
  rw [hnC, ← Complex.exp_add]
  congr 1
  ring

theorem map_standardGaussian_unit_inner (u : F) (hu : ‖u‖ = 1) :
    (stdGaussian F).map (innerSL ℝ u) = gaussianReal 0 1 := by
  rw [IsGaussian.map_eq_gaussianReal, integral_strongDual_stdGaussian,
    variance_dual_stdGaussian, innerSL_apply_norm, hu]
  norm_num

theorem integral_gaussianScore_inner_sq (u : F) (hu : ‖u‖ = 1) :
    (∫ x : F, gaussianScore ⟪u, x⟫_ℝ ^ 2 ∂(stdGaussian F)) = Real.sqrt (3 / 5 : ℝ) := by
  rw [← integral_gaussianScore_sq, ← map_standardGaussian_unit_inner u hu,
    integral_map]
  · rfl
  · exact (innerSL ℝ u).continuous.measurable.aemeasurable
  · unfold gaussianScore
    fun_prop

theorem integrable_gaussianScore_product {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsFiniteMeasure μ] (f g : Ω → ℝ) (hf : Measurable f) (hg : Measurable g) :
    Integrable (fun x => gaussianScore (f x) * gaussianScore (g x)) μ := by
  apply Integrable.of_bound ?_ 1
  · filter_upwards with x
    rw [Real.norm_eq_abs, abs_of_nonneg
      (mul_nonneg (gaussianScore_pos _).le (gaussianScore_pos _).le)]
    calc
      _ ≤ (1 : ℝ) * 1 := mul_le_mul (gaussianScore_le_one _) (gaussianScore_le_one _)
        (gaussianScore_pos _).le (by norm_num)
      _ = 1 := by ring
  · unfold gaussianScore
    fun_prop

theorem integral_gaussianScore_inner_mul (u v : F) (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) :
    (∫ x : F, gaussianScore ⟪u, x⟫_ℝ * gaussianScore ⟪v, x⟫_ℝ ∂(stdGaussian F)) =
      3 / Real.sqrt (16 - ⟪u, v⟫_ℝ ^ 2) := by
  have hr : ⟪u, v⟫_ℝ ^ 2 ≤ 1 := by
    have h := norm_inner_le_norm (𝕜 := ℝ) u v
    rw [hu, hv, mul_one, Real.norm_eq_abs] at h
    exact (sq_le_one_iff_abs_le_one ⟪u, v⟫_ℝ).mpr h
  let σ : ℝ := Real.sqrt (1 - ⟪u, v⟫_ℝ ^ 2)
  have hσ : ⟪u, v⟫_ℝ ^ 2 + σ ^ 2 = 1 := by
    dsimp [σ]
    rw [Real.sq_sqrt (sub_nonneg.mpr hr)]
    ring
  have hmap := map_gaussianProjectionPair u v hu hv σ hσ
  have h := congrArg (fun μ : Measure (ℝ × ℝ) =>
    ∫ p, gaussianScore p.1 * gaussianScore p.2 ∂μ) hmap
  rw [integral_map, integral_map] at h
  · have hint : Integrable
        (fun p : ℝ × ℝ => gaussianScore p.1 * gaussianScore (⟪u, v⟫_ℝ * p.1 + σ * p.2))
        ((gaussianReal 0 1).prod (gaussianReal 0 1)) :=
      integrable_gaussianScore_product _ _ _ (by fun_prop) (by fun_prop)
    have hprod := integral_prod _ hint
    have hnorm :
        (∫ p : ℝ × ℝ, gaussianScore p.1 * gaussianScore (⟪u, v⟫_ℝ * p.1 + σ * p.2)
          ∂((gaussianReal 0 1).prod (gaussianReal 0 1))) =
        3 / Real.sqrt (16 - ⟪u, v⟫_ℝ ^ 2) := by
      rw [hprod]
      exact integral_gaussianScore_pair ⟪u, v⟫_ℝ σ hσ
    simpa [gaussianProjectionPair, gaussianCorrelatedPair] using h.trans hnorm
  · exact (gaussianCorrelatedPair ⟪u, v⟫_ℝ σ).continuous.measurable.aemeasurable
  · unfold gaussianScore
    fun_prop
  · exact (gaussianProjectionPair u v).continuous.measurable.aemeasurable
  · unfold gaussianScore
    fun_prop

end InnerSpace
end CubeSections
