import CubeSections.Analysis.GaussianLaw
import CubeSections.Analysis.GaussianCost
import CubeSections.Analysis.PairEnergy

/-! The Gaussian pair test, with explicit Gaussian marginal and integrable energy. -/

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped InnerProductSpace RealInnerProductSpace

namespace CubeSections

section InnerSpace

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  [FiniteDimensional ℝ F] [MeasurableSpace F] [BorelSpace F]

def gaussianPairObservable (u v : F) (a b : ℝ) (x : F) : ℝ :=
  (a * gaussianScore ⟪u, x⟫_ℝ - b * gaussianScore ⟪v, x⟫_ℝ) ^ 2

theorem integral_gaussianPairObservable (u v : F) (hu : ‖u‖ = 1) (hv : ‖v‖ = 1)
    (a b : ℝ) :
    (∫ x : F, gaussianPairObservable u v a b x ∂(stdGaussian F)) =
      gaussianPairCost (⟪u, v⟫_ℝ ^ 2) a b := by
  have hU : Integrable (fun x : F => gaussianScore ⟪u, x⟫_ℝ ^ 2) (stdGaussian F) := by
    simpa only [pow_two] using integrable_gaussianScore_product (stdGaussian F)
      (fun x => ⟪u, x⟫_ℝ) (fun x => ⟪u, x⟫_ℝ) (by fun_prop) (by fun_prop)
  have hV : Integrable (fun x : F => gaussianScore ⟪v, x⟫_ℝ ^ 2) (stdGaussian F) := by
    simpa only [pow_two] using integrable_gaussianScore_product (stdGaussian F)
      (fun x => ⟪v, x⟫_ℝ) (fun x => ⟪v, x⟫_ℝ) (by fun_prop) (by fun_prop)
  have hUV := integrable_gaussianScore_product (stdGaussian F)
    (fun x => ⟪u, x⟫_ℝ) (fun x => ⟪v, x⟫_ℝ) (by fun_prop) (by fun_prop)
  have hfun : gaussianPairObservable u v a b =
      (fun x => a ^ 2 * gaussianScore ⟪u, x⟫_ℝ ^ 2 + b ^ 2 * gaussianScore ⟪v, x⟫_ℝ ^ 2 -
        (2 * a * b) * (gaussianScore ⟪u, x⟫_ℝ * gaussianScore ⟪v, x⟫_ℝ)) := by
    funext x
    unfold gaussianPairObservable
    ring
  rw [hfun]
  have hs := integral_sub ((hU.const_mul (a ^ 2)).add (hV.const_mul (b ^ 2)))
    (hUV.const_mul (2 * a * b))
  simp only [Pi.add_apply] at hs
  rw [hs, integral_add (hU.const_mul (a ^ 2)) (hV.const_mul (b ^ 2))]
  simp_rw [integral_const_mul, integral_gaussianScore_inner_sq u hu,
    integral_gaussianScore_inner_sq v hv, integral_gaussianScore_inner_mul u v hu hv]
  unfold gaussianPairCost gaussianSecondMoment gaussianCrossMoment
  ring

theorem integral_gaussianPairObservable_lower (u v : F) (hu : ‖u‖ = 1) (hv : ‖v‖ = 1)
    (a b : ℝ) (hab : a = 1 ∨ b = 1) :
    gaussianSecondMoment * ((1 - ⟪u, v⟫_ℝ ^ 2) / (16 - ⟪u, v⟫_ℝ ^ 2)) ≤
      (∫ x : F, gaussianPairObservable u v a b x ∂(stdGaussian F)) := by
  rw [integral_gaussianPairObservable u v hu hv]
  apply gaussianPairCost_lower _ _ _ _ hab
  have h := norm_inner_le_norm (𝕜 := ℝ) u v
  rw [hu, hv, mul_one, Real.norm_eq_abs] at h
  exact (sq_le_one_iff_abs_le_one ⟪u, v⟫_ℝ).mpr h

def potentialPairEnergy (A B β η T S G H : ℝ) : ℝ :=
  phi |(β + T ^ 2 / 2) - (η + S ^ 2 / 2)| +
    (T - G) ^ 2 / (2 * (1 - A)) + (S - H) ^ 2 / (2 * (1 - B))

theorem integral_potentialPairEnergy_lower
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (G : Ω → F) (hG : MeasurePreserving G μ (stdGaussian F))
    (u v : F) (hu : ‖u‖ = 1) (hv : ‖v‖ = 1)
    (A B β η : ℝ) (hA : A < 1) (hB : B < 1)
    (hβ : 0 ≤ β) (hη : 0 ≤ η) (hzero : β = 0 ∨ η = 0)
    (T S : Ω → ℝ)
    (hE : Integrable (fun ω => potentialPairEnergy A B β η (T ω) (S ω)
      ⟪u, G ω⟫_ℝ ⟪v, G ω⟫_ℝ) μ) :
    (gaussianSecondMoment * ((1 - ⟪u, v⟫_ℝ ^ 2) / (16 - ⟪u, v⟫_ℝ ^ 2))) /
        pairTransferCoeff A B ≤
      ∫ ω, potentialPairEnergy A B β η (T ω) (S ω) ⟪u, G ω⟫_ℝ ⟪v, G ω⟫_ℝ ∂μ := by
  let a : ℝ := Real.exp (-β / 3)
  let b : ℝ := Real.exp (-η / 3)
  have hab : a = 1 ∨ b = 1 := by
    rcases hzero with h | h
    · left; simp [a, h]
    · right; simp [b, h]
  have hmoment :
      (∫ ω, gaussianPairObservable u v a b (G ω) ∂μ) =
      (∫ x : F, gaussianPairObservable u v a b x ∂(stdGaussian F)) := by
    rw [← hG.map_eq, integral_map hG.measurable.aemeasurable]
    unfold gaussianPairObservable gaussianScore
    fun_prop
  have hlow := integral_gaussianPairObservable_lower u v hu hv a b hab
  rw [← hmoment] at hlow
  have hup := integral_mono_of_nonneg
    (Filter.Eventually.of_forall (fun ω => sq_nonneg
      (a * gaussianScore ⟪u, G ω⟫_ℝ - b * gaussianScore ⟪v, G ω⟫_ℝ)))
    (hE.const_mul (pairTransferCoeff A B))
    (Filter.Eventually.of_forall (fun ω =>
      potential_pair_transfer_bound A B β η (T ω) (S ω) ⟪u, G ω⟫_ℝ ⟪v, G ω⟫_ℝ
        hA hB hβ hη))
  rw [integral_const_mul] at hup
  apply (div_le_iff₀ (pairTransferCoeff_pos A B hA hB)).mpr
  exact (hlow.trans hup).trans_eq (mul_comm _ _)

end InnerSpace
end CubeSections
