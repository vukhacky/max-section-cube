import CubeSections.Analysis.PositiveGaussianTalagrand

/-! Scalar density-weighted entropy formulas for the actual positive-density law.
Finite KL is explicitly used for weighted-log integrability; the formula alone
is never treated as a finiteness assertion. -/
noncomputable section
open MeasureTheory ProbabilityTheory InformationTheory
open scoped ENNReal NNReal
namespace CubeSections

local notation "γ" => gaussianReal 0 1

theorem positiveDensityLaw_integrable_iff {f : ℝ → ℝ}
    (hc : Continuous f) (hp : ∀ x, 0 < f x) (g : ℝ → ℝ) :
    Integrable g (positiveDensityLaw f) ↔ Integrable (fun x => f x*g x) := by
  unfold positiveDensityLaw
  simpa only [ENNReal.toReal_ofReal (hp _).le, smul_eq_mul] using
    (integrable_withDensity_iff_integrable_smul' (g := g) hc.measurable.ennreal_ofReal
      (ae_of_all _ (fun x => ENNReal.ofReal_lt_top)))

theorem positiveDensityLaw_integral {f : ℝ → ℝ}
    (hc : Continuous f) (hp : ∀ x, 0 < f x) (g : ℝ → ℝ) :
    (∫ x, g x ∂positiveDensityLaw f) = ∫ x, f x*g x := by
  unfold positiveDensityLaw
  rw [integral_withDensity_eq_integral_toReal_smul hc.measurable.ennreal_ofReal
    (ae_of_all _ (fun _ => ENNReal.ofReal_lt_top))]
  simp only [ENNReal.toReal_ofReal (hp _).le, smul_eq_mul]

theorem positiveDensityLaw_llr {f : ℝ → ℝ}
    (hc : Continuous f) (hp : ∀ x, 0 < f x) :
    llr (positiveDensityLaw f) γ =ᵐ[positiveDensityLaw f]
      fun x => Real.log (f x/gaussianPDFReal 0 1 x) := by
  filter_upwards [(positiveDensityLaw_absolutelyContinuous_gaussian hc).ae_le
    (positiveDensityLaw_rnDeriv_gaussian hc)] with x hx
  rw [llr, hx, positiveDensityGaussianRatio, ENNReal.toReal_div,
    ENNReal.toReal_ofReal (hp x).le,
    ENNReal.toReal_ofReal (gaussianPDFReal_pos 0 1 x (by norm_num)).le]

theorem integrable_positiveDensity_weighted_logRatio {f : ℝ → ℝ}
    (hc : Continuous f) (hp : ∀ x, 0 < f x)
    (hKL : klDiv (positiveDensityLaw f) γ ≠ (⊤ : ℝ≥0∞)) :
    Integrable (fun x => f x*Real.log (f x/gaussianPDFReal 0 1 x)) := by
  have h := ((klDiv_ne_top_iff.mp hKL).2).congr (positiveDensityLaw_llr hc hp)
  exact (positiveDensityLaw_integrable_iff hc hp _).mp h

theorem positiveDensity_klDiv_eq_densityIntegral {f : ℝ → ℝ}
    (hc : Continuous f) (hi : Integrable f) (hp : ∀ x, 0 < f x)
    (hm : (∫ x, f x)=1) :
    (klDiv (positiveDensityLaw f) γ).toReal =
      ∫ x, f x*Real.log (f x/gaussianPDFReal 0 1 x) := by
  letI := positiveDensityLaw_isProbabilityMeasure hi hp hm
  rw [toReal_klDiv_of_measure_eq (positiveDensityLaw_absolutelyContinuous_gaussian hc) (by simp),
    integral_congr_ae (positiveDensityLaw_llr hc hp), positiveDensityLaw_integral hc hp]

theorem positiveDensityLaw_memLp_two {f : ℝ → ℝ}
    (hc : Continuous f) (hp : ∀ x, 0 < f x)
    (hsecond : Integrable (fun x => x^2*f x)) : MemLp id 2 (positiveDensityLaw f) := by
  apply (memLp_two_iff_integrable_sq (by fun_prop)).mpr
  apply (positiveDensityLaw_integrable_iff hc hp _).mpr
  simpa only [id_eq, mul_comm] using hsecond

theorem positiveDensityLaw_entropy_integrable {f : ℝ → ℝ}
    (hc : Continuous f) (hi : Integrable f) (hp : ∀ x, 0 < f x)
    (hm : (∫ x, f x)=1)
    (hlog : Integrable (fun x => f x*Real.log (f x)))
    (hsecond : Integrable (fun x => x^2*f x)) :
    Integrable (llr (positiveDensityLaw f) γ) (positiveDensityLaw f) := by
  letI := positiveDensityLaw_isProbabilityMeasure hi hp hm
  have hL : Integrable (fun x => Real.log (f x)) (positiveDensityLaw f) :=
    (positiveDensityLaw_integrable_iff hc hp _).mpr hlog
  have hS : Integrable (fun x => x^2) (positiveDensityLaw f) :=
    (positiveDensityLaw_integrable_iff hc hp _).mpr (by simpa only [mul_comm] using hsecond)
  have hG : Integrable (fun x => Real.log (gaussianPDFReal 0 1 x)) (positiveDensityLaw f) := by
    simp_rw [log_standardGaussianPDF]
    exact (integrable_const _).sub (hS.div_const 2)
  apply ((hL.sub hG).congr ?_).congr (positiveDensityLaw_llr hc hp).symm
  exact ae_of_all _ (fun x => (Real.log_div (ne_of_gt (hp x))
    (ne_of_gt (gaussianPDFReal_pos 0 1 x (by norm_num)))).symm)

theorem positiveDensityLaw_klDiv_finite {f : ℝ → ℝ}
    (hc : Continuous f) (hi : Integrable f) (hp : ∀ x, 0 < f x)
    (hm : (∫ x, f x)=1)
    (hlog : Integrable (fun x => f x*Real.log (f x)))
    (hsecond : Integrable (fun x => x^2*f x)) :
    klDiv (positiveDensityLaw f) γ ≠ (⊤ : ℝ≥0∞) :=
  klDiv_ne_top (positiveDensityLaw_absolutelyContinuous_gaussian hc)
    (positiveDensityLaw_entropy_integrable hc hi hp hm hlog hsecond)

#print axioms integrable_positiveDensity_weighted_logRatio
#print axioms positiveDensity_klDiv_eq_densityIntegral
#print axioms positiveDensityLaw_klDiv_finite
end CubeSections
