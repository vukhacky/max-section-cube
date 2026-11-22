import CubeSections.Analysis.PositiveDensityInverse
import CubeSections.Analysis.GaussianDensity
import Mathlib.InformationTheory.KullbackLeibler.Basic
import Mathlib.MeasureTheory.Function.L2Space

/-! Gaussian quadratic transport for actual positive continuous line densities.
The density, inverse quantile, graph coupling, and entropy are literal objects.
The intermediate theorem keeps only the explicitly displayed monotone Stein
identity and derivative integrability; these are discharged downstream.
-/
noncomputable section
open Set MeasureTheory ProbabilityTheory InformationTheory
open scoped NNReal ENNReal ContDiff
namespace CubeSections

local notation "γ" => gaussianReal 0 1

def positiveDensityGaussianRatio (f : ℝ → ℝ) (y : ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal (f y) / ENNReal.ofReal (gaussianPDFReal 0 1 y)

theorem measurable_positiveDensityGaussianRatio {f : ℝ → ℝ} (hc : Continuous f) :
    Measurable (positiveDensityGaussianRatio f) :=
  hc.measurable.ennreal_ofReal.div (measurable_gaussianPDFReal 0 1).ennreal_ofReal

theorem positiveDensityLaw_eq_gaussian_withDensity {f : ℝ → ℝ} (hc : Continuous f) :
    positiveDensityLaw f = (γ).withDensity (positiveDensityGaussianRatio f) := by
  rw [gaussianReal_of_var_ne_zero 0 (by norm_num : (1 : ℝ≥0) ≠ 0),
    ← withDensity_mul _ (measurable_gaussianPDF 0 1) (measurable_positiveDensityGaussianRatio hc)]
  unfold positiveDensityLaw
  congr 1
  funext y
  exact (ENNReal.mul_div_cancel
    (ne_of_gt (ENNReal.ofReal_pos.mpr (gaussianPDFReal_pos 0 1 y (by norm_num))))
    ENNReal.ofReal_ne_top).symm

theorem positiveDensityLaw_absolutelyContinuous_gaussian {f : ℝ → ℝ} (hc : Continuous f) :
    positiveDensityLaw f ≪ γ := by
  rw [positiveDensityLaw_eq_gaussian_withDensity hc]
  exact withDensity_absolutelyContinuous _ _

theorem positiveDensityLaw_rnDeriv_gaussian {f : ℝ → ℝ} (hc : Continuous f) :
    (positiveDensityLaw f).rnDeriv γ =ᵐ[γ] positiveDensityGaussianRatio f := by
  rw [positiveDensityLaw_eq_gaussian_withDensity hc]
  exact Measure.rnDeriv_withDensity _ (measurable_positiveDensityGaussianRatio hc)

section PositiveDensity
variable (f : ℝ → ℝ) (hc : Continuous f) (hi : Integrable f)
  (hp : ∀ x, 0 < f x) (hm : (∫ x, f x)=1)

local notation "G" => positiveDensityInverse f hc hi hp hm

def positiveDensityInverseEntropy (x : ℝ) : ℝ :=
  ((G x)^2-x^2)/2-Real.log (deriv G x)

theorem log_positiveDensityGaussianRatio_inverse (x : ℝ) :
    Real.log (positiveDensityGaussianRatio f (G x)).toReal =
      positiveDensityInverseEntropy f hc hi hp hm x := by
  have hφx := gaussianPDFReal_pos 0 1 x (by norm_num)
  have hφg := gaussianPDFReal_pos 0 1 (G x) (by norm_num)
  rw [positiveDensityGaussianRatio, ENNReal.toReal_div,
    ENNReal.toReal_ofReal (hp _).le, ENNReal.toReal_ofReal hφg.le,
    Real.log_div (ne_of_gt (hp _)) (ne_of_gt hφg)]
  unfold positiveDensityInverseEntropy
  rw [(hasDerivAt_positiveDensityInverse hc hi hp hm x).deriv,
    Real.log_div (ne_of_gt hφx) (ne_of_gt (hp _)),
    log_standardGaussianPDF, log_standardGaussianPDF]
  ring

theorem positiveDensityInverse_llr :
    (fun x => llr (positiveDensityLaw f) γ (G x)) =ᵐ[γ]
      positiveDensityInverseEntropy f hc hi hp hm := by
  have hν := (positiveDensityLaw_absolutelyContinuous_gaussian hc).ae_le
    (positiveDensityLaw_rnDeriv_gaussian hc)
  have hmap : ∀ᵐ y ∂(γ).map G,
      (positiveDensityLaw f).rnDeriv γ y = positiveDensityGaussianRatio f y := by
    rw [positiveDensityInverse_map_law hc hi hp hm]
    exact hν
  have hsrc := ae_of_ae_map (measurable_positiveDensityInverse hc hi hp hm).aemeasurable hmap
  filter_upwards [hsrc] with x hx
  rw [llr, hx]
  exact log_positiveDensityGaussianRatio_inverse f hc hi hp hm x

theorem memLp_positiveDensityInverse_two (hL2 : MemLp id 2 (positiveDensityLaw f)) :
    MemLp G 2 γ := by
  simpa only [Function.comp_def, id_eq] using
    hL2.comp_measurePreserving (positiveDensityInverse_measurePreserving hc hi hp hm)

theorem integrable_positiveDensityInverseEntropy
    (hKL : klDiv (positiveDensityLaw f) γ ≠ (⊤ : ℝ≥0∞)) :
    Integrable (positiveDensityInverseEntropy f hc hi hp hm) γ := by
  have hllr := (klDiv_ne_top_iff.mp hKL).2
  have hpull := (positiveDensityInverse_measurePreserving hc hi hp hm).integrable_comp_of_integrable hllr
  exact hpull.congr (positiveDensityInverse_llr f hc hi hp hm)

theorem integrable_log_positiveDensityInverse_deriv
    (hL2 : MemLp id 2 (positiveDensityLaw f))
    (hKL : klDiv (positiveDensityLaw f) γ ≠ (⊤ : ℝ≥0∞)) :
    Integrable (fun x => Real.log (deriv G x)) γ := by
  have hq := ((memLp_positiveDensityInverse_two f hc hi hp hm hL2).integrable_sq.sub
    (memLp_id_gaussianReal (μ := 0) (v := 1) 2).integrable_sq).div_const 2
  have h := hq.sub (integrable_positiveDensityInverseEntropy f hc hi hp hm hKL)
  apply h.congr
  filter_upwards with x
  simp only [Pi.sub_apply, id_eq, positiveDensityInverseEntropy]
  ring

theorem positiveDensity_klDiv_eq_inverseEntropy
    (hKL : klDiv (positiveDensityLaw f) γ ≠ (⊤ : ℝ≥0∞)) :
    (klDiv (positiveDensityLaw f) γ).toReal =
      ∫ x, positiveDensityInverseEntropy f hc hi hp hm x ∂γ := by
  letI := positiveDensityLaw_isProbabilityMeasure hi hp hm
  rw [toReal_klDiv_of_measure_eq (positiveDensityLaw_absolutelyContinuous_gaussian hc) (by simp)]
  have hllr := (klDiv_ne_top_iff.mp hKL).2
  have hmap := positiveDensityInverse_map_law hc hi hp hm
  have hpull : (∫ x, llr (positiveDensityLaw f) γ (G x) ∂γ) =
      ∫ y, llr (positiveDensityLaw f) γ y ∂positiveDensityLaw f := by
    have hmeas : AEStronglyMeasurable (llr (positiveDensityLaw f) γ) ((γ).map G) :=
      hmap.symm ▸ hllr.aestronglyMeasurable
    rw [← integral_map (measurable_positiveDensityInverse hc hi hp hm).aemeasurable hmeas, hmap]
  exact hpull.symm.trans (integral_congr_ae (positiveDensityInverse_llr f hc hi hp hm))

theorem measurable_positiveDensityInverse_pair : Measurable (fun x => (G x,x)) :=
  (measurable_positiveDensityInverse hc hi hp hm).prodMk measurable_id

def positiveDensityInverseCoupling : Measure (ℝ × ℝ) :=
  (γ).map (fun x => (G x,x))

theorem positiveDensityInverseCoupling_probability :
    IsProbabilityMeasure (positiveDensityInverseCoupling f hc hi hp hm) := by
  unfold positiveDensityInverseCoupling
  infer_instance

theorem positiveDensityInverseCoupling_fst :
    (positiveDensityInverseCoupling f hc hi hp hm).map Prod.fst = positiveDensityLaw f := by
  rw [positiveDensityInverseCoupling, Measure.map_map measurable_fst
    (measurable_positiveDensityInverse_pair f hc hi hp hm)]
  exact positiveDensityInverse_map_law hc hi hp hm

theorem positiveDensityInverseCoupling_snd :
    (positiveDensityInverseCoupling f hc hi hp hm).map Prod.snd = γ := by
  rw [positiveDensityInverseCoupling, Measure.map_map measurable_snd
    (measurable_positiveDensityInverse_pair f hc hi hp hm)]
  exact Measure.map_id

theorem positiveDensityInverseCoupling_cost_integrable
    (hL2 : MemLp id 2 (positiveDensityLaw f)) :
    Integrable (fun p : ℝ × ℝ => |p.1-p.2|^2)
      (positiveDensityInverseCoupling f hc hi hp hm) := by
  apply (integrable_map_measure (by fun_prop)
    (measurable_positiveDensityInverse_pair f hc hi hp hm).aemeasurable).mpr
  simpa only [Function.comp_def, Pi.sub_apply, id_eq, sq_abs] using
    ((memLp_positiveDensityInverse_two f hc hi hp hm hL2).sub
      (memLp_id_gaussianReal (μ := 0) (v := 1) 2)).integrable_sq

theorem positiveDensityInverseCoupling_cost :
    (∫ p : ℝ × ℝ, |p.1-p.2|^2 ∂positiveDensityInverseCoupling f hc hi hp hm) =
      ∫ x, (G x-x)^2 ∂γ := by
  rw [positiveDensityInverseCoupling, integral_map
    (measurable_positiveDensityInverse_pair f hc hi hp hm).aemeasurable (by fun_prop)]
  apply integral_congr_ae
  filter_upwards with x
  simp only [sq_abs]

/-- The only intermediate assumptions are the literal one-dimensional Stein
identity and integrability of the nonnegative derivative. -/
theorem positiveDensityInverse_cost_le_twice_klDiv_of_stein
    (hL2 : MemLp id 2 (positiveDensityLaw f))
    (hKL : klDiv (positiveDensityLaw f) γ ≠ (⊤ : ℝ≥0∞))
    (hdi : Integrable (deriv G) γ)
    (hstein : (∫ x, deriv G x ∂γ) = ∫ x, x*G x ∂γ) :
    (∫ x, (G x-x)^2 ∂γ) ≤ 2*(klDiv (positiveDensityLaw f) γ).toReal := by
  have hg := memLp_positiveDensityInverse_two f hc hi hp hm hL2
  have hx : MemLp id (2 : ℝ≥0∞) γ := by
    simpa using memLp_id_gaussianReal (μ := 0) (v := 1) (2 : ℝ≥0)
  have hcost : Integrable (fun x => (G x-x)^2) γ := by
    simpa only [Pi.sub_apply, id_eq] using (hg.sub hx).integrable_sq
  have hcross : Integrable (fun x => x*G x) γ := by
    apply (hx.integrable_mul hg).congr
    filter_upwards with x
    rfl
  have hsq : Integrable (fun x : ℝ => x^2) γ := by simpa only [id_eq] using hx.integrable_sq
  have hE := integrable_positiveDensityInverseEntropy f hc hi hp hm hKL
  have hsum : Integrable (fun x => (G x-x)^2/2+x*G x-x^2-deriv G x+1) γ :=
    (((hcost.div_const 2).add hcross).sub hsq).sub hdi |>.add (integrable_const 1)
  have hpoint (x : ℝ) :
      (G x-x)^2/2+x*G x-x^2-deriv G x+1 ≤ positiveDensityInverseEntropy f hc hi hp hm x := by
    have hlog := Real.log_le_sub_one_of_pos (positiveDensityInverse_deriv_pos hc hi hp hm x)
    unfold positiveDensityInverseEntropy
    nlinarith
  have hb := integral_mono hsum hE hpoint
  have hvar := variance_id_gaussianReal (μ := 0) (v := 1)
  rw [variance_eq_integral measurable_id.aemeasurable] at hvar
  change (∫ x : ℝ, (x-∫ x : ℝ, x ∂γ)^2 ∂γ) = (1 : ℝ) at hvar
  simp only [integral_id_gaussianReal, sub_zero] at hvar
  rw [integral_add
      (f := fun x => (G x-x)^2/2+x*G x-x^2-deriv G x) (g := fun _ => (1 : ℝ))
      ((((hcost.div_const 2).add hcross).sub hsq).sub hdi) (integrable_const 1),
    integral_sub
      (f := fun x => (G x-x)^2/2+x*G x-x^2) (g := deriv G)
      (((hcost.div_const 2).add hcross).sub hsq) hdi,
    integral_sub
      (f := fun x => (G x-x)^2/2+x*G x) (g := fun x => x^2)
      ((hcost.div_const 2).add hcross) hsq,
    integral_add
      (f := fun x => (G x-x)^2/2) (g := fun x => x*G x)
      (hcost.div_const 2) hcross, integral_div, hvar, hstein,
    integral_const] at hb
  simp only [probReal_univ, one_smul] at hb
  rw [positiveDensity_klDiv_eq_inverseEntropy f hc hi hp hm hKL]
  linarith

theorem gaussian_quadratic_transport_positiveDensity_of_stein
    (hL2 : MemLp id 2 (positiveDensityLaw f))
    (hKL : klDiv (positiveDensityLaw f) γ ≠ (⊤ : ℝ≥0∞))
    (hdi : Integrable (deriv G) γ)
    (hstein : (∫ x, deriv G x ∂γ) = ∫ x, x*G x ∂γ) :
    ∃ π : Measure (ℝ × ℝ), IsProbabilityMeasure π ∧
      π.map Prod.fst = positiveDensityLaw f ∧ π.map Prod.snd = γ ∧
      Integrable (fun p : ℝ × ℝ => |p.1-p.2|^2) π ∧
      (∫ p : ℝ × ℝ, |p.1-p.2|^2 ∂π) ≤ 2*(klDiv (positiveDensityLaw f) γ).toReal := by
  refine ⟨positiveDensityInverseCoupling f hc hi hp hm,
    positiveDensityInverseCoupling_probability f hc hi hp hm,
    positiveDensityInverseCoupling_fst f hc hi hp hm,
    positiveDensityInverseCoupling_snd f hc hi hp hm,
    positiveDensityInverseCoupling_cost_integrable f hc hi hp hm hL2, ?_⟩
  rw [positiveDensityInverseCoupling_cost]
  exact positiveDensityInverse_cost_le_twice_klDiv_of_stein f hc hi hp hm hL2 hKL hdi hstein

end PositiveDensity
#print axioms positiveDensityInverse_llr
#print axioms positiveDensity_klDiv_eq_inverseEntropy
#print axioms gaussian_quadratic_transport_positiveDensity_of_stein
end CubeSections
