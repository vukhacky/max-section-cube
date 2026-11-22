import CubeSections.Analysis.GaussianStein
import CubeSections.Analysis.TransportDensity
import CubeSections.Analysis.GaussianDensity
import Mathlib.MeasureTheory.Function.JacobianOneDim
import Mathlib.Topology.Order.LeftRightNhds

/-! Actual smooth increasing compact perturbations of the identity, their
change of variables, and their Gaussian Radon–Nikodym density. -/

noncomputable section
open Set Filter MeasureTheory ProbabilityTheory ContinuousLinearMap
open scoped ContDiff NNReal ENNReal Topology

namespace CubeSections

/-- The explicit regularity class used in the one-dimensional transport step. -/
structure CompactGaussianPerturbation where
  displacement : ℝ → ℝ
  contDiff : ContDiff ℝ 1 displacement
  compactSupport : HasCompactSupport displacement
  slope_pos : ∀ x, 0 < 1 + deriv displacement x

namespace CompactGaussianPerturbation

variable (d : CompactGaussianPerturbation)

def map (x : ℝ) : ℝ := x + d.displacement x
def slope (x : ℝ) : ℝ := 1 + deriv d.displacement x

theorem positive_slope (x : ℝ) : 0 < d.slope x := d.slope_pos x

@[fun_prop] theorem continuous_map : Continuous d.map := continuous_id.add d.contDiff.continuous
@[fun_prop] theorem continuous_slope : Continuous d.slope := continuous_const.add d.contDiff.continuous_deriv_one
@[fun_prop] theorem measurable_map : Measurable d.map := d.continuous_map.measurable
@[fun_prop] theorem measurable_slope : Measurable d.slope := d.continuous_slope.measurable

theorem hasDerivAt_map (x : ℝ) : HasDerivAt d.map (d.slope x) x :=
  (hasDerivAt_id x).add (d.contDiff.differentiable (by norm_num) x).hasDerivAt

theorem strictMono_map : StrictMono d.map := by
  apply strictMono_of_deriv_pos
  intro x
  rw [(d.hasDerivAt_map x).deriv]
  exact d.positive_slope x

theorem surjective_map : Function.Surjective d.map := by
  apply d.continuous_map.surjective
  · exact tendsto_id.atTop_add (d.compactSupport.is_zero_at_infty.mono_left atTop_le_cocompact)
  · exact tendsto_id.atBot_add (d.compactSupport.is_zero_at_infty.mono_left atBot_le_cocompact)

def homeomorph : ℝ ≃ₜ ℝ :=
  (StrictMono.orderIsoOfSurjective d.map d.strictMono_map d.surjective_map).toHomeomorph

def inverse : ℝ → ℝ := d.homeomorph.symm

@[simp] theorem inverse_map (x : ℝ) : d.inverse (d.map x) = x := d.homeomorph.symm_apply_apply x
@[simp] theorem map_inverse (x : ℝ) : d.map (d.inverse x) = x := d.homeomorph.apply_symm_apply x
@[fun_prop] theorem continuous_inverse : Continuous d.inverse := d.homeomorph.symm.continuous
@[fun_prop] theorem measurable_inverse : Measurable d.inverse := d.continuous_inverse.measurable

theorem map_jacobian :
    (volume.withDensity (fun x => ENNReal.ofReal (d.slope x))).map d.map = volume := by
  have h := map_withDensity_abs_det_fderiv_eq_addHaar volume
    (s := (univ : Set ℝ)) (MeasurableSet.univ : MeasurableSet (univ : Set ℝ)).nullMeasurableSet
    (fun x _ => (d.hasDerivAt_map x).hasDerivWithinAt.hasFDerivWithinAt) d.strictMono_map.injective.injOn
  simpa only [Measure.restrict_univ, image_univ, d.surjective_map.range_eq,
    det_toSpanSingleton, abs_of_pos (d.positive_slope _)] using h

def law : Measure ℝ := (gaussianReal 0 1).map d.map

instance law_probability : IsProbabilityMeasure d.law := by
  unfold law
  infer_instance

def lebesgueDensity (y : ℝ) : ℝ :=
  gaussianPDFReal 0 1 (d.inverse y) / d.slope (d.inverse y)

theorem lebesgueDensity_pos (y : ℝ) : 0 < d.lebesgueDensity y :=
  div_pos (gaussianPDFReal_pos 0 1 _ (by norm_num)) (d.positive_slope _)

@[fun_prop] theorem continuous_lebesgueDensity : Continuous d.lebesgueDensity :=
  (continuous_standardGaussianPDF.comp d.continuous_inverse).div
    (d.continuous_slope.comp d.continuous_inverse) (fun _ => ne_of_gt (d.positive_slope _))

@[fun_prop] theorem measurable_lebesgueDensity : Measurable d.lebesgueDensity :=
  d.continuous_lebesgueDensity.measurable

theorem jacobian_density (x : ℝ) :
    ENNReal.ofReal (d.slope x) * ENNReal.ofReal (d.lebesgueDensity (d.map x)) =
      gaussianPDF 0 1 x := by
  rw [← ENNReal.ofReal_mul (d.positive_slope x).le, lebesgueDensity, d.inverse_map, gaussianPDF_def]
  congr 1
  field_simp [ne_of_gt (d.positive_slope x)]

theorem law_eq_lebesgue_withDensity :
    d.law = volume.withDensity (fun y => ENNReal.ofReal (d.lebesgueDensity y)) := by
  rw [← d.map_jacobian,
    ← map_withDensity_comp_eq _ _ d.measurable_map _ d.measurable_lebesgueDensity.ennreal_ofReal]
  unfold law
  congr 1
  have hm := withDensity_mul volume d.measurable_slope.ennreal_ofReal
    (d.measurable_lebesgueDensity.ennreal_ofReal.comp d.measurable_map)
  simp only [Function.comp_def] at hm
  rw [← hm, gaussianReal_of_var_ne_zero 0 (by norm_num : (1 : ℝ≥0) ≠ 0)]
  apply withDensity_congr_ae
  exact ae_of_all _ (fun x => (d.jacobian_density x).symm)

def gaussianDensity (y : ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal (d.lebesgueDensity y) / ENNReal.ofReal (gaussianPDFReal 0 1 y)

@[fun_prop] theorem measurable_gaussianDensity : Measurable d.gaussianDensity :=
  d.measurable_lebesgueDensity.ennreal_ofReal.div (measurable_gaussianPDFReal 0 1).ennreal_ofReal

theorem law_eq_gaussian_withDensity : d.law = (gaussianReal 0 1).withDensity d.gaussianDensity := by
  rw [gaussianReal_of_var_ne_zero 0 (by norm_num : (1 : ℝ≥0) ≠ 0),
    ← withDensity_mul _ (measurable_gaussianPDF 0 1) d.measurable_gaussianDensity,
    d.law_eq_lebesgue_withDensity]
  congr 1
  funext y
  exact (ENNReal.mul_div_cancel
    (ne_of_gt (ENNReal.ofReal_pos.mpr (gaussianPDFReal_pos 0 1 y (by norm_num))))
    ENNReal.ofReal_ne_top).symm

theorem absolutelyContinuous_gaussian : d.law ≪ gaussianReal 0 1 := by
  rw [d.law_eq_gaussian_withDensity]
  exact withDensity_absolutelyContinuous _ _

theorem rnDeriv_law : d.law.rnDeriv (gaussianReal 0 1) =ᵐ[gaussianReal 0 1] d.gaussianDensity := by
  rw [d.law_eq_gaussian_withDensity]
  exact Measure.rnDeriv_withDensity _ d.measurable_gaussianDensity

theorem log_gaussianDensity_map (x : ℝ) :
    Real.log (d.gaussianDensity (d.map x)).toReal =
      ((d.map x) ^ 2 - x ^ 2) / 2 - Real.log (d.slope x) := by
  have hp := gaussianPDFReal_pos 0 1 x (by norm_num)
  have hq := gaussianPDFReal_pos 0 1 (d.map x) (by norm_num)
  rw [gaussianDensity, ENNReal.toReal_div,
    ENNReal.toReal_ofReal (d.lebesgueDensity_pos _).le, ENNReal.toReal_ofReal hq.le,
    lebesgueDensity, d.inverse_map,
    Real.log_div (div_ne_zero (ne_of_gt hp) (ne_of_gt (d.positive_slope x))) (ne_of_gt hq),
    Real.log_div (ne_of_gt hp) (ne_of_gt (d.positive_slope x)),
    log_standardGaussianPDF, log_standardGaussianPDF]
  ring

end CompactGaussianPerturbation
end CubeSections
