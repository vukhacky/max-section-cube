import CubeSections.Analysis.PrekopaContracts
import CubeSections.Analysis.GaussianDensity
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral

/-! Integrability and marginal regularity under explicit Gaussian domination.
The product lemmas are stated for E n × R and do not choose an ambient
coordinate decomposition. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 600000
open MeasureTheory Set
open scoped BigOperators
namespace CubeSections

theorem gaussianNormKernel_eq_prod {n : ℕ} (a : ℝ) (x : E n) :
    Real.exp (-a*‖x‖^2) = ∏ i, Real.exp (-a*(x i)^2) := by
  rw [EuclideanSpace.real_norm_sq_eq, Finset.mul_sum, Real.exp_sum]

theorem integrable_gaussianNormKernel (n : ℕ) (a : ℝ) (ha : 0 < a) :
    Integrable (fun x : E n => Real.exp (-a*‖x‖^2)) := by
  have hi : Integrable (fun x : Fin n → ℝ => ∏ i, Real.exp (-a*(x i)^2)) :=
    Integrable.fintype_prod (μ := fun _ : Fin n => (volume : Measure ℝ))
      (f := fun _ : Fin n => fun s : ℝ => Real.exp (-a*s^2))
      (fun _ => integrable_exp_neg_mul_sq ha)
  apply ((PiLp.volume_preserving_toLp (Fin n)).integrable_comp_emb
    (g := fun x : E n => Real.exp (-a*‖x‖^2))
    (MeasurableEquiv.toLp 2 (Fin n → ℝ)).measurableEmbedding).1
  convert hi using 1
  funext x
  exact gaussianNormKernel_eq_prod a (WithLp.toLp 2 x)

theorem GaussianDominated.integrable {n : ℕ} {f : E n → ℝ}
    (hf : GaussianDominated f) (hc : Continuous f) : Integrable f := by
  obtain ⟨C,a,hC,ha,hbound⟩ := hf
  exact ((integrable_gaussianNormKernel n a ha).const_mul C).mono'
    hc.aestronglyMeasurable (ae_of_all _ (fun x => by
      rw [Real.norm_eq_abs]
      exact hbound x))

theorem gaussianProduct_bound_fiber {n : ℕ} (F : E n × ℝ → ℝ) (C a : ℝ)
    (hC : 0 ≤ C) (ha : 0 ≤ a)
    (hbound : ∀ x s, |F (x,s)| ≤ C*Real.exp (-a*(‖x‖^2+s^2))) (x : E n) (s : ℝ) :
    |F (x,s)| ≤ C*Real.exp (-a*s^2) := by
  exact (hbound x s).trans (mul_le_mul_of_nonneg_left
    (Real.exp_le_exp.mpr (by nlinarith [mul_nonneg ha (sq_nonneg ‖x‖)])) hC)

theorem gaussianProduct_fiber_integrable {n : ℕ} (F : E n × ℝ → ℝ) (C a : ℝ)
    (hC : 0 < C) (ha : 0 < a) (hc : Continuous F)
    (hbound : ∀ x s, |F (x,s)| ≤ C*Real.exp (-a*(‖x‖^2+s^2))) (x : E n) :
    Integrable (fun s : ℝ => F (x,s)) := by
  exact ((integrable_exp_neg_mul_sq ha).const_mul C).mono'
    (hc.comp (continuous_const.prodMk continuous_id)).aestronglyMeasurable
    (ae_of_all _ (fun s => by
      rw [Real.norm_eq_abs]
      exact gaussianProduct_bound_fiber F C a hC.le ha.le hbound x s))

theorem gaussianProduct_marginal_continuous {n : ℕ} (F : E n × ℝ → ℝ) (C a : ℝ)
    (hC : 0 < C) (ha : 0 < a) (hc : Continuous F)
    (hbound : ∀ x s, |F (x,s)| ≤ C*Real.exp (-a*(‖x‖^2+s^2))) :
    Continuous (fun x : E n => ∫ s : ℝ, F (x,s)) := by
  apply continuous_of_dominated
    (bound := fun s : ℝ => C*Real.exp (-a*s^2))
  · intro x
    exact (hc.comp (continuous_const.prodMk continuous_id)).aestronglyMeasurable
  · intro x
    exact ae_of_all _ (fun s => by
      rw [Real.norm_eq_abs]
      exact gaussianProduct_bound_fiber F C a hC.le ha.le hbound x s)
  · exact (integrable_exp_neg_mul_sq ha).const_mul C
  · exact ae_of_all _ (fun s => hc.comp (continuous_id.prodMk continuous_const))

theorem gaussianProduct_marginal_abs_le {n : ℕ} (F : E n × ℝ → ℝ) (C a : ℝ)
    (hC : 0 < C) (ha : 0 < a) (hc : Continuous F)
    (hbound : ∀ x s, |F (x,s)| ≤ C*Real.exp (-a*(‖x‖^2+s^2))) (x : E n) :
    |∫ s : ℝ, F (x,s)| ≤ (C*Real.sqrt (Real.pi/a))*Real.exp (-a*‖x‖^2) := by
  have hfi := gaussianProduct_fiber_integrable F C a hC ha hc hbound x
  have hmajor : Integrable (fun s : ℝ =>
      (C*Real.exp (-a*‖x‖^2))*Real.exp (-a*s^2)) :=
    (integrable_exp_neg_mul_sq ha).const_mul _
  calc
    |∫ s : ℝ, F (x,s)| ≤ ∫ s : ℝ, |F (x,s)| := abs_integral_le_integral_abs
    _ ≤ ∫ s : ℝ, (C*Real.exp (-a*‖x‖^2))*Real.exp (-a*s^2) := by
      apply integral_mono hfi.abs hmajor
      intro s
      convert hbound x s using 1
      dsimp only
      rw [mul_assoc, ← Real.exp_add]
      congr 2
      ring
    _ = (C*Real.sqrt (Real.pi/a))*Real.exp (-a*‖x‖^2) := by
      rw [integral_const_mul, integral_gaussian]
      ring

theorem gaussianProduct_marginal_dominated {n : ℕ} (F : E n × ℝ → ℝ) (C a : ℝ)
    (hC : 0 < C) (ha : 0 < a) (hc : Continuous F)
    (hbound : ∀ x s, |F (x,s)| ≤ C*Real.exp (-a*(‖x‖^2+s^2))) :
    GaussianDominated (fun x : E n => ∫ s : ℝ, F (x,s)) := by
  refine ⟨C*Real.sqrt (Real.pi/a), a, ?_, ha, ?_⟩
  · exact mul_pos hC (Real.sqrt_pos.2 (div_pos Real.pi_pos ha))
  · exact gaussianProduct_marginal_abs_le F C a hC ha hc hbound

#print axioms GaussianDominated.integrable
#print axioms gaussianProduct_marginal_continuous
#print axioms gaussianProduct_marginal_dominated
end CubeSections
