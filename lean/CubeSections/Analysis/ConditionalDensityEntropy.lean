import CubeSections.Analysis.ConditionalDensityLaw
import CubeSections.Analysis.EuclideanGaussianSplit

/-! Exact entropy chain rule for the actual Euclidean conditional densities.
The two ordinary entropy integrability premises remain visible; no conditional
entropy identity or disintegration is assumed. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
open MeasureTheory ProbabilityTheory
open scoped ENNReal
namespace CubeSections

theorem euclideanConditionalDensity_gaussian_bound {n : ℕ} (f : E (n+1) → ℝ)
    (hc : Continuous f) (hG : GaussianDominated f) (hp : ∀ x, 0 < f x) (x : E n) :
    ∃ C a : ℝ, 0 < C ∧ 0 < a ∧
      ∀ s : ℝ, |euclideanConditionalDensity f x s| ≤ C * Real.exp (-a*s^2) := by
  obtain ⟨C,a,hC,ha,hb⟩ := hG
  have hM : 0 < euclideanMarginal f x := euclideanMarginal_pos f hc ⟨C,a,hC,ha,hb⟩ hp x
  refine ⟨C/euclideanMarginal f x,a,div_pos hC hM,ha,fun s => ?_⟩
  have hE : Real.exp (-a*‖euclideanSuccJoin n (x,s)‖^2) ≤ Real.exp (-a*s^2) := by
    apply Real.exp_le_exp.mpr
    rw [euclideanSuccJoin_norm_sq]
    nlinarith [mul_nonneg ha.le (sq_nonneg ‖x‖)]
  have h := (hb (euclideanSuccJoin n (x,s))).trans
    (mul_le_mul_of_nonneg_left hE hC.le)
  unfold euclideanConditionalDensity
  rw [abs_div, abs_of_pos hM]
  convert div_le_div_of_nonneg_right h hM.le using 1 <;> ring

theorem euclideanJointDensity_fst {n : ℕ} (f : E (n+1) → ℝ)
    (hc : Continuous f) (hG : GaussianDominated f) (hp : ∀ x, 0 < f x) :
    (((volume : Measure (E n)).prod volume).withDensity
      (fun p => ENNReal.ofReal (f (euclideanSuccJoin n p)))).map Prod.fst =
      euclideanDensityLaw (euclideanMarginal f) := by
  rw [← triangularConditionalInverse_map_law f hc hG hp,
    Measure.map_map measurable_fst (measurable_triangularConditionalInverse f hc hG hp)]
  change (((volume : Measure (E n)).withDensity
      (fun x => ENNReal.ofReal (euclideanMarginal f x))).prod
      (gaussianReal 0 1)).map Prod.fst = _
  simp only [Measure.map_fst_prod, measure_univ, one_smul, euclideanDensityLaw]

private theorem integrable_real_density_iff {α : Type*} [MeasurableSpace α]
    (μ : Measure α) (q : α → ℝ) (hq : Measurable q) (hp : ∀ x, 0 ≤ q x) (g : α → ℝ) :
    Integrable g (μ.withDensity (fun x => ENNReal.ofReal (q x))) ↔
      Integrable (fun x => q x * g x) μ := by
  simpa only [ENNReal.toReal_ofReal (hp _), smul_eq_mul] using
    (integrable_withDensity_iff_integrable_smul' (g := g) hq.ennreal_ofReal
      (ae_of_all μ (fun x => ENNReal.ofReal_lt_top)))

theorem integrable_joint_marginalEntropy {n : ℕ} (f : E (n+1) → ℝ)
    (hc : Continuous f) (hG : GaussianDominated f) (hp : ∀ x, 0 < f x)
    (hM : Integrable (fun x : E n => euclideanMarginal f x *
      Real.log (euclideanMarginal f x / euclideanGaussianDensity n x))) :
    Integrable (fun p : E n × ℝ => f (euclideanSuccJoin n p) *
      Real.log (euclideanMarginal f p.1 / euclideanGaussianDensity n p.1))
      ((volume : Measure (E n)).prod volume) := by
  have hMlaw : Integrable (fun x : E n =>
      Real.log (euclideanMarginal f x / euclideanGaussianDensity n x))
      (euclideanDensityLaw (euclideanMarginal f)) :=
    (integrable_real_density_iff volume _ (continuous_euclideanMarginal f hc hG).measurable
      (fun x => (euclideanMarginal_pos f hc hG hp x).le) _).mpr hM
  rw [← euclideanJointDensity_fst f hc hG hp] at hMlaw
  have hcomp := hMlaw.comp_measurable measurable_fst
  exact (integrable_real_density_iff ((volume : Measure (E n)).prod volume)
    (fun p => f (euclideanSuccJoin n p))
    (hc.comp (continuous_euclideanSuccJoin n)).measurable
    (fun p => (hp _).le) _).mp hcomp

theorem euclideanConditionalDensity_log_split {n : ℕ} (f : E (n+1) → ℝ)
    (hc : Continuous f) (hG : GaussianDominated f) (hp : ∀ x, 0 < f x)
    (x : E n) (s : ℝ) :
    Real.log (f (euclideanSuccJoin n (x,s)) /
      euclideanGaussianDensity (n+1) (euclideanSuccJoin n (x,s))) =
    Real.log (euclideanMarginal f x / euclideanGaussianDensity n x) +
      Real.log (euclideanConditionalDensity f x s / gaussianPDFReal 0 1 s) := by
  have hF := ne_of_gt (hp (euclideanSuccJoin n (x,s)))
  have hM := ne_of_gt (euclideanMarginal_pos f hc hG hp x)
  have hGx := ne_of_gt (euclideanGaussianDensity_pos n x)
  have hφ := ne_of_gt (gaussianPDFReal_pos 0 1 s (by norm_num))
  rw [euclideanGaussianDensity_succ_join, euclideanConditionalDensity,
    Real.log_div hF (mul_ne_zero hGx hφ), Real.log_mul hGx hφ,
    Real.log_div hM hGx, Real.log_div (div_ne_zero hF hM) hφ, Real.log_div hF hM]
  ring

theorem euclideanConditionalDensity_entropy_chain {n : ℕ} (f : E (n+1) → ℝ)
    (hc : Continuous f) (hG : GaussianDominated f) (hp : ∀ x, 0 < f x)
    (hF : Integrable (fun x : E (n+1) => f x * Real.log (f x / euclideanGaussianDensity (n+1) x)))
    (hM : Integrable (fun x : E n => euclideanMarginal f x *
      Real.log (euclideanMarginal f x / euclideanGaussianDensity n x))) :
    (∫ x : E (n+1), f x * Real.log (f x / euclideanGaussianDensity (n+1) x)) =
      (∫ x : E n, euclideanMarginal f x * Real.log (euclideanMarginal f x / euclideanGaussianDensity n x)) +
      ∫ x : E n, euclideanMarginal f x *
        ∫ s : ℝ, euclideanConditionalDensity f x s *
          Real.log (euclideanConditionalDensity f x s / gaussianPDFReal 0 1 s) := by
  have hF' := euclideanSuccJoin_integrable
    (fun x : E (n+1) => f x * Real.log (f x / euclideanGaussianDensity (n+1) x)) hF
  have hM' := integrable_joint_marginalEntropy f hc hG hp hM
  have hC : Integrable (fun p : E n × ℝ => f (euclideanSuccJoin n p) *
      Real.log (euclideanConditionalDensity f p.1 p.2 / gaussianPDFReal 0 1 p.2))
      ((volume : Measure (E n)).prod volume) := by
    apply (hF'.sub hM').congr
    filter_upwards with p
    simp only [Pi.sub_apply]
    rw [euclideanConditionalDensity_log_split f hc hG hp p.1 p.2]
    ring
  have hsum : (fun p : E n × ℝ => f (euclideanSuccJoin n p) *
      Real.log (f (euclideanSuccJoin n p) / euclideanGaussianDensity (n+1) (euclideanSuccJoin n p))) =
      (fun p => f (euclideanSuccJoin n p) * Real.log (euclideanMarginal f p.1 / euclideanGaussianDensity n p.1)) +
      (fun p => f (euclideanSuccJoin n p) *
        Real.log (euclideanConditionalDensity f p.1 p.2 / gaussianPDFReal 0 1 p.2)) := by
    funext p
    rw [euclideanConditionalDensity_log_split f hc hG hp p.1 p.2]
    simp only [Pi.add_apply, mul_add]
  rw [← integral_euclideanSuccJoin _ hF, ← integral_prod _ hF', hsum]
  change (∫ p : E n × ℝ, f (euclideanSuccJoin n p) *
      Real.log (euclideanMarginal f p.1 / euclideanGaussianDensity n p.1) +
      f (euclideanSuccJoin n p) *
      Real.log (euclideanConditionalDensity f p.1 p.2 / gaussianPDFReal 0 1 p.2)
      ∂((volume : Measure (E n)).prod volume)) = _
  rw [integral_add hM' hC, integral_prod _ hM', integral_prod _ hC]
  congr 1
  · apply integral_congr_ae
    filter_upwards with x
    rw [integral_mul_const]
    rfl
  · apply integral_congr_ae
    filter_upwards with x
    rw [← integral_const_mul]
    apply integral_congr_ae
    filter_upwards with s
    unfold euclideanConditionalDensity
    field_simp [ne_of_gt (euclideanMarginal_pos f hc hG hp x)]

#print axioms euclideanJointDensity_fst
#print axioms euclideanConditionalDensity_entropy_chain
end CubeSections
