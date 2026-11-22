import CubeSections.Analysis.ConditionalDensityTransport

/-! The jointly measurable conditional inverse has the actual joint density as
its pushforward. This is an equality of measures, not a family of unassembled
one-dimensional distributional statements. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
open Set MeasureTheory ProbabilityTheory
open scoped ENNReal
namespace CubeSections

def triangularConditionalInverse {n : ℕ} (f : E (n+1) → ℝ)
    (hc : Continuous f) (hG : GaussianDominated f) (hp : ∀ x, 0 < f x)
    (p : E n × ℝ) : E n × ℝ :=
  (p.1, euclideanConditionalInverse f hc hG hp p.1 p.2)

theorem measurable_triangularConditionalInverse {n : ℕ} (f : E (n+1) → ℝ)
    (hc : Continuous f) (hG : GaussianDominated f) (hp : ∀ x, 0 < f x) :
    Measurable (triangularConditionalInverse f hc hG hp) :=
  measurable_fst.prodMk (measurable_euclideanConditionalInverse f hc hG hp)

theorem triangularConditionalInverse_map_law {n : ℕ} (f : E (n+1) → ℝ)
    (hc : Continuous f) (hG : GaussianDominated f) (hp : ∀ x, 0 < f x) :
    (((volume : Measure (E n)).withDensity (fun x => ENNReal.ofReal (euclideanMarginal f x))).prod
      (gaussianReal 0 1)).map (triangularConditionalInverse f hc hG hp) =
      ((volume : Measure (E n)).prod volume).withDensity
        (fun p => ENNReal.ofReal (f (euclideanSuccJoin n p))) := by
  apply Measure.ext_of_lintegral
  intro H hH
  have hT := measurable_triangularConditionalInverse f hc hG hp
  have hM := (continuous_euclideanMarginal f hc hG).measurable.ennreal_ofReal
  have hF : Measurable (fun p : E n × ℝ => ENNReal.ofReal (f (euclideanSuccJoin n p))) :=
    (hc.comp (continuous_euclideanSuccJoin n)).measurable.ennreal_ofReal
  rw [lintegral_map hH hT]
  have hHT : Measurable (fun p : E n × ℝ => H (triangularConditionalInverse f hc hG hp p)) :=
    hH.comp hT
  rw [lintegral_prod (fun p : E n × ℝ => H (triangularConditionalInverse f hc hG hp p))
    hHT.aemeasurable]
  have hfiber : ∀ x : E n,
      (∫⁻ z, H (triangularConditionalInverse f hc hG hp (x,z)) ∂gaussianReal 0 1) =
      ∫⁻ s, ENNReal.ofReal (euclideanConditionalDensity f x s) * H (x,s) := by
    intro x
    have hS : Measurable (euclideanConditionalInverse f hc hG hp x) :=
      measurable_positiveDensityInverse (continuous_euclideanConditionalSlice f hc x)
        (integrable_euclideanConditionalSlice f hc hG x)
        (euclideanConditionalDensity_pos f hc hG hp x)
        (integral_euclideanConditionalDensity f hc hG hp x)
    have hHx : Measurable (fun s : ℝ => H (x,s)) := hH.comp measurable_prodMk_left
    change (∫⁻ z, H (x,euclideanConditionalInverse f hc hG hp x z) ∂gaussianReal 0 1) = _
    rw [← lintegral_map hHx hS, euclideanConditionalInverse_map_law,
      positiveDensityLaw, lintegral_withDensity_eq_lintegral_mul _
        (continuous_euclideanConditionalSlice f hc x).measurable.ennreal_ofReal hHx]
    rfl
  simp_rw [hfiber]
  rw [lintegral_withDensity_eq_lintegral_mul _ hM]
  · rw [lintegral_withDensity_eq_lintegral_mul _ hF hH]
    rw [lintegral_prod ((fun p : E n × ℝ => ENNReal.ofReal (f (euclideanSuccJoin n p))) * H)
      (hF.mul hH).aemeasurable]
    apply lintegral_congr
    intro x
    simp only [Pi.mul_apply]
    have hprod : Measurable (fun s : ℝ => ENNReal.ofReal (euclideanConditionalDensity f x s) * H (x,s)) :=
      (continuous_euclideanConditionalSlice f hc x).measurable.ennreal_ofReal.mul
        (hH.comp (measurable_const.prodMk measurable_id))
    rw [← lintegral_const_mul _ hprod]
    apply lintegral_congr
    intro s
    change ENNReal.ofReal (euclideanMarginal f x) *
      (ENNReal.ofReal (euclideanConditionalDensity f x s) * H (x,s)) = _
    rw [← mul_assoc, ← ENNReal.ofReal_mul (euclideanMarginal_pos f hc hG hp x).le]
    congr 2
    unfold euclideanConditionalDensity
    field_simp [ne_of_gt (euclideanMarginal_pos f hc hG hp x)]
  · exact Measurable.lintegral_prod_right
      (((continuous_euclideanConditionalDensity f hc hG hp).measurable.ennreal_ofReal).mul hH)

#print axioms triangularConditionalInverse_map_law
end CubeSections
