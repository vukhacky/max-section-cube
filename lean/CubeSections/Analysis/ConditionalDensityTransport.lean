import CubeSections.Analysis.PrekopaTensorization
import CubeSections.Analysis.PositiveDensityInverse

/-! Actual jointly measurable conditional inverse transports for positive
Gaussian-dominated densities. The family measurability is proved from CDF
sublevel sets, rather than assumed from separate measurability. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory
open scoped ENNReal
namespace CubeSections

theorem measurable_positiveDensityInverse_family {α : Type*} [MeasurableSpace α]
    (f : α → ℝ → ℝ) (hf : Measurable (Function.uncurry f))
    (hc : ∀ a, Continuous (f a)) (hi : ∀ a, Integrable (f a))
    (hp : ∀ a x, 0 < f a x) (hm : ∀ a, (∫ x, f a x) = 1) :
    Measurable (fun p : α × ℝ =>
      positiveDensityInverse (f p.1) (hc p.1) (hi p.1) (hp p.1) (hm p.1) p.2) := by
  apply measurable_of_Iio
  intro r
  have hCDF : Measurable (fun a => densityCDF (f a) r) :=
    (hf.stronglyMeasurable.integral_prod_right (ν := volume.restrict (Iic r))).measurable
  have hset : (fun p : α × ℝ =>
      positiveDensityInverse (f p.1) (hc p.1) (hi p.1) (hp p.1) (hm p.1) p.2) ⁻¹' Iio r =
      {p | standardGaussianCDF p.2 < densityCDF (f p.1) r} := by
    ext p
    change positiveDensityInverse (f p.1) (hc p.1) (hi p.1) (hp p.1) (hm p.1) p.2 < r ↔
      standardGaussianCDF p.2 < densityCDF (f p.1) r
    rw [← (strictMono_densityCDF (hc p.1) (hi p.1) (hp p.1)).lt_iff_lt,
      densityCDF_positiveDensityInverse]
  rw [hset]
  exact measurableSet_lt ((continuous_standardGaussianCDF.measurable).comp measurable_snd)
    (hCDF.comp measurable_fst)

def euclideanConditionalDensity {n : ℕ} (f : E (n+1) → ℝ) (x : E n) (s : ℝ) : ℝ :=
  f (euclideanSuccJoin n (x,s)) / euclideanMarginal f x

theorem continuous_euclideanConditionalDensity {n : ℕ} (f : E (n+1) → ℝ)
    (hc : Continuous f) (hG : GaussianDominated f) (hp : ∀ x, 0 < f x) :
    Continuous (Function.uncurry (euclideanConditionalDensity f)) := by
  exact (hc.comp (continuous_euclideanSuccJoin n)).div
    ((continuous_euclideanMarginal f hc hG).comp continuous_fst)
    (fun p => ne_of_gt (euclideanMarginal_pos f hc hG hp p.1))

theorem continuous_euclideanConditionalSlice {n : ℕ} (f : E (n+1) → ℝ)
    (hc : Continuous f) (x : E n) : Continuous (euclideanConditionalDensity f x) :=
  (continuous_euclideanSlice f hc x).div_const _

theorem integrable_euclideanConditionalSlice {n : ℕ} (f : E (n+1) → ℝ)
    (hc : Continuous f) (hG : GaussianDominated f) (x : E n) :
    Integrable (euclideanConditionalDensity f x) :=
  (integrable_euclideanSlice f hc hG x).div_const _

theorem euclideanConditionalDensity_pos {n : ℕ} (f : E (n+1) → ℝ)
    (hc : Continuous f) (hG : GaussianDominated f) (hp : ∀ x, 0 < f x) (x : E n) (s : ℝ) :
    0 < euclideanConditionalDensity f x s :=
  div_pos (hp _) (euclideanMarginal_pos f hc hG hp x)

theorem integral_euclideanConditionalDensity {n : ℕ} (f : E (n+1) → ℝ)
    (hc : Continuous f) (hG : GaussianDominated f) (hp : ∀ x, 0 < f x) (x : E n) :
    (∫ s, euclideanConditionalDensity f x s) = 1 := by
  simp only [euclideanConditionalDensity, div_eq_mul_inv, integral_mul_const]
  rw [← div_eq_mul_inv]
  exact div_self (ne_of_gt (euclideanMarginal_pos f hc hG hp x))

def euclideanConditionalInverse {n : ℕ} (f : E (n+1) → ℝ)
    (hc : Continuous f) (hG : GaussianDominated f) (hp : ∀ x, 0 < f x)
    (x : E n) (z : ℝ) : ℝ :=
  positiveDensityInverse (euclideanConditionalDensity f x)
    (continuous_euclideanConditionalSlice f hc x)
    (integrable_euclideanConditionalSlice f hc hG x)
    (euclideanConditionalDensity_pos f hc hG hp x)
    (integral_euclideanConditionalDensity f hc hG hp x) z

theorem measurable_euclideanConditionalInverse {n : ℕ} (f : E (n+1) → ℝ)
    (hc : Continuous f) (hG : GaussianDominated f) (hp : ∀ x, 0 < f x) :
    Measurable (Function.uncurry (euclideanConditionalInverse f hc hG hp)) :=
  measurable_positiveDensityInverse_family (euclideanConditionalDensity f)
    (continuous_euclideanConditionalDensity f hc hG hp).measurable
    (continuous_euclideanConditionalSlice f hc)
    (integrable_euclideanConditionalSlice f hc hG)
    (euclideanConditionalDensity_pos f hc hG hp)
    (integral_euclideanConditionalDensity f hc hG hp)

theorem euclideanConditionalInverse_map_law {n : ℕ} (f : E (n+1) → ℝ)
    (hc : Continuous f) (hG : GaussianDominated f) (hp : ∀ x, 0 < f x) (x : E n) :
    (gaussianReal 0 1).map (euclideanConditionalInverse f hc hG hp x) =
      positiveDensityLaw (euclideanConditionalDensity f x) :=
  positiveDensityInverse_map_law
    (continuous_euclideanConditionalSlice f hc x)
    (integrable_euclideanConditionalSlice f hc hG x)
    (euclideanConditionalDensity_pos f hc hG hp x)
    (integral_euclideanConditionalDensity f hc hG hp x)

#print axioms measurable_positiveDensityInverse_family
#print axioms measurable_euclideanConditionalInverse
#print axioms euclideanConditionalInverse_map_law
end CubeSections
