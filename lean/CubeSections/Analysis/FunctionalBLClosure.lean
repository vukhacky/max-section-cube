import CubeSections.Analysis.FrameGaussianEnergy
import CubeSections.Analysis.GaussianQuantile

/-! Extension of positive continuous functional BL to nonnegative continuous
densities. The positive theorem is an explicit premise here; the downstream
wrapper instantiates it with the actual Gaussian transport proof.

Gaussian regularization gives domination at ε=1 and hence L¹. The bound for
all ε>0 then tends to 1. No limit exchange for integrals is needed.
-/
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped BigOperators Topology

namespace CubeSections

def frameFunctionProduct {n k : ℕ} (U : Frame n k) (f : Fin n → ℝ → ℝ) (x : E k) : ℝ :=
  ∏ i, (f i (normalizedFrameCoordinate U i x)) ^ leverage U i

theorem frameFunctionProduct_nonneg {n k : ℕ} (U : Frame n k)
    (f : Fin n → ℝ → ℝ) (hf : ∀ i t, 0 ≤ f i t) (x : E k) :
    0 ≤ frameFunctionProduct U f x :=
  Finset.prod_nonneg (fun i _ => Real.rpow_nonneg (hf i _) _)

theorem continuous_frameFunctionProduct {n k : ℕ} (U : Frame n k)
    (f : Fin n → ℝ → ℝ) (hf : ∀ i, Continuous (f i)) :
    Continuous (frameFunctionProduct U f) := by
  unfold frameFunctionProduct
  apply continuous_finsetProd
  intro i _
  have hcoord : Continuous (normalizedFrameCoordinate U i) := by
    unfold normalizedFrameCoordinate
    fun_prop
  exact ((hf i).comp hcoord).rpow_const (fun _ => Or.inr (leverage_nonneg U i))

theorem frameFunctionProduct_mono {n k : ℕ} (U : Frame n k)
    (f g : Fin n → ℝ → ℝ) (hf : ∀ i t, 0 ≤ f i t)
    (hfg : ∀ i t, f i t ≤ g i t) (x : E k) :
    frameFunctionProduct U f x ≤ frameFunctionProduct U g x := by
  apply Finset.prod_le_prod₀
  · intro i _
    exact Real.rpow_nonneg (hf i _) _
  · intro i _
    exact Real.rpow_le_rpow (hf i _) (hfg i _) (leverage_nonneg U i)

theorem frameFunctionProduct_const_mul {n k : ℕ} (U : Frame n k)
    (f : Fin n → ℝ → ℝ) (hf : ∀ i t, 0 ≤ f i t)
    (a : ℝ) (ha : 0 ≤ a) (x : E k) :
    frameFunctionProduct U (fun i t => a*f i t) x = a^k*frameFunctionProduct U f x := by
  unfold frameFunctionProduct
  calc
    (∏ i, (a*f i (normalizedFrameCoordinate U i x)) ^ leverage U i) =
        ∏ i, a ^ leverage U i * (f i (normalizedFrameCoordinate U i x)) ^ leverage U i := by
      exact Finset.prod_congr rfl (fun i _ => Real.mul_rpow ha (hf i _))
    _ = (∏ i, a ^ leverage U i) * ∏ i, (f i (normalizedFrameCoordinate U i x)) ^ leverage U i :=
      Finset.prod_mul_distrib
    _ = _ := by
      rw [← Real.rpow_sum_of_nonneg ha (fun i _ => leverage_nonneg U i),
        sum_leverage, Real.rpow_natCast]

def gaussianRegularization (f : ℝ → ℝ) (ε t : ℝ) : ℝ :=
  (f t + ε*gaussianPDFReal 0 1 t)/(1+ε)

theorem gaussianRegularization_pos (f : ℝ → ℝ) (hf : ∀ t, 0 ≤ f t)
    (ε : ℝ) (hε : 0 < ε) (t : ℝ) : 0 < gaussianRegularization f ε t := by
  exact div_pos (add_pos_of_nonneg_of_pos (hf t)
    (mul_pos hε (gaussianPDFReal_pos 0 1 t (by norm_num)))) (by linarith)

theorem continuous_gaussianRegularization (f : ℝ → ℝ) (hf : Continuous f) (ε : ℝ) :
    Continuous (gaussianRegularization f ε) := by
  exact (hf.add (continuous_const.mul continuous_standardGaussianPDF)).div_const _

theorem integrable_gaussianRegularization (f : ℝ → ℝ) (hf : Integrable f) (ε : ℝ) :
    Integrable (gaussianRegularization f ε) :=
  (hf.add ((integrable_gaussianPDFReal 0 1).const_mul ε)).div_const _

theorem integral_gaussianRegularization (f : ℝ → ℝ) (hf : Integrable f)
    (hnorm : ∫ t, f t = 1) (ε : ℝ) (hε : 0 < ε) :
    (∫ t, gaussianRegularization f ε t) = 1 := by
  change (∫ t : ℝ, (f t + ε*gaussianPDFReal 0 1 t)/(1+ε)) = 1
  rw [integral_div, integral_add hf ((integrable_gaussianPDFReal 0 1).const_mul ε),
    integral_const_mul, hnorm, integral_gaussianPDFReal_eq_one 0 (by norm_num : (1 : NNReal) ≠ 0)]
  field_simp
  <;> linarith

theorem le_gaussianRegularization_scaled (f : ℝ → ℝ) (ε : ℝ) (hε : 0 < ε) (t : ℝ) :
    f t ≤ (1+ε)*gaussianRegularization f ε t := by
  have hden : 1+ε ≠ 0 := ne_of_gt (by linarith)
  have heq : (1+ε)*gaussianRegularization f ε t = f t+ε*gaussianPDFReal 0 1 t := by
    unfold gaussianRegularization
    field_simp
  rw [heq]
  exact le_add_of_nonneg_right (mul_nonneg hε.le (gaussianPDFReal_nonneg 0 1 t))

/-- Nonnegative continuous normalized densities inherit the positive functional
BL theorem. The conclusion includes L¹, not just a total Bochner bound. -/
theorem nonnegativeFunctionalBL_of_positive {n k : ℕ} (U : Frame n k)
    (hpositive : ∀ g : Fin n → ℝ → ℝ,
      (∀ i, Continuous (g i)) → (∀ i, Integrable (g i)) →
      (∀ i t, 0 < g i t) → (∀ i, ∫ t, g i t = 1) →
      Integrable (frameFunctionProduct U g) ∧ (∫ x, frameFunctionProduct U g x) ≤ 1)
    (f : Fin n → ℝ → ℝ) (hfcont : ∀ i, Continuous (f i))
    (hfint : ∀ i, Integrable (f i)) (hfpos : ∀ i t, 0 ≤ f i t)
    (hfnorm : ∀ i, ∫ t, f i t = 1) :
    Integrable (frameFunctionProduct U f) ∧ (∫ x, frameFunctionProduct U f x) ≤ 1 := by
  let g : ℝ → Fin n → ℝ → ℝ := fun ε i => gaussianRegularization (f i) ε
  have hg (ε : ℝ) (hε : 0 < ε) :
      Integrable (frameFunctionProduct U (g ε)) ∧
        (∫ x, frameFunctionProduct U (g ε) x) ≤ 1 :=
    hpositive (g ε) (fun i => continuous_gaussianRegularization _ (hfcont i) ε)
      (fun i => integrable_gaussianRegularization _ (hfint i) ε)
      (fun i => gaussianRegularization_pos _ (hfpos i) ε hε)
      (fun i => integral_gaussianRegularization _ (hfint i) (hfnorm i) ε hε)
  have hdom (ε : ℝ) (hε : 0 < ε) (x : E k) :
      frameFunctionProduct U f x ≤ (1+ε)^k*frameFunctionProduct U (g ε) x := by
    calc
      frameFunctionProduct U f x ≤ frameFunctionProduct U (fun i t => (1+ε)*g ε i t) x :=
        frameFunctionProduct_mono U _ _ hfpos (fun i => le_gaussianRegularization_scaled _ ε hε) x
      _ = _ := frameFunctionProduct_const_mul U _
        (fun i t => (gaussianRegularization_pos _ (hfpos i) ε hε t).le) _ (by linarith) x
  have hfI : Integrable (frameFunctionProduct U f) :=
    ((hg 1 (by norm_num)).1.const_mul ((1+(1 : ℝ))^k)).mono_nonneg
      (continuous_frameFunctionProduct U f hfcont).aestronglyMeasurable
      (ae_of_all _ (frameFunctionProduct_nonneg U f hfpos))
      (ae_of_all _ (hdom 1 (by norm_num)))
  refine ⟨hfI, ?_⟩
  have hb (ε : ℝ) (hε : 0 < ε) : (∫ x, frameFunctionProduct U f x) ≤ (1+ε)^k := by
    calc
      (∫ x, frameFunctionProduct U f x) ≤
          ∫ x, (1+ε)^k*frameFunctionProduct U (g ε) x :=
        integral_mono hfI ((hg ε hε).1.const_mul _) (hdom ε hε)
      _ = (1+ε)^k*(∫ x, frameFunctionProduct U (g ε) x) := integral_const_mul _ _
      _ ≤ (1+ε)^k*1 := mul_le_mul_of_nonneg_left (hg ε hε).2 (by positivity)
      _ = (1+ε)^k := mul_one _
  have hlim : Tendsto (fun ε : ℝ => (1+ε)^k) (𝓝[>] (0 : ℝ)) (𝓝 (1 : ℝ)) := by
    have hcont : Continuous (fun ε : ℝ => (1+ε)^k) := by fun_prop
    simpa using (hcont.continuousAt (x := (0 : ℝ))).tendsto.mono_left
      (nhdsWithin_le_nhds : 𝓝[>] (0 : ℝ) ≤ 𝓝 (0 : ℝ))
  apply le_of_tendsto_of_tendsto tendsto_const_nhds hlim
  filter_upwards [self_mem_nhdsWithin] with ε hε
  exact hb ε hε

#print axioms nonnegativeFunctionalBL_of_positive
end CubeSections
