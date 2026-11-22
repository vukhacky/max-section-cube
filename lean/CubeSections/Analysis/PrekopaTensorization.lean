import CubeSections.Analysis.EuclideanSplit
import CubeSections.Analysis.GaussianDominated
import CubeSections.Analysis.PrekopaOne

/-! Dimension induction for positive Gaussian-dominated Prekopa--Leindler.
Actual Euclidean coordinates are split with product Lebesgue measure. Gaussian
domination gives finite, continuous, strictly positive dominated marginals,
so the one-dimensional theorem can be iterated without a regularity gap. -/
noncomputable section
open Set MeasureTheory
namespace CubeSections

def euclideanMarginal {n : ℕ} (f : E (n+1) → ℝ) (x : E n) : ℝ :=
  ∫ s : ℝ, f (euclideanSuccJoin n (x,s))

theorem continuous_euclideanSlice {n : ℕ} (f : E (n+1) → ℝ)
    (hc : Continuous f) (x : E n) :
    Continuous (fun s : ℝ => f (euclideanSuccJoin n (x,s))) :=
  hc.comp ((continuous_euclideanSuccJoin n).comp (continuous_const.prodMk continuous_id))

theorem integrable_euclideanSlice {n : ℕ} (f : E (n+1) → ℝ)
    (hc : Continuous f) (hG : GaussianDominated f) (x : E n) :
    Integrable (fun s : ℝ => f (euclideanSuccJoin n (x,s))) := by
  obtain ⟨C,a,hC,ha,hbound⟩ := hG
  apply gaussianProduct_fiber_integrable (fun p : E n × ℝ => f (euclideanSuccJoin n p))
    C a hC ha (hc.comp (continuous_euclideanSuccJoin n)) _ x
  intro y s
  simpa only [euclideanSuccJoin_norm_sq] using hbound (euclideanSuccJoin n (y,s))

theorem continuous_euclideanMarginal {n : ℕ} (f : E (n+1) → ℝ)
    (hc : Continuous f) (hG : GaussianDominated f) : Continuous (euclideanMarginal f) := by
  obtain ⟨C,a,hC,ha,hbound⟩ := hG
  apply gaussianProduct_marginal_continuous (fun p : E n × ℝ => f (euclideanSuccJoin n p))
    C a hC ha (hc.comp (continuous_euclideanSuccJoin n))
  intro y s
  simpa only [euclideanSuccJoin_norm_sq] using hbound (euclideanSuccJoin n (y,s))

theorem gaussianDominated_euclideanMarginal {n : ℕ} (f : E (n+1) → ℝ)
    (hc : Continuous f) (hG : GaussianDominated f) : GaussianDominated (euclideanMarginal f) := by
  obtain ⟨C,a,hC,ha,hbound⟩ := hG
  apply gaussianProduct_marginal_dominated (fun p : E n × ℝ => f (euclideanSuccJoin n p))
    C a hC ha (hc.comp (continuous_euclideanSuccJoin n))
  intro y s
  simpa only [euclideanSuccJoin_norm_sq] using hbound (euclideanSuccJoin n (y,s))

theorem euclideanMarginal_pos {n : ℕ} (f : E (n+1) → ℝ)
    (hc : Continuous f) (hG : GaussianDominated f) (hp : ∀ x, 0 < f x) (x : E n) :
    0 < euclideanMarginal f x :=
  integral_pos_of_integrable_nonneg_ne_zero (continuous_euclideanSlice f hc x)
    (integrable_euclideanSlice f hc hG x) (fun s => (hp _).le)
    (ne_of_gt (hp (euclideanSuccJoin n (x,0))))

theorem integral_euclideanMarginal {n : ℕ} (f : E (n+1) → ℝ)
    (hc : Continuous f) (hG : GaussianDominated f) :
    (∫ x : E n, euclideanMarginal f x) = ∫ z : E (n+1), f z :=
  integral_euclideanSuccJoin f (hG.integrable hc)

theorem euclideanMarginal_prekopa {n : ℕ} (f g h : E (n+1) → ℝ)
    (t : ℝ) (ht₀ : 0 < t) (ht₁ : t < 1)
    (hfc : Continuous f) (hgc : Continuous g) (hhc : Continuous h)
    (hfp : ∀ x, 0 < f x) (hgp : ∀ x, 0 < g x) (hhp : ∀ x, 0 < h x)
    (hfG : GaussianDominated f) (hgG : GaussianDominated g) (hhG : GaussianDominated h)
    (hbound : ∀ x y, (f x)^(1-t) * (g y)^t ≤ h ((1-t) • x + t • y))
    (x y : E n) :
    (euclideanMarginal f x)^(1-t) * (euclideanMarginal g y)^t ≤
      euclideanMarginal h ((1-t) • x+t • y) := by
  apply prekopaLeindler_one_positive
    (fun s : ℝ => f (euclideanSuccJoin n (x,s)))
    (fun r : ℝ => g (euclideanSuccJoin n (y,r)))
    (fun u : ℝ => h (euclideanSuccJoin n ((1-t) • x+t • y,u)))
    t ht₀ ht₁
    (continuous_euclideanSlice f hfc x) (integrable_euclideanSlice f hfc hfG x)
    (fun s => hfp _) (continuous_euclideanSlice g hgc y) (integrable_euclideanSlice g hgc hgG y)
    (fun r => hgp _) (integrable_euclideanSlice h hhc hhG _) (fun u => (hhp _).le)
  intro s r
  have hjoin : euclideanSuccJoin n ((1-t) • x+t • y,(1-t)*s+t*r) =
      (1-t) • euclideanSuccJoin n (x,s)+t • euclideanSuccJoin n (y,r) := by
    change euclideanSuccJoin n ((1-t) • (x,s)+t • (y,r)) = _
    rw [map_add, map_smul, map_smul]
  rw [hjoin]
  exact hbound _ _

theorem positiveGaussianPrekopa_zero : PositiveGaussianPrekopa 0 := by
  intro t ht₀ ht₁ f g h hfc hgc hhc hfp hgp hhp hfG hgG hhG hbound
  simp only [volume_euclideanSpace_eq_dirac (Fin 0), integral_dirac]
  simpa only [smul_zero, zero_add] using hbound 0 0

theorem positiveGaussianPrekopa_succ (n : ℕ)
    (hPL : PositiveGaussianPrekopa n) : PositiveGaussianPrekopa (n+1) := by
  intro t ht₀ ht₁ f g h hfc hgc hhc hfp hgp hhp hfG hgG hhG hbound
  have hM := hPL t ht₀ ht₁ (euclideanMarginal f) (euclideanMarginal g) (euclideanMarginal h)
    (continuous_euclideanMarginal f hfc hfG) (continuous_euclideanMarginal g hgc hgG)
    (continuous_euclideanMarginal h hhc hhG)
    (euclideanMarginal_pos f hfc hfG hfp) (euclideanMarginal_pos g hgc hgG hgp)
    (euclideanMarginal_pos h hhc hhG hhp)
    (gaussianDominated_euclideanMarginal f hfc hfG) (gaussianDominated_euclideanMarginal g hgc hgG)
    (gaussianDominated_euclideanMarginal h hhc hhG)
    (euclideanMarginal_prekopa f g h t ht₀ ht₁ hfc hgc hhc hfp hgp hhp hfG hgG hhG hbound)
  rwa [integral_euclideanMarginal f hfc hfG, integral_euclideanMarginal g hgc hgG,
    integral_euclideanMarginal h hhc hhG] at hM

/-- Positive Gaussian-dominated Prekopa--Leindler in every finite dimension. -/
theorem positiveGaussianPrekopa (n : ℕ) : PositiveGaussianPrekopa n := by
  induction n with
  | zero => exact positiveGaussianPrekopa_zero
  | succ n ih => exact positiveGaussianPrekopa_succ n ih

#print axioms euclideanMarginal_prekopa
#print axioms positiveGaussianPrekopa
end CubeSections
