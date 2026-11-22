import CubeSections.Analysis.GaussianDominated
import Mathlib.Topology.MetricSpace.HausdorffDistance
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity

/-! Positive Gaussian approximations of compact sets.  The parameter is the
inverse variance: `compactGaussianApprox A s x = exp (-s * dist(x,A)^2)`.
No convexity is needed for the approximation or the multiplicative volume
inequality; convexity is retained in the public BM contract. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
open MeasureTheory Set Filter
open scoped Topology
namespace CubeSections

def compactGaussianApprox {n : ℕ} (A : Set (E n)) (s : ℝ) (x : E n) : ℝ :=
  Real.exp (-s * (Metric.infDist x A)^2)

theorem compactGaussianApprox_pos {n : ℕ} (A : Set (E n)) (s : ℝ) (x : E n) :
    0 < compactGaussianApprox A s x := Real.exp_pos _

theorem continuous_compactGaussianApprox {n : ℕ} (A : Set (E n)) (s : ℝ) :
    Continuous (compactGaussianApprox A s) := by
  unfold compactGaussianApprox
  fun_prop

theorem compactGaussianApprox_gaussianDominated {n : ℕ} {A : Set (E n)}
    (hA : IsCompact A) (hAn : A.Nonempty) (s : ℝ) (hs : 0 < s) :
    GaussianDominated (compactGaussianApprox A s) := by
  obtain ⟨a, ha⟩ := hAn
  let R : ℝ := Metric.diam A + ‖a‖
  have hR : 0 ≤ R := add_nonneg Metric.diam_nonneg (norm_nonneg _)
  refine ⟨Real.exp (s*R^2), s/2, Real.exp_pos _, by positivity, ?_⟩
  intro x
  have hd : 0 ≤ Metric.infDist x A := Metric.infDist_nonneg
  have hnx : ‖x‖ ≤ Metric.infDist x A + R := by
    have htriangle : ‖x‖ ≤ dist x a + ‖a‖ := by
      simpa only [dist_eq_norm, sub_add_cancel] using norm_add_le (x-a) a
    have hdist := Metric.dist_le_infDist_add_diam hA.isBounded ha (x := x)
    dsimp only [R]
    linarith
  have hsq : ‖x‖^2 ≤ 2*(Metric.infDist x A)^2 + 2*R^2 := by
    have hpow := pow_le_pow_left₀ (norm_nonneg x) hnx 2
    nlinarith [sq_nonneg (Metric.infDist x A - R)]
  unfold compactGaussianApprox
  rw [abs_of_pos (Real.exp_pos _), ← Real.exp_add]
  apply Real.exp_le_exp.mpr
  nlinarith [mul_le_mul_of_nonneg_left hsq hs.le]

theorem compactGaussianApprox_integrable {n : ℕ} {A : Set (E n)}
    (hA : IsCompact A) (hAn : A.Nonempty) (s : ℝ) (hs : 0 < s) :
    Integrable (compactGaussianApprox A s) :=
  (compactGaussianApprox_gaussianDominated hA hAn s hs).integrable
    (continuous_compactGaussianApprox A s)

theorem infDist_weightedMinkowski_sq {n : ℕ} {A B : Set (E n)}
    (hA : IsCompact A) (hB : IsCompact B) (hAn : A.Nonempty) (hBn : B.Nonempty)
    {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) (x y : E n) :
    (Metric.infDist ((1-t) • x + t • y) (weightedMinkowski t A B))^2 ≤
      (1-t)*(Metric.infDist x A)^2 + t*(Metric.infDist y B)^2 := by
  obtain ⟨a, ha, hda⟩ := hA.exists_infDist_eq_dist hAn x
  obtain ⟨b, hb, hdb⟩ := hB.exists_infDist_eq_dist hBn y
  have hmem : (1-t) • a + t • b ∈ weightedMinkowski t A B :=
    ⟨(a,b), ⟨ha,hb⟩, rfl⟩
  have hd := Metric.infDist_le_dist_of_mem hmem
    (x := (1-t) • x + t • y)
  have hnorm : dist ((1-t) • x + t • y) ((1-t) • a + t • b) ≤
      (1-t)*dist x a + t*dist y b := by
    rw [dist_eq_norm, show (1-t) • x + t • y - ((1-t) • a + t • b) =
      (1-t) • (x-a) + t • (y-b) by module]
    calc
      _ ≤ ‖(1-t) • (x-a)‖ + ‖t • (y-b)‖ := norm_add_le _ _
      _ = (1-t)*dist x a + t*dist y b := by
        rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs,
          abs_of_nonneg (sub_nonneg.mpr ht1), abs_of_nonneg ht0,
          dist_eq_norm, dist_eq_norm]
  have hnonneg : 0 ≤ Metric.infDist ((1-t) • x + t • y)
      (weightedMinkowski t A B) := Metric.infDist_nonneg
  have hpow := pow_le_pow_left₀ hnonneg (hd.trans hnorm) 2
  rw [← hda, ← hdb] at hpow
  have hvariance := mul_nonneg (mul_nonneg (sub_nonneg.mpr ht1) ht0)
    (sq_nonneg (Metric.infDist x A - Metric.infDist y B))
  nlinarith

theorem compactGaussianApprox_prekopa {n : ℕ} {A B : Set (E n)}
    (hA : IsCompact A) (hB : IsCompact B) (hAn : A.Nonempty) (hBn : B.Nonempty)
    {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) (s : ℝ) (hs : 0 ≤ s) (x y : E n) :
    (compactGaussianApprox A s x)^(1-t) * (compactGaussianApprox B s y)^t ≤
      compactGaussianApprox (weightedMinkowski t A B) s ((1-t) • x + t • y) := by
  have hdist := infDist_weightedMinkowski_sq hA hB hAn hBn ht0 ht1 x y
  unfold compactGaussianApprox
  rw [← Real.exp_mul, ← Real.exp_mul, ← Real.exp_add]
  apply Real.exp_le_exp.mpr
  nlinarith [mul_le_mul_of_nonneg_left hdist hs]

theorem compactGaussianApprox_tendsto {n : ℕ} {A : Set (E n)}
    (hA : IsClosed A) (hAn : A.Nonempty) (x : E n) :
    Tendsto (fun m : ℕ => compactGaussianApprox A ((m:ℝ)+1) x) atTop
      (𝓝 (A.indicator (fun _ => (1:ℝ)) x)) := by
  by_cases hx : x ∈ A
  · simp only [compactGaussianApprox, Metric.infDist_zero_of_mem hx, zero_pow (by decide : 2≠0),
      mul_zero, Real.exp_zero, indicator_of_mem hx]
    exact tendsto_const_nhds
  · rw [indicator_of_notMem hx]
    have hd : 0 < Metric.infDist x A := (hA.notMem_iff_infDist_pos hAn).mp hx
    have hm : Tendsto (fun m : ℕ => (m:ℝ)+1) atTop atTop :=
      tendsto_atTop_add_const_right _ _ tendsto_natCast_atTop_atTop
    have hprod := hm.atTop_mul_const (sq_pos_of_pos hd)
    convert Real.tendsto_exp_neg_atTop_nhds_zero.comp hprod using 1
    funext m
    simp only [compactGaussianApprox, Function.comp_apply, neg_mul]

theorem integral_compactGaussianApprox_tendsto {n : ℕ} {A : Set (E n)}
    (hA : IsCompact A) (hAn : A.Nonempty) :
    Tendsto (fun m : ℕ => ∫ x, compactGaussianApprox A ((m:ℝ)+1) x) atTop
      (𝓝 ((volume A).toReal)) := by
  have hdct := tendsto_integral_of_dominated_convergence
    (compactGaussianApprox A 1)
    (fun m : ℕ => (continuous_compactGaussianApprox A ((m:ℝ)+1)).aestronglyMeasurable)
    (compactGaussianApprox_integrable hA hAn 1 zero_lt_one)
    (fun m => ae_of_all _ (fun x => by
      rw [Real.norm_eq_abs, abs_of_pos (compactGaussianApprox_pos _ _ _)]
      unfold compactGaussianApprox
      apply Real.exp_le_exp.mpr
      have hm : (0:ℝ) ≤ m := Nat.cast_nonneg m
      nlinarith [mul_nonneg hm (sq_nonneg (Metric.infDist x A))]))
    (ae_of_all _ (compactGaussianApprox_tendsto hA.isClosed hAn))
  simpa only [integral_indicator_const (1:ℝ) hA.measurableSet, smul_eq_mul,
    mul_one, measureReal_def] using hdct

theorem compactMultiplicativeBM_of_positiveGaussianPrekopa {n : ℕ}
    (hPL : PositiveGaussianPrekopa n) : CompactMultiplicativeBM n := by
  intro t ht0 ht1 A B hA hB _ _ hAn hBn
  have hM := weightedMinkowski_compact t hA hB
  have hMn := weightedMinkowski_nonempty t hAn hBn
  have hineq (m : ℕ) :
      (∫ x, compactGaussianApprox A ((m:ℝ)+1) x)^(1-t) *
        (∫ x, compactGaussianApprox B ((m:ℝ)+1) x)^t ≤
          ∫ x, compactGaussianApprox (weightedMinkowski t A B) ((m:ℝ)+1) x := by
    have hm : 0 < (m:ℝ)+1 := by positivity
    exact hPL t ht0 ht1 _ _ _
      (continuous_compactGaussianApprox _ _) (continuous_compactGaussianApprox _ _)
      (continuous_compactGaussianApprox _ _)
      (compactGaussianApprox_pos _ _) (compactGaussianApprox_pos _ _)
      (compactGaussianApprox_pos _ _)
      (compactGaussianApprox_gaussianDominated hA hAn _ hm)
      (compactGaussianApprox_gaussianDominated hB hBn _ hm)
      (compactGaussianApprox_gaussianDominated hM hMn _ hm)
      (compactGaussianApprox_prekopa hA hB hAn hBn ht0.le ht1.le _ hm.le)
  have hlimA := (Real.continuousAt_rpow_const (volume A).toReal (1-t)
    (Or.inr (by linarith))).tendsto.comp (integral_compactGaussianApprox_tendsto hA hAn)
  have hlimB := (Real.continuousAt_rpow_const (volume B).toReal t
    (Or.inr ht0.le)).tendsto.comp (integral_compactGaussianApprox_tendsto hB hBn)
  exact le_of_tendsto_of_tendsto (hlimA.mul hlimB)
    (integral_compactGaussianApprox_tendsto hM hMn) (Eventually.of_forall hineq)

#print axioms compactGaussianApprox_gaussianDominated
#print axioms compactGaussianApprox_prekopa
#print axioms integral_compactGaussianApprox_tendsto
#print axioms compactMultiplicativeBM_of_positiveGaussianPrekopa
end CubeSections
