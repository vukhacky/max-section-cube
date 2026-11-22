import CubeSections.Analysis.PositiveDensityInverse
import Mathlib.Analysis.MeanInequalities

/-! One-dimensional Prekopa--Leindler for continuous strictly positive integrable
input densities. The proof constructs their actual increasing transport, uses
weighted AM--GM for the interpolated derivative, and applies change of variables.
The output function needs only nonnegativity and integrability.
-/
noncomputable section
open Set MeasureTheory ProbabilityTheory
namespace CubeSections

/-- The scalar Jacobian inequality behind the one-dimensional transport proof. -/
theorem prekopa_scalar_jacobian (a b t : ℝ) (ha : 0 < a) (hb : 0 < b)
    (ht₀ : 0 ≤ t) (ht₁ : t ≤ 1) :
    a ≤ (a^(1-t)*b^t)*((1-t)+t*(a/b)) := by
  have hgm := Real.geom_mean_le_arith_mean2_weighted
    (show 0 ≤ 1-t by linarith) ht₀ (by norm_num : (0 : ℝ) ≤ 1)
    (div_pos ha hb).le (show (1-t)+t=1 by ring)
  simp only [Real.one_rpow, one_mul, mul_one] at hgm
  have heq : (a^(1-t)*b^t)*(a/b)^t = a := by
    rw [mul_assoc, ← Real.mul_rpow hb.le (div_pos ha hb).le,
      mul_div_cancel₀ _ (ne_of_gt hb), ← Real.rpow_add ha]
    norm_num
  calc
    a = (a^(1-t)*b^t)*(a/b)^t := heq.symm
    _ ≤ _ := mul_le_mul_of_nonneg_left hgm (by positivity)

/-- Normalized positive continuous one-dimensional Prekopa--Leindler. -/
theorem prekopaLeindler_one_normalized
    (f g h : ℝ → ℝ) (t : ℝ) (ht₀ : 0 < t) (ht₁ : t < 1)
    (hfc : Continuous f) (hfi : Integrable f) (hfp : ∀ x, 0 < f x)
    (hfm : (∫ x, f x)=1)
    (hgc : Continuous g) (hgi : Integrable g) (hgp : ∀ x, 0 < g x)
    (hgm : (∫ x, g x)=1)
    (hhi : Integrable h) (hhp : ∀ x, 0 ≤ h x)
    (hbound : ∀ x y, (f x)^(1-t)*(g y)^t ≤ h ((1-t)*x+t*y)) :
    1 ≤ ∫ z, h z := by
  let T : ℝ → ℝ := fun x => positiveDensityInverse g hgc hgi hgp hgm
    (densityGaussianTransport f x)
  have hTd (x : ℝ) : HasDerivAt T (f x/g (T x)) x := by
    have hd := (hasDerivAt_positiveDensityInverse hgc hgi hgp hgm
      (densityGaussianTransport f x)).comp x
      (hasDerivAt_densityGaussianTransport hfc hfi hfp hfm x)
    convert hd using 1
    · rfl
    · dsimp only [densityGaussianSlope, T]
      field_simp [ne_of_gt (gaussianPDFReal_pos 0 1 (densityGaussianTransport f x)
        (by norm_num)), ne_of_gt (hgp _)]
  let S : ℝ → ℝ := fun x => (1-t)*x+t*T x
  let w : ℝ → ℝ := fun x => (1-t)+t*(f x/g (T x))
  have hSd (x : ℝ) : HasDerivAt S (w x) x := by
    convert ((hasDerivAt_id x).const_mul (1-t)).add ((hTd x).const_mul t) using 1 <;>
      simp [S, w] <;> rfl
  have hwp (x : ℝ) : 0 < w x := by
    dsimp only [w]
    have : 0 < f x/g (T x) := div_pos (hfp x) (hgp _)
    positivity
  have hSm : StrictMono S := strictMono_of_hasDerivAt_pos hSd hwp
  have hcov := integral_image_eq_integral_deriv_smul_of_monotoneOn
    (s := (univ : Set ℝ)) MeasurableSet.univ
    (fun x _ => (hSd x).hasDerivWithinAt) (hSm.monotone.monotoneOn univ) h
  have hcovI := integrableOn_image_iff_integrableOn_deriv_smul_of_monotoneOn
    (s := (univ : Set ℝ)) MeasurableSet.univ
    (fun x _ => (hSd x).hasDerivWithinAt) (hSm.monotone.monotoneOn univ) h
  simp only [image_univ, Measure.restrict_univ, smul_eq_mul, integrableOn_univ] at hcov hcovI
  have hwi : Integrable (fun x => w x*h (S x)) := hcovI.1 hhi.integrableOn
  have hpoint (x : ℝ) : f x ≤ w x*h (S x) := by
    have hj := prekopa_scalar_jacobian (f x) (g (T x)) t (hfp x) (hgp _) ht₀.le ht₁.le
    have hh := mul_le_mul_of_nonneg_right (hbound x (T x)) (hwp x).le
    dsimp only [S,w] at *
    nlinarith
  calc
    1 = ∫ x, f x := hfm.symm
    _ ≤ ∫ x, w x*h (S x) := integral_mono hfi hwi hpoint
    _ = ∫ z in range S, h z := hcov.symm
    _ ≤ ∫ z, h z := setIntegral_le_integral hhi (ae_of_all _ hhp)

/-- Unnormalized positive continuous one-dimensional Prekopa--Leindler.
No transportation field, probability law, or analytic inequality is assumed. -/
theorem prekopaLeindler_one_positive
    (f g h : ℝ → ℝ) (t : ℝ) (ht₀ : 0 < t) (ht₁ : t < 1)
    (hfc : Continuous f) (hfi : Integrable f) (hfp : ∀ x, 0 < f x)
    (hgc : Continuous g) (hgi : Integrable g) (hgp : ∀ x, 0 < g x)
    (hhi : Integrable h) (hhp : ∀ x, 0 ≤ h x)
    (hbound : ∀ x y, (f x)^(1-t)*(g y)^t ≤ h ((1-t)*x+t*y)) :
    (∫ x, f x)^(1-t)*(∫ y, g y)^t ≤ ∫ z, h z := by
  let M : ℝ := ∫ x, f x
  let N : ℝ := ∫ y, g y
  have hM : 0 < M := integral_pos_of_integrable_nonneg_ne_zero hfc hfi
    (fun x => (hfp x).le) (ne_of_gt (hfp 0))
  have hN : 0 < N := integral_pos_of_integrable_nonneg_ne_zero hgc hgi
    (fun x => (hgp x).le) (ne_of_gt (hgp 0))
  let K : ℝ := M^(1-t)*N^t
  have hK : 0 < K := mul_pos (Real.rpow_pos_of_pos hM _) (Real.rpow_pos_of_pos hN _)
  have hmassF : (∫ x, f x/M)=1 := by rw [integral_div]; exact div_self (ne_of_gt hM)
  have hmassG : (∫ x, g x/N)=1 := by rw [integral_div]; exact div_self (ne_of_gt hN)
  have hbound' (x y : ℝ) : (f x/M)^(1-t)*(g y/N)^t ≤ h ((1-t)*x+t*y)/K := by
    rw [Real.div_rpow (hfp x).le hM.le, Real.div_rpow (hgp y).le hN.le, div_mul_div_comm]
    exact div_le_div_of_nonneg_right (hbound x y) hK.le
  have hPL := prekopaLeindler_one_normalized
    (fun x => f x/M) (fun x => g x/N) (fun x => h x/K) t ht₀ ht₁
    (hfc.div_const M) (hfi.div_const M) (fun x => div_pos (hfp x) hM) hmassF
    (hgc.div_const N) (hgi.div_const N) (fun x => div_pos (hgp x) hN) hmassG
    (hhi.div_const K) (fun x => div_nonneg (hhp x) hK.le) hbound'
  rw [integral_div] at hPL
  have h := (le_div_iff₀ hK).mp hPL
  simpa only [one_mul] using h

#print axioms prekopaLeindler_one_normalized
#print axioms prekopaLeindler_one_positive
end CubeSections
