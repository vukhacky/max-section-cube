import CubeSections.Analysis.GaussianDominated
import CubeSections.Analysis.PositiveGaussianLaw
import Mathlib.InformationTheory.KullbackLeibler.Basic
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog

/-! Finite moments and entropy of positive Gaussian-dominated densities.
All measure statements refer to the actual density with respect to volume. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 600000
open MeasureTheory ProbabilityTheory InformationTheory Set
open scoped ENNReal NNReal
namespace CubeSections

theorem abs_mul_log_le_sq_add_sqrt {u : ℝ} (hu : 0 < u) :
    |u * Real.log u| ≤ u^2 + 2 * Real.sqrt u := by
  by_cases h : 1 ≤ u
  · rw [abs_of_nonneg (mul_nonneg hu.le (Real.log_nonneg h))]
    have hl := Real.log_le_sub_one_of_pos hu
    have hm := mul_le_mul_of_nonneg_left hl hu.le
    nlinarith [Real.sqrt_nonneg u]
  · have hs : 0 < Real.sqrt u := Real.sqrt_pos.mpr hu
    have hl := Real.log_le_sub_one_of_pos (inv_pos.mpr hs)
    rw [Real.log_inv, Real.log_sqrt hu.le] at hl
    have hm := mul_le_mul_of_nonneg_left hl (by positivity : 0 ≤ 2*u)
    have heq : u * (Real.sqrt u)⁻¹ = Real.sqrt u := by
      rw [← div_eq_mul_inv]
      apply (div_eq_iff (ne_of_gt hs)).mpr
      nlinarith [Real.sq_sqrt hu.le]
    rw [abs_of_nonpos (mul_nonpos_of_nonneg_of_nonpos hu.le
      (Real.log_nonpos hu.le (le_of_not_ge h)))]
    have hid : 2*u*((Real.sqrt u)⁻¹-1) = 2*Real.sqrt u-2*u := by
      calc
        _ = 2*(u*(Real.sqrt u)⁻¹)-2*u := by ring
        _ = _ := by rw [heq]
    rw [hid] at hm
    nlinarith [sq_nonneg u]

theorem GaussianDominated.sq {n : ℕ} {f : E n → ℝ} (hf : GaussianDominated f) :
    GaussianDominated (fun x => (f x)^2) := by
  obtain ⟨C,a,hC,ha,hb⟩ := hf
  refine ⟨C^2, 2*a, by positivity, by positivity, fun x => ?_⟩
  rw [abs_of_nonneg (sq_nonneg _)]
  have hh := sq_le_sq₀ (abs_nonneg (f x)) (by positivity : 0 ≤ C*Real.exp (-a*‖x‖^2)) |>.mpr (hb x)
  rw [sq_abs, mul_pow, ← Real.exp_nat_mul] at hh
  convert hh using 1 <;> congr 1 <;> ring

theorem GaussianDominated.sqrt {n : ℕ} {f : E n → ℝ} (hf : GaussianDominated f) :
    GaussianDominated (fun x => Real.sqrt (f x)) := by
  obtain ⟨C,a,hC,ha,hb⟩ := hf
  refine ⟨Real.sqrt C, a/2, Real.sqrt_pos.mpr hC, by positivity, fun x => ?_⟩
  rw [abs_of_nonneg (Real.sqrt_nonneg _)]
  have hh := Real.sqrt_le_sqrt ((le_abs_self (f x)).trans (hb x))
  rw [Real.sqrt_mul hC.le] at hh
  have he : Real.sqrt (Real.exp (-a*‖x‖^2)) = Real.exp (-(a/2)*‖x‖^2) := by
    apply (Real.sqrt_eq_iff_eq_sq (by positivity) (by positivity)).mpr
    rw [← Real.exp_nat_mul]
    congr 1
    ring
  rw [he] at hh
  exact hh

theorem GaussianDominated.integrable_mul_log {n : ℕ} {f : E n → ℝ}
    (hf : GaussianDominated f) (hc : Continuous f) (hp : ∀ x, 0 < f x) :
    Integrable (fun x => f x * Real.log (f x)) := by
  have hi := (hf.sq.integrable (hc.pow 2)).add
    ((hf.sqrt.integrable hc.sqrt).const_mul 2)
  apply hi.mono' (hc.mul (hc.log (fun x => ne_of_gt (hp x)))).aestronglyMeasurable
  exact ae_of_all _ (fun x => by
    rw [Real.norm_eq_abs]
    exact abs_mul_log_le_sq_add_sqrt (hp x))

theorem GaussianDominated.norm_sq_mul {n : ℕ} {f : E n → ℝ}
    (hf : GaussianDominated f) : GaussianDominated (fun x => ‖x‖^2*f x) := by
  obtain ⟨C,a,hC,ha,hb⟩ := hf
  refine ⟨2*C/a,a/2,by positivity,by positivity,fun x => ?_⟩
  rw [abs_mul, abs_of_nonneg (sq_nonneg _)]
  have ht : (a/2)*‖x‖^2 ≤ Real.exp ((a/2)*‖x‖^2) := by
    linarith [Real.add_one_le_exp ((a/2)*‖x‖^2)]
  have hm := mul_le_mul_of_nonneg_right ht (by positivity : 0 ≤ (2*C/a)*Real.exp (-a*‖x‖^2))
  have hleft : ((a/2)*‖x‖^2)*((2*C/a)*Real.exp (-a*‖x‖^2)) =
      ‖x‖^2*(C*Real.exp (-a*‖x‖^2)) := by field_simp
  have hright : Real.exp ((a/2)*‖x‖^2)*((2*C/a)*Real.exp (-a*‖x‖^2)) =
      (2*C/a)*Real.exp (-(a/2)*‖x‖^2) := by
    rw [mul_left_comm, ← Real.exp_add]
    congr 2
    ring
  rw [hleft, hright] at hm
  exact (mul_le_mul_of_nonneg_left (hb x) (sq_nonneg _)).trans hm

#print axioms GaussianDominated.integrable_mul_log
#print axioms GaussianDominated.norm_sq_mul
end CubeSections
