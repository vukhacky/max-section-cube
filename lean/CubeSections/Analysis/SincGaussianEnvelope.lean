import Mathlib.Analysis.SpecialFunctions.Trigonometric.Sinc
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Tactic

/-! The Gaussian majorant for sinc on its central lobe, proved by elementary
calculus. The continuous value at zero and both endpoints are included. -/

noncomputable section
open Set Filter
open scoped Topology

namespace CubeSections

def sincFirstGap (x : ℝ) : ℝ := Real.sin x - x * Real.cos x
def sincCubicGap (x : ℝ) : ℝ := (3 - x ^ 2) * Real.sin x - 3 * x * Real.cos x
def sincGaussianWeight (x : ℝ) : ℝ := Real.exp (x ^ 2 / 6) * Real.sinc x

theorem hasDerivAt_sincFirstGap (x : ℝ) : HasDerivAt sincFirstGap (x * Real.sin x) x := by
  convert (Real.hasDerivAt_sin x).sub ((hasDerivAt_id x).mul (Real.hasDerivAt_cos x)) using 1
  · rfl
  · simp only [id_eq]
    ring

theorem sincFirstGap_pos {x : ℝ} (hx : x ∈ Ioc (0 : ℝ) Real.pi) : 0 < sincFirstGap x := by
  have hmono : StrictMonoOn sincFirstGap (Icc (0 : ℝ) Real.pi) :=
    strictMonoOn_of_hasDerivWithinAt_pos (convex_Icc _ _)
      (by unfold sincFirstGap; fun_prop)
      (fun t _ => (hasDerivAt_sincFirstGap t).hasDerivWithinAt)
      (fun t ht => by
        rw [interior_Icc] at ht
        exact mul_pos ht.1 (Real.sin_pos_of_mem_Ioo ht))
  have h := hmono ⟨le_rfl, Real.pi_pos.le⟩ ⟨hx.1.le, hx.2⟩ hx.1
  simpa only [sincFirstGap, Real.sin_zero, zero_mul, sub_self] using h

theorem hasDerivAt_sincCubicGap (x : ℝ) : HasDerivAt sincCubicGap (x * sincFirstGap x) x := by
  have h := (((hasDerivAt_const x (3 : ℝ)).sub ((hasDerivAt_id x).pow 2)).mul
    (Real.hasDerivAt_sin x)).sub (((hasDerivAt_id x).const_mul 3).mul (Real.hasDerivAt_cos x))
  convert h using 1
  · rfl
  · simp only [Pi.sub_apply, Pi.pow_apply, id_eq, sincFirstGap]
    ring

theorem sincCubicGap_pos {x : ℝ} (hx : x ∈ Ioc (0 : ℝ) Real.pi) : 0 < sincCubicGap x := by
  have hmono : StrictMonoOn sincCubicGap (Icc (0 : ℝ) Real.pi) :=
    strictMonoOn_of_hasDerivWithinAt_pos (convex_Icc _ _)
      (by unfold sincCubicGap; fun_prop)
      (fun t _ => (hasDerivAt_sincCubicGap t).hasDerivWithinAt)
      (fun t ht => by
        rw [interior_Icc] at ht
        exact mul_pos ht.1 (sincFirstGap_pos ⟨ht.1, ht.2.le⟩))
  have h := hmono ⟨le_rfl, Real.pi_pos.le⟩ ⟨hx.1.le, hx.2⟩ hx.1
  simpa [sincCubicGap] using h

theorem hasDerivAt_sinc_of_ne_zero {x : ℝ} (hx : x ≠ 0) :
    HasDerivAt Real.sinc ((x * Real.cos x - Real.sin x) / x ^ 2) x := by
  have h := (Real.hasDerivAt_sin x).div (hasDerivAt_id x) hx
  have h' : HasDerivAt (fun t => Real.sin t / t)
      ((x * Real.cos x - Real.sin x) / x ^ 2) x := by
    convert h using 1
    · rfl
    · simp only [id_eq, mul_one]
      ring
  apply h'.congr_of_eventuallyEq
  filter_upwards [eventually_ne_nhds hx] with t ht
  exact Real.sinc_of_ne_zero ht

theorem hasDerivAt_sincGaussianWeight {x : ℝ} (hx : x ≠ 0) :
    HasDerivAt sincGaussianWeight
      (-(Real.exp (x ^ 2 / 6) * sincCubicGap x) / (3 * x ^ 2)) x := by
  have h := ((((hasDerivAt_id x).pow 2).div_const 6).exp).mul (hasDerivAt_sinc_of_ne_zero hx)
  convert h using 1
  · rfl
  · simp only [Pi.pow_apply, id_eq, sincCubicGap, Real.sinc_of_ne_zero hx]
    field_simp
    ring

theorem sincGaussianWeight_strictAntiOn :
    StrictAntiOn sincGaussianWeight (Icc (0 : ℝ) Real.pi) := by
  apply strictAntiOn_of_hasDerivWithinAt_neg (convex_Icc _ _)
    (by unfold sincGaussianWeight; fun_prop)
  · intro x hx
    rw [interior_Icc] at hx
    exact (hasDerivAt_sincGaussianWeight (ne_of_gt hx.1)).hasDerivWithinAt
  · intro x hx
    rw [interior_Icc] at hx
    exact div_neg_of_neg_of_pos
      (neg_lt_zero.mpr (mul_pos (Real.exp_pos _) (sincCubicGap_pos ⟨hx.1, hx.2.le⟩)))
      (mul_pos (by norm_num) (sq_pos_of_ne_zero (ne_of_gt hx.1)))

theorem sinc_gaussian_envelope_pos {x : ℝ} (hx : x ∈ Ioc (0 : ℝ) Real.pi) :
    Real.sinc x < Real.exp (-x ^ 2 / 6) := by
  have h := sincGaussianWeight_strictAntiOn ⟨le_rfl, Real.pi_pos.le⟩ ⟨hx.1.le, hx.2⟩ hx.1
  have hm : Real.sinc x * Real.exp (x ^ 2 / 6) < 1 := by
    simpa [sincGaussianWeight, mul_comm] using h
  have hd : Real.sinc x < 1 / Real.exp (x ^ 2 / 6) := (lt_div_iff₀ (Real.exp_pos _)).mpr hm
  simpa only [one_div, ← Real.exp_neg, neg_div] using hd

theorem sinc_gaussian_envelope_nonneg {x : ℝ} (hx : x ∈ Icc (0 : ℝ) Real.pi) :
    Real.sinc x ≤ Real.exp (-x ^ 2 / 6) := by
  rcases hx.1.eq_or_lt with hzero | hpos
  · subst x
    simp
  · exact (sinc_gaussian_envelope_pos ⟨hpos, hx.2⟩).le

theorem sinc_nonneg_central {x : ℝ} (hx : x ∈ Icc (0 : ℝ) Real.pi) : 0 ≤ Real.sinc x := by
  by_cases hzero : x = 0
  · simp [hzero]
  · rw [Real.sinc_of_ne_zero hzero]
    exact div_nonneg (Real.sin_nonneg_of_mem_Icc hx) hx.1

theorem real_sinc_abs (x : ℝ) : Real.sinc |x| = Real.sinc x := by
  by_cases hx : 0 ≤ x
  · rw [abs_of_nonneg hx]
  · rw [abs_of_neg (lt_of_not_ge hx), Real.sinc_neg]

/-- The exact central-lobe Gaussian envelope, including `0` and `±pi`. -/
theorem sinc_gaussian_envelope (x : ℝ) (hx : |x| ≤ Real.pi) :
    |Real.sinc x| ≤ Real.exp (-x ^ 2 / 6) := by
  have hn : 0 ≤ Real.sinc x := by
    rw [← real_sinc_abs x]
    exact sinc_nonneg_central ⟨abs_nonneg x, hx⟩
  rw [abs_of_nonneg hn]
  simpa only [real_sinc_abs, sq_abs] using sinc_gaussian_envelope_nonneg ⟨abs_nonneg x, hx⟩

/-- Strictness holds throughout the central lobe except at zero. -/
theorem sinc_gaussian_envelope_strict (x : ℝ) (hx0 : x ≠ 0) (hx : |x| ≤ Real.pi) :
    |Real.sinc x| < Real.exp (-x ^ 2 / 6) := by
  have hn : 0 ≤ Real.sinc x := by
    rw [← real_sinc_abs x]
    exact sinc_nonneg_central ⟨abs_nonneg x, hx⟩
  rw [abs_of_nonneg hn]
  simpa only [real_sinc_abs, sq_abs] using sinc_gaussian_envelope_pos ⟨abs_pos.mpr hx0, hx⟩

end CubeSections
