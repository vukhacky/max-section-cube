import CubeSections.Integer.FiberRatio
import CubeSections.Geometry.ZeroDimension

/-! Explicit zero-dimensional fiber comparison for the k=2 induction step. -/
noncomputable section
namespace CubeSections

theorem fiberRadius_ge_reciprocal (q m l : ℕ) (hq : 1 ≤ q) (hm : m ≤ q) (hl : l ≤ q) :
    1 / (q : ℝ) ≤ fiberRadius q m l := by
  have hqR : (0 : ℝ) < q := by exact_mod_cast (show 0 < q by omega)
  have hmR : (m : ℝ) ≤ q := by exact_mod_cast hm
  have hlR : (l : ℝ) ≤ q := by exact_mod_cast hl
  have hexp : 0 ≤ (q : ℝ) - ((m : ℝ) + (l : ℝ)) / 2 := by linarith
  have hp : (1 : ℝ) ≤ (1 + 1 / (q : ℝ)) ^ ((q : ℝ) - ((m : ℝ) + (l : ℝ)) / 2) :=
    Real.one_le_rpow (by
      have hi : 0 ≤ 1 / (q : ℝ) := by positivity
      linarith) hexp
  unfold fiberRadius
  simpa only [mul_one] using mul_le_mul_of_nonneg_left hp (by positivity : 0 ≤ 1 / (q : ℝ))

theorem sharpValue_two_ge_quotient (q r : ℕ) (hq : 1 ≤ q) (hr : r ≤ 2) :
    (q : ℝ) ≤ sharpValue (q * 2 + r) 2 := by
  have hqR : (0 : ℝ) < q := by exact_mod_cast (show 0 < q by omega)
  have hb : (1 : ℝ) ≤ 1 + 1 / (q : ℝ) := by
    have hi : 0 ≤ 1 / (q : ℝ) := by positivity
    linarith
  have hp : (1 : ℝ) ≤ (1 + 1 / (q : ℝ)) ^ r := one_le_pow₀ hb
  apply (sq_le_sq₀ hqR.le (sharpValue_nonneg _ _)).mp
  rw [sharpValue_window_sq_factor q 2 r hq (by omega) hr]
  nlinarith [mul_nonneg (sq_nonneg (q : ℝ)) (sub_nonneg.mpr hp)]

theorem pointFiber_target_ratio (q r m l : ℕ) (hq : 1 ≤ q) (hr : r ≤ 2)
    (hm : m ≤ q) (hl : l ≤ q) :
    1 / sharpValue (q * 2 + r) 2 ≤ fiberRadius q m l := by
  have hqR : (0 : ℝ) < q := by exact_mod_cast (show 0 < q by omega)
  exact (one_div_le_one_div_of_le hqR (sharpValue_two_ge_quotient q r hq hr)).trans
    (fiberRadius_ge_reciprocal q m l hq hm hl)

theorem zeroDimensionalFiber_volume_ratio (q r m l N : ℕ) (hq : 1 ≤ q) (hr : r ≤ 2)
    (hm : m ≤ q) (hl : l ≤ q) (U : Frame N 0) :
    sectionVolume U / sharpValue (q * 2 + r) 2 ≤ fiberRadius q m l := by
  rw [zeroDimension_sectionVolume]
  exact pointFiber_target_ratio q r m l hq hr hm hl

end CubeSections
