import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp

/-! A rational curvature majorant for the entropy chord gap. -/

noncomputable section
open Set

namespace CubeSections

/-- Entropy minus its chord on the interval `[0,a]`, in reciprocal coordinates. -/
def entropyChordGap (a z : ℝ) : ℝ :=
  -(1 - z) * Real.log (1 - z) + z * ((1 - a) / a * Real.log (1 - a))

/-- Polynomial with the majorizing negative second derivative and zero endpoints. -/
def entropyCurvaturePoly (a z : ℝ) : ℝ :=
  (a * z - z ^ 2) / 2 + (a ^ 2 * z - z ^ 3) / 6 +
    (a ^ 3 * z - z ^ 4) / (12 * (1 - a))

def entropyCurvaturePolyDeriv (a z : ℝ) : ℝ :=
  (a - 2 * z) / 2 + (a ^ 2 - 3 * z ^ 2) / 6 +
    (a ^ 3 - 4 * z ^ 3) / (12 * (1 - a))

def entropyChordGapDeriv (a z : ℝ) : ℝ :=
  Real.log (1 - z) + 1 + (1 - a) / a * Real.log (1 - a)

theorem hasDerivAt_entropyChordGap (a z : ℝ) (hz : z < 1) :
    HasDerivAt (entropyChordGap a) (entropyChordGapDeriv a z) z := by
  have hn : 1 - z ≠ 0 := by linarith
  have hbase := (hasDerivAt_id z).const_sub 1
  have hlog := hbase.log hn
  have h := (hbase.neg.mul hlog).add
    ((hasDerivAt_id z).mul_const ((1 - a) / a * Real.log (1 - a)))
  convert h using 1
  · rfl
  · dsimp [entropyChordGapDeriv]
    field_simp

theorem hasDerivAt_entropyChordGapDeriv (a z : ℝ) (hz : z < 1) :
    HasDerivAt (entropyChordGapDeriv a) (-(1 / (1 - z))) z := by
  have h := (((hasDerivAt_id z).const_sub 1).log (by linarith : 1 - z ≠ 0)).add_const 1
  convert h.add_const ((1 - a) / a * Real.log (1 - a)) using 1
  · rfl
  · dsimp
    ring

theorem hasDerivAt_entropyCurvaturePoly (a z : ℝ) :
    HasDerivAt (entropyCurvaturePoly a) (entropyCurvaturePolyDeriv a z) z := by
  have h₂ := (((hasDerivAt_id z).const_mul a).sub ((hasDerivAt_id z).pow 2)).div_const 2
  have h₃ := (((hasDerivAt_id z).const_mul (a ^ 2)).sub ((hasDerivAt_id z).pow 3)).div_const 6
  have h₄ := (((hasDerivAt_id z).const_mul (a ^ 3)).sub ((hasDerivAt_id z).pow 4)).div_const (12 * (1 - a))
  convert (h₂.add h₃).add h₄ using 1
  · rfl
  · dsimp [entropyCurvaturePolyDeriv]
    ring

theorem hasDerivAt_entropyCurvaturePolyDeriv (a z : ℝ) :
    HasDerivAt (entropyCurvaturePolyDeriv a) (-1 - z - z ^ 2 / (1 - a)) z := by
  have h₁ := (((hasDerivAt_id z).const_mul 2).const_sub a).div_const 2
  have h₂ := ((((hasDerivAt_id z).pow 2).const_mul 3).const_sub (a ^ 2)).div_const 6
  have h₃ := ((((hasDerivAt_id z).pow 3).const_mul 4).const_sub (a ^ 3)).div_const (12 * (1 - a))
  convert (h₁.add h₂).add h₃ using 1
  · rfl
  · dsimp
    simp only [div_eq_mul_inv, mul_inv_rev]
    ring

theorem entropyCurvature_second_deriv_nonpos (a z : ℝ)
    (ha : a < 1) (hz : z ≤ a) :
    -1 - z - z ^ 2 / (1 - a) + 1 / (1 - z) ≤ 0 := by
  have hza : 0 < 1 - z := by linarith
  have haa : 0 < 1 - a := by linarith
  have hid : -1 - z - z ^ 2 / (1 - a) + 1 / (1 - z) =
      z ^ 2 * (z - a) / ((1 - a) * (1 - z)) := by
    field_simp
    ring
  rw [hid]
  exact div_nonpos_of_nonpos_of_nonneg
    (mul_nonpos_of_nonneg_of_nonpos (sq_nonneg _) (sub_nonpos.mpr hz))
    (mul_pos haa hza).le

theorem entropyCurvature_gap_concave (a : ℝ) (_ha₀ : 0 < a) (ha₁ : a < 1) :
    ConcaveOn ℝ (Icc 0 a) (fun z => entropyCurvaturePoly a z - entropyChordGap a z) := by
  have hfirst (z : ℝ) (hz : z < 1) :=
    (hasDerivAt_entropyCurvaturePoly a z).sub (hasDerivAt_entropyChordGap a z hz)
  have hsecond (z : ℝ) (hz : z < 1) :=
    (hasDerivAt_entropyCurvaturePolyDeriv a z).sub (hasDerivAt_entropyChordGapDeriv a z hz)
  apply concaveOn_of_hasDerivWithinAt2_nonpos (convex_Icc 0 a)
  · intro z hz
    exact (hfirst z (lt_of_le_of_lt hz.2 ha₁)).continuousAt.continuousWithinAt
  · intro z hz
    exact (hfirst z (lt_of_le_of_lt (interior_subset hz).2 ha₁)).hasDerivWithinAt
  · intro z hz
    exact (hsecond z (lt_of_le_of_lt (interior_subset hz).2 ha₁)).hasDerivWithinAt
  · intro z hz
    simpa only [sub_neg_eq_add] using
      entropyCurvature_second_deriv_nonpos a z ha₁ (interior_subset hz).2

theorem entropyChordGap_le_curvaturePoly (a z : ℝ)
    (ha₀ : 0 < a) (ha₁ : a < 1) (hz₀ : 0 ≤ z) (hz₁ : z ≤ a) :
    entropyChordGap a z ≤ entropyCurvaturePoly a z := by
  have h := (entropyCurvature_gap_concave a ha₀ ha₁).2
    (show (0 : ℝ) ∈ Icc 0 a from ⟨le_rfl, ha₀.le⟩)
    (show a ∈ Icc 0 a from ⟨ha₀.le, le_rfl⟩)
    (show 0 ≤ 1 - z / a from sub_nonneg.mpr ((div_le_one ha₀).mpr hz₁))
    (div_nonneg hz₀ ha₀.le) (show 1 - z / a + z / a = 1 by ring)
  have hzero : entropyCurvaturePoly a 0 - entropyChordGap a 0 = 0 := by
    simp [entropyCurvaturePoly, entropyChordGap]
  have hend : entropyCurvaturePoly a a - entropyChordGap a a = 0 := by
    unfold entropyCurvaturePoly entropyChordGap
    field_simp
    ring
  dsimp only at h
  rw [hzero, hend] at h
  have harg : (1 - z / a) • (0 : ℝ) + (z / a) • a = z := by
    simp only [smul_eq_mul, mul_zero, zero_add]
    exact div_mul_cancel₀ z (ne_of_gt ha₀)
  rw [harg] at h
  simpa only [smul_zero, add_zero, sub_nonneg] using h

/-- Manuscript entropy excess above the reciprocal chord. -/
def entropyExcess (q : ℕ) (c : ℝ) : ℝ :=
  -c * Real.log ((q : ℝ) * c) - (1 - (q : ℝ) * c) * Real.log (1 + 1 / (q : ℝ))

/-- Real version of the rational curvature envelope used by the certificate checker. -/
def curvatureEnvelopeReal (q : ℕ) (z : ℝ) : ℝ :=
  let a : ℝ := 1 / ((q : ℝ) + 1)
  a / 2 * (1 + (a + z) / 3 + (a ^ 2 + a * z + z ^ 2) / (6 * (1 - a)))

theorem entropyExcess_le_curvatureEnvelope (q : ℕ) (hq : 2 ≤ q) (c : ℝ)
    (hc₀ : 1 / ((q : ℝ) + 1) ≤ c) (hc₁ : c ≤ 1 / (q : ℝ)) :
    entropyExcess q c ≤
      (1 - (q : ℝ) * c) * (((q : ℝ) + 1) * c - 1) *
        curvatureEnvelopeReal q (1 - (q : ℝ) * c) := by
  have hq₂ : (2 : ℝ) ≤ q := by exact_mod_cast hq
  have hq₀ : (0 : ℝ) < q := by linarith
  have hq₁ : (0 : ℝ) < (q : ℝ) + 1 := by linarith
  let a : ℝ := 1 / ((q : ℝ) + 1)
  let z : ℝ := 1 - (q : ℝ) * c
  have ha₀ : 0 < a := one_div_pos.mpr hq₁
  have ha₁ : a < 1 := (div_lt_one hq₁).mpr (by linarith)
  have hqa : (q : ℝ) * a = 1 - a := by
    dsimp [a]
    field_simp
    ring
  have hz₀ : 0 ≤ z := by
    have hh := (le_div_iff₀ hq₀).mp hc₁
    dsimp [z]
    nlinarith
  have hz₁ : z ≤ a := by
    have hh := mul_le_mul_of_nonneg_left hc₀ hq₀.le
    change (q : ℝ) * a ≤ (q : ℝ) * c at hh
    dsimp [z]
    linarith
  have hlog : Real.log (1 - a) = -Real.log (1 + 1 / (q : ℝ)) := by
    have hinv : 1 - a = (1 + 1 / (q : ℝ))⁻¹ := by
      dsimp [a]
      field_simp
      ring
    rw [hinv, Real.log_inv]
  have hratio : (1 - a) / a = (q : ℝ) := by
    apply (div_eq_iff (ne_of_gt ha₀)).mpr
    linarith
  have hchord : entropyChordGap a z = (q : ℝ) * entropyExcess q c := by
    unfold entropyChordGap entropyExcess
    rw [hlog, hratio]
    dsimp [z]
    have h1 : 1 - (1 - (q : ℝ) * c) = (q : ℝ) * c := by ring
    rw [h1]
    ring
  have hpoly : entropyCurvaturePoly a z =
      (q : ℝ) * ((1 - (q : ℝ) * c) * (((q : ℝ) + 1) * c - 1) *
        curvatureEnvelopeReal q (1 - (q : ℝ) * c)) := by
    unfold entropyCurvaturePoly curvatureEnvelopeReal
    dsimp [a, z]
    field_simp
    ring
  have h := entropyChordGap_le_curvaturePoly a z ha₀ ha₁ hz₀ hz₁
  rw [hchord, hpoly] at h
  nlinarith

end CubeSections
