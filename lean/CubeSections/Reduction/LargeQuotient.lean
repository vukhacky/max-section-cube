import CubeSections.Geometry.WindowMaxima
import CubeSections.Geometry.Rigidity
import CubeSections.Geometry.BalancedVolume
import CubeSections.Integer.ReciprocalWindow
import CubeSections.Integer.LargeQuotient
import CubeSections.Integer.ContinuousTarget

/-! Complete large-quotient window reduction from one explicit analytic premise.
The universal angular inequality is a hypothesis of these declarations. This
module does not close the unconditional main theorem or assert that premise. -/
noncomputable section
namespace CubeSections

theorem sectionVolume_le_slabBound_of_angular {n k : ℕ} (U : Frame n k)
    (hangular : gramAngularDefect U ≤ 20 * slabDeficit U) :
    sectionVolume U ≤ slabBound U := by
  have hδ : 0 ≤ slabDeficit U := by nlinarith [gramAngularDefect_nonneg U]
  rw [slabDeficit_eq_log_ratio] at hδ
  have hratio : 1 ≤ slabBound U / sectionVolume U :=
    (Real.log_nonneg_iff (div_pos (slabBound_pos U) (sectionVolume_pos U))).mp hδ
  exact (one_le_div (sectionVolume_pos U)).mp hratio

theorem window_volume_bound_of_angular
    (q k : ℕ) (hq : 5 ≤ q) (hk : 1 ≤ k)
    (hangular : ∀ m : ℕ, ∀ U : Frame m k,
      gramAngularDefect U ≤ 20 * slabDeficit U)
    (n : ℕ) (hlo : q * k ≤ n) (hhi : n ≤ (q + 1) * k) (U : Frame n k) :
    sectionVolume U ≤ sharpValue n k := by
  have hq1 : 1 ≤ q := by omega
  obtain ⟨t, V, hV⟩ := exists_windowMaximizingFrame hq1 hk
  have hknV := windowDimension_ge hq1 t
  have hboundV : sectionVolume V ≤ sharpValue (windowDimension q k t) k := by
    by_cases ht0 : t.val = 0
    · have hd : windowDimension q k t = q * k := by simp [windowDimension, ht0]
      have hend : ∀ W : Frame (windowDimension q k t) k,
          sectionVolume W ≤ sharpValue (windowDimension q k t) k := by
        rw [hd]
        intro W
        exact sectionVolume_le_sharp_divisible_of_slabBound q k hq1 hk W
          (sectionVolume_le_slabBound_of_angular W (hangular _ W))
      exact hend V
    · by_cases htk : t.val = k
      · have hd : windowDimension q k t = (q + 1) * k := by
          simp only [windowDimension, htk]
          ring
        have hend : ∀ W : Frame (windowDimension q k t) k,
            sectionVolume W ≤ sharpValue (windowDimension q k t) k := by
          rw [hd]
          intro W
          exact sectionVolume_le_sharp_divisible_of_slabBound (q + 1) k (by omega) hk W
            (sectionVolume_le_slabBound_of_angular W (hangular _ W))
        exact hend V
      · have hleft : q * k < windowDimension q k t := by
          dsimp [windowDimension]
          omega
        have hright : windowDimension q k t < (q + 1) * k := by
          dsimp [windowDimension]
          have ht := t.isLt
          have htklt : t.val < k := by omega
          nlinarith
        have hm : RatioMaximalOnWindow q V :=
          windowMaximizing_compare t V hV
        have hwin := reciprocalWindow_of_ratio_maximal q (by omega) hk V hleft hright hm
        have hrep := rowReplacement_of_ratio_maximal q (by omega) hk V hleft hright hm
        have hquot : windowDimension q k t / k = q := by
          have hl : q ≤ windowDimension q k t / k :=
            (Nat.le_div_iff_mul_le (by omega)).mpr hleft.le
          have hh : windowDimension q k t / k < q + 1 :=
            (Nat.div_lt_iff_lt_mul (by omega)).mpr hright
          omega
        apply sectionVolume_le_sharp_largeQuotient hk hknV (by simpa only [hquot] using hq)
          V hrep
        · simpa only [hquot] using hwin
        · exact hangular _ V
  have hkn : k ≤ n := (by simpa using Nat.mul_le_mul_right k hq1 : k ≤ q * k).trans hlo
  have hcompare := windowMaximizing_compare t V hV n hlo hhi U
  have hratio : sectionVolume V / sharpValue (windowDimension q k t) k ≤ 1 :=
    (div_le_one (sharpValue_pos hk hknV)).mpr hboundV
  exact (div_le_one (sharpValue_pos hk hkn)).mp (hcompare.trans hratio)

theorem largeQuotient_bound_of_angular
    (k : ℕ) (hk : 1 ≤ k)
    (hangular : ∀ m : ℕ, ∀ U : Frame m k,
      gramAngularDefect U ≤ 20 * slabDeficit U)
    (n : ℕ) (hkn : k ≤ n) (hq : 5 ≤ n / k) (U : Frame n k) :
    sectionVolume U ≤ sharpValue n k := by
  have hn := quotient_remainder n k
  have hr := remainder_lt (n := n) hk
  apply window_volume_bound_of_angular (n / k) k hq hk hangular n
  · omega
  · nlinarith

theorem divisible_equality_isBalanced_of_angular (q k : ℕ)
    (hq : 2 ≤ q) (hk : 1 ≤ k) (U : Frame (q * k) k)
    (hmax : IsMaximizingFrame U)
    (hangular : gramAngularDefect U ≤ 20 * slabDeficit U)
    (heq : sectionVolume U = sharpValue (q * k) k) : IsBalancedSection U := by
  have hq1 : 1 ≤ q := by omega
  have hkn : k ≤ q * k := by simpa using Nat.mul_le_mul_right k hq1
  have hBL := sectionVolume_le_slabBound_of_angular U hangular
  have hu := leverage_uniform_of_divisible_equality q k hq1 hk U hBL heq
  have hδ := slabDeficit_zero_of_divisible_equality q k hq1 hk U hBL heq
  have hzero : gramAngularDefect U = 0 := by
    rw [hδ, mul_zero] at hangular
    exact le_antisymm hangular (gramAngularDefect_nonneg U)
  have hqR : (1 : ℝ) < q := by exact_mod_cast (show 1 < q by omega)
  have hlt : 1 / (q : ℝ) < 1 := (div_lt_one (by linarith)).mpr hqR
  have hrep : RowReplacement U := by
    intro i j hij
    exact maximizing_leverage_gap U hmax i j
      (by rw [hu i]; exact hlt) (by rw [hu j]; exact hlt)
  have hqdiv : (q * k) / k = q := Nat.mul_div_left q (by omega)
  have hwin : ReciprocalWindow ((q * k) / k) U := by
    rw [hqdiv]
    intro i
    rw [hu i]
    exact ⟨one_div_le_one_div_of_le (by linarith) (by linarith), le_rfl⟩
  exact isBalancedSection_of_rowReplacement_zeroAngular hk hkn U hrep hwin hzero

theorem largeQuotient_equality_of_angular
    (k : ℕ) (hk : 1 ≤ k)
    (hangular : ∀ m : ℕ, ∀ U : Frame m k,
      gramAngularDefect U ≤ 20 * slabDeficit U)
    (n : ℕ) (hkn : k ≤ n) (hq : 5 ≤ n / k) (U : Frame n k) :
    sectionVolume U = sharpValue n k ↔ IsBalancedSection U := by
  constructor
  · intro heq
    generalize hqeq : n / k = q at hq
    have hn := quotient_remainder n k
    rw [hqeq] at hn
    have hr := remainder_lt (n := n) hk
    have hlo : q * k ≤ n := by omega
    have hhi : n < (q + 1) * k := by nlinarith
    have hwindow : RatioMaximalOnWindow q U := by
      intro m hmlo hmhi V
      have hv := window_volume_bound_of_angular q k hq hk hangular m hmlo hmhi V
      have hkm : k ≤ m := (by simpa using Nat.mul_le_mul_right k (show 1 ≤ q by omega) :
        k ≤ q * k).trans hmlo
      rw [heq, div_self (ne_of_gt (sharpValue_pos hk hkn))]
      exact (div_le_one (sharpValue_pos hk hkm)).mpr hv
    have hm : IsMaximizingFrame U := by
      intro V
      have h := hwindow n hlo hhi.le V
      exact (div_le_div_iff_of_pos_right (sharpValue_pos hk hkn)).mp h
    rcases lt_or_eq_of_le hlo with hleft | hleft
    · have hwin := reciprocalWindow_of_ratio_maximal q (by omega) hk U hleft hhi hwindow
      have hrep := rowReplacement_of_ratio_maximal q (by omega) hk U hleft hhi hwindow
      have hwin' : ReciprocalWindow (n / k) U := by simpa only [hqeq] using hwin
      have hz := angularDefect_zero_of_largeQuotient_equality hk hkn
        (by simpa only [hqeq] using hq) U hrep hwin' (hangular n U) heq
      exact isBalancedSection_of_rowReplacement_zeroAngular hk hkn U hrep hwin' hz
    · have hgoal : ∀ (m : ℕ), m = q * k → ∀ V : Frame m k,
          IsMaximizingFrame V → gramAngularDefect V ≤ 20 * slabDeficit V →
          sectionVolume V = sharpValue m k → IsBalancedSection V := by
        intro m hm
        subst m
        exact fun V hV ha he => divisible_equality_isBalanced_of_angular q k
          (by omega) hk V hV ha he
      exact hgoal n hleft.symm U hm (hangular n U) heq
  · exact sectionVolume_eq_sharp_of_isBalancedSection U

end CubeSections
