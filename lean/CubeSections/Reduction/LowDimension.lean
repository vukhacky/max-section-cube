import CubeSections.Reduction.StrongInduction

/-!
# Dimensions one, two and three without Brunn--Minkowski

The geometric density premise in dimensions two and three is proved directly
from point and line fibers. Consequently this reduction retains only the two
explicit global analytic estimates, with no central-domination or induction
hypothesis.
-/
noncomputable section
namespace CubeSections

theorem lowDimension_window_bound_of_global_estimates
    (q k : ℕ) (hq : q=2 ∨ q=3 ∨ q=4) (hk : k=2 ∨ k=3)
    (hincidence : ∀ m : ℕ, ∀ U : Frame m k, RowReplacement U →
      Certificates.framePairIncidence (coalescedFrame U) ≤ slabDeficit U)
    (n : ℕ) (hlo : q*k ≤ n) (hhi : n ≤ (q+1)*k) (U : Frame n k) :
    sectionVolume U ≤ sharpValue n k := by
  have hq₂ : 2 ≤ q := by omega
  have hq₁ : 1 ≤ q := by omega
  have hk₁ : 1 ≤ k := by omega
  obtain ⟨t,V,hV⟩ := exists_windowMaximizingFrame hq₁ hk₁
  have hknV := windowDimension_ge hq₁ t
  have hboundV : sectionVolume V ≤ sharpValue (windowDimension q k t) k := by
    by_cases hend : t.val=0 ∨ t.val=k
    · exact (windowMaximizer_endpoint_eq hq₁ hk₁ t V hV hend).le
    · have hleft : q*k < windowDimension q k t := by dsimp [windowDimension]; omega
      have hright : windowDimension q k t < (q+1)*k := by
        have htk : t.val<k := by have ht := t.isLt; omega
        dsimp [windowDimension]
        nlinarith
      have hquot : windowDimension q k t / k = q := by
        have hl : q ≤ windowDimension q k t / k :=
          (Nat.le_div_iff_mul_le (by omega)).mpr hleft.le
        have hh : windowDimension q k t / k < q+1 :=
          (Nat.div_lt_iff_lt_mul (by omega)).mpr hright
        omega
      have hmax : RatioMaximalOnWindow q V := windowMaximizing_compare t V hV
      have hfixed := windowMaximizing_isMaximizing hq₁ hk₁ t V hV
      have hwin := reciprocalWindow_of_windowMaximizer hq₂ hk₁ t V hV
      have hrep := rowReplacement_of_ratio_maximal q hq₂ hk₁ V hleft hright hmax
      have hdensity : Certificates.ActualClassDensity V q := by
        have h := actualClassDensity_two_three hk (by simpa only [hquot] using hq₂)
          V hfixed (by simpa only [hquot] using hwin)
        simpa only [hquot] using h
      have hinc := hincidence _ V hrep
      rw [Certificates.framePairIncidence_coalesced] at hinc
      exact (Certificates.balanced_and_target_of_ratioMaximizing_smallQuotient q hq hk₁ V
        hleft hright hmax hdensity hinc).2.le
  have hkn : k ≤ n := (by simpa using Nat.mul_le_mul_right k hq₁ : k ≤ q*k).trans hlo
  have hcompare := windowMaximizing_compare t V hV n hlo hhi U
  have hratio : sectionVolume V / sharpValue (windowDimension q k t) k ≤ 1 :=
    (div_le_one (sharpValue_pos hk₁ hknV)).mpr hboundV
  exact (div_le_one (sharpValue_pos hk₁ hkn)).mp (hcompare.trans hratio)

theorem upperBound_le_three_of_global_estimates
    (hangular : ∀ (n k : ℕ) (U : Frame n k), gramAngularDefect U ≤ 20*slabDeficit U)
    (hincidence : ∀ (n k : ℕ) (U : Frame n k), RowReplacement U →
      Certificates.framePairIncidence (coalescedFrame U) ≤ slabDeficit U)
    (k : ℕ) (hk : 1 ≤ k) (hk₃ : k ≤ 3) (n : ℕ) (hn : 2*k ≤ n) (U : Frame n k) :
    sectionVolume U ≤ sharpValue n k := by
  by_cases hk1 : k=1
  · subst k
    exact line_sectionVolume_le_sharp U
  have hk23 : k=2 ∨ k=3 := by omega
  have hkn : k ≤ n := by omega
  have hq₂ : 2 ≤ n/k := (Nat.le_div_iff_mul_le (by omega)).mpr hn
  by_cases hq₅ : 5 ≤ n/k
  · exact largeQuotient_bound_of_angular k hk (fun m V => hangular m k V) n hkn hq₅ U
  have hqsmall : n/k=2 ∨ n/k=3 ∨ n/k=4 := by omega
  have hrep := quotient_remainder n k
  have hr := remainder_lt (n := n) hk
  apply lowDimension_window_bound_of_global_estimates (n/k) k hqsmall hk23
    (fun m V => hincidence m k V) n _ _ U
  · omega
  · nlinarith

theorem equality_le_three_of_global_estimates
    (hangular : ∀ (n k : ℕ) (U : Frame n k), gramAngularDefect U ≤ 20*slabDeficit U)
    (hincidence : ∀ (n k : ℕ) (U : Frame n k), RowReplacement U →
      Certificates.framePairIncidence (coalescedFrame U) ≤ slabDeficit U)
    (k : ℕ) (hk : 1 ≤ k) (hk₃ : k ≤ 3) (n : ℕ) (hn : 2*k ≤ n) (U : Frame n k) :
    sectionVolume U = sharpValue n k ↔ IsBalancedSection U := by
  have hbound := upperBound_le_three_of_global_estimates hangular hincidence k hk hk₃
  have hkn : k ≤ n := by omega
  by_cases hk1 : k=1
  · subst k
    exact line_sectionVolume_eq_iff U (by omega)
  have hk23 : k=2 ∨ k=3 := by omega
  have hq₂ : 2 ≤ n/k := (Nat.le_div_iff_mul_le (by omega)).mpr hn
  by_cases hq₅ : 5 ≤ n/k
  · exact largeQuotient_equality_of_angular k hk (fun m V => hangular m k V) n hkn hq₅ U
  have hqsmall : n/k=2 ∨ n/k=3 ∨ n/k=4 := by omega
  constructor
  · intro heq
    have hnrep := quotient_remainder n k
    have hr := remainder_lt (n := n) hk
    have hlo : (n/k)*k ≤ n := by omega
    have hhi : n < (n/k+1)*k := by nlinarith
    have hmax : IsMaximizingFrame U := by
      intro V
      rw [heq]
      exact hbound n hn V
    have hwindow : RatioMaximalOnWindow (n/k) U := by
      intro m hmlo hmhi V
      have h2km : 2*k ≤ m := (Nat.mul_le_mul_right k hq₂).trans hmlo
      have hkm : k ≤ m := by omega
      rw [heq, div_self (ne_of_gt (sharpValue_pos hk hkn))]
      exact (div_le_one (sharpValue_pos hk hkm)).mpr (hbound m h2km V)
    rcases lt_or_eq_of_le hlo with hleft | hleft
    · have hwin := reciprocalWindow_of_ratio_maximal (n/k) hq₂ hk U hleft hhi hwindow
      have hrep := rowReplacement_of_ratio_maximal (n/k) hq₂ hk U hleft hhi hwindow
      have hdensity := actualClassDensity_two_three hk23 hq₂ U hmax hwin
      have hinc := hincidence n k U hrep
      rw [Certificates.framePairIncidence_coalesced] at hinc
      exact Certificates.isBalancedSection_of_maximizing_smallQuotient
        hk hkn hqsmall U hmax hwin hdensity hinc
    · have hgoal : ∀ (m : ℕ), m=(n/k)*k → ∀ V : Frame m k,
          IsMaximizingFrame V → gramAngularDefect V ≤ 20*slabDeficit V →
          sectionVolume V=sharpValue m k → IsBalancedSection V := by
        intro m hm
        subst m
        exact fun V hV ha he => divisible_equality_isBalanced_of_angular
          (n/k) k hq₂ hk V hV ha he
      exact hgoal n hleft.symm U hmax (hangular n k U) heq
  · exact sectionVolume_eq_sharp_of_isBalancedSection U

/-- No Brunn--Minkowski premise appears in dimensions at most three. -/
theorem maximalSection_le_three_of_global_estimates
    (hangular : ∀ (n k : ℕ) (U : Frame n k), gramAngularDefect U ≤ 20*slabDeficit U)
    (hincidence : ∀ (n k : ℕ) (U : Frame n k), RowReplacement U →
      Certificates.framePairIncidence (coalescedFrame U) ≤ slabDeficit U)
    (n k : ℕ) (hk : 1 ≤ k) (hk₃ : k ≤ 3) (hn : 2*k ≤ n) (U : Frame n k) :
    sectionVolume U ≤ sharpValue n k ∧
      (sectionVolume U=sharpValue n k ↔ IsBalancedSection U) :=
  ⟨upperBound_le_three_of_global_estimates hangular hincidence k hk hk₃ n hn U,
   equality_le_three_of_global_estimates hangular hincidence k hk hk₃ n hn U⟩

#print axioms lowDimension_window_bound_of_global_estimates
#print axioms upperBound_le_three_of_global_estimates
#print axioms equality_le_three_of_global_estimates
#print axioms maximalSection_le_three_of_global_estimates
end CubeSections
