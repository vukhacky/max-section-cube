import CubeSections.Reduction.LargeQuotient
import CubeSections.Geometry.ClassDensityInduction
import CubeSections.Geometry.LowDimensionClassDensity
import CubeSections.Integer.WindowEndpoints
import CubeSections.Certificates.SmallQuotient
import CubeSections.Certificates.CoalescedIncidence

/-!
# Conditional maximal-section theorem on n ≥ 2k

The three global premises are the angular estimate, the coalesced incidence
estimate with the original section deficit, and midpoint Brunn--Minkowski.
Strong induction uses smaller section dimensions in the same n ≥ 2k range.
-/
noncomputable section
namespace CubeSections

theorem smallQuotient_window_bound_of_restricted_induction
    (q k : ℕ) (hq : q=2 ∨ q=3 ∨ q=4) (hk : 2 ≤ k)
    (hincidence : ∀ m : ℕ, ∀ U : Frame m k, RowReplacement U →
      Certificates.framePairIncidence (coalescedFrame U) ≤ slabDeficit U)
    (hBM : MidpointBrunnMinkowski (k-2))
    (hIH : 1 ≤ k-2 → ∀ N : ℕ, 2*(k-2) ≤ N →
      ∀ V : Frame N (k-2), sectionVolume V ≤ sharpValue N (k-2))
    (n : ℕ) (hlo : q*k ≤ n) (hhi : n ≤ (q+1)*k) (U : Frame n k) :
    sectionVolume U ≤ sharpValue n k := by
  have hq₂ : 2 ≤ q := by omega
  have hq₁ : 1 ≤ q := by omega
  have hk₁ : 1 ≤ k := by omega
  obtain ⟨t,V,hV⟩ := exists_windowMaximizingFrame hq₁ hk₁
  have hknV := windowDimension_ge hq₁ t
  have hboundV : sectionVolume V ≤ sharpValue (windowDimension q k t) k := by
    by_cases hend : t.val = 0 ∨ t.val = k
    · exact (windowMaximizer_endpoint_eq hq₁ hk₁ t V hV hend).le
    · have hleft : q*k < windowDimension q k t := by
        dsimp [windowDimension]
        omega
      have hright : windowDimension q k t < (q+1)*k := by
        have htk : t.val < k := by have ht := t.isLt; omega
        dsimp [windowDimension]
        nlinarith
      have hmax : RatioMaximalOnWindow q V := windowMaximizing_compare t V hV
      have hfixed := windowMaximizing_isMaximizing hq₁ hk₁ t V hV
      have hwin := reciprocalWindow_of_windowMaximizer hq₂ hk₁ t V hV
      have hrep := rowReplacement_of_ratio_maximal q hq₂ hk₁ V hleft hright hmax
      have hdensity := actualClassDensity_of_midpointBM_restricted_induction q t.val hq₂ hk
        (by omega) rfl V hfixed hwin hBM hIH
      have hinc := hincidence _ V hrep
      rw [Certificates.framePairIncidence_coalesced] at hinc
      exact (Certificates.balanced_and_target_of_ratioMaximizing_smallQuotient q hq hk₁ V
        hleft hright hmax hdensity hinc).2.le
  have hkn : k ≤ n := (by simpa using Nat.mul_le_mul_right k hq₁ : k ≤ q*k).trans hlo
  have hcompare := windowMaximizing_compare t V hV n hlo hhi U
  have hratio : sectionVolume V / sharpValue (windowDimension q k t) k ≤ 1 :=
    (div_le_one (sharpValue_pos hk₁ hknV)).mpr hboundV
  exact (div_le_one (sharpValue_pos hk₁ hkn)).mp (hcompare.trans hratio)

/-- Upper bound on the entire n ≥ 2k range, by strong induction on the true
section dimension. Each analytic and geometric global premise remains visible. -/
theorem upperBound_ge_two_mul_of_global_estimates
    (hangular : ∀ (n k : ℕ) (U : Frame n k), gramAngularDefect U ≤ 20*slabDeficit U)
    (hincidence : ∀ (n k : ℕ) (U : Frame n k), RowReplacement U →
      Certificates.framePairIncidence (coalescedFrame U) ≤ slabDeficit U)
    (hBM : ∀ d : ℕ, MidpointBrunnMinkowski d) :
    ∀ (k : ℕ), 1 ≤ k → ∀ (n : ℕ), 2*k ≤ n → ∀ U : Frame n k,
      sectionVolume U ≤ sharpValue n k := by
  intro k
  induction k using Nat.strong_induction_on with
  | ind k ih =>
    intro hk n hn U
    by_cases hk1 : k = 1
    · subst k
      exact line_sectionVolume_le_sharp U
    have hk₂ : 2 ≤ k := by omega
    have hkn : k ≤ n := by omega
    have hq₂ : 2 ≤ n/k := (Nat.le_div_iff_mul_le (by omega)).mpr hn
    by_cases hq₅ : 5 ≤ n/k
    · exact largeQuotient_bound_of_angular k hk (fun m V => hangular m k V) n hkn hq₅ U
    have hqsmall : n/k=2 ∨ n/k=3 ∨ n/k=4 := by omega
    have hIH : 1 ≤ k-2 → ∀ N : ℕ, 2*(k-2) ≤ N →
        ∀ V : Frame N (k-2), sectionVolume V ≤ sharpValue N (k-2) := by
      intro hh N hN V
      exact ih (k-2) (by omega) hh N hN V
    have hrep := quotient_remainder n k
    have hr := remainder_lt (n := n) hk
    apply smallQuotient_window_bound_of_restricted_induction (n/k) k hqsmall hk₂
      (fun m V => hincidence m k V) (hBM (k-2)) hIH n _ _ U
    · omega
    · nlinarith


/-- Equality for the same complete range, classified by the range-based signed
balanced-block predicate. The inequality is established first; each equality
frame is then reconsidered as an actual ratio maximizer in its integer window. -/
theorem equality_ge_two_mul_of_global_estimates
    (hangular : ∀ (n k : ℕ) (U : Frame n k), gramAngularDefect U ≤ 20*slabDeficit U)
    (hincidence : ∀ (n k : ℕ) (U : Frame n k), RowReplacement U →
      Certificates.framePairIncidence (coalescedFrame U) ≤ slabDeficit U)
    (hBM : ∀ d : ℕ, MidpointBrunnMinkowski d)
    (k : ℕ) (hk : 1 ≤ k) (n : ℕ) (hn : 2*k ≤ n) (U : Frame n k) :
    sectionVolume U = sharpValue n k ↔ IsBalancedSection U := by
  have hbound := upperBound_ge_two_mul_of_global_estimates hangular hincidence hBM
  have hkn : k ≤ n := by omega
  by_cases hk1 : k=1
  · subst k
    exact line_sectionVolume_eq_iff U (by omega)
  have hk₂ : 2 ≤ k := by omega
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
      exact hbound k hk n hn V
    have hwindow : RatioMaximalOnWindow (n/k) U := by
      intro m hmlo hmhi V
      have h2km : 2*k ≤ m :=
        (Nat.mul_le_mul_right k hq₂).trans hmlo
      have hkm : k ≤ m := by omega
      rw [heq, div_self (ne_of_gt (sharpValue_pos hk hkn))]
      exact (div_le_one (sharpValue_pos hk hkm)).mpr (hbound k hk m h2km V)
    rcases lt_or_eq_of_le hlo with hleft | hleft
    · have hwin := reciprocalWindow_of_ratio_maximal (n/k) hq₂ hk U hleft hhi hwindow
      have hrep := rowReplacement_of_ratio_maximal (n/k) hq₂ hk U hleft hhi hwindow
      have hIH : 1 ≤ k-2 → ∀ N : ℕ, 2*(k-2) ≤ N →
          ∀ V : Frame N (k-2), sectionVolume V ≤ sharpValue N (k-2) := by
        intro hh N hN V
        exact hbound (k-2) hh N hN V
      have hdensity := actualClassDensity_of_midpointBM_restricted_induction_quotient
        hk₂ hq₂ U hmax hwin (hBM (k-2)) hIH
      have hinc := hincidence n k U hrep
      rw [Certificates.framePairIncidence_coalesced] at hinc
      exact Certificates.isBalancedSection_of_maximizing_smallQuotient
        hk hkn hqsmall U hmax hwin hdensity hinc
    · have hgoal : ∀ (m : ℕ), m = (n/k)*k → ∀ V : Frame m k,
          IsMaximizingFrame V → gramAngularDefect V ≤ 20*slabDeficit V →
          sectionVolume V = sharpValue m k → IsBalancedSection V := by
        intro m hm
        subst m
        exact fun V hV ha he => divisible_equality_isBalanced_of_angular
          (n/k) k hq₂ hk V hV ha he
      exact hgoal n hleft.symm U hmax (hangular n k U) heq
  · exact sectionVolume_eq_sharp_of_isBalancedSection U

/-- The full maximal-section conclusion for n ≥ 2k, conditional on exactly the
three global estimates displayed here. Balanced attainment is unconditional in
`Geometry.Attainment`; this theorem proves the upper bound and all equality cases. -/
theorem maximalSection_ge_two_mul_of_global_estimates
    (hangular : ∀ (n k : ℕ) (U : Frame n k), gramAngularDefect U ≤ 20*slabDeficit U)
    (hincidence : ∀ (n k : ℕ) (U : Frame n k), RowReplacement U →
      Certificates.framePairIncidence (coalescedFrame U) ≤ slabDeficit U)
    (hBM : ∀ d : ℕ, MidpointBrunnMinkowski d)
    (n k : ℕ) (hk : 1 ≤ k) (hn : 2*k ≤ n) (U : Frame n k) :
    sectionVolume U ≤ sharpValue n k ∧
      (sectionVolume U = sharpValue n k ↔ IsBalancedSection U) :=
  ⟨upperBound_ge_two_mul_of_global_estimates hangular hincidence hBM k hk n hn U,
   equality_ge_two_mul_of_global_estimates hangular hincidence hBM k hk n hn U⟩

#print axioms smallQuotient_window_bound_of_restricted_induction
#print axioms upperBound_ge_two_mul_of_global_estimates
#print axioms equality_ge_two_mul_of_global_estimates
#print axioms maximalSection_ge_two_mul_of_global_estimates
end CubeSections
