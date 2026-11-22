import CubeSections.Geometry.WindowMaxima
import CubeSections.Integer.ReciprocalWindow
import CubeSections.Analysis.SlabVolumeBound

/-! Unconditional endpoint normalization and the full reciprocal window. -/
noncomputable section
namespace CubeSections

theorem windowMaximizer_endpoint_eq {q k : ℕ} (hq : 1 ≤ q) (hk : 1 ≤ k)
    (t : Fin (k + 1)) (U : Frame (windowDimension q k t) k)
    (hU : IsWindowMaximizingFrame (q := q) (k := k) t U)
    (hend : t.val = 0 ∨ t.val = k) :
    sectionVolume U = sharpValue (windowDimension q k t) k := by
  have hlo : sharpValue (windowDimension q k t) k ≤ sectionVolume U :=
    (one_le_div (sharpValue_pos hk (windowDimension_ge hq t))).1
      (one_le_windowRatio_of_maximizing hq hk t U hU)
  apply le_antisymm _ hlo
  rcases hend with ht | ht
  · have hd : windowDimension q k t = q * k := by simp [windowDimension, ht]
    have hb : ∀ V : Frame (windowDimension q k t) k,
        sectionVolume V ≤ sharpValue (windowDimension q k t) k := by
      rw [hd]
      exact sectionVolume_le_sharp_divisible q k hq hk
    exact hb U
  · have hd : windowDimension q k t = (q + 1) * k := by simp [windowDimension, ht]; ring
    have hb : ∀ V : Frame (windowDimension q k t) k,
        sectionVolume V ≤ sharpValue (windowDimension q k t) k := by
      rw [hd]
      exact sectionVolume_le_sharp_divisible (q + 1) k (by omega) hk
    exact hb U

theorem windowMaximizer_endpoint_ratio {q k : ℕ} (hq : 1 ≤ q) (hk : 1 ≤ k)
    (t : Fin (k + 1)) (U : Frame (windowDimension q k t) k)
    (hU : IsWindowMaximizingFrame (q := q) (k := k) t U)
    (hend : t.val = 0 ∨ t.val = k) :
    sectionVolume U / sharpValue (windowDimension q k t) k = 1 := by
  rw [windowMaximizer_endpoint_eq hq hk t U hU hend,
    div_self (ne_of_gt (sharpValue_pos hk (windowDimension_ge hq t)))]

theorem reciprocalWindow_of_windowMaximizer {q k : ℕ} (hq : 2 ≤ q) (hk : 1 ≤ k)
    (t : Fin (k + 1)) (U : Frame (windowDimension q k t) k)
    (hU : IsWindowMaximizingFrame (q := q) (k := k) t U) :
    ReciprocalWindow q U := by
  have hq1 : 1 ≤ q := by omega
  have hqpos : (0 : ℝ) < q := by exact_mod_cast (show 0 < q by omega)
  have hrecip : 1 / ((q : ℝ) + 1) ≤ 1 / (q : ℝ) :=
    one_div_le_one_div_of_le hqpos (by linarith)
  by_cases ht0 : t.val = 0
  · have hd : windowDimension q k t = q * k := by simp [windowDimension, ht0]
    have hu : ∀ V : Frame (windowDimension q k t) k,
        sectionVolume V = sharpValue (windowDimension q k t) k →
          ∀ i, leverage V i = 1 / (q : ℝ) := by
      rw [hd]
      intro V heq
      exact leverage_uniform_of_divisible_equality q k hq1 hk V (sectionVolume_le_slabBound V) heq
    intro i
    rw [hu U (windowMaximizer_endpoint_eq hq1 hk t U hU (Or.inl ht0)) i]
    exact ⟨hrecip, le_rfl⟩
  · by_cases htk : t.val = k
    · have hd : windowDimension q k t = (q + 1) * k := by simp [windowDimension, htk]; ring
      have hu : ∀ V : Frame (windowDimension q k t) k,
          sectionVolume V = sharpValue (windowDimension q k t) k →
            ∀ i, leverage V i = 1 / ((q : ℝ) + 1) := by
        rw [hd]
        intro V heq
        simpa only [Nat.cast_add, Nat.cast_one] using
          leverage_uniform_of_divisible_equality (q + 1) k (by omega) hk V
            (sectionVolume_le_slabBound V) heq
      intro i
      rw [hu U (windowMaximizer_endpoint_eq hq1 hk t U hU (Or.inr htk)) i]
      exact ⟨le_rfl, hrecip⟩
    · have hlo : q * k < windowDimension q k t := by dsimp [windowDimension]; omega
      have hhi : windowDimension q k t < (q + 1) * k := by
        dsimp [windowDimension]
        have ht := t.isLt
        have htklt : t.val < k := by omega
        nlinarith
      exact reciprocalWindow_of_ratio_maximal q hq hk U hlo hhi
        (windowMaximizing_compare t U hU)

theorem exists_windowMaximizer_reciprocal {q k : ℕ} (hq : 2 ≤ q) (hk : 1 ≤ k) :
    ∃ (t : Fin (k + 1)) (U : Frame (windowDimension q k t) k),
      IsWindowMaximizingFrame (q := q) (k := k) t U ∧ ReciprocalWindow q U := by
  obtain ⟨t, U, hU⟩ := exists_windowMaximizingFrame (show 1 ≤ q by omega) hk
  exact ⟨t, U, hU, reciprocalWindow_of_windowMaximizer hq hk t U hU⟩

end CubeSections
