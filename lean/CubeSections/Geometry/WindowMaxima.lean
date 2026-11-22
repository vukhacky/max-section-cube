import CubeSections.Geometry.Continuity
import Mathlib.Data.Finset.Max

/-! Existence of a volume-ratio maximizer across a finite reciprocal window. -/
noncomputable section
open Set
open scoped Topology
namespace CubeSections

def windowDimension (q k : ℕ) (t : Fin (k + 1)) : ℕ := q * k + t.val
abbrev WindowFrame (q k : ℕ) := Σ t : Fin (k + 1), Frame (windowDimension q k t) k

def windowRatio {q k : ℕ} (X : WindowFrame q k) : ℝ :=
  sectionVolume X.2 / sharpValue (windowDimension q k X.1) k

theorem windowDimension_ge {q k : ℕ} (hq : 1 ≤ q) (t : Fin (k + 1)) :
    k ≤ windowDimension q k t := by
  have h : k ≤ q * k := by simpa using Nat.mul_le_mul_right k hq
  exact h.trans (Nat.le_add_right _ _)

theorem continuous_windowRatio (q k : ℕ) : Continuous (windowRatio : WindowFrame q k → ℝ) := by
  rw [continuous_sigma_iff]
  intro t
  change Continuous (fun U : Frame (windowDimension q k t) k =>
    sectionVolume U / sharpValue (windowDimension q k t) k)
  exact (continuous_sectionVolume (windowDimension q k t) k).div_const
    (sharpValue (windowDimension q k t) k)

def IsWindowMaximizingFrame {q k : ℕ} (t : Fin (k + 1))
    (U : Frame (windowDimension q k t) k) : Prop :=
  ∀ (s : Fin (k + 1)) (V : Frame (windowDimension q k s) k),
    sectionVolume V / sharpValue (windowDimension q k s) k ≤
      sectionVolume U / sharpValue (windowDimension q k t) k

theorem exists_windowMaximizingFrame {q k : ℕ} (hq : 1 ≤ q) (hk : 1 ≤ k) :
    ∃ (t : Fin (k + 1)) (U : Frame (windowDimension q k t) k),
      IsWindowMaximizingFrame (q := q) (k := k) t U := by
  classical
  have hex : ∀ t : Fin (k + 1), ∃ U : Frame (windowDimension q k t) k,
      IsMaximizingFrame U := fun t =>
    exists_maximizingFrame hk (windowDimension_ge hq t)
  choose U hU using hex
  obtain ⟨t, _, ht⟩ := Finset.exists_max_image Finset.univ
    (fun s : Fin (k + 1) => sectionVolume (U s) / sharpValue (windowDimension q k s) k)
    Finset.univ_nonempty
  refine ⟨t, U t, ?_⟩
  intro s V
  have hW := sharpValue_pos hk (windowDimension_ge hq s)
  exact ((div_le_div_iff_of_pos_right hW).mpr (hU s V)).trans
    (ht s (Finset.mem_univ s))

theorem windowMaximizing_isMaximizing {q k : ℕ} (hq : 1 ≤ q) (hk : 1 ≤ k)
    (t : Fin (k + 1)) (U : Frame (windowDimension q k t) k)
    (hU : IsWindowMaximizingFrame (q := q) (k := k) t U) :
    IsMaximizingFrame U := by
  intro V
  have hW := sharpValue_pos hk (windowDimension_ge hq t)
  exact (div_le_div_iff_of_pos_right hW).mp (hU t V)

theorem one_le_windowRatio_of_maximizing {q k : ℕ} (hq : 1 ≤ q) (hk : 1 ≤ k)
    (t : Fin (k + 1)) (U : Frame (windowDimension q k t) k)
    (hU : IsWindowMaximizingFrame (q := q) (k := k) t U) :
    1 ≤ sectionVolume U / sharpValue (windowDimension q k t) k := by
  have hW := sharpValue_pos hk (windowDimension_ge hq t)
  have h := hU t (balancedFrame hk (windowDimension_ge hq t))
  rw [balancedFrame_volume, div_self (ne_of_gt hW)] at h
  exact h

theorem windowMaximizing_compare {q k : ℕ} (t : Fin (k + 1))
    (U : Frame (windowDimension q k t) k)
    (hU : IsWindowMaximizingFrame (q := q) (k := k) t U)
    (m : ℕ) (hlo : q * k ≤ m) (hhi : m ≤ (q + 1) * k) (V : Frame m k) :
    sectionVolume V / sharpValue m k ≤
      sectionVolume U / sharpValue (windowDimension q k t) k := by
  have hbound : m - q * k < k + 1 := by
    rw [Nat.add_mul, Nat.one_mul] at hhi
    omega
  let s : Fin (k + 1) := ⟨m - q * k, hbound⟩
  have hs : windowDimension q k s = m := Nat.add_sub_of_le hlo
  have h := hU s
  rw [hs] at h
  exact h V
end CubeSections
