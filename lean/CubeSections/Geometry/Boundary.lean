import CubeSections.Semantics

/-!
# Null coordinate boundaries of central slab intersections

A coordinate functional may vanish identically. Its nonzero level set is then
empty. The statements therefore require no nonzero-row hypothesis.
-/

noncomputable section
open Set MeasureTheory
open scoped ENNReal

namespace CubeSections

theorem linear_level_nonzero_null {k : ℕ} (f : E k →ₗ[ℝ] ℝ)
    {c : ℝ} (hc : c ≠ 0) : volume {x | f x = c} = 0 := by
  let s : AffineSubspace ℝ (E k) := ({c} : AffineSubspace ℝ ℝ).comap f.toAffineMap
  have hs : s ≠ ⊤ := by
    intro h
    have hz : (0 : E k) ∈ s := by rw [h]; trivial
    have hz' : (0 : ℝ) = c := by simpa [s] using hz
    exact hc hz'.symm
  exact volume.addHaar_affineSubspace s hs

theorem ae_linear_ne_nonzero {k : ℕ} (f : E k →ₗ[ℝ] ℝ)
    {c : ℝ} (hc : c ≠ 0) : ∀ᵐ x ∂volume, f x ≠ c := by
  simpa only [ae_iff, not_not] using linear_level_nonzero_null f hc

theorem ae_linear_abs_ne_half {k : ℕ} (f : E k →ₗ[ℝ] ℝ) :
    ∀ᵐ x ∂volume, |f x| ≠ (1 : ℝ) / 2 := by
  filter_upwards [ae_linear_ne_nonzero f (by norm_num : (1 : ℝ) / 2 ≠ 0),
    ae_linear_ne_nonzero f (by norm_num : -((1 : ℝ) / 2) ≠ 0)] with x hp hn
  intro h
  rcases (abs_eq (by norm_num : (0 : ℝ) ≤ 1 / 2)).mp h with h | h
  · exact hp h
  · exact hn h

theorem ae_raw_coordinates_ne_boundary {n k : ℕ} (R : E k →ₗ[ℝ] E n) :
    ∀ᵐ x ∂volume, ∀ i, |(R x) i| ≠ (1 : ℝ) / 2 := by
  rw [ae_all_iff]
  intro i
  let f : E k →ₗ[ℝ] ℝ :=
    { toFun := fun x => (R x) i
      map_add' := by intros; simp
      map_smul' := by intros; simp }
  exact ae_linear_abs_ne_half f

theorem ae_frame_coordinates_ne_boundary {n k : ℕ} (U : Frame n k) :
    ∀ᵐ x ∂volume, ∀ i, |(U x) i| ≠ (1 : ℝ) / 2 :=
  ae_raw_coordinates_ne_boundary U.toLinearMap

theorem frame_closed_open_slabs_ae {n k : ℕ} (U : Frame n k) :
    (U ⁻¹' cube n) =ᵐ[volume] {x | ∀ i, |(U x) i| < (1 : ℝ) / 2} := by
  filter_upwards [ae_frame_coordinates_ne_boundary U] with x hx
  change (∀ i, |(U x) i| ≤ (1 : ℝ) / 2) ↔ (∀ i, |(U x) i| < (1 : ℝ) / 2)
  exact forall_congr' fun i => ⟨fun h => lt_iff_le_and_ne.mpr ⟨h, hx i⟩, le_of_lt⟩

end CubeSections
