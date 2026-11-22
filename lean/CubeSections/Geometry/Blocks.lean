import CubeSections.Semantics
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic.Ring

/-!
# Signed coordinate-block frames

For every surjective signed block assignment we construct its normalized
linear isometric embedding, with no balance assumption. These results are
independent of the conjectural maximal-section upper bound.
-/

noncomputable section
open Set MeasureTheory
open scoped BigOperators ENNReal

namespace CubeSections
namespace BlockData

variable {n k : ℕ} (d : BlockData n k)

theorem blockSize_pos (j : Fin k) : 0 < d.blockSize j := by
  obtain ⟨i, hi⟩ := d.onto j
  exact Finset.card_pos.mpr ⟨i, by simp [hi]⟩

theorem blockSize_ne_zero (j : Fin k) : d.blockSize j ≠ 0 :=
  Nat.ne_of_gt (d.blockSize_pos j)

theorem sum_blockSize : ∑ j : Fin k, d.blockSize j = n := by
  simpa [blockSize] using
    (Finset.sum_card_fiberwise_eq_card_filter
      (Finset.univ : Finset (Fin n)) (Finset.univ : Finset (Fin k)) d.block)

/-- A sum whose summand depends only on the block can be grouped by block size. -/
theorem sum_block (f : Fin k → ℝ) :
    ∑ i : Fin n, f (d.block i) = ∑ j : Fin k, (d.blockSize j : ℝ) * f j := by
  simpa [blockSize, nsmul_eq_mul] using
    (Finset.sum_fiberwise' (Finset.univ : Finset (Fin n)) d.block f).symm

theorem sqrt_blockSize_pos (j : Fin k) : 0 < Real.sqrt (d.blockSize j) := by
  exact Real.sqrt_pos.mpr (Nat.cast_pos.mpr (d.blockSize_pos j))

theorem sqrt_blockSize_ne_zero (j : Fin k) : Real.sqrt (d.blockSize j) ≠ 0 :=
  ne_of_gt (d.sqrt_blockSize_pos j)

@[simp] theorem abs_sign (i : Fin n) : |d.sign i| = 1 := by
  simp only [sign]
  split <;> norm_num

theorem sign_ne_zero (i : Fin n) : d.sign i ≠ 0 := by
  have h := d.abs_sign i
  intro hz
  simp [hz] at h

/-- Repeat a coordinate on its block with its sign and L2 normalization. -/
def linearMap : E k →ₗ[ℝ] E n where
  toFun x := WithLp.toLp 2 (fun i =>
    d.sign i * x (d.block i) / Real.sqrt (d.blockSize (d.block i)))
  map_add' x y := by
    ext i
    simp only [PiLp.add_apply]
    ring
  map_smul' a x := by
    ext i
    simp only [PiLp.smul_apply, smul_eq_mul, RingHom.id_apply]
    ring

@[simp] theorem linearMap_apply (x : E k) (i : Fin n) :
    d.linearMap x i = d.sign i * x (d.block i) / Real.sqrt (d.blockSize (d.block i)) := rfl

theorem linearMap_norm (x : E k) : ‖d.linearMap x‖ = ‖x‖ := by
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  rw [EuclideanSpace.real_norm_sq_eq, EuclideanSpace.real_norm_sq_eq]
  simp_rw [d.linearMap_apply, div_pow, mul_pow, blockSign_sq, one_mul,
    Real.sq_sqrt (Nat.cast_nonneg _)]
  rw [d.sum_block (fun j => x j ^ 2 / (d.blockSize j : ℝ))]
  apply Finset.sum_congr rfl
  intro j hj
  exact mul_div_cancel₀ _ (Nat.cast_ne_zero.mpr (d.blockSize_ne_zero j))

/-- The normalized signed block embedding. -/
def frame : Frame n k where
  toLinearMap := d.linearMap
  norm_map' := d.linearMap_norm

@[simp] theorem frame_apply (x : E k) (i : Fin n) :
    d.frame x i = d.sign i * x (d.block i) / Real.sqrt (d.blockSize (d.block i)) := rfl

theorem range_frame : Set.range d.frame = d.plane := by
  ext z
  constructor
  · rintro ⟨x, rfl⟩
    refine ⟨fun j => x j / Real.sqrt (d.blockSize j), ?_⟩
    intro i
    rw [d.frame_apply, mul_div_assoc]
  · rintro ⟨t, ht⟩
    refine ⟨WithLp.toLp 2 (fun j => Real.sqrt (d.blockSize j) * t j), ?_⟩
    ext i
    rw [d.frame_apply, ht i]
    change d.sign i * (Real.sqrt (d.blockSize (d.block i)) * t (d.block i)) /
      Real.sqrt (d.blockSize (d.block i)) = d.sign i * t (d.block i)
    field_simp [d.sqrt_blockSize_ne_zero (d.block i)]

theorem isBalancedSection_frame (h : d.IsBalanced) : IsBalancedSection d.frame :=
  ⟨d, h, d.range_frame⟩

end BlockData
end CubeSections
