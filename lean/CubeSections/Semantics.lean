import Mathlib.Geometry.Euclidean.Volume.Measure
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Measure.OpenPos
import Mathlib.Tactic.NormNum

/-!
# Central cube sections and the maximal-volume statements

The definitions specify intrinsic volume, the balanced target, and the signed
block-range equality condition. The four final theorems are in `CubeSections.Main`.
-/

noncomputable section
open Set MeasureTheory
open scoped ENNReal

namespace CubeSections

abbrev E (n : ℕ) := EuclideanSpace ℝ (Fin n)

def cube (n : ℕ) : Set (E n) := {x | ∀ i, |x i| ≤ (1 : ℝ) / 2}

abbrev Frame (n k : ℕ) := E k →ₗᵢ[ℝ] E n

def sectionMass {n k : ℕ} (U : Frame n k) : ℝ≥0∞ := volume (U ⁻¹' cube n)

def sectionVolume {n k : ℕ} (U : Frame n k) : ℝ := (sectionMass U).toReal

/-- The natural-number expression is coerced to the reals before taking a square root. -/
def sharpValue (n k : ℕ) : ℝ :=
  Real.sqrt (((n / k) ^ (k - n % k) * (n / k + 1) ^ (n % k) : ℕ) : ℝ)

structure BlockData (n k : ℕ) where
  block : Fin n → Fin k
  onto : Function.Surjective block
  negative : Fin n → Bool

def BlockData.sign {n k : ℕ} (d : BlockData n k) (i : Fin n) : ℝ :=
  if d.negative i then -1 else 1

def BlockData.blockSize {n k : ℕ} (d : BlockData n k) (j : Fin k) : ℕ :=
  (Finset.univ.filter (fun i => d.block i = j)).card

def BlockData.IsBalanced {n k : ℕ} (d : BlockData n k) : Prop :=
  ∀ j, d.blockSize j = n / k ∨ d.blockSize j = n / k + 1

/-- A signed coordinate-block plane. The coordinates within a block agree up to signs. -/
def BlockData.plane {n k : ℕ} (d : BlockData n k) : Set (E n) :=
  {x | ∃ t : Fin k → ℝ, ∀ i, x i = d.sign i * t (d.block i)}

def IsBalancedSection {n k : ℕ} (U : Frame n k) : Prop :=
  ∃ d : BlockData n k, d.IsBalanced ∧ Set.range U = d.plane

theorem blockSign_sq {n k : ℕ} (d : BlockData n k) (i : Fin n) : d.sign i ^ 2 = 1 := by
  simp only [BlockData.sign]
  split <;> norm_num

theorem sharpValue_nonneg (n k : ℕ) : 0 ≤ sharpValue n k := Real.sqrt_nonneg _

/-- Intrinsic section mass agrees with normalized k-dimensional Hausdorff measure. -/
theorem sectionMass_eq_hausdorff {n k : ℕ} (U : Frame n k) :
    sectionMass U =
      (Measure.euclideanHausdorffMeasure k) (cube n ∩ Set.range U) := by
  unfold sectionMass
  rw [← EuclideanSpace.euclideanHausdorffMeasure_eq_volume k]
  exact U.isometry.euclideanHausdorffMeasure_preimage (cube n)

theorem cube_compact (n : ℕ) : IsCompact (cube n) := by
  have heq : cube n = (PiLp.homeomorph 2 (fun _ : Fin n => ℝ)) ⁻¹'
      Set.Icc (fun _ => -((1 : ℝ) / 2)) (fun _ => (1 : ℝ) / 2) := by
    ext x
    simp only [cube, Set.mem_ofPred_eq, Set.mem_preimage, Set.mem_Icc, Pi.le_def]
    simp only [abs_le]
    constructor
    · intro h
      exact ⟨fun i => (h i).1, fun i => (h i).2⟩
    · rintro ⟨h₁, h₂⟩ i
      exact ⟨h₁ i, h₂ i⟩
  rw [heq]
  exact (PiLp.homeomorph 2 (fun _ : Fin n => ℝ)).isCompact_preimage.mpr isCompact_Icc

theorem sectionMass_ne_top {n k : ℕ} (U : Frame n k) : sectionMass U ≠ ∞ := by
  exact (U.isometry.isClosedEmbedding.isCompact_preimage (cube_compact n)).measure_ne_top

theorem sectionMass_pos {n k : ℕ} (U : Frame n k) : 0 < sectionMass U := by
  have hball : Metric.ball (0 : E k) ((1 : ℝ) / 2) ⊆ U ⁻¹' cube n := by
    intro x hx
    change ∀ i, |(U x) i| ≤ (1 : ℝ) / 2
    intro i
    have hxnorm : ‖x‖ < (1 : ℝ) / 2 := by simpa using hx
    calc
      |(U x) i| = ‖(U x) i‖ := (Real.norm_eq_abs _).symm
      _ ≤ ‖U x‖ := PiLp.norm_apply_le _ _
      _ = ‖x‖ := U.norm_map x
      _ ≤ (1 : ℝ) / 2 := hxnorm.le
  exact (Metric.measure_ball_pos volume (0 : E k) (by norm_num : (0 : ℝ) < 1 / 2)).trans_le
    (measure_mono hball)

theorem sectionVolume_pos {n k : ℕ} (U : Frame n k) : 0 < sectionVolume U := by
  exact ENNReal.toReal_pos (ne_of_gt (sectionMass_pos U)) (sectionMass_ne_top U)

/-- The upper-bound statement for every isometric frame with `1 ≤ k ≤ n`. -/
def UpperBoundStatement : Prop :=
  ∀ (n k : ℕ), 1 ≤ k → k ≤ n → ∀ U : Frame n k,
    sectionVolume U ≤ sharpValue n k

/-- Equality classification in terms of the represented subspace. -/
def EqualityStatement : Prop :=
  ∀ (n k : ℕ), 1 ≤ k → k ≤ n → ∀ U : Frame n k,
    (sectionVolume U = sharpValue n k ↔ IsBalancedSection U)

/-- Existence of a signed balanced section attaining the target in every admissible dimension. -/
def AttainmentStatement : Prop :=
  ∀ (n k : ℕ), 1 ≤ k → k ≤ n → ∃ U : Frame n k,
    IsBalancedSection U ∧ sectionVolume U = sharpValue n k

def MainStatement : Prop := UpperBoundStatement ∧ EqualityStatement ∧ AttainmentStatement

end CubeSections
