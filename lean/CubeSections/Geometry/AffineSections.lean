import CubeSections.Geometry.ZeroDimension
import Mathlib.Analysis.Convex.Basic

/-!
# Affine cube sections and elementary convex geometry

Offsets are arbitrary ambient vectors; no choice of an orthogonal complement is
needed. Empty and lower-dimensional affine sections are allowed. This file does
not assume, or claim to prove, the Brunn--Minkowski volume inequality.
-/

noncomputable section
open Set MeasureTheory Classical
open scoped ENNReal

namespace CubeSections

def affineSlab {n k : ℕ} (U : Frame n k) (y : E n) : Set (E k) :=
  {x | y + U x ∈ cube n}

def affineMass {n k : ℕ} (U : Frame n k) (y : E n) : ℝ≥0∞ := volume (affineSlab U y)

def affineVolume {n k : ℕ} (U : Frame n k) (y : E n) : ℝ := (affineMass U y).toReal

@[simp] theorem affineSlab_zero {n k : ℕ} (U : Frame n k) :
    affineSlab U 0 = U ⁻¹' cube n := by ext x; simp [affineSlab]

@[simp] theorem affineMass_zero {n k : ℕ} (U : Frame n k) : affineMass U 0 = sectionMass U := by
  simp [affineMass, sectionMass]

@[simp] theorem affineVolume_zero {n k : ℕ} (U : Frame n k) :
    affineVolume U 0 = sectionVolume U := by simp [affineVolume, sectionVolume]

theorem affineSlab_compact {n k : ℕ} (U : Frame n k) (y : E n) : IsCompact (affineSlab U y) :=
  ((isometry_add_left y).comp U.isometry).isClosedEmbedding.isCompact_preimage (cube_compact n)

theorem affineSlab_measurableSet {n k : ℕ} (U : Frame n k) (y : E n) :
    MeasurableSet (affineSlab U y) := (affineSlab_compact U y).isClosed.measurableSet

theorem affineMass_ne_top {n k : ℕ} (U : Frame n k) (y : E n) : affineMass U y ≠ ∞ :=
  (affineSlab_compact U y).measure_ne_top

theorem affineVolume_nonneg {n k : ℕ} (U : Frame n k) (y : E n) : 0 ≤ affineVolume U y :=
  ENNReal.toReal_nonneg

theorem cube_convex (n : ℕ) : Convex ℝ (cube n) := by
  intro x hx z hz a b ha hb hab i
  change |a * x i + b * z i| ≤ (1 : ℝ) / 2
  calc
    |a * x i + b * z i| ≤ |a * x i| + |b * z i| := abs_add_le _ _
    _ = a * |x i| + b * |z i| := by rw [abs_mul, abs_mul, abs_of_nonneg ha, abs_of_nonneg hb]
    _ ≤ a * (1 / 2) + b * (1 / 2) := add_le_add
      (mul_le_mul_of_nonneg_left (hx i) ha) (mul_le_mul_of_nonneg_left (hz i) hb)
    _ = (1 : ℝ) / 2 := by rw [← add_mul, hab, one_mul]

theorem affineSlab_convex {n k : ℕ} (U : Frame n k) (y : E n) :
    Convex ℝ (affineSlab U y) :=
  ((cube_convex n).translate_preimage_right y).linear_preimage U.toLinearMap

@[simp] theorem cube_neg_iff {n : ℕ} (x : E n) : -x ∈ cube n ↔ x ∈ cube n := by
  simp [cube]

theorem affineSlab_neg {n k : ℕ} (U : Frame n k) (y : E n) :
    affineSlab U (-y) = Neg.neg ⁻¹' affineSlab U y := by
  ext x
  change (-y + U x ∈ cube n) ↔ (y + U (-x) ∈ cube n)
  have h : y + U (-x) = -(-y + U x) := by simp [add_comm]
  rw [h, cube_neg_iff]

theorem affineMass_neg {n k : ℕ} (U : Frame n k) (y : E n) :
    affineMass U (-y) = affineMass U y := by
  unfold affineMass
  rw [affineSlab_neg]
  exact volume.measure_preimage_neg _

theorem affineVolume_neg {n k : ℕ} (U : Frame n k) (y : E n) :
    affineVolume U (-y) = affineVolume U y := by rw [affineVolume, affineMass_neg]; rfl

theorem affineSlab_offset_add_frame {n k : ℕ} (U : Frame n k) (y : E n) (t : E k) :
    affineSlab U (y + U t) = (fun x => t + x) ⁻¹' affineSlab U y := by
  ext x
  simp [affineSlab, map_add, add_assoc]

theorem affineMass_offset_add_frame {n k : ℕ} (U : Frame n k) (y : E n) (t : E k) :
    affineMass U (y + U t) = affineMass U y := by
  unfold affineMass
  rw [affineSlab_offset_add_frame]
  exact measure_preimage_add volume t _

theorem affineVolume_offset_add_frame {n k : ℕ} (U : Frame n k) (y : E n) (t : E k) :
    affineVolume U (y + U t) = affineVolume U y := by
  rw [affineVolume, affineMass_offset_add_frame]
  rfl

theorem midpoint_opposite_affineSlabs_mem {n k : ℕ} (U : Frame n k) (y : E n)
    {x z : E k} (hx : x ∈ affineSlab U y) (hz : z ∈ affineSlab U (-y)) :
    (1 / 2 : ℝ) • (x + z) ∈ U ⁻¹' cube n := by
  have h : (1 / 2 : ℝ) • (y + U x) + (1 / 2 : ℝ) • (-y + U z) ∈ cube n :=
    (cube_convex n) hx hz (by norm_num) (by norm_num) (by norm_num)
  change U ((1 / 2 : ℝ) • (x + z)) ∈ cube n
  convert h using 1
  ext i
  simp only [map_smul, map_add, PiLp.add_apply, PiLp.smul_apply, PiLp.neg_apply,
    smul_eq_mul]
  ring

theorem affineSlab_zeroDimension {n : ℕ} (U : Frame n 0) (y : E n) :
    affineSlab U y = if y ∈ cube n then Set.univ else ∅ := by
  ext x
  have hx : x = 0 := Subsingleton.elim _ _
  subst x
  by_cases hy : y ∈ cube n <;> simp [affineSlab, hy]

theorem affineMass_zeroDimension {n : ℕ} (U : Frame n 0) (y : E n) :
    affineMass U y = if y ∈ cube n then 1 else 0 := by
  have hv : volume (Set.univ : Set (E 0)) = 1 := by
    simpa only [sectionMass, zeroDimension_preimage] using zeroDimension_sectionMass U
  unfold affineMass
  rw [affineSlab_zeroDimension]
  split_ifs <;> simp [hv]

theorem affineVolume_zeroDimension {n : ℕ} (U : Frame n 0) (y : E n) :
    affineVolume U y = if y ∈ cube n then 1 else 0 := by
  unfold affineVolume
  rw [affineMass_zeroDimension]
  split_ifs <;> simp

end CubeSections
