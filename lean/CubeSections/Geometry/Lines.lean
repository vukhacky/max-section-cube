import CubeSections.Geometry.BlockVolume
import CubeSections.Geometry.Invariance
import Mathlib.Tactic.Linarith

/-!
# Central line sections

Every line section has the exact length `1 / max_i |v_i|` for its unit direction.
The supremum norm below is intentionally on the coordinate function `v.ofLp`;
the ambient geometric space continues to carry its Euclidean norm.
-/

noncomputable section
open Set MeasureTheory
open scoped BigOperators ENNReal

namespace CubeSections

def lineUnit : E 1 := WithLp.toLp 2 (fun _ => (1 : ℝ))

@[simp] theorem lineUnit_apply (i : Fin 1) : lineUnit i = 1 := rfl

@[simp] theorem norm_lineUnit : ‖lineUnit‖ = 1 := by
  rw [EuclideanSpace.norm_eq]
  simp [lineUnit]

def lineVector {n : ℕ} (U : Frame n 1) : E n := U lineUnit

def lineMax {n : ℕ} (U : Frame n 1) : ℝ := ‖(lineVector U).ofLp‖

@[simp] theorem lineVector_norm {n : ℕ} (U : Frame n 1) : ‖lineVector U‖ = 1 := by
  rw [lineVector, U.norm_map, norm_lineUnit]

theorem lineVector_ne_zero {n : ℕ} (U : Frame n 1) : lineVector U ≠ 0 := by
  intro h
  have hn := lineVector_norm U
  rw [h, norm_zero] at hn
  norm_num at hn

theorem lineMax_pos {n : ℕ} (U : Frame n 1) : 0 < lineMax U := by
  exact norm_pos_iff.mpr (by simpa using lineVector_ne_zero U)

theorem lineMap_apply {n : ℕ} (U : Frame n 1) (x : E 1) :
    U x = x 0 • lineVector U := by
  have hx : x = x 0 • lineUnit := by
    ext i
    simp [Subsingleton.elim i (0 : Fin 1)]
  calc
    U x = U (x 0 • lineUnit) := congrArg U hx
    _ = x 0 • lineVector U := by
      simpa only [lineVector] using (map_smul U (x 0) lineUnit)

theorem cube_iff_pi_norm {n : ℕ} (x : E n) :
    x ∈ cube n ↔ ‖x.ofLp‖ ≤ (1 : ℝ) / 2 := by
  change (∀ i, |x i| ≤ (1 : ℝ) / 2) ↔ ‖x.ofLp‖ ≤ (1 : ℝ) / 2
  simpa only [Real.norm_eq_abs] using
    (pi_norm_le_iff_of_nonneg (x := x.ofLp) (by norm_num : (0 : ℝ) ≤ 1 / 2)).symm

def lineRadius {n : ℕ} (U : Frame n 1) : ℝ := (1 / 2 : ℝ) / lineMax U

theorem lineRadius_pos {n : ℕ} (U : Frame n 1) : 0 < lineRadius U :=
  div_pos (by norm_num) (lineMax_pos U)

theorem line_mem_cube_iff {n : ℕ} (U : Frame n 1) (x : E 1) :
    U x ∈ cube n ↔ |x 0| ≤ lineRadius U := by
  rw [cube_iff_pi_norm, lineMap_apply]
  change ‖x 0 • (lineVector U).ofLp‖ ≤ (1 : ℝ) / 2 ↔ _
  rw [norm_smul, Real.norm_eq_abs]
  exact (le_div_iff₀ (lineMax_pos U)).symm

theorem line_preimage_cube {n : ℕ} (U : Frame n 1) :
    U ⁻¹' cube n = (WithLp.ofLp : E 1 → Fin 1 → ℝ) ⁻¹'
      Set.Icc (fun _ => -lineRadius U) (fun _ => lineRadius U) := by
  ext x
  rw [Set.mem_preimage, line_mem_cube_iff]
  simp only [Set.mem_preimage, Set.mem_Icc, Pi.le_def, abs_le]
  constructor
  · rintro ⟨hl, hr⟩
    exact ⟨fun j => by simpa [Subsingleton.elim j (0 : Fin 1)] using hl,
      fun j => by simpa [Subsingleton.elim j (0 : Fin 1)] using hr⟩
  · rintro ⟨hl, hr⟩
    exact ⟨hl 0, hr 0⟩

theorem line_sectionMass {n : ℕ} (U : Frame n 1) :
    sectionMass U = ENNReal.ofReal (1 / lineMax U) := by
  unfold sectionMass
  rw [line_preimage_cube]
  rw [(PiLp.volume_preserving_ofLp (Fin 1)).measure_preimage
    measurableSet_Icc.nullMeasurableSet]
  rw [Real.volume_Icc_pi]
  simp only [Fin.prod_univ_one]
  congr 1
  unfold lineRadius
  ring

theorem line_sectionVolume {n : ℕ} (U : Frame n 1) :
    sectionVolume U = 1 / lineMax U := by
  unfold sectionVolume
  rw [line_sectionMass, ENNReal.toReal_ofReal (one_div_pos.mpr (lineMax_pos U)).le]

theorem lineVector_sq_sum {n : ℕ} (U : Frame n 1) :
    ∑ i : Fin n, lineVector U i ^ 2 = 1 := by
  rw [← EuclideanSpace.real_norm_sq_eq, lineVector_norm]
  norm_num

theorem lineVector_abs_le_max {n : ℕ} (U : Frame n 1) (i : Fin n) :
    |lineVector U i| ≤ lineMax U := by
  simpa only [Real.norm_eq_abs, lineMax] using norm_le_pi_norm (lineVector U).ofLp i

theorem lineVector_sq_le_max_sq {n : ℕ} (U : Frame n 1) (i : Fin n) :
    lineVector U i ^ 2 ≤ lineMax U ^ 2 := by
  simpa only [sq_abs] using
    (sq_le_sq₀ (abs_nonneg _) (lineMax_pos U).le).mpr (lineVector_abs_le_max U i)

theorem one_le_n_mul_lineMax_sq {n : ℕ} (U : Frame n 1) :
    1 ≤ (n : ℝ) * lineMax U ^ 2 := by
  calc
    1 = ∑ i : Fin n, lineVector U i ^ 2 := (lineVector_sq_sum U).symm
    _ ≤ ∑ _i : Fin n, lineMax U ^ 2 :=
      Finset.sum_le_sum (fun i hi => lineVector_sq_le_max_sq U i)
    _ = (n : ℝ) * lineMax U ^ 2 := by simp

theorem line_sectionVolume_le_sqrt {n : ℕ} (U : Frame n 1) :
    sectionVolume U ≤ Real.sqrt n := by
  rw [line_sectionVolume, div_le_iff₀ (lineMax_pos U)]
  apply (one_le_sq_iff₀ (mul_nonneg (Real.sqrt_nonneg _) (lineMax_pos U).le)).mp
  rw [mul_pow, Real.sq_sqrt (Nat.cast_nonneg _)]
  exact one_le_n_mul_lineMax_sq U

theorem line_sectionVolume_le_sharp {n : ℕ} (U : Frame n 1) :
    sectionVolume U ≤ sharpValue n 1 := by
  simpa [sharpValue, Nat.mod_one] using line_sectionVolume_le_sqrt U

theorem line_max_eq_inv_sqrt_of_eq {n : ℕ} (U : Frame n 1)
    (h : sectionVolume U = Real.sqrt n) : lineMax U = 1 / Real.sqrt n := by
  have hsqrt : 0 < Real.sqrt n := h ▸ sectionVolume_pos U
  have hprod : 1 = Real.sqrt n * lineMax U := by
    exact (div_eq_iff (ne_of_gt (lineMax_pos U))).mp ((line_sectionVolume U).symm.trans h)
  apply (eq_div_iff (ne_of_gt hsqrt)).mpr
  simpa only [mul_comm] using hprod.symm

theorem line_abs_eq_max_of_eq {n : ℕ} (U : Frame n 1)
    (h : sectionVolume U = Real.sqrt n) (i : Fin n) :
    |lineVector U i| = lineMax U := by
  have hprod : 1 = Real.sqrt n * lineMax U :=
    (div_eq_iff (ne_of_gt (lineMax_pos U))).mp ((line_sectionVolume U).symm.trans h)
  have hnM : (n : ℝ) * lineMax U ^ 2 = 1 := by
    calc
      (n : ℝ) * lineMax U ^ 2 = (Real.sqrt n * lineMax U) ^ 2 := by
        rw [mul_pow, Real.sq_sqrt (Nat.cast_nonneg _)]
      _ = 1 := by rw [← hprod]; norm_num
  have hsum : ∑ j : Fin n, lineVector U j ^ 2 = ∑ _j : Fin n, lineMax U ^ 2 := by
    rw [lineVector_sq_sum]
    simpa using hnM.symm
  have heq : lineVector U i ^ 2 = lineMax U ^ 2 :=
    (Finset.sum_eq_sum_iff_of_le (fun j hj => lineVector_sq_le_max_sq U j)).mp
      hsum i (Finset.mem_univ i)
  exact (sq_eq_sq₀ (abs_nonneg _) (lineMax_pos U).le).mp (by simpa only [sq_abs] using heq)

theorem BlockData.blockSize_one (d : BlockData n 1) (j : Fin 1) : d.blockSize j = n := by
  have h := d.sum_blockSize
  simpa only [Fin.sum_univ_one, Subsingleton.elim j (0 : Fin 1)] using h

theorem BlockData.isBalanced_one (d : BlockData n 1) : d.IsBalanced := by
  intro j
  left
  simp [d.blockSize_one]

/-- The signed full diagonal whose signs are those of a given line direction. -/
def lineSignedData {n : ℕ} (U : Frame n 1) (hn : 0 < n) : BlockData n 1 where
  block := fun _ => 0
  onto := by
    intro j
    refine ⟨⟨0, hn⟩, ?_⟩
    exact Subsingleton.elim _ _
  negative := fun i => decide (lineVector U i < 0)

theorem lineVector_eq_sign_mul_max {n : ℕ} (U : Frame n 1) (hn : 0 < n)
    (h : sectionVolume U = Real.sqrt n) (i : Fin n) :
    lineVector U i = (lineSignedData U hn).sign i * lineMax U := by
  have habs := line_abs_eq_max_of_eq U h i
  by_cases hi : lineVector U i < 0
  · rw [abs_of_neg hi] at habs
    simp only [BlockData.sign, lineSignedData, hi, decide_true, ↓reduceIte]
    linarith
  · rw [abs_of_nonneg (le_of_not_gt hi)] at habs
    simpa [BlockData.sign, lineSignedData, hi] using habs

theorem line_eq_signed_frame_of_eq {n : ℕ} (U : Frame n 1) (hn : 0 < n)
    (h : sectionVolume U = Real.sqrt n) : U = (lineSignedData U hn).frame := by
  ext x i
  rw [lineMap_apply U x]
  simp only [PiLp.smul_apply, smul_eq_mul]
  rw [BlockData.frame_apply, BlockData.blockSize_one,
    lineVector_eq_sign_mul_max U hn h i, line_max_eq_inv_sqrt_of_eq U h]
  change x 0 * ((lineSignedData U hn).sign i * (1 / Real.sqrt n)) =
    (lineSignedData U hn).sign i * x 0 / Real.sqrt n
  ring

theorem line_sectionVolume_eq_sqrt_iff {n : ℕ} (U : Frame n 1) (hn : 0 < n) :
    sectionVolume U = Real.sqrt n ↔ IsBalancedSection U := by
  constructor
  · intro h
    rw [line_eq_signed_frame_of_eq U hn h]
    exact (lineSignedData U hn).isBalancedSection_frame
      (lineSignedData U hn).isBalanced_one
  · rintro ⟨d, hd, hU⟩
    have hvol : sectionVolume U = sectionVolume d.frame :=
      sectionVolume_eq_of_range_eq (hU.trans d.range_frame.symm)
    rw [hvol, d.sectionVolume_frame]
    simp [d.blockSize_one]

theorem line_sectionVolume_eq_iff {n : ℕ} (U : Frame n 1) (hn : 1 ≤ n) :
    sectionVolume U = sharpValue n 1 ↔ IsBalancedSection U := by
  simpa [sharpValue, Nat.mod_one] using line_sectionVolume_eq_sqrt_iff U hn

end CubeSections
