import CubeSections.Geometry.AffineSections
import CubeSections.Geometry.Lines

/-! Affine central domination in dimensions zero and one, proved directly.
These endpoints do not use a Brunn--Minkowski assumption. -/
noncomputable section
open Set MeasureTheory Classical
open scoped ENNReal
namespace CubeSections

theorem affineMass_zero_le_sectionMass {n : ℕ} (U : Frame n 0) (y : E n) :
    affineMass U y ≤ sectionMass U := by
  rw [affineMass_zeroDimension, zeroDimension_sectionMass]
  split_ifs <;> simp

theorem lineVector_exists_abs_eq_max {n : ℕ} (U : Frame n 1) :
    ∃ i : Fin n, |lineVector U i| = lineMax U := by
  have hne : ∃ i : Fin n, lineVector U i ≠ 0 := by
    by_contra h
    push_neg at h
    apply lineVector_ne_zero U
    ext i
    exact h i
  obtain ⟨a,ha⟩ := hne
  obtain ⟨i,hi,hmax⟩ := Finset.exists_max_image Finset.univ (fun i : Fin n => |lineVector U i|)
    ⟨a, Finset.mem_univ a⟩
  refine ⟨i, le_antisymm (lineVector_abs_le_max U i) ?_⟩
  apply (pi_norm_le_iff_of_nonneg (abs_nonneg (lineVector U i))).mpr
  intro j
  simpa only [Real.norm_eq_abs] using hmax j (Finset.mem_univ j)

theorem lineScalar_measurePreserving : MeasurePreserving (fun x : E 1 => x 0) := by
  exact (volume_preserving_funUnique (Fin 1) ℝ).comp (PiLp.volume_preserving_ofLp (Fin 1))

theorem line_coordinate_affineSlab_mass {n : ℕ} (U : Frame n 1) (y : E n)
    (i : Fin n) (hi : lineVector U i ≠ 0) :
    volume {x : E 1 | |y i + (U x) i| ≤ (1 : ℝ)/2} = ENNReal.ofReal (1/|lineVector U i|) := by
  let S : Set ℝ := (fun t : ℝ => y i + t * lineVector U i) ⁻¹' Icc (-(1:ℝ)/2) (1/2)
  have hS : MeasurableSet S := measurableSet_Icc.preimage (by fun_prop)
  have hset : {x : E 1 | |y i + (U x) i| ≤ (1 : ℝ)/2} = (fun x : E 1 => x 0) ⁻¹' S := by
    ext x
    simp only [Set.mem_setOf_eq, Set.mem_preimage, S, Set.mem_Icc, abs_le,
      lineMap_apply, PiLp.smul_apply, smul_eq_mul, neg_div]
  rw [hset, lineScalar_measurePreserving.measure_preimage hS.nullMeasurableSet]
  change volume ((fun t : ℝ => t * lineVector U i) ⁻¹'
    ((fun t : ℝ => y i + t) ⁻¹' Icc (-(1:ℝ)/2) (1/2))) = _
  rw [Real.volume_preimage_mul_right hi, measure_preimage_add volume (y i), Real.volume_Icc]
  norm_num only [sub_neg_eq_add, add_halves, ENNReal.ofReal_one, mul_one]
  rw [abs_inv, one_div]

theorem affineMass_line_le_sectionMass {n : ℕ} (U : Frame n 1) (y : E n) :
    affineMass U y ≤ sectionMass U := by
  obtain ⟨i, hi⟩ := lineVector_exists_abs_eq_max U
  have hnonzero : lineVector U i ≠ 0 := by
    intro hz
    rw [hz, abs_zero] at hi
    exact (ne_of_gt (lineMax_pos U)) hi.symm
  calc
    affineMass U y ≤ volume {x : E 1 | |y i + (U x) i| ≤ (1 : ℝ)/2} := by
      apply measure_mono
      intro x hx
      exact hx i
    _ = ENNReal.ofReal (1/|lineVector U i|) := line_coordinate_affineSlab_mass U y i hnonzero
    _ = sectionMass U := by rw [hi, line_sectionMass]

theorem affineVolume_line_le_sectionVolume {n : ℕ} (U : Frame n 1) (y : E n) :
    affineVolume U y ≤ sectionVolume U :=
  ENNReal.toReal_mono (sectionMass_ne_top U) (affineMass_line_le_sectionMass U y)

#print axioms affineMass_zero_le_sectionMass
#print axioms affineMass_line_le_sectionMass
#print axioms affineVolume_line_le_sectionVolume
end CubeSections
