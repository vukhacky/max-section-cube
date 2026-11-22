import CubeSections.Analysis.PrekopaContracts
import CubeSections.Geometry.MidpointLowDimension

/-! Zero-volume boundary cases for midpoint Brunn--Minkowski. -/
noncomputable section
open Set MeasureTheory
open scoped Pointwise
namespace CubeSections

theorem midpointMinkowski_comm {n : ℕ} (A B : Set (E n)) :
    midpointMinkowski A B = midpointMinkowski B A := by
  ext z
  constructor <;> rintro ⟨⟨x,y⟩,⟨hx,hy⟩,rfl⟩ <;>
    exact ⟨⟨y,x⟩,⟨hy,hx⟩,by simp only [add_comm]⟩

theorem midpoint_half_volume_right {n : ℕ} (A B : Set (E n))
    (hA : A.Nonempty) (hAc : IsCompact A) (hBc : IsCompact B) :
    (1/2:ℝ)^n * (volume B).toReal ≤ (volume (midpointMinkowski A B)).toReal := by
  obtain ⟨a,ha⟩ := hA
  let S : Set (E n) := (fun x : E n => (1/2:ℝ) • a + x) '' ((1/2:ℝ) • B)
  have hsub : S ⊆ midpointMinkowski A B := by
    rintro z ⟨w,⟨b,hb,rfl⟩,rfl⟩
    exact ⟨⟨a,b⟩,⟨ha,hb⟩,by simp only [smul_add]⟩
  have hvol : volume S = volume ((1/2:ℝ) • B) := by
    dsimp only [S]
    rw [image_add_left]
    simp
  have hfinite : volume (midpointMinkowski A B) ≠ ⊤ :=
    (midpointMinkowski_compact hAc hBc).measure_ne_top
  have h := ENNReal.toReal_mono hfinite (measure_mono hsub)
  rw [hvol,Measure.addHaar_smul_of_nonneg volume (by norm_num : (0:ℝ) ≤ 1/2),
    finrank_euclideanSpace_fin, ENNReal.toReal_mul,
    ENNReal.toReal_ofReal (by positivity : 0 ≤ (1/2:ℝ)^n)] at h
  exact h

theorem midpoint_root_zero_left {n : ℕ} (hn : 1 ≤ n) (A B : Set (E n))
    (hA : A.Nonempty) (hAc : IsCompact A) (hBc : IsCompact B)
    (hzero : (volume A).toReal = 0) :
    (((volume A).toReal)^((1:ℝ)/(n:ℝ)) + ((volume B).toReal)^((1:ℝ)/(n:ℝ)))/2 ≤
      ((volume (midpointMinkowski A B)).toReal)^((1:ℝ)/(n:ℝ)) := by
  have hnR : (0:ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have he : (0:ℝ) < 1/(n:ℝ) := by positivity
  rw [hzero,Real.zero_rpow (ne_of_gt he),zero_add]
  have h := Real.rpow_le_rpow (show 0 ≤ (1/2:ℝ)^n*(volume B).toReal by positivity)
    (midpoint_half_volume_right A B hA hAc hBc) he.le
  have hroot : ((1/2:ℝ)^n)^((1:ℝ)/(n:ℝ)) = 1/2 := by
    simpa only [one_div] using Real.pow_rpow_inv_natCast (x := (1/2:ℝ)) (n := n) (by norm_num) (by omega)
  rw [Real.mul_rpow (by positivity : 0 ≤ (1/2:ℝ)^n) ENNReal.toReal_nonneg,hroot] at h
  simpa only [one_div, div_eq_mul_inv, mul_comm, one_mul, mul_one] using h

#print axioms midpoint_half_volume_right
#print axioms midpoint_root_zero_left
end CubeSections
