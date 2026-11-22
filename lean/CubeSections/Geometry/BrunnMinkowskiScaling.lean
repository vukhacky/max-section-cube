import CubeSections.Analysis.PrekopaContracts
import CubeSections.Geometry.MidpointLowDimension

/-! Reduction of arithmetic root-volume BM to multiplicative BM by positive
homotheties. The multiplicative inequality remains an explicit hypothesis. -/
noncomputable section
open Set MeasureTheory
open scoped Pointwise
set_option maxHeartbeats 800000
namespace CubeSections

theorem realVolume_smul {n : ℕ} (r : ℝ) (hr : 0 ≤ r) (A : Set (E n)) :
    (volume (r • A)).toReal = r^n * (volume A).toReal := by
  rw [Measure.addHaar_smul_of_nonneg volume hr, ENNReal.toReal_mul,
    finrank_euclideanSpace_fin, ENNReal.toReal_ofReal (pow_nonneg hr n)]

theorem weightedMinkowski_rescale {n : ℕ} (A B : Set (E n)) (a b : ℝ)
    (ha : 0 < a) (hb : 0 < b) :
    weightedMinkowski (b/(a+b)) (a⁻¹ • A) (b⁻¹ • B) =
      (2/(a+b)) • midpointMinkowski A B := by
  have hab : a+b ≠ 0 := ne_of_gt (add_pos ha hb)
  have h1 : (1-b/(a+b))*a⁻¹ = (a+b)⁻¹ := by field_simp; ring
  have h2 : (b/(a+b))*b⁻¹ = (a+b)⁻¹ := by field_simp
  have h3 : (2/(a+b))*(1/2:ℝ) = (a+b)⁻¹ := by ring
  have hpoint (x y : E n) :
      (1-b/(a+b)) • (a⁻¹ • x) + (b/(a+b)) • (b⁻¹ • y) =
        (2/(a+b)) • ((1/2:ℝ) • (x+y)) := by
    simp only [smul_smul, h1,h2,h3,smul_add]
  ext z
  constructor
  · rintro ⟨⟨u,v⟩,⟨hu,hv⟩,rfl⟩
    obtain ⟨x,hx,rfl⟩ := hu
    obtain ⟨y,hy,rfl⟩ := hv
    refine ⟨(1/2:ℝ) • (x+y), ⟨⟨x,y⟩,⟨hx,hy⟩,rfl⟩, ?_⟩
    exact (hpoint x y).symm
  · rintro ⟨w,⟨⟨x,y⟩,⟨hx,hy⟩,rfl⟩,rfl⟩
    exact ⟨⟨a⁻¹ • x,b⁻¹ • y⟩,⟨⟨x,hx,rfl⟩,⟨y,hy,rfl⟩⟩,hpoint x y⟩

theorem midpoint_root_volume_of_positive_multiplicative {n : ℕ} (hn : 1 ≤ n)
    (hBM : CompactMultiplicativeBM n) (A B : Set (E n))
    (hAc : IsCompact A) (hBc : IsCompact B) (hAv : Convex ℝ A) (hBv : Convex ℝ B)
    (hAn : A.Nonempty) (hBn : B.Nonempty)
    (hA : 0 < (volume A).toReal) (hB : 0 < (volume B).toReal) :
    (((volume A).toReal)^((1:ℝ)/(n:ℝ)) +
      ((volume B).toReal)^((1:ℝ)/(n:ℝ)))/2 ≤
        ((volume (midpointMinkowski A B)).toReal)^((1:ℝ)/(n:ℝ)) := by
  let a : ℝ := ((volume A).toReal)^((1:ℝ)/(n:ℝ))
  let b : ℝ := ((volume B).toReal)^((1:ℝ)/(n:ℝ))
  have ha : 0 < a := Real.rpow_pos_of_pos hA _
  have hb : 0 < b := Real.rpow_pos_of_pos hB _
  have han : a^n = (volume A).toReal := by
    simpa only [a, one_div] using Real.rpow_inv_natCast_pow (x := (volume A).toReal) (n := n) ENNReal.toReal_nonneg (by omega)
  have hbn : b^n = (volume B).toReal := by
    simpa only [b, one_div] using Real.rpow_inv_natCast_pow (x := (volume B).toReal) (n := n) ENNReal.toReal_nonneg (by omega)
  have hnA : (volume (a⁻¹ • A)).toReal = 1 := by
    rw [realVolume_smul _ (inv_nonneg.mpr ha.le), ← han, inv_pow]
    exact inv_mul_cancel₀ (ne_of_gt (pow_pos ha n))
  have hnB : (volume (b⁻¹ • B)).toReal = 1 := by
    rw [realVolume_smul _ (inv_nonneg.mpr hb.le), ← hbn, inv_pow]
    exact inv_mul_cancel₀ (ne_of_gt (pow_pos hb n))
  have h := hBM (b/(a+b)) (div_pos hb (add_pos ha hb))
    ((div_lt_one (add_pos ha hb)).mpr (by linarith))
    (a⁻¹ • A) (b⁻¹ • B)
    (hAc.image (by fun_prop : Continuous (fun x : E n => a⁻¹ • x)))
    (hBc.image (by fun_prop : Continuous (fun x : E n => b⁻¹ • x)))
    (hAv.smul _) (hBv.smul _) (hAn.image _) (hBn.image _)
  rw [hnA,hnB,Real.one_rpow,Real.one_rpow,one_mul,weightedMinkowski_rescale A B a b ha hb,
    realVolume_smul _ (by positivity : 0 ≤ 2/(a+b))] at h
  have hs : 0 ≤ (a+b)/2 := by positivity
  have hcancel : ((a+b)/2:ℝ)*(2/(a+b)) = 1 := by field_simp
  have hp : ((a+b)/2)^n ≤ (volume (midpointMinkowski A B)).toReal := by
    have hmul := mul_le_mul_of_nonneg_left h (pow_nonneg hs n)
    rw [mul_one,← mul_assoc,← mul_pow,hcancel,one_pow,one_mul] at hmul
    exact hmul
  change (a+b)/2 ≤ _
  calc
    _ = (((a+b)/2)^n)^((1:ℝ)/(n:ℝ)) := by
      rw [one_div,Real.pow_rpow_inv_natCast hs (by omega)]
    _ ≤ _ := Real.rpow_le_rpow (pow_nonneg hs n) hp (by positivity)

#print axioms midpoint_root_volume_of_positive_multiplicative
end CubeSections
