import CubeSections.Geometry.PairCoarea
import CubeSections.Geometry.CentralDomination
import CubeSections.Integer.PointFiber
import CubeSections.Certificates.ActualGroupedComparison

/-! The fiber density cap from midpoint Brunn--Minkowski and the
smaller-dimensional cube bound. The proof combines coarea, the reduced ambient
dimension, the balanced-target ratio and coordinate orientation.
-/
noncomputable section
open Set MeasureTheory Classical
open scoped ENNReal
namespace CubeSections

theorem reducedClassFrame_volume_le_radius_mul_of_reduced_bound {n k : ℕ} (q r : ℕ)
    (hq : 1 ≤ q) (hk : 2 ≤ k) (hr : r ≤ k) (hn : n = q*k+r)
    (U : Frame n k) (hU : IsMaximizingFrame U) (hrep : RowReplacement U)
    (hwin : ReciprocalWindow q U) (c d : RowClass U) (hw : 0 < classWeight U c d)
    (hIH : 1 ≤ k-2 →
      sectionVolume (reducedClassFrame U c d (classWeight_pos_ne U c d hw)) ≤
        sharpValue (remainingRowCount U c d) (k-2)) :
    sectionVolume (reducedClassFrame U c d (classWeight_pos_ne U c d hw)) ≤
      fiberRadius q (rowClassMultiplicity U c) (rowClassMultiplicity U d) * sectionVolume U := by
  have hcd := classWeight_pos_ne U c d hw
  have hm := rowClassMultiplicity_le_of_weight_pos q hq U hrep hwin c d hw
  have hkn : k ≤ n := by
    have hmul := Nat.mul_le_mul_right k hq
    simp only [one_mul] at hmul
    omega
  have hW := sharpValue_pos (by omega : 1 ≤ k) hkn
  have hmax := sharpValue_le_of_maximizing U hU (by omega) hkn
  have hratio : sectionVolume (reducedClassFrame U c d hcd) / sharpValue n k ≤
      fiberRadius q (rowClassMultiplicity U c) (rowClassMultiplicity U d) := by
    by_cases hk2 : k = 2
    · subst k
      simpa only [← hn] using
        zeroDimensionalFiber_volume_ratio q r _ _ _ hq hr hm.1 hm.2 (reducedClassFrame U c d hcd)
    · have hh : 1 ≤ k-2 := by omega
      have hsplit : k = (k-2)+2 := by omega
      have hcount := remainingRowCount_eq_of_pos U c d hcd (reciprocalWindow_pos q U hwin)
      calc
        _ ≤ sharpValue (remainingRowCount U c d) (k-2) / sharpValue n k :=
          div_le_div_of_nonneg_right (hIH hh) hW.le
        _ ≤ _ := by
          simpa only [← hsplit, ← hn, ← hcount] using
            sharpValue_fiber_ratio q (k-2) r (rowClassMultiplicity U c)
              (rowClassMultiplicity U d) hq hh (by omega) hm.1 hm.2
  have h := (div_le_iff₀ hW).mp hratio
  exact h.trans (mul_le_mul_of_nonneg_left hmax (fiberRadius_pos _ _ _ hq).le)

theorem reducedClassFrame_volume_le_radius_mul {n k : ℕ} (q r : ℕ)
    (hq : 1 ≤ q) (hk : 2 ≤ k) (hr : r ≤ k) (hn : n = q*k+r)
    (U : Frame n k) (hU : IsMaximizingFrame U) (hrep : RowReplacement U)
    (hwin : ReciprocalWindow q U) (c d : RowClass U) (hw : 0 < classWeight U c d)
    (hIH : 1 ≤ k-2 → ∀ N : ℕ, ∀ V : Frame N (k-2), sectionVolume V ≤ sharpValue N (k-2)) :
    sectionVolume (reducedClassFrame U c d (classWeight_pos_ne U c d hw)) ≤
      fiberRadius q (rowClassMultiplicity U c) (rowClassMultiplicity U d) * sectionVolume U :=
  reducedClassFrame_volume_le_radius_mul_of_reduced_bound q r hq hk hr hn U hU hrep hwin c d hw
    (fun hh => hIH hh _ _)

theorem remainingRowCount_ge_quotient_fiber {n k : ℕ} (q r : ℕ)
    (hq : 1 ≤ q) (hk : 2 ≤ k) (hn : n = q*k+r)
    (U : Frame n k) (hrep : RowReplacement U) (hwin : ReciprocalWindow q U)
    (c d : RowClass U) (hw : 0 < classWeight U c d) :
    q*(k-2) ≤ remainingRowCount U c d := by
  have hm := rowClassMultiplicity_le_of_weight_pos q hq U hrep hwin c d hw
  have hcount := remainingRowCount_eq_of_pos U c d (classWeight_pos_ne U c d hw)
    (reciprocalWindow_pos q U hwin)
  have hsplit : q*k = q*(k-2)+2*q := by
    have hk' : k = (k-2)+2 := by omega
    calc
      q*k = q*((k-2)+2) := congrArg (q*·) hk'
      _ = _ := by ring
  omega

theorem reducedClassFrame_volume_le_radius_mul_restricted {n k : ℕ} (q r : ℕ)
    (hq : 2 ≤ q) (hk : 2 ≤ k) (hr : r ≤ k) (hn : n = q*k+r)
    (U : Frame n k) (hU : IsMaximizingFrame U) (hrep : RowReplacement U)
    (hwin : ReciprocalWindow q U) (c d : RowClass U) (hw : 0 < classWeight U c d)
    (hIH : 1 ≤ k-2 → ∀ N : ℕ, 2*(k-2) ≤ N →
      ∀ V : Frame N (k-2), sectionVolume V ≤ sharpValue N (k-2)) :
    sectionVolume (reducedClassFrame U c d (classWeight_pos_ne U c d hw)) ≤
      fiberRadius q (rowClassMultiplicity U c) (rowClassMultiplicity U d) * sectionVolume U := by
  apply reducedClassFrame_volume_le_radius_mul_of_reduced_bound q r (by omega) hk hr hn
    U hU hrep hwin c d hw
  intro hh
  apply hIH hh
  exact (Nat.mul_le_mul_right (k-2) hq).trans
    (remainingRowCount_ge_quotient_fiber q r (by omega) hk hn U hrep hwin c d hw)

theorem pairClass_density_cap_of_affine_domination {n k : ℕ} (q : ℕ)
    (U : Frame n k) (c d : RowClass U) (hcd : c ≠ d)
    (hcentral : ∀ y, affineMass (reducedClassFrame U c d hcd) y ≤
      sectionMass (reducedClassFrame U c d hcd))
    (hvol : sectionVolume (reducedClassFrame U c d hcd) ≤
      fiberRadius q (rowClassMultiplicity U c) (rowClassMultiplicity U d) * sectionVolume U) :
    Certificates.SourcePairDensity U ⟨q,rowClassMultiplicity U c,rowClassMultiplicity U d⟩
      (rowClassRep U c).val (rowClassRep U d).val
      (rowClassLeverage U c) (rowClassLeverage U d) (rowClassAngle U c d) := by
  let i := (rowClassRep U c).val
  let j := (rowClassRep U d).val
  let hd := pairGramDet_classRep_pos U c d hcd
  refine ⟨pairPushforwardDensity U i j hd (U ⁻¹' cube n), pairSection_coarea U i j hd, ?_⟩
  apply Filter.Eventually.of_forall
  intro p
  have hf := pairClassSliceMass_le_affineMass U c d hcd p
  have hb := hcentral
    (reducedOffset U c d (pairFiberOffset U i j hd p))
  have hm : sectionMass (reducedClassFrame U c d hcd) ≤
      ENNReal.ofReal (fiberRadius q (rowClassMultiplicity U c) (rowClassMultiplicity U d) * sectionVolume U) := by
    rw [← ENNReal.ofReal_toReal (sectionMass_ne_top _)]
    exact ENNReal.ofReal_le_ofReal hvol
  have hdet : pairGramDet U i j = rowClassLeverage U c * rowClassLeverage U d *
      (1-rowClassAngle U c d) := by
    unfold pairGramDet
    rw [rowClassRep_gram_sq]
    change rowClassLeverage U c * rowClassLeverage U d -
      rowClassLeverage U c * rowClassLeverage U d * rowClassAngle U c d = _
    ring
  have hsqrt : Real.sqrt (pairGramDet U i j) =
      Real.sqrt (rowClassLeverage U c * rowClassLeverage U d) * Real.sqrt (1-rowClassAngle U c d) := by
    rw [hdet, Real.sqrt_mul (mul_pos (rowClassLeverage_pos U c) (rowClassLeverage_pos U d)).le]
  calc
    _ ≤ ENNReal.ofReal (4 * Real.sqrt (pairGramDet U i j))⁻¹ *
        ENNReal.ofReal (fiberRadius q (rowClassMultiplicity U c) (rowClassMultiplicity U d) * sectionVolume U) :=
      by
        unfold pairPushforwardDensity
        gcongr
        exact hf.trans (hb.trans hm)
    _ = _ := by
      rw [← ENNReal.ofReal_mul (by positivity : 0 ≤ (4 * Real.sqrt (pairGramDet U i j))⁻¹)]
      congr 1
      rw [hsqrt]
      unfold Certificates.sourceRadius fiberRadius
      simp only [div_eq_mul_inv, mul_inv_rev]
      ring

theorem pairClass_density_cap_of_central_bound {n k : ℕ} (q : ℕ)
    (U : Frame n k) (c d : RowClass U) (hcd : c ≠ d)
    (hBM : MidpointBrunnMinkowski (k-2))
    (hvol : sectionVolume (reducedClassFrame U c d hcd) ≤
      fiberRadius q (rowClassMultiplicity U c) (rowClassMultiplicity U d) * sectionVolume U) :
    Certificates.SourcePairDensity U ⟨q,rowClassMultiplicity U c,rowClassMultiplicity U d⟩
      (rowClassRep U c).val (rowClassRep U d).val
      (rowClassLeverage U c) (rowClassLeverage U d) (rowClassAngle U c d) :=
  pairClass_density_cap_of_affine_domination q U c d hcd
    (affineMass_le_sectionMass_of_midpointBM _ hBM) hvol

end CubeSections
