import CubeSections.Certificates.FrameIncidence
import CubeSections.Geometry.GroupedFrame

/-! Exact incidence accounting on the actual coalesced frame. Its geometric
rows have the original class masses; the width parameters remain arbitrary β
in the transport energy, with no interpretation as a new cube section.
-/
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped BigOperators

namespace CubeSections.Certificates

theorem groupedGramWeight_coalesced {n k : ℕ} (U : Frame n k) (c d : RowClass U) :
    groupedGramWeight (coalescedFrame U) (rowClassEquiv U c) (rowClassEquiv U d) =
      classWeight U c d := by
  by_cases h : c = d
  · subst d
    simp [groupedGramWeight,classWeight]
  · have he : rowClassEquiv U c ≠ rowClassEquiv U d := fun hh => h ((rowClassEquiv U).injective hh)
    simp only [groupedGramWeight,classWeight,h,he,if_false,classGram]

theorem coalesced_squared_correlation {n k : ℕ} (U : Frame n k) (c d : RowClass U) :
    gramProjection (coalescedFrame U) (rowClassEquiv U c) (rowClassEquiv U d)^2 /
      (leverage (coalescedFrame U) (rowClassEquiv U c) *
        leverage (coalescedFrame U) (rowClassEquiv U d)) = rowClassAngle U c d := by
  rw [leverage_coalescedFrame,leverage_coalescedFrame,
    Equiv.symm_apply_apply,Equiv.symm_apply_apply]
  change classGram U c d^2/(rowClassMass U c*rowClassMass U d) = _
  rw [classGram_sq]
  unfold rowClassAngle
  have hc : rowClassMass U c ≠ 0 := ne_of_gt (rowClassMass_pos U c)
  have hd : rowClassMass U d ≠ 0 := ne_of_gt (rowClassMass_pos U d)
  field_simp

theorem framePairIncidence_coalesced {n k : ℕ} (U : Frame n k) :
    framePairIncidence (coalescedFrame U) =
      (1/2 : ℝ)*∑ c : RowClass U, ∑ d : RowClass U,
        classWeight U c d * pairAngularCost (rowClassMass U c) (rowClassMass U d)
          (rowClassAngle U c d) := by
  let V := coalescedFrame U
  let e := rowClassEquiv U
  let f := fun i j : Fin (rowClassCount U) => groupedGramWeight V i j *
    pairAngularCost (leverage V i) (leverage V j)
      (gramProjection V i j^2/(leverage V i*leverage V j))
  have hsum : (∑ i, ∑ j, f i j) = ∑ c : RowClass U, ∑ d : RowClass U, f (e c) (e d) := by
    calc
      _ = ∑ c : RowClass U, ∑ j, f (e c) j := (e.sum_comp (fun i => ∑ j, f i j)).symm
      _ = _ := Finset.sum_congr rfl (fun c _ => (e.sum_comp (fun j => f (e c) j)).symm)
  change (1/2 : ℝ)*(∑ i, ∑ j, f i j) = _
  rw [hsum]
  congr 1
  apply Finset.sum_congr rfl
  intro c hc
  apply Finset.sum_congr rfl
  intro d hd
  dsimp [f,V,e]
  rw [groupedGramWeight_coalesced,coalesced_squared_correlation,
    leverage_coalescedFrame,leverage_coalescedFrame,
    Equiv.symm_apply_apply,Equiv.symm_apply_apply]

/-- The original frame may have zero rows. Coalescing uses only its active row
classes, and every class mass is positive. Unit classes require no strict bound. -/
theorem actualClass_incidence_bound_of_energy {n k : ℕ} (U : Frame n k)
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (G : Ω → E k) (hG : MeasurePreserving G μ (stdGaussian (E k)))
    (β : Fin (rowClassCount U) → ℝ) (T : Ω → Fin (rowClassCount U) → ℝ) (δ : ℝ)
    (hE : Integrable (fun ω => frameTransportEnergy (coalescedFrame U) β (T ω) (G ω)) μ)
    (hbound : (∫ ω, frameTransportEnergy (coalescedFrame U) β (T ω) (G ω) ∂μ) ≤ δ) :
    (1/2 : ℝ)*∑ c : RowClass U, ∑ d : RowClass U,
      classWeight U c d * pairAngularCost (rowClassMass U c) (rowClassMass U d)
        (rowClassAngle U c d) ≤ δ := by
  rw [← framePairIncidence_coalesced]
  exact frame_incidence_bound_of_energy (coalescedFrame U) μ G hG β T δ hE hbound

#print axioms framePairIncidence_coalesced
#print axioms actualClass_incidence_bound_of_energy
end CubeSections.Certificates
