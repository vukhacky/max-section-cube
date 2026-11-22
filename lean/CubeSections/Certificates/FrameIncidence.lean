import CubeSections.Analysis.GlobalTransportEnergy
import CubeSections.LinearAlgebra.GroupedCharges
import CubeSections.Certificates.PairEnergyBridge

/-! The weighted incidence inequality from the exact common-Gaussian total
energy bound. Only Gaussian observables are integrated before the final energy
comparison, so no extra measurability assumption on the transported coordinates
is imposed. Unit and zero rows are handled by their zero off-diagonal weights.
-/
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped BigOperators InnerProductSpace RealInnerProductSpace

namespace CubeSections.Certificates
set_option maxHeartbeats 800000

def potentialAmplitude (β η : ℝ) : ℝ := Real.exp (-(β-min β η)/3)

theorem potentialAmplitude_one_or (β η : ℝ) :
    potentialAmplitude β η = 1 ∨ potentialAmplitude η β = 1 := by
  rcases le_total β η with h | h
  · left
    simp [potentialAmplitude,min_eq_left h]
  · right
    simp [potentialAmplitude,min_eq_left h]

theorem potentialPairEnergy_sub_min (A B β η T S G H : ℝ) :
    potentialPairEnergy A B (β-min β η) (η-min β η) T S G H =
      potentialPairEnergy A B β η T S G H := by
  have h : ((β-min β η)+T^2/2)-((η-min β η)+S^2/2) =
      (β+T^2/2)-(η+S^2/2) := by ring
  unfold potentialPairEnergy
  rw [h]

theorem leverage_bounds_of_positive_weight {n k : ℕ} (U : Frame n k) (i j : Fin n)
    (hij : 0 < groupedGramWeight U i j) : 0 < leverage U i ∧ leverage U i < 1 := by
  have hsum := Finset.single_le_sum
    (fun z (_ : z ∈ (Finset.univ : Finset (Fin n))) => groupedGramWeight_nonneg U i z)
    (Finset.mem_univ j)
  have hd := hij.trans_le hsum
  rw [groupedGramWeight_degree] at hd
  constructor
  · nlinarith [sq_nonneg (leverage U i)]
  · by_contra h
    have heq : leverage U i = 1 := le_antisymm (leverage_le_one U i) (le_of_not_gt h)
    rw [heq] at hd
    norm_num at hd

def framePairObservable {n k : ℕ} (U : Frame n k) (β : Fin n → ℝ)
    (i j : Fin n) (x : E k) : ℝ :=
  (potentialAmplitude (β i) (β j) * gaussianScore (normalizedFrameCoordinate U i x) -
    potentialAmplitude (β j) (β i) * gaussianScore (normalizedFrameCoordinate U j x))^2 /
      pairTransferCoeff (leverage U i) (leverage U j)

def frameIncidenceObservable {n k : ℕ} (U : Frame n k) (β : Fin n → ℝ) (x : E k) : ℝ :=
  (1/2 : ℝ) * ∑ i, ∑ j, groupedGramWeight U i j * framePairObservable U β i j x

def framePairIncidence {n k : ℕ} (U : Frame n k) : ℝ :=
  (1/2 : ℝ) * ∑ i, ∑ j, groupedGramWeight U i j *
    pairAngularCost (leverage U i) (leverage U j)
      (gramProjection U i j^2/(leverage U i*leverage U j))

theorem integrable_framePairObservable {n k : ℕ} (U : Frame n k) (β : Fin n → ℝ)
    (i j : Fin n) : Integrable (framePairObservable U β i j) (stdGaussian (E k)) := by
  unfold framePairObservable
  apply Integrable.div_const
  exact integrable_scaledGaussianScore_diff_sq (stdGaussian (E k))
    (normalizedFrameCoordinate U i) (normalizedFrameCoordinate U j)
    (by unfold normalizedFrameCoordinate; fun_prop)
    (by unfold normalizedFrameCoordinate; fun_prop) _ _

theorem integrable_frameIncidenceObservable {n k : ℕ} (U : Frame n k) (β : Fin n → ℝ) :
    Integrable (frameIncidenceObservable U β) (stdGaussian (E k)) := by
  unfold frameIncidenceObservable
  apply Integrable.const_mul
  apply integrable_finsetSum
  intro i hi
  apply integrable_finsetSum
  intro j hj
  exact (integrable_framePairObservable U β i j).const_mul _

theorem framePairObservable_integral_lower {n k : ℕ} (U : Frame n k) (β : Fin n → ℝ)
    (i j : Fin n) (hw : 0 < groupedGramWeight U i j) :
    pairAngularCost (leverage U i) (leverage U j)
      (gramProjection U i j^2/(leverage U i*leverage U j)) ≤
      ∫ x, framePairObservable U β i j x ∂(stdGaussian (E k)) := by
  have hi := leverage_bounds_of_positive_weight U i j hw
  have hw' : 0 < groupedGramWeight U j i := by rwa [groupedGramWeight_symm]
  have hj := leverage_bounds_of_positive_weight U j i hw'
  let a : ActiveRow U := ⟨i,hi.1⟩
  let b : ActiveRow U := ⟨j,hj.1⟩
  have hs : gramProjection U i j^2/(leverage U i*leverage U j) ≤ 1 := by
    apply (div_le_iff₀ (mul_pos hi.1 hj.1)).mpr
    simpa using gramProjection_entry_sq_le U i j
  have hm := integral_gaussianPairObservable (unitRow U a) (unitRow U b)
    (unitRow_norm U a) (unitRow_norm U b)
    (potentialAmplitude (β i) (β j)) (potentialAmplitude (β j) (β i))
  rw [unitRow_inner_sq] at hm
  have hm' :
      (∫ x : E k,
        (potentialAmplitude (β i) (β j) * gaussianScore (normalizedFrameCoordinate U i x) -
          potentialAmplitude (β j) (β i) * gaussianScore (normalizedFrameCoordinate U j x))^2
          ∂(stdGaussian (E k))) =
        gaussianPairCost (gramProjection U i j^2/(leverage U i*leverage U j))
          (potentialAmplitude (β i) (β j)) (potentialAmplitude (β j) (β i)) := by
    simpa only [gaussianPairObservable,normalizedFrameCoordinate,unitRow,a,b] using hm
  rw [pairAngularCost_eq_gaussian_quotient]
  unfold framePairObservable
  rw [integral_div,hm']
  exact div_le_div_of_nonneg_right
    (gaussianPairCost_lower _ _ _ hs (potentialAmplitude_one_or (β i) (β j)))
    (pairTransferCoeff_pos _ _ hi.2 hj.2).le

theorem frame_incidence_gaussian_lower {n k : ℕ} (U : Frame n k) (β : Fin n → ℝ) :
    framePairIncidence U ≤ ∫ x, frameIncidenceObservable U β x ∂(stdGaussian (E k)) := by
  unfold framePairIncidence frameIncidenceObservable
  rw [integral_const_mul]
  rw [integral_finsetSum Finset.univ (fun i _ => integrable_finsetSum Finset.univ
    (fun j _ => (integrable_framePairObservable U β i j).const_mul _))]
  apply mul_le_mul_of_nonneg_left _ (by norm_num : (0 : ℝ) ≤ 1/2)
  apply Finset.sum_le_sum
  intro i hi
  rw [integral_finsetSum Finset.univ (fun j _ => (integrable_framePairObservable U β i j).const_mul _)]
  apply Finset.sum_le_sum
  intro j hj
  rw [integral_const_mul]
  by_cases hw : groupedGramWeight U i j = 0
  · simp [hw]
  · have hp := lt_of_le_of_ne (groupedGramWeight_nonneg U i j) (Ne.symm hw)
    exact mul_le_mul_of_nonneg_left (framePairObservable_integral_lower U β i j hp) hp.le

theorem weighted_framePairObservable_le {n k : ℕ} (U : Frame n k)
    (β T : Fin n → ℝ) (g : E k) (i j : Fin n) :
    groupedGramWeight U i j * framePairObservable U β i j g ≤
      groupedGramWeight U i j * potentialPairEnergy (leverage U i) (leverage U j)
        (β i) (β j) (T i) (T j) (normalizedFrameCoordinate U i g) (normalizedFrameCoordinate U j g) := by
  by_cases hw : groupedGramWeight U i j = 0
  · simp [hw]
  have hp := lt_of_le_of_ne (groupedGramWeight_nonneg U i j) (Ne.symm hw)
  have hi := leverage_bounds_of_positive_weight U i j hp
  have hp' : 0 < groupedGramWeight U j i := by rwa [groupedGramWeight_symm]
  have hj := leverage_bounds_of_positive_weight U j i hp'
  have hβ : 0 ≤ β i-min (β i) (β j) := sub_nonneg.mpr (min_le_left _ _)
  have hη : 0 ≤ β j-min (β i) (β j) := sub_nonneg.mpr (min_le_right _ _)
  have h := potential_pair_transfer_bound (leverage U i) (leverage U j)
    (β i-min (β i) (β j)) (β j-min (β i) (β j)) (T i) (T j)
    (normalizedFrameCoordinate U i g) (normalizedFrameCoordinate U j g) hi.2 hj.2 hβ hη
  change _ ≤ pairTransferCoeff (leverage U i) (leverage U j) *
    potentialPairEnergy _ _ _ _ _ _ _ _ at h
  rw [potentialPairEnergy_sub_min] at h
  have hbound : framePairObservable U β i j g ≤
      potentialPairEnergy (leverage U i) (leverage U j) (β i) (β j) (T i) (T j)
        (normalizedFrameCoordinate U i g) (normalizedFrameCoordinate U j g) := by
    unfold framePairObservable potentialAmplitude
    rw [min_comm (β j) (β i)]
    apply (div_le_iff₀ (pairTransferCoeff_pos _ _ hi.2 hj.2)).mpr
    simpa only [mul_comm] using h
  exact mul_le_mul_of_nonneg_left hbound hp.le

theorem offdiag_production_eq {n k : ℕ} (U : Frame n k) (β T : Fin n → ℝ) :
    (∑ i, ∑ j, groupedGramWeight U i j * phi |(β i+T i^2/2)-(β j+T j^2/2)|) =
      ∑ i, ∑ j, gramProjection U i j^2 * phi |(β i+T i^2/2)-(β j+T j^2/2)| := by
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  by_cases hij : i = j
  · subst j
    simp [groupedGramWeight,phi]
  · simp [groupedGramWeight,hij]

theorem frame_incidence_observable_le_energy {n k : ℕ} (U : Frame n k)
    (β T : Fin n → ℝ) (g : E k) :
    frameIncidenceObservable U β g ≤ frameTransportEnergy U β T g := by
  have hsum := Finset.sum_le_sum (s := Finset.univ) (fun i _ =>
    Finset.sum_le_sum (s := Finset.univ) (fun j _ => weighted_framePairObservable_le U β T g i j))
  have hhalf := mul_le_mul_of_nonneg_left hsum (by norm_num : (0 : ℝ) ≤ 1/2)
  have htransport := degree_transport_le_total (groupedGramWeight U) (leverage U)
    (fun i => T i-normalizedFrameCoordinate U i g) (groupedGramWeight_symm U)
    (leverage_nonneg U) (leverage_le_one U) (groupedGramWeight_degree U)
  have hsplit :
      (1/2 : ℝ)*∑ i, ∑ j, groupedGramWeight U i j *
        potentialPairEnergy (leverage U i) (leverage U j) (β i) (β j) (T i) (T j)
          (normalizedFrameCoordinate U i g) (normalizedFrameCoordinate U j g) =
      (1/2 : ℝ)*∑ i, ∑ j, groupedGramWeight U i j * phi |(β i+T i^2/2)-(β j+T j^2/2)| +
        (1/2 : ℝ)*∑ i, ∑ j, groupedGramWeight U i j *
          ((T i-normalizedFrameCoordinate U i g)^2/(2*(1-leverage U i)) +
            (T j-normalizedFrameCoordinate U j g)^2/(2*(1-leverage U j))) := by
    simp only [potentialPairEnergy,mul_add,Finset.sum_add_distrib]
    ring
  rw [hsplit,offdiag_production_eq] at hhalf
  exact hhalf.trans (add_le_add le_rfl htransport)

/-- Exact incidence bound with the same common-Gaussian total-energy premise as
the global angular theorem. No global strict upper bound on leverages is assumed. -/
theorem frame_incidence_bound_of_energy {n k : ℕ} (U : Frame n k)
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (G : Ω → E k) (hG : MeasurePreserving G μ (stdGaussian (E k)))
    (β : Fin n → ℝ) (T : Ω → Fin n → ℝ) (δ : ℝ)
    (hE : Integrable (fun ω => frameTransportEnergy U β (T ω) (G ω)) μ)
    (hbound : (∫ ω, frameTransportEnergy U β (T ω) (G ω) ∂μ) ≤ δ) :
    framePairIncidence U ≤ δ := by
  have hobs := integrable_frameIncidenceObservable U β
  have hobsμ : Integrable (fun ω => frameIncidenceObservable U β (G ω)) μ :=
    hG.integrable_comp_of_integrable hobs
  have hAE : AEStronglyMeasurable (frameIncidenceObservable U β) (μ.map G) := by
    rw [hG.map_eq]
    exact hobs.aestronglyMeasurable
  have hmoment := (integral_map hG.measurable.aemeasurable hAE).symm
  rw [hG.map_eq] at hmoment
  have hlow := frame_incidence_gaussian_lower U β
  rw [← hmoment] at hlow
  exact hlow.trans ((integral_mono hobsμ hE
    (fun ω => frame_incidence_observable_le_energy U β (T ω) (G ω))).trans hbound)

#print axioms frame_incidence_gaussian_lower
#print axioms frame_incidence_observable_le_energy
#print axioms frame_incidence_bound_of_energy
end CubeSections.Certificates
