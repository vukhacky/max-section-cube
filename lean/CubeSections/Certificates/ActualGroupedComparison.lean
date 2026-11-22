import CubeSections.Geometry.GroupedFrame
import CubeSections.Geometry.RowOrientation
import CubeSections.Geometry.Rigidity
import CubeSections.Geometry.BalancedVolume
import CubeSections.Integer.EntropyGap
import CubeSections.Certificates.DensityStripBridge
import CubeSections.Certificates.GroupedComparison

/-! Conditional small-quotient closure on the actual unoriented row classes.
Only the planar density caps and the analytic weighted incidence bound remain
inputs. All finite grouping, orientation, maximality, and scalar certificates
are proved internally.
-/
noncomputable section
open Set MeasureTheory Classical
open scoped BigOperators InnerProductSpace

namespace CubeSections.Certificates

def orientedPairFrame {n k : ℕ} (U : Frame n k) (i j : Fin n) : Frame n k :=
  if 0 ≤ gramProjection U i j then U else flipRowFrame U i

theorem orientedPairFrame_volume {n k : ℕ} (U : Frame n k) (i j : Fin n) :
    sectionVolume (orientedPairFrame U i j) = sectionVolume U := by
  unfold orientedPairFrame
  split_ifs
  · rfl
  · exact flipRowFrame_volume U i

theorem orientedPairFrame_leverage {n k : ℕ} (U : Frame n k) (i j p : Fin n) :
    leverage (orientedPairFrame U i j) p = leverage U p := by
  unfold orientedPairFrame
  split_ifs
  · rfl
  · exact leverage_flipRowFrame U i p

theorem orientedPairFrame_maximizing {n k : ℕ} (U : Frame n k) (i j : Fin n)
    (hU : IsMaximizingFrame U) : IsMaximizingFrame (orientedPairFrame U i j) := by
  unfold orientedPairFrame
  split_ifs
  · exact hU
  · exact flipRowFrame_maximizing U i hU

theorem orientedPairFrame_gram_nonneg {n k : ℕ} (U : Frame n k) (i j : Fin n)
    (hij : i ≠ j) : 0 ≤ gramProjection (orientedPairFrame U i j) i j := by
  unfold orientedPairFrame
  split_ifs with h
  · exact h
  · rw [gramProjection_flipRowFrame U i j hij]
    linarith

theorem orientedPairFrame_gram_sq {n k : ℕ} (U : Frame n k) (i j : Fin n)
    (hij : i ≠ j) :
    gramProjection (orientedPairFrame U i j) i j ^ 2 = gramProjection U i j ^ 2 := by
  unfold orientedPairFrame
  split_ifs
  · rfl
  · rw [gramProjection_flipRowFrame U i j hij, neg_sq]

/-- The density obligation only for interacting actual classes, on an explicitly
defined coordinate reflection of the original frame. -/
def ActualClassDensity {n k : ℕ} (U : Frame n k) (q : ℕ) : Prop :=
  ∀ c d : RowClass U, 0 < classWeight U c d →
    SourcePairDensity
      (orientedPairFrame U (rowClassRep U c).val (rowClassRep U d).val)
      ⟨q,rowClassMultiplicity U c,rowClassMultiplicity U d⟩
      (rowClassRep U c).val (rowClassRep U d).val
      (rowClassLeverage U c) (rowClassLeverage U d) (rowClassAngle U c d)

theorem rowReplacement_of_maximizing_window {n k : ℕ} (q : ℕ) (hq : 2 ≤ q)
    (U : Frame n k) (hU : IsMaximizingFrame U) (hwin : ReciprocalWindow q U) :
    RowReplacement U := by
  have hqR : (2 : ℝ) ≤ q := by exact_mod_cast hq
  have hupper : (1 : ℝ)/(q : ℝ) < 1 :=
    (div_lt_one (by linarith : (0 : ℝ) < q)).mpr (by linarith)
  intro i j hij
  exact maximizing_leverage_gap U hU i j ((hwin i).2.trans_lt hupper)
    ((hwin j).2.trans_lt hupper)

theorem actualGroupedFrameConstraints {n k : ℕ} (q : ℕ) (U : Frame n k)
    (hrep : RowReplacement U) (hwin : ReciprocalWindow q U) :
    GroupedFrameConstraints q (rowClassMultiplicity U) (rowClassLeverage U)
      (classWeight U) (rowClassAngle U) := by
  refine {
    multiplicity_pos := rowClassMultiplicity_pos U
    window := rowClassLeverage_window q U hwin
    class_le_one := ?_
    weight_nonneg := classWeight_nonneg U
    weight_symm := classWeight_symm U
    degree := classWeight_degree_multiplicity U hrep
    angle := ?_
    projection := ?_ }
  · intro c
    rw [← rowClassMass_eq_multiplicity_mul_leverage U hrep]
    exact rowClassMass_le_one U c
  · intro c d hw
    exact ⟨rowClassAngle_pos_of_weight_pos U c d hw,
      rowClassAngle_lt_one U c d (classWeight_pos_ne U c d hw)⟩
  · intro c d hw
    exact rowClass_complementary_angle U hrep c d (classWeight_pos_ne U c d hw)

theorem actualGroupedConstraints_of_density {n k : ℕ} (q : ℕ) (hq : 2 ≤ q)
    (U : Frame n k) (hU : IsMaximizingFrame U) (hwin : ReciprocalWindow q U)
    (hdensity : ActualClassDensity U q) :
    GroupedConstraints q (rowClassMultiplicity U) (rowClassLeverage U)
      (classWeight U) (rowClassAngle U) := by
  have hrep := rowReplacement_of_maximizing_window q hq U hU hwin
  refine ⟨actualGroupedFrameConstraints q U hrep hwin,?_⟩
  intro c d hw
  have hcd := classWeight_pos_ne U c d hw
  have hij := rowClassRep_val_ne U c d hcd
  have hm := rowClassMultiplicity_le_of_weight_pos q (by omega) U hrep hwin c d hw
  let i := (rowClassRep U c).val
  let j := (rowClassRep U d).val
  have hc : leverage (orientedPairFrame U i j) i = rowClassLeverage U c :=
    orientedPairFrame_leverage U i j i
  have hd : leverage (orientedPairFrame U i j) j = rowClassLeverage U d :=
    orientedPairFrame_leverage U i j j
  have hcorr : gramProjection (orientedPairFrame U i j) i j ^ 2 =
      rowClassLeverage U c * rowClassLeverage U d * rowClassAngle U c d := by
    rw [orientedPairFrame_gram_sq U i j hij]
    exact rowClassRep_gram_sq U c d
  exact sourceDirectStrip_of_maximizing_density (orientedPairFrame U i j)
    (orientedPairFrame_maximizing U i j hU)
    ⟨q,rowClassMultiplicity U c,rowClassMultiplicity U d⟩ hq hm.1 hm.2
    i j hij (rowClassLeverage U c) (rowClassLeverage U d) (rowClassAngle U c d)
    hc hd (rowClassLeverage_window q U hwin c).1 (rowClassLeverage_window q U hwin c).2
    (rowClassLeverage_window q U hwin d).1 (rowClassLeverage_window q U hwin d).2
    (rowClassAngle_pos_of_weight_pos U c d hw) (rowClassAngle_lt_one U c d hcd)
    (orientedPairFrame_gram_nonneg U i j hij) hcorr (hdensity c d hw)

theorem actualGroupedDeficitReduction {n k : ℕ} (q : ℕ)
    (hq : q=2 ∨ q=3 ∨ q=4) (U : Frame n k) (hU : IsMaximizingFrame U)
    (hwin : ReciprocalWindow q U) (hdensity : ActualClassDensity U q)
    (hincidence : (1/2 : ℝ) * ∑ c : RowClass U, ∑ d : RowClass U,
      classWeight U c d * pairAngularCost (rowClassMass U c) (rowClassMass U d)
        (rowClassAngle U c d) ≤ slabDeficit U)
    (hpositive : ∃ c d : RowClass U, 0 < classWeight U c d) :
    groupedEntropy q (rowClassMultiplicity U) (rowClassLeverage U) +
      (1 : ℝ)/4000*((1/2 : ℝ)*∑ c : RowClass U, ∑ d : RowClass U, classWeight U c d) <
        slabDeficit U := by
  have hq₂ : 2 ≤ q := by rcases hq with rfl | rfl | rfl <;> omega
  have hrep := rowReplacement_of_maximizing_window q hq₂ U hU hwin
  apply groupedDeficitReduction (actualGroupedConstraints_of_density q hq₂ U hU hwin hdensity)
    hq (slabDeficit U) _ hpositive
  simpa only [rowClassMass_eq_multiplicity_mul_leverage U hrep] using hincidence

/-- Quantitative strict ratio gain for a maximizing frame with interacting classes,
under the stated density and global incidence bounds. -/
theorem log_ratio_gt_class_surplus {n k : ℕ} (hk : 1 ≤ k) (hkn : k ≤ n)
    (hq : n/k=2 ∨ n/k=3 ∨ n/k=4) (U : Frame n k) (hU : IsMaximizingFrame U)
    (hwin : ReciprocalWindow (n/k) U) (hdensity : ActualClassDensity U (n/k))
    (hincidence : (1/2 : ℝ) * ∑ c : RowClass U, ∑ d : RowClass U,
      classWeight U c d * pairAngularCost (rowClassMass U c) (rowClassMass U d)
        (rowClassAngle U c d) ≤ slabDeficit U)
    (hpositive : ∃ c d : RowClass U, 0 < classWeight U c d) :
    (1 : ℝ)/4000*((1/2 : ℝ)*∑ c : RowClass U, ∑ d : RowClass U, classWeight U c d) <
      Real.log (sharpValue n k / sectionVolume U) := by
  have hq₂ : 2 ≤ n/k := by rcases hq with h | h | h <;> omega
  have hrep := rowReplacement_of_maximizing_window (n/k) hq₂ U hU hwin
  have h := actualGroupedDeficitReduction (n/k) hq U hU hwin hdensity hincidence hpositive
  rw [← raw_entropy_eq_actualGrouped (n/k) U hrep hwin] at h
  rw [log_target_ratio hk hkn U hwin]
  linarith

theorem sectionVolume_lt_sharp_of_interacting_classes {n k : ℕ}
    (hk : 1 ≤ k) (hkn : k ≤ n) (hq : n/k=2 ∨ n/k=3 ∨ n/k=4)
    (U : Frame n k) (hU : IsMaximizingFrame U) (hwin : ReciprocalWindow (n/k) U)
    (hdensity : ActualClassDensity U (n/k))
    (hincidence : (1/2 : ℝ) * ∑ c : RowClass U, ∑ d : RowClass U,
      classWeight U c d * pairAngularCost (rowClassMass U c) (rowClassMass U d)
        (rowClassAngle U c d) ≤ slabDeficit U)
    (hpositive : ∃ c d : RowClass U, 0 < classWeight U c d) :
    sectionVolume U < sharpValue n k := by
  have hlog := log_ratio_gt_class_surplus hk hkn hq U hU hwin hdensity hincidence hpositive
  have hsum : 0 ≤ ∑ c : RowClass U, ∑ d : RowClass U, classWeight U c d :=
    Finset.sum_nonneg (fun c _ => Finset.sum_nonneg (fun d _ => classWeight_nonneg U c d))
  have hp : 0 < Real.log (sharpValue n k / sectionVolume U) := by nlinarith
  have hratio := (Real.log_pos_iff (div_nonneg (sharpValue_nonneg _ _) (sectionVolume_pos U).le)).mp hp
  exact (one_lt_div (sectionVolume_pos U)).mp hratio

theorem classWeights_zero_of_maximizing_smallQuotient {n k : ℕ}
    (hk : 1 ≤ k) (hkn : k ≤ n) (hq : n/k=2 ∨ n/k=3 ∨ n/k=4)
    (U : Frame n k) (hU : IsMaximizingFrame U) (hwin : ReciprocalWindow (n/k) U)
    (hdensity : ActualClassDensity U (n/k))
    (hincidence : (1/2 : ℝ) * ∑ c : RowClass U, ∑ d : RowClass U,
      classWeight U c d * pairAngularCost (rowClassMass U c) (rowClassMass U d)
        (rowClassAngle U c d) ≤ slabDeficit U) :
    ∀ c d : RowClass U, classWeight U c d = 0 := by
  intro c d
  by_contra hne
  have hw : 0 < classWeight U c d := lt_of_le_of_ne (classWeight_nonneg U c d) (Ne.symm hne)
  have hlt := sectionVolume_lt_sharp_of_interacting_classes hk hkn hq U hU hwin
    hdensity hincidence ⟨c,d,hw⟩
  have hmax := hU (balancedFrame hk hkn)
  rw [balancedFrame_volume] at hmax
  exact (not_lt_of_ge hmax) hlt

theorem unitRows_inner_sq_eq_classAngle {n k : ℕ} (U : Frame n k)
    (i j : ActiveRow U) :
    (inner ℝ (unitRow U i) (unitRow U j))^2 = rowClassAngle U (rowClass U i) (rowClass U j) := by
  calc
    _ = (inner ℝ (rowClassUnit U (rowClass U i)) (unitRow U j))^2 :=
      unitRow_inner_sq_eq_classUnit U i (unitRow U j)
    _ = (inner ℝ (unitRow U j) (rowClassUnit U (rowClass U i)))^2 := by rw [real_inner_comm]
    _ = (inner ℝ (rowClassUnit U (rowClass U j)) (rowClassUnit U (rowClass U i)))^2 :=
      unitRow_inner_sq_eq_classUnit U j (rowClassUnit U (rowClass U i))
    _ = _ := by unfold rowClassAngle; rw [real_inner_comm]

theorem gramAngularDefect_zero_of_classWeights_zero {n k : ℕ} (U : Frame n k)
    (hpos : ∀ i : Fin n, 0 < leverage U i)
    (hzero : ∀ c d : RowClass U, classWeight U c d = 0) : gramAngularDefect U = 0 := by
  apply (gramAngularDefect_eq_zero_iff U).mpr
  intro i j
  let a : ActiveRow U := ⟨i,hpos i⟩
  let b : ActiveRow U := ⟨j,hpos j⟩
  by_cases hab : rowClass U a = rowClass U b
  · exact Or.inr (gramProjection_sq_of_rowClass_eq U a b hab)
  · left
    have hw := hzero (rowClass U a) (rowClass U b)
    rw [classWeight_eq_mass_mul_angle U _ _ hab] at hw
    have hm : 0 < rowClassMass U (rowClass U a) * rowClassMass U (rowClass U b) :=
      mul_pos (rowClassMass_pos U _) (rowClassMass_pos U _)
    have hs : rowClassAngle U (rowClass U a) (rowClass U b) = 0 :=
      (mul_eq_zero.mp hw).resolve_left (ne_of_gt hm)
    have hraw := gramProjection_sq_unitRows U a b
    rw [unitRows_inner_sq_eq_classAngle,hs,mul_zero] at hraw
    exact sq_eq_zero_iff.mp hraw

/-- Actual signed balanced-block classification of a small-quotient maximizer,
conditional only on the displayed reciprocal window, density, and incidence inputs. -/
theorem isBalancedSection_of_maximizing_smallQuotient {n k : ℕ}
    (hk : 1 ≤ k) (hkn : k ≤ n) (hq : n/k=2 ∨ n/k=3 ∨ n/k=4)
    (U : Frame n k) (hU : IsMaximizingFrame U) (hwin : ReciprocalWindow (n/k) U)
    (hdensity : ActualClassDensity U (n/k))
    (hincidence : (1/2 : ℝ) * ∑ c : RowClass U, ∑ d : RowClass U,
      classWeight U c d * pairAngularCost (rowClassMass U c) (rowClassMass U d)
        (rowClassAngle U c d) ≤ slabDeficit U) : IsBalancedSection U := by
  have hq₂ : 2 ≤ n/k := by rcases hq with h | h | h <;> omega
  have hrep := rowReplacement_of_maximizing_window (n/k) hq₂ U hU hwin
  have hw := classWeights_zero_of_maximizing_smallQuotient hk hkn hq U hU hwin hdensity hincidence
  have hzero := gramAngularDefect_zero_of_classWeights_zero U
    (reciprocalWindow_pos (n/k) U hwin) hw
  exact isBalancedSection_of_rowReplacement_zeroAngular hk hkn U hrep hwin hzero

theorem sectionVolume_eq_sharp_of_maximizing_smallQuotient {n k : ℕ}
    (hk : 1 ≤ k) (hkn : k ≤ n) (hq : n/k=2 ∨ n/k=3 ∨ n/k=4)
    (U : Frame n k) (hU : IsMaximizingFrame U) (hwin : ReciprocalWindow (n/k) U)
    (hdensity : ActualClassDensity U (n/k))
    (hincidence : (1/2 : ℝ) * ∑ c : RowClass U, ∑ d : RowClass U,
      classWeight U c d * pairAngularCost (rowClassMass U c) (rowClassMass U d)
        (rowClassAngle U c d) ≤ slabDeficit U) : sectionVolume U = sharpValue n k :=
  sectionVolume_eq_sharp_of_isBalancedSection U
    (isBalancedSection_of_maximizing_smallQuotient hk hkn hq U hU hwin hdensity hincidence)

#print axioms actualGroupedConstraints_of_density
#print axioms actualGroupedDeficitReduction
#print axioms log_ratio_gt_class_surplus
#print axioms classWeights_zero_of_maximizing_smallQuotient
#print axioms isBalancedSection_of_maximizing_smallQuotient
#print axioms sectionVolume_eq_sharp_of_maximizing_smallQuotient
end CubeSections.Certificates
