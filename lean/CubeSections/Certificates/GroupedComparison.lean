import CubeSections.Certificates.AllPairs
import CubeSections.Certificates.DirectStripExtraction
import CubeSections.LinearAlgebra.GroupedCharges

/-! Conditional small-quotient finite assembly with explicit incidence and
geometric replacement hypotheses. -/
noncomputable section
open Finset
namespace CubeSections.Certificates

theorem class_lt_one_of_positive_weight {ι : Type*} [Fintype ι]
    (w : ι → ι → ℝ) (a : ι → ℝ) (hw : ∀ i j, 0 ≤ w i j)
    (ha : ∀ i, a i ≤ 1) (hdegree : ∀ i, ∑ j, w i j = a i*(1-a i))
    (i j : ι) (hij : 0 < w i j) : a i < 1 := by
  by_contra h
  have heq : a i = 1 := le_antisymm (ha i) (le_of_not_gt h)
  have hzero : ∑ j, w i j = 0 := by rw [hdegree, heq]; ring
  have hwzero := CubeSections.weight_zero_of_degree_zero w hw i hzero j
  linarith

theorem multiplicity_le_quotient_of_class_lt (q m : ℕ) (c : ℝ)
    (hc : 1 / ((q : ℝ)+1) ≤ c) (hclass : (m : ℝ)*c < 1) : m ≤ q := by
  have hmul := mul_le_mul_of_nonneg_left hc (Nat.cast_nonneg m : (0 : ℝ) ≤ m)
  have hfrac : (m : ℝ)/((q : ℝ)+1) < 1 := by
    simpa only [mul_one_div] using hmul.trans_lt hclass
  have hmR : (m : ℝ) < (q : ℝ)+1 :=
    (div_lt_one (by positivity : (0 : ℝ) < (q : ℝ)+1)).mp hfrac
  have hmN : m < q+1 := by exact_mod_cast hmR
  omega

structure GroupedFrameConstraints {ι : Type*} [Fintype ι]
    (q : ℕ) (m : ι → ℕ) (c : ι → ℝ) (w s : ι → ι → ℝ) : Prop where
  multiplicity_pos : ∀ i, 1 ≤ m i
  window : ∀ i, 1/((q : ℝ)+1) ≤ c i ∧ c i ≤ 1/(q : ℝ)
  class_le_one : ∀ i, (m i : ℝ)*c i ≤ 1
  weight_nonneg : ∀ i j, 0 ≤ w i j
  weight_symm : ∀ i j, w i j = w j i
  degree : ∀ i, ∑ j, w i j = ((m i : ℝ)*c i)*(1-(m i : ℝ)*c i)
  angle : ∀ i j, 0 < w i j → 0 < s i j ∧ s i j < 1
  projection : ∀ i j, 0 < w i j →
    s i j ≤ (1-(m i : ℝ)*c i)*(1-(m j : ℝ)*c j) /
      (((m i : ℝ)*c i)*((m j : ℝ)*c j))

structure GroupedConstraints {ι : Type*} [Fintype ι]
    (q : ℕ) (m : ι → ℕ) (c : ι → ℝ) (w s : ι → ι → ℝ) : Prop
    extends GroupedFrameConstraints q m c w s where
  strip : ∀ i j, 0 < w i j → SourceStripLaw ⟨q,m i,m j⟩ (c i) (c j) (s i j)

theorem GroupedFrameConstraints.withExactStrip {ι : Type*} [Fintype ι]
    {q : ℕ} {m : ι → ℕ} {c : ι → ℝ} {w s : ι → ι → ℝ}
    (h : GroupedFrameConstraints q m c w s) (hq : 2 ≤ q)
    (hrep : ∀ i j, 0 < w i j → |(c i)⁻¹-(c j)⁻¹| ≤ 1-s i j)
    (hexact : ∀ i j, 0 < w i j → SourceExactStripLaw ⟨q,m i,m j⟩ (c i) (c j) (s i j)) :
    GroupedConstraints q m c w s := by
  refine ⟨h, ?_⟩
  intro i j hij
  have hi := class_lt_one_of_positive_weight w (fun i => (m i : ℝ)*c i)
    h.weight_nonneg h.class_le_one h.degree i j hij
  have hji : 0 < w j i := by rw [← h.weight_symm i j]; exact hij
  have hj := class_lt_one_of_positive_weight w (fun i => (m i : ℝ)*c i)
    h.weight_nonneg h.class_le_one h.degree j i hji
  have hcpos : 0 < c i := (one_div_pos.mpr (by positivity : (0 : ℝ) < (q : ℝ)+1)).trans_le (h.window i).1
  have hdpos : 0 < c j := (one_div_pos.mpr (by positivity : (0 : ℝ) < (q : ℝ)+1)).trans_le (h.window j).1
  exact sourceDirectStrip_of_exact hq
    (multiplicity_le_quotient_of_class_lt q (m i) (c i) (h.window i).1 hi)
    (multiplicity_le_quotient_of_class_lt q (m j) (c j) (h.window j).1 hj)
    (h.window i).1 (h.window i).2 (h.window j).1 (h.window j).2
    (h.angle i j hij).1 (h.angle i j hij).2
    (rowDiscrepancy_of_reciprocal hcpos hdpos (hrep i j hij)) (hexact i j hij)

theorem GroupedConstraints.positive_pair_comparison {ι : Type*} [Fintype ι]
    {q : ℕ} {m : ι → ℕ} {c : ι → ℝ} {w s : ι → ι → ℝ}
    (h : GroupedConstraints q m c w s) (hq : q=2 ∨ q=3 ∨ q=4)
    (i j : ι) (hij : 0 < w i j) :
    sourceCharge q (m i) (c i) + sourceCharge q (m j) (c j) + (1 : ℝ)/4000 <
      pairAngularCost ((m i : ℝ)*c i) ((m j : ℝ)*c j) (s i j) := by
  have hi := class_lt_one_of_positive_weight w (fun i => (m i : ℝ)*c i)
    h.weight_nonneg h.class_le_one h.degree i j hij
  have hji : 0 < w j i := by rw [← h.weight_symm i j]; exact hij
  have hj := class_lt_one_of_positive_weight w (fun i => (m i : ℝ)*c i)
    h.weight_nonneg h.class_le_one h.degree j i hji
  exact smallQuotientPairComparison q (m i) (m j) hq (h.multiplicity_pos i)
    (multiplicity_le_quotient_of_class_lt q (m i) (c i) (h.window i).1 hi)
    (h.multiplicity_pos j)
    (multiplicity_le_quotient_of_class_lt q (m j) (c j) (h.window j).1 hj)
    (c i) (c j) (s i j) (h.window i).1 (h.window i).2 (h.window j).1 (h.window j).2
    (h.angle i j hij).1 (h.angle i j hij).2 (h.projection i j hij) (h.strip i j hij)

theorem groupedDeficitReduction {ι : Type*} [Fintype ι]
    {q : ℕ} {m : ι → ℕ} {c : ι → ℝ} {w s : ι → ι → ℝ}
    (h : GroupedConstraints q m c w s) (hq : q=2 ∨ q=3 ∨ q=4)
    (δ : ℝ) (hincidence : (1 / 2 : ℝ) * ∑ i, ∑ j, w i j *
      pairAngularCost ((m i : ℝ)*c i) ((m j : ℝ)*c j) (s i j) ≤ δ)
    (hpositive : ∃ i j, 0 < w i j) :
    CubeSections.groupedEntropy q m c + (1 : ℝ)/4000 * ((1/2 : ℝ)*∑ i, ∑ j, w i j) < δ := by
  have hqpos : 1 ≤ q := by rcases hq with rfl | rfl | rfl <;> omega
  have hidentity := CubeSections.grouped_charge_identity q hqpos m c w h.window
    h.class_le_one h.weight_symm h.degree
  have hstrict := CubeSections.grouped_strict_comparison w
    (fun i => sourceCharge q (m i) (c i))
    (fun i j => pairAngularCost ((m i : ℝ)*c i) ((m j : ℝ)*c j) (s i j))
    ((1 : ℝ)/4000) h.weight_nonneg (h.positive_pair_comparison hq) hpositive
  rw [← hidentity] at hstrict
  exact hstrict.trans_le hincidence

theorem groupedEntropy_lt_deficit {ι : Type*} [Fintype ι]
    {q : ℕ} {m : ι → ℕ} {c : ι → ℝ} {w s : ι → ι → ℝ}
    (h : GroupedConstraints q m c w s) (hq : q=2 ∨ q=3 ∨ q=4)
    (δ : ℝ) (hincidence : (1 / 2 : ℝ) * ∑ i, ∑ j, w i j *
      pairAngularCost ((m i : ℝ)*c i) ((m j : ℝ)*c j) (s i j) ≤ δ)
    (hpositive : ∃ i j, 0 < w i j) : CubeSections.groupedEntropy q m c < δ := by
  have hstrict := groupedDeficitReduction h hq δ hincidence hpositive
  have hsum : 0 ≤ ∑ i, ∑ j, w i j := by
    exact Finset.sum_nonneg (fun i _ => Finset.sum_nonneg (fun j _ => h.weight_nonneg i j))
  nlinarith

theorem groupedDeficitReduction_of_exact {ι : Type*} [Fintype ι]
    {q : ℕ} {m : ι → ℕ} {c : ι → ℝ} {w s : ι → ι → ℝ}
    (h : GroupedFrameConstraints q m c w s) (hq : q=2 ∨ q=3 ∨ q=4)
    (hrep : ∀ i j, 0 < w i j → |(c i)⁻¹-(c j)⁻¹| ≤ 1-s i j)
    (hexact : ∀ i j, 0 < w i j → SourceExactStripLaw ⟨q,m i,m j⟩ (c i) (c j) (s i j))
    (δ : ℝ) (hincidence : (1 / 2 : ℝ) * ∑ i, ∑ j, w i j *
      pairAngularCost ((m i : ℝ)*c i) ((m j : ℝ)*c j) (s i j) ≤ δ)
    (hpositive : ∃ i j, 0 < w i j) :
    CubeSections.groupedEntropy q m c + (1 : ℝ)/4000 * ((1/2 : ℝ)*∑ i, ∑ j, w i j) < δ := by
  have hq₂ : 2 ≤ q := by rcases hq with rfl | rfl | rfl <;> omega
  exact groupedDeficitReduction (h.withExactStrip hq₂ hrep hexact) hq δ hincidence hpositive

theorem pairAngularCost_symm (A B s : ℝ) : pairAngularCost A B s = pairAngularCost B A s := by
  unfold pairAngularCost
  congr 1
  ring

theorem incidence_half_sum_eq_upper {ι : Type*} [Fintype ι] [LinearOrder ι]
    (w : ι → ι → ℝ) (a : ι → ℝ) (s : ι → ι → ℝ)
    (hw : ∀ i j, w i j = w j i) (hs : ∀ i j, s i j = s j i)
    (hdiag : ∀ i, w i i = 0) :
    (1/2 : ℝ) * ∑ i, ∑ j, w i j * pairAngularCost (a i) (a j) (s i j) =
      ∑ i, ∑ j ∈ Finset.univ.filter (fun j => i < j),
        w i j * pairAngularCost (a i) (a j) (s i j) := by
  apply CubeSections.half_symmetric_sum_eq_upper
  · intro i j
    rw [hw i j, hs i j, pairAngularCost_symm (a i) (a j) (s j i)]
  · intro i
    rw [hdiag i, zero_mul]

theorem groupedDeficitReduction_upper {ι : Type*} [Fintype ι] [LinearOrder ι]
    {q : ℕ} {m : ι → ℕ} {c : ι → ℝ} {w s : ι → ι → ℝ}
    (h : GroupedConstraints q m c w s) (hq : q=2 ∨ q=3 ∨ q=4)
    (hsymm : ∀ i j, s i j = s j i) (hdiag : ∀ i, w i i = 0)
    (δ : ℝ) (hincidence : (∑ i, ∑ j ∈ Finset.univ.filter (fun j => i < j),
      w i j * pairAngularCost ((m i : ℝ)*c i) ((m j : ℝ)*c j) (s i j)) ≤ δ)
    (hpositive : ∃ i j, 0 < w i j) :
    CubeSections.groupedEntropy q m c + (1 : ℝ)/4000 * ((1/2 : ℝ)*∑ i, ∑ j, w i j) < δ := by
  apply groupedDeficitReduction h hq δ _ hpositive
  rw [incidence_half_sum_eq_upper w (fun i => (m i : ℝ)*c i) s h.weight_symm hsymm hdiag]
  exact hincidence

#print axioms groupedDeficitReduction
#print axioms groupedEntropy_lt_deficit
#print axioms groupedDeficitReduction_of_exact
#print axioms groupedDeficitReduction_upper
end CubeSections.Certificates
