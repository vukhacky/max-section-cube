import CubeSections.LinearAlgebra.Gram
import CubeSections.Analysis.SharpEntropy
import CubeSections.Certificates.SourceSemantics
import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-! Exact grouped entropy accounting and finite strict-sum assembly.
Unit classes have zero degree and zero entropy. No zero denominator is cancelled.
-/

noncomputable section
open Finset
namespace CubeSections

theorem symmetric_degree_charge_identity {ι : Type*} [Fintype ι]
    (w : ι → ι → ℝ) (degree H : ι → ℝ)
    (hsymm : ∀ i j, w i j = w j i)
    (hdegree : ∀ i, ∑ j, w i j = degree i) :
    ∑ i, degree i * H i = (1 / 2 : ℝ) * ∑ i, ∑ j, w i j * (H i + H j) := by
  have hfirst : (∑ i, ∑ j, w i j * H i) = ∑ i, degree i * H i := by
    simp_rw [← Finset.sum_mul, hdegree]
  have hsecond : (∑ i, ∑ j, w i j * H j) = ∑ i, degree i * H i := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro j _
    rw [← Finset.sum_mul]
    congr 1
    calc
      ∑ i, w i j = ∑ i, w j i := Finset.sum_congr rfl (fun i _ => hsymm i j)
      _ = degree j := hdegree j
  simp_rw [mul_add, Finset.sum_add_distrib]
  rw [hfirst, hsecond]
  ring

theorem entropyExcess_zero_of_unit_class (q m : ℕ) (hq : 1 ≤ q) (c : ℝ)
    (hc₀ : 1 / ((q : ℝ) + 1) ≤ c) (hc₁ : c ≤ 1 / (q : ℝ))
    (hunit : (m : ℝ) * c = 1) : entropyExcess q c = 0 := by
  have hq₀ : (0 : ℝ) < q := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hq)
  have hcpos : 0 < c := (one_div_pos.mpr (by positivity : (0 : ℝ) < (q : ℝ) + 1)).trans_le hc₀
  have hqc : (q : ℝ) * c ≤ 1 := by
    have h := (le_div_iff₀ hq₀).mp hc₁
    nlinarith
  have hqpc : 1 ≤ ((q : ℝ) + 1) * c := by
    have h := (div_le_iff₀ (by positivity : (0 : ℝ) < (q : ℝ) + 1)).mp hc₀
    nlinarith
  have hqmR : (q : ℝ) ≤ m := (mul_le_mul_iff_left₀ hcpos).mp (by linarith)
  have hmqR : (m : ℝ) ≤ (q : ℝ) + 1 := (mul_le_mul_iff_left₀ hcpos).mp (by linarith)
  have hqm : q ≤ m := by exact_mod_cast hqmR
  have hmq : m ≤ q + 1 := by exact_mod_cast hmqR
  have hm : m = q ∨ m = q + 1 := by omega
  rcases hm with hm | hm
  · subst m
    have hc : c = 1 / (q : ℝ) := (eq_div_iff (ne_of_gt hq₀)).mpr (by nlinarith)
    rw [hc, entropyExcess_right q hq]
  · subst m
    have hc : c = 1 / ((q : ℝ) + 1) :=
      (eq_div_iff (by positivity : (q : ℝ) + 1 ≠ 0)).mpr (by simpa [mul_comm] using hunit)
    rw [hc, entropyExcess_left q hq]

theorem degree_mul_charge (q m : ℕ) (hq : 1 ≤ q) (c : ℝ)
    (hc : 0 < c) (hclass : (m : ℝ) * c < 1) :
    ((m : ℝ) * c) * (1 - (m : ℝ) * c) * Certificates.sourceCharge q m c =
      (m : ℝ) * entropyExcess q c / 2 := by
  rw [Certificates.sourceCharge_eq_of_class_lt q m hq c hclass]
  unfold Certificates.chargeReal
  have hc₀ : c ≠ 0 := ne_of_gt hc
  have hd₀ : 1 - (m : ℝ) * c ≠ 0 := ne_of_gt (sub_pos.mpr hclass)
  field_simp
  <;> ring

theorem degree_mul_charge_in_window (q m : ℕ) (hq : 1 ≤ q) (c : ℝ)
    (hc₀ : 1 / ((q : ℝ) + 1) ≤ c) (hc₁ : c ≤ 1 / (q : ℝ))
    (hclass : (m : ℝ) * c ≤ 1) :
    ((m : ℝ) * c) * (1 - (m : ℝ) * c) * Certificates.sourceCharge q m c =
      (m : ℝ) * entropyExcess q c / 2 := by
  rcases hclass.eq_or_lt with heq | hlt
  · rw [heq, entropyExcess_zero_of_unit_class q m hq c hc₀ hc₁ heq]
    ring
  · have hc : 0 < c := (one_div_pos.mpr (by positivity : (0 : ℝ) < (q : ℝ) + 1)).trans_le hc₀
    exact degree_mul_charge q m hq c hc hlt

def groupedEntropy {ι : Type*} [Fintype ι] (q : ℕ) (m : ι → ℕ) (c : ι → ℝ) : ℝ :=
  (1 / 2 : ℝ) * ∑ i, (m i : ℝ) * entropyExcess q (c i)

theorem grouped_charge_identity {ι : Type*} [Fintype ι]
    (q : ℕ) (hq : 1 ≤ q) (m : ι → ℕ) (c : ι → ℝ) (w : ι → ι → ℝ)
    (hwindow : ∀ i, 1 / ((q : ℝ) + 1) ≤ c i ∧ c i ≤ 1 / (q : ℝ))
    (hclass : ∀ i, (m i : ℝ) * c i ≤ 1)
    (hsymm : ∀ i j, w i j = w j i)
    (hdegree : ∀ i, ∑ j, w i j = ((m i : ℝ) * c i) * (1 - (m i : ℝ) * c i)) :
    groupedEntropy q m c = (1 / 2 : ℝ) * ∑ i, ∑ j, w i j *
      (Certificates.sourceCharge q (m i) (c i) + Certificates.sourceCharge q (m j) (c j)) := by
  have h := symmetric_degree_charge_identity w
    (fun i => ((m i : ℝ) * c i) * (1 - (m i : ℝ) * c i))
    (fun i => Certificates.sourceCharge q (m i) (c i)) hsymm hdegree
  have hleft : (∑ i, ((m i : ℝ) * c i) * (1 - (m i : ℝ) * c i) *
      Certificates.sourceCharge q (m i) (c i)) = groupedEntropy q m c := by
    simp_rw [degree_mul_charge_in_window q _ hq _ (hwindow _).1 (hwindow _).2 (hclass _)]
    simp only [groupedEntropy, div_eq_mul_inv, ← Finset.sum_mul]
    ring
  rw [hleft] at h
  exact h

def groupedGramWeight {n k : ℕ} (U : Frame n k) (i j : Fin n) : ℝ :=
  if i = j then 0 else gramProjection U i j ^ 2

theorem groupedGramWeight_nonneg {n k : ℕ} (U : Frame n k) (i j : Fin n) :
    0 ≤ groupedGramWeight U i j := by
  unfold groupedGramWeight
  split_ifs
  · rfl
  · exact sq_nonneg _

theorem groupedGramWeight_symm {n k : ℕ} (U : Frame n k) (i j : Fin n) :
    groupedGramWeight U i j = groupedGramWeight U j i := by
  by_cases h : i = j
  · subst j
    rfl
  · simp only [groupedGramWeight, h, Ne.symm h, if_false]
    rw [gramProjection_symm U i j]

theorem groupedGramWeight_degree {n k : ℕ} (U : Frame n k) (i : Fin n) :
    ∑ j, groupedGramWeight U i j = leverage U i * (1 - leverage U i) := by
  have h := Finset.sum_erase_add (Finset.univ : Finset (Fin n))
    (fun j => groupedGramWeight U i j) (Finset.mem_univ i)
  have hzero : groupedGramWeight U i i = 0 := by simp [groupedGramWeight]
  rw [hzero, add_zero] at h
  rw [← h]
  have heq : (∑ j ∈ (Finset.univ : Finset (Fin n)).erase i, groupedGramWeight U i j) =
      ∑ j ∈ (Finset.univ : Finset (Fin n)).erase i, gramProjection U i j ^ 2 := by
    apply Finset.sum_congr rfl
    intro j hj
    simp [groupedGramWeight, Ne.symm (Finset.mem_erase.mp hj).1]
  rw [heq]
  exact gramProjection_offdiag_sq_sum U i

theorem frame_grouped_charge_identity {n k : ℕ} (U : Frame n k)
    (q : ℕ) (hq : 1 ≤ q) (m : Fin n → ℕ) (c : Fin n → ℝ)
    (hwindow : ∀ i, 1 / ((q : ℝ) + 1) ≤ c i ∧ c i ≤ 1 / (q : ℝ))
    (hleverage : ∀ i, leverage U i = (m i : ℝ) * c i) :
    groupedEntropy q m c = (1 / 2 : ℝ) * ∑ i, ∑ j, groupedGramWeight U i j *
      (Certificates.sourceCharge q (m i) (c i) + Certificates.sourceCharge q (m j) (c j)) := by
  apply grouped_charge_identity q hq m c (groupedGramWeight U) hwindow
  · intro i
    rw [← hleverage i]
    exact leverage_le_one U i
  · exact groupedGramWeight_symm U
  · intro i
    rw [groupedGramWeight_degree, hleverage]

theorem strict_weighted_sum {ι : Type*} (s : Finset ι) (w f g : ι → ℝ) (ε : ℝ)
    (hw : ∀ i ∈ s, 0 ≤ w i)
    (hgap : ∀ i ∈ s, 0 < w i → f i + ε < g i)
    (hpos : ∃ i ∈ s, 0 < w i) :
    (∑ i ∈ s, w i * f i) + ε * (∑ i ∈ s, w i) < ∑ i ∈ s, w i * g i := by
  have hle : ∀ i ∈ s, w i * (f i + ε) ≤ w i * g i := by
    intro i hi
    rcases (hw i hi).eq_or_lt with hz | hp
    · rw [← hz]
      simp
    · exact (mul_lt_mul_of_pos_left (hgap i hi hp) hp).le
  have hlt : ∃ i ∈ s, w i * (f i + ε) < w i * g i := by
    obtain ⟨i, hi, hp⟩ := hpos
    exact ⟨i, hi, mul_lt_mul_of_pos_left (hgap i hi hp) hp⟩
  have h := Finset.sum_lt_sum hle hlt
  simp_rw [mul_add, Finset.sum_add_distrib] at h
  rw [← Finset.sum_mul] at h
  simpa only [mul_comm ε] using h

theorem grouped_strict_comparison {ι : Type*} [Fintype ι]
    (w : ι → ι → ℝ) (H : ι → ℝ) (L : ι → ι → ℝ) (ε : ℝ)
    (hw : ∀ i j, 0 ≤ w i j)
    (hgap : ∀ i j, 0 < w i j → H i + H j + ε < L i j)
    (hpos : ∃ i j, 0 < w i j) :
    (1 / 2 : ℝ) * (∑ i, ∑ j, w i j * (H i + H j)) +
      ε * ((1 / 2 : ℝ) * ∑ i, ∑ j, w i j) <
      (1 / 2 : ℝ) * ∑ i, ∑ j, w i j * L i j := by
  classical
  have h := strict_weighted_sum (Finset.univ : Finset (ι × ι))
    (fun p => w p.1 p.2) (fun p => H p.1 + H p.2) (fun p => L p.1 p.2) ε
    (fun p _ => hw p.1 p.2) (fun p _ hp => hgap p.1 p.2 hp)
    (by obtain ⟨i, j, h⟩ := hpos; exact ⟨(i,j), Finset.mem_univ _, h⟩)
  simp only [Fintype.sum_prod_type] at h
  linarith

theorem half_symmetric_sum_eq_upper {ι : Type*} [Fintype ι] [LinearOrder ι]
    (f : ι → ι → ℝ) (hsymm : ∀ i j, f i j = f j i) (hdiag : ∀ i, f i i = 0) :
    (1 / 2 : ℝ) * ∑ i, ∑ j, f i j =
      ∑ i, ∑ j ∈ Finset.univ.filter (fun j => i < j), f i j := by
  have hpoint (i j : ι) : f i j =
      (if i < j then f i j else 0) + (if j < i then f i j else 0) := by
    rcases lt_trichotomy i j with h | h | h
    · simp [h, not_lt.mpr h.le]
    · subst j
      simp [hdiag]
    · simp [h, not_lt.mpr h.le]
  have hsplit : (∑ i, ∑ j, f i j) =
      (∑ i, ∑ j, if i < j then f i j else 0) +
      (∑ i, ∑ j, if j < i then f i j else 0) := by
    calc
      _ = ∑ i, ∑ j, ((if i < j then f i j else 0) +
          (if j < i then f i j else 0)) := by
        apply Finset.sum_congr rfl
        intro i _
        exact Finset.sum_congr rfl (fun j _ => hpoint i j)
      _ = _ := by simp_rw [Finset.sum_add_distrib]
  have hswap : (∑ i, ∑ j, if j < i then f i j else 0) =
      ∑ i, ∑ j, if i < j then f i j else 0 := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro j _
    apply Finset.sum_congr rfl
    intro i _
    rw [hsymm i j]
  simp_rw [Finset.sum_filter]
  rw [hsplit, hswap]
  ring

theorem grouped_charge_identity_positive_edges {ι : Type*} [Fintype ι] [LinearOrder ι]
    (q : ℕ) (hq : 1 ≤ q) (m : ι → ℕ) (c : ι → ℝ) (w : ι → ι → ℝ)
    (hwindow : ∀ i, 1 / ((q : ℝ) + 1) ≤ c i ∧ c i ≤ 1 / (q : ℝ))
    (hclass : ∀ i, (m i : ℝ) * c i ≤ 1)
    (hsymm : ∀ i j, w i j = w j i) (hdiag : ∀ i, w i i = 0)
    (hw : ∀ i j, 0 ≤ w i j)
    (hdegree : ∀ i, ∑ j, w i j = ((m i : ℝ) * c i) * (1 - (m i : ℝ) * c i)) :
    groupedEntropy q m c = ∑ i, ∑ j ∈ Finset.univ.filter (fun j => i < j ∧ 0 < w i j),
      w i j * (Certificates.sourceCharge q (m i) (c i) +
        Certificates.sourceCharge q (m j) (c j)) := by
  rw [grouped_charge_identity q hq m c w hwindow hclass hsymm hdegree,
    half_symmetric_sum_eq_upper
      (fun i j => w i j * (Certificates.sourceCharge q (m i) (c i) +
        Certificates.sourceCharge q (m j) (c j)))
      (by intro i j; rw [hsymm i j, add_comm]) (by intro i; rw [hdiag i, zero_mul])]
  apply Finset.sum_congr rfl
  intro i _
  simp only [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro j _
  by_cases hij : i < j
  · by_cases hp : 0 < w i j
    · simp [hij, hp]
    · have hz : w i j = 0 := le_antisymm (le_of_not_gt hp) (hw i j)
      simp [hij, hp, hz]
  · simp [hij]

theorem raw_entropy_eq_grouped {n k r : ℕ} (U : Frame n k) (q : ℕ)
    (group : Fin n → Fin r) (m : Fin r → ℕ) (c : Fin r → ℝ)
    (hcard : ∀ i, (Finset.univ.filter (fun j => group j = i)).card = m i)
    (hleverage : ∀ j, leverage U j = c (group j)) :
    (1 / 2 : ℝ) * ∑ j, entropyExcess q (leverage U j) = groupedEntropy q m c := by
  have h := (Finset.sum_fiberwise' (Finset.univ : Finset (Fin n)) group
    (fun i => entropyExcess q (c i))).symm
  simp only [hleverage]
  unfold groupedEntropy
  congr 1
  simpa only [Finset.sum_const, hcard, nsmul_eq_mul] using h

theorem degree_transport_identity {ι : Type*} [Fintype ι]
    (w : ι → ι → ℝ) (a e : ι → ℝ)
    (hsymm : ∀ i j, w i j = w j i) (ha : ∀ i, a i ≤ 1)
    (hdegree : ∀ i, ∑ j, w i j = a i * (1-a i)) :
    (1 / 2 : ℝ) * ∑ i, ∑ j, w i j *
      (e i ^ 2 / (2*(1-a i)) + e j ^ 2 / (2*(1-a j))) =
      (1 / 2 : ℝ) * ∑ i, if a i < 1 then a i * e i ^ 2 else 0 := by
  have hpoint (i : ι) : a i * (1-a i) * (e i ^ 2 / (2*(1-a i))) =
      (1 / 2 : ℝ) * (if a i < 1 then a i * e i ^ 2 else 0) := by
    by_cases hi : a i < 1
    · rw [if_pos hi]
      have hd : 1-a i ≠ 0 := ne_of_gt (sub_pos.mpr hi)
      field_simp
      <;> ring
    · have heq : a i = 1 := le_antisymm (ha i) (le_of_not_gt hi)
      simp [heq]
  rw [← symmetric_degree_charge_identity w (fun i => a i*(1-a i))
    (fun i => e i ^ 2 / (2*(1-a i))) hsymm hdegree]
  simp_rw [hpoint]
  rw [Finset.mul_sum]

theorem degree_transport_le_total {ι : Type*} [Fintype ι]
    (w : ι → ι → ℝ) (a e : ι → ℝ)
    (hsymm : ∀ i j, w i j = w j i) (ha₀ : ∀ i, 0 ≤ a i) (ha₁ : ∀ i, a i ≤ 1)
    (hdegree : ∀ i, ∑ j, w i j = a i * (1-a i)) :
    (1 / 2 : ℝ) * ∑ i, ∑ j, w i j *
      (e i ^ 2 / (2*(1-a i)) + e j ^ 2 / (2*(1-a j))) ≤
      (1 / 2 : ℝ) * ∑ i, a i * e i ^ 2 := by
  rw [degree_transport_identity w a e hsymm ha₁ hdegree]
  apply mul_le_mul_of_nonneg_left _ (by norm_num : (0 : ℝ) ≤ 1/2)
  apply Finset.sum_le_sum
  intro i _
  split_ifs
  · exact le_rfl
  · exact mul_nonneg (ha₀ i) (sq_nonneg _)

theorem degree_transport_identity_upper {ι : Type*} [Fintype ι] [LinearOrder ι]
    (w : ι → ι → ℝ) (a e : ι → ℝ)
    (hsymm : ∀ i j, w i j = w j i) (hdiag : ∀ i, w i i = 0) (ha : ∀ i, a i ≤ 1)
    (hdegree : ∀ i, ∑ j, w i j = a i * (1-a i)) :
    (∑ i, ∑ j ∈ Finset.univ.filter (fun j => i < j), w i j *
      (e i ^ 2 / (2*(1-a i)) + e j ^ 2 / (2*(1-a j)))) =
      (1 / 2 : ℝ) * ∑ i, if a i < 1 then a i * e i ^ 2 else 0 := by
  rw [← half_symmetric_sum_eq_upper
    (fun i j => w i j * (e i ^ 2 / (2*(1-a i)) + e j ^ 2 / (2*(1-a j))))
    (by intro i j; rw [hsymm i j, add_comm]) (by intro i; rw [hdiag i, zero_mul])]
  exact degree_transport_identity w a e hsymm ha hdegree

theorem weight_zero_of_degree_zero {ι : Type*} [Fintype ι]
    (w : ι → ι → ℝ) (hw : ∀ i j, 0 ≤ w i j) (i : ι)
    (hdegree : ∑ j, w i j = 0) (j : ι) : w i j = 0 := by
  have h := Finset.single_le_sum (fun k (_ : k ∈ (Finset.univ : Finset ι)) => hw i k)
    (Finset.mem_univ j)
  rw [hdegree] at h
  exact le_antisymm h (hw i j)

#print axioms grouped_charge_identity
#print axioms frame_grouped_charge_identity
#print axioms grouped_strict_comparison
#print axioms grouped_charge_identity_positive_edges
#print axioms raw_entropy_eq_grouped
#print axioms degree_transport_identity
#print axioms degree_transport_le_total
#print axioms degree_transport_identity_upper

end CubeSections
