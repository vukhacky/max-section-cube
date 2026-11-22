import CubeSections.Geometry.RowVectors
import CubeSections.Integer.GramPacking
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-!
# Finite unoriented classes of the positive row support

Zero rows remain valid in the input frame. Only ActiveRow is normalized, and its
unit vectors are quotiented by equality up to sign. Class mass is a sum of
leverages, so its definition does not assume equal lengths within a class.
-/

noncomputable section
open Set Classical
open scoped BigOperators InnerProductSpace
namespace CubeSections

instance activeRowFintype {n k : ℕ} (U : Frame n k) : Fintype (ActiveRow U) :=
  inferInstanceAs (Fintype {i : Fin n // 0 < leverage U i})

def SignedParallel {n k : ℕ} (U : Frame n k) (i j : ActiveRow U) : Prop :=
  unitRow U i = unitRow U j ∨ unitRow U i = -unitRow U j

def activeRowSetoid {n k : ℕ} (U : Frame n k) : Setoid (ActiveRow U) where
  r := SignedParallel U
  iseqv :=
    { refl := fun _ => Or.inl rfl
      symm := by
        intro i j h
        rcases h with h | h
        · exact Or.inl h.symm
        · right
          rw [h]
          simp
      trans := by
        intro i j l hij hjl
        rcases hij with hij | hij <;> rcases hjl with hjl | hjl
        · exact Or.inl (hij.trans hjl)
        · exact Or.inr (hij.trans hjl)
        · right; rw [hij, hjl]
        · left; rw [hij, hjl, neg_neg] }

abbrev RowClass {n k : ℕ} (U : Frame n k) := Quotient (activeRowSetoid U)

instance rowClassFintype {n k : ℕ} (U : Frame n k) : Fintype (RowClass U) :=
  Fintype.ofFinite _

def rowClass {n k : ℕ} (U : Frame n k) (i : ActiveRow U) : RowClass U :=
  Quotient.mk _ i

theorem rowClass_eq_iff {n k : ℕ} (U : Frame n k) (i j : ActiveRow U) :
    rowClass U i = rowClass U j ↔ SignedParallel U i j := by
  constructor
  · intro h
    exact Quotient.exact h
  · intro h
    apply Quotient.sound
    exact h

theorem rowClass_surjective {n k : ℕ} (U : Frame n k) : Function.Surjective (rowClass U) := by
  intro c
  refine Quotient.inductionOn c (fun i => ?_)
  exact ⟨i, rfl⟩

def rowClassRep {n k : ℕ} (U : Frame n k) (c : RowClass U) : ActiveRow U :=
  Classical.choose (rowClass_surjective U c)

@[simp] theorem rowClass_rep {n k : ℕ} (U : Frame n k) (c : RowClass U) :
    rowClass U (rowClassRep U c) = c := Classical.choose_spec (rowClass_surjective U c)

def rowClassUnit {n k : ℕ} (U : Frame n k) (c : RowClass U) : E k :=
  unitRow U (rowClassRep U c)

theorem rowClassUnit_norm {n k : ℕ} (U : Frame n k) (c : RowClass U) :
    ‖rowClassUnit U c‖ = 1 := unitRow_norm U _

theorem unitRow_eq_signed_classUnit {n k : ℕ} (U : Frame n k) (i : ActiveRow U) :
    unitRow U i = rowClassUnit U (rowClass U i) ∨
      unitRow U i = -rowClassUnit U (rowClass U i) := by
  exact (rowClass_eq_iff U i (rowClassRep U (rowClass U i))).mp (by rw [rowClass_rep])

def rowClassMultiplicity {n k : ℕ} (U : Frame n k) (c : RowClass U) : ℕ :=
  (Finset.univ.filter (fun i : ActiveRow U => rowClass U i = c)).card

def rowClassMass {n k : ℕ} (U : Frame n k) (c : RowClass U) : ℝ :=
  ∑ i : ActiveRow U with rowClass U i = c, leverage U i.val

def rowClassLeverage {n k : ℕ} (U : Frame n k) (c : RowClass U) : ℝ :=
  leverage U (rowClassRep U c).val

theorem rowClassMultiplicity_pos {n k : ℕ} (U : Frame n k) (c : RowClass U) :
    0 < rowClassMultiplicity U c := by
  apply Finset.card_pos.mpr
  exact ⟨rowClassRep U c, by simp⟩

theorem rowClassMass_pos {n k : ℕ} (U : Frame n k) (c : RowClass U) :
    0 < rowClassMass U c := by
  exact Finset.sum_pos (fun i _ => i.property) ⟨rowClassRep U c, by simp⟩

theorem rowClassLeverage_pos {n k : ℕ} (U : Frame n k) (c : RowClass U) :
    0 < rowClassLeverage U c := (rowClassRep U c).property

theorem sum_rowClassMultiplicity {n k : ℕ} (U : Frame n k) :
    ∑ c : RowClass U, rowClassMultiplicity U c = Fintype.card (ActiveRow U) := by
  simpa [rowClassMultiplicity]
    using Finset.sum_card_fiberwise_eq_card_filter
      (Finset.univ : Finset (ActiveRow U)) (Finset.univ : Finset (RowClass U)) (rowClass U)

theorem sum_activeRows {n k : ℕ} (U : Frame n k) (f : Fin n → ℝ)
    (hzero : ∀ i, leverage U i = 0 → f i = 0) :
    ∑ i : ActiveRow U, f i.val = ∑ i : Fin n, f i := by
  have h := Fintype.sum_subtype_add_sum_subtype (fun i : Fin n => 0 < leverage U i) f
  have hz : (∑ i : {i : Fin n // ¬ 0 < leverage U i}, f i.val) = 0 := by
    apply Finset.sum_eq_zero
    intro i hi
    exact hzero i.val (le_antisymm (le_of_not_gt i.property) (leverage_nonneg U i.val))
  rw [hz, add_zero] at h
  exact h

theorem sum_rowClassMass {n k : ℕ} (U : Frame n k) :
    ∑ c : RowClass U, rowClassMass U c = k := by
  unfold rowClassMass
  rw [Finset.sum_fiberwise]
  rw [sum_activeRows U (leverage U) (fun _ h => h), sum_leverage]

theorem card_rowClass_le_n {n k : ℕ} (U : Frame n k) :
    Fintype.card (RowClass U) ≤ n := by
  calc
    _ ≤ Fintype.card (ActiveRow U) := Fintype.card_le_of_surjective _ (rowClass_surjective U)
    _ ≤ n := by
      have h := Fintype.card_le_of_injective (fun i : ActiveRow U => i.val) Subtype.val_injective
      simpa using h

theorem rowVector_eq_sqrt_smul_unitRow {n k : ℕ} (U : Frame n k) (i : ActiveRow U) :
    rowVector U i.val = Real.sqrt (leverage U i.val) • unitRow U i := by
  rw [unitRow, smul_smul, mul_inv_cancel₀ (ne_of_gt (Real.sqrt_pos.mpr i.property)), one_smul]

theorem gramProjection_sq_unitRows {n k : ℕ} (U : Frame n k) (i j : ActiveRow U) :
    gramProjection U i.val j.val ^ 2 = leverage U i.val * leverage U j.val *
      (inner ℝ (unitRow U i) (unitRow U j)) ^ 2 := by
  rw [← inner_rowVector_rowVector U i.val j.val,
    rowVector_eq_sqrt_smul_unitRow U i, rowVector_eq_sqrt_smul_unitRow U j,
    real_inner_smul_left, inner_smul_right]
  rw [mul_pow, mul_pow, Real.sq_sqrt (leverage_nonneg U i.val),
    Real.sq_sqrt (leverage_nonneg U j.val)]
  ring

theorem gramProjection_sq_of_rowClass_eq {n k : ℕ} (U : Frame n k)
    (i j : ActiveRow U) (h : rowClass U i = rowClass U j) :
    gramProjection U i.val j.val ^ 2 = leverage U i.val * leverage U j.val := by
  rw [gramProjection_sq_unitRows]
  rcases (rowClass_eq_iff U i j).mp h with hs | hs
  · rw [hs, real_inner_self_eq_norm_sq, unitRow_norm]
    norm_num
  · rw [hs, inner_neg_left, real_inner_self_eq_norm_sq, unitRow_norm]
    norm_num

theorem leverage_eq_of_rowClass_eq {n k : ℕ} (U : Frame n k) (hrep : RowReplacement U)
    (i j : ActiveRow U) (h : rowClass U i = rowClass U j) :
    leverage U i.val = leverage U j.val := by
  by_cases hij : i.val = j.val
  · rw [hij]
  · have hgap := hrep i.val j.val hij
    rw [gramProjection_sq_of_rowClass_eq U i j h, sub_self] at hgap
    exact sub_eq_zero.mp (abs_nonpos_iff.mp hgap)

theorem rowClassMass_eq_multiplicity_mul_leverage {n k : ℕ} (U : Frame n k)
    (hrep : RowReplacement U) (c : RowClass U) :
    rowClassMass U c = (rowClassMultiplicity U c : ℝ) * rowClassLeverage U c := by
  unfold rowClassMass
  calc
    _ = ∑ i : ActiveRow U with rowClass U i = c, rowClassLeverage U c := by
      apply Finset.sum_congr rfl
      intro i hi
      exact leverage_eq_of_rowClass_eq U hrep i (rowClassRep U c)
        ((Finset.mem_filter.mp hi).2.trans (rowClass_rep U c).symm)
    _ = _ := by simp [rowClassMultiplicity]

end CubeSections
