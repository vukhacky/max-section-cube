import CubeSections.Geometry.PairKernel
import CubeSections.Geometry.RowSupport
import CubeSections.Geometry.AffineSections

/-! Removing two distinct signed row classes on the actual rank-two kernel
produces an isometric frame in dimension k-2. The ambient dimension is counted
from the finite support, with the full n-m-l formula under positive support. -/
noncomputable section
open Set Classical
open scoped BigOperators InnerProductSpace
namespace CubeSections

def RemainingRow {n k : ℕ} (U : Frame n k) (c d : RowClass U) :=
  {a : ActiveRow U // rowClass U a ≠ c ∧ rowClass U a ≠ d}

instance remainingRowFintype {n k : ℕ} (U : Frame n k) (c d : RowClass U) :
    Fintype (RemainingRow U c d) := inferInstanceAs (Fintype {a : ActiveRow U //
      rowClass U a ≠ c ∧ rowClass U a ≠ d})

def remainingRowCount {n k : ℕ} (U : Frame n k) (c d : RowClass U) : ℕ :=
  Fintype.card (RemainingRow U c d)

def remainingRowEquiv {n k : ℕ} (U : Frame n k) (c d : RowClass U) :
    RemainingRow U c d ≃ Fin (remainingRowCount U c d) := Fintype.equivFin _

theorem remainingRowCount_eq {n k : ℕ} (U : Frame n k) (c d : RowClass U)
    (hcd : c ≠ d) :
    remainingRowCount U c d = Fintype.card (ActiveRow U) -
      rowClassMultiplicity U c - rowClassMultiplicity U d := by
  let s := Finset.univ.filter (fun a : ActiveRow U => rowClass U a = c)
  let t := Finset.univ.filter (fun a : ActiveRow U => rowClass U a = d)
  have hdisj : Disjoint s t := by
    apply Finset.disjoint_left.mpr
    intro a ha hb
    exact hcd ((Finset.mem_filter.mp ha).2.symm.trans (Finset.mem_filter.mp hb).2)
  have heq : Finset.univ.filter (fun a : ActiveRow U => rowClass U a ≠ c ∧ rowClass U a ≠ d) =
      Finset.univ \ (s ∪ t) := by ext a; simp [s, t]
  change Fintype.card {a : ActiveRow U // rowClass U a ≠ c ∧ rowClass U a ≠ d} = _
  rw [Fintype.card_subtype, heq, Finset.card_univ_sdiff,
    Finset.card_union_of_disjoint hdisj, Nat.sub_add_eq]
  rfl

theorem activeRow_card_of_pos {n k : ℕ} (U : Frame n k)
    (hpos : ∀ i, 0 < leverage U i) : Fintype.card (ActiveRow U) = n := by
  change Fintype.card {i : Fin n // 0 < leverage U i} = n
  simp [Fintype.card_subtype, hpos]

theorem remainingRowCount_eq_of_pos {n k : ℕ} (U : Frame n k) (c d : RowClass U)
    (hcd : c ≠ d) (hpos : ∀ i, 0 < leverage U i) :
    remainingRowCount U c d = n - rowClassMultiplicity U c - rowClassMultiplicity U d := by
  rw [remainingRowCount_eq U c d hcd, activeRow_card_of_pos U hpos]

def classKernelFrame {n k : ℕ} (U : Frame n k) (c d : RowClass U)
    (hcd : c ≠ d) : Frame k (k - 2) :=
  pairKernelFrame U (rowClassRep U c).val (rowClassRep U d).val
    (ne_of_gt (pairGramDet_classRep_pos U c d hcd))

theorem classKernelFrame_representatives_zero {n k : ℕ} (U : Frame n k)
    (c d : RowClass U) (hcd : c ≠ d) (x : E (k - 2)) :
    (U (classKernelFrame U c d hcd x)) (rowClassRep U c).val = 0 ∧
      (U (classKernelFrame U c d hcd x)) (rowClassRep U d).val = 0 := by
  exact (mem_pairKernel U _ _ _).mp (pairKernelFrame_mem U _ _ _ x)

theorem coordinate_zero_of_class_eq {n k : ℕ} (U : Frame n k) (a b : ActiveRow U)
    (hab : rowClass U a = rowClass U b) (x : E k) (hb : (U x) b.val = 0) :
    (U x) a.val = 0 := by
  have hb' : inner ℝ (unitRow U b) x = 0 := by
    rw [unitRow_coordinate U b] at hb
    exact (mul_eq_zero.mp hb).resolve_left (ne_of_gt (Real.sqrt_pos.mpr b.property))
  rw [unitRow_coordinate U a]
  rcases (rowClass_eq_iff U a b).mp hab with hs | hs
  · rw [hs, hb', mul_zero]
  · rw [hs, inner_neg_left, hb', neg_zero, mul_zero]

theorem classKernelFrame_class_zero {n k : ℕ} (U : Frame n k)
    (c d : RowClass U) (hcd : c ≠ d) (a : ActiveRow U)
    (ha : rowClass U a = c ∨ rowClass U a = d) (x : E (k - 2)) :
    (U (classKernelFrame U c d hcd x)) a.val = 0 := by
  have hz := classKernelFrame_representatives_zero U c d hcd x
  rcases ha with ha | ha
  · exact coordinate_zero_of_class_eq U a (rowClassRep U c)
      (ha.trans (rowClass_rep U c).symm) _ hz.1
  · exact coordinate_zero_of_class_eq U a (rowClassRep U d)
      (ha.trans (rowClass_rep U d).symm) _ hz.2

theorem remainingRow_sum_sq {n k : ℕ} (U : Frame n k) (c d : RowClass U)
    (hcd : c ≠ d) (x : E (k - 2)) :
    ∑ a : RemainingRow U c d, ((U (classKernelFrame U c d hcd x)) a.val.val) ^ 2 =
      ‖x‖ ^ 2 := by
  let f : ActiveRow U → ℝ := fun a => ((U (classKernelFrame U c d hcd x)) a.val) ^ 2
  have hsum := Fintype.sum_subtype_add_sum_subtype
    (fun a : ActiveRow U => rowClass U a ≠ c ∧ rowClass U a ≠ d) f
  have hz : (∑ a : {a : ActiveRow U // ¬ (rowClass U a ≠ c ∧ rowClass U a ≠ d)}, f a.val) = 0 := by
    apply Finset.sum_eq_zero
    intro a ha
    have hab : rowClass U a.val = c ∨ rowClass U a.val = d := by
      have ha' := a.property
      tauto
    dsimp [f]
    rw [classKernelFrame_class_zero U c d hcd a.val hab, sq, zero_mul]
  rw [hz, add_zero] at hsum
  calc
    _ = ∑ a : ActiveRow U, f a := hsum
    _ = ∑ i : Fin n, ((U (classKernelFrame U c d hcd x)) i) ^ 2 := by
      dsimp only [f]
      apply sum_activeRows U (fun i => ((U (classKernelFrame U c d hcd x)) i) ^ 2)
      intro i hi
      rw [(leverage_eq_zero_iff_coordinate_zero U i).mp hi, sq, zero_mul]
    _ = ‖x‖ ^ 2 := by
      rw [← EuclideanSpace.real_norm_sq_eq, U.norm_map, (classKernelFrame U c d hcd).norm_map]

def reducedClassMap {n k : ℕ} (U : Frame n k) (c d : RowClass U) (hcd : c ≠ d) :
    E (k - 2) →ₗ[ℝ] E (remainingRowCount U c d) where
  toFun x := WithLp.toLp 2 (fun a =>
    (U (classKernelFrame U c d hcd x)) ((remainingRowEquiv U c d).symm a).val.val)
  map_add' x y := by ext; simp
  map_smul' a x := by ext; simp

theorem reducedClassMap_norm {n k : ℕ} (U : Frame n k) (c d : RowClass U)
    (hcd : c ≠ d) (x : E (k - 2)) : ‖reducedClassMap U c d hcd x‖ = ‖x‖ := by
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  rw [EuclideanSpace.real_norm_sq_eq]
  change (∑ a : Fin (remainingRowCount U c d),
    ((U (classKernelFrame U c d hcd x)) ((remainingRowEquiv U c d).symm a).val.val) ^ 2) = _
  rw [(remainingRowEquiv U c d).symm.sum_comp
    (fun a : RemainingRow U c d => ((U (classKernelFrame U c d hcd x)) a.val.val) ^ 2)]
  exact remainingRow_sum_sq U c d hcd x

def reducedClassFrame {n k : ℕ} (U : Frame n k) (c d : RowClass U) (hcd : c ≠ d) :
    Frame (remainingRowCount U c d) (k - 2) :=
  { reducedClassMap U c d hcd with norm_map' := reducedClassMap_norm U c d hcd }

@[simp] theorem reducedClassFrame_apply {n k : ℕ} (U : Frame n k) (c d : RowClass U)
    (hcd : c ≠ d) (x : E (k - 2)) (a : Fin (remainingRowCount U c d)) :
    reducedClassFrame U c d hcd x a =
      (U (classKernelFrame U c d hcd x)) ((remainingRowEquiv U c d).symm a).val.val := rfl

def reducedOffset {n k : ℕ} (U : Frame n k) (c d : RowClass U) (z : E k) :
    E (remainingRowCount U c d) := WithLp.toLp 2 (fun a =>
      (U z) ((remainingRowEquiv U c d).symm a).val.val)

theorem fiber_subset_reduced_affineSlab {n k : ℕ} (U : Frame n k) (c d : RowClass U)
    (hcd : c ≠ d) (z : E k) :
    {x | U (z + classKernelFrame U c d hcd x) ∈ cube n} ⊆
      affineSlab (reducedClassFrame U c d hcd) (reducedOffset U c d z) := by
  intro x hx a
  have h := hx ((remainingRowEquiv U c d).symm a).val.val
  simpa [affineSlab, reducedOffset, map_add] using h

end CubeSections
