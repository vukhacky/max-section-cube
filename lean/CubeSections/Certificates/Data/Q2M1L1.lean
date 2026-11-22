import CubeSections.Certificates.Coverage
import CubeSections.Certificates.Data.Q2M1L1.C000
import CubeSections.Certificates.Data.Q2M1L1.C001
import CubeSections.Certificates.Data.Q2M1L1.C002
import CubeSections.Certificates.Data.Q2M1L1.C003
import CubeSections.Certificates.Data.Q2M1L1.C004
import CubeSections.Certificates.Data.Q2M1L1.C005
import CubeSections.Certificates.Data.Q2M1L1.C006
import CubeSections.Certificates.Data.Q2M1L1.C007

/-! Generated from computation/data/pair_trees.json; all arithmetic is proved in Lean. -/
namespace CubeSections.Certificates.Data.Q2M1L1

set_option maxRecDepth 8192
set_option maxHeartbeats 4000000

def parameters : Parameters := ⟨2, 1, 1⟩

private def box_4 : Rectangle := ⟨(1 / 3 : ℚ), (3 / 8 : ℚ), (1 / 3 : ℚ), (3 / 8 : ℚ)⟩
private def node_4 : Tree := C000.tree
private theorem node_4_accepts : node_4.Accepts parameters box_4 := C000.accepted

private def box_5 : Rectangle := ⟨(1 / 3 : ℚ), (3 / 8 : ℚ), (3 / 8 : ℚ), (5 / 12 : ℚ)⟩
private def node_5 : Tree := C001.tree
private theorem node_5_accepts : node_5.Accepts parameters box_5 := C001.accepted

private def box_3 : Rectangle := ⟨(1 / 3 : ℚ), (3 / 8 : ℚ), (1 / 3 : ℚ), (5 / 12 : ℚ)⟩
private def node_3 : Tree := .splitD (3 / 8 : ℚ) node_4 node_5
private theorem node_3_accepts : node_3.Accepts parameters box_3 := by
  change SplitDValid box_3 (3 / 8 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitDValid, box_3], node_4_accepts, node_5_accepts⟩

private def box_7 : Rectangle := ⟨(3 / 8 : ℚ), (5 / 12 : ℚ), (1 / 3 : ℚ), (3 / 8 : ℚ)⟩
private def node_7 : Tree := C002.tree
private theorem node_7_accepts : node_7.Accepts parameters box_7 := C002.accepted

private def box_10 : Rectangle := ⟨(3 / 8 : ℚ), (19 / 48 : ℚ), (3 / 8 : ℚ), (19 / 48 : ℚ)⟩
private def node_10 : Tree := C003.tree
private theorem node_10_accepts : node_10.Accepts parameters box_10 := C003.accepted

private def box_11 : Rectangle := ⟨(3 / 8 : ℚ), (19 / 48 : ℚ), (19 / 48 : ℚ), (5 / 12 : ℚ)⟩
private def node_11 : Tree := C004.tree
private theorem node_11_accepts : node_11.Accepts parameters box_11 := C004.accepted

private def box_9 : Rectangle := ⟨(3 / 8 : ℚ), (19 / 48 : ℚ), (3 / 8 : ℚ), (5 / 12 : ℚ)⟩
private def node_9 : Tree := .splitD (19 / 48 : ℚ) node_10 node_11
private theorem node_9_accepts : node_9.Accepts parameters box_9 := by
  change SplitDValid box_9 (19 / 48 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitDValid, box_9], node_10_accepts, node_11_accepts⟩

private def box_12 : Rectangle := ⟨(19 / 48 : ℚ), (5 / 12 : ℚ), (3 / 8 : ℚ), (5 / 12 : ℚ)⟩
private def node_12 : Tree := C005.tree
private theorem node_12_accepts : node_12.Accepts parameters box_12 := C005.accepted

private def box_8 : Rectangle := ⟨(3 / 8 : ℚ), (5 / 12 : ℚ), (3 / 8 : ℚ), (5 / 12 : ℚ)⟩
private def node_8 : Tree := .splitC (19 / 48 : ℚ) node_9 node_12
private theorem node_8_accepts : node_8.Accepts parameters box_8 := by
  change SplitCValid box_8 (19 / 48 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitCValid, box_8], node_9_accepts, node_12_accepts⟩

private def box_6 : Rectangle := ⟨(3 / 8 : ℚ), (5 / 12 : ℚ), (1 / 3 : ℚ), (5 / 12 : ℚ)⟩
private def node_6 : Tree := .splitD (3 / 8 : ℚ) node_7 node_8
private theorem node_6_accepts : node_6.Accepts parameters box_6 := by
  change SplitDValid box_6 (3 / 8 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitDValid, box_6], node_7_accepts, node_8_accepts⟩

private def box_2 : Rectangle := ⟨(1 / 3 : ℚ), (5 / 12 : ℚ), (1 / 3 : ℚ), (5 / 12 : ℚ)⟩
private def node_2 : Tree := .splitC (3 / 8 : ℚ) node_3 node_6
private theorem node_2_accepts : node_2.Accepts parameters box_2 := by
  change SplitCValid box_2 (3 / 8 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitCValid, box_2], node_3_accepts, node_6_accepts⟩

private def box_13 : Rectangle := ⟨(1 / 3 : ℚ), (5 / 12 : ℚ), (5 / 12 : ℚ), (1 / 2 : ℚ)⟩
private def node_13 : Tree := C006.tree
private theorem node_13_accepts : node_13.Accepts parameters box_13 := C006.accepted

private def box_1 : Rectangle := ⟨(1 / 3 : ℚ), (5 / 12 : ℚ), (1 / 3 : ℚ), (1 / 2 : ℚ)⟩
private def node_1 : Tree := .splitD (5 / 12 : ℚ) node_2 node_13
private theorem node_1_accepts : node_1.Accepts parameters box_1 := by
  change SplitDValid box_1 (5 / 12 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitDValid, box_1], node_2_accepts, node_13_accepts⟩

private def box_14 : Rectangle := ⟨(5 / 12 : ℚ), (1 / 2 : ℚ), (1 / 3 : ℚ), (1 / 2 : ℚ)⟩
private def node_14 : Tree := C007.tree
private theorem node_14_accepts : node_14.Accepts parameters box_14 := C007.accepted

private def box_0 : Rectangle := ⟨(1 / 3 : ℚ), (1 / 2 : ℚ), (1 / 3 : ℚ), (1 / 2 : ℚ)⟩
private def node_0 : Tree := .splitC (5 / 12 : ℚ) node_1 node_14
private theorem node_0_accepts : node_0.Accepts parameters box_0 := by
  change SplitCValid box_0 (5 / 12 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitCValid, box_0], node_1_accepts, node_14_accepts⟩

def tree : Tree := node_0
theorem accepted : tree.Accepts parameters (rootRectangle parameters.q) := by
  have hb : box_0 = rootRectangle parameters.q := by
    norm_num [box_0, rootRectangle, parameters]
  simpa only [tree, ← hb] using node_0_accepts

theorem checked : tree.check parameters (rootRectangle parameters.q) = true :=
  (tree.check_eq_true_iff parameters (rootRectangle parameters.q)).mpr accepted

#print axioms accepted
#print axioms checked

end CubeSections.Certificates.Data.Q2M1L1
