import CubeSections.Certificates.Coverage

/-! Generated from computation/data/pair_trees.json; all arithmetic is proved in Lean. -/
namespace CubeSections.Certificates.Data.Q4M2L4

set_option maxRecDepth 8192
set_option maxHeartbeats 4000000

def parameters : Parameters := ⟨4, 2, 4⟩

private def box_1 : Rectangle := ⟨(1 / 5 : ℚ), (9 / 40 : ℚ), (1 / 5 : ℚ), (1 / 4 : ℚ)⟩
private def node_1 : Tree := .leaf .projection
private theorem node_1_accepts : node_1.Accepts parameters box_1 := by
  norm_num [Tree.Accepts, node_1, box_1, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_2 : Rectangle := ⟨(9 / 40 : ℚ), (1 / 4 : ℚ), (1 / 5 : ℚ), (1 / 4 : ℚ)⟩
private def node_2 : Tree := .leaf .projection
private theorem node_2_accepts : node_2.Accepts parameters box_2 := by
  norm_num [Tree.Accepts, node_2, box_2, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_0 : Rectangle := ⟨(1 / 5 : ℚ), (1 / 4 : ℚ), (1 / 5 : ℚ), (1 / 4 : ℚ)⟩
private def node_0 : Tree := .splitC (9 / 40 : ℚ) node_1 node_2
private theorem node_0_accepts : node_0.Accepts parameters box_0 := by
  change SplitCValid box_0 (9 / 40 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitCValid, box_0], node_1_accepts, node_2_accepts⟩

def tree : Tree := node_0
theorem accepted : tree.Accepts parameters (rootRectangle parameters.q) := by
  have hb : box_0 = rootRectangle parameters.q := by
    norm_num [box_0, rootRectangle, parameters]
  simpa only [tree, ← hb] using node_0_accepts

theorem checked : tree.check parameters (rootRectangle parameters.q) = true :=
  (tree.check_eq_true_iff parameters (rootRectangle parameters.q)).mpr accepted

#print axioms accepted
#print axioms checked

end CubeSections.Certificates.Data.Q4M2L4
