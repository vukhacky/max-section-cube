import CubeSections.Certificates.Coverage

/-! Generated from computation/data/pair_trees.json; all arithmetic is proved in Lean. -/
namespace CubeSections.Certificates.Data.Q3M2L3

set_option maxRecDepth 8192
set_option maxHeartbeats 4000000

def parameters : Parameters := ⟨3, 2, 3⟩

private def box_2 : Rectangle := ⟨(1 / 4 : ℚ), (7 / 24 : ℚ), (1 / 4 : ℚ), (7 / 24 : ℚ)⟩
private def node_2 : Tree := .leaf .projection
private theorem node_2_accepts : node_2.Accepts parameters box_2 := by
  norm_num [Tree.Accepts, node_2, box_2, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_3 : Rectangle := ⟨(1 / 4 : ℚ), (7 / 24 : ℚ), (7 / 24 : ℚ), (1 / 3 : ℚ)⟩
private def node_3 : Tree := .leaf .projection
private theorem node_3_accepts : node_3.Accepts parameters box_3 := by
  norm_num [Tree.Accepts, node_3, box_3, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_1 : Rectangle := ⟨(1 / 4 : ℚ), (7 / 24 : ℚ), (1 / 4 : ℚ), (1 / 3 : ℚ)⟩
private def node_1 : Tree := .splitD (7 / 24 : ℚ) node_2 node_3
private theorem node_1_accepts : node_1.Accepts parameters box_1 := by
  change SplitDValid box_1 (7 / 24 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitDValid, box_1], node_2_accepts, node_3_accepts⟩

private def box_5 : Rectangle := ⟨(7 / 24 : ℚ), (1 / 3 : ℚ), (1 / 4 : ℚ), (7 / 24 : ℚ)⟩
private def node_5 : Tree := .leaf .projection
private theorem node_5_accepts : node_5.Accepts parameters box_5 := by
  norm_num [Tree.Accepts, node_5, box_5, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_6 : Rectangle := ⟨(7 / 24 : ℚ), (1 / 3 : ℚ), (7 / 24 : ℚ), (1 / 3 : ℚ)⟩
private def node_6 : Tree := .leaf .projection
private theorem node_6_accepts : node_6.Accepts parameters box_6 := by
  norm_num [Tree.Accepts, node_6, box_6, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_4 : Rectangle := ⟨(7 / 24 : ℚ), (1 / 3 : ℚ), (1 / 4 : ℚ), (1 / 3 : ℚ)⟩
private def node_4 : Tree := .splitD (7 / 24 : ℚ) node_5 node_6
private theorem node_4_accepts : node_4.Accepts parameters box_4 := by
  change SplitDValid box_4 (7 / 24 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitDValid, box_4], node_5_accepts, node_6_accepts⟩

private def box_0 : Rectangle := ⟨(1 / 4 : ℚ), (1 / 3 : ℚ), (1 / 4 : ℚ), (1 / 3 : ℚ)⟩
private def node_0 : Tree := .splitC (7 / 24 : ℚ) node_1 node_4
private theorem node_0_accepts : node_0.Accepts parameters box_0 := by
  change SplitCValid box_0 (7 / 24 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitCValid, box_0], node_1_accepts, node_4_accepts⟩

def tree : Tree := node_0
theorem accepted : tree.Accepts parameters (rootRectangle parameters.q) := by
  have hb : box_0 = rootRectangle parameters.q := by
    norm_num [box_0, rootRectangle, parameters]
  simpa only [tree, ← hb] using node_0_accepts

theorem checked : tree.check parameters (rootRectangle parameters.q) = true :=
  (tree.check_eq_true_iff parameters (rootRectangle parameters.q)).mpr accepted

#print axioms accepted
#print axioms checked

end CubeSections.Certificates.Data.Q3M2L3
