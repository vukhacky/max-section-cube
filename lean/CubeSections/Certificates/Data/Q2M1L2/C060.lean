import CubeSections.Certificates.Coverage

/-! Generated from computation/data/pair_trees.json; all arithmetic is proved in Lean. -/
namespace CubeSections.Certificates.Data.Q2M1L2.C060

set_option maxRecDepth 8192
set_option maxHeartbeats 4000000

def parameters : Parameters := ⟨2, 1, 2⟩

private def box_1 : Rectangle := ⟨(3 / 8 : ℚ), (37 / 96 : ℚ), (1 / 3 : ℚ), (17 / 48 : ℚ)⟩
private def node_1 : Tree := .leaf (.strip (163 / 512 : ℚ))
private theorem node_1_accepts : node_1.Accepts parameters box_1 := by
  norm_num [Tree.Accepts, node_1, box_1, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_3 : Rectangle := ⟨(37 / 96 : ℚ), (19 / 48 : ℚ), (1 / 3 : ℚ), (11 / 32 : ℚ)⟩
private def node_3 : Tree := .leaf (.strip (35 / 128 : ℚ))
private theorem node_3_accepts : node_3.Accepts parameters box_3 := by
  norm_num [Tree.Accepts, node_3, box_3, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_4 : Rectangle := ⟨(37 / 96 : ℚ), (19 / 48 : ℚ), (11 / 32 : ℚ), (17 / 48 : ℚ)⟩
private def node_4 : Tree := .leaf (.strip (329 / 1024 : ℚ))
private theorem node_4_accepts : node_4.Accepts parameters box_4 := by
  norm_num [Tree.Accepts, node_4, box_4, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_2 : Rectangle := ⟨(37 / 96 : ℚ), (19 / 48 : ℚ), (1 / 3 : ℚ), (17 / 48 : ℚ)⟩
private def node_2 : Tree := .splitD (11 / 32 : ℚ) node_3 node_4
private theorem node_2_accepts : node_2.Accepts parameters box_2 := by
  change SplitDValid box_2 (11 / 32 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitDValid, box_2], node_3_accepts, node_4_accepts⟩

private def box_0 : Rectangle := ⟨(3 / 8 : ℚ), (19 / 48 : ℚ), (1 / 3 : ℚ), (17 / 48 : ℚ)⟩
private def node_0 : Tree := .splitC (37 / 96 : ℚ) node_1 node_2
private theorem node_0_accepts : node_0.Accepts parameters box_0 := by
  change SplitCValid box_0 (37 / 96 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitCValid, box_0], node_1_accepts, node_2_accepts⟩

def tree : Tree := node_0
def rootBox : Rectangle := box_0
theorem accepted : tree.Accepts parameters rootBox := node_0_accepts

end CubeSections.Certificates.Data.Q2M1L2.C060
