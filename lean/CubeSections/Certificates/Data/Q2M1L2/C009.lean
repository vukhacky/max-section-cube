import CubeSections.Certificates.Coverage

/-! Generated from computation/data/pair_trees.json; all arithmetic is proved in Lean. -/
namespace CubeSections.Certificates.Data.Q2M1L2.C009

set_option maxRecDepth 8192
set_option maxHeartbeats 4000000

def parameters : Parameters := ⟨2, 1, 2⟩

private def box_1 : Rectangle := ⟨(17 / 48 : ℚ), (137 / 384 : ℚ), (35 / 96 : ℚ), (71 / 192 : ℚ)⟩
private def node_1 : Tree := .leaf (.strip (173 / 512 : ℚ))
private theorem node_1_accepts : node_1.Accepts parameters box_1 := by
  norm_num [Tree.Accepts, node_1, box_1, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_2 : Rectangle := ⟨(137 / 384 : ℚ), (23 / 64 : ℚ), (35 / 96 : ℚ), (71 / 192 : ℚ)⟩
private def node_2 : Tree := .leaf (.strip (175 / 512 : ℚ))
private theorem node_2_accepts : node_2.Accepts parameters box_2 := by
  norm_num [Tree.Accepts, node_2, box_2, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_0 : Rectangle := ⟨(17 / 48 : ℚ), (23 / 64 : ℚ), (35 / 96 : ℚ), (71 / 192 : ℚ)⟩
private def node_0 : Tree := .splitC (137 / 384 : ℚ) node_1 node_2
private theorem node_0_accepts : node_0.Accepts parameters box_0 := by
  change SplitCValid box_0 (137 / 384 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitCValid, box_0], node_1_accepts, node_2_accepts⟩

def tree : Tree := node_0
def rootBox : Rectangle := box_0
theorem accepted : tree.Accepts parameters rootBox := node_0_accepts

end CubeSections.Certificates.Data.Q2M1L2.C009
