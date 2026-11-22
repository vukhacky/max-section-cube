import CubeSections.Certificates.Coverage

/-! Generated from computation/data/pair_trees.json; all arithmetic is proved in Lean. -/
namespace CubeSections.Certificates.Data.Q2M1L2.C004

set_option maxRecDepth 8192
set_option maxHeartbeats 4000000

def parameters : Parameters := ⟨2, 1, 2⟩

private def box_0 : Rectangle := ⟨(67 / 192 : ℚ), (17 / 48 : ℚ), (35 / 96 : ℚ), (71 / 192 : ℚ)⟩
private def node_0 : Tree := .leaf (.strip (343 / 1024 : ℚ))
private theorem node_0_accepts : node_0.Accepts parameters box_0 := by
  norm_num [Tree.Accepts, node_0, box_0, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

def tree : Tree := node_0
def rootBox : Rectangle := box_0
theorem accepted : tree.Accepts parameters rootBox := node_0_accepts

end CubeSections.Certificates.Data.Q2M1L2.C004
