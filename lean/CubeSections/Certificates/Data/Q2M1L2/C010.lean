import CubeSections.Certificates.Coverage

/-! Generated from computation/data/pair_trees.json; all arithmetic is proved in Lean. -/
namespace CubeSections.Certificates.Data.Q2M1L2.C010

set_option maxRecDepth 8192
set_option maxHeartbeats 4000000

def parameters : Parameters := ⟨2, 1, 2⟩

private def box_2 : Rectangle := ⟨(17 / 48 : ℚ), (91 / 256 : ℚ), (71 / 192 : ℚ), (95 / 256 : ℚ)⟩
private def node_2 : Tree := .leaf (.strip (347 / 1024 : ℚ))
private theorem node_2_accepts : node_2.Accepts parameters box_2 := by
  norm_num [Tree.Accepts, node_2, box_2, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_3 : Rectangle := ⟨(17 / 48 : ℚ), (91 / 256 : ℚ), (95 / 256 : ℚ), (143 / 384 : ℚ)⟩
private def node_3 : Tree := .leaf (.strip (11 / 32 : ℚ))
private theorem node_3_accepts : node_3.Accepts parameters box_3 := by
  norm_num [Tree.Accepts, node_3, box_3, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_1 : Rectangle := ⟨(17 / 48 : ℚ), (91 / 256 : ℚ), (71 / 192 : ℚ), (143 / 384 : ℚ)⟩
private def node_1 : Tree := .splitD (95 / 256 : ℚ) node_2 node_3
private theorem node_1_accepts : node_1.Accepts parameters box_1 := by
  change SplitDValid box_1 (95 / 256 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitDValid, box_1], node_2_accepts, node_3_accepts⟩

private def box_5 : Rectangle := ⟨(91 / 256 : ℚ), (137 / 384 : ℚ), (71 / 192 : ℚ), (95 / 256 : ℚ)⟩
private def node_5 : Tree := .leaf (.strip (349 / 1024 : ℚ))
private theorem node_5_accepts : node_5.Accepts parameters box_5 := by
  norm_num [Tree.Accepts, node_5, box_5, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_7 : Rectangle := ⟨(91 / 256 : ℚ), (547 / 1536 : ℚ), (95 / 256 : ℚ), (143 / 384 : ℚ)⟩
private def node_7 : Tree := .leaf (.strip (353 / 1024 : ℚ))
private theorem node_7_accepts : node_7.Accepts parameters box_7 := by
  norm_num [Tree.Accepts, node_7, box_7, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_8 : Rectangle := ⟨(547 / 1536 : ℚ), (137 / 384 : ℚ), (95 / 256 : ℚ), (143 / 384 : ℚ)⟩
private def node_8 : Tree := .leaf (.strip (177 / 512 : ℚ))
private theorem node_8_accepts : node_8.Accepts parameters box_8 := by
  norm_num [Tree.Accepts, node_8, box_8, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_6 : Rectangle := ⟨(91 / 256 : ℚ), (137 / 384 : ℚ), (95 / 256 : ℚ), (143 / 384 : ℚ)⟩
private def node_6 : Tree := .splitC (547 / 1536 : ℚ) node_7 node_8
private theorem node_6_accepts : node_6.Accepts parameters box_6 := by
  change SplitCValid box_6 (547 / 1536 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitCValid, box_6], node_7_accepts, node_8_accepts⟩

private def box_4 : Rectangle := ⟨(91 / 256 : ℚ), (137 / 384 : ℚ), (71 / 192 : ℚ), (143 / 384 : ℚ)⟩
private def node_4 : Tree := .splitD (95 / 256 : ℚ) node_5 node_6
private theorem node_4_accepts : node_4.Accepts parameters box_4 := by
  change SplitDValid box_4 (95 / 256 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitDValid, box_4], node_5_accepts, node_6_accepts⟩

private def box_0 : Rectangle := ⟨(17 / 48 : ℚ), (137 / 384 : ℚ), (71 / 192 : ℚ), (143 / 384 : ℚ)⟩
private def node_0 : Tree := .splitC (91 / 256 : ℚ) node_1 node_4
private theorem node_0_accepts : node_0.Accepts parameters box_0 := by
  change SplitCValid box_0 (91 / 256 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitCValid, box_0], node_1_accepts, node_4_accepts⟩

def tree : Tree := node_0
def rootBox : Rectangle := box_0
theorem accepted : tree.Accepts parameters rootBox := node_0_accepts

end CubeSections.Certificates.Data.Q2M1L2.C010
