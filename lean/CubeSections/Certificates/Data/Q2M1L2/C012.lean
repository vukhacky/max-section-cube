import CubeSections.Certificates.Coverage

/-! Generated from computation/data/pair_trees.json; all arithmetic is proved in Lean. -/
namespace CubeSections.Certificates.Data.Q2M1L2.C012

set_option maxRecDepth 8192
set_option maxHeartbeats 4000000

def parameters : Parameters := ⟨2, 1, 2⟩

private def box_2 : Rectangle := ⟨(137 / 384 : ℚ), (275 / 768 : ℚ), (71 / 192 : ℚ), (95 / 256 : ℚ)⟩
private def node_2 : Tree := .leaf (.strip (351 / 1024 : ℚ))
private theorem node_2_accepts : node_2.Accepts parameters box_2 := by
  norm_num [Tree.Accepts, node_2, box_2, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_4 : Rectangle := ⟨(137 / 384 : ℚ), (183 / 512 : ℚ), (95 / 256 : ℚ), (143 / 384 : ℚ)⟩
private def node_4 : Tree := .leaf (.strip (355 / 1024 : ℚ))
private theorem node_4_accepts : node_4.Accepts parameters box_4 := by
  norm_num [Tree.Accepts, node_4, box_4, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_6 : Rectangle := ⟨(183 / 512 : ℚ), (275 / 768 : ℚ), (95 / 256 : ℚ), (571 / 1536 : ℚ)⟩
private def node_6 : Tree := .leaf (.strip (353 / 1024 : ℚ))
private theorem node_6_accepts : node_6.Accepts parameters box_6 := by
  norm_num [Tree.Accepts, node_6, box_6, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_7 : Rectangle := ⟨(183 / 512 : ℚ), (275 / 768 : ℚ), (571 / 1536 : ℚ), (143 / 384 : ℚ)⟩
private def node_7 : Tree := .leaf (.strip (355 / 1024 : ℚ))
private theorem node_7_accepts : node_7.Accepts parameters box_7 := by
  norm_num [Tree.Accepts, node_7, box_7, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_5 : Rectangle := ⟨(183 / 512 : ℚ), (275 / 768 : ℚ), (95 / 256 : ℚ), (143 / 384 : ℚ)⟩
private def node_5 : Tree := .splitD (571 / 1536 : ℚ) node_6 node_7
private theorem node_5_accepts : node_5.Accepts parameters box_5 := by
  change SplitDValid box_5 (571 / 1536 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitDValid, box_5], node_6_accepts, node_7_accepts⟩

private def box_3 : Rectangle := ⟨(137 / 384 : ℚ), (275 / 768 : ℚ), (95 / 256 : ℚ), (143 / 384 : ℚ)⟩
private def node_3 : Tree := .splitC (183 / 512 : ℚ) node_4 node_5
private theorem node_3_accepts : node_3.Accepts parameters box_3 := by
  change SplitCValid box_3 (183 / 512 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitCValid, box_3], node_4_accepts, node_5_accepts⟩

private def box_1 : Rectangle := ⟨(137 / 384 : ℚ), (275 / 768 : ℚ), (71 / 192 : ℚ), (143 / 384 : ℚ)⟩
private def node_1 : Tree := .splitD (95 / 256 : ℚ) node_2 node_3
private theorem node_1_accepts : node_1.Accepts parameters box_1 := by
  change SplitDValid box_1 (95 / 256 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitDValid, box_1], node_2_accepts, node_3_accepts⟩

private def box_9 : Rectangle := ⟨(275 / 768 : ℚ), (23 / 64 : ℚ), (71 / 192 : ℚ), (95 / 256 : ℚ)⟩
private def node_9 : Tree := .leaf (.strip (353 / 1024 : ℚ))
private theorem node_9_accepts : node_9.Accepts parameters box_9 := by
  norm_num [Tree.Accepts, node_9, box_9, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_12 : Rectangle := ⟨(275 / 768 : ℚ), (551 / 1536 : ℚ), (95 / 256 : ℚ), (571 / 1536 : ℚ)⟩
private def node_12 : Tree := .leaf (.strip (177 / 512 : ℚ))
private theorem node_12_accepts : node_12.Accepts parameters box_12 := by
  norm_num [Tree.Accepts, node_12, box_12, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_13 : Rectangle := ⟨(275 / 768 : ℚ), (551 / 1536 : ℚ), (571 / 1536 : ℚ), (143 / 384 : ℚ)⟩
private def node_13 : Tree := .leaf (.strip (89 / 256 : ℚ))
private theorem node_13_accepts : node_13.Accepts parameters box_13 := by
  norm_num [Tree.Accepts, node_13, box_13, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_11 : Rectangle := ⟨(275 / 768 : ℚ), (551 / 1536 : ℚ), (95 / 256 : ℚ), (143 / 384 : ℚ)⟩
private def node_11 : Tree := .splitD (571 / 1536 : ℚ) node_12 node_13
private theorem node_11_accepts : node_11.Accepts parameters box_11 := by
  change SplitDValid box_11 (571 / 1536 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitDValid, box_11], node_12_accepts, node_13_accepts⟩

private def box_15 : Rectangle := ⟨(551 / 1536 : ℚ), (23 / 64 : ℚ), (95 / 256 : ℚ), (571 / 1536 : ℚ)⟩
private def node_15 : Tree := .leaf (.strip (355 / 1024 : ℚ))
private theorem node_15_accepts : node_15.Accepts parameters box_15 := by
  norm_num [Tree.Accepts, node_15, box_15, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_16 : Rectangle := ⟨(551 / 1536 : ℚ), (23 / 64 : ℚ), (571 / 1536 : ℚ), (143 / 384 : ℚ)⟩
private def node_16 : Tree := .leaf (.strip (357 / 1024 : ℚ))
private theorem node_16_accepts : node_16.Accepts parameters box_16 := by
  norm_num [Tree.Accepts, node_16, box_16, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_14 : Rectangle := ⟨(551 / 1536 : ℚ), (23 / 64 : ℚ), (95 / 256 : ℚ), (143 / 384 : ℚ)⟩
private def node_14 : Tree := .splitD (571 / 1536 : ℚ) node_15 node_16
private theorem node_14_accepts : node_14.Accepts parameters box_14 := by
  change SplitDValid box_14 (571 / 1536 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitDValid, box_14], node_15_accepts, node_16_accepts⟩

private def box_10 : Rectangle := ⟨(275 / 768 : ℚ), (23 / 64 : ℚ), (95 / 256 : ℚ), (143 / 384 : ℚ)⟩
private def node_10 : Tree := .splitC (551 / 1536 : ℚ) node_11 node_14
private theorem node_10_accepts : node_10.Accepts parameters box_10 := by
  change SplitCValid box_10 (551 / 1536 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitCValid, box_10], node_11_accepts, node_14_accepts⟩

private def box_8 : Rectangle := ⟨(275 / 768 : ℚ), (23 / 64 : ℚ), (71 / 192 : ℚ), (143 / 384 : ℚ)⟩
private def node_8 : Tree := .splitD (95 / 256 : ℚ) node_9 node_10
private theorem node_8_accepts : node_8.Accepts parameters box_8 := by
  change SplitDValid box_8 (95 / 256 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitDValid, box_8], node_9_accepts, node_10_accepts⟩

private def box_0 : Rectangle := ⟨(137 / 384 : ℚ), (23 / 64 : ℚ), (71 / 192 : ℚ), (143 / 384 : ℚ)⟩
private def node_0 : Tree := .splitC (275 / 768 : ℚ) node_1 node_8
private theorem node_0_accepts : node_0.Accepts parameters box_0 := by
  change SplitCValid box_0 (275 / 768 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitCValid, box_0], node_1_accepts, node_8_accepts⟩

def tree : Tree := node_0
def rootBox : Rectangle := box_0
theorem accepted : tree.Accepts parameters rootBox := node_0_accepts

end CubeSections.Certificates.Data.Q2M1L2.C012
