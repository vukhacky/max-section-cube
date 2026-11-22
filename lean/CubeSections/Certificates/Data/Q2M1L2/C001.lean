import CubeSections.Certificates.Coverage

/-! Generated from computation/data/pair_trees.json; all arithmetic is proved in Lean. -/
namespace CubeSections.Certificates.Data.Q2M1L2.C001

set_option maxRecDepth 8192
set_option maxHeartbeats 4000000

def parameters : Parameters := ⟨2, 1, 2⟩

private def box_1 : Rectangle := ⟨(1 / 3 : ℚ), (11 / 32 : ℚ), (17 / 48 : ℚ), (35 / 96 : ℚ)⟩
private def node_1 : Tree := .leaf (.strip (305 / 1024 : ℚ))
private theorem node_1_accepts : node_1.Accepts parameters box_1 := by
  norm_num [Tree.Accepts, node_1, box_1, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_4 : Rectangle := ⟨(1 / 3 : ℚ), (65 / 192 : ℚ), (35 / 96 : ℚ), (71 / 192 : ℚ)⟩
private def node_4 : Tree := .leaf (.strip (155 / 512 : ℚ))
private theorem node_4_accepts : node_4.Accepts parameters box_4 := by
  norm_num [Tree.Accepts, node_4, box_4, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_6 : Rectangle := ⟨(1 / 3 : ℚ), (43 / 128 : ℚ), (71 / 192 : ℚ), (3 / 8 : ℚ)⟩
private def node_6 : Tree := .leaf (.strip (323 / 1024 : ℚ))
private theorem node_6_accepts : node_6.Accepts parameters box_6 := by
  norm_num [Tree.Accepts, node_6, box_6, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_7 : Rectangle := ⟨(43 / 128 : ℚ), (65 / 192 : ℚ), (71 / 192 : ℚ), (3 / 8 : ℚ)⟩
private def node_7 : Tree := .leaf (.strip (165 / 512 : ℚ))
private theorem node_7_accepts : node_7.Accepts parameters box_7 := by
  norm_num [Tree.Accepts, node_7, box_7, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_5 : Rectangle := ⟨(1 / 3 : ℚ), (65 / 192 : ℚ), (71 / 192 : ℚ), (3 / 8 : ℚ)⟩
private def node_5 : Tree := .splitC (43 / 128 : ℚ) node_6 node_7
private theorem node_5_accepts : node_5.Accepts parameters box_5 := by
  change SplitCValid box_5 (43 / 128 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitCValid, box_5], node_6_accepts, node_7_accepts⟩

private def box_3 : Rectangle := ⟨(1 / 3 : ℚ), (65 / 192 : ℚ), (35 / 96 : ℚ), (3 / 8 : ℚ)⟩
private def node_3 : Tree := .splitD (71 / 192 : ℚ) node_4 node_5
private theorem node_3_accepts : node_3.Accepts parameters box_3 := by
  change SplitDValid box_3 (71 / 192 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitDValid, box_3], node_4_accepts, node_5_accepts⟩

private def box_9 : Rectangle := ⟨(65 / 192 : ℚ), (11 / 32 : ℚ), (35 / 96 : ℚ), (71 / 192 : ℚ)⟩
private def node_9 : Tree := .leaf (.strip (323 / 1024 : ℚ))
private theorem node_9_accepts : node_9.Accepts parameters box_9 := by
  norm_num [Tree.Accepts, node_9, box_9, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_12 : Rectangle := ⟨(65 / 192 : ℚ), (131 / 384 : ℚ), (71 / 192 : ℚ), (143 / 384 : ℚ)⟩
private def node_12 : Tree := .leaf (.strip (325 / 1024 : ℚ))
private theorem node_12_accepts : node_12.Accepts parameters box_12 := by
  norm_num [Tree.Accepts, node_12, box_12, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_13 : Rectangle := ⟨(65 / 192 : ℚ), (131 / 384 : ℚ), (143 / 384 : ℚ), (3 / 8 : ℚ)⟩
private def node_13 : Tree := .leaf (.strip (335 / 1024 : ℚ))
private theorem node_13_accepts : node_13.Accepts parameters box_13 := by
  norm_num [Tree.Accepts, node_13, box_13, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_11 : Rectangle := ⟨(65 / 192 : ℚ), (131 / 384 : ℚ), (71 / 192 : ℚ), (3 / 8 : ℚ)⟩
private def node_11 : Tree := .splitD (143 / 384 : ℚ) node_12 node_13
private theorem node_11_accepts : node_11.Accepts parameters box_11 := by
  change SplitDValid box_11 (143 / 384 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitDValid, box_11], node_12_accepts, node_13_accepts⟩

private def box_15 : Rectangle := ⟨(131 / 384 : ℚ), (11 / 32 : ℚ), (71 / 192 : ℚ), (143 / 384 : ℚ)⟩
private def node_15 : Tree := .leaf (.strip (331 / 1024 : ℚ))
private theorem node_15_accepts : node_15.Accepts parameters box_15 := by
  norm_num [Tree.Accepts, node_15, box_15, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_17 : Rectangle := ⟨(131 / 384 : ℚ), (263 / 768 : ℚ), (143 / 384 : ℚ), (3 / 8 : ℚ)⟩
private def node_17 : Tree := .leaf (.strip (337 / 1024 : ℚ))
private theorem node_17_accepts : node_17.Accepts parameters box_17 := by
  norm_num [Tree.Accepts, node_17, box_17, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_19 : Rectangle := ⟨(263 / 768 : ℚ), (11 / 32 : ℚ), (143 / 384 : ℚ), (287 / 768 : ℚ)⟩
private def node_19 : Tree := .leaf (.strip (335 / 1024 : ℚ))
private theorem node_19_accepts : node_19.Accepts parameters box_19 := by
  norm_num [Tree.Accepts, node_19, box_19, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_20 : Rectangle := ⟨(263 / 768 : ℚ), (11 / 32 : ℚ), (287 / 768 : ℚ), (3 / 8 : ℚ)⟩
private def node_20 : Tree := .leaf (.strip (85 / 256 : ℚ))
private theorem node_20_accepts : node_20.Accepts parameters box_20 := by
  norm_num [Tree.Accepts, node_20, box_20, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_18 : Rectangle := ⟨(263 / 768 : ℚ), (11 / 32 : ℚ), (143 / 384 : ℚ), (3 / 8 : ℚ)⟩
private def node_18 : Tree := .splitD (287 / 768 : ℚ) node_19 node_20
private theorem node_18_accepts : node_18.Accepts parameters box_18 := by
  change SplitDValid box_18 (287 / 768 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitDValid, box_18], node_19_accepts, node_20_accepts⟩

private def box_16 : Rectangle := ⟨(131 / 384 : ℚ), (11 / 32 : ℚ), (143 / 384 : ℚ), (3 / 8 : ℚ)⟩
private def node_16 : Tree := .splitC (263 / 768 : ℚ) node_17 node_18
private theorem node_16_accepts : node_16.Accepts parameters box_16 := by
  change SplitCValid box_16 (263 / 768 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitCValid, box_16], node_17_accepts, node_18_accepts⟩

private def box_14 : Rectangle := ⟨(131 / 384 : ℚ), (11 / 32 : ℚ), (71 / 192 : ℚ), (3 / 8 : ℚ)⟩
private def node_14 : Tree := .splitD (143 / 384 : ℚ) node_15 node_16
private theorem node_14_accepts : node_14.Accepts parameters box_14 := by
  change SplitDValid box_14 (143 / 384 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitDValid, box_14], node_15_accepts, node_16_accepts⟩

private def box_10 : Rectangle := ⟨(65 / 192 : ℚ), (11 / 32 : ℚ), (71 / 192 : ℚ), (3 / 8 : ℚ)⟩
private def node_10 : Tree := .splitC (131 / 384 : ℚ) node_11 node_14
private theorem node_10_accepts : node_10.Accepts parameters box_10 := by
  change SplitCValid box_10 (131 / 384 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitCValid, box_10], node_11_accepts, node_14_accepts⟩

private def box_8 : Rectangle := ⟨(65 / 192 : ℚ), (11 / 32 : ℚ), (35 / 96 : ℚ), (3 / 8 : ℚ)⟩
private def node_8 : Tree := .splitD (71 / 192 : ℚ) node_9 node_10
private theorem node_8_accepts : node_8.Accepts parameters box_8 := by
  change SplitDValid box_8 (71 / 192 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitDValid, box_8], node_9_accepts, node_10_accepts⟩

private def box_2 : Rectangle := ⟨(1 / 3 : ℚ), (11 / 32 : ℚ), (35 / 96 : ℚ), (3 / 8 : ℚ)⟩
private def node_2 : Tree := .splitC (65 / 192 : ℚ) node_3 node_8
private theorem node_2_accepts : node_2.Accepts parameters box_2 := by
  change SplitCValid box_2 (65 / 192 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitCValid, box_2], node_3_accepts, node_8_accepts⟩

private def box_0 : Rectangle := ⟨(1 / 3 : ℚ), (11 / 32 : ℚ), (17 / 48 : ℚ), (3 / 8 : ℚ)⟩
private def node_0 : Tree := .splitD (35 / 96 : ℚ) node_1 node_2
private theorem node_0_accepts : node_0.Accepts parameters box_0 := by
  change SplitDValid box_0 (35 / 96 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitDValid, box_0], node_1_accepts, node_2_accepts⟩

def tree : Tree := node_0
def rootBox : Rectangle := box_0
theorem accepted : tree.Accepts parameters rootBox := node_0_accepts

end CubeSections.Certificates.Data.Q2M1L2.C001
