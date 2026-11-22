import CubeSections.Certificates.Coverage

/-! Generated from computation/data/pair_trees.json; all arithmetic is proved in Lean. -/
namespace CubeSections.Certificates.Data.Q2M1L1.C000

set_option maxRecDepth 8192
set_option maxHeartbeats 4000000

def parameters : Parameters := ⟨2, 1, 1⟩

private def box_2 : Rectangle := ⟨(1 / 3 : ℚ), (17 / 48 : ℚ), (1 / 3 : ℚ), (17 / 48 : ℚ)⟩
private def node_2 : Tree := .leaf (.strip (125 / 512 : ℚ))
private theorem node_2_accepts : node_2.Accepts parameters box_2 := by
  norm_num [Tree.Accepts, node_2, box_2, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_4 : Rectangle := ⟨(1 / 3 : ℚ), (11 / 32 : ℚ), (17 / 48 : ℚ), (3 / 8 : ℚ)⟩
private def node_4 : Tree := .leaf (.strip (131 / 512 : ℚ))
private theorem node_4_accepts : node_4.Accepts parameters box_4 := by
  norm_num [Tree.Accepts, node_4, box_4, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_6 : Rectangle := ⟨(11 / 32 : ℚ), (17 / 48 : ℚ), (17 / 48 : ℚ), (35 / 96 : ℚ)⟩
private def node_6 : Tree := .leaf (.strip (265 / 1024 : ℚ))
private theorem node_6_accepts : node_6.Accepts parameters box_6 := by
  norm_num [Tree.Accepts, node_6, box_6, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_7 : Rectangle := ⟨(11 / 32 : ℚ), (17 / 48 : ℚ), (35 / 96 : ℚ), (3 / 8 : ℚ)⟩
private def node_7 : Tree := .leaf (.strip (141 / 512 : ℚ))
private theorem node_7_accepts : node_7.Accepts parameters box_7 := by
  norm_num [Tree.Accepts, node_7, box_7, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_5 : Rectangle := ⟨(11 / 32 : ℚ), (17 / 48 : ℚ), (17 / 48 : ℚ), (3 / 8 : ℚ)⟩
private def node_5 : Tree := .splitD (35 / 96 : ℚ) node_6 node_7
private theorem node_5_accepts : node_5.Accepts parameters box_5 := by
  change SplitDValid box_5 (35 / 96 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitDValid, box_5], node_6_accepts, node_7_accepts⟩

private def box_3 : Rectangle := ⟨(1 / 3 : ℚ), (17 / 48 : ℚ), (17 / 48 : ℚ), (3 / 8 : ℚ)⟩
private def node_3 : Tree := .splitC (11 / 32 : ℚ) node_4 node_5
private theorem node_3_accepts : node_3.Accepts parameters box_3 := by
  change SplitCValid box_3 (11 / 32 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitCValid, box_3], node_4_accepts, node_5_accepts⟩

private def box_1 : Rectangle := ⟨(1 / 3 : ℚ), (17 / 48 : ℚ), (1 / 3 : ℚ), (3 / 8 : ℚ)⟩
private def node_1 : Tree := .splitD (17 / 48 : ℚ) node_2 node_3
private theorem node_1_accepts : node_1.Accepts parameters box_1 := by
  change SplitDValid box_1 (17 / 48 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitDValid, box_1], node_2_accepts, node_3_accepts⟩

private def box_10 : Rectangle := ⟨(17 / 48 : ℚ), (35 / 96 : ℚ), (1 / 3 : ℚ), (17 / 48 : ℚ)⟩
private def node_10 : Tree := .leaf (.strip (269 / 1024 : ℚ))
private theorem node_10_accepts : node_10.Accepts parameters box_10 := by
  norm_num [Tree.Accepts, node_10, box_10, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_12 : Rectangle := ⟨(35 / 96 : ℚ), (3 / 8 : ℚ), (1 / 3 : ℚ), (11 / 32 : ℚ)⟩
private def node_12 : Tree := .leaf (.strip (127 / 512 : ℚ))
private theorem node_12_accepts : node_12.Accepts parameters box_12 := by
  norm_num [Tree.Accepts, node_12, box_12, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_13 : Rectangle := ⟨(35 / 96 : ℚ), (3 / 8 : ℚ), (11 / 32 : ℚ), (17 / 48 : ℚ)⟩
private def node_13 : Tree := .leaf (.strip (141 / 512 : ℚ))
private theorem node_13_accepts : node_13.Accepts parameters box_13 := by
  norm_num [Tree.Accepts, node_13, box_13, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_11 : Rectangle := ⟨(35 / 96 : ℚ), (3 / 8 : ℚ), (1 / 3 : ℚ), (17 / 48 : ℚ)⟩
private def node_11 : Tree := .splitD (11 / 32 : ℚ) node_12 node_13
private theorem node_11_accepts : node_11.Accepts parameters box_11 := by
  change SplitDValid box_11 (11 / 32 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitDValid, box_11], node_12_accepts, node_13_accepts⟩

private def box_9 : Rectangle := ⟨(17 / 48 : ℚ), (3 / 8 : ℚ), (1 / 3 : ℚ), (17 / 48 : ℚ)⟩
private def node_9 : Tree := .splitC (35 / 96 : ℚ) node_10 node_11
private theorem node_9_accepts : node_9.Accepts parameters box_9 := by
  change SplitCValid box_9 (35 / 96 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitCValid, box_9], node_10_accepts, node_11_accepts⟩

private def box_16 : Rectangle := ⟨(17 / 48 : ℚ), (35 / 96 : ℚ), (17 / 48 : ℚ), (35 / 96 : ℚ)⟩
private def node_16 : Tree := .leaf (.strip (287 / 1024 : ℚ))
private theorem node_16_accepts : node_16.Accepts parameters box_16 := by
  norm_num [Tree.Accepts, node_16, box_16, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_18 : Rectangle := ⟨(17 / 48 : ℚ), (23 / 64 : ℚ), (35 / 96 : ℚ), (3 / 8 : ℚ)⟩
private def node_18 : Tree := .leaf (.strip (291 / 1024 : ℚ))
private theorem node_18_accepts : node_18.Accepts parameters box_18 := by
  norm_num [Tree.Accepts, node_18, box_18, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_19 : Rectangle := ⟨(23 / 64 : ℚ), (35 / 96 : ℚ), (35 / 96 : ℚ), (3 / 8 : ℚ)⟩
private def node_19 : Tree := .leaf (.strip (301 / 1024 : ℚ))
private theorem node_19_accepts : node_19.Accepts parameters box_19 := by
  norm_num [Tree.Accepts, node_19, box_19, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_17 : Rectangle := ⟨(17 / 48 : ℚ), (35 / 96 : ℚ), (35 / 96 : ℚ), (3 / 8 : ℚ)⟩
private def node_17 : Tree := .splitC (23 / 64 : ℚ) node_18 node_19
private theorem node_17_accepts : node_17.Accepts parameters box_17 := by
  change SplitCValid box_17 (23 / 64 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitCValid, box_17], node_18_accepts, node_19_accepts⟩

private def box_15 : Rectangle := ⟨(17 / 48 : ℚ), (35 / 96 : ℚ), (17 / 48 : ℚ), (3 / 8 : ℚ)⟩
private def node_15 : Tree := .splitD (35 / 96 : ℚ) node_16 node_17
private theorem node_15_accepts : node_15.Accepts parameters box_15 := by
  change SplitDValid box_15 (35 / 96 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitDValid, box_15], node_16_accepts, node_17_accepts⟩

private def box_22 : Rectangle := ⟨(35 / 96 : ℚ), (71 / 192 : ℚ), (17 / 48 : ℚ), (35 / 96 : ℚ)⟩
private def node_22 : Tree := .leaf (.strip (293 / 1024 : ℚ))
private theorem node_22_accepts : node_22.Accepts parameters box_22 := by
  norm_num [Tree.Accepts, node_22, box_22, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_23 : Rectangle := ⟨(71 / 192 : ℚ), (3 / 8 : ℚ), (17 / 48 : ℚ), (35 / 96 : ℚ)⟩
private def node_23 : Tree := .leaf (.strip (75 / 256 : ℚ))
private theorem node_23_accepts : node_23.Accepts parameters box_23 := by
  norm_num [Tree.Accepts, node_23, box_23, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_21 : Rectangle := ⟨(35 / 96 : ℚ), (3 / 8 : ℚ), (17 / 48 : ℚ), (35 / 96 : ℚ)⟩
private def node_21 : Tree := .splitC (71 / 192 : ℚ) node_22 node_23
private theorem node_21_accepts : node_21.Accepts parameters box_21 := by
  change SplitCValid box_21 (71 / 192 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitCValid, box_21], node_22_accepts, node_23_accepts⟩

private def box_25 : Rectangle := ⟨(35 / 96 : ℚ), (71 / 192 : ℚ), (35 / 96 : ℚ), (3 / 8 : ℚ)⟩
private def node_25 : Tree := .leaf (.strip (309 / 1024 : ℚ))
private theorem node_25_accepts : node_25.Accepts parameters box_25 := by
  norm_num [Tree.Accepts, node_25, box_25, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_27 : Rectangle := ⟨(71 / 192 : ℚ), (3 / 8 : ℚ), (35 / 96 : ℚ), (71 / 192 : ℚ)⟩
private def node_27 : Tree := .leaf (.strip (305 / 1024 : ℚ))
private theorem node_27_accepts : node_27.Accepts parameters box_27 := by
  norm_num [Tree.Accepts, node_27, box_27, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_28 : Rectangle := ⟨(71 / 192 : ℚ), (3 / 8 : ℚ), (71 / 192 : ℚ), (3 / 8 : ℚ)⟩
private def node_28 : Tree := .leaf (.strip (313 / 1024 : ℚ))
private theorem node_28_accepts : node_28.Accepts parameters box_28 := by
  norm_num [Tree.Accepts, node_28, box_28, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_26 : Rectangle := ⟨(71 / 192 : ℚ), (3 / 8 : ℚ), (35 / 96 : ℚ), (3 / 8 : ℚ)⟩
private def node_26 : Tree := .splitD (71 / 192 : ℚ) node_27 node_28
private theorem node_26_accepts : node_26.Accepts parameters box_26 := by
  change SplitDValid box_26 (71 / 192 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitDValid, box_26], node_27_accepts, node_28_accepts⟩

private def box_24 : Rectangle := ⟨(35 / 96 : ℚ), (3 / 8 : ℚ), (35 / 96 : ℚ), (3 / 8 : ℚ)⟩
private def node_24 : Tree := .splitC (71 / 192 : ℚ) node_25 node_26
private theorem node_24_accepts : node_24.Accepts parameters box_24 := by
  change SplitCValid box_24 (71 / 192 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitCValid, box_24], node_25_accepts, node_26_accepts⟩

private def box_20 : Rectangle := ⟨(35 / 96 : ℚ), (3 / 8 : ℚ), (17 / 48 : ℚ), (3 / 8 : ℚ)⟩
private def node_20 : Tree := .splitD (35 / 96 : ℚ) node_21 node_24
private theorem node_20_accepts : node_20.Accepts parameters box_20 := by
  change SplitDValid box_20 (35 / 96 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitDValid, box_20], node_21_accepts, node_24_accepts⟩

private def box_14 : Rectangle := ⟨(17 / 48 : ℚ), (3 / 8 : ℚ), (17 / 48 : ℚ), (3 / 8 : ℚ)⟩
private def node_14 : Tree := .splitC (35 / 96 : ℚ) node_15 node_20
private theorem node_14_accepts : node_14.Accepts parameters box_14 := by
  change SplitCValid box_14 (35 / 96 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitCValid, box_14], node_15_accepts, node_20_accepts⟩

private def box_8 : Rectangle := ⟨(17 / 48 : ℚ), (3 / 8 : ℚ), (1 / 3 : ℚ), (3 / 8 : ℚ)⟩
private def node_8 : Tree := .splitD (17 / 48 : ℚ) node_9 node_14
private theorem node_8_accepts : node_8.Accepts parameters box_8 := by
  change SplitDValid box_8 (17 / 48 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitDValid, box_8], node_9_accepts, node_14_accepts⟩

private def box_0 : Rectangle := ⟨(1 / 3 : ℚ), (3 / 8 : ℚ), (1 / 3 : ℚ), (3 / 8 : ℚ)⟩
private def node_0 : Tree := .splitC (17 / 48 : ℚ) node_1 node_8
private theorem node_0_accepts : node_0.Accepts parameters box_0 := by
  change SplitCValid box_0 (17 / 48 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitCValid, box_0], node_1_accepts, node_8_accepts⟩

def tree : Tree := node_0
def rootBox : Rectangle := box_0
theorem accepted : tree.Accepts parameters rootBox := node_0_accepts

end CubeSections.Certificates.Data.Q2M1L1.C000
