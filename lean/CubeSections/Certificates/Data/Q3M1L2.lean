import CubeSections.Certificates.Coverage

/-! Generated from computation/data/pair_trees.json; all arithmetic is proved in Lean. -/
namespace CubeSections.Certificates.Data.Q3M1L2

set_option maxRecDepth 8192
set_option maxHeartbeats 4000000

def parameters : Parameters := ⟨3, 1, 2⟩

private def box_5 : Rectangle := ⟨(1 / 4 : ℚ), (25 / 96 : ℚ), (1 / 4 : ℚ), (13 / 48 : ℚ)⟩
private def node_5 : Tree := .leaf (.strip (219 / 1024 : ℚ))
private theorem node_5_accepts : node_5.Accepts parameters box_5 := by
  norm_num [Tree.Accepts, node_5, box_5, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_7 : Rectangle := ⟨(25 / 96 : ℚ), (13 / 48 : ℚ), (1 / 4 : ℚ), (25 / 96 : ℚ)⟩
private def node_7 : Tree := .leaf (.strip (49 / 256 : ℚ))
private theorem node_7_accepts : node_7.Accepts parameters box_7 := by
  norm_num [Tree.Accepts, node_7, box_7, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_8 : Rectangle := ⟨(25 / 96 : ℚ), (13 / 48 : ℚ), (25 / 96 : ℚ), (13 / 48 : ℚ)⟩
private def node_8 : Tree := .leaf (.strip (229 / 1024 : ℚ))
private theorem node_8_accepts : node_8.Accepts parameters box_8 := by
  norm_num [Tree.Accepts, node_8, box_8, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_6 : Rectangle := ⟨(25 / 96 : ℚ), (13 / 48 : ℚ), (1 / 4 : ℚ), (13 / 48 : ℚ)⟩
private def node_6 : Tree := .splitD (25 / 96 : ℚ) node_7 node_8
private theorem node_6_accepts : node_6.Accepts parameters box_6 := by
  change SplitDValid box_6 (25 / 96 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitDValid, box_6], node_7_accepts, node_8_accepts⟩

private def box_4 : Rectangle := ⟨(1 / 4 : ℚ), (13 / 48 : ℚ), (1 / 4 : ℚ), (13 / 48 : ℚ)⟩
private def node_4 : Tree := .splitC (25 / 96 : ℚ) node_5 node_6
private theorem node_4_accepts : node_4.Accepts parameters box_4 := by
  change SplitCValid box_4 (25 / 96 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitCValid, box_4], node_5_accepts, node_6_accepts⟩

private def box_11 : Rectangle := ⟨(1 / 4 : ℚ), (25 / 96 : ℚ), (13 / 48 : ℚ), (9 / 32 : ℚ)⟩
private def node_11 : Tree := .leaf (.strip (115 / 512 : ℚ))
private theorem node_11_accepts : node_11.Accepts parameters box_11 := by
  norm_num [Tree.Accepts, node_11, box_11, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_12 : Rectangle := ⟨(1 / 4 : ℚ), (25 / 96 : ℚ), (9 / 32 : ℚ), (7 / 24 : ℚ)⟩
private def node_12 : Tree := .leaf (.strip (239 / 1024 : ℚ))
private theorem node_12_accepts : node_12.Accepts parameters box_12 := by
  norm_num [Tree.Accepts, node_12, box_12, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_10 : Rectangle := ⟨(1 / 4 : ℚ), (25 / 96 : ℚ), (13 / 48 : ℚ), (7 / 24 : ℚ)⟩
private def node_10 : Tree := .splitD (9 / 32 : ℚ) node_11 node_12
private theorem node_10_accepts : node_10.Accepts parameters box_10 := by
  change SplitDValid box_10 (9 / 32 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitDValid, box_10], node_11_accepts, node_12_accepts⟩

private def box_14 : Rectangle := ⟨(25 / 96 : ℚ), (13 / 48 : ℚ), (13 / 48 : ℚ), (9 / 32 : ℚ)⟩
private def node_14 : Tree := .leaf (.strip (31 / 128 : ℚ))
private theorem node_14_accepts : node_14.Accepts parameters box_14 := by
  norm_num [Tree.Accepts, node_14, box_14, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_15 : Rectangle := ⟨(25 / 96 : ℚ), (13 / 48 : ℚ), (9 / 32 : ℚ), (7 / 24 : ℚ)⟩
private def node_15 : Tree := .leaf (.strip (257 / 1024 : ℚ))
private theorem node_15_accepts : node_15.Accepts parameters box_15 := by
  norm_num [Tree.Accepts, node_15, box_15, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_13 : Rectangle := ⟨(25 / 96 : ℚ), (13 / 48 : ℚ), (13 / 48 : ℚ), (7 / 24 : ℚ)⟩
private def node_13 : Tree := .splitD (9 / 32 : ℚ) node_14 node_15
private theorem node_13_accepts : node_13.Accepts parameters box_13 := by
  change SplitDValid box_13 (9 / 32 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitDValid, box_13], node_14_accepts, node_15_accepts⟩

private def box_9 : Rectangle := ⟨(1 / 4 : ℚ), (13 / 48 : ℚ), (13 / 48 : ℚ), (7 / 24 : ℚ)⟩
private def node_9 : Tree := .splitC (25 / 96 : ℚ) node_10 node_13
private theorem node_9_accepts : node_9.Accepts parameters box_9 := by
  change SplitCValid box_9 (25 / 96 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitCValid, box_9], node_10_accepts, node_13_accepts⟩

private def box_3 : Rectangle := ⟨(1 / 4 : ℚ), (13 / 48 : ℚ), (1 / 4 : ℚ), (7 / 24 : ℚ)⟩
private def node_3 : Tree := .splitD (13 / 48 : ℚ) node_4 node_9
private theorem node_3_accepts : node_3.Accepts parameters box_3 := by
  change SplitDValid box_3 (13 / 48 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitDValid, box_3], node_4_accepts, node_9_accepts⟩

private def box_19 : Rectangle := ⟨(13 / 48 : ℚ), (9 / 32 : ℚ), (1 / 4 : ℚ), (25 / 96 : ℚ)⟩
private def node_19 : Tree := .leaf (.strip (209 / 1024 : ℚ))
private theorem node_19_accepts : node_19.Accepts parameters box_19 := by
  norm_num [Tree.Accepts, node_19, box_19, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_20 : Rectangle := ⟨(13 / 48 : ℚ), (9 / 32 : ℚ), (25 / 96 : ℚ), (13 / 48 : ℚ)⟩
private def node_20 : Tree := .leaf (.strip (15 / 64 : ℚ))
private theorem node_20_accepts : node_20.Accepts parameters box_20 := by
  norm_num [Tree.Accepts, node_20, box_20, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_18 : Rectangle := ⟨(13 / 48 : ℚ), (9 / 32 : ℚ), (1 / 4 : ℚ), (13 / 48 : ℚ)⟩
private def node_18 : Tree := .splitD (25 / 96 : ℚ) node_19 node_20
private theorem node_18_accepts : node_18.Accepts parameters box_18 := by
  change SplitDValid box_18 (25 / 96 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitDValid, box_18], node_19_accepts, node_20_accepts⟩

private def box_22 : Rectangle := ⟨(9 / 32 : ℚ), (7 / 24 : ℚ), (1 / 4 : ℚ), (25 / 96 : ℚ)⟩
private def node_22 : Tree := .leaf (.strip (213 / 1024 : ℚ))
private theorem node_22_accepts : node_22.Accepts parameters box_22 := by
  norm_num [Tree.Accepts, node_22, box_22, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_23 : Rectangle := ⟨(9 / 32 : ℚ), (7 / 24 : ℚ), (25 / 96 : ℚ), (13 / 48 : ℚ)⟩
private def node_23 : Tree := .leaf (.strip (61 / 256 : ℚ))
private theorem node_23_accepts : node_23.Accepts parameters box_23 := by
  norm_num [Tree.Accepts, node_23, box_23, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_21 : Rectangle := ⟨(9 / 32 : ℚ), (7 / 24 : ℚ), (1 / 4 : ℚ), (13 / 48 : ℚ)⟩
private def node_21 : Tree := .splitD (25 / 96 : ℚ) node_22 node_23
private theorem node_21_accepts : node_21.Accepts parameters box_21 := by
  change SplitDValid box_21 (25 / 96 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitDValid, box_21], node_22_accepts, node_23_accepts⟩

private def box_17 : Rectangle := ⟨(13 / 48 : ℚ), (7 / 24 : ℚ), (1 / 4 : ℚ), (13 / 48 : ℚ)⟩
private def node_17 : Tree := .splitC (9 / 32 : ℚ) node_18 node_21
private theorem node_17_accepts : node_17.Accepts parameters box_17 := by
  change SplitCValid box_17 (9 / 32 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitCValid, box_17], node_18_accepts, node_21_accepts⟩

private def box_26 : Rectangle := ⟨(13 / 48 : ℚ), (9 / 32 : ℚ), (13 / 48 : ℚ), (9 / 32 : ℚ)⟩
private def node_26 : Tree := .leaf (.strip (259 / 1024 : ℚ))
private theorem node_26_accepts : node_26.Accepts parameters box_26 := by
  norm_num [Tree.Accepts, node_26, box_26, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_27 : Rectangle := ⟨(13 / 48 : ℚ), (9 / 32 : ℚ), (9 / 32 : ℚ), (7 / 24 : ℚ)⟩
private def node_27 : Tree := .leaf (.strip (267 / 1024 : ℚ))
private theorem node_27_accepts : node_27.Accepts parameters box_27 := by
  norm_num [Tree.Accepts, node_27, box_27, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_25 : Rectangle := ⟨(13 / 48 : ℚ), (9 / 32 : ℚ), (13 / 48 : ℚ), (7 / 24 : ℚ)⟩
private def node_25 : Tree := .splitD (9 / 32 : ℚ) node_26 node_27
private theorem node_25_accepts : node_25.Accepts parameters box_25 := by
  change SplitDValid box_25 (9 / 32 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitDValid, box_25], node_26_accepts, node_27_accepts⟩

private def box_29 : Rectangle := ⟨(9 / 32 : ℚ), (7 / 24 : ℚ), (13 / 48 : ℚ), (9 / 32 : ℚ)⟩
private def node_29 : Tree := .leaf (.strip (131 / 512 : ℚ))
private theorem node_29_accepts : node_29.Accepts parameters box_29 := by
  norm_num [Tree.Accepts, node_29, box_29, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_30 : Rectangle := ⟨(9 / 32 : ℚ), (7 / 24 : ℚ), (9 / 32 : ℚ), (7 / 24 : ℚ)⟩
private def node_30 : Tree := .leaf (.strip (135 / 512 : ℚ))
private theorem node_30_accepts : node_30.Accepts parameters box_30 := by
  norm_num [Tree.Accepts, node_30, box_30, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_28 : Rectangle := ⟨(9 / 32 : ℚ), (7 / 24 : ℚ), (13 / 48 : ℚ), (7 / 24 : ℚ)⟩
private def node_28 : Tree := .splitD (9 / 32 : ℚ) node_29 node_30
private theorem node_28_accepts : node_28.Accepts parameters box_28 := by
  change SplitDValid box_28 (9 / 32 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitDValid, box_28], node_29_accepts, node_30_accepts⟩

private def box_24 : Rectangle := ⟨(13 / 48 : ℚ), (7 / 24 : ℚ), (13 / 48 : ℚ), (7 / 24 : ℚ)⟩
private def node_24 : Tree := .splitC (9 / 32 : ℚ) node_25 node_28
private theorem node_24_accepts : node_24.Accepts parameters box_24 := by
  change SplitCValid box_24 (9 / 32 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitCValid, box_24], node_25_accepts, node_28_accepts⟩

private def box_16 : Rectangle := ⟨(13 / 48 : ℚ), (7 / 24 : ℚ), (1 / 4 : ℚ), (7 / 24 : ℚ)⟩
private def node_16 : Tree := .splitD (13 / 48 : ℚ) node_17 node_24
private theorem node_16_accepts : node_16.Accepts parameters box_16 := by
  change SplitDValid box_16 (13 / 48 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitDValid, box_16], node_17_accepts, node_24_accepts⟩

private def box_2 : Rectangle := ⟨(1 / 4 : ℚ), (7 / 24 : ℚ), (1 / 4 : ℚ), (7 / 24 : ℚ)⟩
private def node_2 : Tree := .splitC (13 / 48 : ℚ) node_3 node_16
private theorem node_2_accepts : node_2.Accepts parameters box_2 := by
  change SplitCValid box_2 (13 / 48 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitCValid, box_2], node_3_accepts, node_16_accepts⟩

private def box_35 : Rectangle := ⟨(1 / 4 : ℚ), (25 / 96 : ℚ), (7 / 24 : ℚ), (29 / 96 : ℚ)⟩
private def node_35 : Tree := .leaf (.strip (237 / 1024 : ℚ))
private theorem node_35_accepts : node_35.Accepts parameters box_35 := by
  norm_num [Tree.Accepts, node_35, box_35, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_36 : Rectangle := ⟨(1 / 4 : ℚ), (25 / 96 : ℚ), (29 / 96 : ℚ), (5 / 16 : ℚ)⟩
private def node_36 : Tree := .leaf (.strip (113 / 512 : ℚ))
private theorem node_36_accepts : node_36.Accepts parameters box_36 := by
  norm_num [Tree.Accepts, node_36, box_36, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_34 : Rectangle := ⟨(1 / 4 : ℚ), (25 / 96 : ℚ), (7 / 24 : ℚ), (5 / 16 : ℚ)⟩
private def node_34 : Tree := .splitD (29 / 96 : ℚ) node_35 node_36
private theorem node_34_accepts : node_34.Accepts parameters box_34 := by
  change SplitDValid box_34 (29 / 96 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitDValid, box_34], node_35_accepts, node_36_accepts⟩

private def box_38 : Rectangle := ⟨(25 / 96 : ℚ), (13 / 48 : ℚ), (7 / 24 : ℚ), (29 / 96 : ℚ)⟩
private def node_38 : Tree := .leaf (.strip (1 / 4 : ℚ))
private theorem node_38_accepts : node_38.Accepts parameters box_38 := by
  norm_num [Tree.Accepts, node_38, box_38, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_39 : Rectangle := ⟨(25 / 96 : ℚ), (13 / 48 : ℚ), (29 / 96 : ℚ), (5 / 16 : ℚ)⟩
private def node_39 : Tree := .leaf (.strip (245 / 1024 : ℚ))
private theorem node_39_accepts : node_39.Accepts parameters box_39 := by
  norm_num [Tree.Accepts, node_39, box_39, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_37 : Rectangle := ⟨(25 / 96 : ℚ), (13 / 48 : ℚ), (7 / 24 : ℚ), (5 / 16 : ℚ)⟩
private def node_37 : Tree := .splitD (29 / 96 : ℚ) node_38 node_39
private theorem node_37_accepts : node_37.Accepts parameters box_37 := by
  change SplitDValid box_37 (29 / 96 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitDValid, box_37], node_38_accepts, node_39_accepts⟩

private def box_33 : Rectangle := ⟨(1 / 4 : ℚ), (13 / 48 : ℚ), (7 / 24 : ℚ), (5 / 16 : ℚ)⟩
private def node_33 : Tree := .splitC (25 / 96 : ℚ) node_34 node_37
private theorem node_33_accepts : node_33.Accepts parameters box_33 := by
  change SplitCValid box_33 (25 / 96 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitCValid, box_33], node_34_accepts, node_37_accepts⟩

private def box_40 : Rectangle := ⟨(1 / 4 : ℚ), (13 / 48 : ℚ), (5 / 16 : ℚ), (1 / 3 : ℚ)⟩
private def node_40 : Tree := .leaf (.strip (119 / 512 : ℚ))
private theorem node_40_accepts : node_40.Accepts parameters box_40 := by
  norm_num [Tree.Accepts, node_40, box_40, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_32 : Rectangle := ⟨(1 / 4 : ℚ), (13 / 48 : ℚ), (7 / 24 : ℚ), (1 / 3 : ℚ)⟩
private def node_32 : Tree := .splitD (5 / 16 : ℚ) node_33 node_40
private theorem node_32_accepts : node_32.Accepts parameters box_32 := by
  change SplitDValid box_32 (5 / 16 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitDValid, box_32], node_33_accepts, node_40_accepts⟩

private def box_44 : Rectangle := ⟨(13 / 48 : ℚ), (9 / 32 : ℚ), (7 / 24 : ℚ), (29 / 96 : ℚ)⟩
private def node_44 : Tree := .leaf (.strip (133 / 512 : ℚ))
private theorem node_44_accepts : node_44.Accepts parameters box_44 := by
  norm_num [Tree.Accepts, node_44, box_44, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_45 : Rectangle := ⟨(13 / 48 : ℚ), (9 / 32 : ℚ), (29 / 96 : ℚ), (5 / 16 : ℚ)⟩
private def node_45 : Tree := .leaf (.strip (255 / 1024 : ℚ))
private theorem node_45_accepts : node_45.Accepts parameters box_45 := by
  norm_num [Tree.Accepts, node_45, box_45, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_43 : Rectangle := ⟨(13 / 48 : ℚ), (9 / 32 : ℚ), (7 / 24 : ℚ), (5 / 16 : ℚ)⟩
private def node_43 : Tree := .splitD (29 / 96 : ℚ) node_44 node_45
private theorem node_43_accepts : node_43.Accepts parameters box_43 := by
  change SplitDValid box_43 (29 / 96 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitDValid, box_43], node_44_accepts, node_45_accepts⟩

private def box_46 : Rectangle := ⟨(9 / 32 : ℚ), (7 / 24 : ℚ), (7 / 24 : ℚ), (5 / 16 : ℚ)⟩
private def node_46 : Tree := .leaf (.strip (71 / 256 : ℚ))
private theorem node_46_accepts : node_46.Accepts parameters box_46 := by
  norm_num [Tree.Accepts, node_46, box_46, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_42 : Rectangle := ⟨(13 / 48 : ℚ), (7 / 24 : ℚ), (7 / 24 : ℚ), (5 / 16 : ℚ)⟩
private def node_42 : Tree := .splitC (9 / 32 : ℚ) node_43 node_46
private theorem node_42_accepts : node_42.Accepts parameters box_42 := by
  change SplitCValid box_42 (9 / 32 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitCValid, box_42], node_43_accepts, node_46_accepts⟩

private def box_47 : Rectangle := ⟨(13 / 48 : ℚ), (7 / 24 : ℚ), (5 / 16 : ℚ), (1 / 3 : ℚ)⟩
private def node_47 : Tree := .leaf (.strip (257 / 1024 : ℚ))
private theorem node_47_accepts : node_47.Accepts parameters box_47 := by
  norm_num [Tree.Accepts, node_47, box_47, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_41 : Rectangle := ⟨(13 / 48 : ℚ), (7 / 24 : ℚ), (7 / 24 : ℚ), (1 / 3 : ℚ)⟩
private def node_41 : Tree := .splitD (5 / 16 : ℚ) node_42 node_47
private theorem node_41_accepts : node_41.Accepts parameters box_41 := by
  change SplitDValid box_41 (5 / 16 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitDValid, box_41], node_42_accepts, node_47_accepts⟩

private def box_31 : Rectangle := ⟨(1 / 4 : ℚ), (7 / 24 : ℚ), (7 / 24 : ℚ), (1 / 3 : ℚ)⟩
private def node_31 : Tree := .splitC (13 / 48 : ℚ) node_32 node_41
private theorem node_31_accepts : node_31.Accepts parameters box_31 := by
  change SplitCValid box_31 (13 / 48 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitCValid, box_31], node_32_accepts, node_41_accepts⟩

private def box_1 : Rectangle := ⟨(1 / 4 : ℚ), (7 / 24 : ℚ), (1 / 4 : ℚ), (1 / 3 : ℚ)⟩
private def node_1 : Tree := .splitD (7 / 24 : ℚ) node_2 node_31
private theorem node_1_accepts : node_1.Accepts parameters box_1 := by
  change SplitDValid box_1 (7 / 24 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitDValid, box_1], node_2_accepts, node_31_accepts⟩

private def box_53 : Rectangle := ⟨(7 / 24 : ℚ), (29 / 96 : ℚ), (1 / 4 : ℚ), (25 / 96 : ℚ)⟩
private def node_53 : Tree := .leaf (.strip (105 / 512 : ℚ))
private theorem node_53_accepts : node_53.Accepts parameters box_53 := by
  norm_num [Tree.Accepts, node_53, box_53, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_54 : Rectangle := ⟨(7 / 24 : ℚ), (29 / 96 : ℚ), (25 / 96 : ℚ), (13 / 48 : ℚ)⟩
private def node_54 : Tree := .leaf (.strip (241 / 1024 : ℚ))
private theorem node_54_accepts : node_54.Accepts parameters box_54 := by
  norm_num [Tree.Accepts, node_54, box_54, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_52 : Rectangle := ⟨(7 / 24 : ℚ), (29 / 96 : ℚ), (1 / 4 : ℚ), (13 / 48 : ℚ)⟩
private def node_52 : Tree := .splitD (25 / 96 : ℚ) node_53 node_54
private theorem node_52_accepts : node_52.Accepts parameters box_52 := by
  change SplitDValid box_52 (25 / 96 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitDValid, box_52], node_53_accepts, node_54_accepts⟩

private def box_55 : Rectangle := ⟨(29 / 96 : ℚ), (5 / 16 : ℚ), (1 / 4 : ℚ), (13 / 48 : ℚ)⟩
private def node_55 : Tree := .leaf (.strip (121 / 512 : ℚ))
private theorem node_55_accepts : node_55.Accepts parameters box_55 := by
  norm_num [Tree.Accepts, node_55, box_55, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_51 : Rectangle := ⟨(7 / 24 : ℚ), (5 / 16 : ℚ), (1 / 4 : ℚ), (13 / 48 : ℚ)⟩
private def node_51 : Tree := .splitC (29 / 96 : ℚ) node_52 node_55
private theorem node_51_accepts : node_51.Accepts parameters box_51 := by
  change SplitCValid box_51 (29 / 96 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitCValid, box_51], node_52_accepts, node_55_accepts⟩

private def box_58 : Rectangle := ⟨(7 / 24 : ℚ), (29 / 96 : ℚ), (13 / 48 : ℚ), (9 / 32 : ℚ)⟩
private def node_58 : Tree := .leaf (.strip (65 / 256 : ℚ))
private theorem node_58_accepts : node_58.Accepts parameters box_58 := by
  norm_num [Tree.Accepts, node_58, box_58, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_59 : Rectangle := ⟨(7 / 24 : ℚ), (29 / 96 : ℚ), (9 / 32 : ℚ), (7 / 24 : ℚ)⟩
private def node_59 : Tree := .leaf (.strip (67 / 256 : ℚ))
private theorem node_59_accepts : node_59.Accepts parameters box_59 := by
  norm_num [Tree.Accepts, node_59, box_59, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_57 : Rectangle := ⟨(7 / 24 : ℚ), (29 / 96 : ℚ), (13 / 48 : ℚ), (7 / 24 : ℚ)⟩
private def node_57 : Tree := .splitD (9 / 32 : ℚ) node_58 node_59
private theorem node_57_accepts : node_57.Accepts parameters box_57 := by
  change SplitDValid box_57 (9 / 32 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitDValid, box_57], node_58_accepts, node_59_accepts⟩

private def box_60 : Rectangle := ⟨(29 / 96 : ℚ), (5 / 16 : ℚ), (13 / 48 : ℚ), (7 / 24 : ℚ)⟩
private def node_60 : Tree := .leaf (.strip (277 / 1024 : ℚ))
private theorem node_60_accepts : node_60.Accepts parameters box_60 := by
  norm_num [Tree.Accepts, node_60, box_60, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_56 : Rectangle := ⟨(7 / 24 : ℚ), (5 / 16 : ℚ), (13 / 48 : ℚ), (7 / 24 : ℚ)⟩
private def node_56 : Tree := .splitC (29 / 96 : ℚ) node_57 node_60
private theorem node_56_accepts : node_56.Accepts parameters box_56 := by
  change SplitCValid box_56 (29 / 96 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitCValid, box_56], node_57_accepts, node_60_accepts⟩

private def box_50 : Rectangle := ⟨(7 / 24 : ℚ), (5 / 16 : ℚ), (1 / 4 : ℚ), (7 / 24 : ℚ)⟩
private def node_50 : Tree := .splitD (13 / 48 : ℚ) node_51 node_56
private theorem node_50_accepts : node_50.Accepts parameters box_50 := by
  change SplitDValid box_50 (13 / 48 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitDValid, box_50], node_51_accepts, node_56_accepts⟩

private def box_62 : Rectangle := ⟨(5 / 16 : ℚ), (1 / 3 : ℚ), (1 / 4 : ℚ), (13 / 48 : ℚ)⟩
private def node_62 : Tree := .leaf (.strip (29 / 128 : ℚ))
private theorem node_62_accepts : node_62.Accepts parameters box_62 := by
  norm_num [Tree.Accepts, node_62, box_62, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_63 : Rectangle := ⟨(5 / 16 : ℚ), (1 / 3 : ℚ), (13 / 48 : ℚ), (7 / 24 : ℚ)⟩
private def node_63 : Tree := .leaf (.strip (67 / 256 : ℚ))
private theorem node_63_accepts : node_63.Accepts parameters box_63 := by
  norm_num [Tree.Accepts, node_63, box_63, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_61 : Rectangle := ⟨(5 / 16 : ℚ), (1 / 3 : ℚ), (1 / 4 : ℚ), (7 / 24 : ℚ)⟩
private def node_61 : Tree := .splitD (13 / 48 : ℚ) node_62 node_63
private theorem node_61_accepts : node_61.Accepts parameters box_61 := by
  change SplitDValid box_61 (13 / 48 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitDValid, box_61], node_62_accepts, node_63_accepts⟩

private def box_49 : Rectangle := ⟨(7 / 24 : ℚ), (1 / 3 : ℚ), (1 / 4 : ℚ), (7 / 24 : ℚ)⟩
private def node_49 : Tree := .splitC (5 / 16 : ℚ) node_50 node_61
private theorem node_49_accepts : node_49.Accepts parameters box_49 := by
  change SplitCValid box_49 (5 / 16 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitCValid, box_49], node_50_accepts, node_61_accepts⟩

private def box_66 : Rectangle := ⟨(7 / 24 : ℚ), (5 / 16 : ℚ), (7 / 24 : ℚ), (5 / 16 : ℚ)⟩
private def node_66 : Tree := .leaf (.strip (145 / 512 : ℚ))
private theorem node_66_accepts : node_66.Accepts parameters box_66 := by
  norm_num [Tree.Accepts, node_66, box_66, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_67 : Rectangle := ⟨(7 / 24 : ℚ), (5 / 16 : ℚ), (5 / 16 : ℚ), (1 / 3 : ℚ)⟩
private def node_67 : Tree := .leaf (.strip (251 / 1024 : ℚ))
private theorem node_67_accepts : node_67.Accepts parameters box_67 := by
  norm_num [Tree.Accepts, node_67, box_67, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_65 : Rectangle := ⟨(7 / 24 : ℚ), (5 / 16 : ℚ), (7 / 24 : ℚ), (1 / 3 : ℚ)⟩
private def node_65 : Tree := .splitD (5 / 16 : ℚ) node_66 node_67
private theorem node_65_accepts : node_65.Accepts parameters box_65 := by
  change SplitDValid box_65 (5 / 16 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitDValid, box_65], node_66_accepts, node_67_accepts⟩

private def box_68 : Rectangle := ⟨(5 / 16 : ℚ), (1 / 3 : ℚ), (7 / 24 : ℚ), (1 / 3 : ℚ)⟩
private def node_68 : Tree := .leaf (.strip (73 / 256 : ℚ))
private theorem node_68_accepts : node_68.Accepts parameters box_68 := by
  norm_num [Tree.Accepts, node_68, box_68, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_64 : Rectangle := ⟨(7 / 24 : ℚ), (1 / 3 : ℚ), (7 / 24 : ℚ), (1 / 3 : ℚ)⟩
private def node_64 : Tree := .splitC (5 / 16 : ℚ) node_65 node_68
private theorem node_64_accepts : node_64.Accepts parameters box_64 := by
  change SplitCValid box_64 (5 / 16 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitCValid, box_64], node_65_accepts, node_68_accepts⟩

private def box_48 : Rectangle := ⟨(7 / 24 : ℚ), (1 / 3 : ℚ), (1 / 4 : ℚ), (1 / 3 : ℚ)⟩
private def node_48 : Tree := .splitD (7 / 24 : ℚ) node_49 node_64
private theorem node_48_accepts : node_48.Accepts parameters box_48 := by
  change SplitDValid box_48 (7 / 24 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitDValid, box_48], node_49_accepts, node_64_accepts⟩

private def box_0 : Rectangle := ⟨(1 / 4 : ℚ), (1 / 3 : ℚ), (1 / 4 : ℚ), (1 / 3 : ℚ)⟩
private def node_0 : Tree := .splitC (7 / 24 : ℚ) node_1 node_48
private theorem node_0_accepts : node_0.Accepts parameters box_0 := by
  change SplitCValid box_0 (7 / 24 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitCValid, box_0], node_1_accepts, node_48_accepts⟩

def tree : Tree := node_0
theorem accepted : tree.Accepts parameters (rootRectangle parameters.q) := by
  have hb : box_0 = rootRectangle parameters.q := by
    norm_num [box_0, rootRectangle, parameters]
  simpa only [tree, ← hb] using node_0_accepts

theorem checked : tree.check parameters (rootRectangle parameters.q) = true :=
  (tree.check_eq_true_iff parameters (rootRectangle parameters.q)).mpr accepted

#print axioms accepted
#print axioms checked

end CubeSections.Certificates.Data.Q3M1L2
