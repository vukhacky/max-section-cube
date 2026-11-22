import CubeSections.Certificates.Coverage

/-! Generated from computation/data/pair_trees.json; all arithmetic is proved in Lean. -/
namespace CubeSections.Certificates.Data.Q3M1L1

set_option maxRecDepth 8192
set_option maxHeartbeats 4000000

def parameters : Parameters := ⟨3, 1, 1⟩

private def box_5 : Rectangle := ⟨(1 / 4 : ℚ), (25 / 96 : ℚ), (1 / 4 : ℚ), (13 / 48 : ℚ)⟩
private def node_5 : Tree := .leaf (.strip (25 / 128 : ℚ))
private theorem node_5_accepts : node_5.Accepts parameters box_5 := by
  norm_num [Tree.Accepts, node_5, box_5, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_7 : Rectangle := ⟨(25 / 96 : ℚ), (13 / 48 : ℚ), (1 / 4 : ℚ), (25 / 96 : ℚ)⟩
private def node_7 : Tree := .leaf (.strip (95 / 512 : ℚ))
private theorem node_7_accepts : node_7.Accepts parameters box_7 := by
  norm_num [Tree.Accepts, node_7, box_7, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_8 : Rectangle := ⟨(25 / 96 : ℚ), (13 / 48 : ℚ), (25 / 96 : ℚ), (13 / 48 : ℚ)⟩
private def node_8 : Tree := .leaf (.strip (107 / 512 : ℚ))
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
private def node_11 : Tree := .leaf (.strip (205 / 1024 : ℚ))
private theorem node_11_accepts : node_11.Accepts parameters box_11 := by
  norm_num [Tree.Accepts, node_11, box_11, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_12 : Rectangle := ⟨(1 / 4 : ℚ), (25 / 96 : ℚ), (9 / 32 : ℚ), (7 / 24 : ℚ)⟩
private def node_12 : Tree := .leaf (.strip (209 / 1024 : ℚ))
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

private def box_15 : Rectangle := ⟨(25 / 96 : ℚ), (17 / 64 : ℚ), (13 / 48 : ℚ), (9 / 32 : ℚ)⟩
private def node_15 : Tree := .leaf (.strip (107 / 512 : ℚ))
private theorem node_15_accepts : node_15.Accepts parameters box_15 := by
  norm_num [Tree.Accepts, node_15, box_15, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_16 : Rectangle := ⟨(17 / 64 : ℚ), (13 / 48 : ℚ), (13 / 48 : ℚ), (9 / 32 : ℚ)⟩
private def node_16 : Tree := .leaf (.strip (223 / 1024 : ℚ))
private theorem node_16_accepts : node_16.Accepts parameters box_16 := by
  norm_num [Tree.Accepts, node_16, box_16, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_14 : Rectangle := ⟨(25 / 96 : ℚ), (13 / 48 : ℚ), (13 / 48 : ℚ), (9 / 32 : ℚ)⟩
private def node_14 : Tree := .splitC (17 / 64 : ℚ) node_15 node_16
private theorem node_14_accepts : node_14.Accepts parameters box_14 := by
  change SplitCValid box_14 (17 / 64 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitCValid, box_14], node_15_accepts, node_16_accepts⟩

private def box_18 : Rectangle := ⟨(25 / 96 : ℚ), (17 / 64 : ℚ), (9 / 32 : ℚ), (7 / 24 : ℚ)⟩
private def node_18 : Tree := .leaf (.strip (219 / 1024 : ℚ))
private theorem node_18_accepts : node_18.Accepts parameters box_18 := by
  norm_num [Tree.Accepts, node_18, box_18, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_19 : Rectangle := ⟨(17 / 64 : ℚ), (13 / 48 : ℚ), (9 / 32 : ℚ), (7 / 24 : ℚ)⟩
private def node_19 : Tree := .leaf (.strip (57 / 256 : ℚ))
private theorem node_19_accepts : node_19.Accepts parameters box_19 := by
  norm_num [Tree.Accepts, node_19, box_19, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_17 : Rectangle := ⟨(25 / 96 : ℚ), (13 / 48 : ℚ), (9 / 32 : ℚ), (7 / 24 : ℚ)⟩
private def node_17 : Tree := .splitC (17 / 64 : ℚ) node_18 node_19
private theorem node_17_accepts : node_17.Accepts parameters box_17 := by
  change SplitCValid box_17 (17 / 64 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitCValid, box_17], node_18_accepts, node_19_accepts⟩

private def box_13 : Rectangle := ⟨(25 / 96 : ℚ), (13 / 48 : ℚ), (13 / 48 : ℚ), (7 / 24 : ℚ)⟩
private def node_13 : Tree := .splitD (9 / 32 : ℚ) node_14 node_17
private theorem node_13_accepts : node_13.Accepts parameters box_13 := by
  change SplitDValid box_13 (9 / 32 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitDValid, box_13], node_14_accepts, node_17_accepts⟩

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

private def box_23 : Rectangle := ⟨(13 / 48 : ℚ), (9 / 32 : ℚ), (1 / 4 : ℚ), (25 / 96 : ℚ)⟩
private def node_23 : Tree := .leaf (.strip (205 / 1024 : ℚ))
private theorem node_23_accepts : node_23.Accepts parameters box_23 := by
  norm_num [Tree.Accepts, node_23, box_23, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_25 : Rectangle := ⟨(13 / 48 : ℚ), (53 / 192 : ℚ), (25 / 96 : ℚ), (13 / 48 : ℚ)⟩
private def node_25 : Tree := .leaf (.strip (217 / 1024 : ℚ))
private theorem node_25_accepts : node_25.Accepts parameters box_25 := by
  norm_num [Tree.Accepts, node_25, box_25, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_26 : Rectangle := ⟨(53 / 192 : ℚ), (9 / 32 : ℚ), (25 / 96 : ℚ), (13 / 48 : ℚ)⟩
private def node_26 : Tree := .leaf (.strip (221 / 1024 : ℚ))
private theorem node_26_accepts : node_26.Accepts parameters box_26 := by
  norm_num [Tree.Accepts, node_26, box_26, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_24 : Rectangle := ⟨(13 / 48 : ℚ), (9 / 32 : ℚ), (25 / 96 : ℚ), (13 / 48 : ℚ)⟩
private def node_24 : Tree := .splitC (53 / 192 : ℚ) node_25 node_26
private theorem node_24_accepts : node_24.Accepts parameters box_24 := by
  change SplitCValid box_24 (53 / 192 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitCValid, box_24], node_25_accepts, node_26_accepts⟩

private def box_22 : Rectangle := ⟨(13 / 48 : ℚ), (9 / 32 : ℚ), (1 / 4 : ℚ), (13 / 48 : ℚ)⟩
private def node_22 : Tree := .splitD (25 / 96 : ℚ) node_23 node_24
private theorem node_22_accepts : node_22.Accepts parameters box_22 := by
  change SplitDValid box_22 (25 / 96 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitDValid, box_22], node_23_accepts, node_24_accepts⟩

private def box_28 : Rectangle := ⟨(9 / 32 : ℚ), (7 / 24 : ℚ), (1 / 4 : ℚ), (25 / 96 : ℚ)⟩
private def node_28 : Tree := .leaf (.strip (209 / 1024 : ℚ))
private theorem node_28_accepts : node_28.Accepts parameters box_28 := by
  norm_num [Tree.Accepts, node_28, box_28, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_30 : Rectangle := ⟨(9 / 32 : ℚ), (55 / 192 : ℚ), (25 / 96 : ℚ), (13 / 48 : ℚ)⟩
private def node_30 : Tree := .leaf (.strip (7 / 32 : ℚ))
private theorem node_30_accepts : node_30.Accepts parameters box_30 := by
  norm_num [Tree.Accepts, node_30, box_30, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_31 : Rectangle := ⟨(55 / 192 : ℚ), (7 / 24 : ℚ), (25 / 96 : ℚ), (13 / 48 : ℚ)⟩
private def node_31 : Tree := .leaf (.strip (7 / 32 : ℚ))
private theorem node_31_accepts : node_31.Accepts parameters box_31 := by
  norm_num [Tree.Accepts, node_31, box_31, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_29 : Rectangle := ⟨(9 / 32 : ℚ), (7 / 24 : ℚ), (25 / 96 : ℚ), (13 / 48 : ℚ)⟩
private def node_29 : Tree := .splitC (55 / 192 : ℚ) node_30 node_31
private theorem node_29_accepts : node_29.Accepts parameters box_29 := by
  change SplitCValid box_29 (55 / 192 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitCValid, box_29], node_30_accepts, node_31_accepts⟩

private def box_27 : Rectangle := ⟨(9 / 32 : ℚ), (7 / 24 : ℚ), (1 / 4 : ℚ), (13 / 48 : ℚ)⟩
private def node_27 : Tree := .splitD (25 / 96 : ℚ) node_28 node_29
private theorem node_27_accepts : node_27.Accepts parameters box_27 := by
  change SplitDValid box_27 (25 / 96 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitDValid, box_27], node_28_accepts, node_29_accepts⟩

private def box_21 : Rectangle := ⟨(13 / 48 : ℚ), (7 / 24 : ℚ), (1 / 4 : ℚ), (13 / 48 : ℚ)⟩
private def node_21 : Tree := .splitC (9 / 32 : ℚ) node_22 node_27
private theorem node_21_accepts : node_21.Accepts parameters box_21 := by
  change SplitCValid box_21 (9 / 32 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitCValid, box_21], node_22_accepts, node_27_accepts⟩

private def box_35 : Rectangle := ⟨(13 / 48 : ℚ), (53 / 192 : ℚ), (13 / 48 : ℚ), (9 / 32 : ℚ)⟩
private def node_35 : Tree := .leaf (.strip (115 / 512 : ℚ))
private theorem node_35_accepts : node_35.Accepts parameters box_35 := by
  norm_num [Tree.Accepts, node_35, box_35, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_36 : Rectangle := ⟨(53 / 192 : ℚ), (9 / 32 : ℚ), (13 / 48 : ℚ), (9 / 32 : ℚ)⟩
private def node_36 : Tree := .leaf (.strip (117 / 512 : ℚ))
private theorem node_36_accepts : node_36.Accepts parameters box_36 := by
  norm_num [Tree.Accepts, node_36, box_36, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_34 : Rectangle := ⟨(13 / 48 : ℚ), (9 / 32 : ℚ), (13 / 48 : ℚ), (9 / 32 : ℚ)⟩
private def node_34 : Tree := .splitC (53 / 192 : ℚ) node_35 node_36
private theorem node_34_accepts : node_34.Accepts parameters box_34 := by
  change SplitCValid box_34 (53 / 192 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitCValid, box_34], node_35_accepts, node_36_accepts⟩

private def box_38 : Rectangle := ⟨(13 / 48 : ℚ), (53 / 192 : ℚ), (9 / 32 : ℚ), (7 / 24 : ℚ)⟩
private def node_38 : Tree := .leaf (.strip (117 / 512 : ℚ))
private theorem node_38_accepts : node_38.Accepts parameters box_38 := by
  norm_num [Tree.Accepts, node_38, box_38, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_39 : Rectangle := ⟨(53 / 192 : ℚ), (9 / 32 : ℚ), (9 / 32 : ℚ), (7 / 24 : ℚ)⟩
private def node_39 : Tree := .leaf (.strip (119 / 512 : ℚ))
private theorem node_39_accepts : node_39.Accepts parameters box_39 := by
  norm_num [Tree.Accepts, node_39, box_39, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_37 : Rectangle := ⟨(13 / 48 : ℚ), (9 / 32 : ℚ), (9 / 32 : ℚ), (7 / 24 : ℚ)⟩
private def node_37 : Tree := .splitC (53 / 192 : ℚ) node_38 node_39
private theorem node_37_accepts : node_37.Accepts parameters box_37 := by
  change SplitCValid box_37 (53 / 192 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitCValid, box_37], node_38_accepts, node_39_accepts⟩

private def box_33 : Rectangle := ⟨(13 / 48 : ℚ), (9 / 32 : ℚ), (13 / 48 : ℚ), (7 / 24 : ℚ)⟩
private def node_33 : Tree := .splitD (9 / 32 : ℚ) node_34 node_37
private theorem node_33_accepts : node_33.Accepts parameters box_33 := by
  change SplitDValid box_33 (9 / 32 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitDValid, box_33], node_34_accepts, node_37_accepts⟩

private def box_42 : Rectangle := ⟨(9 / 32 : ℚ), (55 / 192 : ℚ), (13 / 48 : ℚ), (9 / 32 : ℚ)⟩
private def node_42 : Tree := .leaf (.strip (59 / 256 : ℚ))
private theorem node_42_accepts : node_42.Accepts parameters box_42 := by
  norm_num [Tree.Accepts, node_42, box_42, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_43 : Rectangle := ⟨(55 / 192 : ℚ), (7 / 24 : ℚ), (13 / 48 : ℚ), (9 / 32 : ℚ)⟩
private def node_43 : Tree := .leaf (.strip (237 / 1024 : ℚ))
private theorem node_43_accepts : node_43.Accepts parameters box_43 := by
  norm_num [Tree.Accepts, node_43, box_43, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_41 : Rectangle := ⟨(9 / 32 : ℚ), (7 / 24 : ℚ), (13 / 48 : ℚ), (9 / 32 : ℚ)⟩
private def node_41 : Tree := .splitC (55 / 192 : ℚ) node_42 node_43
private theorem node_41_accepts : node_41.Accepts parameters box_41 := by
  change SplitCValid box_41 (55 / 192 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitCValid, box_41], node_42_accepts, node_43_accepts⟩

private def box_44 : Rectangle := ⟨(9 / 32 : ℚ), (7 / 24 : ℚ), (9 / 32 : ℚ), (7 / 24 : ℚ)⟩
private def node_44 : Tree := .leaf (.strip (31 / 128 : ℚ))
private theorem node_44_accepts : node_44.Accepts parameters box_44 := by
  norm_num [Tree.Accepts, node_44, box_44, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_40 : Rectangle := ⟨(9 / 32 : ℚ), (7 / 24 : ℚ), (13 / 48 : ℚ), (7 / 24 : ℚ)⟩
private def node_40 : Tree := .splitD (9 / 32 : ℚ) node_41 node_44
private theorem node_40_accepts : node_40.Accepts parameters box_40 := by
  change SplitDValid box_40 (9 / 32 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitDValid, box_40], node_41_accepts, node_44_accepts⟩

private def box_32 : Rectangle := ⟨(13 / 48 : ℚ), (7 / 24 : ℚ), (13 / 48 : ℚ), (7 / 24 : ℚ)⟩
private def node_32 : Tree := .splitC (9 / 32 : ℚ) node_33 node_40
private theorem node_32_accepts : node_32.Accepts parameters box_32 := by
  change SplitCValid box_32 (9 / 32 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitCValid, box_32], node_33_accepts, node_40_accepts⟩

private def box_20 : Rectangle := ⟨(13 / 48 : ℚ), (7 / 24 : ℚ), (1 / 4 : ℚ), (7 / 24 : ℚ)⟩
private def node_20 : Tree := .splitD (13 / 48 : ℚ) node_21 node_32
private theorem node_20_accepts : node_20.Accepts parameters box_20 := by
  change SplitDValid box_20 (13 / 48 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitDValid, box_20], node_21_accepts, node_32_accepts⟩

private def box_2 : Rectangle := ⟨(1 / 4 : ℚ), (7 / 24 : ℚ), (1 / 4 : ℚ), (7 / 24 : ℚ)⟩
private def node_2 : Tree := .splitC (13 / 48 : ℚ) node_3 node_20
private theorem node_2_accepts : node_2.Accepts parameters box_2 := by
  change SplitCValid box_2 (13 / 48 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitCValid, box_2], node_3_accepts, node_20_accepts⟩

private def box_48 : Rectangle := ⟨(1 / 4 : ℚ), (25 / 96 : ℚ), (7 / 24 : ℚ), (5 / 16 : ℚ)⟩
private def node_48 : Tree := .leaf (.strip (109 / 512 : ℚ))
private theorem node_48_accepts : node_48.Accepts parameters box_48 := by
  norm_num [Tree.Accepts, node_48, box_48, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_50 : Rectangle := ⟨(25 / 96 : ℚ), (13 / 48 : ℚ), (7 / 24 : ℚ), (29 / 96 : ℚ)⟩
private def node_50 : Tree := .leaf (.strip (229 / 1024 : ℚ))
private theorem node_50_accepts : node_50.Accepts parameters box_50 := by
  norm_num [Tree.Accepts, node_50, box_50, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_51 : Rectangle := ⟨(25 / 96 : ℚ), (13 / 48 : ℚ), (29 / 96 : ℚ), (5 / 16 : ℚ)⟩
private def node_51 : Tree := .leaf (.strip (219 / 1024 : ℚ))
private theorem node_51_accepts : node_51.Accepts parameters box_51 := by
  norm_num [Tree.Accepts, node_51, box_51, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_49 : Rectangle := ⟨(25 / 96 : ℚ), (13 / 48 : ℚ), (7 / 24 : ℚ), (5 / 16 : ℚ)⟩
private def node_49 : Tree := .splitD (29 / 96 : ℚ) node_50 node_51
private theorem node_49_accepts : node_49.Accepts parameters box_49 := by
  change SplitDValid box_49 (29 / 96 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitDValid, box_49], node_50_accepts, node_51_accepts⟩

private def box_47 : Rectangle := ⟨(1 / 4 : ℚ), (13 / 48 : ℚ), (7 / 24 : ℚ), (5 / 16 : ℚ)⟩
private def node_47 : Tree := .splitC (25 / 96 : ℚ) node_48 node_49
private theorem node_47_accepts : node_47.Accepts parameters box_47 := by
  change SplitCValid box_47 (25 / 96 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitCValid, box_47], node_48_accepts, node_49_accepts⟩

private def box_52 : Rectangle := ⟨(1 / 4 : ℚ), (13 / 48 : ℚ), (5 / 16 : ℚ), (1 / 3 : ℚ)⟩
private def node_52 : Tree := .leaf (.strip (217 / 1024 : ℚ))
private theorem node_52_accepts : node_52.Accepts parameters box_52 := by
  norm_num [Tree.Accepts, node_52, box_52, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_46 : Rectangle := ⟨(1 / 4 : ℚ), (13 / 48 : ℚ), (7 / 24 : ℚ), (1 / 3 : ℚ)⟩
private def node_46 : Tree := .splitD (5 / 16 : ℚ) node_47 node_52
private theorem node_46_accepts : node_46.Accepts parameters box_46 := by
  change SplitDValid box_46 (5 / 16 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitDValid, box_46], node_47_accepts, node_52_accepts⟩

private def box_56 : Rectangle := ⟨(13 / 48 : ℚ), (9 / 32 : ℚ), (7 / 24 : ℚ), (29 / 96 : ℚ)⟩
private def node_56 : Tree := .leaf (.strip (241 / 1024 : ℚ))
private theorem node_56_accepts : node_56.Accepts parameters box_56 := by
  norm_num [Tree.Accepts, node_56, box_56, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_57 : Rectangle := ⟨(13 / 48 : ℚ), (9 / 32 : ℚ), (29 / 96 : ℚ), (5 / 16 : ℚ)⟩
private def node_57 : Tree := .leaf (.strip (29 / 128 : ℚ))
private theorem node_57_accepts : node_57.Accepts parameters box_57 := by
  norm_num [Tree.Accepts, node_57, box_57, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_55 : Rectangle := ⟨(13 / 48 : ℚ), (9 / 32 : ℚ), (7 / 24 : ℚ), (5 / 16 : ℚ)⟩
private def node_55 : Tree := .splitD (29 / 96 : ℚ) node_56 node_57
private theorem node_55_accepts : node_55.Accepts parameters box_55 := by
  change SplitDValid box_55 (29 / 96 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitDValid, box_55], node_56_accepts, node_57_accepts⟩

private def box_58 : Rectangle := ⟨(9 / 32 : ℚ), (7 / 24 : ℚ), (7 / 24 : ℚ), (5 / 16 : ℚ)⟩
private def node_58 : Tree := .leaf (.strip (1 / 4 : ℚ))
private theorem node_58_accepts : node_58.Accepts parameters box_58 := by
  norm_num [Tree.Accepts, node_58, box_58, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_54 : Rectangle := ⟨(13 / 48 : ℚ), (7 / 24 : ℚ), (7 / 24 : ℚ), (5 / 16 : ℚ)⟩
private def node_54 : Tree := .splitC (9 / 32 : ℚ) node_55 node_58
private theorem node_54_accepts : node_54.Accepts parameters box_54 := by
  change SplitCValid box_54 (9 / 32 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitCValid, box_54], node_55_accepts, node_58_accepts⟩

private def box_59 : Rectangle := ⟨(13 / 48 : ℚ), (7 / 24 : ℚ), (5 / 16 : ℚ), (1 / 3 : ℚ)⟩
private def node_59 : Tree := .leaf (.strip (15 / 64 : ℚ))
private theorem node_59_accepts : node_59.Accepts parameters box_59 := by
  norm_num [Tree.Accepts, node_59, box_59, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_53 : Rectangle := ⟨(13 / 48 : ℚ), (7 / 24 : ℚ), (7 / 24 : ℚ), (1 / 3 : ℚ)⟩
private def node_53 : Tree := .splitD (5 / 16 : ℚ) node_54 node_59
private theorem node_53_accepts : node_53.Accepts parameters box_53 := by
  change SplitDValid box_53 (5 / 16 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitDValid, box_53], node_54_accepts, node_59_accepts⟩

private def box_45 : Rectangle := ⟨(1 / 4 : ℚ), (7 / 24 : ℚ), (7 / 24 : ℚ), (1 / 3 : ℚ)⟩
private def node_45 : Tree := .splitC (13 / 48 : ℚ) node_46 node_53
private theorem node_45_accepts : node_45.Accepts parameters box_45 := by
  change SplitCValid box_45 (13 / 48 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitCValid, box_45], node_46_accepts, node_53_accepts⟩

private def box_1 : Rectangle := ⟨(1 / 4 : ℚ), (7 / 24 : ℚ), (1 / 4 : ℚ), (1 / 3 : ℚ)⟩
private def node_1 : Tree := .splitD (7 / 24 : ℚ) node_2 node_45
private theorem node_1_accepts : node_1.Accepts parameters box_1 := by
  change SplitDValid box_1 (7 / 24 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitDValid, box_1], node_2_accepts, node_45_accepts⟩

private def box_65 : Rectangle := ⟨(7 / 24 : ℚ), (29 / 96 : ℚ), (1 / 4 : ℚ), (25 / 96 : ℚ)⟩
private def node_65 : Tree := .leaf (.strip (103 / 512 : ℚ))
private theorem node_65_accepts : node_65.Accepts parameters box_65 := by
  norm_num [Tree.Accepts, node_65, box_65, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_66 : Rectangle := ⟨(7 / 24 : ℚ), (29 / 96 : ℚ), (25 / 96 : ℚ), (13 / 48 : ℚ)⟩
private def node_66 : Tree := .leaf (.strip (229 / 1024 : ℚ))
private theorem node_66_accepts : node_66.Accepts parameters box_66 := by
  norm_num [Tree.Accepts, node_66, box_66, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_64 : Rectangle := ⟨(7 / 24 : ℚ), (29 / 96 : ℚ), (1 / 4 : ℚ), (13 / 48 : ℚ)⟩
private def node_64 : Tree := .splitD (25 / 96 : ℚ) node_65 node_66
private theorem node_64_accepts : node_64.Accepts parameters box_64 := by
  change SplitDValid box_64 (25 / 96 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitDValid, box_64], node_65_accepts, node_66_accepts⟩

private def box_68 : Rectangle := ⟨(29 / 96 : ℚ), (5 / 16 : ℚ), (1 / 4 : ℚ), (25 / 96 : ℚ)⟩
private def node_68 : Tree := .leaf (.strip (49 / 256 : ℚ))
private theorem node_68_accepts : node_68.Accepts parameters box_68 := by
  norm_num [Tree.Accepts, node_68, box_68, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_69 : Rectangle := ⟨(29 / 96 : ℚ), (5 / 16 : ℚ), (25 / 96 : ℚ), (13 / 48 : ℚ)⟩
private def node_69 : Tree := .leaf (.strip (219 / 1024 : ℚ))
private theorem node_69_accepts : node_69.Accepts parameters box_69 := by
  norm_num [Tree.Accepts, node_69, box_69, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_67 : Rectangle := ⟨(29 / 96 : ℚ), (5 / 16 : ℚ), (1 / 4 : ℚ), (13 / 48 : ℚ)⟩
private def node_67 : Tree := .splitD (25 / 96 : ℚ) node_68 node_69
private theorem node_67_accepts : node_67.Accepts parameters box_67 := by
  change SplitDValid box_67 (25 / 96 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitDValid, box_67], node_68_accepts, node_69_accepts⟩

private def box_63 : Rectangle := ⟨(7 / 24 : ℚ), (5 / 16 : ℚ), (1 / 4 : ℚ), (13 / 48 : ℚ)⟩
private def node_63 : Tree := .splitC (29 / 96 : ℚ) node_64 node_67
private theorem node_63_accepts : node_63.Accepts parameters box_63 := by
  change SplitCValid box_63 (29 / 96 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitCValid, box_63], node_64_accepts, node_67_accepts⟩

private def box_72 : Rectangle := ⟨(7 / 24 : ℚ), (29 / 96 : ℚ), (13 / 48 : ℚ), (9 / 32 : ℚ)⟩
private def node_72 : Tree := .leaf (.strip (241 / 1024 : ℚ))
private theorem node_72_accepts : node_72.Accepts parameters box_72 := by
  norm_num [Tree.Accepts, node_72, box_72, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_73 : Rectangle := ⟨(7 / 24 : ℚ), (29 / 96 : ℚ), (9 / 32 : ℚ), (7 / 24 : ℚ)⟩
private def node_73 : Tree := .leaf (.strip (123 / 512 : ℚ))
private theorem node_73_accepts : node_73.Accepts parameters box_73 := by
  norm_num [Tree.Accepts, node_73, box_73, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_71 : Rectangle := ⟨(7 / 24 : ℚ), (29 / 96 : ℚ), (13 / 48 : ℚ), (7 / 24 : ℚ)⟩
private def node_71 : Tree := .splitD (9 / 32 : ℚ) node_72 node_73
private theorem node_71_accepts : node_71.Accepts parameters box_71 := by
  change SplitDValid box_71 (9 / 32 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitDValid, box_71], node_72_accepts, node_73_accepts⟩

private def box_75 : Rectangle := ⟨(29 / 96 : ℚ), (5 / 16 : ℚ), (13 / 48 : ℚ), (9 / 32 : ℚ)⟩
private def node_75 : Tree := .leaf (.strip (29 / 128 : ℚ))
private theorem node_75_accepts : node_75.Accepts parameters box_75 := by
  norm_num [Tree.Accepts, node_75, box_75, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_76 : Rectangle := ⟨(29 / 96 : ℚ), (5 / 16 : ℚ), (9 / 32 : ℚ), (7 / 24 : ℚ)⟩
private def node_76 : Tree := .leaf (.strip (59 / 256 : ℚ))
private theorem node_76_accepts : node_76.Accepts parameters box_76 := by
  norm_num [Tree.Accepts, node_76, box_76, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_74 : Rectangle := ⟨(29 / 96 : ℚ), (5 / 16 : ℚ), (13 / 48 : ℚ), (7 / 24 : ℚ)⟩
private def node_74 : Tree := .splitD (9 / 32 : ℚ) node_75 node_76
private theorem node_74_accepts : node_74.Accepts parameters box_74 := by
  change SplitDValid box_74 (9 / 32 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitDValid, box_74], node_75_accepts, node_76_accepts⟩

private def box_70 : Rectangle := ⟨(7 / 24 : ℚ), (5 / 16 : ℚ), (13 / 48 : ℚ), (7 / 24 : ℚ)⟩
private def node_70 : Tree := .splitC (29 / 96 : ℚ) node_71 node_74
private theorem node_70_accepts : node_70.Accepts parameters box_70 := by
  change SplitCValid box_70 (29 / 96 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitCValid, box_70], node_71_accepts, node_74_accepts⟩

private def box_62 : Rectangle := ⟨(7 / 24 : ℚ), (5 / 16 : ℚ), (1 / 4 : ℚ), (7 / 24 : ℚ)⟩
private def node_62 : Tree := .splitD (13 / 48 : ℚ) node_63 node_70
private theorem node_62_accepts : node_62.Accepts parameters box_62 := by
  change SplitDValid box_62 (13 / 48 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitDValid, box_62], node_63_accepts, node_70_accepts⟩

private def box_78 : Rectangle := ⟨(5 / 16 : ℚ), (1 / 3 : ℚ), (1 / 4 : ℚ), (13 / 48 : ℚ)⟩
private def node_78 : Tree := .leaf (.strip (217 / 1024 : ℚ))
private theorem node_78_accepts : node_78.Accepts parameters box_78 := by
  norm_num [Tree.Accepts, node_78, box_78, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_79 : Rectangle := ⟨(5 / 16 : ℚ), (1 / 3 : ℚ), (13 / 48 : ℚ), (7 / 24 : ℚ)⟩
private def node_79 : Tree := .leaf (.strip (15 / 64 : ℚ))
private theorem node_79_accepts : node_79.Accepts parameters box_79 := by
  norm_num [Tree.Accepts, node_79, box_79, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_77 : Rectangle := ⟨(5 / 16 : ℚ), (1 / 3 : ℚ), (1 / 4 : ℚ), (7 / 24 : ℚ)⟩
private def node_77 : Tree := .splitD (13 / 48 : ℚ) node_78 node_79
private theorem node_77_accepts : node_77.Accepts parameters box_77 := by
  change SplitDValid box_77 (13 / 48 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitDValid, box_77], node_78_accepts, node_79_accepts⟩

private def box_61 : Rectangle := ⟨(7 / 24 : ℚ), (1 / 3 : ℚ), (1 / 4 : ℚ), (7 / 24 : ℚ)⟩
private def node_61 : Tree := .splitC (5 / 16 : ℚ) node_62 node_77
private theorem node_61_accepts : node_61.Accepts parameters box_61 := by
  change SplitCValid box_61 (5 / 16 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitCValid, box_61], node_62_accepts, node_77_accepts⟩

private def box_82 : Rectangle := ⟨(7 / 24 : ℚ), (5 / 16 : ℚ), (7 / 24 : ℚ), (5 / 16 : ℚ)⟩
private def node_82 : Tree := .leaf (.strip (33 / 128 : ℚ))
private theorem node_82_accepts : node_82.Accepts parameters box_82 := by
  norm_num [Tree.Accepts, node_82, box_82, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_83 : Rectangle := ⟨(7 / 24 : ℚ), (5 / 16 : ℚ), (5 / 16 : ℚ), (1 / 3 : ℚ)⟩
private def node_83 : Tree := .leaf (.strip (117 / 512 : ℚ))
private theorem node_83_accepts : node_83.Accepts parameters box_83 := by
  norm_num [Tree.Accepts, node_83, box_83, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_81 : Rectangle := ⟨(7 / 24 : ℚ), (5 / 16 : ℚ), (7 / 24 : ℚ), (1 / 3 : ℚ)⟩
private def node_81 : Tree := .splitD (5 / 16 : ℚ) node_82 node_83
private theorem node_81_accepts : node_81.Accepts parameters box_81 := by
  change SplitDValid box_81 (5 / 16 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitDValid, box_81], node_82_accepts, node_83_accepts⟩

private def box_84 : Rectangle := ⟨(5 / 16 : ℚ), (1 / 3 : ℚ), (7 / 24 : ℚ), (1 / 3 : ℚ)⟩
private def node_84 : Tree := .leaf (.strip (253 / 1024 : ℚ))
private theorem node_84_accepts : node_84.Accepts parameters box_84 := by
  norm_num [Tree.Accepts, node_84, box_84, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_80 : Rectangle := ⟨(7 / 24 : ℚ), (1 / 3 : ℚ), (7 / 24 : ℚ), (1 / 3 : ℚ)⟩
private def node_80 : Tree := .splitC (5 / 16 : ℚ) node_81 node_84
private theorem node_80_accepts : node_80.Accepts parameters box_80 := by
  change SplitCValid box_80 (5 / 16 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitCValid, box_80], node_81_accepts, node_84_accepts⟩

private def box_60 : Rectangle := ⟨(7 / 24 : ℚ), (1 / 3 : ℚ), (1 / 4 : ℚ), (1 / 3 : ℚ)⟩
private def node_60 : Tree := .splitD (7 / 24 : ℚ) node_61 node_80
private theorem node_60_accepts : node_60.Accepts parameters box_60 := by
  change SplitDValid box_60 (7 / 24 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitDValid, box_60], node_61_accepts, node_80_accepts⟩

private def box_0 : Rectangle := ⟨(1 / 4 : ℚ), (1 / 3 : ℚ), (1 / 4 : ℚ), (1 / 3 : ℚ)⟩
private def node_0 : Tree := .splitC (7 / 24 : ℚ) node_1 node_60
private theorem node_0_accepts : node_0.Accepts parameters box_0 := by
  change SplitCValid box_0 (7 / 24 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitCValid, box_0], node_1_accepts, node_60_accepts⟩

def tree : Tree := node_0
theorem accepted : tree.Accepts parameters (rootRectangle parameters.q) := by
  have hb : box_0 = rootRectangle parameters.q := by
    norm_num [box_0, rootRectangle, parameters]
  simpa only [tree, ← hb] using node_0_accepts

theorem checked : tree.check parameters (rootRectangle parameters.q) = true :=
  (tree.check_eq_true_iff parameters (rootRectangle parameters.q)).mpr accepted

#print axioms accepted
#print axioms checked

end CubeSections.Certificates.Data.Q3M1L1
