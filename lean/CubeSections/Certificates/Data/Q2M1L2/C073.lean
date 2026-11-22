import CubeSections.Certificates.Coverage

/-! Generated from computation/data/pair_trees.json; all arithmetic is proved in Lean. -/
namespace CubeSections.Certificates.Data.Q2M1L2.C073

set_option maxRecDepth 8192
set_option maxHeartbeats 4000000

def parameters : Parameters := ⟨2, 1, 2⟩

private def box_6 : Rectangle := ⟨(5 / 12 : ℚ), (41 / 96 : ℚ), (1 / 3 : ℚ), (17 / 48 : ℚ)⟩
private def node_6 : Tree := .leaf (.strip (333 / 1024 : ℚ))
private theorem node_6_accepts : node_6.Accepts parameters box_6 := by
  norm_num [Tree.Accepts, node_6, box_6, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_7 : Rectangle := ⟨(41 / 96 : ℚ), (7 / 16 : ℚ), (1 / 3 : ℚ), (17 / 48 : ℚ)⟩
private def node_7 : Tree := .leaf (.strip (327 / 1024 : ℚ))
private theorem node_7_accepts : node_7.Accepts parameters box_7 := by
  norm_num [Tree.Accepts, node_7, box_7, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_5 : Rectangle := ⟨(5 / 12 : ℚ), (7 / 16 : ℚ), (1 / 3 : ℚ), (17 / 48 : ℚ)⟩
private def node_5 : Tree := .splitC (41 / 96 : ℚ) node_6 node_7
private theorem node_5_accepts : node_5.Accepts parameters box_5 := by
  change SplitCValid box_5 (41 / 96 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitCValid, box_5], node_6_accepts, node_7_accepts⟩

private def box_10 : Rectangle := ⟨(5 / 12 : ℚ), (41 / 96 : ℚ), (17 / 48 : ℚ), (35 / 96 : ℚ)⟩
private def node_10 : Tree := .leaf .projection
private theorem node_10_accepts : node_10.Accepts parameters box_10 := by
  norm_num [Tree.Accepts, node_10, box_10, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_11 : Rectangle := ⟨(5 / 12 : ℚ), (41 / 96 : ℚ), (35 / 96 : ℚ), (3 / 8 : ℚ)⟩
private def node_11 : Tree := .leaf .projection
private theorem node_11_accepts : node_11.Accepts parameters box_11 := by
  norm_num [Tree.Accepts, node_11, box_11, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_9 : Rectangle := ⟨(5 / 12 : ℚ), (41 / 96 : ℚ), (17 / 48 : ℚ), (3 / 8 : ℚ)⟩
private def node_9 : Tree := .splitD (35 / 96 : ℚ) node_10 node_11
private theorem node_9_accepts : node_9.Accepts parameters box_9 := by
  change SplitDValid box_9 (35 / 96 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitDValid, box_9], node_10_accepts, node_11_accepts⟩

private def box_13 : Rectangle := ⟨(41 / 96 : ℚ), (7 / 16 : ℚ), (17 / 48 : ℚ), (35 / 96 : ℚ)⟩
private def node_13 : Tree := .leaf .projection
private theorem node_13_accepts : node_13.Accepts parameters box_13 := by
  norm_num [Tree.Accepts, node_13, box_13, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_14 : Rectangle := ⟨(41 / 96 : ℚ), (7 / 16 : ℚ), (35 / 96 : ℚ), (3 / 8 : ℚ)⟩
private def node_14 : Tree := .leaf .projection
private theorem node_14_accepts : node_14.Accepts parameters box_14 := by
  norm_num [Tree.Accepts, node_14, box_14, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_12 : Rectangle := ⟨(41 / 96 : ℚ), (7 / 16 : ℚ), (17 / 48 : ℚ), (3 / 8 : ℚ)⟩
private def node_12 : Tree := .splitD (35 / 96 : ℚ) node_13 node_14
private theorem node_12_accepts : node_12.Accepts parameters box_12 := by
  change SplitDValid box_12 (35 / 96 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitDValid, box_12], node_13_accepts, node_14_accepts⟩

private def box_8 : Rectangle := ⟨(5 / 12 : ℚ), (7 / 16 : ℚ), (17 / 48 : ℚ), (3 / 8 : ℚ)⟩
private def node_8 : Tree := .splitC (41 / 96 : ℚ) node_9 node_12
private theorem node_8_accepts : node_8.Accepts parameters box_8 := by
  change SplitCValid box_8 (41 / 96 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitCValid, box_8], node_9_accepts, node_12_accepts⟩

private def box_4 : Rectangle := ⟨(5 / 12 : ℚ), (7 / 16 : ℚ), (1 / 3 : ℚ), (3 / 8 : ℚ)⟩
private def node_4 : Tree := .splitD (17 / 48 : ℚ) node_5 node_8
private theorem node_4_accepts : node_4.Accepts parameters box_4 := by
  change SplitDValid box_4 (17 / 48 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitDValid, box_4], node_5_accepts, node_8_accepts⟩

private def box_16 : Rectangle := ⟨(7 / 16 : ℚ), (11 / 24 : ℚ), (1 / 3 : ℚ), (17 / 48 : ℚ)⟩
private def node_16 : Tree := .leaf .projection
private theorem node_16_accepts : node_16.Accepts parameters box_16 := by
  norm_num [Tree.Accepts, node_16, box_16, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_17 : Rectangle := ⟨(7 / 16 : ℚ), (11 / 24 : ℚ), (17 / 48 : ℚ), (3 / 8 : ℚ)⟩
private def node_17 : Tree := .leaf .projection
private theorem node_17_accepts : node_17.Accepts parameters box_17 := by
  norm_num [Tree.Accepts, node_17, box_17, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_15 : Rectangle := ⟨(7 / 16 : ℚ), (11 / 24 : ℚ), (1 / 3 : ℚ), (3 / 8 : ℚ)⟩
private def node_15 : Tree := .splitD (17 / 48 : ℚ) node_16 node_17
private theorem node_15_accepts : node_15.Accepts parameters box_15 := by
  change SplitDValid box_15 (17 / 48 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitDValid, box_15], node_16_accepts, node_17_accepts⟩

private def box_3 : Rectangle := ⟨(5 / 12 : ℚ), (11 / 24 : ℚ), (1 / 3 : ℚ), (3 / 8 : ℚ)⟩
private def node_3 : Tree := .splitC (7 / 16 : ℚ) node_4 node_15
private theorem node_3_accepts : node_3.Accepts parameters box_3 := by
  change SplitCValid box_3 (7 / 16 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitCValid, box_3], node_4_accepts, node_15_accepts⟩

private def box_23 : Rectangle := ⟨(5 / 12 : ℚ), (27 / 64 : ℚ), (3 / 8 : ℚ), (37 / 96 : ℚ)⟩
private def node_23 : Tree := .leaf .projection
private theorem node_23_accepts : node_23.Accepts parameters box_23 := by
  norm_num [Tree.Accepts, node_23, box_23, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_24 : Rectangle := ⟨(27 / 64 : ℚ), (41 / 96 : ℚ), (3 / 8 : ℚ), (37 / 96 : ℚ)⟩
private def node_24 : Tree := .leaf .projection
private theorem node_24_accepts : node_24.Accepts parameters box_24 := by
  norm_num [Tree.Accepts, node_24, box_24, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_22 : Rectangle := ⟨(5 / 12 : ℚ), (41 / 96 : ℚ), (3 / 8 : ℚ), (37 / 96 : ℚ)⟩
private def node_22 : Tree := .splitC (27 / 64 : ℚ) node_23 node_24
private theorem node_22_accepts : node_22.Accepts parameters box_22 := by
  change SplitCValid box_22 (27 / 64 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitCValid, box_22], node_23_accepts, node_24_accepts⟩

private def box_26 : Rectangle := ⟨(5 / 12 : ℚ), (27 / 64 : ℚ), (37 / 96 : ℚ), (19 / 48 : ℚ)⟩
private def node_26 : Tree := .leaf .projection
private theorem node_26_accepts : node_26.Accepts parameters box_26 := by
  norm_num [Tree.Accepts, node_26, box_26, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_27 : Rectangle := ⟨(27 / 64 : ℚ), (41 / 96 : ℚ), (37 / 96 : ℚ), (19 / 48 : ℚ)⟩
private def node_27 : Tree := .leaf .projection
private theorem node_27_accepts : node_27.Accepts parameters box_27 := by
  norm_num [Tree.Accepts, node_27, box_27, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_25 : Rectangle := ⟨(5 / 12 : ℚ), (41 / 96 : ℚ), (37 / 96 : ℚ), (19 / 48 : ℚ)⟩
private def node_25 : Tree := .splitC (27 / 64 : ℚ) node_26 node_27
private theorem node_25_accepts : node_25.Accepts parameters box_25 := by
  change SplitCValid box_25 (27 / 64 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitCValid, box_25], node_26_accepts, node_27_accepts⟩

private def box_21 : Rectangle := ⟨(5 / 12 : ℚ), (41 / 96 : ℚ), (3 / 8 : ℚ), (19 / 48 : ℚ)⟩
private def node_21 : Tree := .splitD (37 / 96 : ℚ) node_22 node_25
private theorem node_21_accepts : node_21.Accepts parameters box_21 := by
  change SplitDValid box_21 (37 / 96 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitDValid, box_21], node_22_accepts, node_25_accepts⟩

private def box_29 : Rectangle := ⟨(41 / 96 : ℚ), (7 / 16 : ℚ), (3 / 8 : ℚ), (37 / 96 : ℚ)⟩
private def node_29 : Tree := .leaf .projection
private theorem node_29_accepts : node_29.Accepts parameters box_29 := by
  norm_num [Tree.Accepts, node_29, box_29, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_30 : Rectangle := ⟨(41 / 96 : ℚ), (7 / 16 : ℚ), (37 / 96 : ℚ), (19 / 48 : ℚ)⟩
private def node_30 : Tree := .leaf .projection
private theorem node_30_accepts : node_30.Accepts parameters box_30 := by
  norm_num [Tree.Accepts, node_30, box_30, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_28 : Rectangle := ⟨(41 / 96 : ℚ), (7 / 16 : ℚ), (3 / 8 : ℚ), (19 / 48 : ℚ)⟩
private def node_28 : Tree := .splitD (37 / 96 : ℚ) node_29 node_30
private theorem node_28_accepts : node_28.Accepts parameters box_28 := by
  change SplitDValid box_28 (37 / 96 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitDValid, box_28], node_29_accepts, node_30_accepts⟩

private def box_20 : Rectangle := ⟨(5 / 12 : ℚ), (7 / 16 : ℚ), (3 / 8 : ℚ), (19 / 48 : ℚ)⟩
private def node_20 : Tree := .splitC (41 / 96 : ℚ) node_21 node_28
private theorem node_20_accepts : node_20.Accepts parameters box_20 := by
  change SplitCValid box_20 (41 / 96 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitCValid, box_20], node_21_accepts, node_28_accepts⟩

private def box_34 : Rectangle := ⟨(5 / 12 : ℚ), (27 / 64 : ℚ), (19 / 48 : ℚ), (13 / 32 : ℚ)⟩
private def node_34 : Tree := .leaf .projection
private theorem node_34_accepts : node_34.Accepts parameters box_34 := by
  norm_num [Tree.Accepts, node_34, box_34, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_35 : Rectangle := ⟨(27 / 64 : ℚ), (41 / 96 : ℚ), (19 / 48 : ℚ), (13 / 32 : ℚ)⟩
private def node_35 : Tree := .leaf .projection
private theorem node_35_accepts : node_35.Accepts parameters box_35 := by
  norm_num [Tree.Accepts, node_35, box_35, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_33 : Rectangle := ⟨(5 / 12 : ℚ), (41 / 96 : ℚ), (19 / 48 : ℚ), (13 / 32 : ℚ)⟩
private def node_33 : Tree := .splitC (27 / 64 : ℚ) node_34 node_35
private theorem node_33_accepts : node_33.Accepts parameters box_33 := by
  change SplitCValid box_33 (27 / 64 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitCValid, box_33], node_34_accepts, node_35_accepts⟩

private def box_36 : Rectangle := ⟨(5 / 12 : ℚ), (41 / 96 : ℚ), (13 / 32 : ℚ), (5 / 12 : ℚ)⟩
private def node_36 : Tree := .leaf .projection
private theorem node_36_accepts : node_36.Accepts parameters box_36 := by
  norm_num [Tree.Accepts, node_36, box_36, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_32 : Rectangle := ⟨(5 / 12 : ℚ), (41 / 96 : ℚ), (19 / 48 : ℚ), (5 / 12 : ℚ)⟩
private def node_32 : Tree := .splitD (13 / 32 : ℚ) node_33 node_36
private theorem node_32_accepts : node_32.Accepts parameters box_32 := by
  change SplitDValid box_32 (13 / 32 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitDValid, box_32], node_33_accepts, node_36_accepts⟩

private def box_38 : Rectangle := ⟨(41 / 96 : ℚ), (7 / 16 : ℚ), (19 / 48 : ℚ), (13 / 32 : ℚ)⟩
private def node_38 : Tree := .leaf .projection
private theorem node_38_accepts : node_38.Accepts parameters box_38 := by
  norm_num [Tree.Accepts, node_38, box_38, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_39 : Rectangle := ⟨(41 / 96 : ℚ), (7 / 16 : ℚ), (13 / 32 : ℚ), (5 / 12 : ℚ)⟩
private def node_39 : Tree := .leaf .projection
private theorem node_39_accepts : node_39.Accepts parameters box_39 := by
  norm_num [Tree.Accepts, node_39, box_39, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_37 : Rectangle := ⟨(41 / 96 : ℚ), (7 / 16 : ℚ), (19 / 48 : ℚ), (5 / 12 : ℚ)⟩
private def node_37 : Tree := .splitD (13 / 32 : ℚ) node_38 node_39
private theorem node_37_accepts : node_37.Accepts parameters box_37 := by
  change SplitDValid box_37 (13 / 32 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitDValid, box_37], node_38_accepts, node_39_accepts⟩

private def box_31 : Rectangle := ⟨(5 / 12 : ℚ), (7 / 16 : ℚ), (19 / 48 : ℚ), (5 / 12 : ℚ)⟩
private def node_31 : Tree := .splitC (41 / 96 : ℚ) node_32 node_37
private theorem node_31_accepts : node_31.Accepts parameters box_31 := by
  change SplitCValid box_31 (41 / 96 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitCValid, box_31], node_32_accepts, node_37_accepts⟩

private def box_19 : Rectangle := ⟨(5 / 12 : ℚ), (7 / 16 : ℚ), (3 / 8 : ℚ), (5 / 12 : ℚ)⟩
private def node_19 : Tree := .splitD (19 / 48 : ℚ) node_20 node_31
private theorem node_19_accepts : node_19.Accepts parameters box_19 := by
  change SplitDValid box_19 (19 / 48 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitDValid, box_19], node_20_accepts, node_31_accepts⟩

private def box_43 : Rectangle := ⟨(7 / 16 : ℚ), (43 / 96 : ℚ), (3 / 8 : ℚ), (37 / 96 : ℚ)⟩
private def node_43 : Tree := .leaf .projection
private theorem node_43_accepts : node_43.Accepts parameters box_43 := by
  norm_num [Tree.Accepts, node_43, box_43, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_44 : Rectangle := ⟨(7 / 16 : ℚ), (43 / 96 : ℚ), (37 / 96 : ℚ), (19 / 48 : ℚ)⟩
private def node_44 : Tree := .leaf .projection
private theorem node_44_accepts : node_44.Accepts parameters box_44 := by
  norm_num [Tree.Accepts, node_44, box_44, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_42 : Rectangle := ⟨(7 / 16 : ℚ), (43 / 96 : ℚ), (3 / 8 : ℚ), (19 / 48 : ℚ)⟩
private def node_42 : Tree := .splitD (37 / 96 : ℚ) node_43 node_44
private theorem node_42_accepts : node_42.Accepts parameters box_42 := by
  change SplitDValid box_42 (37 / 96 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitDValid, box_42], node_43_accepts, node_44_accepts⟩

private def box_45 : Rectangle := ⟨(43 / 96 : ℚ), (11 / 24 : ℚ), (3 / 8 : ℚ), (19 / 48 : ℚ)⟩
private def node_45 : Tree := .leaf .projection
private theorem node_45_accepts : node_45.Accepts parameters box_45 := by
  norm_num [Tree.Accepts, node_45, box_45, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_41 : Rectangle := ⟨(7 / 16 : ℚ), (11 / 24 : ℚ), (3 / 8 : ℚ), (19 / 48 : ℚ)⟩
private def node_41 : Tree := .splitC (43 / 96 : ℚ) node_42 node_45
private theorem node_41_accepts : node_41.Accepts parameters box_41 := by
  change SplitCValid box_41 (43 / 96 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitCValid, box_41], node_42_accepts, node_45_accepts⟩

private def box_48 : Rectangle := ⟨(7 / 16 : ℚ), (43 / 96 : ℚ), (19 / 48 : ℚ), (13 / 32 : ℚ)⟩
private def node_48 : Tree := .leaf .projection
private theorem node_48_accepts : node_48.Accepts parameters box_48 := by
  norm_num [Tree.Accepts, node_48, box_48, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_49 : Rectangle := ⟨(7 / 16 : ℚ), (43 / 96 : ℚ), (13 / 32 : ℚ), (5 / 12 : ℚ)⟩
private def node_49 : Tree := .leaf .projection
private theorem node_49_accepts : node_49.Accepts parameters box_49 := by
  norm_num [Tree.Accepts, node_49, box_49, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_47 : Rectangle := ⟨(7 / 16 : ℚ), (43 / 96 : ℚ), (19 / 48 : ℚ), (5 / 12 : ℚ)⟩
private def node_47 : Tree := .splitD (13 / 32 : ℚ) node_48 node_49
private theorem node_47_accepts : node_47.Accepts parameters box_47 := by
  change SplitDValid box_47 (13 / 32 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitDValid, box_47], node_48_accepts, node_49_accepts⟩

private def box_50 : Rectangle := ⟨(43 / 96 : ℚ), (11 / 24 : ℚ), (19 / 48 : ℚ), (5 / 12 : ℚ)⟩
private def node_50 : Tree := .leaf .projection
private theorem node_50_accepts : node_50.Accepts parameters box_50 := by
  norm_num [Tree.Accepts, node_50, box_50, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_46 : Rectangle := ⟨(7 / 16 : ℚ), (11 / 24 : ℚ), (19 / 48 : ℚ), (5 / 12 : ℚ)⟩
private def node_46 : Tree := .splitC (43 / 96 : ℚ) node_47 node_50
private theorem node_46_accepts : node_46.Accepts parameters box_46 := by
  change SplitCValid box_46 (43 / 96 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitCValid, box_46], node_47_accepts, node_50_accepts⟩

private def box_40 : Rectangle := ⟨(7 / 16 : ℚ), (11 / 24 : ℚ), (3 / 8 : ℚ), (5 / 12 : ℚ)⟩
private def node_40 : Tree := .splitD (19 / 48 : ℚ) node_41 node_46
private theorem node_40_accepts : node_40.Accepts parameters box_40 := by
  change SplitDValid box_40 (19 / 48 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitDValid, box_40], node_41_accepts, node_46_accepts⟩

private def box_18 : Rectangle := ⟨(5 / 12 : ℚ), (11 / 24 : ℚ), (3 / 8 : ℚ), (5 / 12 : ℚ)⟩
private def node_18 : Tree := .splitC (7 / 16 : ℚ) node_19 node_40
private theorem node_18_accepts : node_18.Accepts parameters box_18 := by
  change SplitCValid box_18 (7 / 16 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitCValid, box_18], node_19_accepts, node_40_accepts⟩

private def box_2 : Rectangle := ⟨(5 / 12 : ℚ), (11 / 24 : ℚ), (1 / 3 : ℚ), (5 / 12 : ℚ)⟩
private def node_2 : Tree := .splitD (3 / 8 : ℚ) node_3 node_18
private theorem node_2_accepts : node_2.Accepts parameters box_2 := by
  change SplitDValid box_2 (3 / 8 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitDValid, box_2], node_3_accepts, node_18_accepts⟩

private def box_54 : Rectangle := ⟨(11 / 24 : ℚ), (23 / 48 : ℚ), (1 / 3 : ℚ), (17 / 48 : ℚ)⟩
private def node_54 : Tree := .leaf .projection
private theorem node_54_accepts : node_54.Accepts parameters box_54 := by
  norm_num [Tree.Accepts, node_54, box_54, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_55 : Rectangle := ⟨(11 / 24 : ℚ), (23 / 48 : ℚ), (17 / 48 : ℚ), (3 / 8 : ℚ)⟩
private def node_55 : Tree := .leaf .projection
private theorem node_55_accepts : node_55.Accepts parameters box_55 := by
  norm_num [Tree.Accepts, node_55, box_55, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_53 : Rectangle := ⟨(11 / 24 : ℚ), (23 / 48 : ℚ), (1 / 3 : ℚ), (3 / 8 : ℚ)⟩
private def node_53 : Tree := .splitD (17 / 48 : ℚ) node_54 node_55
private theorem node_53_accepts : node_53.Accepts parameters box_53 := by
  change SplitDValid box_53 (17 / 48 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitDValid, box_53], node_54_accepts, node_55_accepts⟩

private def box_56 : Rectangle := ⟨(23 / 48 : ℚ), (1 / 2 : ℚ), (1 / 3 : ℚ), (3 / 8 : ℚ)⟩
private def node_56 : Tree := .leaf .projection
private theorem node_56_accepts : node_56.Accepts parameters box_56 := by
  norm_num [Tree.Accepts, node_56, box_56, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_52 : Rectangle := ⟨(11 / 24 : ℚ), (1 / 2 : ℚ), (1 / 3 : ℚ), (3 / 8 : ℚ)⟩
private def node_52 : Tree := .splitC (23 / 48 : ℚ) node_53 node_56
private theorem node_52_accepts : node_52.Accepts parameters box_52 := by
  change SplitCValid box_52 (23 / 48 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitCValid, box_52], node_53_accepts, node_56_accepts⟩

private def box_59 : Rectangle := ⟨(11 / 24 : ℚ), (23 / 48 : ℚ), (3 / 8 : ℚ), (19 / 48 : ℚ)⟩
private def node_59 : Tree := .leaf .projection
private theorem node_59_accepts : node_59.Accepts parameters box_59 := by
  norm_num [Tree.Accepts, node_59, box_59, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_60 : Rectangle := ⟨(11 / 24 : ℚ), (23 / 48 : ℚ), (19 / 48 : ℚ), (5 / 12 : ℚ)⟩
private def node_60 : Tree := .leaf .projection
private theorem node_60_accepts : node_60.Accepts parameters box_60 := by
  norm_num [Tree.Accepts, node_60, box_60, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_58 : Rectangle := ⟨(11 / 24 : ℚ), (23 / 48 : ℚ), (3 / 8 : ℚ), (5 / 12 : ℚ)⟩
private def node_58 : Tree := .splitD (19 / 48 : ℚ) node_59 node_60
private theorem node_58_accepts : node_58.Accepts parameters box_58 := by
  change SplitDValid box_58 (19 / 48 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitDValid, box_58], node_59_accepts, node_60_accepts⟩

private def box_61 : Rectangle := ⟨(23 / 48 : ℚ), (1 / 2 : ℚ), (3 / 8 : ℚ), (5 / 12 : ℚ)⟩
private def node_61 : Tree := .leaf .projection
private theorem node_61_accepts : node_61.Accepts parameters box_61 := by
  norm_num [Tree.Accepts, node_61, box_61, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_57 : Rectangle := ⟨(11 / 24 : ℚ), (1 / 2 : ℚ), (3 / 8 : ℚ), (5 / 12 : ℚ)⟩
private def node_57 : Tree := .splitC (23 / 48 : ℚ) node_58 node_61
private theorem node_57_accepts : node_57.Accepts parameters box_57 := by
  change SplitCValid box_57 (23 / 48 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitCValid, box_57], node_58_accepts, node_61_accepts⟩

private def box_51 : Rectangle := ⟨(11 / 24 : ℚ), (1 / 2 : ℚ), (1 / 3 : ℚ), (5 / 12 : ℚ)⟩
private def node_51 : Tree := .splitD (3 / 8 : ℚ) node_52 node_57
private theorem node_51_accepts : node_51.Accepts parameters box_51 := by
  change SplitDValid box_51 (3 / 8 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitDValid, box_51], node_52_accepts, node_57_accepts⟩

private def box_1 : Rectangle := ⟨(5 / 12 : ℚ), (1 / 2 : ℚ), (1 / 3 : ℚ), (5 / 12 : ℚ)⟩
private def node_1 : Tree := .splitC (11 / 24 : ℚ) node_2 node_51
private theorem node_1_accepts : node_1.Accepts parameters box_1 := by
  change SplitCValid box_1 (11 / 24 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitCValid, box_1], node_2_accepts, node_51_accepts⟩

private def box_68 : Rectangle := ⟨(5 / 12 : ℚ), (41 / 96 : ℚ), (5 / 12 : ℚ), (41 / 96 : ℚ)⟩
private def node_68 : Tree := .leaf .projection
private theorem node_68_accepts : node_68.Accepts parameters box_68 := by
  norm_num [Tree.Accepts, node_68, box_68, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_69 : Rectangle := ⟨(5 / 12 : ℚ), (41 / 96 : ℚ), (41 / 96 : ℚ), (7 / 16 : ℚ)⟩
private def node_69 : Tree := .leaf .projection
private theorem node_69_accepts : node_69.Accepts parameters box_69 := by
  norm_num [Tree.Accepts, node_69, box_69, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_67 : Rectangle := ⟨(5 / 12 : ℚ), (41 / 96 : ℚ), (5 / 12 : ℚ), (7 / 16 : ℚ)⟩
private def node_67 : Tree := .splitD (41 / 96 : ℚ) node_68 node_69
private theorem node_67_accepts : node_67.Accepts parameters box_67 := by
  change SplitDValid box_67 (41 / 96 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitDValid, box_67], node_68_accepts, node_69_accepts⟩

private def box_71 : Rectangle := ⟨(41 / 96 : ℚ), (7 / 16 : ℚ), (5 / 12 : ℚ), (41 / 96 : ℚ)⟩
private def node_71 : Tree := .leaf .projection
private theorem node_71_accepts : node_71.Accepts parameters box_71 := by
  norm_num [Tree.Accepts, node_71, box_71, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_72 : Rectangle := ⟨(41 / 96 : ℚ), (7 / 16 : ℚ), (41 / 96 : ℚ), (7 / 16 : ℚ)⟩
private def node_72 : Tree := .leaf .projection
private theorem node_72_accepts : node_72.Accepts parameters box_72 := by
  norm_num [Tree.Accepts, node_72, box_72, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_70 : Rectangle := ⟨(41 / 96 : ℚ), (7 / 16 : ℚ), (5 / 12 : ℚ), (7 / 16 : ℚ)⟩
private def node_70 : Tree := .splitD (41 / 96 : ℚ) node_71 node_72
private theorem node_70_accepts : node_70.Accepts parameters box_70 := by
  change SplitDValid box_70 (41 / 96 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitDValid, box_70], node_71_accepts, node_72_accepts⟩

private def box_66 : Rectangle := ⟨(5 / 12 : ℚ), (7 / 16 : ℚ), (5 / 12 : ℚ), (7 / 16 : ℚ)⟩
private def node_66 : Tree := .splitC (41 / 96 : ℚ) node_67 node_70
private theorem node_66_accepts : node_66.Accepts parameters box_66 := by
  change SplitCValid box_66 (41 / 96 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitCValid, box_66], node_67_accepts, node_70_accepts⟩

private def box_75 : Rectangle := ⟨(5 / 12 : ℚ), (41 / 96 : ℚ), (7 / 16 : ℚ), (43 / 96 : ℚ)⟩
private def node_75 : Tree := .leaf .projection
private theorem node_75_accepts : node_75.Accepts parameters box_75 := by
  norm_num [Tree.Accepts, node_75, box_75, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_76 : Rectangle := ⟨(5 / 12 : ℚ), (41 / 96 : ℚ), (43 / 96 : ℚ), (11 / 24 : ℚ)⟩
private def node_76 : Tree := .leaf .projection
private theorem node_76_accepts : node_76.Accepts parameters box_76 := by
  norm_num [Tree.Accepts, node_76, box_76, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_74 : Rectangle := ⟨(5 / 12 : ℚ), (41 / 96 : ℚ), (7 / 16 : ℚ), (11 / 24 : ℚ)⟩
private def node_74 : Tree := .splitD (43 / 96 : ℚ) node_75 node_76
private theorem node_74_accepts : node_74.Accepts parameters box_74 := by
  change SplitDValid box_74 (43 / 96 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitDValid, box_74], node_75_accepts, node_76_accepts⟩

private def box_78 : Rectangle := ⟨(41 / 96 : ℚ), (7 / 16 : ℚ), (7 / 16 : ℚ), (43 / 96 : ℚ)⟩
private def node_78 : Tree := .leaf .projection
private theorem node_78_accepts : node_78.Accepts parameters box_78 := by
  norm_num [Tree.Accepts, node_78, box_78, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_79 : Rectangle := ⟨(41 / 96 : ℚ), (7 / 16 : ℚ), (43 / 96 : ℚ), (11 / 24 : ℚ)⟩
private def node_79 : Tree := .leaf .projection
private theorem node_79_accepts : node_79.Accepts parameters box_79 := by
  norm_num [Tree.Accepts, node_79, box_79, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_77 : Rectangle := ⟨(41 / 96 : ℚ), (7 / 16 : ℚ), (7 / 16 : ℚ), (11 / 24 : ℚ)⟩
private def node_77 : Tree := .splitD (43 / 96 : ℚ) node_78 node_79
private theorem node_77_accepts : node_77.Accepts parameters box_77 := by
  change SplitDValid box_77 (43 / 96 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitDValid, box_77], node_78_accepts, node_79_accepts⟩

private def box_73 : Rectangle := ⟨(5 / 12 : ℚ), (7 / 16 : ℚ), (7 / 16 : ℚ), (11 / 24 : ℚ)⟩
private def node_73 : Tree := .splitC (41 / 96 : ℚ) node_74 node_77
private theorem node_73_accepts : node_73.Accepts parameters box_73 := by
  change SplitCValid box_73 (41 / 96 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitCValid, box_73], node_74_accepts, node_77_accepts⟩

private def box_65 : Rectangle := ⟨(5 / 12 : ℚ), (7 / 16 : ℚ), (5 / 12 : ℚ), (11 / 24 : ℚ)⟩
private def node_65 : Tree := .splitD (7 / 16 : ℚ) node_66 node_73
private theorem node_65_accepts : node_65.Accepts parameters box_65 := by
  change SplitDValid box_65 (7 / 16 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitDValid, box_65], node_66_accepts, node_73_accepts⟩

private def box_82 : Rectangle := ⟨(7 / 16 : ℚ), (43 / 96 : ℚ), (5 / 12 : ℚ), (7 / 16 : ℚ)⟩
private def node_82 : Tree := .leaf .projection
private theorem node_82_accepts : node_82.Accepts parameters box_82 := by
  norm_num [Tree.Accepts, node_82, box_82, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_83 : Rectangle := ⟨(43 / 96 : ℚ), (11 / 24 : ℚ), (5 / 12 : ℚ), (7 / 16 : ℚ)⟩
private def node_83 : Tree := .leaf .projection
private theorem node_83_accepts : node_83.Accepts parameters box_83 := by
  norm_num [Tree.Accepts, node_83, box_83, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_81 : Rectangle := ⟨(7 / 16 : ℚ), (11 / 24 : ℚ), (5 / 12 : ℚ), (7 / 16 : ℚ)⟩
private def node_81 : Tree := .splitC (43 / 96 : ℚ) node_82 node_83
private theorem node_81_accepts : node_81.Accepts parameters box_81 := by
  change SplitCValid box_81 (43 / 96 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitCValid, box_81], node_82_accepts, node_83_accepts⟩

private def box_84 : Rectangle := ⟨(7 / 16 : ℚ), (11 / 24 : ℚ), (7 / 16 : ℚ), (11 / 24 : ℚ)⟩
private def node_84 : Tree := .leaf .projection
private theorem node_84_accepts : node_84.Accepts parameters box_84 := by
  norm_num [Tree.Accepts, node_84, box_84, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_80 : Rectangle := ⟨(7 / 16 : ℚ), (11 / 24 : ℚ), (5 / 12 : ℚ), (11 / 24 : ℚ)⟩
private def node_80 : Tree := .splitD (7 / 16 : ℚ) node_81 node_84
private theorem node_80_accepts : node_80.Accepts parameters box_80 := by
  change SplitDValid box_80 (7 / 16 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitDValid, box_80], node_81_accepts, node_84_accepts⟩

private def box_64 : Rectangle := ⟨(5 / 12 : ℚ), (11 / 24 : ℚ), (5 / 12 : ℚ), (11 / 24 : ℚ)⟩
private def node_64 : Tree := .splitC (7 / 16 : ℚ) node_65 node_80
private theorem node_64_accepts : node_64.Accepts parameters box_64 := by
  change SplitCValid box_64 (7 / 16 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitCValid, box_64], node_65_accepts, node_80_accepts⟩

private def box_88 : Rectangle := ⟨(5 / 12 : ℚ), (41 / 96 : ℚ), (11 / 24 : ℚ), (23 / 48 : ℚ)⟩
private def node_88 : Tree := .leaf .projection
private theorem node_88_accepts : node_88.Accepts parameters box_88 := by
  norm_num [Tree.Accepts, node_88, box_88, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_89 : Rectangle := ⟨(41 / 96 : ℚ), (7 / 16 : ℚ), (11 / 24 : ℚ), (23 / 48 : ℚ)⟩
private def node_89 : Tree := .leaf .projection
private theorem node_89_accepts : node_89.Accepts parameters box_89 := by
  norm_num [Tree.Accepts, node_89, box_89, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_87 : Rectangle := ⟨(5 / 12 : ℚ), (7 / 16 : ℚ), (11 / 24 : ℚ), (23 / 48 : ℚ)⟩
private def node_87 : Tree := .splitC (41 / 96 : ℚ) node_88 node_89
private theorem node_87_accepts : node_87.Accepts parameters box_87 := by
  change SplitCValid box_87 (41 / 96 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitCValid, box_87], node_88_accepts, node_89_accepts⟩

private def box_90 : Rectangle := ⟨(5 / 12 : ℚ), (7 / 16 : ℚ), (23 / 48 : ℚ), (1 / 2 : ℚ)⟩
private def node_90 : Tree := .leaf .projection
private theorem node_90_accepts : node_90.Accepts parameters box_90 := by
  norm_num [Tree.Accepts, node_90, box_90, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_86 : Rectangle := ⟨(5 / 12 : ℚ), (7 / 16 : ℚ), (11 / 24 : ℚ), (1 / 2 : ℚ)⟩
private def node_86 : Tree := .splitD (23 / 48 : ℚ) node_87 node_90
private theorem node_86_accepts : node_86.Accepts parameters box_86 := by
  change SplitDValid box_86 (23 / 48 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitDValid, box_86], node_87_accepts, node_90_accepts⟩

private def box_92 : Rectangle := ⟨(7 / 16 : ℚ), (11 / 24 : ℚ), (11 / 24 : ℚ), (23 / 48 : ℚ)⟩
private def node_92 : Tree := .leaf .projection
private theorem node_92_accepts : node_92.Accepts parameters box_92 := by
  norm_num [Tree.Accepts, node_92, box_92, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_93 : Rectangle := ⟨(7 / 16 : ℚ), (11 / 24 : ℚ), (23 / 48 : ℚ), (1 / 2 : ℚ)⟩
private def node_93 : Tree := .leaf .projection
private theorem node_93_accepts : node_93.Accepts parameters box_93 := by
  norm_num [Tree.Accepts, node_93, box_93, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_91 : Rectangle := ⟨(7 / 16 : ℚ), (11 / 24 : ℚ), (11 / 24 : ℚ), (1 / 2 : ℚ)⟩
private def node_91 : Tree := .splitD (23 / 48 : ℚ) node_92 node_93
private theorem node_91_accepts : node_91.Accepts parameters box_91 := by
  change SplitDValid box_91 (23 / 48 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitDValid, box_91], node_92_accepts, node_93_accepts⟩

private def box_85 : Rectangle := ⟨(5 / 12 : ℚ), (11 / 24 : ℚ), (11 / 24 : ℚ), (1 / 2 : ℚ)⟩
private def node_85 : Tree := .splitC (7 / 16 : ℚ) node_86 node_91
private theorem node_85_accepts : node_85.Accepts parameters box_85 := by
  change SplitCValid box_85 (7 / 16 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitCValid, box_85], node_86_accepts, node_91_accepts⟩

private def box_63 : Rectangle := ⟨(5 / 12 : ℚ), (11 / 24 : ℚ), (5 / 12 : ℚ), (1 / 2 : ℚ)⟩
private def node_63 : Tree := .splitD (11 / 24 : ℚ) node_64 node_85
private theorem node_63_accepts : node_63.Accepts parameters box_63 := by
  change SplitDValid box_63 (11 / 24 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitDValid, box_63], node_64_accepts, node_85_accepts⟩

private def box_97 : Rectangle := ⟨(11 / 24 : ℚ), (23 / 48 : ℚ), (5 / 12 : ℚ), (7 / 16 : ℚ)⟩
private def node_97 : Tree := .leaf .projection
private theorem node_97_accepts : node_97.Accepts parameters box_97 := by
  norm_num [Tree.Accepts, node_97, box_97, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_98 : Rectangle := ⟨(11 / 24 : ℚ), (23 / 48 : ℚ), (7 / 16 : ℚ), (11 / 24 : ℚ)⟩
private def node_98 : Tree := .leaf .projection
private theorem node_98_accepts : node_98.Accepts parameters box_98 := by
  norm_num [Tree.Accepts, node_98, box_98, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_96 : Rectangle := ⟨(11 / 24 : ℚ), (23 / 48 : ℚ), (5 / 12 : ℚ), (11 / 24 : ℚ)⟩
private def node_96 : Tree := .splitD (7 / 16 : ℚ) node_97 node_98
private theorem node_96_accepts : node_96.Accepts parameters box_96 := by
  change SplitDValid box_96 (7 / 16 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitDValid, box_96], node_97_accepts, node_98_accepts⟩

private def box_99 : Rectangle := ⟨(23 / 48 : ℚ), (1 / 2 : ℚ), (5 / 12 : ℚ), (11 / 24 : ℚ)⟩
private def node_99 : Tree := .leaf .projection
private theorem node_99_accepts : node_99.Accepts parameters box_99 := by
  norm_num [Tree.Accepts, node_99, box_99, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_95 : Rectangle := ⟨(11 / 24 : ℚ), (1 / 2 : ℚ), (5 / 12 : ℚ), (11 / 24 : ℚ)⟩
private def node_95 : Tree := .splitC (23 / 48 : ℚ) node_96 node_99
private theorem node_95_accepts : node_95.Accepts parameters box_95 := by
  change SplitCValid box_95 (23 / 48 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitCValid, box_95], node_96_accepts, node_99_accepts⟩

private def box_100 : Rectangle := ⟨(11 / 24 : ℚ), (1 / 2 : ℚ), (11 / 24 : ℚ), (1 / 2 : ℚ)⟩
private def node_100 : Tree := .leaf .projection
private theorem node_100_accepts : node_100.Accepts parameters box_100 := by
  norm_num [Tree.Accepts, node_100, box_100, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_94 : Rectangle := ⟨(11 / 24 : ℚ), (1 / 2 : ℚ), (5 / 12 : ℚ), (1 / 2 : ℚ)⟩
private def node_94 : Tree := .splitD (11 / 24 : ℚ) node_95 node_100
private theorem node_94_accepts : node_94.Accepts parameters box_94 := by
  change SplitDValid box_94 (11 / 24 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitDValid, box_94], node_95_accepts, node_100_accepts⟩

private def box_62 : Rectangle := ⟨(5 / 12 : ℚ), (1 / 2 : ℚ), (5 / 12 : ℚ), (1 / 2 : ℚ)⟩
private def node_62 : Tree := .splitC (11 / 24 : ℚ) node_63 node_94
private theorem node_62_accepts : node_62.Accepts parameters box_62 := by
  change SplitCValid box_62 (11 / 24 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitCValid, box_62], node_63_accepts, node_94_accepts⟩

private def box_0 : Rectangle := ⟨(5 / 12 : ℚ), (1 / 2 : ℚ), (1 / 3 : ℚ), (1 / 2 : ℚ)⟩
private def node_0 : Tree := .splitD (5 / 12 : ℚ) node_1 node_62
private theorem node_0_accepts : node_0.Accepts parameters box_0 := by
  change SplitDValid box_0 (5 / 12 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitDValid, box_0], node_1_accepts, node_62_accepts⟩

def tree : Tree := node_0
def rootBox : Rectangle := box_0
theorem accepted : tree.Accepts parameters rootBox := node_0_accepts

end CubeSections.Certificates.Data.Q2M1L2.C073
